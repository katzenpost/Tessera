/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Style
import Tessera.Char

/-! # Screen buffers

A buffer is a grid of cells, `w` wide and `h` high. A cell holds a glyph, which is a character
its charset allows, the right half of a two-cell glyph, or nothing. Each row carries the proof
that it is well formed: every two-cell glyph is followed by its right half, and a right half
follows nothing else. Every write preserves it, blanking whatever half of a two-cell glyph it
leaves behind. -/

namespace Tessera

variable {cs : Charset}

/-- A character that may be written to the terminal as it is. -/
structure Glyph (cs : Charset) where
  char : Char
  printable : cs.Printable char

instance : DecidableEq (Glyph cs) := fun a b =>
  if h : a.char = b.char then isTrue (by cases a; cases b; simp_all)
  else isFalse fun e => h (congrArg Glyph.char e)

namespace Glyph

def ofChar? (c : Char) : Option (Glyph cs) := if h : cs.Printable c then some ⟨c, h⟩ else none

def width (g : Glyph cs) : Nat := cs.width g.char

def wide (g : Glyph cs) : Bool := cs.width g.char == 2

end Glyph

/-- The characters of `s` that `cs` allows; the rest take no cell and are left out. -/
def Charset.glyphs (cs : Charset) (s : String) : List (Glyph cs) := s.toList.filterMap Glyph.ofChar?

/-- How many cells `s` takes, leaving out the characters `cs` does not allow. -/
def Charset.textWidth (cs : Charset) (s : String) : Nat :=
  s.foldl (fun n c => n + if cs.Printable c then cs.width c else 0) 0

inductive Cell (cs : Charset) where
  | glyph (g : Glyph cs) (style : Style)
  /-- The right half of a two-cell glyph. -/
  | wideRight (style : Style)
  | blank (style : Style)
  deriving DecidableEq

instance : Inhabited (Cell cs) := ⟨.blank {}⟩

namespace Cell

def style : Cell cs → Style
  | .glyph _ s | .wideRight s | .blank s => s

/-- The character shown: a right half shows as nothing, and is not a character of its own. -/
def char : Cell cs → Char
  | .glyph g _ => g.char
  | _ => ' '

def isContinuation : Cell cs → Bool
  | .wideRight _ => true
  | _ => false

/-- Every two-cell glyph is followed by its right half, and a right half follows nothing else. -/
def wellFormed : List (Cell cs) → Bool
  | [] => true
  | .wideRight _ :: _ => false
  | .blank _ :: rest => wellFormed rest
  | .glyph g _ :: .wideRight _ :: rest => g.wide && wellFormed rest
  | .glyph g _ :: rest => !g.wide && wellFormed rest

theorem wellFormed_cons_blank {s : Style} {l : List (Cell cs)} (h : wellFormed l) :
    wellFormed (.blank s :: l) := by
  simpa [wellFormed] using h

theorem wellFormed_cons_narrow {g : Glyph cs} {s : Style} {l : List (Cell cs)} (hg : g.wide = false)
    (h : wellFormed l) : wellFormed (.glyph g s :: l) := by
  match l with
  | [] => simp [wellFormed, hg]
  | .wideRight _ :: _ => simp [wellFormed] at h
  | .blank _ :: _ => simpa [wellFormed, hg] using h
  | .glyph _ _ :: _ => simpa [wellFormed, hg] using h

theorem wellFormed_cons_wide {g : Glyph cs} {s s' : Style} {l : List (Cell cs)} (hg : g.wide = true)
    (h : wellFormed l) : wellFormed (.glyph g s :: .wideRight s' :: l) := by
  simpa [wellFormed, hg] using h

theorem wellFormed_append {a b : List (Cell cs)} (ha : wellFormed a) (hb : wellFormed b) :
    wellFormed (a ++ b) := by
  induction a using wellFormed.induct with
  | case1 => simpa using hb
  | case2 => simp [wellFormed] at ha
  | case3 _ _ ih => exact wellFormed_cons_blank (ih (by simpa [wellFormed] using ha))
  | case4 g _ _ _ ih =>
    simp only [wellFormed, Bool.and_eq_true] at ha
    exact wellFormed_cons_wide ha.1 (ih ha.2)
  | case5 g _ rest hrest ih =>
    have ha' : g.wide = false ∧ wellFormed rest := by
      match rest, hrest with
      | [], _ => simpa [wellFormed] using ha
      | .blank _ :: _, _ => simpa [wellFormed] using ha
      | .glyph _ _ :: _, _ => simpa [wellFormed] using ha
      | .wideRight _ :: _, h => exact absurd rfl (h _ _)
    exact wellFormed_cons_narrow ha'.1 (ih ha'.2)

theorem wellFormed_replicate_blank (n : Nat) (s : Style) :
    wellFormed (List.replicate n (Cell.blank (cs := cs) s)) := by
  induction n with
  | zero => rfl
  | succ n ih => exact wellFormed_cons_blank ih

/-- The cells of `gs` in style `s`, each two-cell glyph followed by its right half. A space is a
blank, so that a space shows one way however it was drawn. -/
def ofGlyphs (s : Style) : List (Glyph cs) → List (Cell cs)
  | [] => []
  | g :: gs =>
    if g.char = ' ' then .blank s :: ofGlyphs s gs
    else if g.wide then .glyph g s :: .wideRight s :: ofGlyphs s gs
    else .glyph g s :: ofGlyphs s gs

theorem wellFormed_ofGlyphs (s : Style) (gs : List (Glyph cs)) : wellFormed (ofGlyphs s gs) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    unfold ofGlyphs
    split
    · exact wellFormed_cons_blank ih
    · cases hg : g.wide
      · simpa [hg] using wellFormed_cons_narrow hg ih
      · simpa [hg] using wellFormed_cons_wide hg ih

/-- The first `n` cells; a two-cell glyph cut in half becomes a blank. -/
def cut : Nat → List (Cell cs) → List (Cell cs)
  | 0, _ => []
  | _, [] => []
  | n + 1, .glyph g s :: .wideRight s' :: rest =>
    if n = 0 then [.blank s] else .glyph g s :: .wideRight s' :: cut (n - 1) rest
  | n + 1, c :: rest => c :: cut n rest

/-- All but the first `n` cells; the right half of a two-cell glyph cut in half becomes a
blank. -/
def skip : Nat → List (Cell cs) → List (Cell cs)
  | 0, l => l
  | _, [] => []
  | n + 1, .glyph _ _ :: .wideRight s' :: rest => if n = 0 then .blank s' :: rest else skip (n - 1) rest
  | n + 1, _ :: rest => skip n rest

@[simp] theorem cut_nil (n : Nat) : cut n ([] : List (Cell cs)) = [] := by
  cases n <;> simp [cut]

@[simp] theorem skip_nil (n : Nat) : skip n ([] : List (Cell cs)) = [] := by
  cases n <;> simp [skip]

theorem length_cut (n : Nat) (l : List (Cell cs)) : (cut n l).length = min n l.length := by
  induction n, l using cut.induct with
  | case1 => simp [cut]
  | case2 x hx => simp [cut.eq_2 x hx]
  | case3 => simp [cut]
  | case4 n g s s' rest hn ih => simp [cut, hn, ih]; omega
  | case5 n c rest hp ih => rw [cut.eq_4 _ _ _ hp]; simp [ih]

theorem length_skip (n : Nat) (l : List (Cell cs)) : (skip n l).length = l.length - n := by
  induction n, l using skip.induct with
  | case1 => simp [skip]
  | case2 x hx => simp [skip.eq_2 x hx]
  | case3 => simp [skip]
  | case4 n g s s' rest hn ih => simp [skip, hn, ih]; omega
  | case5 n c rest hp ih => rw [skip.eq_4 _ _ _ hp]; simp [ih]

theorem wellFormed_cut (n : Nat) {l : List (Cell cs)} (h : wellFormed l) : wellFormed (cut n l) := by
  induction n, l using cut.induct with
  | case1 => simp [cut, wellFormed]
  | case2 x hx => rw [cut.eq_2 x hx]; rfl
  | case3 => simp [cut, wellFormed]
  | case4 n g s s' rest hn ih =>
    simp only [wellFormed, Bool.and_eq_true] at h
    simpa [cut, hn] using wellFormed_cons_wide h.1 (ih h.2)
  | case5 n c rest hpair ih =>
    rw [cut.eq_4 _ _ _ hpair]
    match c, rest, hpair with
    | .blank _, rest, _ => exact wellFormed_cons_blank (ih (by simpa [wellFormed] using h))
    | .wideRight _, _, _ => simp [wellFormed] at h
    | .glyph g s, [], _ => simpa [cut] using h
    | .glyph g s, .wideRight _ :: _, hp => exact (hp g s _ _ rfl rfl).elim
    | .glyph g s, .blank _ :: _, _ =>
      simp only [wellFormed, Bool.and_eq_true, Bool.not_eq_true'] at h
      exact wellFormed_cons_narrow h.1 (ih (by simpa [wellFormed] using h.2))
    | .glyph g s, .glyph _ _ :: _, _ =>
      simp only [wellFormed, Bool.and_eq_true, Bool.not_eq_true'] at h
      exact wellFormed_cons_narrow h.1 (ih (by simpa [wellFormed] using h.2))

theorem wellFormed_skip (n : Nat) {l : List (Cell cs)} (h : wellFormed l) : wellFormed (skip n l) := by
  induction n, l using skip.induct with
  | case1 => simpa [skip] using h
  | case2 x hx => rw [skip.eq_2 x hx]; rfl
  | case3 =>
    simp only [wellFormed, Bool.and_eq_true] at h
    simpa [skip] using wellFormed_cons_blank h.2
  | case4 n g s s' rest hn ih =>
    simp only [wellFormed, Bool.and_eq_true] at h
    simpa [skip, hn] using ih h.2
  | case5 n c rest hpair ih =>
    rw [skip.eq_4 _ _ _ hpair]
    match c, rest, hpair with
    | .blank _, rest, _ => exact ih (by simpa [wellFormed] using h)
    | .wideRight _, _, _ => simp [wellFormed] at h
    | .glyph g s, [], _ => simp [wellFormed]
    | .glyph g s, .wideRight _ :: _, hp => exact (hp g s _ _ rfl rfl).elim
    | .glyph g s, .blank _ :: _, _ =>
      simp only [wellFormed, Bool.and_eq_true] at h
      exact ih (by simpa [wellFormed] using h.2)
    | .glyph g s, .glyph _ _ :: _, _ =>
      simp only [wellFormed, Bool.and_eq_true] at h
      exact ih (by simpa [wellFormed] using h.2)

end Cell

open Cell in
/-- One row of `w` cells. -/
structure Row (cs : Charset) (w : Nat) where
  cells : List (Cell cs)
  length_eq : cells.length = w
  wf : wellFormed cells = true

namespace Row

open Cell

instance {w : Nat} : DecidableEq (Row cs w) := fun a b =>
  if h : a.cells = b.cells then isTrue (by cases a; cases b; simp_all)
  else isFalse fun e => h (congrArg Row.cells e)

def blank (w : Nat) (s : Style := {}) : Row cs w :=
  ⟨List.replicate w (.blank s), by simp, wellFormed_replicate_blank w s⟩

/-- `seg` written from column `x`, clipped at the right edge. A two-cell glyph half covered
by it, or cut by the edge, becomes a blank. -/
def splice {w : Nat} (r : Row cs w) (x : Nat) (seg : List (Cell cs)) (hseg : wellFormed seg) :
    Row cs w :=
  if hx : x ≤ w then
    let mid := cut (w - x) seg
    have hmid : mid.length ≤ w - x := by simp [mid, length_cut]; omega
    ⟨cut x r.cells ++ mid ++ skip (x + mid.length) r.cells,
      by simp only [List.length_append, length_cut, length_skip, r.length_eq]; omega,
      wellFormed_append (wellFormed_append (wellFormed_cut x r.wf) (wellFormed_cut _ hseg))
        (wellFormed_skip _ r.wf)⟩
  else r

/-- How many cells of `seg` `splice` writes from column `x`. -/
def written (w x : Nat) (seg : List (Cell cs)) : Nat := (cut (w - x) seg).length

theorem written_le (w x : Nat) (seg : List (Cell cs)) : written w x seg ≤ w - x := by
  simp [written, length_cut]; omega

/-- The `n` cells from column `x`, blank past the end. A two-cell glyph cut by either edge
becomes a blank. -/
def slice {w : Nat} (r : Row cs w) (x n : Nat) (s : Style := {}) : Row cs n :=
  let l := cut n (skip x r.cells)
  ⟨l ++ List.replicate (n - l.length) (.blank s),
    by simp only [List.length_append, List.length_replicate, l, length_cut]; omega,
    wellFormed_append (wellFormed_cut n (wellFormed_skip x r.wf)) (wellFormed_replicate_blank _ s)⟩

def get {w : Nat} (r : Row cs w) (x : Nat) : Cell cs := r.cells.getD x default

end Row

structure Buffer (cs : Charset) (w h : Nat) where
  rows : Vector (Row cs w) h
  deriving DecidableEq

namespace Buffer

variable {w h : Nat}

def blank (w h : Nat) (s : Style := {}) : Buffer cs w h := ⟨.replicate h (.blank w s)⟩

instance : Inhabited (Buffer cs w h) := ⟨blank w h⟩

def width (_ : Buffer cs w h) : Nat := w

def height (_ : Buffer cs w h) : Nat := h

/-- The cell at `(x, y)`; outside the buffer, a blank. -/
def get (b : Buffer cs w h) (x y : Nat) : Cell cs :=
  if hy : y < h then b.rows[y].get x else default

def modifyRow (b : Buffer cs w h) (y : Nat) (f : Row cs w → Row cs w) : Buffer cs w h :=
  if hy : y < h then ⟨b.rows.set y (f b.rows[y])⟩ else b

/-- Write `seg` from column `x` of row `y`, clipped at the edges. -/
def putCells (b : Buffer cs w h) (x y : Nat) (seg : List (Cell cs)) (hseg : Cell.wellFormed seg) :
    Buffer cs w h :=
  b.modifyRow y (·.splice x seg hseg)

/-- Write `gs` from column `x` of row `y`, clipped at the right edge, and return the column after
them. -/
def putString (b : Buffer cs w h) (x y : Nat) (gs : List (Glyph cs)) (style : Style := {}) :
    Buffer cs w h × {x' : Nat // x' ≤ w} :=
  let seg := Cell.ofGlyphs style gs
  (b.putCells x y seg (Cell.wellFormed_ofGlyphs style gs),
    ⟨min w (x + Row.written w x seg), Nat.min_le_left _ _⟩)

/-- Copy `src` onto `b` with its top left corner at `(x, y)`, clipped at the edges. -/
def blit {sw sh : Nat} (b : Buffer cs w h) (x y : Nat) (src : Buffer cs sw sh) : Buffer cs w h :=
  src.rows.toList.zipIdx.foldl (init := b) fun b (r, j) => b.putCells x (y + j) r.cells r.wf

/-- The `cw` by `ch` part of `b` from `(x, y)`, blank past its edges. -/
def crop (b : Buffer cs w h) (x y cw ch : Nat) : Buffer cs cw ch :=
  ⟨.ofFn fun j => if hy : y + j.val < h then b.rows[y + j.val].slice x cw else .blank cw⟩

/-- The characters of row `y`, without continuations. -/
def row (b : Buffer cs w h) (y : Nat) : String :=
  if hy : y < h then
    String.ofList <| b.rows[y].cells.filterMap fun c => if c.isContinuation then none else some c.char
  else ""

/-- The buffer's text, one line per row. -/
def lines (b : Buffer cs w h) : List String := (List.range h).map b.row

end Buffer

end Tessera
