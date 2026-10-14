/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Text

/-! # Widgets

A widget draws itself into the space it is given, and its result, an `Image`, carries the proof
that it fits there. On each axis a widget is either fixed, taking only the room it needs, or
greedy, taking all the room it is given. A box gives its fixed children their room first and
shares what is left among the greedy ones, so `hBox [str "Name: ", txt name]` keeps the label
whole and wraps the name in the rest of the line. Each widget proves that its image fits from
the proofs its children's images carry. -/

namespace Tessera

variable {cs : Charset}

inductive Policy where
  | fixed
  | greedy
  deriving DecidableEq, Repr, Inhabited

/-- The space a widget is drawn into, and the style it inherits. -/
structure Context where
  width : Nat
  height : Nat
  style : Style := {}

/-- A buffer that fits in `maxW` by `maxH`. -/
structure Image (cs : Charset) (maxW maxH : Nat) where
  w : Nat
  h : Nat
  w_le : w ≤ maxW
  h_le : h ≤ maxH
  buf : Buffer cs w h

namespace Image

def empty {maxW maxH : Nat} : Image cs maxW maxH := ⟨0, 0, Nat.zero_le _, Nat.zero_le _, .blank 0 0⟩

def mono {a b a' b' : Nat} (i : Image cs a b) (ha : a ≤ a') (hb : b ≤ b') : Image cs a' b' :=
  ⟨i.w, i.h, Nat.le_trans i.w_le ha, Nat.le_trans i.h_le hb, i.buf⟩

end Image

structure Widget (cs : Charset) where
  hPolicy : Policy := .fixed
  vPolicy : Policy := .fixed
  render : (ctx : Context) → Image cs ctx.width ctx.height

instance : Inhabited (Widget cs) := ⟨{ render := fun _ => .empty }⟩

/-- The longest prefix of `s` that fits in `width` cells. -/
def truncate (cs : Charset) (width : Nat) (s : String) : String :=
  (s.foldl (init := ("", 0)) fun (acc, n) c =>
    let cw := cs.textWidth (String.singleton c)
    if n + cw ≤ width then (acc.push c, n + cw) else (acc, width + 1)).1

/-- Break `s` into lines of at most `width` cells, at spaces where it can and inside words
longer than a line. -/
def wrap (cs : Charset) (width : Nat) (s : String) : List String :=
  if width == 0 then [] else (s.splitOn "\n").flatMap paragraph
where
  paragraph (p : String) : List String :=
    let (lines, cur) := (p.splitOn " ").foldl (init := (([] : List String), "")) fun (lines, cur) word =>
      let joined := if cur.isEmpty then word else cur ++ " " ++ word
      if cs.textWidth joined ≤ width then (lines, joined)
      else
        let lines := if cur.isEmpty then lines else cur :: lines
        breakWord lines word
    (cur :: lines).reverse
  /-- Lines of a word too long for one, and what is left of it. -/
  breakWord (lines : List String) (word : String) : List String × String :=
    word.foldl (init := (lines, "")) fun (lines, cur) c =>
      if cs.textWidth (cur.push c) ≤ width then (lines, cur.push c)
      else (cur :: lines, String.singleton c)

/-- `lines` drawn one per row, in a buffer `width` wide. -/
private def linesImage (ctx : Context) (lines : List String) (width : Nat) (hw : width ≤ ctx.width)
    (hh : lines.length ≤ ctx.height) : Image cs ctx.width ctx.height :=
  ⟨width, lines.length, hw, hh,
    lines.zipIdx.foldl (init := Buffer.blank width lines.length ctx.style) fun b (l, y) =>
      (b.putString 0 y (cs.glyphs l) ctx.style).1⟩

namespace Widget

def empty : Widget cs := default

variable {o : Origin}

/-- Lines of text, one per row, clipped to the space given. -/
def strs (ts : List (Text cs o)) : Widget cs where
  render ctx :=
    let lines := (ts.map (·.text)).take ctx.height
    linesImage ctx lines (min ctx.width (lines.foldl (fun n l => max n (cs.textWidth l)) 0))
      (Nat.min_le_left _ _) (by simp [lines]; omega)

/-- One line of text, clipped to the space given. -/
def str (t : Text cs o) : Widget cs := strs [t]

/-- Text wrapped to the width given. -/
def txt (t : Text cs o) : Widget cs where
  hPolicy := .greedy
  render ctx :=
    let lines := (wrap cs ctx.width t.text).take ctx.height
    linesImage ctx lines ctx.width (Nat.le_refl _) (by simp [lines]; omega)

/-- All the space given, filled with `c`, or blank if `cs` does not allow it. -/
def fill (c : Char := ' ') : Widget cs where
  hPolicy := .greedy
  vPolicy := .greedy
  render ctx :=
    let gs := (cs.glyphs (String.singleton c)).flatMap fun g =>
      List.replicate (ctx.width / max 1 g.width) g
    ⟨ctx.width, ctx.height, Nat.le_refl _, Nat.le_refl _,
      (List.range ctx.height).foldl (init := Buffer.blank ctx.width ctx.height ctx.style) fun b y =>
        (b.putString 0 y gs ctx.style).1⟩

/-- Draw `w` and everything in it in style `s`, over the inherited style. -/
def withStyle (s : Style) (w : Widget cs) : Widget cs :=
  { w with render := fun ctx => w.render { ctx with style := s.over ctx.style } }

def pad (left top right bottom : Nat) (w : Widget cs) : Widget cs :=
  { w with
    render := fun ctx =>
      let inner := w.render { ctx with width := ctx.width - left - right,
                                       height := ctx.height - top - bottom }
      let iw := min ctx.width (inner.w + left + right)
      let ih := min ctx.height (inner.h + top + bottom)
      ⟨iw, ih, Nat.min_le_left _ _, Nat.min_le_left _ _,
        (Buffer.blank iw ih ctx.style).blit left top inner.buf⟩ }

def padAll (n : Nat) (w : Widget cs) : Widget cs := pad n n n n w

/-- At most `n` cells wide. -/
def hLimit (n : Nat) (w : Widget cs) : Widget cs :=
  { w with
    hPolicy := .fixed
    render := fun ctx =>
      (w.render { ctx with width := min n ctx.width }).mono (Nat.min_le_right _ _) (Nat.le_refl _) }

/-- At most `n` cells high. -/
def vLimit (n : Nat) (w : Widget cs) : Widget cs :=
  { w with
    vPolicy := .fixed
    render := fun ctx =>
      (w.render { ctx with height := min n ctx.height }).mono (Nat.le_refl _) (Nat.min_le_right _ _) }

/-! ## Boxes

A box lays its children out along one axis (`hz`: across the screen, or down it). Each child is
drawn within the length it is given along that axis; the lengths given add up to at most the
box's own, so the children's images do too. -/

/-- A child's image, no thicker than the box across its axis. -/
private structure Piece (cs : Charset) (hz : Bool) (across : Nat) where
  w : Nat
  h : Nat
  buf : Buffer cs w h
  across_le : (if hz then h else w) ≤ across

private def Piece.along {hz : Bool} {a : Nat} (p : Piece cs hz a) : Nat := if hz then p.w else p.h

private def Piece.thickness {hz : Bool} {a : Nat} (p : Piece cs hz a) : Nat := if hz then p.h else p.w

private abbrev Render (cs : Charset) (hz : Bool) (a : Nat) :=
  Widget cs → (n : Nat) → {p : Piece cs hz a // p.along ≤ n}

/-- Draw a child within `n` along the axis. -/
private def renderIn (ctx : Context) : (hz : Bool) → Render cs hz (if hz then ctx.height else ctx.width)
  | true, c, n =>
    let i := c.render { ctx with width := n }
    ⟨⟨i.w, i.h, i.buf, by simpa using i.h_le⟩, by simpa [Piece.along] using i.w_le⟩
  | false, c, n =>
    let i := c.render { ctx with height := n }
    ⟨⟨i.w, i.h, i.buf, by simpa using i.w_le⟩, by simpa [Piece.along] using i.h_le⟩

private def policy (hz : Bool) (w : Widget cs) : Policy := if hz then w.hPolicy else w.vPolicy

private def sumAlong {hz : Bool} {a : Nat} : List (Piece cs hz a ⊕ Widget cs) → Nat
  | [] => 0
  | .inl p :: r => p.along + sumAlong r
  | .inr _ :: r => sumAlong r

private def greedyCount {hz : Bool} {a : Nat} : List (Piece cs hz a ⊕ Widget cs) → Nat
  | [] => 0
  | .inl _ :: r => greedyCount r
  | .inr _ :: r => greedyCount r + 1

/-- Draw the fixed children, in order, each within what is left; the greedy ones wait. -/
private def fixedPass {hz : Bool} {a : Nat} (r : Render cs hz a) :
    (ws : List (Widget cs)) → (left : Nat) →
      {out : List (Piece cs hz a ⊕ Widget cs) × Nat // sumAlong out.1 + out.2 ≤ left}
  | [], left => ⟨([], left), by simp [sumAlong]⟩
  | c :: ws, left =>
    if policy hz c == .fixed then
      let ⟨p, hp⟩ := r c left
      let ⟨(rest, left'), h⟩ := fixedPass r ws (left - p.along)
      ⟨(.inl p :: rest, left'), by simp only [sumAlong] at h ⊢; omega⟩
    else
      let ⟨(rest, left'), h⟩ := fixedPass r ws left
      ⟨(.inr c :: rest, left'), by simpa [sumAlong] using h⟩

/-- Draw the greedy children, sharing `pool` among them, the first ones taking a cell more when
it does not divide evenly. -/
private def greedyPass {hz : Bool} {a : Nat} (r : Render cs hz a) :
    (xs : List (Piece cs hz a ⊕ Widget cs)) → (pool : Nat) →
      {ps : List (Piece cs hz a) // (ps.map (·.along)).sum ≤ sumAlong xs + pool}
  | [], _ => ⟨[], by simp⟩
  | .inl p :: xs, pool =>
    let ⟨ps, h⟩ := greedyPass r xs pool
    ⟨p :: ps, by simp only [List.map_cons, List.sum_cons, sumAlong]; omega⟩
  | .inr c :: xs, pool =>
    let g := greedyCount xs + 1
    let share := min pool ((pool + g - 1) / g)
    let ⟨p, hp⟩ := r c share
    let ⟨ps, h⟩ := greedyPass r xs (pool - share)
    ⟨p :: ps, by simp only [List.map_cons, List.sum_cons, sumAlong] at h ⊢; omega⟩

private def maxThickness {hz : Bool} {a : Nat} : List (Piece cs hz a) → Nat
  | [] => 0
  | p :: ps => max p.thickness (maxThickness ps)

private theorem maxThickness_le {hz : Bool} {a : Nat} :
    (ps : List (Piece cs hz a)) → maxThickness ps ≤ a
  | [] => Nat.zero_le _
  | p :: ps => by
    have := p.across_le
    have := maxThickness_le ps
    simp only [maxThickness, Piece.thickness]
    omega

/-- Children side by side (`hz`) or one above the other. -/
private def box (hz : Bool) (ws : List (Widget cs)) : Widget cs where
  hPolicy := if ws.any (·.hPolicy == .greedy) then .greedy else .fixed
  vPolicy := if ws.any (·.vPolicy == .greedy) then .greedy else .fixed
  render ctx :=
    let r := renderIn ctx hz
    let total := if hz then ctx.width else ctx.height
    let ⟨(xs, left), hfixed⟩ := fixedPass r ws total
    let ⟨ps, hgreedy⟩ := greedyPass r xs left
    let length := (ps.map (·.along)).sum
    let thickness := maxThickness ps
    have hl : length ≤ total := by simp only at hfixed; omega
    have ht : thickness ≤ _ := maxThickness_le ps
    let bw := if hz then length else thickness
    let bh := if hz then thickness else length
    let b := (ps.foldl (init := (Buffer.blank (cs := cs) bw bh ctx.style, 0)) fun (b, pos) p =>
      (if hz then b.blit pos 0 p.buf else b.blit 0 pos p.buf, pos + p.along)).1
    have hbw : bw ≤ ctx.width := by cases hz; exact ht; exact hl
    have hbh : bh ≤ ctx.height := by cases hz; exact hl; exact ht
    ⟨bw, bh, hbw, hbh, b⟩

/-- Children side by side. -/
def hBox (ws : List (Widget cs)) : Widget cs := box true ws

/-- Children one above the other. -/
def vBox (ws : List (Widget cs)) : Widget cs := box false ws

/-- A line around `w`, with `label` in its top edge. -/
def borderWithLabel (label : Text cs o) (w : Widget cs) : Widget cs :=
  { w with
    render := fun ctx =>
      if hs : ctx.width < 2 ∨ ctx.height < 2 then
        ⟨min ctx.width 2, min ctx.height 2, Nat.min_le_left _ _, Nat.min_le_left _ _,
          .blank _ _ ctx.style⟩
      else
        let inner := w.render { ctx with width := ctx.width - 2, height := ctx.height - 2 }
        let bw := inner.w + 2
        let bh := inner.h + 2
        have hw : inner.w ≤ ctx.width - 2 := inner.w_le
        have hh : inner.h ≤ ctx.height - 2 := inner.h_le
        have hs : 2 ≤ ctx.width ∧ 2 ≤ ctx.height := by omega
        let put (b : Buffer cs bw bh) (x y : Nat) (s : String) :=
          (b.putString x y (cs.glyphs s) ctx.style).1
        let horizontal := String.ofList (List.replicate inner.w '─')
        let b := Buffer.blank bw bh ctx.style
        let b := put b 0 0 ("┌" ++ horizontal ++ "┐")
        let b := put b 0 (bh - 1) ("└" ++ horizontal ++ "┘")
        let b := (List.range inner.h).foldl (init := b) fun b y =>
          put (put b 0 (y + 1) "│") (bw - 1) (y + 1) "│"
        let b := put b 1 0 (truncate cs inner.w label.text)
        ⟨bw, bh, by omega, by omega, b.blit 1 1 inner.buf⟩ }

def border (w : Widget cs) : Widget cs := borderWithLabel (o := .app) .empty w

/-- `w` in the middle of all the space given. -/
def center (w : Widget cs) : Widget cs where
  hPolicy := .greedy
  vPolicy := .greedy
  render ctx :=
    let img := w.render ctx
    ⟨ctx.width, ctx.height, Nat.le_refl _, Nat.le_refl _,
      (Buffer.blank ctx.width ctx.height ctx.style).blit
        ((ctx.width - img.w) / 2) ((ctx.height - img.h) / 2) img.buf⟩

/-- The rows of `w` from `offset` on, in all the space given. -/
def viewport (offset : Nat) (w : Widget cs) : Widget cs where
  hPolicy := .greedy
  vPolicy := .greedy
  render ctx :=
    let img := w.render { ctx with height := offset + ctx.height }
    ⟨ctx.width, ctx.height, Nat.le_refl _, Nat.le_refl _,
      (Buffer.blank ctx.width ctx.height ctx.style).blit 0 0
        (img.buf.crop 0 offset img.w (min ctx.height (img.h - offset)))⟩

/-- The whole frame: `w` drawn into a `width` by `height` screen. -/
def draw (w : Widget cs) (width height : Nat) : Buffer cs width height :=
  (Buffer.blank width height).blit 0 0 (w.render { width, height }).buf

end Widget

end Tessera
