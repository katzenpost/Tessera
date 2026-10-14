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

/-- A widget whose text is of origin `o`. Its constructor is private: a widget of origin `.app`
is built only from text the program wrote, by the functions here, and one of a program's own
making (`Widget.custom`) is of origin `.remote`, so a remote text cannot pass for the program's
by being drawn in a widget of its own. -/
structure Widget (cs : Charset) (o : Origin) where
  private mk ::
  hPolicy : Policy := .fixed
  vPolicy : Policy := .fixed
  render : (ctx : Context) → Image cs ctx.width ctx.height

variable {o : Origin}

/-- Text of origin `t` may be shown in a widget of origin `w`: the program's text in any widget,
text from elsewhere only in a widget of origin `.remote`. -/
class Shows (t w : Origin) : Prop

instance {w : Origin} : Shows .app w := ⟨⟩
instance : Shows .remote .remote := ⟨⟩

instance : Inhabited (Widget cs o) := ⟨{ render := fun _ => .empty }⟩

/-- `lines` drawn one per row, in a buffer `width` wide. -/
private def linesImage {t : Origin} (ctx : Context) (lines : List (Text cs t)) (width : Nat)
    (hw : width ≤ ctx.width) (hh : lines.length ≤ ctx.height) : Image cs ctx.width ctx.height :=
  ⟨width, lines.length, hw, hh,
    lines.zipIdx.foldl (init := Buffer.blank width lines.length ctx.style) fun b (l, y) =>
      (b.putString 0 y l.glyphs ctx.style).1⟩

namespace Widget

def empty : Widget cs o := default

/-- A widget of the program's own making. Its text may be from anywhere, so it is of origin
`.remote`. -/
def custom (render : (ctx : Context) → Image cs ctx.width ctx.height)
    (hPolicy vPolicy : Policy := .fixed) : Widget cs .remote :=
  { hPolicy, vPolicy, render }

/-- A widget of the program's text, used where text from elsewhere may be. -/
def lift (w : Widget cs .app) : Widget cs .remote :=
  { hPolicy := w.hPolicy, vPolicy := w.vPolicy, render := w.render }

instance : Coe (Widget cs .app) (Widget cs .remote) := ⟨lift⟩

/-- Lines of text, one per row, clipped to the space given. -/
def strs {t : Origin} [Shows t o] (ts : List (Text cs t)) : Widget cs o where
  render ctx :=
    let lines := ts.take ctx.height
    linesImage ctx lines (min ctx.width (lines.foldl (fun n l => max n l.width) 0))
      (Nat.min_le_left _ _) (by simp [lines]; omega)

/-- One line of text, clipped to the space given. -/
def str {t : Origin} [Shows t o] (s : Text cs t) : Widget cs o := strs [s]

/-- Text wrapped to the width given. -/
def txt {t : Origin} [Shows t o] (s : Text cs t) : Widget cs o where
  hPolicy := .greedy
  render ctx :=
    let lines := ((s.wrap ctx.width).map (·.text)).take ctx.height
    linesImage ctx lines ctx.width (Nat.le_refl _) (by simp [lines]; omega)

/-- All the space given, filled with `c`, or blank if `cs` does not allow it. -/
def fill (c : Char := ' ') : Widget cs o where
  hPolicy := .greedy
  vPolicy := .greedy
  render ctx :=
    let gs := (cs.glyphs (String.singleton c)).flatMap fun g =>
      List.replicate (ctx.width / max 1 g.width) g
    ⟨ctx.width, ctx.height, Nat.le_refl _, Nat.le_refl _,
      (List.range ctx.height).foldl (init := Buffer.blank ctx.width ctx.height ctx.style) fun b y =>
        (b.putString 0 y gs ctx.style).1⟩

/-- Draw `w` and everything in it in style `s`, over the inherited style. -/
def withStyle (s : Style) (w : Widget cs o) : Widget cs o :=
  { w with render := fun ctx => w.render { ctx with style := s.over ctx.style } }

def pad (left top right bottom : Nat) (w : Widget cs o) : Widget cs o :=
  { w with
    render := fun ctx =>
      let inner := w.render { ctx with width := ctx.width - left - right,
                                       height := ctx.height - top - bottom }
      let iw := min ctx.width (inner.w + left + right)
      let ih := min ctx.height (inner.h + top + bottom)
      ⟨iw, ih, Nat.min_le_left _ _, Nat.min_le_left _ _,
        (Buffer.blank iw ih ctx.style).blit left top inner.buf⟩ }

def padAll (n : Nat) (w : Widget cs o) : Widget cs o := pad n n n n w

/-- A widget chosen by the space it is given. -/
def sized (f : Context → Widget cs o) (hPolicy vPolicy : Policy := .greedy) : Widget cs o where
  hPolicy
  vPolicy
  render ctx := (f ctx).render ctx

/-- At most `n` cells wide. -/
def hLimit (n : Nat) (w : Widget cs o) : Widget cs o :=
  { w with
    hPolicy := .fixed
    render := fun ctx =>
      (w.render { ctx with width := min n ctx.width }).mono (Nat.min_le_right _ _) (Nat.le_refl _) }

/-- At most `n` cells high. -/
def vLimit (n : Nat) (w : Widget cs o) : Widget cs o :=
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

private abbrev Render (cs : Charset) (o : Origin) (hz : Bool) (a : Nat) :=
  Widget cs o → (n : Nat) → {p : Piece cs hz a // p.along ≤ n}

/-- Draw a child within `n` along the axis. -/
private def renderIn (ctx : Context) : (hz : Bool) → Render cs o hz (if hz then ctx.height else ctx.width)
  | true, c, n =>
    let i := c.render { ctx with width := n }
    ⟨⟨i.w, i.h, i.buf, by simpa using i.h_le⟩, by simpa [Piece.along] using i.w_le⟩
  | false, c, n =>
    let i := c.render { ctx with height := n }
    ⟨⟨i.w, i.h, i.buf, by simpa using i.w_le⟩, by simpa [Piece.along] using i.h_le⟩

private def policy (hz : Bool) (w : Widget cs o) : Policy := if hz then w.hPolicy else w.vPolicy

private def sumAlong {hz : Bool} {a : Nat} : List (Piece cs hz a ⊕ Widget cs o) → Nat
  | [] => 0
  | .inl p :: r => p.along + sumAlong r
  | .inr _ :: r => sumAlong r

private def greedyCount {hz : Bool} {a : Nat} : List (Piece cs hz a ⊕ Widget cs o) → Nat
  | [] => 0
  | .inl _ :: r => greedyCount r
  | .inr _ :: r => greedyCount r + 1

/-- Draw the fixed children, in order, each within what is left; the greedy ones wait. -/
private def fixedPass {hz : Bool} {a : Nat} (r : Render cs o hz a) :
    (ws : List (Widget cs o)) → (left : Nat) →
      {out : List (Piece cs hz a ⊕ Widget cs o) × Nat // sumAlong out.1 + out.2 ≤ left}
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
private def greedyPass {hz : Bool} {a : Nat} (r : Render cs o hz a) :
    (xs : List (Piece cs hz a ⊕ Widget cs o)) → (pool : Nat) →
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
private def box (hz : Bool) (ws : List (Widget cs o)) : Widget cs o where
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
def hBox (ws : List (Widget cs o)) : Widget cs o := box true ws

/-- Children one above the other. -/
def vBox (ws : List (Widget cs o)) : Widget cs o := box false ws

/-- A line around `w`, with `label` in its top edge. -/
def borderWithLabel {t : Origin} [Shows t o] (label : Text cs t) (w : Widget cs o) : Widget cs o :=
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
        let b := (b.putString 1 0 (label.truncate inner.w).glyphs ctx.style).1
        ⟨bw, bh, by omega, by omega, b.blit 1 1 inner.buf⟩ }

def border (w : Widget cs o) : Widget cs o := borderWithLabel (t := .app) .empty w

/-- `w` in the middle of all the space given. -/
def center (w : Widget cs o) : Widget cs o where
  hPolicy := .greedy
  vPolicy := .greedy
  render ctx :=
    let img := w.render ctx
    ⟨ctx.width, ctx.height, Nat.le_refl _, Nat.le_refl _,
      (Buffer.blank ctx.width ctx.height ctx.style).blit
        ((ctx.width - img.w) / 2) ((ctx.height - img.h) / 2) img.buf⟩

/-- The rows of `w` from `offset` on, in all the space given. -/
def viewport (offset : Nat) (w : Widget cs o) : Widget cs o where
  hPolicy := .greedy
  vPolicy := .greedy
  render ctx :=
    let img := w.render { ctx with height := offset + ctx.height }
    ⟨ctx.width, ctx.height, Nat.le_refl _, Nat.le_refl _,
      (Buffer.blank ctx.width ctx.height ctx.style).blit 0 0
        (img.buf.crop 0 offset img.w (min ctx.height (img.h - offset)))⟩

/-- Draw `w` in a style its sender chose, over the inherited style. Whatever the sender chose, the
result is a reserved style only where the inherited one was (`RemoteStyle.reserved_over`). -/
def withSenderStyle (r : RemoteStyle) (w : Widget cs o) : Widget cs o := withStyle r.toStyle w

/-- Text from elsewhere in a place the program keeps for its own, such as a room's topic in its
header: cut to `budget` cells and drawn between the program's delimiters. It is the one way text
from elsewhere reaches a widget of origin `.app`, and it is never wider than the delimiters and
`budget`. -/
def delimited (openD closeD : Text cs .app) (budget : Nat) (t : Text cs .remote) : Widget cs .app :=
  let inner : Widget cs .remote :=
    hLimit (openD.width + budget + closeD.width) (str (openD.lift ++ t.truncate budget ++ closeD.lift))
  { hPolicy := inner.hPolicy, vPolicy := inner.vPolicy, render := inner.render }

/-- The whole frame: `w` drawn into a `width` by `height` screen. -/
def draw (w : Widget cs o) (width height : Nat) : Buffer cs width height :=
  (Buffer.blank width height).blit 0 0 (w.render { width, height }).buf

end Widget

end Tessera
