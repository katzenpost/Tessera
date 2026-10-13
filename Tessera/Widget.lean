/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Buffer

/-! # Widgets

A widget draws itself into the space it is given and returns a buffer no larger than that
space. On each axis it is either fixed, taking only the room it needs, or greedy, taking all the
room it is given. A box gives its fixed children their room first and shares what is left among
the greedy ones, so `hBox [str "Name: ", txt name]` keeps the label whole and wraps the name in
the rest of the line. -/

namespace Tessera

inductive Policy where
  | fixed
  | greedy
  deriving DecidableEq, Repr, Inhabited

/-- The space a widget is drawn into, and the style it inherits. -/
structure Context where
  width : Nat
  height : Nat
  style : Style := {}

structure Widget where
  hPolicy : Policy := .fixed
  vPolicy : Policy := .fixed
  render : Context → Buffer

instance : Inhabited Widget := ⟨{ render := fun _ => .blank 0 0 }⟩

namespace Buffer

/-- The `width` by `height` part of `b` from `(x, y)`. -/
def crop (b : Buffer) (x y width height : Nat) : Buffer := Id.run do
  let mut r := Buffer.blank width height
  for j in [0:height] do
    for i in [0:width] do
      r := { r with cells := r.cells.set! (j * width + i) (b.get (x + i) (y + j)) }
  r

end Buffer

/-- The longest prefix of `s` that fits in `width` cells. -/
def truncate (width : Nat) (s : String) : String :=
  (s.foldl (init := ("", 0)) fun (acc, n) c =>
    if n + charWidth c ≤ width then (acc.push c, n + charWidth c) else (acc, width + 1)).1

/-- Break `s` into lines of at most `width` cells, at spaces where it can and inside words
longer than a line. -/
def wrap (width : Nat) (s : String) : List String :=
  if width == 0 then [] else (s.splitOn "\n").flatMap paragraph
where
  paragraph (p : String) : List String :=
    let (lines, cur) := (p.splitOn " ").foldl (init := (([] : List String), "")) fun (lines, cur) word =>
      let joined := if cur.isEmpty then word else cur ++ " " ++ word
      if stringWidth joined ≤ width then (lines, joined)
      else
        let lines := if cur.isEmpty then lines else cur :: lines
        let (lines, rest) := breakWord lines word
        (lines, rest)
    (cur :: lines).reverse
  /-- Lines of a word too long for one, and what is left of it. -/
  breakWord (lines : List String) (word : String) : List String × String :=
    word.foldl (init := (lines, "")) fun (lines, cur) c =>
      if stringWidth (cur.push c) ≤ width then (lines, cur.push c) else (cur :: lines, String.singleton c)

namespace Widget

def empty : Widget := default

/-- Text as it is, one line per line of `s`, clipped to the space given. -/
def str (s : String) : Widget where
  render ctx :=
    let lines := (s.splitOn "\n").take ctx.height
    let width := min ctx.width (lines.foldl (fun n l => max n (stringWidth l)) 0)
    lines.zipIdx.foldl (init := Buffer.blank width lines.length ctx.style) fun b (l, y) =>
      (b.putString 0 y l ctx.style).1

/-- Text wrapped to the width given. -/
def txt (s : String) : Widget where
  hPolicy := .greedy
  render ctx :=
    let lines := (wrap ctx.width s).take ctx.height
    lines.zipIdx.foldl (init := Buffer.blank ctx.width lines.length ctx.style) fun b (l, y) =>
      (b.putString 0 y l ctx.style).1

/-- All the space given, filled with `c`. -/
def fill (c : Char := ' ') : Widget where
  hPolicy := .greedy
  vPolicy := .greedy
  render ctx :=
    let line := String.ofList (List.replicate (ctx.width / max 1 (charWidth c)) c)
    (List.range ctx.height).foldl (init := Buffer.blank ctx.width ctx.height ctx.style) fun b y =>
      (b.putString 0 y line ctx.style).1

/-- Draw `w` and everything in it in style `s`, over the inherited style. -/
def withStyle (s : Style) (w : Widget) : Widget :=
  { w with render := fun ctx => w.render { ctx with style := s.over ctx.style } }

def pad (left top right bottom : Nat) (w : Widget) : Widget :=
  { w with
    render := fun ctx =>
      let inner := w.render { ctx with width := ctx.width - left - right,
                                       height := ctx.height - top - bottom }
      let b := Buffer.blank (min ctx.width (inner.width + left + right))
        (min ctx.height (inner.height + top + bottom)) ctx.style
      b.blit left top inner }

def padAll (n : Nat) (w : Widget) : Widget := pad n n n n w

/-- At most `n` cells wide. -/
def hLimit (n : Nat) (w : Widget) : Widget :=
  { w with hPolicy := .fixed, render := fun ctx => w.render { ctx with width := min n ctx.width } }

/-- At most `n` cells high. -/
def vLimit (n : Nat) (w : Widget) : Widget :=
  { w with vPolicy := .fixed, render := fun ctx => w.render { ctx with height := min n ctx.height } }

/-- Children side by side (`horizontal`) or one above the other. -/
private def box (horizontal : Bool) (ws : List Widget) : Widget where
  hPolicy := if ws.any (·.hPolicy == .greedy) then .greedy else .fixed
  vPolicy := if ws.any (·.vPolicy == .greedy) then .greedy else .fixed
  render ctx := Id.run do
    let policy (w : Widget) := if horizontal then w.hPolicy else w.vPolicy
    let along (b : Buffer) := if horizontal then b.width else b.height
    let across (b : Buffer) := if horizontal then b.height else b.width
    let within (n : Nat) : Context :=
      if horizontal then { ctx with width := n } else { ctx with height := n }
    let mut images : Array Buffer := .replicate ws.length (.blank 0 0)
    let mut left := if horizontal then ctx.width else ctx.height
    for (w, i) in ws.zipIdx do
      if policy w == .fixed then
        let img := w.render (within left)
        images := images.set! i img
        left := left - along img
    let greedy := ws.zipIdx.filter (policy ·.1 == .greedy)
    for ((w, i), k) in greedy.zipIdx do
      let n := left / greedy.length + if k < left % greedy.length then 1 else 0
      images := images.set! i (w.render (within n))
    let length := images.foldl (· + along ·) 0
    let thickness := images.foldl (fun n b => max n (across b)) 0
    let mut b := if horizontal then Buffer.blank length thickness ctx.style
      else Buffer.blank thickness length ctx.style
    let mut pos := 0
    for img in images do
      b := if horizontal then b.blit pos 0 img else b.blit 0 pos img
      pos := pos + along img
    return b

/-- Children side by side. -/
def hBox (ws : List Widget) : Widget := box true ws

/-- Children one above the other. -/
def vBox (ws : List Widget) : Widget := box false ws

/-- A line around `w`, with `label` in its top edge. -/
def borderWithLabel (label : String) (w : Widget) : Widget :=
  { w with
    render := fun ctx =>
      if ctx.width < 2 || ctx.height < 2 then .blank (min ctx.width 2) (min ctx.height 2) ctx.style
      else
        let inner := w.render { ctx with width := ctx.width - 2, height := ctx.height - 2 }
        let (w, h) := (inner.width + 2, inner.height + 2)
        let horizontal := String.ofList (List.replicate (w - 2) '─')
        let b := Buffer.blank w h ctx.style
        let b := (b.putString 0 0 ("┌" ++ horizontal ++ "┐") ctx.style).1
        let b := (b.putString 0 (h - 1) ("└" ++ horizontal ++ "┘") ctx.style).1
        let b := (List.range (h - 2)).foldl (init := b) fun b y =>
          ((b.putString 0 (y + 1) "│" ctx.style).1.putString (w - 1) (y + 1) "│" ctx.style).1
        let b := (b.putString 1 0 (truncate (w - 2) label) ctx.style).1
        b.blit 1 1 inner }

def border (w : Widget) : Widget := borderWithLabel "" w

/-- `w` in the middle of all the space given. -/
def center (w : Widget) : Widget where
  hPolicy := .greedy
  vPolicy := .greedy
  render ctx :=
    let img := w.render ctx
    (Buffer.blank ctx.width ctx.height ctx.style).blit
      ((ctx.width - img.width) / 2) ((ctx.height - img.height) / 2) img

/-- The rows of `w` from `offset` on, in all the space given. -/
def viewport (offset : Nat) (w : Widget) : Widget where
  hPolicy := .greedy
  vPolicy := .greedy
  render ctx :=
    let img := w.render { ctx with height := offset + ctx.height }
    (Buffer.blank ctx.width ctx.height ctx.style).blit 0 0
      (img.crop 0 offset img.width (min ctx.height (img.height - offset)))

/-- The whole frame: `w` drawn into a `width` by `height` screen. -/
def draw (w : Widget) (width height : Nat) : Buffer :=
  (Buffer.blank width height).blit 0 0 (w.render { width, height })

end Widget

end Tessera
