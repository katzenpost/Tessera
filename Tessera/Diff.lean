/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Buffer
import Tessera.Ansi

/-! # Drawing a frame

`diffOps old new` is the list of operations that turns a terminal showing `old` into one showing
`new`, two frames of the same size. It writes only the cells that changed, moving the cursor once
per run of them and changing the style only when it differs from the last cell written.
`redrawOps new` clears the screen and draws all of `new`. `diff` and `redraw` are their output,
and a terminal reads that output as nothing but those operations (`diff_own`, `redraw_own`). -/

namespace Tessera

open Ansi

variable {cs : Charset}

structure DiffState (cs : Charset) where
  ops : Array (Op cs) := #[]
  /-- Where the terminal's cursor is, if known. -/
  cursor : Option (Nat × Nat) := none
  style : Option Style := none

namespace DiffState

/-- Write `g`, `width` cells wide, at `(x, y)`. -/
def write (s : DiffState cs) (x y : Nat) (g : Glyph cs) (width : Nat) (style : Style) :
    DiffState cs :=
  let move : List (Op cs) := if s.cursor = some (x, y) then [] else [.moveTo x y]
  let sgr : List (Op cs) := if s.style = some style then [] else [.sgr style]
  { ops := s.ops ++ (move ++ sgr ++ [Op.print g]).toArray, cursor := some (x + width, y),
    style := some style }

end DiffState

/-- Write the cells of a row, from column `x`, that differ from those of `old` in the same
place, or all of them if `all`. A two-cell glyph is written when either of its halves changed. -/
def drawRow (y : Nat) (all : Bool) :
    (x : Nat) → (new old : List (Cell cs)) → DiffState cs → DiffState cs
  | x, .glyph g s :: .wideRight :: ns, o₁ :: o₂ :: os, st =>
    let st := if all || .glyph g s != o₁ || .wideRight != o₂ then st.write x y g 2 s else st
    drawRow y all (x + 2) ns os st
  | x, c :: ns, o :: os, st =>
    let st := if all || c != o then
      match c with
      | .glyph g s => st.write x y g g.width s
      | .blank s => st.write x y .space 1 s
      | .wideRight => st
      else st
    drawRow y all (x + 1) ns os st
  | _, _, _, st => st

/-- Draw row `y`, unless only what changed is drawn and nothing in it did. -/
def drawRowOf {w h : Nat} (old new : Buffer cs w h) (all : Bool) (s : DiffState cs) (y : Nat) :
    DiffState cs :=
  let n := new.rows[y]?.map (·.cells) |>.getD []
  let o := old.rows[y]?.map (·.cells) |>.getD []
  if all = false ∧ Cell.listBeq n o then s else drawRow y all 0 n o s

def drawRows {w h : Nat} (old new : Buffer cs w h) (all : Bool) (start : DiffState cs) :
    Array (Op cs) :=
  ((List.range h).foldl (init := start) (drawRowOf old new all)).ops

/-- The operations that turn a terminal showing `old` into one showing `new`. -/
def diffOps {w h : Nat} (old new : Buffer cs w h) : List (Op cs) :=
  let ops := drawRows old new false {}
  if ops.isEmpty then [] else ops.toList ++ [.sgr {}]

/-- The operations that clear the screen and draw all of `new`. -/
def redrawOps {w h : Nat} (new : Buffer cs w h) : List (Op cs) :=
  (drawRows new new true { ops := #[.sgr {}, .clear] }).toList ++ [.sgr {}]

def diff {w h : Nat} (old new : Buffer cs w h) (p : Placement := .fullscreen) : String :=
  encode (diffOps old new) p

def redraw {w h : Nat} (new : Buffer cs w h) (p : Placement := .fullscreen) : String :=
  encode (redrawOps new) p

/-- A terminal reads a frame's output as printed characters and Tessera's own control sequences,
and nothing else. -/
theorem diff_own {w h : Nat} (old new : Buffer cs w h) (p : Placement) :
    ∀ t ∈ VT.tokens (diff old new p).toList, Own t :=
  output_own _ p

theorem redraw_own {w h : Nat} (new : Buffer cs w h) (p : Placement) :
    ∀ t ∈ VT.tokens (redraw new p).toList, Own t :=
  output_own _ p

end Tessera
