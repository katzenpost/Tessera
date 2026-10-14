/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Buffer
import Tessera.Ansi

/-! # Drawing a frame

`diff old new` is the output that turns a terminal showing `old` into one showing `new`, two
frames of the same size. It writes only the cells that changed, moving the cursor once per run
of them and changing the style only when it differs from the last cell written. `redraw new`
clears the screen and draws all of `new`. -/

namespace Tessera

variable {cs : Charset}

structure DiffState where
  out : String := ""
  /-- Where the terminal's cursor is, if known. -/
  cursor : Option (Nat × Nat) := none
  style : Option Style := none

namespace DiffState

/-- Write `ch`, `width` cells wide, at `(x, y)`. -/
def write (s : DiffState) (x y : Nat) (ch : Char) (width : Nat) (style : Style) : DiffState := Id.run do
  let mut s := s
  if s.cursor != some (x, y) then
    s := { s with out := s.out ++ Ansi.moveTo x y }
  if s.style != some style then
    s := { s with out := s.out ++ Ansi.sgr style, style := some style }
  { s with out := s.out.push ch, cursor := some (x + width, y) }

end DiffState

/-- Write the cells of a row, from column `x`, that differ from those of `old` in the same
place, or all of them if `all`. A two-cell glyph is written when either of its halves changed. -/
def drawRow (y : Nat) (all : Bool) : (x : Nat) → (new old : List (Cell cs)) → DiffState → DiffState
  | x, .glyph g s :: .wideRight s' :: ns, o₁ :: o₂ :: os, st =>
    let st := if all || .glyph g s != o₁ || .wideRight s' != o₂ then st.write x y g.char 2 s else st
    drawRow y all (x + 2) ns os st
  | x, c :: ns, o :: os, st =>
    let st := if all || c != o then
      match c with
      | .glyph g s => st.write x y g.char g.width s
      | .blank s => st.write x y ' ' 1 s
      | .wideRight _ => st
      else st
    drawRow y all (x + 1) ns os st
  | _, _, _, st => st

private def drawRows {w h : Nat} (old new : Buffer cs w h) (all : Bool) (start : DiffState) : String :=
  let s := (List.range h).foldl (init := start) fun s y =>
    drawRow y all 0 (new.rows[y]?.map (·.cells) |>.getD []) (old.rows[y]?.map (·.cells) |>.getD []) s
  if s.out.isEmpty then "" else s.out ++ Ansi.resetStyle

/-- The output that turns a terminal showing `old` into one showing `new`. -/
def diff {w h : Nat} (old new : Buffer cs w h) : String := drawRows old new false {}

/-- The output that clears the screen and draws all of `new`. -/
def redraw {w h : Nat} (new : Buffer cs w h) : String :=
  drawRows new new true { out := Ansi.resetStyle ++ Ansi.clearScreen }

end Tessera
