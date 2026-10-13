/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Buffer
import Tessera.Ansi

/-! # Drawing a frame

`diff old new` is the output that turns a terminal showing `old` into one showing `new`. It
writes only the cells that changed, moving the cursor once per run of them and changing the style
only when it differs from the last cell written. -/

namespace Tessera

structure DiffState where
  out : String := ""
  /-- Where the terminal's cursor is, if known. -/
  cursor : Option (Nat × Nat) := none
  style : Option Style := none

namespace DiffState

def write (s : DiffState) (x y : Nat) (c : Cell) : DiffState := Id.run do
  let mut s := s
  if s.cursor != some (x, y) then
    s := { s with out := s.out ++ Ansi.moveTo x y }
  if s.style != some c.style then
    s := { s with out := s.out ++ Ansi.sgr c.style, style := some c.style }
  -- A cell holds a character to draw. One that takes no cell, such as a control character put
  -- there with `Buffer.set`, would act on the terminal or move the cursor; it is drawn as `␦`.
  let ch := if charWidth c.char == 0 then '␦' else c.char
  { s with out := s.out.push ch, cursor := some (x + charWidth ch, y) }

end DiffState

/-- Write the cells of row `y` for which `changed` holds. -/
def drawRow (b : Buffer) (y : Nat) (changed : Nat → Bool) (s : DiffState) : DiffState :=
  (List.range b.width).foldl (init := s) fun s x =>
    let c := b.get x y
    if c.isContinuation || !changed x then s else s.write x y c

/-- The output that turns a terminal showing `old` into one showing `new`; with no `old`, or one
of another size, it clears the screen and draws all of `new`. -/
def diff (old : Option Buffer) (new : Buffer) : String :=
  let full := match old with
    | some o => o.width != new.width || o.height != new.height
    | none => true
  let changed (y x : Nat) : Bool :=
    full || match old with
      | none => true
      | some o =>
        new.get x y != o.get x y
          -- a double-width character whose right half changed is drawn again
          || ((new.get (x + 1) y).isContinuation && new.get (x + 1) y != o.get (x + 1) y)
  let start : DiffState := if full then { out := Ansi.resetStyle ++ Ansi.clearScreen } else {}
  let s := (List.range new.height).foldl (init := start) fun s y => drawRow new y (changed y) s
  if s.out.isEmpty then "" else s.out ++ Ansi.resetStyle

end Tessera
