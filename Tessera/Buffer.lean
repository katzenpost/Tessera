/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Style

/-! # Screen buffers

A buffer is a grid of cells. A double-width character, such as a CJK ideograph or an emoji, fills
its own cell and the one to its right, which holds `Cell.continuation`. -/

namespace Tessera

/-- How many cells `c` takes: 0 for control and combining characters, which are not drawn; 2 for
double-width characters; 1 for the rest. -/
def charWidth (c : Char) : Nat :=
  let n := c.toNat
  if n < 0x20 || (0x7F ≤ n && n < 0xA0) then 0
  else if (0x300 ≤ n && n < 0x370) || (0x200B ≤ n && n < 0x2010) || n == 0xFE0F then 0
  else if wide n then 2
  else 1
where
  wide (n : Nat) : Bool :=
    [(0x1100, 0x115F), (0x2E80, 0x303E), (0x3041, 0x33FF), (0x3400, 0x4DBF), (0x4E00, 0x9FFF),
     (0xA000, 0xA4CF), (0xAC00, 0xD7A3), (0xF900, 0xFAFF), (0xFE30, 0xFE4F), (0xFF00, 0xFF60),
     (0xFFE0, 0xFFE6), (0x1F300, 0x1F64F), (0x1F900, 0x1F9FF), (0x20000, 0x3FFFD)].any
      fun (lo, hi) => lo ≤ n && n ≤ hi

/-- How many cells `s` takes. -/
def stringWidth (s : String) : Nat :=
  s.foldl (fun n c => n + charWidth c) 0

structure Cell where
  char : Char := ' '
  style : Style := {}
  deriving DecidableEq, Repr, Inhabited

namespace Cell

/-- The right half of a double-width character. -/
def continuation (style : Style := {}) : Cell := { char := '\x00', style }

def isContinuation (c : Cell) : Bool := c.char == '\x00'

end Cell

structure Buffer where
  width : Nat
  height : Nat
  /-- Row by row, `width * height` of them. -/
  cells : Array Cell
  deriving DecidableEq, Repr, Inhabited

namespace Buffer

def blank (width height : Nat) (style : Style := {}) : Buffer :=
  { width, height, cells := .replicate (width * height) { style } }

def get (b : Buffer) (x y : Nat) : Cell :=
  if x < b.width && y < b.height then b.cells[y * b.width + x]?.getD {} else {}

/-- Replace one cell, outside the buffer doing nothing. -/
private def put (b : Buffer) (x y : Nat) (c : Cell) : Buffer :=
  if x < b.width && y < b.height then { b with cells := b.cells.set! (y * b.width + x) c } else b

/-- Set a cell. Overwriting half of a double-width character blanks its other half. -/
def set (b : Buffer) (x y : Nat) (c : Cell) : Buffer := Id.run do
  let mut b := b
  let old := b.get x y
  if old.isContinuation && x > 0 then
    b := b.put (x - 1) y { style := (b.get (x - 1) y).style }
  if charWidth old.char == 2 && (b.get (x + 1) y).isContinuation then
    b := b.put (x + 1) y { style := (b.get (x + 1) y).style }
  b.put x y c

/-- Write `s` from column `x` of row `y`, clipped at the right edge, and return the column after
it. A double-width character that does not fit is not drawn. -/
def putString (b : Buffer) (x y : Nat) (s : String) (style : Style := {}) : Buffer × Nat :=
  s.foldl (init := (b, x)) fun (b, x) c =>
    match charWidth c with
    | 0 => (b, x)
    | 1 => if x < b.width then (b.set x y { char := c, style }, x + 1) else (b, x)
    | _ =>
      if x + 1 < b.width then
        ((b.set x y { char := c, style }).set (x + 1) y (.continuation style), x + 2)
      else (b, x)

/-- Copy `src` onto `b` with its top left corner at `(x, y)`, clipped at the edges. -/
def blit (b : Buffer) (x y : Nat) (src : Buffer) : Buffer := Id.run do
  let mut b := b
  for j in [0:src.height] do
    for i in [0:src.width] do
      b := b.put (x + i) (y + j) (src.get i j)
  -- A double-width character cut by the right edge
  if x + src.width ≤ b.width && x + src.width > 0 then
    for j in [0:src.height] do
      if (b.get (x + src.width) (y + j)).isContinuation
          && charWidth (b.get (x + src.width - 1) (y + j)).char != 2 then
        b := b.put (x + src.width) (y + j) { style := (b.get (x + src.width) (y + j)).style }
  b

/-- The characters of row `y`, without continuations. -/
def row (b : Buffer) (y : Nat) : String :=
  String.ofList <| (List.range b.width).filterMap fun x =>
    let c := b.get x y
    if c.isContinuation then none else some c.char

/-- The buffer's text, one line per row. -/
def lines (b : Buffer) : List String := (List.range b.height).map b.row

end Buffer

end Tessera
