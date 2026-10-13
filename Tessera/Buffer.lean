/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Style

/-! # Screen buffers

A buffer is a grid of cells. A double-width character, such as a CJK ideograph or an emoji, fills
its own cell and the one to its right, which holds `Cell.continuation`. -/

namespace Tessera

/-- Characters that take no cell: controls, which a terminal would act on rather than draw;
format characters, which reorder or hide text (bidi controls, zero-width spaces and joiners, word
joiners, the byte order mark, tag characters) or pick a glyph's presentation (variation
selectors); and combining marks, which a terminal draws over the character before them. None of
them is ever drawn. -/
def zeroWidth (n : Nat) : Bool :=
  n < 0x20 || (0x7F ≤ n && n < 0xA0) || n == 0xAD ||
  [(0x300, 0x36F), (0x483, 0x489), (0x591, 0x5BD), (0x5BF, 0x5BF), (0x5C1, 0x5C2),
   (0x5C4, 0x5C5), (0x5C7, 0x5C7), (0x600, 0x605), (0x610, 0x61A), (0x61C, 0x61C),
   (0x64B, 0x65F), (0x670, 0x670), (0x6D6, 0x6DD), (0x6DF, 0x6E4), (0x6E7, 0x6E8),
   (0x6EA, 0x6ED), (0x70F, 0x70F), (0x711, 0x711), (0x730, 0x74A), (0x900, 0x902),
   (0x93A, 0x93A), (0x93C, 0x93C), (0x941, 0x948), (0x94D, 0x94D), (0x951, 0x957),
   (0x962, 0x963), (0xE31, 0xE31), (0xE34, 0xE3A), (0xE47, 0xE4E), (0x1160, 0x11FF),
   (0x180B, 0x180F), (0x1AB0, 0x1AFF), (0x1DC0, 0x1DFF), (0x200B, 0x200F), (0x2028, 0x202E),
   (0x2060, 0x206F), (0x20D0, 0x20FF), (0xFE00, 0xFE0F), (0xFE20, 0xFE2F), (0xFEFF, 0xFEFF),
   (0xFFF9, 0xFFFB), (0x1D167, 0x1D169), (0x1D173, 0x1D182), (0xE0000, 0xE0FFF)].any
    fun (lo, hi) => lo ≤ n && n ≤ hi

/-- Characters two cells wide: Unicode's East Asian Wide and Fullwidth ones, as terminals take
them from `wcwidth`, CJK and the emoji drawn as pictures among them. -/
def doubleWidth (n : Nat) : Bool :=
  [(0x1100, 0x115F), (0x231A, 0x231B), (0x2329, 0x232A), (0x23E9, 0x23EC), (0x23F0, 0x23F0),
   (0x23F3, 0x23F3), (0x25FD, 0x25FE), (0x2614, 0x2615), (0x2648, 0x2653), (0x267F, 0x267F),
   (0x2693, 0x2693), (0x26A1, 0x26A1), (0x26AA, 0x26AB), (0x26BD, 0x26BE), (0x26C4, 0x26C5),
   (0x26CE, 0x26CE), (0x26D4, 0x26D4), (0x26EA, 0x26EA), (0x26F2, 0x26F3), (0x26F5, 0x26F5),
   (0x26FA, 0x26FA), (0x26FD, 0x26FD), (0x2705, 0x2705), (0x270A, 0x270B), (0x2728, 0x2728),
   (0x274C, 0x274C), (0x274E, 0x274E), (0x2753, 0x2755), (0x2757, 0x2757), (0x2795, 0x2797),
   (0x27B0, 0x27B0), (0x27BF, 0x27BF), (0x2B1B, 0x2B1C), (0x2B50, 0x2B50), (0x2B55, 0x2B55),
   (0x2E80, 0x303E), (0x3041, 0x33FF), (0x3400, 0x4DBF), (0x4E00, 0x9FFF), (0xA000, 0xA4CF),
   (0xA960, 0xA97F), (0xAC00, 0xD7A3), (0xF900, 0xFAFF), (0xFE10, 0xFE19), (0xFE30, 0xFE6F),
   (0xFF00, 0xFF60), (0xFFE0, 0xFFE6), (0x16FE0, 0x16FE4), (0x17000, 0x18CFF),
   (0x1B000, 0x1B2FF), (0x1F004, 0x1F004), (0x1F0CF, 0x1F0CF), (0x1F18E, 0x1F18E),
   (0x1F191, 0x1F19A), (0x1F200, 0x1F202), (0x1F210, 0x1F23B), (0x1F240, 0x1F248),
   (0x1F250, 0x1F251), (0x1F260, 0x1F265), (0x1F300, 0x1F320), (0x1F32D, 0x1F335),
   (0x1F337, 0x1F37C), (0x1F37E, 0x1F393), (0x1F3A0, 0x1F3CA), (0x1F3CF, 0x1F3D3),
   (0x1F3E0, 0x1F3F0), (0x1F3F4, 0x1F3F4), (0x1F3F8, 0x1F43E), (0x1F440, 0x1F440),
   (0x1F442, 0x1F4FC), (0x1F4FF, 0x1F53D), (0x1F54B, 0x1F54E), (0x1F550, 0x1F567),
   (0x1F57A, 0x1F57A), (0x1F595, 0x1F596), (0x1F5A4, 0x1F5A4), (0x1F5FB, 0x1F64F),
   (0x1F680, 0x1F6C5), (0x1F6CC, 0x1F6CC), (0x1F6D0, 0x1F6D2), (0x1F6D5, 0x1F6D7),
   (0x1F6DC, 0x1F6DF), (0x1F6EB, 0x1F6EC), (0x1F6F4, 0x1F6FC), (0x1F7E0, 0x1F7EB),
   (0x1F7F0, 0x1F7F0), (0x1F90C, 0x1F93A), (0x1F93C, 0x1F945), (0x1F947, 0x1F9FF),
   (0x1FA70, 0x1FA7C), (0x1FA80, 0x1FA89), (0x1FA8F, 0x1FAC6), (0x1FACE, 0x1FADC),
   (0x1FADF, 0x1FAE9), (0x1FAF0, 0x1FAF8), (0x20000, 0x2FFFD), (0x30000, 0x3FFFD)].any
    fun (lo, hi) => lo ≤ n && n ≤ hi

/-- How many cells `c` takes: 0 for the characters `zeroWidth` names, which are not drawn; 2 for
double-width characters; 1 for the rest. East Asian ambiguous-width characters take one cell, as
terminals outside CJK locales draw them. -/
def charWidth (c : Char) : Nat :=
  let n := c.toNat
  if zeroWidth n then 0 else if doubleWidth n then 2 else 1

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
