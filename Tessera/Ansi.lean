/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Style

/-! # ANSI escape sequences -/

namespace Tessera.Ansi

def csi (s : String) : String := "\x1b[" ++ s

/-- Move the cursor to column `x`, row `y`, counting from 0. -/
def moveTo (x y : Nat) : String := csi s!"{y + 1};{x + 1}H"

def clearScreen : String := csi "2J"

def resetStyle : String := csi "0m"

def colorCodes (fg : Bool) : Color → List String
  | .default => [if fg then "39" else "49"]
  | .ansi n =>
    if n.val < 8 then [toString ((if fg then 30 else 40) + n.val)]
    else [toString ((if fg then 90 else 100) + n.val - 8)]
  | .indexed n => [if fg then "38" else "48", "5", toString n]
  | .rgb r g b => [if fg then "38" else "48", "2", toString r, toString g, toString b]

/-- Select graphic rendition: reset, then set everything `s` sets. -/
def sgr (s : Style) : String :=
  let attrs := [(s.bold, "1"), (s.dim, "2"), (s.italic, "3"), (s.underline, "4"), (s.reverse, "7")]
  let codes := "0" :: attrs.filterMap (fun (on, c) => if on then some c else none)
    ++ (s.fg.map (colorCodes true)).getD [] ++ (s.bg.map (colorCodes false)).getD []
  csi (";".intercalate codes ++ "m")

end Tessera.Ansi
