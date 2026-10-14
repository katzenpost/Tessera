/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Widget
import Tessera.Tests.Util

/-! # Widgets, drawn into small screens -/

namespace Tessera.Tests.Widgets

open Tessera Widget

def drawn (w : Widget CS .app) (width height : Nat) : List String := (w.draw width height).lines

def tests : TestM Unit := do
  checkEq "str" ["hi  ", "    "] (drawn (str t!"hi") 4 2)
  checkEq "str lines" ["ab ", "cde"] (drawn (strs [t!"ab", t!"cde"]) 3 2)
  checkEq "str clipped" ["abc"] (drawn (strs [t!"abcdef", t!"x"]) 3 1)
  checkEq "wrap" ["one two", "three", "abcdefg", "hi"] (wrap CS 7 "one two three abcdefghi")
  checkEq "wrap newline" ["a", "b c"] (wrap CS 5 "a\nb c")
  checkEq "txt" ["the  ", "quick", "fox  "] (drawn (txt t!"the quick fox") 5 3)
  checkEq "fill" ["..", ".."] (drawn (fill '.') 2 2)
  checkEq "hBox of fixed" ["ab cd "] (drawn (hBox [str t!"ab", str t!" cd"]) 6 1)
  checkEq "fixed first, greedy the rest" ["ab....xy"]
    (drawn (hBox [str t!"ab", fill '.', str t!"xy"]) 8 1)
  checkEq "greedy children share" ["aaabb"] (drawn (hBox [fill 'a', fill 'b']) 5 1)
  checkEq "vBox" ["top", "---", "bot"] (drawn (vBox [str t!"top", vLimit 1 (fill '-'), str t!"bot"]) 3 3)
  checkEq "vBox greedy share" ["a", "a", "b"] (drawn (vBox [fill 'a', fill 'b']) 1 3)
  check "box policies" (let w : Widget CS .app := hBox [str t!"a", txt t!"b"]; w.hPolicy == .greedy && w.vPolicy == .fixed)
  checkEq "border" ["┌──┐", "│hi│", "└──┘", "    "] (drawn (border (str t!"hi")) 4 4)
  checkEq "border of greedy" ["┌──┐", "│..│", "└──┘"] (drawn (border (fill '.')) 4 3)
  checkEq "border too small" ["  "] (drawn (border (str t!"hi")) 2 1)
  checkEq "label" ["┌ab┐", "│..│", "└──┘"] (drawn (borderWithLabel t!"abcdef" (fill '.')) 4 3)
  checkEq "pad" ["     ", "  x  ", "     "] (drawn (padAll 1 (pad 1 0 0 0 (str t!"x"))) 5 3)
  checkEq "hLimit" ["..  "] (drawn (hBox [hLimit 2 (fill '.')]) 4 1)
  checkEq "center" ["     ", "  x  ", "     "] (drawn (center (str t!"x")) 5 3)
  let lines : Widget CS .app := vBox ((List.range 6).map fun i => str (t!"line " ++ .ofNat i))
  checkEq "viewport" ["line 2", "line 3"] (drawn (viewport 2 lines) 6 2)
  checkEq "viewport past the end" ["line 5", "      "] (drawn (viewport 5 lines) 6 2)
  checkEq "wide in a box" ["漢|"] (drawn (hBox [str t!"漢", str t!"|"]) 3 1)
  let styled := (withStyle (cs := CS) (o := .app) (Style.fgOf .red) (hBox [str t!"a", withStyle { bold := true } (str t!"b")])).draw 2 1
  check "style inherited" ((styled.get 0 0).style == Style.fgOf .red)
  check "style layered" ((styled.get 1 0).style == { fg := some .red, bold := true })
  let bg := (withStyle (cs := CS) (o := .app) (Style.bgOf .blue) (border (str t!"x"))).draw 3 3
  check "border takes the style" ((bg.get 0 0).style == Style.bgOf .blue)
  checkEq "zero size" ([] : List String) (drawn (border (txt t!"abc")) 0 0)

end Tessera.Tests.Widgets
