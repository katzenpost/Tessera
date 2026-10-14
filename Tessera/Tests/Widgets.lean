/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Widget
import Tessera.Tests.Util

/-! # Widgets, drawn into small screens -/

namespace Tessera.Tests.Widgets

open Tessera Widget

def drawn (w : Widget CS) (width height : Nat) : List String := (w.draw width height).lines

def tests : TestM Unit := do
  checkEq "str" ["hi  ", "    "] (drawn (str "hi") 4 2)
  checkEq "str lines" ["ab ", "cde"] (drawn (str "ab\ncde") 3 2)
  checkEq "str clipped" ["abc"] (drawn (str "abcdef\nx") 3 1)
  checkEq "wrap" ["one two", "three", "abcdefg", "hi"] (wrap CS 7 "one two three abcdefghi")
  checkEq "wrap newline" ["a", "b c"] (wrap CS 5 "a\nb c")
  checkEq "txt" ["the  ", "quick", "fox  "] (drawn (txt "the quick fox") 5 3)
  checkEq "fill" ["..", ".."] (drawn (fill '.') 2 2)
  checkEq "hBox of fixed" ["ab cd "] (drawn (hBox [str "ab", str " cd"]) 6 1)
  checkEq "fixed first, greedy the rest" ["ab....xy"]
    (drawn (hBox [str "ab", fill '.', str "xy"]) 8 1)
  checkEq "greedy children share" ["aaabb"] (drawn (hBox [fill 'a', fill 'b']) 5 1)
  checkEq "vBox" ["top", "---", "bot"] (drawn (vBox [str "top", vLimit 1 (fill '-'), str "bot"]) 3 3)
  checkEq "vBox greedy share" ["a", "a", "b"] (drawn (vBox [fill 'a', fill 'b']) 1 3)
  check "box policies" (let w : Widget CS := hBox [str "a", txt "b"]; w.hPolicy == .greedy && w.vPolicy == .fixed)
  checkEq "border" ["┌──┐", "│hi│", "└──┘", "    "] (drawn (border (str "hi")) 4 4)
  checkEq "border of greedy" ["┌──┐", "│..│", "└──┘"] (drawn (border (fill '.')) 4 3)
  checkEq "border too small" ["  "] (drawn (border (str "hi")) 2 1)
  checkEq "label" ["┌ab┐", "│..│", "└──┘"] (drawn (borderWithLabel "abcdef" (fill '.')) 4 3)
  checkEq "pad" ["     ", "  x  ", "     "] (drawn (padAll 1 (pad 1 0 0 0 (str "x"))) 5 3)
  checkEq "hLimit" ["..  "] (drawn (hBox [hLimit 2 (fill '.')]) 4 1)
  checkEq "center" ["     ", "  x  ", "     "] (drawn (center (str "x")) 5 3)
  let lines : Widget CS := vBox ((List.range 6).map fun i => str s!"line {i}")
  checkEq "viewport" ["line 2", "line 3"] (drawn (viewport 2 lines) 6 2)
  checkEq "viewport past the end" ["line 5", "      "] (drawn (viewport 5 lines) 6 2)
  checkEq "wide in a box" ["漢|"] (drawn (hBox [str "漢", str "|"]) 3 1)
  let styled := (withStyle (cs := CS) (Style.fgOf .red) (hBox [str "a", withStyle { bold := true } (str "b")])).draw 2 1
  check "style inherited" ((styled.get 0 0).style == Style.fgOf .red)
  check "style layered" ((styled.get 1 0).style == { fg := some .red, bold := true })
  let bg := (withStyle (cs := CS) (Style.bgOf .blue) (border (str "x"))).draw 3 3
  check "border takes the style" ((bg.get 0 0).style == Style.bgOf .blue)
  checkEq "zero size" ([] : List String) (drawn (border (txt "abc")) 0 0)

end Tessera.Tests.Widgets
