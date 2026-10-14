/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Diff
import Tessera.Untrusted
import Tessera.VT
import Tessera.Widget
import Tessera.Tests.Util

/-! # Text from elsewhere

Random and known-hostile text, filtered and drawn: nothing a terminal would act on reaches a
cell or the output, and widgets beside the text keep their borders where they were drawn. -/

namespace Tessera.Tests.Untrusted

open Tessera Widget Tessera.Untrusted Ident

/-- A character a terminal would act on, or could reorder or hide text by, or whose width is
uncertain. -/
def forbidden (c : Char) : Bool :=
  let n := c.toNat
  n < 0x20 || (0x7F ≤ n && n < 0xA0) || inRanges n [(0x200B, 0x200F), (0x202A, 0x202E),
    (0x2060, 0x2064), (0x2066, 0x2069), (0xFEFF, 0xFEFF), (0x61C, 0x61C), (0xE000, 0xF8FF),
    (0xE0000, 0xE007F), (0xF0000, 0x10FFFF), (0xFE00, 0xFE0F), (0x1F1E6, 0x1F1FF)]

def clean (s : String) : Bool := !s.any forbidden

/-- A character another program's terminal would act on, or reorder text by. -/
def steers (c : Char) : Bool :=
  let n := c.toNat
  (n < 0x20 && c != '\n' && c != '\t') || (0x7F ≤ n && n < 0xA0) ||
    inRanges n [(0x202A, 0x202E), (0x2066, 0x2069), (0x200E, 0x200F), (0x61C, 0x61C)]

def randomChar (g : StdGen) : Char × StdGen :=
  let (kind, g) := randNat g 0 5
  let (n, g) := match kind with
    | 0 => randNat g 0 0x40
    | 1 => randNat g 0x7F 0xA0
    | 2 => randNat g 0x2000 0x2070
    | 3 => randNat g 0x1F000 0x1FAFF
    | 4 => randNat g 0x300 0x370
    | _ => randNat g 0 0x10FFFF
  (Char.ofNat (if (0xD800 ≤ n && n ≤ 0xDFFF) || n > 0x10FFFF then 0x41 else n), g)

def randomString (g : StdGen) (len : Nat) : String × StdGen := Id.run do
  let mut g := g
  let mut s := ""
  for _ in [0:len] do
    let (c, g') := randomChar g
    s := s.push c
    g := g'
  return (s, g)

/-- Payloads that have attacked terminals and the programs in them. -/
def corpus : List (String × String) := [
  ("OSC 52 sets the clipboard", "\x1b]52;c;ZXZpbA==\x07"),
  ("OSC 0 sets the title", "\x1b]0;pwned\x07"),
  ("tmux passthrough", "\x1bPtmux;\x1b\x1b]0;x\x07\x1b\\"),
  ("a one-byte CSI", "\u009b31mred"),
  ("a carriage return overwrites", "safe\rEVIL"),
  ("a paste's end marker", "a\x1b[201~b"),
  ("Trojan Source", "access‮⁦ // admin⁩⁦"),
  ("ZWJ emoji", "👨‍👩‍👧"),
  ("VS16 emoji", "❤️ and 🚀 and ⌚"),
  ("a flag", "🇺🇳"),
  ("Zalgo", "Z" ++ String.ofList (List.replicate 40 '́')),
  ("tag characters", "hi" ++ String.ofList [Char.ofNat 0xE0041, Char.ofNat 0xE0042]),
  ("a private-use glyph", " verified"),
  ("wide text", "全角の文字がたくさん全角の文字がたくさん全角の文字がたくさん"),
  ("a bell", "ding\x07ding"),
  ("DEL", "back\x7Fspace")]

/-- `text` between two bordered panes, as an application might draw a message. -/
def framed (text : List (Text CS .remote)) : Buffer CS 40 6 :=
  (hBox (o := .remote) [hLimit 6 (border (str t!"left")), border (vBox (text.map str ++ [fill])),
    hLimit 7 (border (str t!"right"))]).draw 40 6

/-- The borders between the panes, on every row inside them. -/
def bordersHold (b : Buffer CS 40 6) : Bool :=
  (List.range 4).all fun y => [6, 32].all fun x => (b.get x (y + 1)).char == '│'

def cellsClean (b : Buffer CS 40 6) : Bool :=
  (List.range 6).all fun y => (List.range 40).all fun x =>
    let c := b.get x y
    c.isContinuation || !forbidden c.char

/-- Every escape sequence in `out` is a CSI, as Tessera writes only those. -/
def onlyCsi (out : String) : Bool :=
  let parts := out.splitOn "\x1b"
  (parts.drop 1).all (·.startsWith "[") && !out.any fun c => 0x80 ≤ c.toNat && c.toNat < 0xA0

def tests : TestM Unit := do
  checkEq "widths" [1, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0]
    (['a', '漢', '🦀', '🚀', '⌚', '\x07', '́', '‮', '‍', '️', '­'].map charWidth)
  checkEq "ambiguous widths in a CJK locale" [1, 2, 2, 2, 2]
    (['a', 'α', 'Ж', '→', '─'].map Charset.cjk.width)
  checkEq "and outside one" [1, 1, 1, 1, 1] (['a', 'α', 'Ж', '→', '─'].map Charset.standard.width)
  check "the allowlist refuses controls, bidi, invisibles and marks"
    (['\x1b', '\u009b', '\x7f', '‮', '⁦', '​', '﻿', '́'].all (!isPrintable ·))
  let mut g := mkStdGen 2026
  let mut ok := true
  for _ in [0:2000] do
    let (len, g') := randNat g 0 80
    let (s, g'') := randomString g' len
    g := g''
    if !(clean (line (cs := CS) s).text && (lines (cs := CS) s).1.all (clean ·.text)) then ok := false
  check "random text never leaves a forbidden character" ok
  for (what, payload) in corpus do
    let b := framed (lines s!"{payload}\n{payload} and {payload}").1
    check s!"{what}: nothing forbidden reaches a cell" (cellsClean b)
    check s!"{what}: the panes keep their borders" (bordersHold b)
    check s!"{what}: the output writes nothing but its own CSI" (onlyCsi (redraw b))
    check s!"{what}: nothing that steers is passed on"
      (!(withoutControls payload).1.any steers)
  check "the model reads OSC 52"
    ([VT.Token.osc "52;c;ZXZpbA==".toList] == VT.tokens "\x1b]52;c;ZXZpbA==\x07".toList)
  check "the model reads a one-byte CSI"
    ([VT.Token.csi "31".toList [] 'm', .print 'r'] == VT.tokens "\u009b31mr".toList)
  check "the model reads tmux passthrough as a control string"
    ([VT.Token.str 'P' "tmux;".toList] == (VT.tokens "\x1bPtmux;\x1b\\".toList).take 1)
  for (what, payload) in corpus do
    let steersTerminal := payload.any fun c => c.toNat < 0x20 || (0x7F ≤ c.toNat && c.toNat < 0xA0)
    if steersTerminal then
      check s!"{what}: the model sees more than printing in the payload"
        ((VT.tokens payload.toList).any (!·.isPrint))
    check s!"{what}: the model sees only printing once filtered"
      ((VT.tokens (line (cs := CS) payload).text.toList).all (·.isPrint))
  checkEq "controls show as Control Pictures" "␛]0;x␇" (line (cs := CS) "\x1b]0;x\x07").text
  checkEq "a newline in one line shows" "a␊b" (line (cs := CS) "a\nb").text
  checkEq "lines are capped" 20 (lines (cs := CS) (String.intercalate "\n" (List.replicate 30 "x"))).1.length
  checkEq "marks are capped" 1 ((line (cs := CS) ("e" ++ String.ofList (List.replicate 9 '́'))).text.toList.filter (· == '␦')).length
  checkEq "paste markers go" "ab" (pasted "a\x1b[201~b\x1b[200~").text
  checkEq "a marker hidden in a marker goes too" "[201~" (pasted "\x1b[2\x1b[201~01~").text
  check "no control character becomes a glyph"
    ((List.range 0xA0).all fun n => n ≥ 0x20 && n != 0x7F && n < 0x80 ||
      (Glyph.ofChar? (Char.ofNat n) : Option (Glyph CS)).isNone)
  let name (s : String) : Ident CS := ofRemote s
  check "look-alike names share a skeleton" (skeleton (name "Alice") == skeleton (name "аlicе"))
  check "names that differ do not" (skeleton (name "alice") != skeleton (name "alicia"))
  check "mixed scripts" (mixedScript (name "pаypal") && !mixedScript (name "paypal"))
  checkEq "a name cannot wear a badge" "alice ␦" (name "alice 🔒").text.text
  checkEq "numbers as text" "1234" (Text.ofNat (cs := CS) 1234).text
  checkEq "app text is drawn as written" ["┌ok┐"] ((str (cs := CS) (o := .app) t!"┌ok┐").draw 4 1).lines

end Tessera.Tests.Untrusted
