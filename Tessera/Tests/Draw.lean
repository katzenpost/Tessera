/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Diff
import Tessera.Tests.Util
import Tessera.Tests.Model

/-! # Styles, buffers, escape sequences and diffs -/

namespace Tessera.Tests.Draw

open Tessera

def sgrTests : TestM Unit := do
  checkEq "plain" "\x1b[0m" (Ansi.sgr {})
  checkEq "bold red" "\x1b[0;1;31m" (Ansi.sgr { bold := true, fg := some .red })
  checkEq "bright on blue" "\x1b[0;92;44m" (Ansi.sgr { fg := some .brightGreen, bg := some .blue })
  checkEq "indexed" "\x1b[0;38;5;208m" (Ansi.sgr { fg := some (.indexed 208) })
  checkEq "rgb background" "\x1b[0;48;2;1;2;3m" (Ansi.sgr { bg := some (.rgb 1 2 3) })
  checkEq "all attributes" "\x1b[0;1;2;3;4;7m"
    (Ansi.sgr { bold := true, dim := true, italic := true, underline := true, reverse := true })
  checkEq "move" "\x1b[3;5H" (Ansi.moveTo 4 2)
  check "over keeps base color" ((Style.fgOf .red).over (Style.bgOf .blue) ==
    { fg := some .red, bg := some .blue })
  check "over replaces color" ((Style.fgOf .red).over (Style.fgOf .blue) == Style.fgOf .red)

def bufferTests : TestM Unit := do
  checkEq "char widths" [1, 2, 2, 0, 0] (['a', '漢', '🦀', '\x07', '́'].map charWidth)
  checkEq "string width" 5 (stringWidth "a漢🦀")
  let (b, x) := (Buffer.blank 5 2).putString 1 0 "ab漢"
  checkEq "put string" [" ab漢", "     "] b.lines
  checkEq "column after" 5 x
  check "continuation" (b.get 4 0).isContinuation
  let (c, _) := (Buffer.blank 4 1).putString 2 0 "a漢"
  checkEq "wide char clipped" ["  a "] c.lines
  let (d, _) := (Buffer.blank 4 1).putString 0 0 "abcdef"
  checkEq "clipped at the edge" ["abcd"] d.lines
  let e := b.set 4 0 { char := 'z' }
  checkEq "overwrite right half" [" ab z", "     "] e.lines
  let f := b.set 3 0 { char := 'z' }
  checkEq "overwrite left half" [" abz ", "     "] f.lines
  let small := (Buffer.blank 2 1).putString 0 0 "xy" |>.1
  checkEq "blit clipped" [" ab漢", "    x"] (b.blit 4 1 small).lines
  check "outside reads blank" (b.get 9 9 == {})

/-- A random buffer: strings of plain and wide characters in a few styles. -/
def randomBuffer (w h : Nat) (r : Rng) : Buffer × Rng := Id.run do
  let styles : Array Style := #[{}, Style.fgOf .red, { bold := true, bg := some (.indexed 17) },
    Style.fgOf (.rgb 1 2 3)]
  let chars := #['a', 'b', ' ', '漢', '🦀', 'é']
  let mut b := Buffer.blank w h
  let mut r := r
  let (n, r1) := r.next 12
  r := r1
  for _ in [0:n] do
    let (x, r2) := r.next w
    let (y, r3) := r2.next h
    let (len, r4) := r3.next 6
    let (si, r5) := r4.next styles.size
    r := r5
    let mut s := ""
    for _ in [0:len] do
      let (ci, r') := r.next chars.size
      r := r'
      s := s.push chars[ci]!
    b := (b.putString x y s styles[si]!).1
  return (b, r)

def diffTests : TestM Unit := do
  let (b, _) := (Buffer.blank 6 2).putString 1 1 "hi"
  checkEq "same buffer, no output" "" (diff (some b) b)
  let b2 := b.set 0 0 { char := 'x' }
  checkEq "one cell" ("\x1b[1;1H" ++ "\x1b[0mx" ++ "\x1b[0m") (diff (some b) b2)
  let b3 := (b.putString 1 1 "yo").1
  checkEq "one run, one move" ("\x1b[2;2H\x1b[0myo\x1b[0m") (diff (some b) b3)
  let b4 := (b.putString 1 1 "hi" (Style.fgOf .red)).1
  checkEq "a style change" ("\x1b[2;2H\x1b[0;31mhi\x1b[0m") (diff (some b) b4)
  check "resize redraws" ((diff (some b) (Buffer.blank 3 3)).startsWith (Ansi.resetStyle ++ Ansi.clearScreen))
  check "first frame shows the buffer" ((Terminal.new 6 2 |>.run (diff none b)).screen == b)
  let mut rng : Rng := ⟨42⟩
  let mut agree := 0
  for _ in [0:300] do
    let (old, r1) := randomBuffer 9 4 rng
    let (new, r2) := randomBuffer 9 4 r1
    rng := r2
    let shown := (Terminal.showing old |>.run (diff (some old) new)).screen
    if shown == new then agree := agree + 1
    else check "diff reproduces the new buffer" false fun _ => s!"{old.lines} → {new.lines}, shown {shown.lines}"
  checkEq "random diffs reproduce the new buffer" 300 agree

end Tessera.Tests.Draw
