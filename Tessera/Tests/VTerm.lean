/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Tests.Draw
import Tessera.Tests.Untrusted

/-! # Tessera's output on libvterm

The proofs about drawing assume one thing of the terminal, `Emulator.agrees`: that it gives each
character the charset allows as many cells as the charset says. This checks that assumption
against a real terminal emulator, libvterm, through `tests/vterm/vterm_screen.c`:

* every character `Charset.standard` allows is given the width the charset gives it;
* random frames, each drawn over the last, on the whole screen and inline, show as they are;
* the hostile corpus, drawn in a frame, shows as the frame and sets no title.

A character libvterm measures differently is a counterexample to the assumption, and is named. -/

namespace Tessera.Tests.VTerm

open Tessera

/-- Run the shim with `args`, `input` on its standard input. -/
def shim (path : String) (args : Array String) (input : String) : IO String := do
  let child ← IO.Process.spawn { cmd := path, args, stdin := .piped, stdout := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr input
  stdin.flush
  let out ← IO.asTask child.stdout.readToEnd
  let _ ← child.wait
  IO.ofExcept out.get

def screen (path : String) (w h : Nat) (out : String) : IO (List String × Option String) := do
  let lines := (← shim path #["screen", toString w, toString h] out).splitOn "\n" |>.filter (· ≠ "")
  let title := lines.find? (·.startsWith "#title ") |>.map (·.drop 7 |>.toString)
  return (lines.filter (!·.startsWith "#title "), title)

/-- `n` as `U+XXXX`. -/
def codePoint (n : Nat) : String :=
  let h := String.ofList (Nat.toDigits 16 n) |>.toUpper
  "U+" ++ String.ofList (List.replicate (4 - min 4 h.length) '0') ++ h

/-- Runs of consecutive code points, as `(first, last)`. -/
def runs : List Nat → List (Nat × Nat)
  | [] => []
  | n :: r =>
    match runs r with
    | (a, b) :: rest => if n + 1 = a then (n, b) :: rest else (n, n) :: (a, b) :: rest
    | [] => [(n, n)]

def widthTests (path : String) : TestM Unit := do
  let cs := Charset.standard
  let chars := (List.range 0x110000).filterMap fun n =>
    let c := Char.ofNat n
    if c.toNat == n && cs.Printable c then some c else none
  let out ← shim path #["widths"] (String.intercalate "\n" (chars.map String.singleton) ++ "\n")
  let got := (out.splitOn "\n").filter (· ≠ "") |>.map String.toNat!
  checkEq "libvterm measured every character" chars.length got.length
  let wrong := (chars.zip got).filter fun (c, n) => cs.width c != n
  let byWidth (n : Nat) := runs (wrong.filter (·.2 == n) |>.map (·.1.toNat))
  let fmt (rs : List (Nat × Nat)) := ", ".intercalate (rs.take 40 |>.map fun (a, b) =>
    if a == b then codePoint a else codePoint a ++ "–" ++ codePoint b)
  check s!"libvterm agrees on the width of all {chars.length} printable characters" wrong.isEmpty
    fun _ => s!"{wrong.length} disagree. libvterm gives 1 cell to {fmt (byWidth 1)}; " ++
      s!"2 cells to {fmt (byWidth 2)}"

def frameTests (path : String) : TestM Unit := do
  let mut rng : Rng := ⟨7⟩
  let inl := Ansi.Placement.inline 5
  let mut old : Buffer Charset.standard 12 5 := .blank 12 5
  let mut full := redraw old
  let mut inline := Ansi.encode (cs := Charset.standard) [.enterInline 5] inl ++ redraw old inl
  let mut agree := 0
  for i in [0:60] do
    let (new, r) := Draw.randomBuffer (cs := Charset.standard) 12 5 rng
    rng := r
    full := full ++ diff old new
    inline := inline ++ diff old new inl
    let (a, _) ← screen path 12 5 full
    let (b, _) ← screen path 12 5 inline
    if a == new.lines && b == new.lines then agree := agree + 1
    else check s!"frame {i} shows as drawn" false fun _ =>
      s!"drawn {new.lines}, libvterm shows {a} on the whole screen and {b} inline"
    old := new
  checkEq "random frames show on libvterm as drawn" 60 agree

def corpusTests (path : String) : TestM Unit := do
  for (what, payload) in Untrusted.corpus do
    let b := Untrusted.framed (Untrusted.lines (cs := CS) s!"{payload}\n{payload} and {payload}").1
    let (shown, title) ← screen path 40 6 (redraw b)
    check s!"{what}: libvterm shows the frame as drawn" (shown == b.lines) fun _ =>
      s!"drawn {b.lines}, shown {shown}"
    check s!"{what}: no title is set" title.isNone

def main (args : List String) : IO UInt32 := do
  let path := args.headD "./.lake/build/bin/vterm_screen"
  let results ← [("libvterm widths", widthTests path), ("libvterm frames", frameTests path),
    ("libvterm corpus", corpusTests path)].mapM fun (n, t) => runSuite n t
  return if results.all id then 0 else 1

end Tessera.Tests.VTerm

def main (args : List String) : IO UInt32 := Tessera.Tests.VTerm.main args
