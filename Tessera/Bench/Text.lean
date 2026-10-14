/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Untrusted
import Tessera.VT
import LeanBench

/-! # Filtering untrusted text at growing sizes

Inputs are read from refs so the compiler cannot hoist the work out of the timed action. -/

namespace Tessera.Bench.Text

private abbrev CS : Charset := .standard

private def cfg : LeanBench.BenchConfig := { suite := some "text", samples := 10, warmup := 1 }

def sizes : List (Nat × String) := [(256, "256B"), (4096, "4KiB"), (65536, "64KiB")]

/-- `n` characters cycling through `pattern`. -/
def sample (pattern : String) (n : Nat) : String :=
  let p := pattern.toList.toArray
  String.ofList ((List.range n).map fun i => p[i % p.size]!)

def inputs : List (String × String) :=
  [("ascii", "the quick brown fox jumps over the lazy dog "),
   ("mixed", "héllo 漢字 🦀 é "),
   ("hostile", "\x1b]0;pwned\x07\x1b[2J‮​\x9b31m")]

def benches : IO (Array LeanBench.Bench) := do
  let out ← IO.mkRef ""
  let toks ← IO.mkRef (0 : Nat)
  let mut bs := #[]
  for (size, label) in sizes do
    for (kind, pattern) in inputs do
      let s ← IO.mkRef (sample pattern size)
      bs := bs.push { name := s!"line {kind} {label}", config := cfg,
                      action := do out.set (Untrusted.line (cs := CS) (← s.get)).text }
      bs := bs.push { name := s!"tokens {kind} {label}", config := cfg,
                      action := do toks.set (VT.tokens (← s.get).toList).length }
    let s ← IO.mkRef (sample "one line of a message\n" size)
    bs := bs.push { name := s!"lines {label}", config := cfg,
                    action := do out.set (toString (Untrusted.lines (cs := CS) (← s.get)).val.length) }
    let p ← IO.mkRef (sample "\x1b[200~text\x1b[201~" size)
    bs := bs.push { name := s!"pasted {label}", config := cfg,
                    action := do out.set (Untrusted.pasted (← p.get)).text }
  pure bs

end Tessera.Bench.Text
