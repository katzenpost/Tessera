/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Bench.Text
import Tessera.Bench.Draw

/-! # Benchmark driver -/

def main (args : List String) : IO UInt32 := do
  (← Tessera.Bench.Text.benches).forM LeanBench.register
  (← Tessera.Bench.Draw.benches).forM LeanBench.register
  LeanBench.runMain args
