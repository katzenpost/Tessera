/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Tests.Draw
import Tessera.Tests.Widgets
import Tessera.Tests.AppLoop
import Tessera.Tests.Untrusted
import Tessera.Tests.Axioms
import Tessera.Tests.Rejects
import Tessera.Tests.TrustedPath

open Tessera.Tests

def main : IO UInt32 := do
  let results ← [
    ("sgr", Draw.sgrTests),
    ("buffer", Draw.bufferTests),
    ("diff", Draw.diffTests),
    ("widgets", Widgets.tests),
    ("app", AppLoop.tests),
    ("untrusted", Untrusted.tests),
    ("trusted path", TrustedPath.tests)].mapM fun (n, t) => runSuite n t
  return if results.all id then 0 else 1
