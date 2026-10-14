/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Char

/-! # Axioms

The main results depend on no axiom beyond Lean's standard ones. A change that adds one fails
the build. -/

namespace Tessera.Tests.Axioms

open Tessera

/-- info: 'Tessera.Charset.standard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Charset.standard

/-- info: 'Tessera.Charset.cjk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Charset.cjk

end Tessera.Tests.Axioms
