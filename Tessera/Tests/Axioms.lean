/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Widget

/-! # Axioms

The main results depend on no axiom beyond Lean's standard ones. A change that adds one fails
the build. -/

namespace Tessera.Tests.Axioms

open Tessera

/-- info: 'Tessera.Charset.standard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Charset.standard

/-- info: 'Tessera.Charset.cjk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Charset.cjk

/-- info: 'Tessera.Row.splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Row.splice

/-- info: 'Tessera.Row.slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Row.slice

/-- info: 'Tessera.Widget.hBox' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Widget.hBox

/-- info: 'Tessera.Widget.borderWithLabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Widget.borderWithLabel

end Tessera.Tests.Axioms
