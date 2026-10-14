/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Widget
import Tessera.Untrusted
import Tessera.Terminal
import Tessera.TrustedPath
import Tessera.Input
import Tessera.ListView
import Tessera.Table
import Tessera.Consent

/-! # Axioms

The main results depend on no axiom beyond Lean's standard ones. A change that adds one fails
the build. -/

namespace Tessera.Tests.Axioms

open Tessera Untrusted

/-- info: 'Tessera.Charset.standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Charset.standard

/-- info: 'Tessera.Charset.cjk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Charset.cjk

/-- info: 'Tessera.Row.splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Row.splice

/-- info: 'Tessera.Row.slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Row.slice

/-- info: 'Tessera.Widget.hBox' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Widget.hBox

/-- info: 'Tessera.Widget.borderWithLabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Widget.borderWithLabel

/-- info: 'Tessera.Untrusted.line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms line

/-- info: 'Tessera.Untrusted.filterChars_marksOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms filterChars_marksOk

/-- info: 'Tessera.Text.append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Text.append

/-- info: 'Tessera.Untrusted.Ident.ofRemote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ident.ofRemote

/-- info: 'Tessera.Untrusted.pasted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pasted

/-- info: 'Tessera.Untrusted.withoutControls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms withoutControls

/-- info: 'Tessera.VT.text_tokens_print' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms VT.text_tokens_print

/-- info: 'Tessera.Ansi.output_only_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ansi.output_only_own

/-- info: 'Tessera.diff_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms diff_own

/-- info: 'Tessera.diff_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms diff_correct

/-- info: 'Tessera.redraw_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms redraw_correct

/-- info: 'Tessera.RemoteStyle.not_reserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RemoteStyle.not_reserved

/-- info: 'Tessera.RemoteStyle.reserved_over' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RemoteStyle.reserved_over

/-- info: 'Tessera.Roster.build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Roster.build

/-- info: 'Tessera.Style.reserved_downgrade' depends on axioms: [propext] -/
#guard_msgs in #print axioms Style.reserved_downgrade

/-- info: 'Tessera.Buffer.mapStyle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Buffer.mapStyle

/-- info: 'Tessera.Text.wrap_width_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Text.wrap_width_le

/-- info: 'Tessera.Input.cursor_visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Input.cursor_visible

/-- info: 'Tessera.selected_visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms selected_visible

/-- info: 'Tessera.fitWidths_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fitWidths_le

/-- info: 'Tessera.answer_refocus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms answer_refocus

end Tessera.Tests.Axioms
