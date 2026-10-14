/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera

/-! # Programs that must not compile

Each example tries to put text on the screen past the types, and each fails to compile with the
error shown. -/

namespace Tessera.Tests.Rejects

open Tessera

/--
error: Application type mismatch: The argument
  s
has type
  String
but is expected to have type
  Text Charset.standard Origin.remote
in the application
  Widget.str s
-/
#guard_msgs in
example (s : String) : Widget Charset.standard := Widget.str (o := .remote) s

/--
error: Tactic `decide` proved that the proposition
  ∀ (c : Char), c ∈ "\x1b]0;x\x07".toList → 32 ≤ c.toNat ∧ c.toNat ≤ 126
is false
-/
#guard_msgs in
example : Text Charset.standard .app := t!"\x1b]0;x\x07"

/-- error: Invalid `⟨...⟩` notation: Constructor for `Tessera.Text` is marked as private -/
#guard_msgs in
example (s : String) (h₁ : ∀ c ∈ s.toList, Charset.standard.Printable c ∨ Combining c)
    (h₂ : marksOk none s.toList = true) : Text Charset.standard .remote := ⟨s, h₁, h₂⟩

/--
error: Type mismatch
  t
has type
  Text Charset.standard Origin.remote
but is expected to have type
  Text Charset.standard Origin.app
-/
#guard_msgs in
example (t : Text Charset.standard .remote) : Text Charset.standard .app := t

/--
error: Tactic `decide` proved that the proposition
  Charset.standard.Printable '\x1b'
is false
-/
#guard_msgs in
example : Glyph Charset.standard := ⟨'\x1b', by decide⟩

end Tessera.Tests.Rejects
