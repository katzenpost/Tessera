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
example (s : String) : Widget Charset.standard .remote := Widget.str (t := .remote) s

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

/--
error: failed to synthesize instance of type class
  Shows Origin.remote Origin.app

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (t : Text Charset.standard .remote) : Widget Charset.standard .app := Widget.str t

/--
error: Type mismatch
  Widget.custom r
has type
  Widget Charset.standard Origin.remote
but is expected to have type
  Widget Charset.standard Origin.app
-/
#guard_msgs in
example (r : (ctx : Context) → Image Charset.standard ctx.width ctx.height) :
    Widget Charset.standard .app := Widget.custom r

/-- error: Invalid `⟨...⟩` notation: Constructor for `Tessera.Widget` is marked as private -/
#guard_msgs in
example : Widget Charset.standard .app := ⟨.fixed, .fixed, fun _ => .empty⟩

/--
error: Type mismatch
  b
has type
  Widget Charset.standard Origin.remote
but is expected to have type
  Widget Charset.standard Origin.app
-/
#guard_msgs in
example (b : Widget Charset.standard .remote) (a : Widget Charset.standard .app) :
    Frame Charset.standard :=
  { header := b, body := b, statusBar := a, prompt := a }

/-- error: `reverse` is not a field of structure `RemoteStyle` -/
#guard_msgs in
example : RemoteStyle := { reverse := true }

/-- error: Invalid `⟨...⟩` notation: Constructor for `Tessera.UserInput` is marked as private -/
#guard_msgs in
example : UserInput := ⟨⟩

/-- error: Invalid `⟨...⟩` notation: Constructor for `Tessera.Designation` is marked as private -/
#guard_msgs in
example (u : Url) : Designation u := ⟨⟩

/-- error: Invalid `⟨...⟩` notation: Constructor for `Tessera.Confirmed` is marked as private -/
#guard_msgs in
example (c : Confirmation Charset.standard) : Confirmed c := ⟨⟩

/--
error: Type mismatch
  fun x => openLink u x
has type
  Designation u → IO Unit
but is expected to have type
  IO Unit
-/
#guard_msgs in
example (u : Url) : IO Unit := openLink u

/--
error: Invalid field `toMsg`: The environment does not contain `Tessera.Incoming.toMsg`, so it is not possible to project the field `toMsg` from an expression
  Incoming.terminal (CrosstermFfi.Event.key CrosstermFfi.Key.enter)
of type `Incoming Unit`
-/
#guard_msgs in
example : Msg Unit := (Incoming.terminal (.key .enter) : Incoming Unit).toMsg

end Tessera.Tests.Rejects
