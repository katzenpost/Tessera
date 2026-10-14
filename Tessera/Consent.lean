/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.App

/-! # Consent

An action that grants authority, such as opening a link, saving a file or trusting a key, is one
the user chose, on the thing it acts on. Such an action takes a `Designation` of that thing, and
a designation is made only from a `UserInput`, which only a key or a paste read from the terminal
carries. An event from elsewhere, such as a message from the network, has none, and so cannot
open a link, take the keyboard's focus with a modal, or confirm a question.

A question put before an action that cannot be undone is a `Confirmation`. It says what the
action does, ignores keys for a moment after it appears, and is confirmed only by Ctrl+Y, never
by Enter or `y` alone, which someone typing might press. -/

namespace Tessera

variable {cs : Charset}

/-- The user chose `x`. -/
structure Designation {α : Type} (x : α) : Type where
  private mk ::

/-- Designate `x` by what the user just did. -/
def UserInput.designate (_ : UserInput) {α : Type} (x : α) : Designation x := ⟨⟩

/-- A dialog that takes the keyboard's focus. Only the user opens one. -/
structure Modal (α : Type) where
  private mk ::
  content : α

def Modal.open (_ : UserInput) {α : Type} (content : α) : Modal α := ⟨content⟩

/-- How long a confirmation ignores keys after it appears, in milliseconds. -/
def confirmDelayMs : Nat := 500

/-- A question put to the user before an action that cannot be undone. Only the user opens one,
and it says what the action does: "Trust key 3F2A…91C0 as Alice? Messages from this key will
show as verified.", never "Continue?". -/
structure Confirmation (cs : Charset) where
  private mk ::
  consequence : Text cs .app
  /-- When it appeared, in milliseconds. -/
  shownAt : Nat

def Confirmation.ask (_ : UserInput) (consequence : Text cs .app) (now : Nat) : Confirmation cs :=
  ⟨consequence, now⟩

/-- `c` when the window regains the focus at `now`: the delay starts again, so a key pressed by
someone just back at the window does not answer a question they have not seen. -/
def Confirmation.refocus (c : Confirmation cs) (now : Nat) : Confirmation cs :=
  ⟨c.consequence, max c.shownAt now⟩

/-- The user confirmed `c`. -/
structure Confirmed (c : Confirmation cs) : Type where
  private mk ::

/-- The key that confirms: Ctrl+Y. -/
def isConfirmKey (k : Key) (m : Modifiers) : Bool := k == .char 'y' && m.ctrl

theorem enter_not_confirm (m : Modifiers) : isConfirmKey .enter m = false := rfl

theorem y_not_confirm : isConfirmKey (.char 'y') {} = false := rfl

/-- Whether `msg`, arriving at `now`, confirms `c`: Ctrl+Y, once the delay has passed. Anything
else leaves the question unanswered, which is the safe answer. -/
def Confirmation.answer {ε : Type} (c : Confirmation cs) (msg : Msg ε) (now : Nat) :
    Option (Confirmed c) :=
  match msg with
  | .key k m _ => if isConfirmKey k m && c.shownAt + confirmDelayMs ≤ now then some ⟨⟩ else none
  | _ => none

/-- A message from elsewhere never confirms. -/
theorem answer_custom {ε : Type} (c : Confirmation cs) (e : ε) (now : Nat) :
    c.answer (.custom e) now = none := rfl

/-- Nor does a key pressed before the delay has passed. -/
theorem answer_early {ε : Type} (c : Confirmation cs) (k : Key) (m : Modifiers) (u : UserInput)
    (now : Nat) (h : now < c.shownAt + confirmDelayMs) :
    c.answer (ε := ε) (.key k m u) now = none := by
  simp [Confirmation.answer]; omega

/-- After the window regains the focus, a key pressed before the delay has passed again does not
confirm. -/
theorem answer_refocus {ε : Type} (c : Confirmation cs) (k : Key) (m : Modifiers) (u : UserInput)
    (back now : Nat) (h : now < back + confirmDelayMs) :
    (c.refocus back).answer (ε := ε) (.key k m u) now = none :=
  answer_early _ k m u now (by simp only [Confirmation.refocus]; omega)

/-! ## Links -/

/-- A link that may be opened: printable ASCII with no space, beginning with `https://` or
`http://`. -/
structure Url where
  text : String
  scheme_ok : "https://".toList <+: text.toList ∨ "http://".toList <+: text.toList
  clean : ∀ c ∈ text.toList, 0x21 ≤ c.toNat ∧ c.toNat ≤ 0x7E

/-- `s` as a link, if it is one that may be opened. -/
def Url.parse? (s : String) : Option Url :=
  if h : ("https://".toList <+: s.toList ∨ "http://".toList <+: s.toList) ∧
      ∀ c ∈ s.toList, 0x21 ≤ c.toNat ∧ c.toNat ≤ 0x7E then
    some ⟨s, h.1, h.2⟩
  else none

/-- A link begins with `h`, so a program it is passed to cannot take it for an option. -/
theorem Url.head (u : Url) : u.text.toList.head? = some 'h' := by
  rcases u.scheme_ok with ⟨t, ht⟩ | ⟨t, ht⟩ <;> simp [← ht]

/-- Open a link the user chose with `opener`, as one argument, through no shell, with the
opener's output kept off the screen. -/
def openLink (u : Url) (_ : Designation u) (opener : String := "xdg-open") : IO Unit := do
  let child ← IO.Process.spawn
    { cmd := opener, args := #[u.text], stdin := .null, stdout := .null, stderr := .null }
  discard <| IO.asTask child.wait

/-! ## Commands -/

/-- A line the user typed: a message, or a command they named. -/
inductive Typed where
  | message (text : String)
  | command (name : String) (args : String)
  deriving DecidableEq, Repr

/-- A typed line beginning with `/` is a command, which must be one of `known`; an unknown one is
an error, never a message sent. A paste is message text whatever it begins with, and is never
read this way. -/
def Typed.classify (known : List String) (line : String) : Except String Typed :=
  if line.startsWith "/" then
    let rest := (line.drop 1).toString
    let name := (rest.takeWhile (· != ' ')).toString
    let args := ((rest.drop name.length).dropWhile (· == ' ')).toString
    if name ∈ known then .ok (.command name args) else .error name
  else .ok (.message line)

end Tessera
