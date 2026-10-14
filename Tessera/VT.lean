/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Text

/-! # What a terminal makes of characters

A terminal reads the characters written to it with a state machine, after ECMA-48 and the DEC
parser terminals follow. `VT.tokens` is that machine: it turns characters into what a terminal
acts on, printed characters, controls and escape sequences.

It takes every introducer a terminal might honour: ESC, and the C1 controls that begin a control
sequence, an operating system command or a control string on their own. A character that is
neither an introducer nor any other control is printed, whatever state the machine is in after
it; so text with none of them is printed and nothing else, on any terminal that reads this way.
That is `text_tokens_print`. -/

namespace Tessera.VT

/-- A character that only prints: not a C0 control (among them ESC), not DEL, not a C1 control. -/
def Inert (c : Char) : Prop :=
  0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬ (0x80 ≤ c.toNat ∧ c.toNat < 0xA0)

def isParam (c : Char) : Bool := 0x30 ≤ c.toNat && c.toNat ≤ 0x3F

def isInter (c : Char) : Bool := 0x20 ≤ c.toNat && c.toNat ≤ 0x2F

def isFinal (c : Char) : Bool := 0x40 ≤ c.toNat && c.toNat ≤ 0x7E

def isC0 (c : Char) : Bool := c.toNat < 0x20

def isC1 (c : Char) : Bool := 0x80 ≤ c.toNat && c.toNat < 0xA0

/-- String terminator, as a C1 control. -/
def isST (c : Char) : Bool := c.toNat == 0x9C

inductive Token where
  | print (c : Char)
  /-- A control acted on alone: C0, DEL or C1. -/
  | control (c : Char)
  /-- A control sequence: CSI, parameters, intermediates, final. -/
  | csi (params inter : List Char) (final : Char)
  /-- An operating system command, such as setting the title or the clipboard. -/
  | osc (body : List Char)
  /-- A control string (DCS, SOS, PM or APC), by the character that began it. -/
  | str (intro : Char) (body : List Char)
  /-- Any other escape sequence. -/
  | esc (inter : List Char) (final : Char)
  /-- A sequence the input ends inside, or one cut off by a character it may not hold. -/
  | incomplete
  deriving DecidableEq, Repr, Inhabited

def Token.isPrint : Token → Bool
  | .print _ => true
  | _ => false

inductive State where
  | ground
  | escape (inter : List Char)
  | csi (params inter : List Char)
  | osc (body : List Char)
  | oscEsc (body : List Char)
  | str (intro : Char) (body : List Char)
  | strEsc (intro : Char) (body : List Char)
  deriving DecidableEq, Repr, Inhabited

/-- The character after ESC and any intermediates. -/
def afterEsc (inter : List Char) (c : Char) : State × List Token :=
  if c == '\x1b' then (.escape [], [])
  else if inter.isEmpty && c == '[' then (.csi [] [], [])
  else if inter.isEmpty && c == ']' then (.osc [], [])
  else if inter.isEmpty && (c == 'P' || c == 'X' || c == '^' || c == '_') then (.str c [], [])
  else if isInter c then (.escape (inter ++ [c]), [])
  else if isC0 c then (.escape inter, [.control c])
  else if c.toNat == 0x7F then (.escape inter, [])
  else (.ground, [.esc inter c])

def stepGround (c : Char) : State × List Token :=
  if c == '\x1b' then (.escape [], [])
  else if c.toNat == 0x9B then (.csi [] [], [])
  else if c.toNat == 0x9D then (.osc [], [])
  else if c.toNat == 0x90 || c.toNat == 0x98 || c.toNat == 0x9E || c.toNat == 0x9F then
    (.str c [], [])
  else if isC0 c || c.toNat == 0x7F || isC1 c then (.ground, [.control c])
  else (.ground, [.print c])

def step : State → Char → State × List Token
  | .ground, c => stepGround c
  | .escape inter, c => afterEsc inter c
  | .csi ps is, c =>
    if c == '\x1b' then (.escape [], [])
    else if isParam c && is.isEmpty then (.csi (ps ++ [c]) is, [])
    else if isInter c then (.csi ps (is ++ [c]), [])
    else if isFinal c then (.ground, [.csi ps is c])
    else if isC0 c then (.csi ps is, [.control c])
    else (.ground, [.incomplete])
  | .osc b, c =>
    if c == '\x07' || isST c then (.ground, [.osc b])
    else if c == '\x1b' then (.oscEsc b, [])
    else (.osc (b ++ [c]), [])
  | .oscEsc b, c =>
    if c == '\\' then (.ground, [.osc b])
    else let (s, ts) := afterEsc [] c; (s, .osc b :: ts)
  | .str i b, c =>
    if isST c then (.ground, [.str i b])
    else if c == '\x1b' then (.strEsc i b, [])
    else (.str i (b ++ [c]), [])
  | .strEsc i b, c =>
    if c == '\\' then (.ground, [.str i b])
    else let (s, ts) := afterEsc [] c; (s, .str i b :: ts)

def run : State → List Char → List Token
  | .ground, [] => []
  | _, [] => [.incomplete]
  | s, c :: r => let (s', ts) := step s c; ts ++ run s' r

/-- What a terminal makes of `l`, read from its ground state. -/
def tokens (l : List Char) : List Token := run .ground l

theorem stepGround_inert {c : Char} (h : Inert c) : stepGround c = (.ground, [.print c]) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hesc : (c == '\x1b') = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; simp at h1
  have h9b : (c.toNat == 0x9B) = false := by simp; omega
  have h9d : (c.toNat == 0x9D) = false := by simp; omega
  have hstr : (c.toNat == 0x90 || c.toNat == 0x98 || c.toNat == 0x9E || c.toNat == 0x9F) = false := by
    simp; omega
  have hctl : (isC0 c || c.toNat == 0x7F || isC1 c) = false := by
    simp [isC0, isC1]; omega
  simp [stepGround, hesc, h9b, h9d, hstr, hctl]

/-- Characters that only print are printed, one token each, and the terminal stays in its ground
state. -/
theorem run_inert {l : List Char} (h : ∀ c ∈ l, Inert c) (rest : List Char) :
    run .ground (l ++ rest) = l.map .print ++ run .ground rest := by
  induction l with
  | nil => rfl
  | cons c t ih =>
    simp only [List.cons_append, run, step, stepGround_inert (h c (List.mem_cons_self ..)),
      List.map_cons]
    rw [ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

theorem tokens_inert {l : List Char} (h : ∀ c ∈ l, Inert c) : tokens l = l.map .print := by
  have := run_inert h []
  simp only [List.append_nil] at this
  rw [tokens, this, show run .ground [] = [] from rfl, List.append_nil]

/-- A character a charset allows, or a combining accent, only prints. -/
theorem inert_of_text {cs : Charset} {c : Char} (h : cs.Printable c ∨ Combining c) : Inert c := by
  rcases h with h | h
  · exact ⟨cs.printable_not_c0 c h, cs.printable_not_del c h, cs.printable_not_c1 c h⟩
  · simp only [Combining] at h
    exact ⟨by omega, by omega, by omega⟩

/-- Text, however it was made, is printed and nothing else: it holds no escape sequence and no
control, whatever the text and whatever its charset. -/
theorem text_tokens_print {cs : Charset} {o : Origin} (t : Text cs o) :
    tokens t.text.toList = t.text.toList.map .print :=
  tokens_inert fun c hc => inert_of_text (t.charsOk c hc)

/-- The parameter bytes of a control sequence, then its final byte, after CSI. -/
theorem run_csi_body {ps : List Char} (hp : ∀ p ∈ ps, isParam p) {f : Char} (hf : isFinal f)
    (acc rest : List Char) :
    run (.csi acc []) (ps ++ f :: rest) = .csi (acc ++ ps) [] f :: run .ground rest := by
  induction ps generalizing acc with
  | nil =>
    have hesc : (f == '\x1b') = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp [isFinal] at hf
    have hpar : isParam f = false := by simp [isParam, isFinal] at hf ⊢; omega
    have hint : isInter f = false := by simp [isInter, isFinal] at hf ⊢; omega
    simp [run, step, hesc, hpar, hint, hf]
  | cons p t ih =>
    have hpp := hp p (List.mem_cons_self ..)
    have hesc : (p == '\x1b') = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp [isParam] at hpp
    simp only [List.cons_append, run, step, hesc, hpp, List.isEmpty_nil, Bool.and_true,
      Bool.false_eq_true, ↓reduceIte, List.nil_append]
    rw [ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))]
    simp

/-- A control sequence with parameter bytes `ps` and final byte `f` is read as one, and the
terminal is in its ground state after it. -/
theorem run_csi {ps : List Char} (hp : ∀ p ∈ ps, isParam p) {f : Char} (hf : isFinal f)
    (rest : List Char) :
    run .ground ('\x1b' :: '[' :: (ps ++ f :: rest)) = .csi ps [] f :: run .ground rest := by
  have h := run_csi_body hp hf [] rest
  simp only [List.nil_append] at h
  simp [run, step, stepGround, afterEsc, h]

/-- The body of an operating system command, then BEL, after OSC. -/
theorem run_osc_body {body : List Char} (hb : ∀ c ∈ body, Inert c) (acc rest : List Char) :
    run (.osc acc) (body ++ '\x07' :: rest) = .osc (acc ++ body) :: run .ground rest := by
  induction body generalizing acc with
  | nil => simp [run, step]
  | cons c t ih =>
    obtain ⟨h1, h2, h3⟩ := hb c (List.mem_cons_self ..)
    have hbel : (c == '\x07') = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at h1
    have hst : isST c = false := by simp [isST]; omega
    have hesc : (c == '\x1b') = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at h1
    simp only [List.cons_append, run, step, hbel, hst, hesc, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte, List.nil_append]
    rw [ih (fun x hx => hb x (List.mem_cons_of_mem _ hx))]
    simp

/-- An operating system command whose body only prints is read as one, ended by BEL, and the
terminal is in its ground state after it. -/
theorem run_osc {body : List Char} (hb : ∀ c ∈ body, Inert c) (rest : List Char) :
    run .ground ('\x1b' :: ']' :: (body ++ '\x07' :: rest)) = .osc body :: run .ground rest := by
  have h := run_osc_body hb [] rest
  simp only [List.nil_append] at h
  simp [run, step, stepGround, afterEsc, h]

end Tessera.VT
