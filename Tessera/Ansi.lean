/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Buffer
import Tessera.VT

/-! # What Tessera writes to the terminal

Everything Tessera writes is an `Op`: move the cursor, set the style, clear the screen, or print
a glyph. Text reaches the terminal only as glyphs, each a character its charset allows, and no
operation places text inside an escape sequence or asks the terminal a question.

`output_only_own` says what a terminal makes of the output: read with `VT.tokens`, the encoding
of a list of operations gives back exactly those operations, each a printed character or one of
Tessera's own control sequences. -/

namespace Tessera.Ansi

open VT

/-- Parameters of a control sequence: decimal numbers separated by `;`. -/
def paramChars : List Nat → List Char
  | [] => []
  | [n] => (toString n).toList
  | n :: ns => (toString n).toList ++ ';' :: paramChars ns

/-- A control sequence: CSI, the parameters `ns`, and the final byte `f`. -/
def csiChars (ns : List Nat) (f : Char) : List Char := '\x1b' :: '[' :: (paramChars ns ++ [f])

def csi (ns : List Nat) (f : Char) : String := String.ofList (csiChars ns f)

/-- Move the cursor to column `x`, row `y`, counting from 0. -/
def moveTo (x y : Nat) : String := csi [y + 1, x + 1] 'H'

def clearScreen : String := csi [2] 'J'

def colorCodes (fg : Bool) : Color → List Nat
  | .default => [if fg then 39 else 49]
  | .ansi n => if n.val < 8 then [(if fg then 30 else 40) + n.val] else [(if fg then 90 else 100) + n.val - 8]
  | .indexed n => [if fg then 38 else 48, 5, n.toNat]
  | .rgb r g b => [if fg then 38 else 48, 2, r.toNat, g.toNat, b.toNat]

/-- Select graphic rendition: reset, then set everything `s` sets. -/
def sgrCodes (s : Style) : List Nat :=
  let attrs := [(s.bold, 1), (s.dim, 2), (s.italic, 3), (s.underline, 4), (s.reverse, 7)]
  0 :: attrs.filterMap (fun (on, c) => if on then some c else none)
    ++ (s.fg.map (colorCodes true)).getD [] ++ (s.bg.map (colorCodes false)).getD []

def sgr (s : Style) : String := csi (sgrCodes s) 'm'

def resetStyle : String := sgr {}

inductive Op (cs : Charset) where
  | moveTo (x y : Nat)
  | sgr (s : Style)
  | clear
  | print (g : Glyph cs)
  /-- Set the window's title, to text the program wrote. -/
  | title (t : Text cs .app)

variable {cs : Charset}

def Op.chars : Op cs → List Char
  | .moveTo x y => csiChars [y + 1, x + 1] 'H'
  | .sgr s => csiChars (sgrCodes s) 'm'
  | .clear => csiChars [2] 'J'
  | .print g => [g.char]
  | .title t => '\x1b' :: ']' :: '0' :: ';' :: (t.text.toList ++ ['\x07'])

/-- What a terminal makes of an operation. -/
def Op.token : Op cs → Token
  | .moveTo x y => .csi (paramChars [y + 1, x + 1]) [] 'H'
  | .sgr s => .csi (paramChars (sgrCodes s)) [] 'm'
  | .clear => .csi (paramChars [2]) [] 'J'
  | .print g => .print g.char
  | .title t => .osc ('0' :: ';' :: t.text.toList)

def encode (ops : List (Op cs)) : String := String.ofList (ops.flatMap Op.chars)

/-- The tokens of Tessera's own output: a character that only prints; one of its control
sequences, moving the cursor (`H`), setting the style (`m`) or clearing the screen (`J`); or the
command setting the window's title, to characters that only print. -/
def Own : Token → Prop
  | .print c => Inert c
  | .csi ps [] f => (∀ p ∈ ps, isParam p) ∧ (f = 'H' ∨ f = 'm' ∨ f = 'J')
  | .osc ('0' :: ';' :: t) => ∀ c ∈ t, Inert c
  | _ => False

theorem isParam_of_isDigit {c : Char} (h : c.isDigit) : isParam c := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [isParam, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h.1, Nat.le_trans h.2 (by decide)⟩

theorem paramChars_param (ns : List Nat) : ∀ p ∈ paramChars ns, isParam p := by
  have digits : ∀ n : Nat, ∀ p ∈ (toString n).toList, isParam p := fun n p hp => by
    simp only [Nat.toString_eq_repr, Nat.toList_repr] at hp
    exact isParam_of_isDigit (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hp)
  induction ns with
  | nil => simp [paramChars]
  | cons n ns ih =>
    match ns, ih with
    | [], _ => exact digits n
    | m :: ms, ih =>
      intro p hp
      simp only [paramChars, List.mem_append, List.mem_cons] at hp
      rcases hp with hp | rfl | hp
      · exact digits n p hp
      · decide
      · exact ih p (by simpa [paramChars] using hp)

theorem run_op (op : Op cs) (rest : List Char) :
    run .ground (op.chars ++ rest) = op.token :: run .ground rest := by
  have csiOp : ∀ (ns : List Nat) (f : Char), isFinal f →
      run .ground (csiChars ns f ++ rest) = .csi (paramChars ns) [] f :: run .ground rest :=
    fun ns f hf => by
      simpa [csiChars] using run_csi (paramChars_param ns) hf rest
  cases op with
  | moveTo x y => exact csiOp _ _ (by decide)
  | sgr s => exact csiOp _ _ (by decide)
  | clear => exact csiOp _ _ (by decide)
  | print g =>
    have := run_inert (l := [g.char])
      (fun c hc => by simp at hc; subst hc; exact inert_of_text (.inl g.printable)) rest
    simpa [Op.chars, Op.token] using this
  | title t =>
    have hb : ∀ c ∈ '0' :: ';' :: t.text.toList, Inert c := by
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · exact ⟨by decide, by decide, by decide⟩
      · exact ⟨by decide, by decide, by decide⟩
      · exact inert_of_text (t.charsOk c hc)
    simpa [Op.chars, Op.token] using run_osc hb rest

/-- A terminal reads Tessera's output as exactly the operations it encodes. -/
theorem output_only_own (ops : List (Op cs)) : tokens (encode ops).toList = ops.map Op.token := by
  simp only [encode, String.toList_ofList, tokens]
  induction ops with
  | nil => rfl
  | cons op ops ih => rw [List.flatMap_cons, run_op, ih]; rfl

theorem own_token (op : Op cs) : Own op.token := by
  cases op with
  | moveTo => exact ⟨paramChars_param _, .inl rfl⟩
  | sgr => exact ⟨paramChars_param _, .inr (.inl rfl)⟩
  | clear => exact ⟨paramChars_param _, .inr (.inr rfl)⟩
  | print g => exact inert_of_text (.inl g.printable)
  | title t => exact fun c hc => inert_of_text (t.charsOk c hc)

/-- Every token of Tessera's output is its own: a character that only prints, or one of its
control sequences. -/
theorem output_own (ops : List (Op cs)) : ∀ t ∈ tokens (encode ops).toList, Own t := by
  rw [output_only_own]
  intro t ht
  obtain ⟨op, _, rfl⟩ := List.mem_map.mp ht
  exact own_token op

end Tessera.Ansi
