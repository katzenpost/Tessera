/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Buffer
import Tessera.VT
import Tessera.Image

/-! # What Tessera writes to the terminal

Everything Tessera writes is an `Op`: move the cursor, set the style, clear the screen, print a
glyph, set the title, or make room for an inline frame and leave it. Text reaches the terminal only as glyphs, each a character its charset allows, and no
operation places text inside an escape sequence or asks the terminal a question.

A frame is drawn either on the whole screen or inline, in rows below the cursor, with the
terminal's scrollback left as it was. Inline, positions are relative to the frame's first row,
which the terminal is asked to remember (ESC 7), so a move is a return there (ESC 8) and moves
down and right, and clearing clears from there down.

`output_only_own` says what a terminal makes of the output: read with `VT.tokens`, the encoding
of a list of operations gives back exactly the tokens of those operations, each a printed
character or one of Tessera's own controls and sequences. -/

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

/-- Where frames are drawn: on the whole screen, or inline, in `rows` rows from the cursor. -/
inductive Placement where
  | fullscreen
  | inline (rows : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- How many rows a frame has on a screen `h` rows high. -/
def Placement.height : Placement → Nat → Nat
  | .fullscreen, h => h
  | .inline n, h => min n h

inductive Op (cs : Charset) where
  | moveTo (x y : Nat)
  | sgr (s : Style)
  | clear
  | print (g : Glyph cs)
  /-- Set the window's title, to text the program wrote. -/
  | title (t : Text cs .app)
  /-- Make room for an inline frame of `rows` rows from the cursor, scrolling if need be, and
  remember where it starts. -/
  | enterInline (rows : Nat)
  /-- Put the cursor on the line after an inline frame of `rows` rows. -/
  | leaveInline (rows : Nat)
  /-- Show a picture at the cursor, as `g` shows them. -/
  | image (g : Graphics) (p : Pixels)

variable {cs : Charset}

/-- Move `n` (`f`: `A` up, `B` down, `C` right), or not at all. -/
def relChars (n : Nat) (f : Char) : List Char := if n = 0 then [] else csiChars [n] f

def relTokens (n : Nat) (f : Char) : List Token := if n = 0 then [] else [.csi (paramChars [n]) [] f]

def Op.chars (p : Placement) : Op cs → List Char
  | .moveTo x y => match p with
    | .fullscreen => csiChars [y + 1, x + 1] 'H'
    | .inline _ => '\x1b' :: '8' :: (relChars y 'B' ++ relChars x 'C')
  | .sgr s => csiChars (sgrCodes s) 'm'
  | .clear => match p with
    | .fullscreen => csiChars [2] 'J'
    | .inline _ => '\x1b' :: '8' :: csiChars [] 'J'
  | .print g => g.chars
  | .title t => '\x1b' :: ']' :: '0' :: ';' :: (t.text.toList ++ ['\x07'])
  | .enterInline n =>
    '\r' :: (List.replicate (n - 1) '\n' ++ relChars (n - 1) 'A' ++ ['\x1b', '7'])
  | .leaveInline n => '\x1b' :: '8' :: (relChars (n - 1) 'B' ++ ['\r', '\n'])
  | .image .sixel px => '\x1b' :: 'P' :: ('q' :: (plain (Sixel.body px)).1 ++ ['\x1b', '\\'])
  | .image .kitty px => (Kitty.bodies px).flatMap fun b =>
    '\x1b' :: '_' :: ('G' :: (plain b).1 ++ ['\x1b', '\\'])

/-- What a terminal makes of an operation. -/
def Op.tokens (p : Placement) : Op cs → List Token
  | .moveTo x y => match p with
    | .fullscreen => [.csi (paramChars [y + 1, x + 1]) [] 'H']
    | .inline _ => .esc [] '8' :: (relTokens y 'B' ++ relTokens x 'C')
  | .sgr s => [.csi (paramChars (sgrCodes s)) [] 'm']
  | .clear => match p with
    | .fullscreen => [.csi (paramChars [2]) [] 'J']
    | .inline _ => [.esc [] '8', .csi [] [] 'J']
  | .print g => g.chars.map .print
  | .title t => [.osc ('0' :: ';' :: t.text.toList)]
  | .enterInline n =>
    .control '\r' :: (List.replicate (n - 1) (.control '\n') ++ relTokens (n - 1) 'A' ++ [.esc [] '7'])
  | .leaveInline n => .esc [] '8' :: (relTokens (n - 1) 'B' ++ [.control '\r', .control '\n'])
  | .image .sixel px => [.str 'P' ('q' :: (plain (Sixel.body px)).1)]
  | .image .kitty px => (Kitty.bodies px).map fun b => .str '_' ('G' :: (plain b).1)

def encode (ops : List (Op cs)) (p : Placement := .fullscreen) : String :=
  String.ofList (ops.flatMap (Op.chars p))

/-- The tokens of Tessera's own output: a character that only prints; one of its control
sequences, moving the cursor (`H`, or `A`, `B` and `C` by a number of cells), setting the style
(`m`) or clearing the screen (`J`); remembering the cursor's place (ESC 7) and returning to it
(ESC 8); a carriage return and a line feed; the command setting the window's title, to
characters that only print; or a picture, as sixel or kitty graphics, in printable ASCII. -/
def Own : Token → Prop
  | .print c => Inert c
  | .csi ps [] f => (∀ p ∈ ps, isParam p) ∧ f ∈ ['H', 'm', 'J', 'A', 'B', 'C']
  | .osc ('0' :: ';' :: t) => ∀ c ∈ t, Inert c
  | .esc [] f => f = '7' ∨ f = '8'
  | .control c => c = '\r' ∨ c = '\n'
  | .str 'P' ('q' :: b) => ∀ c ∈ b, Plain c
  | .str '_' ('G' :: b) => ∀ c ∈ b, Plain c
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

/-- A glyph's characters, it and its accents, only print. -/
theorem glyph_inert (g : Glyph cs) : ∀ c ∈ g.chars, Inert c := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact inert_of_text (.inl g.printable)
  · exact inert_of_text (cs := cs) (.inr (g.marks_combining c hc))

theorem run_esc {f : Char} (hf : f = '7' ∨ f = '8') (rest : List Char) :
    run .ground ('\x1b' :: f :: rest) = .esc [] f :: run .ground rest := by
  rcases hf with rfl | rfl <;> rfl

theorem run_control {c : Char} (hc : c = '\r' ∨ c = '\n') (rest : List Char) :
    run .ground (c :: rest) = .control c :: run .ground rest := by
  rcases hc with rfl | rfl <;> rfl

theorem run_csiOf (ns : List Nat) {f : Char} (hf : isFinal f) (rest : List Char) :
    run .ground (csiChars ns f ++ rest) = .csi (paramChars ns) [] f :: run .ground rest := by
  simpa [csiChars] using run_csi (paramChars_param ns) hf rest

theorem run_rel (n : Nat) {f : Char} (hf : isFinal f) (rest : List Char) :
    run .ground (relChars n f ++ rest) = relTokens n f ++ run .ground rest := by
  unfold relChars relTokens
  split
  · rfl
  · simpa using run_csiOf [n] hf rest

theorem run_lf (n : Nat) (rest : List Char) :
    run .ground (List.replicate n '\n' ++ rest) =
      List.replicate n (.control '\n') ++ run .ground rest := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, run_control (.inr rfl), ih]; rfl

theorem run_str_body {i : Char} {body : List Char} (hb : ∀ c ∈ body, Plain c) (acc rest : List Char) :
    run (.str i acc) (body ++ '\x1b' :: '\\' :: rest) = .str i (acc ++ body) :: run .ground rest := by
  induction body generalizing acc with
  | nil => simp [run, step, isST]
  | cons c t ih =>
    obtain ⟨h1, h2⟩ := hb c (List.mem_cons_self ..)
    have hst : isST c = false := by simp [isST]; omega
    have hesc : (c == '\x1b') = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at h1
    simp only [List.cons_append, run, step, hst, hesc, Bool.false_eq_true, ↓reduceIte,
      List.nil_append]
    rw [ih (fun x hx => hb x (List.mem_cons_of_mem _ hx))]
    simp

/-- A control string that only `Plain` characters, after its first, is read as one, ended by ST,
and the terminal is in its ground state after it. -/
theorem run_str {i : Char} (hi : i = 'P' ∨ i = '_') {body : List Char} (hb : ∀ c ∈ body, Plain c)
    (rest : List Char) :
    run .ground ('\x1b' :: i :: (body ++ '\x1b' :: '\\' :: rest)) = .str i body :: run .ground rest := by
  have h := run_str_body (i := i) hb [] rest
  simp only [List.nil_append] at h
  rcases hi with rfl | rfl <;> simp [run, step, stepGround, afterEsc, h]

theorem plain_cons {c : Char} (hc : Plain c) {l : List Char} (hl : ∀ x ∈ l, Plain x) :
    ∀ x ∈ c :: l, Plain x := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx
  · exact hc
  · exact hl x hx

theorem run_op (p : Placement) (op : Op cs) (rest : List Char) :
    run .ground (op.chars p ++ rest) = op.tokens p ++ run .ground rest := by
  cases op with
  | moveTo x y =>
    cases p with
    | fullscreen => simpa [Op.chars, Op.tokens] using run_csiOf [y + 1, x + 1] (f := 'H') (by decide) rest
    | inline _ =>
      simp only [Op.chars, Op.tokens, List.cons_append, List.append_assoc]
      rw [run_esc (.inr rfl), run_rel _ (by decide), run_rel _ (by decide)]
  | sgr s => simpa [Op.chars, Op.tokens] using run_csiOf (sgrCodes s) (f := 'm') (by decide) rest
  | clear =>
    cases p with
    | fullscreen => simpa [Op.chars, Op.tokens] using run_csiOf [2] (f := 'J') (by decide) rest
    | inline _ =>
      simp only [Op.chars, Op.tokens, List.cons_append]
      rw [run_esc (.inr rfl), run_csiOf [] (f := 'J') (by decide)]
      rfl
  | print g => simpa [Op.chars, Op.tokens] using run_inert (glyph_inert g) rest
  | title t =>
    have hb : ∀ c ∈ '0' :: ';' :: t.text.toList, Inert c := by
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · exact ⟨by decide, by decide, by decide⟩
      · exact ⟨by decide, by decide, by decide⟩
      · exact inert_of_text (t.charsOk c hc)
    simpa [Op.chars, Op.tokens] using run_osc hb rest
  | enterInline n =>
    simp only [Op.chars, Op.tokens, List.cons_append, List.append_assoc]
    rw [run_control (.inl rfl), run_lf, run_rel _ (by decide), run_esc (.inl rfl)]
    simp
  | leaveInline n =>
    simp only [Op.chars, Op.tokens, List.cons_append, List.append_assoc]
    rw [run_esc (.inr rfl), run_rel _ (by decide), run_control (.inl rfl), run_control (.inr rfl)]
    simp
  | image g px =>
    cases g with
    | sixel =>
      simp only [Op.chars, Op.tokens, List.cons_append, List.append_assoc]
      have := run_str (i := 'P') (.inl rfl) (plain_cons (c := 'q') (by decide) (plain (Sixel.body px)).2) rest
      simpa using this
    | kitty =>
      simp only [Op.chars, Op.tokens]
      generalize Kitty.bodies px = bs
      induction bs with
      | nil => rfl
      | cons b bs ih =>
        have e : ('\x1b' :: '_' :: ('G' :: (plain b).1 ++ ['\x1b', '\\'])) ++
            (bs.flatMap (fun b => '\x1b' :: '_' :: ('G' :: (plain b).1 ++ ['\x1b', '\\'])) ++ rest) =
            '\x1b' :: '_' :: (('G' :: (plain b).1) ++ '\x1b' :: '\\' ::
              (bs.flatMap (fun b => '\x1b' :: '_' :: ('G' :: (plain b).1 ++ ['\x1b', '\\'])) ++ rest)) := by
          simp
        rw [List.flatMap_cons, List.append_assoc, e,
          run_str (.inr rfl) (plain_cons (c := 'G') (by decide) (plain b).2), ih]
        rfl

/-- A terminal reads Tessera's output as exactly the tokens of the operations it encodes. -/
theorem output_only_own (ops : List (Op cs)) (p : Placement := .fullscreen) :
    tokens (encode ops p).toList = ops.flatMap (Op.tokens p) := by
  simp only [encode, String.toList_ofList, tokens]
  induction ops with
  | nil => rfl
  | cons op ops ih => simp only [List.flatMap_cons]; rw [run_op, ih]

theorem own_rel (n : Nat) {f : Char} (hf : f ∈ ['H', 'm', 'J', 'A', 'B', 'C']) :
    ∀ t ∈ relTokens n f, Own t := by
  unfold relTokens; split
  · simp
  · simp only [List.mem_singleton]; rintro t rfl; exact ⟨paramChars_param _, hf⟩

theorem own_tokens (p : Placement) (op : Op cs) : ∀ t ∈ op.tokens p, Own t := by
  cases op with
  | moveTo =>
    cases p with
    | fullscreen => simp only [Op.tokens, List.mem_singleton]; rintro t rfl; exact ⟨paramChars_param _, by simp⟩
    | inline _ =>
      simp only [Op.tokens, List.mem_cons, List.mem_append]
      rintro t (rfl | h | h)
      · exact .inr rfl
      · exact own_rel _ (by simp) t h
      · exact own_rel _ (by simp) t h
  | sgr => simp only [Op.tokens, List.mem_singleton]; rintro t rfl; exact ⟨paramChars_param _, by simp⟩
  | clear =>
    cases p with
    | fullscreen => simp only [Op.tokens, List.mem_singleton]; rintro t rfl; exact ⟨paramChars_param _, by simp⟩
    | inline _ =>
      simp only [Op.tokens, List.mem_cons, List.not_mem_nil, or_false]
      rintro t (rfl | rfl)
      · exact .inr rfl
      · exact ⟨by simp, by simp⟩
  | print g =>
    simp only [Op.tokens, List.mem_map]
    rintro t ⟨c, hc, rfl⟩
    exact glyph_inert g c hc
  | title t => simp only [Op.tokens, List.mem_singleton]; rintro t' rfl; exact fun c hc => inert_of_text (t.charsOk c hc)
  | enterInline n =>
    intro t ht
    simp only [Op.tokens, List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | (⟨_, rfl⟩ | h) | rfl
    · exact .inl rfl
    · exact .inr rfl
    · exact own_rel _ (by simp) t h
    · exact .inl rfl
  | leaveInline n =>
    intro t ht
    simp only [Op.tokens, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | h | rfl | rfl
    · exact .inr rfl
    · exact own_rel _ (by simp) t h
    · exact .inl rfl
    · exact .inr rfl
  | image g px =>
    cases g with
    | sixel => simp only [Op.tokens, List.mem_singleton]; rintro t rfl; exact (plain _).2
    | kitty =>
      simp only [Op.tokens, List.mem_map]
      rintro t ⟨b, _, rfl⟩
      exact (plain b).2

/-- Every token of Tessera's output is its own: a character that only prints, or one of its
controls and sequences. -/
theorem output_own (ops : List (Op cs)) (p : Placement := .fullscreen) :
    ∀ t ∈ tokens (encode ops p).toList, Own t := by
  rw [output_only_own ops p]
  intro t ht
  obtain ⟨op, _, ht⟩ := List.mem_flatMap.mp ht
  exact own_tokens p op t ht

end Tessera.Ansi
