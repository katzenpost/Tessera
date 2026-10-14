/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Buffer

/-! # Text

A `Text` is one line that may be drawn: each of its characters is one its charset allows, or a
combining accent on the character before it. It has no value holding a control character, a bidi
control or an invisible character, so no value holding an escape sequence, which begins with ESC
or a C1 control.

Its constructor is private. A `Text` comes from `Untrusted.line`, which filters text from
elsewhere and shows each character it refuses as a visible stand-in; from a literal written with
`t!"…"`, checked when the program compiles; or from operations that keep the proofs, such as
`++`.

Its origin says where it came from: `.app` for text the program wrote, `.remote` for text from
elsewhere. Text the program wrote may be used wherever text from elsewhere may, never the
reverse. -/

namespace Tessera

variable {cs : Charset}

inductive Origin where
  | app
  | remote
  deriving DecidableEq, Repr, Inhabited

/-- Combining accents kept on one character. -/
def maxMarks : Nat := 4

/-- Every combining accent follows a character, at most `maxMarks` of them in a row. `run` is how
many follow the last character so far, or `none` before the first. -/
def marksOk : Option Nat → List Char → Bool
  | _, [] => true
  | none, c :: r => !isCombining c && marksOk (some 0) r
  | some k, c :: r =>
    if isCombining c then decide (k < maxMarks) && marksOk (some (k + 1)) r else marksOk (some 0) r

theorem marksOk_of_none {r : Option Nat} {l : List Char} (h : marksOk none l) : marksOk r l := by
  match r, l with
  | none, l => exact h
  | some _, [] => rfl
  | some _, c :: t =>
    simp only [marksOk, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [marksOk, h.1, h.2]

theorem marksOk_append {r : Option Nat} {a b : List Char} (ha : marksOk r a) (hb : marksOk none b) :
    marksOk r (a ++ b) := by
  induction a generalizing r with
  | nil => exact marksOk_of_none hb
  | cons c t ih =>
    match r with
    | none =>
      simp only [marksOk, Bool.and_eq_true, List.cons_append] at ha ⊢
      exact ⟨ha.1, ih ha.2⟩
    | some k =>
      simp only [marksOk, List.cons_append] at ha ⊢
      cases hc : isCombining c
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at ha ⊢
        exact ih ha
      · simp only [hc, ↓reduceIte, Bool.and_eq_true] at ha ⊢
        exact ⟨ha.1, ih ha.2⟩

theorem marksOk_of_noMarks {r : Option Nat} {l : List Char} (h : ∀ c ∈ l, isCombining c = false) :
    marksOk r l := by
  induction l generalizing r with
  | nil => cases r <;> rfl
  | cons c t ih =>
    have hc := h c (List.mem_cons_self ..)
    have ht := ih (r := some 0) fun x hx => h x (List.mem_cons_of_mem _ hx)
    cases r <;> simp [marksOk, hc, ht]

structure Text (cs : Charset) (o : Origin) where
  private mk ::
  text : String
  charsOk : ∀ c ∈ text.toList, cs.Printable c ∨ Combining c
  seqOk : marksOk none text.toList = true

namespace Text

variable {o : Origin}

instance : BEq (Text cs o) := ⟨fun a b => a.text == b.text⟩

instance : Repr (Text cs o) := ⟨fun t _ => repr t.text⟩

instance : ToString (Text cs o) := ⟨Text.text⟩

def empty : Text cs o := ⟨"", by simp, rfl⟩

instance : Inhabited (Text cs o) := ⟨empty⟩

/-- Text the program wrote, used where text from elsewhere may be. -/
def lift (t : Text cs .app) : Text cs .remote := ⟨t.text, t.charsOk, t.seqOk⟩

instance : Coe (Text cs .app) (Text cs .remote) := ⟨lift⟩

/-- `a` then `b`. A text never begins with a combining accent, so none of `b`'s attaches to `a`,
and the rules for accents hold of the whole. -/
def append (a b : Text cs o) : Text cs o :=
  ⟨a.text ++ b.text,
    by
      intro c hc
      simp only [String.toList_append, List.mem_append] at hc
      exact hc.elim (a.charsOk c) (b.charsOk c),
    by simpa using marksOk_append a.seqOk b.seqOk⟩

instance : Append (Text cs o) := ⟨append⟩

@[simp] theorem text_append (a b : Text cs o) : (a ++ b).text = a.text ++ b.text := rfl

theorem printable_of_not_combining (t : Text cs o) {c : Char} (hc : c ∈ t.text.toList)
    (hm : isCombining c = false) : cs.Printable c :=
  (t.charsOk c hc).resolve_right fun h => by simp [combining_iff.mp h] at hm

/-- Text from a literal whose every character `cs` allows. -/
def ofLit (s : String) (h : ∀ c ∈ s.toList, cs.Printable c) : Text cs .app :=
  ⟨s, fun c hc => .inl (h c hc),
    marksOk_of_noMarks fun c hc => by
      have := cs.printable_not_combining c (h c hc)
      simpa [combining_iff] using this⟩

theorem printable_of_ascii {l : List Char}
    (h : ∀ c ∈ l, 0x20 ≤ c.toNat ∧ c.toNat ≤ 0x7E) : ∀ c ∈ l, cs.Printable c :=
  fun c hc => cs.printable_of_ascii (h c hc).1 (h c hc).2

/-- `s` as text the program wrote, if it is printable ASCII. -/
def ofAscii? (s : String) : Option (Text cs .app) :=
  if h : ∀ c ∈ s.toList, 0x20 ≤ c.toNat ∧ c.toNat ≤ 0x7E then some (ofLit s (printable_of_ascii h))
  else none

/-- The decimal digits of `n`. -/
def ofNat (n : Nat) : Text cs .app := (ofAscii? (toString n)).getD empty

/-- The glyphs drawn: the characters, without the combining accents, which take no cell. -/
def glyphs (t : Text cs o) : List (Glyph cs) := cs.glyphs t.text

/-- How many cells `t` takes. -/
def width (t : Text cs o) : Nat := cs.textWidth t.text

end Text

/-- `t!"…"` is text the program wrote, from a literal checked when it compiles: for a charset
known then, every character must be one it allows; for any charset, printable ASCII. -/
macro:max "t!" s:str : term =>
  `(Text.ofLit $s (by first | decide | exact Text.printable_of_ascii (by decide)))

namespace Untrusted

structure Policy where
  /-- Combining marks kept on one character, at most `maxMarks`; beyond them, a stand-in. -/
  maxMarks : Nat := 4
  /-- Lines of a text kept by `lines`. -/
  maxLines : Nat := 20
  tabWidth : Nat := 4

/-- The stand-in for a character refused that is not a control character. -/
def substitute : Char := '␦'

/-- What a character refused shows as: a control character as its Control Picture (`␛` for
ESC), DEL as `␡`, anything else as `␦`. -/
def standIn (c : Char) : Char :=
  if c.toNat < 0x20 then Char.ofNat (0x2400 + c.toNat)
  else if c.toNat == 0x7F then '␡'
  else substitute

def IsControlPicture (c : Char) : Prop := 0x2400 ≤ c.toNat ∧ c.toNat ≤ 0x2426

instance : DecidablePred IsControlPicture := fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem controlPictures : ∀ n < 0x20, IsControlPicture (Char.ofNat (0x2400 + n)) := by decide

theorem standIn_controlPicture (c : Char) : IsControlPicture (standIn c) := by
  unfold standIn
  split
  · exact controlPictures _ ‹_›
  · split <;> decide

theorem controlPicture_not_combining {c : Char} (h : IsControlPicture c) : isCombining c = false := by
  simp only [IsControlPicture] at h
  simp [isCombining]; omega

/-- `l` filtered. `base` says whether the last character kept was one `cs` allows, and `k` how
many combining accents have followed it. -/
def filterChars (cs : Charset) (cap : Nat) : Bool → Nat → List Char → List Char
  | _, _, [] => []
  | base, k, c :: r =>
    if isCombining c then
      if base && decide (k < cap) then c :: filterChars cs cap base (k + 1) r
      else if !base || k == cap then substitute :: filterChars cs cap base (k + 1) r
      else filterChars cs cap base (k + 1) r
    else if cs.Printable c then c :: filterChars cs cap true 0 r
    else standIn c :: filterChars cs cap false 0 r

theorem filterChars_charsOk (cs : Charset) (cap : Nat) (base : Bool) (k : Nat) (l : List Char) :
    ∀ c ∈ filterChars cs cap base k l, cs.Printable c ∨ Combining c := by
  induction l generalizing base k with
  | nil => simp [filterChars]
  | cons c r ih =>
    have hsub : cs.Printable substitute := cs.printable_of_controlPicture (by decide) (by decide)
    have hstand : cs.Printable (standIn c) :=
      cs.printable_of_controlPicture (standIn_controlPicture c).1 (standIn_controlPicture c).2
    intro x hx
    simp only [filterChars] at hx
    split at hx
    · rename_i hm
      split at hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact .inr (combining_iff.mpr hm)
        · exact ih _ _ x hx
      · split at hx
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact .inl hsub
          · exact ih _ _ x hx
        · exact ih _ _ x hx
    · split at hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact .inl ‹_›
        · exact ih _ _ x hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact .inl hstand
        · exact ih _ _ x hx

/-- Each character kept is one of the input or a stand-in. -/
theorem filterChars_sub (cs : Charset) (cap : Nat) (base : Bool) (k : Nat) (l : List Char) :
    ∀ c ∈ filterChars cs cap base k l, c ∈ l ∨ IsControlPicture c := by
  induction l generalizing base k with
  | nil => simp [filterChars]
  | cons c r ih =>
    intro x hx
    have lift : ∀ base k, x ∈ filterChars cs cap base k r → x ∈ c :: r ∨ IsControlPicture x :=
      fun base k h => (ih base k x h).imp (List.mem_cons_of_mem _) id
    simp only [filterChars] at hx
    split at hx
    · split at hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact .inl (List.mem_cons_self ..)
        · exact lift _ _ hx
      · split at hx
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact .inr ⟨by decide, by decide⟩
          · exact lift _ _ hx
        · exact lift _ _ hx
    · split at hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact .inl (List.mem_cons_self ..)
        · exact lift _ _ hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact .inr (standIn_controlPicture _)
        · exact lift _ _ hx

/-- What `filterChars` has written so far, as `marksOk` counts it, in each state it can be in. -/
private def Inv (cap : Nat) (base : Bool) (k : Nat) (run : Option Nat) : Prop :=
  (base = true ∧ k ≤ cap ∧ run = some k) ∨ (base = true ∧ cap < k ∧ run = some 0) ∨
    (base = false ∧ (run = none ∨ run = some 0))

theorem filterChars_marksOk (cs : Charset) (cap : Nat) (hcap : cap ≤ maxMarks) (l : List Char) :
    ∀ base k run, Inv cap base k run → marksOk run (filterChars cs cap base k l) := by
  have hsub : isCombining substitute = false := by decide
  -- After a character that is not an accent, `marksOk` starts again from `some 0`.
  have reset : ∀ {run : Option Nat} {c : Char} {t : List Char}, isCombining c = false →
      marksOk (some 0) t → marksOk run (c :: t) := by
    intro run c t hc ht
    cases run <;> simp [marksOk, hc, ht]
  induction l with
  | nil => intros; cases ‹Option Nat› <;> rfl
  | cons c r ih =>
    intro base k run hinv
    simp only [filterChars]
    split
    · rename_i hm
      split
      · rename_i hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        obtain ⟨rfl, hk⟩ := hb
        have hrun : run = some k := by
          rcases hinv with ⟨_, _, h⟩ | ⟨_, h1, _⟩ | ⟨h, _⟩
          · exact h
          · omega
          · cases h
        subst hrun
        simp only [marksOk, hm, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by omega, ih _ _ _ (.inl ⟨rfl, by omega, rfl⟩)⟩
      · split
        · rename_i hb hb'
          refine reset hsub (ih _ _ _ ?_)
          cases base
          · exact .inr (.inr ⟨rfl, .inr rfl⟩)
          · simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at hb'
            exact .inr (.inl ⟨rfl, by omega, rfl⟩)
        · rename_i hb hb'
          simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, Bool.or_eq_true,
            Bool.not_eq_true', beq_iff_eq, not_or] at hb hb'
          obtain ⟨hbase, hk⟩ := hb'
          have hbase' : base = true := by cases base <;> simp_all
          have hk' : cap < k := by have := hb hbase'; omega
          have hrun : run = some 0 := by
            rcases hinv with ⟨_, h1, _⟩ | ⟨_, _, h⟩ | ⟨h, _⟩
            · omega
            · exact h
            · simp_all
          subst hrun
          exact ih _ _ _ (.inr (.inl ⟨hbase', by omega, rfl⟩))
    · split
      · rename_i hm hp
        exact reset (by simpa using hm) (ih _ _ _ (.inl ⟨rfl, Nat.zero_le _, rfl⟩))
      · exact reset (controlPicture_not_combining (standIn_controlPicture c))
          (ih _ _ _ (.inr (.inr ⟨rfl, .inr rfl⟩)))

/-- One line, filtered: each character `cs` allows is kept, and each it refuses shows as its
stand-in, so that an attempt to steer the terminal shows. A combining accent is kept on the
character before it, up to `p.maxMarks` of them; one more shows as `␦` and the rest go. A newline
shows as `␊`. -/
def line (s : String) (p : Policy := {}) : Text cs .remote :=
  let cap := min p.maxMarks maxMarks
  ⟨String.ofList (filterChars cs cap false 0 s.toList),
    by simpa using filterChars_charsOk cs cap false 0 s.toList,
    by simpa using (filterChars_marksOk cs cap (Nat.min_le_right _ _) s.toList false 0 none
      (.inr (.inr ⟨rfl, .inl rfl⟩)))⟩

/-- Each character of `line s` is one of `s` or a stand-in. -/
theorem line_sub (s : String) (p : Policy) :
    ∀ c ∈ (line (cs := cs) s p).text.toList, c ∈ s.toList ∨ IsControlPicture c := by
  simpa [line] using filterChars_sub cs _ false 0 s.toList

/-- A text as its lines, filtered: tabs become spaces, a carriage return before a newline goes,
and of more than `maxLines` lines, the last kept says how many more there were. -/
def lines (s : String) (p : Policy := {}) :
    {ls : List (Text cs .remote) // ls.length ≤ max 1 p.maxLines} :=
  let tab := String.ofList (List.replicate p.tabWidth ' ')
  let ls := ((s.replace "\r\n" "\n").splitOn "\n").map fun l => line (l.replace "\t" tab) p
  if h : ls.length ≤ p.maxLines then ⟨ls, by omega⟩
  else
    let more := line s!"[{ls.length - (p.maxLines - 1)} more lines not shown]" p
    ⟨ls.take (p.maxLines - 1) ++ [more], by simp; omega⟩

end Untrusted

end Tessera
