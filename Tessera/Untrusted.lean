/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Text

/-! # Text from elsewhere

A terminal is an interpreter: every character a program writes to it is an instruction. Text the
program did not write itself, such as a chat message, a file name or a name someone chose, can
carry instructions that set the clipboard or the title, make the terminal type input back into
the program, move the cursor, or reorder what is shown. `Untrusted.line` and `Untrusted.lines`
turn such text into `Text`, keeping characters by an allowlist and showing every other one as a
visible stand-in, so that an attempt shows.

This module adds what names, pastes and text passed on need beyond that.
`docs/TUI_SECURITY_GUIDELINES.md` covers the rest of what a TUI showing such text should do. -/

namespace Tessera.Untrusted

variable {cs : Charset}

/-! ## Names -/

/-- Glyphs a name could use to fake a badge the program draws: locks and keys, check marks,
shields and warning signs. -/
def badgeRanges : List (Nat × Nat) :=
  [(0x2611, 0x2611), (0x26A0, 0x26A0), (0x2705, 0x2705), (0x2713, 0x2714), (0x1F50F, 0x1F513),
   (0x1F6E1, 0x1F6E1)]

def Badge (c : Char) : Prop := inRanges c.toNat badgeRanges = true

instance : DecidablePred Badge := fun _ => inferInstanceAs (Decidable (_ = true))

theorem controlPicture_not_badge {c : Char} (h : IsControlPicture c) : ¬ Badge c := fun hb => by
  obtain ⟨r, hr, h1, h2⟩ := inRanges_iff.mp hb
  have hall : ∀ r ∈ badgeRanges, r.2 < 0x2400 ∨ 0x2426 < r.1 := by decide
  have := hall r hr
  simp only [IsControlPicture] at h
  omega

/-- A name: text from elsewhere with no glyph that could fake a badge. -/
structure Ident (cs : Charset) where
  text : Text cs .remote
  noBadge : ∀ c ∈ text.text.toList, ¬ Badge c

namespace Ident

/-- A name from elsewhere, filtered as `line` filters, with each badge glyph shown as `␦`. -/
def ofRemote (s : String) (p : Policy := {}) : Ident cs :=
  let pre := String.ofList (s.toList.map fun c => if Badge c then substitute else c)
  ⟨line pre p, fun c hc => by
    rcases line_sub pre p c hc with h | h
    · simp only [pre, String.toList_ofList, List.mem_map] at h
      obtain ⟨d, _, rfl⟩ := h
      split
      · exact controlPicture_not_badge ⟨by decide, by decide⟩
      · assumption
    · exact controlPicture_not_badge h⟩

/-- Letters of other scripts drawn like Latin ones, and digits and symbols drawn like letters, as
the Latin letter they pass for: a small part of Unicode's confusables (UTS #39), for the scripts
`narrow` keeps. -/
def confusables : List (Char × Char) :=
  [('а', 'a'), ('е', 'e'), ('о', 'o'), ('р', 'p'), ('с', 'c'), ('у', 'y'), ('х', 'x'),
   ('і', 'i'), ('ј', 'j'), ('ѕ', 's'), ('һ', 'h'), ('ԁ', 'd'), ('ɡ', 'g'), ('ӏ', 'l'),
   ('α', 'a'), ('ο', 'o'), ('ν', 'v'), ('ρ', 'p'), ('τ', 't'), ('ι', 'i'), ('κ', 'k'),
   ('А', 'a'), ('В', 'b'), ('Е', 'e'), ('К', 'k'), ('М', 'm'), ('Н', 'h'), ('О', 'o'),
   ('Р', 'p'), ('С', 'c'), ('Т', 't'), ('Х', 'x'), ('Α', 'a'), ('Β', 'b'), ('Ε', 'e'),
   ('Ζ', 'z'), ('Η', 'h'), ('Ι', 'i'), ('Κ', 'k'), ('Μ', 'm'), ('Ν', 'n'), ('Ο', 'o'),
   ('Ρ', 'p'), ('Τ', 't'), ('Χ', 'x'), ('Υ', 'y'),
   ('0', 'o'), ('1', 'l'), ('I', 'l'), ('|', 'l'), ('5', 's'), ('$', 's')]

/-- What a name looks like, ignoring case, look-alike letters, accents and separators: two names
with one skeleton are easily taken for each other. -/
def skeletonOf (s : String) : String :=
  String.ofList <| s.toList.filterMap fun c =>
    if isCombining c || c == ' ' || c == '_' || c == '-' || c == '.' then none
    else some ((confusables.lookup c).getD c.toLower)

def skeleton (i : Ident cs) : String := skeletonOf i.text.text

/-- Whether a name mixes Latin letters with Greek or Cyrillic ones, as a forged name might. -/
def mixedScript (i : Ident cs) : Bool :=
  let s := i.text.text
  s.any (fun c => c.isAlpha) && s.any fun c => 0x370 ≤ c.toNat && c.toNat ≤ 0x52F

end Ident

/-! ## Text passed on -/

def pasteStart : String := "\x1b[200~"

def pasteEnd : String := "\x1b[201~"

/-- A paste, without bracketed paste's start and end markers, either of which, left in, would
let the paste end early and the rest of it be taken as keys typed. -/
structure Pasted where
  text : String
  noMarkers : ¬ pasteStart.toList <:+: text.toList ∧ ¬ pasteEnd.toList <:+: text.toList

/-- A paste without its markers and without ESC, which only a marker or an escape sequence
would begin with. -/
def pasted (s : String) : Pasted :=
  let l := ((s.replace pasteStart "").replace pasteEnd "").toList.filter (· != '\x1b')
  have noEsc : '\x1b' ∉ l := by simp [l]
  have hesc : ∀ m : String, '\x1b' ∈ m.toList → ¬ m.toList <:+: l := fun _ hm hi =>
    noEsc (hi.subset hm)
  ⟨String.ofList l, by
    simp only [String.toList_ofList]
    exact ⟨hesc _ (by decide), hesc _ (by decide)⟩⟩

/-- A character another program's terminal would act on, or reorder text by. -/
def Steers (c : Char) : Prop :=
  (c.toNat < 0x20 ∧ c ≠ '\n' ∧ c ≠ '\t') ∨ (0x7F ≤ c.toNat ∧ c.toNat < 0xA0) ∨ Bidi c

instance : DecidablePred Steers := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Text without the characters that another program's terminal would act on or reorder text by:
controls other than newlines and tabs, and bidi controls. For text passed on, such as a message
sent. -/
def withoutControls (s : String) : {t : String // ∀ c ∈ t.toList, ¬ Steers c} :=
  ⟨String.ofList (s.toList.filter fun c => !decide (Steers c)), by simp⟩

end Tessera.Untrusted
