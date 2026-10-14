/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

/-! # Characters

A `Charset` decides which characters may be written to a terminal as they are, and how many cells
each takes, together with the laws those decisions must satisfy: nothing it allows is a control,
a bidi control or an invisible character, and everything it allows takes one cell or two.

Every table here is a list of code point ranges. A law about all characters is proved by checking
it on each range of a table, a finite check, and lifting it with `inRanges_iff`. -/

namespace Tessera

def inRanges (n : Nat) (rs : List (Nat × Nat)) : Bool := rs.any fun r => r.1 ≤ n && n ≤ r.2

theorem inRanges_iff {n : Nat} {rs : List (Nat × Nat)} :
    inRanges n rs = true ↔ ∃ r ∈ rs, r.1 ≤ n ∧ n ≤ r.2 := by
  simp [inRanges]

/-- Every range of `inner` lies within one of `outer`. -/
def Covers (outer inner : List (Nat × Nat)) : Prop :=
  ∀ i ∈ inner, ∃ o ∈ outer, o.1 ≤ i.1 ∧ i.2 ≤ o.2

instance {outer inner : List (Nat × Nat)} : Decidable (Covers outer inner) := by
  unfold Covers; infer_instance

theorem inRanges_of_covers {n : Nat} {outer inner : List (Nat × Nat)} (h : Covers outer inner)
    (hn : inRanges n inner = true) : inRanges n outer = true := by
  obtain ⟨i, hi, h1, h2⟩ := inRanges_iff.mp hn
  obtain ⟨o, ho, h3, h4⟩ := h i hi
  exact inRanges_iff.mpr ⟨o, ho, by omega, by omega⟩

/-- Bidi controls, which reorder the text around them. -/
def bidiRanges : List (Nat × Nat) :=
  [(0x61C, 0x61C), (0x200E, 0x200F), (0x202A, 0x202E), (0x2066, 0x2069)]

/-- Characters that take no space and show nothing: zero-width spaces and joiners, word joiners,
the byte order mark, the Mongolian vowel separator and tag characters. -/
def invisibleRanges : List (Nat × Nat) :=
  [(0x180E, 0x180E), (0x200B, 0x200D), (0x2060, 0x2064), (0xFEFF, 0xFEFF), (0xE0000, 0xE007F)]

def Bidi (c : Char) : Prop := inRanges c.toNat bidiRanges = true

def Invisible (c : Char) : Prop := inRanges c.toNat invisibleRanges = true

/-- Combining accents, which a terminal draws over the character before them. -/
def Combining (c : Char) : Prop := 0x300 ≤ c.toNat ∧ c.toNat ≤ 0x36F

def isCombining (c : Char) : Bool := 0x300 ≤ c.toNat && c.toNat ≤ 0x36F

theorem combining_iff {c : Char} : Combining c ↔ isCombining c = true := by
  simp [Combining, isCombining]

instance : DecidablePred Bidi := fun _ => inferInstanceAs (Decidable (_ = true))
instance : DecidablePred Invisible := fun _ => inferInstanceAs (Decidable (_ = true))
instance : DecidablePred Combining := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-! ## Widths -/

/-- Format characters, which reorder or hide text (bidi controls, zero-width spaces and joiners,
word joiners, the byte order mark, tag characters) or pick a glyph's presentation (variation
selectors), and combining marks, which a terminal draws over the character before them. -/
def zeroWidthRanges : List (Nat × Nat) :=
  [(0x300, 0x36F), (0x483, 0x489), (0x591, 0x5BD), (0x5BF, 0x5BF), (0x5C1, 0x5C2),
   (0x5C4, 0x5C5), (0x5C7, 0x5C7), (0x600, 0x605), (0x610, 0x61A), (0x61C, 0x61C),
   (0x64B, 0x65F), (0x670, 0x670), (0x6D6, 0x6DD), (0x6DF, 0x6E4), (0x6E7, 0x6E8),
   (0x6EA, 0x6ED), (0x70F, 0x70F), (0x711, 0x711), (0x730, 0x74A), (0x900, 0x902),
   (0x93A, 0x93A), (0x93C, 0x93C), (0x941, 0x948), (0x94D, 0x94D), (0x951, 0x957),
   (0x962, 0x963), (0xE31, 0xE31), (0xE34, 0xE3A), (0xE47, 0xE4E), (0x1160, 0x11FF),
   (0x180B, 0x180F), (0x1AB0, 0x1AFF), (0x1DC0, 0x1DFF), (0x200B, 0x200F), (0x2028, 0x202E),
   (0x2060, 0x206F), (0x20D0, 0x20FF), (0xFE00, 0xFE0F), (0xFE20, 0xFE2F), (0xFEFF, 0xFEFF),
   (0xFFF9, 0xFFFB), (0x1D167, 0x1D169), (0x1D173, 0x1D182), (0xE0000, 0xE0FFF)]

/-- Characters that take no cell: controls, which a terminal would act on rather than draw, the
soft hyphen, and `zeroWidthRanges`. None of them is ever drawn. -/
def zeroWidth (n : Nat) : Bool :=
  n < 0x20 || (0x7F ≤ n && n < 0xA0) || n == 0xAD || inRanges n zeroWidthRanges

/-- Characters two cells wide: Unicode's East Asian Wide and Fullwidth ones, as terminals take
them from `wcwidth`, CJK and the emoji drawn as pictures among them. Those that terminals with
older width tables draw one cell wide are left out, so that every terminal and Tessera agree:
the emoji and syllables of Unicode 13 and later, and code points not yet assigned in wide blocks.
`make vterm` checks the table against libvterm. -/
def doubleWidthRanges : List (Nat × Nat) :=
  [(0x1100, 0x115F), (0x231A, 0x231B), (0x2329, 0x232A), (0x23E9, 0x23EC), (0x23F0, 0x23F0),
   (0x23F3, 0x23F3), (0x25FD, 0x25FE), (0x2614, 0x2615), (0x2648, 0x2653), (0x267F, 0x267F),
   (0x2693, 0x2693), (0x26A1, 0x26A1), (0x26AA, 0x26AB), (0x26BD, 0x26BE), (0x26C4, 0x26C5),
   (0x26CE, 0x26CE), (0x26D4, 0x26D4), (0x26EA, 0x26EA), (0x26F2, 0x26F3), (0x26F5, 0x26F5),
   (0x26FA, 0x26FA), (0x26FD, 0x26FD), (0x2705, 0x2705), (0x270A, 0x270B), (0x2728, 0x2728),
   (0x274C, 0x274C), (0x274E, 0x274E), (0x2753, 0x2755), (0x2757, 0x2757), (0x2795, 0x2797),
   (0x27B0, 0x27B0), (0x27BF, 0x27BF), (0x2B1B, 0x2B1C), (0x2B50, 0x2B50), (0x2B55, 0x2B55),
   (0x2E80, 0x303E), (0x3041, 0x33FF), (0x3400, 0x4DBF), (0x4E00, 0x9FFF), (0xA000, 0xA4CF),
   (0xA960, 0xA97C), (0xAC00, 0xD7A3), (0xF900, 0xFAFF), (0xFE10, 0xFE19), (0xFE30, 0xFE6F),
   (0xFF00, 0xFF60), (0xFFE0, 0xFFE6), (0x16FE0, 0x16FE3), (0x17000, 0x187F7), (0x18800, 0x18AF2),
   (0x1B000, 0x1B11E), (0x1B150, 0x1B152), (0x1B164, 0x1B167), (0x1B170, 0x1B2FB),
   (0x1F004, 0x1F004), (0x1F0CF, 0x1F0CF), (0x1F18E, 0x1F18E), (0x1F191, 0x1F19A),
   (0x1F200, 0x1F202), (0x1F210, 0x1F23B), (0x1F240, 0x1F248), (0x1F250, 0x1F251),
   (0x1F260, 0x1F265), (0x1F300, 0x1F320), (0x1F32D, 0x1F335), (0x1F337, 0x1F37C),
   (0x1F37E, 0x1F393), (0x1F3A0, 0x1F3CA), (0x1F3CF, 0x1F3D3), (0x1F3E0, 0x1F3F0),
   (0x1F3F4, 0x1F3F4), (0x1F3F8, 0x1F43E), (0x1F440, 0x1F440), (0x1F442, 0x1F4FC),
   (0x1F4FF, 0x1F53D), (0x1F54B, 0x1F54E), (0x1F550, 0x1F567), (0x1F57A, 0x1F57A),
   (0x1F595, 0x1F596), (0x1F5A4, 0x1F5A4), (0x1F5FB, 0x1F64F), (0x1F680, 0x1F6C5),
   (0x1F6CC, 0x1F6CC), (0x1F6D0, 0x1F6D2), (0x1F6D5, 0x1F6D5), (0x1F6EB, 0x1F6EC),
   (0x1F6F4, 0x1F6FA), (0x1F7E0, 0x1F7EB), (0x1F90D, 0x1F93A), (0x1F93C, 0x1F945),
   (0x1F947, 0x1F971), (0x1F973, 0x1F976), (0x1F97A, 0x1F9A2), (0x1F9A5, 0x1F9AA),
   (0x1F9AE, 0x1F9CA), (0x1F9CD, 0x1F9FF), (0x1FA70, 0x1FA73), (0x1FA78, 0x1FA7A),
   (0x1FA80, 0x1FA82), (0x1FA90, 0x1FA95), (0x20000, 0x2FFFD), (0x30000, 0x3FFFD)]

def doubleWidth (n : Nat) : Bool := inRanges n doubleWidthRanges

/-- How many cells `c` takes: 0 for the characters `zeroWidth` names, which are not drawn; 2 for
double-width characters; 1 for the rest. East Asian ambiguous-width characters take one cell, as
terminals outside CJK locales draw them. -/
def charWidth (c : Char) : Nat :=
  let n := c.toNat
  if zeroWidth n then 0 else if doubleWidth n then 2 else 1

/-- How many cells `s` takes. -/
def stringWidth (s : String) : Nat :=
  s.foldl (fun n c => n + charWidth c) 0

/-- The scripts and symbols terminals draw one cell wide. -/
def narrowRanges : List (Nat × Nat) :=
  [(0x20, 0x7E), (0xA0, 0xAC), (0xAE, 0x2FF),        -- Latin, not the soft hyphen
   (0x370, 0x377), (0x37A, 0x37F), (0x384, 0x3FF),   -- Greek
   (0x400, 0x482), (0x48A, 0x52F),                   -- Cyrillic, not its combining marks
   (0x531, 0x556), (0x561, 0x587),                   -- Armenian
   (0x5D0, 0x5EA),                                   -- Hebrew letters
   (0x621, 0x64A),                                   -- Arabic letters
   (0x10A0, 0x10FF),                                 -- Georgian
   (0x1E00, 0x1FFE),                                 -- Latin and Greek extended
   (0x2010, 0x2027), (0x2030, 0x205E),               -- punctuation, not the invisibles
   (0x2070, 0x209C), (0x20A0, 0x20C0),               -- super- and subscripts, currency
   (0x2100, 0x214F), (0x2150, 0x218B),               -- letterlike, number forms
   (0x2190, 0x21FF), (0x2200, 0x22FF),               -- arrows, mathematics
   (0x2400, 0x2426),                                 -- control pictures
   (0x2500, 0x257F)]                                 -- box drawing

def narrow (n : Nat) : Bool := inRanges n narrowRanges

/-- East Asian ambiguous-width characters among those `narrow` keeps, from Unicode 15.1's
`EastAsianWidth.txt`. Terminals in CJK locales draw them two cells wide. -/
def ambiguousRanges : List (Nat × Nat) :=
  [(0xA1, 0xA1), (0xA4, 0xA4), (0xA7, 0xA8), (0xAA, 0xAA), (0xAE, 0xAE), (0xB0, 0xB4),
   (0xB6, 0xBA), (0xBC, 0xBF), (0xC6, 0xC6), (0xD0, 0xD0), (0xD7, 0xD8), (0xDE, 0xE1),
   (0xE6, 0xE6), (0xE8, 0xEA), (0xEC, 0xED), (0xF0, 0xF0), (0xF2, 0xF3), (0xF7, 0xFA),
   (0xFC, 0xFC), (0xFE, 0xFE), (0x101, 0x101), (0x111, 0x111), (0x113, 0x113), (0x11B, 0x11B),
   (0x126, 0x127), (0x12B, 0x12B), (0x131, 0x133), (0x138, 0x138), (0x13F, 0x142),
   (0x144, 0x144), (0x148, 0x14B), (0x14D, 0x14D), (0x152, 0x153), (0x166, 0x167),
   (0x16B, 0x16B), (0x1CE, 0x1CE), (0x1D0, 0x1D0), (0x1D2, 0x1D2), (0x1D4, 0x1D4),
   (0x1D6, 0x1D6), (0x1D8, 0x1D8), (0x1DA, 0x1DA), (0x1DC, 0x1DC), (0x251, 0x251),
   (0x261, 0x261), (0x2C4, 0x2C4), (0x2C7, 0x2C7), (0x2C9, 0x2CB), (0x2CD, 0x2CD),
   (0x2D0, 0x2D0), (0x2D8, 0x2DB), (0x2DD, 0x2DD), (0x2DF, 0x2DF), (0x391, 0x3A1),
   (0x3A3, 0x3A9), (0x3B1, 0x3C1), (0x3C3, 0x3C9), (0x401, 0x401), (0x410, 0x44F),
   (0x451, 0x451), (0x2010, 0x2010), (0x2013, 0x2016), (0x2018, 0x2019), (0x201C, 0x201D),
   (0x2020, 0x2022), (0x2024, 0x2027), (0x2030, 0x2030), (0x2032, 0x2033), (0x2035, 0x2035),
   (0x203B, 0x203B), (0x203E, 0x203E), (0x2074, 0x2074), (0x207F, 0x207F), (0x2081, 0x2084),
   (0x20AC, 0x20AC), (0x2103, 0x2103), (0x2105, 0x2105), (0x2109, 0x2109), (0x2113, 0x2113),
   (0x2116, 0x2116), (0x2121, 0x2122), (0x2126, 0x2126), (0x212B, 0x212B), (0x2153, 0x2154),
   (0x215B, 0x215E), (0x2160, 0x216B), (0x2170, 0x2179), (0x2189, 0x2189), (0x2190, 0x2199),
   (0x21B8, 0x21B9), (0x21D2, 0x21D2), (0x21D4, 0x21D4), (0x21E7, 0x21E7), (0x2200, 0x2200),
   (0x2202, 0x2203), (0x2207, 0x2208), (0x220B, 0x220B), (0x220F, 0x220F), (0x2211, 0x2211),
   (0x2215, 0x2215), (0x221A, 0x221A), (0x221D, 0x2220), (0x2223, 0x2223), (0x2225, 0x2225),
   (0x2227, 0x222C), (0x222E, 0x222E), (0x2234, 0x2237), (0x223C, 0x223D), (0x2248, 0x2248),
   (0x224C, 0x224C), (0x2252, 0x2252), (0x2260, 0x2261), (0x2264, 0x2267), (0x226A, 0x226B),
   (0x226E, 0x226F), (0x2282, 0x2283), (0x2286, 0x2287), (0x2295, 0x2295), (0x2299, 0x2299),
   (0x22A5, 0x22A5), (0x22BF, 0x22BF), (0x2500, 0x254B), (0x2550, 0x2573)]

def ambiguous (n : Nat) : Bool := inRanges n ambiguousRanges

/-- One cell wide or two to Tessera and to terminals, and neither a control nor a format
character. -/
def isPrintable (c : Char) : Bool :=
  let n := c.toNat
  (narrow n || doubleWidth n) && !zeroWidth n

/-! ## Laws -/

structure Charset where
  /-- May be written to a terminal as it is. -/
  Printable : Char → Prop
  [decPrintable : DecidablePred Printable]
  width : Char → Nat
  printable_width   : ∀ c, Printable c → width c = 1 ∨ width c = 2
  printable_not_c0  : ∀ c, Printable c → 0x20 ≤ c.toNat
  printable_not_del : ∀ c, Printable c → c.toNat ≠ 0x7F
  printable_not_c1  : ∀ c, Printable c → ¬ (0x80 ≤ c.toNat ∧ c.toNat < 0xA0)
  printable_not_bidi      : ∀ c, Printable c → ¬ Bidi c
  printable_not_invisible : ∀ c, Printable c → ¬ Invisible c
  printable_not_combining : ∀ c, Printable c → ¬ Combining c
  /-- Printable ASCII, so that any charset can show plain text. -/
  ascii_printable : ∀ n ≤ 0x5E, Printable (Char.ofNat (0x20 + n))
  /-- Control Pictures, U+2400 to U+2426, so that any charset can show a stand-in for a
  character it refuses. -/
  controlPicture_printable : ∀ n ≤ 0x26, Printable (Char.ofNat (0x2400 + n))
  /-- Printable ASCII is one cell wide, as every terminal draws it. -/
  ascii_width : ∀ c, 0x20 ≤ c.toNat → c.toNat ≤ 0x7E → width c = 1

attribute [instance] Charset.decPrintable

theorem Charset.space_width (cs : Charset) : cs.width ' ' = 1 :=
  cs.ascii_width ' ' (by decide) (by decide)

theorem Charset.printable_of_ascii (cs : Charset) {c : Char} (h1 : 0x20 ≤ c.toNat)
    (h2 : c.toNat ≤ 0x7E) : cs.Printable c := by
  have := cs.ascii_printable (c.toNat - 0x20) (by omega)
  rwa [show 0x20 + (c.toNat - 0x20) = c.toNat by omega, Char.ofNat_toNat] at this

theorem Charset.printable_of_controlPicture (cs : Charset) {c : Char} (h1 : 0x2400 ≤ c.toNat)
    (h2 : c.toNat ≤ 0x2426) : cs.Printable c := by
  have := cs.controlPicture_printable (c.toNat - 0x2400) (by omega)
  rwa [show 0x2400 + (c.toNat - 0x2400) = c.toNat by omega, Char.ofNat_toNat] at this

/-- What a terminal does with the characters a charset allows. Tessera cannot prove that a
terminal measures them as it does; theorems that need it take an `Emulator`. -/
structure Emulator (cs : Charset) where
  width : Char → Nat
  agrees : ∀ c, cs.Printable c → width c = cs.width c

theorem zeroWidth_false {n : Nat} (h : zeroWidth n = false) :
    0x20 ≤ n ∧ n ≠ 0x7F ∧ ¬ (0x80 ≤ n ∧ n < 0xA0) ∧ inRanges n zeroWidthRanges = false := by
  simp only [zeroWidth, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff,
    beq_eq_false_iff_ne] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨by omega, by omega, by omega, h4⟩

theorem bidi_covered : Covers zeroWidthRanges bidiRanges := by decide

theorem invisible_covered : Covers zeroWidthRanges invisibleRanges := by decide

theorem combining_covered : Covers zeroWidthRanges [(0x300, 0x36F)] := by decide

theorem not_of_zeroWidth_false {c : Char} {rs : List (Nat × Nat)} (hc : Covers zeroWidthRanges rs)
    (h : zeroWidth c.toNat = false) : ¬ inRanges c.toNat rs = true := fun hr => by
  have := (zeroWidth_false h).2.2.2
  rw [inRanges_of_covers hc hr] at this
  contradiction

theorem isPrintable_zeroWidth {c : Char} (h : isPrintable c = true) : zeroWidth c.toNat = false := by
  simp only [isPrintable, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2

/-- The laws every charset allowing exactly `isPrintable` satisfies, whatever widths it gives. -/
def Charset.ofPrintable (width : Char → Nat)
    (hw : ∀ c, isPrintable c = true → width c = 1 ∨ width c = 2)
    (hascii : ∀ c, 0x20 ≤ c.toNat → c.toNat ≤ 0x7E → width c = 1) : Charset where
  Printable c := isPrintable c = true
  width := width
  printable_width := hw
  printable_not_c0 _ h := (zeroWidth_false (isPrintable_zeroWidth h)).1
  printable_not_del _ h := (zeroWidth_false (isPrintable_zeroWidth h)).2.1
  printable_not_c1 _ h := (zeroWidth_false (isPrintable_zeroWidth h)).2.2.1
  printable_not_bidi _ h := not_of_zeroWidth_false bidi_covered (isPrintable_zeroWidth h)
  printable_not_invisible _ h := not_of_zeroWidth_false invisible_covered (isPrintable_zeroWidth h)
  printable_not_combining c h hc :=
    not_of_zeroWidth_false (c := c) combining_covered (isPrintable_zeroWidth h)
      (inRanges_iff.mpr ⟨(0x300, 0x36F), List.mem_singleton_self _, hc⟩)
  ascii_printable := by decide
  controlPicture_printable := by decide
  ascii_width := hascii

theorem charWidth_printable {c : Char} (h : isPrintable c = true) : charWidth c = 1 ∨ charWidth c = 2 := by
  simp only [charWidth, isPrintable_zeroWidth h, Bool.false_eq_true, ↓reduceIte]
  split <;> simp

/-- How many cells `c` takes in a CJK locale: as `charWidth`, but East Asian ambiguous-width
characters take two. -/
def cjkWidth (c : Char) : Nat :=
  let n := c.toNat
  if zeroWidth n then 0 else if doubleWidth n || ambiguous n then 2 else 1

theorem cjkWidth_printable {c : Char} (h : isPrintable c = true) : cjkWidth c = 1 ∨ cjkWidth c = 2 := by
  simp only [cjkWidth, isPrintable_zeroWidth h, Bool.false_eq_true, ↓reduceIte]
  split <;> simp

theorem inRanges_below {n : Nat} {rs : List (Nat × Nat)} (h : ∀ r ∈ rs, n < r.1) :
    inRanges n rs = false := by
  cases hr : inRanges n rs
  · rfl
  · obtain ⟨r, hr, h1, _⟩ := inRanges_iff.mp hr
    have := h r hr
    omega

set_option maxRecDepth 4000 in
theorem ascii_narrow {c : Char} (h1 : 0x20 ≤ c.toNat) (h2 : c.toNat ≤ 0x7E) :
    zeroWidth c.toNat = false ∧ doubleWidth c.toNat = false ∧ ambiguous c.toNat = false := by
  have below : ∀ rs : List (Nat × Nat), (∀ r ∈ rs, 0x7E < r.1) → inRanges c.toNat rs = false :=
    fun rs h => inRanges_below fun r hr => by have := h r hr; omega
  refine ⟨?_, below doubleWidthRanges (by decide), below ambiguousRanges (by decide)⟩
  simp only [zeroWidth, below _ (by decide : ∀ r ∈ zeroWidthRanges, 0x7E < r.1), Bool.or_false,
    Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  omega

theorem charWidth_ascii (c : Char) (h1 : 0x20 ≤ c.toNat) (h2 : c.toNat ≤ 0x7E) : charWidth c = 1 := by
  obtain ⟨hz, hd, _⟩ := ascii_narrow h1 h2
  simp [charWidth, hz, hd]

theorem cjkWidth_ascii (c : Char) (h1 : 0x20 ≤ c.toNat) (h2 : c.toNat ≤ 0x7E) : cjkWidth c = 1 := by
  obtain ⟨hz, hd, ha⟩ := ascii_narrow h1 h2
  simp [cjkWidth, hz, hd, ha]

/-- The characters terminals outside CJK locales and Tessera agree on the width of. -/
def Charset.standard : Charset :=
  .ofPrintable charWidth (fun _ => charWidth_printable) charWidth_ascii

/-- The same characters, with East Asian ambiguous-width characters two cells wide. -/
def Charset.cjk : Charset := .ofPrintable cjkWidth (fun _ => cjkWidth_printable) cjkWidth_ascii

end Tessera
