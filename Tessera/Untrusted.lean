/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Widget

/-! # Text from elsewhere

A terminal is an interpreter: every character a program writes to it is an instruction. Text the
program did not write itself, such as a chat message, a file name or a name someone chose, can
carry instructions that set the clipboard or the title, make the terminal type input back into
the program, move the cursor, or reorder what is shown. This module turns such text into `Safe`
text, which `Widget.safe` draws.

Filtering keeps characters by an allowlist, not a blocklist: a character is kept only when it is
printable and the terminal and Tessera agree on how many cells it takes. Anything else becomes a
visible stand-in rather than vanishing, so that an attempt shows: a control character becomes its
Control Picture (`␛` for ESC, `␊` for a newline), DEL becomes `␡`, and every other character
refused becomes `␦`.

Agreeing on width matters as much as refusing controls. Tessera lays a row out by its own idea of
each character's width; a character the terminal draws wider or narrower shifts everything after
it on that row, into whatever is drawn beside it. So the allowlist holds the scripts and symbols
terminals draw one cell wide, and the characters `charWidth` and terminals both take as two cells
wide (CJK, and emoji drawn as pictures). East Asian ambiguous-width characters are taken as one
cell, as terminals outside CJK locales draw them.

`docs/TUI_SECURITY_GUIDELINES.md` covers the rest of what a TUI showing such text should do. -/

namespace Tessera.Untrusted

/-- Text that may be drawn: filtered, or written by the program itself. One line. -/
structure Safe where
  private mk ::
  text : String
  deriving Inhabited, BEq, Repr

/-- Text the program wrote itself, which needs no filtering. Never use it for text from
elsewhere. -/
def Safe.trusted (s : String) : Safe := ⟨s⟩

instance : Append Safe := ⟨fun a b => ⟨a.text ++ b.text⟩⟩

/-- The stand-in for a character refused that is not a control character. -/
def substitute : Char := '␦'

structure Policy where
  /-- Combining marks kept on one character; beyond them, a stand-in. -/
  maxMarks : Nat := 4
  /-- Lines of a text kept by `lines`. -/
  maxLines : Nat := 20
  tabWidth : Nat := 4

/-- Combining accents, kept on the character before them. -/
def combining (n : Nat) : Bool := 0x300 ≤ n && n ≤ 0x36F

/-- Whether `c` may be drawn as it is: its width is certain, or it is a combining accent. -/
def allowed (c : Char) : Bool :=
  let n := c.toNat
  combining n || isPrintable c

/-- What a character refused shows as. -/
def standIn (c : Char) : Char :=
  let n := c.toNat
  if n < 0x20 then Char.ofNat (0x2400 + n)
  else if n == 0x7F then '␡'
  else substitute

/-- One line, filtered: a newline in it shows as `␊`, as every character refused shows. -/
def line (s : String) (p : Policy := {}) : Safe := Id.run do
  let mut out := ""
  let mut marks := 0
  let mut base := false
  for c in s.toList do
    if combining c.toNat then
      if base && marks < p.maxMarks then
        out := out.push c
      else if !base || marks == p.maxMarks then
        out := out.push substitute
      marks := marks + 1
    else if allowed c then
      out := out.push c
      marks := 0
      base := true
    else
      out := out.push (standIn c)
      marks := 0
      base := false
  return ⟨out⟩

/-- A text as its lines, filtered: tabs become spaces, a carriage return before a newline goes,
and of more than `maxLines` lines, the last kept says how many more there were. -/
def lines (s : String) (p : Policy := {}) : List Safe :=
  let tab := String.ofList (List.replicate p.tabWidth ' ')
  let ls := ((s.replace "\r\n" "\n").splitOn "\n").map fun l => line (l.replace "\t" tab) p
  if ls.length ≤ p.maxLines then ls
  else ls.take (p.maxLines - 1) ++ [⟨s!"[{ls.length - (p.maxLines - 1)} more lines not shown]"⟩]

/-- A paste without bracketed paste's start and end markers, either of which, left in, would let
the paste end early and the rest of it be taken as keys typed. -/
def pasted (s : String) : String := (s.replace "\x1b[200~" "").replace "\x1b[201~" ""

/-- Text without the characters that another program's terminal would act on or reorder text by:
controls other than newlines and tabs, and bidi controls. For text passed on, such as a message
sent. -/
def withoutControls (s : String) : String :=
  String.ofList <| s.toList.filter fun c =>
    let n := c.toNat
    c == '\n' || c == '\t' ||
      !(n < 0x20 || (0x7F ≤ n && n < 0xA0) || inRanges n [(0x202A, 0x202E), (0x2066, 0x2069),
        (0x200E, 0x200F), (0x61C, 0x61C)])

/-! ## Names that look alike -/

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
def skeleton (s : String) : String :=
  String.ofList <| (line s).text.toList.filterMap fun c =>
    if combining c.toNat || c == ' ' || c == '_' || c == '-' || c == '.' then none
    else some ((confusables.lookup c).getD c.toLower)

/-- Whether a name mixes Latin letters with Greek or Cyrillic ones, as a forged name might. -/
def mixedScript (s : String) : Bool :=
  s.any (fun c => c.isAlpha) && s.any fun c => 0x370 ≤ c.toNat && c.toNat ≤ 0x52F

end Tessera.Untrusted

namespace Tessera.Widget

open Untrusted

/-- Safe text, on one row. -/
def safe (s : Safe) : Widget := str s.text

/-- Safe text, word-wrapped. -/
def safeTxt (s : Safe) : Widget := txt s.text

end Tessera.Widget
