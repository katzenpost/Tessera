/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

/-! # Colors and styles -/

namespace Tessera

inductive Color where
  /-- The terminal's own color. -/
  | default
  /-- One of the 16 standard colors; 8–15 are the bright ones. -/
  | ansi (n : Fin 16)
  /-- One of the 256 indexed colors. -/
  | indexed (n : UInt8)
  | rgb (r g b : UInt8)
  deriving DecidableEq, Repr, Inhabited

namespace Color

def black : Color := .ansi 0
def red : Color := .ansi 1
def green : Color := .ansi 2
def yellow : Color := .ansi 3
def blue : Color := .ansi 4
def magenta : Color := .ansi 5
def cyan : Color := .ansi 6
def white : Color := .ansi 7
def brightBlack : Color := .ansi 8
def brightRed : Color := .ansi 9
def brightGreen : Color := .ansi 10
def brightYellow : Color := .ansi 11
def brightBlue : Color := .ansi 12
def brightMagenta : Color := .ansi 13
def brightCyan : Color := .ansi 14
def brightWhite : Color := .ansi 15

end Color

/-- How a cell is drawn. A color left unset is the terminal's own. -/
structure Style where
  fg : Option Color := none
  bg : Option Color := none
  bold : Bool := false
  dim : Bool := false
  italic : Bool := false
  underline : Bool := false
  reverse : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace Style

def fgOf (c : Color) : Style := { fg := some c }
def bgOf (c : Color) : Style := { bg := some c }

/-- `s` laid over `base`: the colors `s` sets replace those of `base`, and the attributes of both
apply. -/
def over (s base : Style) : Style where
  fg := s.fg <|> base.fg
  bg := s.bg <|> base.bg
  bold := s.bold || base.bold
  dim := s.dim || base.dim
  italic := s.italic || base.italic
  underline := s.underline || base.underline
  reverse := s.reverse || base.reverse

/-- Whether `s` is one a program keeps for itself: reverse video, dim, a background, or a
foreground other than the eight basic colours. Text from elsewhere is never drawn in such a style
unless the program puts it there. -/
def reserved (s : Style) : Bool :=
  s.reverse || s.dim || s.bg.isSome ||
    match s.fg with
    | some (.ansi n) => decide (8 ≤ n.val)
    | some (.indexed _) | some (.rgb ..) => true
    | _ => false

end Style

/-- The styles a sender may choose for their text: one of the eight basic colours, bold, italic
and underline. -/
structure RemoteStyle where
  fg : Option (Fin 8) := none
  bold : Bool := false
  italic : Bool := false
  underline : Bool := false
  deriving DecidableEq, Repr, Inhabited

def RemoteStyle.toStyle (r : RemoteStyle) : Style where
  fg := r.fg.map fun n => .ansi ⟨n.val, by omega⟩
  bold := r.bold
  italic := r.italic
  underline := r.underline

/-- A sender cannot choose a reserved style. -/
theorem RemoteStyle.not_reserved (r : RemoteStyle) : r.toStyle.reserved = false := by
  rcases r with ⟨_ | ⟨n, hn⟩, _, _, _⟩ <;> simp [toStyle, Style.reserved] <;> omega

/-- Nor make one by laying their style over another: if the result is reserved, so was what it
was laid over. -/
theorem RemoteStyle.reserved_over (r : RemoteStyle) (base : Style)
    (h : (r.toStyle.over base).reserved = true) : base.reserved = true := by
  rcases r with ⟨_ | ⟨n, hn⟩, b, i, u⟩ <;>
    rcases base with ⟨bfg, bbg, bb, bd, bi, bu, brev⟩ <;>
    simp only [toStyle, Style.over, Style.reserved, Option.map, HOrElse.hOrElse, OrElse.orElse,
      Option.orElse, Bool.false_or, Bool.or_eq_true] at h ⊢
  · exact h
  · rcases h with ((h | h) | h) | h
    · exact .inl (.inl (.inl h))
    · exact .inl (.inl (.inr h))
    · exact .inl (.inr h)
    · simp at h; omega

end Tessera
