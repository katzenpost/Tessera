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

end Style

end Tessera
