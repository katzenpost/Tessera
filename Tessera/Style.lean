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

/-! ## Colour depth -/

/-- How many colours a terminal shows, or none, when the user asked for none with `NO_COLOR`. -/
inductive Depth where
  | none
  | ansi16
  | ansi256
  | truecolor
  deriving DecidableEq, Repr, Inhabited

/-- The nearest of the six levels of the 256-colour cube to `v`. -/
def cubeLevel (v : UInt8) : Nat := if v.toNat < 48 then 0 else if v.toNat < 115 then 1 else (v.toNat - 35) / 40

/-- The 256-colour index nearest `(r, g, b)`: the cube, or the grey ramp for a grey. -/
def rgbTo256 (r g b : UInt8) : UInt8 :=
  if r == g && g == b then
    if r.toNat < 8 then 16 else if r.toNat > 238 then 231 else (232 + (r.toNat - 8) / 10).toUInt8
  else (16 + 36 * cubeLevel r + 6 * cubeLevel g + cubeLevel b).toUInt8

/-- The 16-colour index nearest `(r, g, b)`: the bright one when any channel is high. -/
def rgbTo16 (r g b : UInt8) : Fin 16 :=
  let bit (v : UInt8) (k : Nat) := if v.toNat ≥ 96 then k else 0
  let n := bit r 1 + bit g 2 + bit b 4
  let bright := r.toNat ≥ 192 || g.toNat ≥ 192 || b.toNat ≥ 192
  ⟨(n + if bright then 8 else 0) % 16, Nat.mod_lt _ (by decide)⟩

/-- The 16-colour index nearest 256-colour index `n`. -/
def indexedTo16 (n : UInt8) : Fin 16 :=
  if h : n.toNat < 16 then ⟨n.toNat, h⟩
  else if n.toNat < 232 then
    let c := n.toNat - 16
    let lvl (k : Nat) : UInt8 := if k = 0 then 0 else (55 + 40 * k).toUInt8
    rgbTo16 (lvl (c / 36)) (lvl (c / 6 % 6)) (lvl (c % 6))
  else let v := (8 + 10 * (n.toNat - 232)).toUInt8; rgbTo16 v v v

/-- `c` as a terminal of depth `d` shows it, or no colour. The eight basic colours, and the
terminal's own, are shown as they are at every depth but none. -/
def Color.downgrade : Depth → Color → Option Color
  | .none, _ => none
  | .ansi16, .indexed n => some (.ansi (indexedTo16 n))
  | .ansi16, .rgb r g b => some (.ansi (rgbTo16 r g b))
  | .ansi256, .rgb r g b => some (.indexed (rgbTo256 r g b))
  | _, c => some c

namespace Style

/-- `s` as a terminal of depth `d` can show it, as reserved as it was (`reserved_downgrade`): a
reserved style that only its colour reserved, such as a bright green that becomes no colour, is
shown in reverse video, so that what the program keeps for itself still looks its own. -/
def downgrade (d : Depth) (s : Style) : Style :=
  let t := { s with fg := s.fg.bind (Color.downgrade d), bg := s.bg.bind (Color.downgrade d) }
  if s.reserved && !t.reserved then { t with reverse := true } else t

theorem reserved_downgrade (d : Depth) (s : Style) : (s.downgrade d).reserved = s.reserved := by
  rcases s with ⟨fg, bg, b, dm, i, u, rv⟩
  cases hr : reserved ⟨fg, bg, b, dm, i, u, rv⟩
  · simp only [reserved, Bool.or_eq_false_iff] at hr
    obtain ⟨⟨⟨hrv, hdm⟩, hbg⟩, hfg⟩ := hr
    simp only [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hbg
    subst hrv hdm hbg
    rcases fg with _ | ((_ | n | n | ⟨r, g, b'⟩))
    · cases d <;> simp_all [downgrade, reserved]
    · cases d <;> simp_all [downgrade, reserved, Color.downgrade]
    · have hn : ¬ 8 ≤ (n : Nat) := by simp_all
      cases d <;> simp [downgrade, reserved, Color.downgrade, hn]
    · simp_all
    · simp_all
  · simp only [downgrade]
    split
    · simp [reserved]
    · rename_i h; simp_all

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
