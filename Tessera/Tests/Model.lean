/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Buffer
import Tessera.Tests.Util

/-! # A model terminal

Interprets the escape sequences Tessera writes, to check what a terminal would show. -/

namespace Tessera.Tests

structure Terminal (w h : Nat) where
  screen : Buffer CS w h
  x : Nat := 0
  y : Nat := 0
  style : Style := {}

namespace Terminal

variable {w h : Nat}

def new (width height : Nat) : Terminal width height := { screen := .blank width height }

def showing (b : Buffer CS w h) : Terminal w h := { screen := b }

/-- Apply SGR parameters to a style. -/
partial def sgr (s : Style) : List Nat → Style
  | [] => s
  | 0 :: r => sgr {} r
  | 1 :: r => sgr { s with bold := true } r
  | 2 :: r => sgr { s with dim := true } r
  | 3 :: r => sgr { s with italic := true } r
  | 4 :: r => sgr { s with underline := true } r
  | 7 :: r => sgr { s with reverse := true } r
  | 39 :: r => sgr { s with fg := some .default } r
  | 49 :: r => sgr { s with bg := some .default } r
  | 38 :: 5 :: n :: r => sgr { s with fg := some (.indexed n.toUInt8) } r
  | 48 :: 5 :: n :: r => sgr { s with bg := some (.indexed n.toUInt8) } r
  | 38 :: 2 :: a :: b :: c :: r => sgr { s with fg := some (.rgb a.toUInt8 b.toUInt8 c.toUInt8) } r
  | 48 :: 2 :: a :: b :: c :: r => sgr { s with bg := some (.rgb a.toUInt8 b.toUInt8 c.toUInt8) } r
  | n :: r =>
    if 30 ≤ n && n < 38 then sgr { s with fg := some (.ansi (Fin.ofNat 16 (n - 30))) } r
    else if 90 ≤ n && n < 98 then sgr { s with fg := some (.ansi (Fin.ofNat 16 (n - 82))) } r
    else if 40 ≤ n && n < 48 then sgr { s with bg := some (.ansi (Fin.ofNat 16 (n - 40))) } r
    else if 100 ≤ n && n < 108 then sgr { s with bg := some (.ansi (Fin.ofNat 16 (n - 92))) } r
    else sgr s r

def params (p : String) : List Nat := (p.splitOn ";").map (·.toNat!)

def control (t : Terminal w h) (p : String) (final : Char) : Terminal w h :=
  match final with
  | 'H' =>
    match params p with
    | [r, c] => { t with y := r - 1, x := c - 1 }
    | _ => { t with x := 0, y := 0 }
  | 'm' => { t with style := sgr t.style (params p) }
  | 'J' => { t with screen := .blank w h { bg := t.style.bg } }
  | _ => t

def putChar (t : Terminal w h) (c : Char) : Terminal w h :=
  let (screen, x) := t.screen.putString t.x t.y (CS.glyphs (String.singleton c)) t.style
  { t with screen, x := x.val }

/-- Run `out` on the terminal. -/
partial def run (t : Terminal w h) (out : String) : Terminal w h :=
  go t out.toList
where
  go (t : Terminal w h) : List Char → Terminal w h
    | '\x1b' :: '[' :: rest =>
      let p := rest.takeWhile fun c => c.isDigit || c == ';'
      match rest.drop p.length with
      | f :: rest' => go (t.control (String.ofList p) f) rest'
      | [] => t
    | c :: rest => go (t.putChar c) rest
    | [] => t

end Terminal

end Tessera.Tests
