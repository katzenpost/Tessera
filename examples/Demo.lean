/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera

/-! # Tessera demo

A list to move through with the arrow keys, the mouse wheel or a click, a line to type into, and a counter that a
background task advances through the application's own events. Enter adds the typed line to the
list; Esc or Ctrl+C quits. With `--inline`, it is drawn in 14 rows below the cursor, not on the
whole screen. -/

open Tessera Widget Untrusted

abbrev CS := Charset.standard

abbrev W := Widget CS .remote

structure State where
  items : ListView (Text CS .remote)
  input : Input CS := {}
  /-- Rows of the list on screen, for paging: the screen's height less the frame around it. -/
  rows : Nat := 10
  placement : Ansi.Placement := .fullscreen
  beats : Nat := 0

def draw (s : State) : W :=
  vBox [
    hBox [
      hLimit 28 (borderWithLabel t!" Items " (s.items.view str)),
      borderWithLabel t!" Tessera " (vBox [padAll 1 (txt
        t!"Up and Down move through the list. Type, then press Enter to add a line to it. Esc quits."),
        fill])],
    vLimit 3 (borderWithLabel t!" New item " (hBox [
      withStyle (Style.fgOf .cyan) (str t!"> "), s.input.view])),
    withStyle { dim := true } (str (t!" heartbeats from a background task: " ++ .ofNat s.beats))]

def update (m : Msg Unit) (s : State) : IO (State × Bool) :=
  match m with
  | .key .esc _ _ => pure (s, true)
  | .key (.char 'c') { ctrl := true, .. } _ => pure (s, true)
  | .key .up _ _ | .key .down _ _ | .key .pageUp _ _ | .key .pageDown _ _ =>
    pure ({ s with items := s.items.update m s.rows }, false)
  | .mouse { kind := .down .left, column, row, .. } _ =>
    -- The list is drawn in a border from the second row, 28 cells wide.
    if column < 28 && row ≥ 1 then pure ({ s with items := s.items.click (row - 1) s.rows }, false)
    else pure (s, false)
  | .mouse .. => pure ({ s with items := s.items.update m s.rows }, false)
  | .resize _ h => pure ({ s with rows := s.placement.height h - 6 }, false)
  | .custom () => pure ({ s with beats := s.beats + 1 }, false)
  | m =>
    let (input, sent) := s.input.update m
    let items := match sent with
      | some t => let l := s.items.push t; l.select (l.items.size - 1) s.rows
      | none => s.items
    pure ({ s with input, items }, false)

def main (args : List String) : IO Unit := do
  let placement : Ansi.Placement := if args.contains "--inline" then .inline 14 else .fullscreen
  let stop ← IO.mkRef false
  let items := #["apples", "bread", "cheese", "dates", "eggs", "figs", "grapes", "honey",
    "ice cream", "jam", "kale", "lemons", "mangoes", "nuts", "olives", "pears"].map (Untrusted.line ·)
  let rows := placement.height (← CrosstermFfi.size).2.toNat - 6
  let final ← App.run (placement := placement) { draw, update, mouse := placement == .fullscreen }
    { items := { items }, rows, placement } fun post => do
    discard <| IO.asTask (prio := .dedicated) do
      while !(← stop.get) do
        IO.sleep 1000
        post ()
  stop.set true
  IO.println s!"{final.items.items.size} items, {final.beats} heartbeats"
