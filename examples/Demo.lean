/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera

/-! # Tessera demo

A list to move through with the arrow keys, a line to type into, and a counter that a
background task advances through the application's own events. Enter adds the typed line to the
list; Esc or Ctrl+C quits. -/

open Tessera Widget

abbrev W := Widget Charset.standard

structure State where
  items : Array String
  selected : Nat := 0
  input : String := ""
  beats : Nat := 0

/-- The items, the selected one highlighted, scrolled to keep it in view. -/
def list (items : Array String) (selected : Nat) : W where
  hPolicy := .greedy
  vPolicy := .greedy
  render ctx :=
    let offset := selected + 1 - min (selected + 1) ctx.height
    let row (i : Nat) (s : String) : W :=
      if i == selected then withStyle { reverse := true } (hBox [str s, fill]) else str s
    (viewport offset (vBox (items.toList.zipIdx.map fun (s, i) => row i s))).render ctx

def draw (s : State) : W :=
  vBox [
    hBox [
      hLimit 28 (borderWithLabel " Items " (list s.items s.selected)),
      borderWithLabel " Tessera " (vBox [padAll 1 (txt
        "Up and Down move through the list. Type, then press Enter to add a line to it. Esc quits."),
        fill])],
    vLimit 3 (borderWithLabel " New item " (hBox [
      withStyle (Style.fgOf .cyan) (str "> "), str s.input,
      withStyle { reverse := true } (str " "), fill])),
    withStyle { dim := true } (str s!" heartbeats from a background task: {s.beats}")]

def update : Msg Unit → State → IO (State × Bool)
  | .input (.key .esc _), s => pure (s, true)
  | .input (.key (.char 'c') { ctrl := true, .. }), s => pure (s, true)
  | .input (.key .up _), s => pure ({ s with selected := s.selected - 1 }, false)
  | .input (.key .down _), s => pure ({ s with selected := min (s.selected + 1) (s.items.size - 1) }, false)
  | .input (.key .backspace _), s => pure ({ s with input := s.input.dropEnd 1 |>.toString }, false)
  | .input (.key .enter _), s =>
    if s.input.isEmpty then pure (s, false)
    else pure ({ s with items := s.items.push s.input, input := "", selected := s.items.size }, false)
  | .input (.key (.char c) m), s =>
    if m.ctrl || m.alt then pure (s, false) else pure ({ s with input := s.input.push c }, false)
  | .input (.paste text), s => pure ({ s with input := s.input ++ text }, false)
  | .custom (), s => pure ({ s with beats := s.beats + 1 }, false)
  | _, s => pure (s, false)

def main : IO Unit := do
  let stop ← IO.mkRef false
  let items := #["apples", "bread", "cheese", "dates", "eggs", "figs", "grapes", "honey",
    "ice cream", "jam", "kale", "lemons", "mangoes", "nuts", "olives", "pears"]
  let final ← App.run { draw, update } { items } fun post => do
    discard <| IO.asTask (prio := .dedicated) do
      while !(← stop.get) do
        IO.sleep 1000
        post ()
  stop.set true
  IO.println s!"{final.items.size} items, {final.beats} heartbeats"
