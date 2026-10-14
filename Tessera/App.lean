/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import CrosstermFfi
import Std.Sync.Channel
import Tessera.Diff
import Tessera.Widget

/-! # Applications

An application is a state, a function that draws it, and a function that updates it for each
message: an input event, a timer tick, or an event of the application's own, such as a message
arriving from the network. After each update the screen is drawn again, writing only what
changed. -/

namespace Tessera

export CrosstermFfi (Event Key Modifiers)

inductive Msg (ε : Type) where
  | input (e : Event)
  | tick
  | custom (e : ε)

/-- An application with state `σ` and events of its own of type `ε`, drawn with the characters
`cs` allows. -/
structure App (cs : Charset) (σ ε : Type) where
  draw : σ → Widget cs
  /-- The new state, and whether to quit. -/
  update : Msg ε → σ → IO (σ × Bool)
  /-- How often to send `Msg.tick`, if at all. -/
  tickMs : Option UInt32 := none

/-- What drawing needs from a terminal. -/
structure Screen where
  size : IO (Nat × Nat)
  write : String → IO Unit

namespace App

variable {cs : Charset} {σ ε : Type}

/-- Draw `init`, then update and draw again for each message from `next`, until `update` asks to
quit or `next` has no more. Returns the last state. -/
partial def loop (app : App cs σ ε) (screen : Screen) (next : IO (Option (Msg ε))) (init : σ) :
    IO σ := do
  let (w, h) ← screen.size
  let frame := (app.draw init).draw w h
  screen.write (redraw frame)
  go init w h frame
where
  go (s : σ) (w h : Nat) (shown : Buffer cs w h) : IO σ := do
    let some m ← next | return s
    let (w', h') := match m with
      | .input (.resize w' h') => (w', h')
      | _ => (w, h)
    let (s, quit) ← app.update m s
    if quit then return s
    let frame := (app.draw s).draw w' h'
    if hs : w = w' ∧ h = h' then
      screen.write (diff (cast (by rw [hs.1, hs.2]) shown) frame)
    else
      screen.write (redraw frame)
    go s w' h' frame

/-- The terminal, through crossterm and standard output. -/
def terminal : IO Screen := do
  let out ← IO.getStdout
  return {
    size := do
      let (w, h) ← CrosstermFfi.size
      return (w.toNat, h.toNat)
    write := fun s => do out.putStr s; out.flush }

/-- Run `app` from `init` in the terminal's alternate screen, in raw mode, and return its last
state. `start` is called once with a function that sends the application one of its own events;
it may keep that function and call it from other tasks. -/
def run (app : App cs σ ε) (init : σ) (start : (ε → IO Unit) → IO Unit := fun _ => pure ()) :
    IO σ := do
  let messages ← Std.CloseableChannel.new (α := Msg ε)
  let send (m : Msg ε) : IO Unit := discard <| messages.send m
  let stop ← IO.mkRef false
  let screen ← terminal
  CrosstermFfi.enableRawMode
  CrosstermFfi.enterAlternateScreen
  CrosstermFfi.hideCursor
  CrosstermFfi.enableBracketedPaste
  let input ← IO.asTask (prio := .dedicated) do
    while !(← stop.get) do
      if let some e ← CrosstermFfi.poll 50 then send (.input e)
  let ticker ← IO.asTask (prio := .dedicated) do
    if let some ms := app.tickMs then
      while !(← stop.get) do
        IO.sleep ms
        send .tick
  try
    start (send ∘ .custom)
    app.loop screen (do IO.wait (← messages.recv)) init
  finally
    stop.set true
    discard <| IO.wait input
    discard <| IO.wait ticker
    CrosstermFfi.disableBracketedPaste
    CrosstermFfi.showCursor
    CrosstermFfi.leaveAlternateScreen
    CrosstermFfi.disableRawMode

end App

end Tessera
