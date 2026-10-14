/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import CrosstermFfi
import Std.Sync.Channel
import Tessera.Diff
import Tessera.Widget
import Tessera.Untrusted

/-! # Applications

An application is a state, a function that draws it, and a function that updates it for each
message: an input event, a timer tick, or an event of the application's own, such as a message
arriving from the network. After each update the screen is drawn again, writing only what
changed. -/

namespace Tessera

export CrosstermFfi (Event Key Modifiers)

/-- Proof that a message is a key or a paste read from the terminal: something only the user can
do. Its constructor is private: only `App.loop` makes one, so no message from elsewhere, such as
the network, carries one. -/
structure UserInput where
  private mk ::

/-- A message to the application. -/
inductive Msg (ε : Type) where
  /-- A key the user pressed. -/
  | key (k : Key) (m : Modifiers) (u : UserInput)
  /-- Text the user pasted, without bracketed paste's markers. -/
  | paste (p : Untrusted.Pasted) (u : UserInput)
  | resize (width height : Nat)
  | tick
  /-- An event of the application's own, such as a message from the network. -/
  | custom (e : ε)

/-- What reaches the application loop: an event read from the terminal, a tick, or an event of
the application's own. `App.run` makes `terminal` only from what it reads from the terminal; an
event from elsewhere arrives as `custom`. -/
inductive Incoming (ε : Type) where
  | terminal (e : Event)
  | tick
  | custom (e : ε)

/-- The message for what arrived. Only here is a `UserInput` made, for a key or a paste read from
the terminal. -/
private def Incoming.toMsg {ε : Type} : Incoming ε → Msg ε
  | .terminal (.key k m) => .key k m ⟨⟩
  | .terminal (.paste text) => .paste (Untrusted.pasted text) ⟨⟩
  | .terminal (.resize w h) => .resize w h
  | .tick => .tick
  | .custom e => .custom e

/-- An application with state `σ` and events of its own of type `ε`, drawn with the characters
`cs` allows. -/
structure App (cs : Charset) (σ ε : Type) where
  draw : σ → Widget cs .remote
  /-- The new state, and whether to quit. -/
  update : Msg ε → σ → IO (σ × Bool)
  /-- The window's title, if the application sets one: text it wrote, never text from
  elsewhere. -/
  title : σ → Option (Text cs .app) := fun _ => none
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
partial def loop (app : App cs σ ε) (screen : Screen) (next : IO (Option (Incoming ε)))
    (init : σ) : IO σ := do
  let (w, h) ← screen.size
  let frame := (app.draw init).draw w h
  screen.write (redraw frame ++ titleOutput none (app.title init))
  go init w h frame (app.title init)
where
  /-- The title, written when it changes. -/
  titleOutput (shown new : Option (Text cs .app)) : String :=
    match new with
    | some t => if shown.map (·.text) == some t.text then "" else Ansi.encode [.title t]
    | none => ""
  go (s : σ) (w h : Nat) (shown : Buffer cs w h) (title : Option (Text cs .app)) : IO σ := do
    let some i ← next | return s
    let m := i.toMsg
    let (w', h') := match m with
      | .resize w' h' => (w', h')
      | _ => (w, h)
    let (s, quit) ← app.update m s
    if quit then return s
    let frame := (app.draw s).draw w' h'
    let out := if hs : w = w' ∧ h = h' then diff (cast (by rw [hs.1, hs.2]) shown) frame
      else redraw frame
    screen.write (out ++ titleOutput title (app.title s))
    go s w' h' frame (app.title s)

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
  let messages ← Std.CloseableChannel.new (α := Incoming ε)
  let send (m : Incoming ε) : IO Unit := discard <| messages.send m
  let stop ← IO.mkRef false
  let screen ← terminal
  CrosstermFfi.enableRawMode
  CrosstermFfi.enterAlternateScreen
  CrosstermFfi.hideCursor
  CrosstermFfi.enableBracketedPaste
  let input ← IO.asTask (prio := .dedicated) do
    while !(← stop.get) do
      if let some e ← CrosstermFfi.poll 50 then send (.terminal e)
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
