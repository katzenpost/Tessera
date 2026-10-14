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

export CrosstermFfi (Event Key Modifiers MouseEvent MouseKind MouseButton)

/-- Proof that a message is a key, a paste or a mouse event read from the terminal: something only
the user can do. Its constructor is private: only `App.loop` makes one, so no message from elsewhere, such as
the network, carries one. -/
structure UserInput where
  private mk ::

/-- A message to the application. -/
inductive Msg (ε : Type) where
  /-- A key the user pressed. -/
  | key (k : Key) (m : Modifiers) (u : UserInput)
  /-- Text the user pasted, without bracketed paste's markers. -/
  | paste (p : Untrusted.Pasted) (u : UserInput)
  /-- What the user did with the mouse, when the application captures it. -/
  | mouse (e : MouseEvent) (u : UserInput)
  /-- The window gained or lost the focus. -/
  | focus (gained : Bool)
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

/-- The message for what arrived. Only here is a `UserInput` made, for a key, a paste or a mouse
event read from the terminal. -/
private def Incoming.toMsg {ε : Type} : Incoming ε → Msg ε
  | .terminal (.key k m) => .key k m ⟨⟩
  | .terminal (.paste text) => .paste (Untrusted.pasted text) ⟨⟩
  | .terminal (.mouse e) => .mouse e ⟨⟩
  | .terminal (.focus g) => .focus g
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
  /-- Whether to capture the mouse, and receive `Msg.mouse`. A terminal that captures the mouse
  leaves selecting text to Shift and the mouse. -/
  mouse : Bool := false

/-- The colour depth the environment asks for: none if `NO_COLOR` is set, 24-bit if `COLORTERM`
says so, 256 colours if `TERM` does, and 16 otherwise. -/
def Depth.detect : IO Depth := do
  if let some v ← IO.getEnv "NO_COLOR" then
    if !v.isEmpty then return .none
  if let some v ← IO.getEnv "COLORTERM" then
    if v == "truecolor" || v == "24bit" then return .truecolor
  if let some v ← IO.getEnv "TERM" then
    if (v.splitOn "256color").length > 1 then return .ansi256
  return .ansi16

/-- What drawing needs from a terminal. -/
structure Screen where
  size : IO (Nat × Nat)
  write : String → IO Unit

namespace App

variable {cs : Charset} {σ ε : Type}

/-- Draw `init`, then update and draw again for each message from `next`, until `update` asks to
quit or `next` has no more. Messages already waiting, which `ready` returns without blocking,
are all taken in before the next frame is drawn, so that a flood of them is drawn once. Returns
the last state. -/
partial def loop (app : App cs σ ε) (screen : Screen) (next : IO (Option (Incoming ε)))
    (init : σ) (ready : IO (Option (Incoming ε)) := pure none) (depth : Depth := .truecolor) :
    IO σ := do
  let (w, h) ← screen.size
  let frame := render init w h
  screen.write (redraw frame ++ titleOutput none (app.title init))
  go init w h frame (app.title init)
where
  /-- The frame for `s`, in the colours the terminal shows. -/
  render (s : σ) (w h : Nat) : Buffer cs w h :=
    let frame := (app.draw s).draw w h
    if depth = .truecolor then frame else frame.mapStyle (Style.downgrade depth)
  /-- The title, written when it changes. -/
  titleOutput (shown new : Option (Text cs .app)) : String :=
    match new with
    | some t => if shown.map (·.text) == some t.text then "" else Ansi.encode [.title t]
    | none => ""
  /-- Update for one message: the new state, the screen's size, and whether to quit. -/
  step (s : σ) (w h : Nat) (i : Incoming ε) : IO (σ × Nat × Nat × Bool) := do
    let m := i.toMsg
    let (w, h) := match m with
      | .resize w' h' => (w', h')
      | _ => (w, h)
    let (s, quit) ← app.update m s
    return (s, w, h, quit)
  /-- Update for each message already waiting. -/
  drain (s : σ) (w h : Nat) : IO (σ × Nat × Nat × Bool) := do
    let some i ← ready | return (s, w, h, false)
    let (s, w, h, quit) ← step s w h i
    if quit then return (s, w, h, true) else drain s w h
  go (s : σ) (w h : Nat) (shown : Buffer cs w h) (title : Option (Text cs .app)) : IO σ := do
    let some i ← next | return s
    let (s, w', h', quit) ← step s w h i
    if quit then return s
    let (s, w', h', quit) ← drain s w' h'
    if quit then return s
    let frame := render s w' h'
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

/-- Run `app` from `init` in the terminal's alternate screen, in raw mode, in the colours the
environment asks for (`Depth.detect`), and return its last state. `start` is called once with a function that sends the application one of its own events;
it may keep that function and call it from other tasks. -/
def run (app : App cs σ ε) (init : σ) (start : (ε → IO Unit) → IO Unit := fun _ => pure ()) :
    IO σ := do
  let messages ← Std.CloseableChannel.new (α := Incoming ε)
  let send (m : Incoming ε) : IO Unit := discard <| messages.send m
  let stop ← IO.mkRef false
  let screen ← terminal
  let depth ← Depth.detect
  CrosstermFfi.enableRawMode
  CrosstermFfi.enterAlternateScreen
  CrosstermFfi.hideCursor
  CrosstermFfi.enableBracketedPaste
  CrosstermFfi.enableFocusChange
  if app.mouse then CrosstermFfi.enableMouseCapture
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
    app.loop screen (do IO.wait (← messages.recv)) init messages.tryRecv depth
  catch e =>
    -- Shown after the terminal is restored: filtered, as it may quote text from elsewhere.
    throw (IO.userError ("\n".intercalate ((Untrusted.lines (cs := cs) (toString e)).1.map (·.text))))
  finally
    stop.set true
    discard <| IO.wait input
    discard <| IO.wait ticker
    if app.mouse then CrosstermFfi.disableMouseCapture
    CrosstermFfi.disableFocusChange
    CrosstermFfi.disableBracketedPaste
    CrosstermFfi.showCursor
    CrosstermFfi.leaveAlternateScreen
    CrosstermFfi.disableRawMode

end App

end Tessera
