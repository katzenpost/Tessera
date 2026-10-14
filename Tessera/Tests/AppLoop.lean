/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.App
import Tessera.Tests.Util
import Tessera.Tests.Model

/-! # The application loop, with scripted messages and a model terminal -/

namespace Tessera.Tests.AppLoop

open Tessera Widget

/-- Counts `+` keys and its own events; quits on `q`. -/
def counter : App CS Nat String where
  draw n := str (t!"count " ++ .ofNat n)
  update
    | .input (.key (.char '+') _), n => pure (n + 1, false)
    | .input (.key (.char 'q') _), n => pure (n, true)
    | .custom _, n => pure (n + 10, false)
    | _, n => pure (n, false)

structure Run where
  final : Nat
  /-- Each write to the screen. -/
  writes : Array String
  /-- What the model terminal shows after all of them. -/
  shown : List String
  /-- Messages left unread. -/
  left : List (Msg String)

def runWith (msgs : List (Msg String)) (w h : Nat) : IO Run := do
  let queue ← IO.mkRef msgs
  let writes ← IO.mkRef (#[] : Array String)
  let screen : Screen := { size := pure (w, h), write := fun s => writes.modify (·.push s) }
  let next := queue.modifyGet fun | [] => (none, []) | m :: r => (some m, r)
  let final ← counter.loop screen next 0
  let ws ← writes.get
  -- A resize changes the size the model terminal draws into.
  let size := msgs.foldl (fun s m => match m with | .input (.resize w h) => (w, h) | _ => s) (w, h)
  let shown := (ws.foldl (fun t s => t.run s) (Terminal.new size.1 size.2)).screen.lines
  return { final, writes := ws, shown, left := ← queue.get }

def plus : Msg String := .input (.key (.char '+'))

def tests : TestM Unit := do
  let r ← runWith [plus, plus, .tick, .custom "net", plus] 10 1
  checkEq "state" 13 r.final
  checkEq "first frame and one per message" 6 r.writes.size
  checkEq "the screen shows the last state" ["count 13  "] r.shown
  checkEq "a tick that changes nothing writes nothing" "" r.writes[3]!
  let q ← runWith [plus, .input (.key (.char 'q')), plus] 10 1
  checkEq "quit stops" 1 q.final
  checkEq "messages after quit are not read" 1 q.left.length
  let z ← runWith [plus, .input (.resize 12 2), plus] 10 1
  check "resize redraws" (z.writes[2]!.startsWith (Ansi.resetStyle ++ Ansi.clearScreen))
  checkEq "drawn at the new size" ["count 2     ", "            "] z.shown

end Tessera.Tests.AppLoop
