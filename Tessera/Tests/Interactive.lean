/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Input
import Tessera.ListView
import Tessera.Table
import Tessera.Tests.Util

/-! # Input, lists and tables, driven by keys through the application loop -/

namespace Tessera.Tests.Interactive

open Tessera Widget

/-- The final state of `app` after `events`, read from a terminal of no size. -/
def feed {σ : Type} (app : App CS σ Unit) (init : σ) (events : List Event) : IO σ := do
  let queue ← IO.mkRef (events.map Incoming.terminal)
  let screen : Screen := { size := pure (0, 0), write := fun _ => pure () }
  app.loop screen (queue.modifyGet fun | [] => (none, []) | m :: r => (some m, r)) init

def typing : App CS (Input CS × Array String) Unit where
  draw s := s.1.view
  update m s := let (i, t) := s.1.update m; pure ((i, s.2 ++ (t.map (·.text)).toArray), false)

def keys (s : String) : List Event := s.toList.map fun c => .key (.char c)

def ctrl (c : Char) : Event := .key (.char c) { ctrl := true }

def typed (events : List Event) : IO (String × Nat × Array String) := do
  let (i, sent) ← feed typing ({}, #[]) events
  return (i.text.text, i.cursor, sent)

def drawn (w : Widget CS .remote) (width height : Nat) : List String := (w.draw width height).lines

def listOf (n : Nat) : ListView String := { items := (List.range n).toArray.map toString }

def moved (l : ListView String) (ks : List Key) (rows : Nat) : IO (ListView String) :=
  feed { draw := fun _ => .empty, update := fun m l => pure (l.update m rows, false) } l
    (ks.map (.key ·))

def tests : TestM Unit := do
  checkEq "type" ("hello", 5, #[]) (← typed (keys "hello"))
  checkEq "left and insert" ("hexllo", 3, #[]) (← typed (keys "hello" ++ [.key .left, .key .left, .key .left] ++ keys "x"))
  checkEq "home, end" ("ahellob", 7, #[]) (← typed (keys "hello" ++ [.key .home] ++ keys "a" ++ [.key .end_] ++ keys "b"))
  checkEq "backspace, delete" ("lo", 1, #[]) (← typed (keys "hello" ++ [.key .home, .key .right, .key .delete, .key .backspace, .key .right, .key .delete]))
  checkEq "ctrl-w" ("one ", 4, #[]) (← typed (keys "one two  " ++ [ctrl 'w']))
  checkEq "ctrl-u" ("lo", 0, #[]) (← typed (keys "hello" ++ [.key .left, .key .left, ctrl 'u']))
  checkEq "enter sends" ("", 0, #["hi"]) (← typed (keys "hi" ++ [.key .enter, .key .enter]))
  checkEq "history" ("one", 3, #["one", "two"])
    (← typed (keys "one" ++ [.key .enter] ++ keys "two" ++ [.key .enter, .key .up, .key .up]))
  checkEq "history down past the end" ("", 0, #["one"])
    (← typed (keys "one" ++ [.key .enter, .key .up, .key .down]))
  checkEq "accent joins its letter" ("é", 1, #[]) (← typed (keys "é"))
  checkEq "accent moves with its letter" ("e\u0301x", 1, #[]) (← typed (keys "e\u0301x" ++ [.key .left]))
  checkEq "paste with a newline does not send" ("a␊b", 3, #[])
    (← typed [.paste "a\nb"])
  checkEq "paste of an escape" ("]0;x␇", 5, #[]) (← typed [.paste "\x1b]0;x\x07"])
  let long : Input CS := Input.ofText (Untrusted.line "abcdefghij")
  checkEq "scrolls to the cursor" ["ghij "] (drawn long.view 5 1)
  checkEq "cursor in the middle" ["abcd"] (drawn (long.home.view) 4 1)
  checkEq "wide characters scroll whole" ["漢字 "] (drawn (Input.ofText (Untrusted.line "漢字漢字")).view 5 1)
  checkEq "down" 1 (← moved (listOf 5) [.down] 3).selected
  checkEq "down stops at the end" 4 (← moved (listOf 5) [.down, .down, .down, .down, .down, .down] 3).selected
  checkEq "up stops at the start" 0 (← moved (listOf 5) [.up] 3).selected
  checkEq "page down" 3 (← moved (listOf 10) [.pageDown] 3).selected
  checkEq "end" 9 (← moved (listOf 10) [.end_] 3).selected
  let l ← moved (listOf 10) [.down, .down, .down, .down] 3
  checkEq "scrolls only to keep the selection in view" 2 l.offset
  checkEq "list drawn" ["2  ", "3  ", "4  "] (drawn (l.view fun s => str (Untrusted.line s)) 3 3)
  let l ← moved l [.up] 3
  checkEq "moving up within view does not scroll" 2 l.offset
  let t : Widget CS .remote := table [.fit, .ratio 1, .fixed 3] [t!"id", t!"name", t!"n"]
    [[t!"1", t!"alice", t!"12345"], [t!"22", t!"bob", t!"7"]]
  checkEq "table" ["id name  n  ", "1  alice 123", "22 bob   7  "] (drawn t 12 3)
  checkEq "table cut to its width" ["id  n", "1   1", "22  7"] (drawn t 5 3)
  checkEq "fitWidths" [3, 1] (fitWidths 5 [3, 5])
  checkEq "fitWidths stops at the budget" [3] (fitWidths 3 [5, 2])

end Tessera.Tests.Interactive
