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

def countFocus : Msg Unit → Nat → IO (Nat × Bool)
  | .focus true, n => pure (n + 1, false)
  | .focus false, n => pure (n + 10, false)
  | _, n => pure (n, false)

/-- The rows of the mouse events an application sees. -/
def mouseRows : Msg Unit → List Nat → IO (List Nat × Bool)
  | .mouse e _, rs => pure (rs ++ [e.row], false)
  | _, rs => pure (rs, false)

def mouseSeen (placement : Ansi.Placement) (sh : Nat) (events : List Event) : IO (List Nat) := do
  let queue ← IO.mkRef (events.map Incoming.terminal)
  let screen : Screen := { size := pure (10, sh), write := fun _ => pure (), placement }
  (App.mk (cs := CS) (fun _ => .empty) mouseRows (fun _ => none) none true none (fun _ => [])).loop
    screen (queue.modifyGet fun | [] => (none, []) | m :: r => (some m, r)) []

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
  let l ← feed { draw := fun _ => .empty, update := fun m l => pure (l.update m 3, false) } (listOf 10)
    [.mouse { kind := .scrollDown, column := 0, row := 0 }, .mouse { kind := .scrollDown, column := 0, row := 0 },
     .mouse { kind := .scrollUp, column := 0, row := 0 }]
  checkEq "wheel" 1 l.selected
  let click (row : Nat) : Event := .mouse { kind := .down .left, column := 1, row }
  checkEq "mouse rows on the whole screen" [0, 2, 7] (← mouseSeen .fullscreen 8 [click 0, click 2, click 7])
  checkEq "mouse rows from an inline frame's first row" [0, 2]
    (← mouseSeen (.inline 3) 8 [click 2, click 5, click 7])
  checkEq "after a resize, from where the frame is then" [1]
    (← mouseSeen (.inline 3) 8 [.resize 10 12, click 7, click 10])
  checkEq "click" 2 ((listOf 10).click 2 3).selected
  checkEq "click past the items" 0 ((listOf 2).click 2 3).selected
  checkEq "click below the list" 0 ((listOf 10).click 3 3).selected
  let scrolled := (listOf 10).select 9 3
  checkEq "click in a scrolled list" 8 (scrolled.click 1 3).selected
  checkEq "click keeps the scroll" scrolled.offset (scrolled.click 1 3).offset
  let focus ← feed { draw := fun _ => .empty, update := countFocus } 0 [.focus true, .focus false]
  checkEq "focus" 11 focus
  let t : Widget CS .remote := table [.fit, .ratio 1, .fixed 3] [t!"id", t!"name", t!"n"]
    [[t!"1", t!"alice", t!"12345"], [t!"22", t!"bob", t!"7"]]
  checkEq "table" ["id name  n  ", "1  alice 123", "22 bob   7  "] (drawn t 12 3)
  checkEq "table cut to its width" ["id  n", "1   1", "22  7"] (drawn t 5 3)
  checkEq "a table given more room keeps a row a line" ["id name  n  ", "1  alice 123", "22 bob   7  ", "            ", "            "]
    (drawn t 12 5)
  let wide : Widget CS .remote := hBox [str (Untrusted.line "claude-demo"), fill, str t!"3"]
  checkEq "a selected row that fills its width is drawn whole" ["claude-demo  3", "work          "]
    (drawn (({ items := #["claude-demo", "work"] } : ListView String).view fun s =>
      if s == "claude-demo" then wide else str (Untrusted.line s)) 14 2)
  check "and in reverse video to the edge"
    (((({ items := #["claude-demo", "work"] } : ListView String).view fun s =>
      if s == "claude-demo" then wide else str (Untrusted.line s)).draw 14 2).get 13 0).style.reverse
  check "a list takes all the height it is given, as it asks to"
    (((({ items := #["a"] } : ListView String).view (cs := CS) (o := .remote) fun s => str (Untrusted.line s)).render
      { width := 3, height := 4 }).h == 4)
  checkEq "a row taller than a line takes one" ["a", "b", " "]
    (drawn (({ items := #["a", "b"] } : ListView String).view fun s => vBox [str (Untrusted.line s), fill]) 1 3)
  checkEq "fitWidths" [3, 1] (fitWidths 5 [3, 5])
  checkEq "fitWidths stops at the budget" [3] (fitWidths 3 [5, 2])

end Tessera.Tests.Interactive
