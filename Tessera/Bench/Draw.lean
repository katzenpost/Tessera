/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Widget
import Tessera.Diff
import LeanBench

/-! # Laying out, diffing and encoding frames at common screen sizes

Inputs are read from refs so the compiler cannot hoist the work out of the timed action. -/

namespace Tessera.Bench.Draw

open Widget

private abbrev CS : Charset := .standard

private def cfg : LeanBench.BenchConfig := { suite := some "draw", samples := 10, warmup := 1 }

def screens : List (Nat × Nat) := [(80, 24), (200, 60)]

/-- A chat window: a header, `n` messages from elsewhere starting at `first`, in a border, and a
status bar showing `status`. -/
def chat (n first status : Nat) : Widget CS .remote :=
  let msg (i : Nat) : Text CS .remote :=
    Untrusted.line s!"<peer{i % 7}> message {first + i}: héllo 漢字 🦀 and some more words"
  vBox [withStyle { bold := true } (str t!"Tessera"),
        borderWithLabel t!"room" (vBox ((List.range n).map fun i => str (msg i)) |> viewport 0),
        withStyle { reverse := true } (hBox [str t!"connected", fill ' ', str (Text.ofNat status)])]

def benches : IO (Array LeanBench.Bench) := do
  let out ← IO.mkRef ""
  let size ← IO.mkRef (0 : Nat)
  let mut bs := #[]
  for (w, h) in screens do
    let label := s!"{w}x{h}"
    let status ← IO.mkRef (0 : Nat)
    let old := (chat h 0 0).draw w h
    let new := (chat h 0 1).draw w h
    let scrolled := (chat h 1 0).draw w h
    let bufs ← IO.mkRef (old, new, scrolled)
    bs := bs.push { name := s!"layout {label}", config := cfg,
                    action := do size.set ((chat h 0 (← status.get)).draw w h).lines.length }
    bs := bs.push { name := s!"diff unchanged {label}", config := cfg,
                    action := do let (o, _, _) ← bufs.get; out.set (diff o o) }
    bs := bs.push { name := s!"diff status {label}", config := cfg,
                    action := do let (o, n, _) ← bufs.get; out.set (diff o n) }
    bs := bs.push { name := s!"diff scrolled {label}", config := cfg,
                    action := do let (o, _, s) ← bufs.get; out.set (diff o s) }
    bs := bs.push { name := s!"redraw {label}", config := cfg,
                    action := do let (_, n, _) ← bufs.get; out.set (redraw n) }
  pure bs

end Tessera.Bench.Draw
