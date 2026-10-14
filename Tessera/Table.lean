/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Widget

/-! # Tables

A table lays text out in columns, with one cell of space between them. Each column is a fixed
width, a share of what the fixed and fitted columns leave, or as wide as its widest cell. The
widths are then cut, column by column, to what is left of the width given, so a table never
draws past it (`fitWidths_le`), and each cell is cut to its column. -/

namespace Tessera

variable {cs : Charset} {o : Origin}

inductive Column where
  /-- `n` cells wide. -/
  | fixed (n : Nat)
  /-- `k` shares of the width the other columns leave. -/
  | ratio (k : Nat)
  /-- As wide as its widest cell. -/
  | fit
  deriving DecidableEq, Repr, Inhabited

/-- Widths `ws` cut, in turn, to what is left of `budget`, with a cell of space between each;
columns past the end of the budget are left out. -/
def fitWidths : Nat → List Nat → List Nat
  | _, [] => []
  | b, w :: ws => if b = 0 then [] else let w' := min w b; w' :: fitWidths (b - w' - 1) ws

/-- The columns, and the space between them, take at most the width given. -/
theorem fitWidths_le (b : Nat) (ws : List Nat) :
    (fitWidths b ws).sum + ((fitWidths b ws).length - 1) ≤ b := by
  induction ws generalizing b with
  | nil => simp [fitWidths]
  | cons w ws ih =>
    have := ih (b - min w b - 1)
    simp only [fitWidths]
    split
    · simp
    · simp only [List.sum_cons, List.length_cons]
      by_cases hz : b - min w b - 1 = 0
      · have h0 : fitWidths (b - min w b - 1) ws = [] := by rw [hz]; cases ws <;> simp [fitWidths]
        simp [h0]; omega
      · rcases hws : fitWidths (b - min w b - 1) ws with _ | ⟨x, xs⟩
        · simp; omega
        · rw [hws] at this; simp at this ⊢; omega

/-- The widths of the columns `cols` in `width` cells, for cells `cells` wide, row by row. -/
def columnWidths (cols : List Column) (cells : List (List Nat)) (width : Nat) : List Nat :=
  let widest (j : Nat) := cells.foldl (fun n r => max n (r[j]?.getD 0)) 0
  let firm := cols.zipIdx.map fun (c, j) => match c with
    | .fixed n => n
    | .ratio _ => 0
    | .fit => widest j
  let shares := cols.foldl (fun n c => match c with | .ratio k => n + k | _ => n) 0
  let left := width - firm.sum - (cols.length - 1)
  let raw := cols.zipIdx.map fun (c, j) => match c with
    | .ratio k => if shares = 0 then 0 else left * k / shares
    | _ => firm[j]?.getD 0
  fitWidths width raw

namespace Widget

/-- `rows` in columns `cols` under the program's `header`, which is drawn bold. -/
def table {t : Origin} [Shows t o] (cols : List Column) (header : List (Text cs .app))
    (rows : List (List (Text cs t))) : Widget cs o :=
  sized (vPolicy := .fixed) fun ctx =>
    let widths := columnWidths cols (header.map (·.width) :: rows.map (·.map (·.width))) ctx.width
    let line {u : Origin} [Shows u o] (cells : List (Text cs u)) : Widget cs o :=
      hBox <| (widths.zipIdx.map fun (w, j) =>
        let cell := (cells[j]?.getD .empty).truncate w
        hLimit (w + 1) (hBox [str cell, fill])) ++ [fill]
    vBox (withStyle { bold := true } (line header) :: rows.map line)

end Widget

end Tessera
