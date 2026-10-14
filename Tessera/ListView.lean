/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.App

/-! # A list to move through

`ListView` is a list with one item selected, scrolled to keep that item in view. It scrolls only
when the selection would leave the rows shown, and wherever it scrolled to, the rows drawn hold
the selected item (`selected_visible`). -/

namespace Tessera

/-- The first row shown when `offset` was, `selected` is the selected row, and `rows` are shown:
`offset`, moved as little as keeps `selected` in view. -/
def scrollTo (offset selected rows : Nat) : Nat :=
  if selected < offset then selected
  else if selected + 1 > offset + rows then selected + 1 - rows
  else offset

theorem selected_visible (offset selected rows : Nat) (h : 0 < rows) :
    scrollTo offset selected rows ≤ selected ∧ selected < scrollTo offset selected rows + rows := by
  unfold scrollTo; split <;> (try split) <;> omega

structure ListView (α : Type) where
  items : Array α
  selected : Nat := 0
  /-- The first row shown. -/
  offset : Nat := 0

namespace ListView

variable {α : Type}

def selectedItem? (l : ListView α) : Option α := l.items[l.selected]?

/-- Select row `n`, or the last if there is no row `n`, and scroll to it in `rows` rows. -/
def select (l : ListView α) (n : Nat) (rows : Nat) : ListView α :=
  let n := min n (l.items.size - 1)
  { l with selected := n, offset := scrollTo l.offset n rows }

def push (l : ListView α) (a : α) : ListView α := { l with items := l.items.push a }

/-- The list after `msg`, when `rows` rows of it are shown: Up and Down move by one, Page Up and
Page Down by a page, Home and End to the first and last. -/
def update {ε : Type} (msg : Msg ε) (rows : Nat) (l : ListView α) : ListView α :=
  match msg with
  | .key .up _ _ => l.select (l.selected - 1) rows
  | .key .down _ _ => l.select (l.selected + 1) rows
  | .key .pageUp _ _ => l.select (l.selected - max rows 1) rows
  | .key .pageDown _ _ => l.select (l.selected + max rows 1) rows
  | .key .home _ _ => l.select 0 rows
  | .key .end_ _ _ => l.select l.items.size rows
  | _ => l

variable {cs : Charset} {o : Origin}

/-- The items, each drawn by `row`, the selected one in reverse video. -/
def view (l : ListView α) (row : α → Widget cs o) : Widget cs o :=
  Widget.sized fun ctx =>
    let offset := scrollTo l.offset l.selected ctx.height
    let shown := (l.items.toList.zipIdx.drop offset).take ctx.height
    Widget.vBox <| shown.map fun (a, i) =>
      if i == l.selected then Widget.withStyle { reverse := true } (Widget.hBox [row a, Widget.fill])
      else row a

end ListView

end Tessera
