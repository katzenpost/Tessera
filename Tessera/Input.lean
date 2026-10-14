/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.App

/-! # A line to type into

`Input` holds what the user typed as the characters before the cursor and those after it, each
with its combining accents, so the cursor is always between two characters and never past the
end. What is typed or pasted goes through `Untrusted.line`, with the character before the cursor,
so an accent typed after a letter joins it. A newline pasted shows as `␊` and does not send the
line; only Enter does.

The cursor is drawn as a cell in reverse video, not with the terminal's own cursor, so drawing it
needs no operation beyond Tessera's own. The line scrolls to keep it in view
(`cursor_visible`). -/

namespace Tessera

variable {cs : Charset}

structure Input (cs : Charset) where
  /-- The characters before the cursor, the nearest first. -/
  before : List (Text cs .remote) := []
  /-- The characters after the cursor, in order. -/
  after : List (Text cs .remote) := []
  /-- Lines sent, the latest last. -/
  history : Array (Text cs .remote) := #[]
  /-- Which line of `history` is shown, if one is. -/
  browsing : Option Nat := none

namespace Input

/-- Everything typed. -/
def text (i : Input cs) : Text cs .remote :=
  (i.before.reverse ++ i.after).foldl (· ++ ·) .empty

/-- The cursor's position, counted in characters with their accents. -/
def cursor (i : Input cs) : Nat := i.before.length

def length (i : Input cs) : Nat := i.before.length + i.after.length

theorem cursor_le_length (i : Input cs) : i.cursor ≤ i.length := Nat.le_add_right _ _

/-- `t` in the line, the cursor at its end. -/
def ofText (t : Text cs .remote) : Input cs := { before := t.graphemes.reverse }

/-- `s` typed or pasted at the cursor. -/
def insert (i : Input cs) (s : String) : Input cs :=
  let (prev, rest) := match i.before with
    | g :: r => (g.text, r)
    | [] => ("", [])
  { i with before := (Untrusted.line (prev ++ s)).graphemes.reverse ++ rest, browsing := none }

def left (i : Input cs) : Input cs :=
  match i.before with
  | g :: r => { i with before := r, after := g :: i.after }
  | [] => i

def right (i : Input cs) : Input cs :=
  match i.after with
  | g :: r => { i with before := g :: i.before, after := r }
  | [] => i

def home (i : Input cs) : Input cs := { i with before := [], after := i.before.reverse ++ i.after }

def «end» (i : Input cs) : Input cs := { i with before := i.after.reverse ++ i.before, after := [] }

def backspace (i : Input cs) : Input cs := { i with before := i.before.drop 1 }

def delete (i : Input cs) : Input cs := { i with after := i.after.drop 1 }

/-- Delete back to the start of the word before the cursor, and the spaces after it. -/
def deleteWord (i : Input cs) : Input cs :=
  let isSpace (g : Text cs .remote) := g.text == " "
  { i with before := (i.before.dropWhile isSpace).dropWhile (!isSpace ·) }

/-- Show line `n` of the history, or an empty line past its end. -/
def browse (i : Input cs) (n : Nat) : Input cs :=
  match i.history[n]? with
  | some t => { ofText t with history := i.history, browsing := some n }
  | none => { history := i.history }

/-- An earlier line of the history. -/
def up (i : Input cs) : Input cs :=
  match i.browsing with
  | some 0 => i
  | some n => i.browse (n - 1)
  | none => if i.history.isEmpty then i else i.browse (i.history.size - 1)

/-- A later line of the history. -/
def down (i : Input cs) : Input cs :=
  match i.browsing with
  | some n => i.browse (n + 1)
  | none => i

/-- Send the line: what was typed, and the input emptied, with the line added to the history. -/
def submit (i : Input cs) : Input cs × Text cs .remote :=
  let t := i.text
  ({ history := if t.text.isEmpty then i.history else i.history.push t }, t)

/-- The input after `msg`, and the line sent, if Enter sent one. A message that is not a key or
a paste leaves it as it was. -/
def update {ε : Type} (msg : Msg ε) (i : Input cs) : Input cs × Option (Text cs .remote) :=
  match msg with
  | .key .enter _ _ => let (i, t) := i.submit; (i, if t.text.isEmpty then none else some t)
  | .key k m _ =>
    let i := if m.ctrl then
        match k with
        | .char 'a' => i.home
        | .char 'e' => i.«end»
        | .char 'u' => { i with before := [] }
        | .char 'k' => { i with after := [] }
        | .char 'w' => i.deleteWord
        | _ => i
      else
        match k with
        | .char c => if m.alt then i else i.insert (String.singleton c)
        | .backspace => i.backspace
        | .delete => i.delete
        | .left => i.left
        | .right => i.right
        | .home => i.home
        | .end_ => i.«end»
        | .up => i.up
        | .down => i.down
        | _ => i
    (i, none)
  | .paste p _ => (i.insert p.text, none)
  | _ => (i, none)

/-- How many cells `l` takes. -/
def widthOf : List (Text cs .remote) → Nat
  | [] => 0
  | g :: r => g.width + widthOf r

/-- The characters before the cursor shown in `budget` cells, the nearest first: as many as fit. -/
def shown (budget : Nat) : List (Text cs .remote) → List (Text cs .remote)
  | [] => []
  | g :: r => if g.width ≤ budget then g :: shown (budget - g.width) r else []

theorem widthOf_shown (budget : Nat) (l : List (Text cs .remote)) :
    widthOf (shown budget l) ≤ budget := by
  induction l generalizing budget with
  | nil => simp [shown, widthOf]
  | cons g r ih =>
    simp only [shown]
    split
    · have := ih (budget - g.width); simp only [widthOf]; omega
    · simp [widthOf]

/-- The cursor is always in view: the characters shown before it, and its own cell, `cw` wide,
take at most `width` cells, whenever its cell fits at all. -/
theorem cursor_visible (width cw : Nat) (hcw : cw ≤ width) (l : List (Text cs .remote)) :
    widthOf (shown (width - cw) l) + cw ≤ width := by
  have := widthOf_shown (width - cw) l; omega

/-- The line, drawn one row high, with the cursor in reverse video when `focused`. -/
def view (i : Input cs) (focused : Bool := true) : Widget cs .remote :=
  Widget.vLimit 1 <| Widget.sized (vPolicy := .fixed) fun ctx =>
    let (cur, after) := match i.after with
      | g :: r => (g, r)
      | [] => (Text.space, [])
    let kept := shown (ctx.width - cur.width) i.before
    let join (l : List (Text cs .remote)) := l.foldl (· ++ ·) Text.empty
    let cursor : Widget cs .remote :=
      if focused then Widget.withStyle { reverse := true } (Widget.str cur) else Widget.str cur
    Widget.hBox [Widget.str (join kept.reverse), cursor, Widget.str (join after), Widget.fill]

end Input

end Tessera
