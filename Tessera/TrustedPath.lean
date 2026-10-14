/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Untrusted
import Tessera.Widget

/-! # The trusted path

The parts of the screen that tell the user who said something, where they are, and whether it is
safe belong to the program: the header, the status bar, the prompt, and the column that names
each message's sender. A `Frame` has them as widgets of origin `.app`, which hold only text the
program wrote, and the body, where text from elsewhere goes, as one of origin `.remote`. Text
from elsewhere reaches a reserved place only through `Widget.delimited`, cut to a budget and
between the program's delimiters: so does a name a sender chose, drawn as `~name`.

A sender's own styling is a `RemoteStyle`, which cannot be any of the styles the program keeps
for itself, those of its `Theme`. -/

namespace Tessera

open Untrusted Ident Widget

variable {cs : Charset}

/-- The styles the program keeps for itself, each reserved: no sender can draw text in them. -/
structure Theme where
  /-- A contact the user verified. -/
  verified : Style := { fg := some .brightGreen, bold := true }
  /-- A notice from the program itself. -/
  notice : Style := { fg := some .brightBlack, dim := true }
  /-- The status bar and the prompt. -/
  bar : Style := { reverse := true }
  verified_reserved : verified.reserved = true := by decide
  notice_reserved : notice.reserved = true := by decide
  bar_reserved : bar.reserved = true := by decide

/-- Who sent something, as the sender column shows it. -/
inductive SenderLabel (cs : Charset) where
  /-- A contact the user verified, by the name the user gave them. -/
  | verified (petname : Text cs .app)
  /-- A name the sender chose, which the user has not verified. -/
  | unverified (nick : Ident cs)

namespace SenderLabel

/-- The label's text as it is shown, for telling labels apart. -/
def shown : SenderLabel cs → Text cs .remote
  | .verified p => p.lift
  | .unverified n => (t!"~" : Text cs .app).lift ++ n.text

/-- The label in at most `budget` cells: a verified contact by their petname in the theme's
style for them, a name a sender chose after `~`. -/
def widget (θ : Theme) (budget : Nat) : SenderLabel cs → Widget cs .app
  | .verified p => withStyle θ.verified (hLimit budget (str p))
  | .unverified n => delimited t!"~" .empty (budget - 1) n.text

end SenderLabel

/-- A screen's places: the program's own, and the body. -/
structure Frame (cs : Charset) where
  header : Widget cs .app
  body : Widget cs .remote
  statusBar : Widget cs .app
  prompt : Widget cs .app

/-- The frame laid out: the header on the first row, the status bar and the prompt on the last
two, and the body in between, however little of it there is. -/
def Frame.widget (f : Frame cs) : Widget cs .remote :=
  vBox [(vLimit 1 f.header).lift, vBox [f.body, fill], (vLimit 1 f.statusBar).lift,
    (vLimit 1 f.prompt).lift]

/-- A message: the sender's label on its first row of a sender column `labelWidth` wide, which
the program draws, and the lines of the body beside it. No line of the body can reach the sender
column, so none can pass for another message. -/
def message (θ : Theme) (labelWidth : Nat) (sender : SenderLabel cs) (body : List (Text cs .remote)) :
    Widget cs .remote :=
  let column : Widget cs .app :=
    hLimit labelWidth (vBox [hBox [sender.widget θ labelWidth, fill], vLimit (body.length - 1) fill])
  hBox [column.lift, strs body]

/-! ## Rosters -/

/-- A member of a room: how they are labelled, and a short fingerprint of their key, which the
program makes. -/
structure Member (cs : Charset) where
  label : SenderLabel cs
  key : Text cs .app

/-- The first of each element by `f`. -/
def dedupBy {α β : Type} [DecidableEq β] (f : α → β) : List β → List α → List α
  | _, [] => []
  | seen, a :: r => if f a ∈ seen then dedupBy f seen r else a :: dedupBy f (f a :: seen) r

theorem dedupBy_nodup {α β : Type} [DecidableEq β] (f : α → β) :
    ∀ (seen : List β) (l : List α),
      ((dedupBy f seen l).map f).Nodup ∧ ∀ a ∈ dedupBy f seen l, f a ∉ seen
  | _, [] => by simp [dedupBy]
  | seen, a :: r => by
    unfold dedupBy
    split
    · exact dedupBy_nodup f seen r
    · rename_i hn
      obtain ⟨h1, h2⟩ := dedupBy_nodup f (f a :: seen) r
      refine ⟨List.nodup_cons.mpr ⟨fun hm => ?_, h1⟩, fun b hb => ?_⟩
      · obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
        exact h2 b hb (by simp [he])
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact hn
        · exact fun hs => h2 b hb (List.mem_cons_of_mem _ hs)

/-- What a member's label, as shown, looks like. -/
def labelSkeleton (e : Member cs × Text cs .remote) : String := skeletonOf e.2.text

/-- The members of a room with the labels they are shown by, no two of which look alike. -/
structure Roster (cs : Charset) where
  entries : List (Member cs × Text cs .remote)
  distinct : (entries.map labelSkeleton).Nodup

/-- A member's label with their key after it. -/
def Member.withKey (m : Member cs) : Text cs .remote := m.label.shown ++ (t!"#" ++ m.key).lift

/-- A room's members, labelled so that no two look alike. A label that looks like another's gets
its member's key after it. If two still look alike, each label gets its key; and two that look
alike even then are of one key, and only the first is listed. -/
def Roster.build (ms : List (Member cs)) : Roster cs :=
  let collides (m : Member cs) :=
    (ms.filter fun m' => skeletonOf m'.label.shown.text == skeletonOf m.label.shown.text).length > 1
  let first := ms.map fun m => (m, if collides m then m.withKey else m.label.shown)
  if h : (first.map labelSkeleton).Nodup then ⟨first, h⟩
  else
    let keyed := ms.map fun m => (m, m.withKey)
    if h : (keyed.map labelSkeleton).Nodup then ⟨keyed, h⟩
    else ⟨dedupBy labelSkeleton [] keyed, (dedupBy_nodup labelSkeleton [] keyed).1⟩

end Tessera
