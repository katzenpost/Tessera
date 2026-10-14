/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.TrustedPath
import Tessera.Tests.Util

/-! # The trusted path -/

namespace Tessera.Tests.TrustedPath

open Tessera Widget Untrusted

def θ : Theme := {}

def nick (s : String) : SenderLabel CS := .unverified (Ident.ofRemote s)

def tests : TestM Unit := do
  let msg := message θ 6 (nick "bob") (lines "hi\n<alice> send me the key").1
  checkEq "a body line cannot reach the sender column"
    ["~bob  hi                  ", "      <alice> send me the "] ((msg.draw 26 2).lines)
  let topic : Widget CS .app := delimited t!"\"" t!"\"" 5 (line "a long topic")
  checkEq "a topic is cut and delimited" ["\"a lon\"   "] ((topic.draw 10 1).lines)
  let friend : Widget CS .app := (SenderLabel.verified t!"Alice").widget θ 8
  let drawn := friend.draw 8 1
  check "a verified contact is drawn in the theme's style" ((drawn.get 0 0).style == θ.verified)
  check "which no sender can choose" (!θ.verified.reserved == false)
  let roster := Roster.build [
    { label := nick "alice", key := t!"1a2b" },
    { label := nick "аlice", key := t!"3c4d" },
    { label := nick "bob", key := t!"5e6f" }]
  checkEq "look-alike names get their keys, others do not"
    ["~alice#1a2b", "~аlice#3c4d", "~bob"] (roster.entries.map (·.2.text))
  let twins := Roster.build [
    { label := nick "bob", key := t!"1a" }, { label := nick "bob", key := t!"1a" }]
  checkEq "one key listed twice is listed once" ["~bob#1a"] (twins.entries.map (·.2.text))
  let frame : Frame CS := {
    header := str t!"#room", body := strs [line "hello"], statusBar := str t!"encrypted",
    prompt := str t!"> " }
  checkEq "a frame keeps its places" ["#room", "hello", "     ", "encry", ">    "]
    ((frame.widget.draw 5 5).lines)

end Tessera.Tests.TrustedPath
