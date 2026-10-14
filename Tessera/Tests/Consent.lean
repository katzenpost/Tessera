/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Consent
import Tessera.Tests.Util

/-! # Consent

A small application asks a question when `d` is pressed, and counts time in ticks of 100 ms. -/

namespace Tessera.Tests.Consent

open Tessera Widget

structure S where
  asked : Option (Confirmation CS) := none
  confirmed : Bool := false
  clock : Nat := 0
  pasted : String := ""
  fromNetwork : Nat := 0

def app : App CS S String where
  draw _ := str t!"."
  update
    | .key (.char 'd') _ u, s => pure ({ s with asked := some (.ask u t!"Delete it?" s.clock) }, false)
    | m@(.key _ _ _), s =>
      match s.asked with
      | some c => pure ({ s with confirmed := (c.answer m s.clock).isSome }, false)
      | none => pure (s, false)
    | .paste p _, s => pure ({ s with pasted := p.text }, false)
    | .tick, s => pure ({ s with clock := s.clock + 100 }, false)
    | .custom _, s => pure ({ s with fromNetwork := s.fromNetwork + 1 }, false)
    | _, s => pure (s, false)
  title s := if s.confirmed then some t!"done" else some t!"asking"

def runWith (msgs : List (Incoming String)) : IO (S × Array String) := do
  let queue ← IO.mkRef msgs
  let writes ← IO.mkRef (#[] : Array String)
  let screen : Screen := { size := pure (4, 1), write := fun s => writes.modify (·.push s) }
  let next := queue.modifyGet fun | [] => (none, []) | m :: r => (some m, r)
  let s ← app.loop screen next {}
  return (s, ← writes.get)

def shown : Except String Typed → String
  | .ok (.message t) => s!"message {t}"
  | .ok (.command n a) => s!"command {n} {a}"
  | .error n => s!"unknown {n}"

def ctrlY : Incoming String := .terminal (.key (.char 'y') { ctrl := true })

def tests : TestM Unit := do
  let (early, _) ← runWith [.terminal (.key (.char 'd')), ctrlY]
  check "a confirmation ignores keys at first" !early.confirmed
  let (late, out) ← runWith ([.terminal (.key (.char 'd'))] ++ List.replicate 5 .tick ++ [ctrlY])
  check "and takes Ctrl+Y once the delay has passed" late.confirmed
  let (plainY, _) ← runWith ([.terminal (.key (.char 'd'))] ++ List.replicate 5 .tick ++
    [.terminal (.key (.char 'y')), .terminal (.key .enter)])
  check "y and Enter do not confirm" !plainY.confirmed
  let (net, _) ← runWith [.terminal (.key (.char 'd')), .custom "confirm"]
  check "an event from elsewhere does not either" (!net.confirmed && net.fromNetwork == 1)
  checkEq "the title is written first" true (out[0]!.endsWith "\x1b]0;asking\x07")
  checkEq "and again only when it changes" 1
    ((out.toList.drop 1).filter (·.endsWith "\x1b]0;done\x07")).length
  let (p, _) ← runWith [.terminal (.paste "rm -rf\x1b[201~ ~")]
  checkEq "a paste arrives without its markers" "rm -rf ~" p.pasted
  check "a link with a scheme opens" (Url.parse? "https://example.org/a?b=c").isSome
  check "one without does not" (Url.parse? "javascript:alert(1)").isNone
  check "nor one with a space" (Url.parse? "https://example.org/ --help").isNone
  check "nor an option" (Url.parse? "--help").isNone
  checkEq "a typed command" "command join #room" (shown (Typed.classify ["join", "leave"] "/join #room"))
  checkEq "an unknown command is an error, not a message" "unknown jion"
    (shown (Typed.classify ["join", "leave"] "/jion #room"))
  checkEq "anything else is a message" "message hi /join" (shown (Typed.classify ["join"] "hi /join"))

end Tessera.Tests.Consent
