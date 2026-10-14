/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.App
import Tessera.Tests.Util

/-! # Pictures: encoding, reading PPM, and drawing them from the application loop -/

namespace Tessera.Tests.Images

open Tessera

def solid (w h : Nat) (c : Rgb) : Pixels := .ofFn w h fun _ _ => c

def random (w h : Nat) (r : Rng) : Pixels × Rng := Id.run do
  let mut r := r
  let mut data := #[]
  for _ in [0:w * h] do
    let (a, r1) := r.next 256
    let (b, r2) := r1.next 256
    let (c, r3) := r2.next 256
    r := r3
    data := data.push { r := a.toUInt8, g := b.toUInt8, b := c.toUInt8 }
  return (.ofFn w h fun x y => data[y * w + x]!, r)

def ppm (header : String) (body : List UInt8) : ByteArray := header.toUTF8 ++ ⟨body.toArray⟩

def pictureApp : App CS Nat Unit where
  draw n := Widget.str (Text.ofNat n)
  update
    | .key (.char '+') _ _, n => pure (n + 1, false)
    | .key (.char 'q') _ _, n => pure (n, true)
    | _, n => pure (n, false)
  graphics := some .sixel
  pictures n := [{ x := 0, y := 1, pixels := solid 1 1 { r := 255, g := 0, b := 0 } }] ++
    if n ≥ 2 then [{ x := 2, y := 1, pixels := solid 1 1 { r := 0, g := 0, b := 255 } }] else []

def tests : TestM Unit := do
  let red : Rgb := { r := 255, g := 0, b := 0 }
  checkEq "sixel of one red pixel" "\x1bPq\"1;1;1;1#180;2;100;0;0#180@$-\x1b\\"
    (Ansi.encode (cs := CS) [.image .sixel (solid 1 1 red)])
  checkEq "sixel bands of six rows" 2 (((Sixel.body (solid 1 7 red)).filter (· == '-')).length)
  checkEq "base64" ["TWFu", "TWE=", "TQ==", ""]
    (["Man", "Ma", "M", ""].map fun s => String.ofList (Kitty.base64 s.toUTF8.toList))
  checkEq "kitty of one pixel" "\x1b_Ga=T,f=24,s=1,v=1,m=0;/wAA\x1b\\"
    (Ansi.encode (cs := CS) [.image .kitty (solid 1 1 red)])
  let big := Kitty.bodies (solid 40 40 red)
  checkEq "kitty in pieces" 2 big.length
  check "the first piece says what follows" ((String.ofList big[0]!).startsWith "a=T,f=24,s=40,v=40,m=1;")
  check "the last says it is the last" ((String.ofList big[1]!).startsWith "m=0;")
  let mut rng : Rng := ⟨5⟩
  let mut whole := true
  for _ in [0:50] do
    let (w, r1) := rng.next 13
    let (h, r2) := r1.next 13
    let (p, r3) := random (w + 1) (h + 1) r2
    rng := r3
    let body := Sixel.body p
    if (plain body).1.length != body.length then whole := false
    for b in Kitty.bodies p do
      if (plain b).1.length != b.length then whole := false
  check "the encoders write nothing but plain characters" whole
  let tokens := VT.tokens (Ansi.encode (cs := CS) [.image .sixel (solid 3 8 red), .image .kitty (solid 50 50 red)]).toList
  checkEq "a terminal reads each picture as control strings" 1 ((tokens.filter fun | .str 'P' _ => true | _ => false).length)
  checkEq "and kitty's pieces as one each" 3 ((tokens.filter fun | .str '_' _ => true | _ => false).length)
  check "nothing else" (tokens.all fun | .str _ _ => true | _ => false)
  let px := (Pixels.ofPPM? (ppm "P6\n2 1\n255\n" [1, 2, 3, 4, 5, 6])).map fun p =>
    let c := p.get 1 0; (p.w, p.h, c.r, c.g, c.b)
  checkEq "PPM" (some (2, 1, 4, 5, 6)) px
  check "PPM too large" (Pixels.ofPPM? (ppm "P6 2 2 255\n" (List.replicate 12 0)) (limit := 3)).isNone
  check "PPM cut short" (Pixels.ofPPM? (ppm "P6 2 2 255\n" (List.replicate 11 0))).isNone
  check "PPM of 16 bits" (Pixels.ofPPM? (ppm "P6 1 1 65535\n" (List.replicate 6 0))).isNone
  check "text PPM" (Pixels.ofPPM? (ppm "P3 1 1 255\n0 0 0\n" [])).isNone
  check "PPM of no pixels" (Pixels.ofPPM? (ppm "P6 0 0 255\n" [])).isNone
  let queue ← IO.mkRef ((keys "x+x+q").map Incoming.terminal)
  let writes ← IO.mkRef (#[] : Array String)
  let screen : Screen := { size := pure (6, 2), write := fun s => writes.modify (·.push s) }
  discard <| pictureApp.loop screen (queue.modifyGet fun | [] => (none, []) | m :: r => (some m, r)) 0
  let counts := (← writes.get).toList.map fun s => (s.splitOn "\x1bPq").length - 1
  checkEq "pictures are drawn with the first frame, and again when the frame changes" [1, 0, 1, 0, 2] counts
where
  keys (s : String) : List Event := s.toList.map fun c => .key (.char c)

end Tessera.Tests.Images
