/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

/-! # Pictures

A picture is drawn by a terminal that shows them, with sixel or the kitty graphics protocol, from
pixels Tessera holds and encodes itself. No byte of a picture's encoding comes from elsewhere as
it is: the body of each control string is built by Tessera from numbers, and holds nothing but
printable ASCII (`Plain`), so it cannot end the string early or hold an escape sequence.

A picture from elsewhere is read by Tessera, in Lean, from binary PPM, up to a size, and only its
pixels are kept. Whether the terminal shows pictures is configured, never asked of it: Tessera
asks a terminal nothing. -/

namespace Tessera

/-- A character a picture's encoding may hold: printable ASCII, not a space. -/
def Plain (c : Char) : Prop := 0x21 ≤ c.toNat ∧ c.toNat ≤ 0x7E

instance : DecidablePred Plain := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Characters of a picture's encoding. Built by keeping only those that are `Plain`, which the
encoders below make all of them, as the tests check. -/
def plain (l : List Char) : {l : List Char // ∀ c ∈ l, Plain c} :=
  ⟨l.filter (decide <| Plain ·), by simp⟩

structure Rgb where
  r : UInt8
  g : UInt8
  b : UInt8
  deriving DecidableEq, Repr, Inhabited

/-- A picture `w` pixels wide and `h` high, row by row. -/
structure Pixels where
  w : Nat
  h : Nat
  data : Array Rgb
  size_eq : data.size = w * h

instance : BEq Pixels := ⟨fun a b => a.w == b.w && a.h == b.h && a.data == b.data⟩

namespace Pixels

def get (p : Pixels) (x y : Nat) : Rgb := p.data[y * p.w + x]?.getD default

def ofFn (w h : Nat) (f : Nat → Nat → Rgb) : Pixels :=
  ⟨w, h, Array.ofFn fun (i : Fin (w * h)) => f (i.val % w) (i.val / w), by simp⟩

/-- The most pixels a picture from elsewhere may have. -/
def maxPixels : Nat := 1 <<< 20

/-- A picture from binary PPM (`P6`, values up to 255), if `bytes` hold one of at most `limit`
pixels. Comments are not read. -/
def ofPPM? (bytes : ByteArray) (limit : Nat := maxPixels) : Option Pixels := do
  let isSpace (b : UInt8) := b == 0x20 || b == 0x0A || b == 0x0D || b == 0x09
  -- The header: "P6", then width, height and the largest value, each after white space.
  let rec field (i : Nat) (fuel : Nat) : Option (Nat × Nat) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      if h : i < bytes.size then
        if isSpace bytes[i] then field (i + 1) fuel
        else
          let rec digits (j n : Nat) (fuel : Nat) : Option (Nat × Nat) :=
            match fuel with
            | 0 => none
            | fuel + 1 =>
              if h : j < bytes.size then
                let b := bytes[j]
                if 0x30 ≤ b && b ≤ 0x39 then
                  if n > 100000 then none else digits (j + 1) (n * 10 + (b - 0x30).toNat) fuel
                else if j == i then none else some (n, j)
              else none
          digits i 0 8
      else none
  guard (bytes.size ≥ 2 && bytes[0]! == 0x50 && bytes[1]! == 0x36)
  let (w, i) ← field 2 64
  let (h, i) ← field i 64
  let (maxv, i) ← field i 64
  guard (maxv == 255 && w * h ≤ limit && w > 0 && h > 0)
  let start := i + 1
  guard (start + 3 * w * h ≤ bytes.size)
  let data := Array.ofFn fun (k : Fin (w * h)) =>
    let o := start + 3 * k.val
    ({ r := bytes[o]!, g := bytes[o + 1]!, b := bytes[o + 2]! } : Rgb)
  return ⟨w, h, data, by simp [data]⟩

end Pixels

/-- How a terminal shows pictures. -/
inductive Graphics where
  | sixel
  | kitty
  deriving DecidableEq, Repr, Inhabited

namespace Sixel

/-- The nearest of six levels of `v`. -/
def level (v : UInt8) : Nat := (v.toNat * 5 + 127) / 255

/-- The colour register for `c`: one of 216, a 6×6×6 cube. -/
def register (c : Rgb) : Nat := 36 * level c.r + 6 * level c.g + level c.b

/-- The sixel body of `p`, after the `q` that begins it: its size, the colours it uses, and each
band of six rows, a pass for each colour in it. -/
def body (p : Pixels) : List Char := Id.run do
  let mut out : String := s!"\"1;1;{p.w};{p.h}"
  let used := (p.data.toList.map register).eraseDups
  for c in used do
    let pct (k : Nat) := k * 20
    out := out ++ s!"#{c};2;{pct (c / 36)};{pct (c / 6 % 6)};{pct (c % 6)}"
  for band in List.range ((p.h + 5) / 6) do
    let colours := ((List.range p.w).flatMap fun x => (List.range 6).filterMap fun i =>
      let y := 6 * band + i
      if y < p.h then some (register (p.get x y)) else none).eraseDups
    for c in colours do
      out := out ++ s!"#{c}"
      for x in List.range p.w do
        let bits := (List.range 6).foldl (init := 0) fun n i =>
          let y := 6 * band + i
          if y < p.h && register (p.get x y) == c then n + (1 <<< i) else n
        out := out.push (Char.ofNat (63 + bits))
      out := out.push '$'
    out := out.push '-'
  return out.toList

end Sixel

namespace Kitty

def alphabet : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

def base64 (bytes : List UInt8) : List Char :=
  let rec go : List UInt8 → List Char
    | a :: b :: c :: r =>
      let n := a.toNat <<< 16 ||| b.toNat <<< 8 ||| c.toNat
      alphabet[n >>> 18]! :: alphabet[n >>> 12 &&& 63]! :: alphabet[n >>> 6 &&& 63]! ::
        alphabet[n &&& 63]! :: go r
    | [a, b] =>
      let n := a.toNat <<< 16 ||| b.toNat <<< 8
      [alphabet[n >>> 18]!, alphabet[n >>> 12 &&& 63]!, alphabet[n >>> 6 &&& 63]!, '=']
    | [a] => let n := a.toNat <<< 16; [alphabet[n >>> 18]!, alphabet[n >>> 12 &&& 63]!, '=', '=']
    | [] => []
  go bytes

/-- The bodies of the kitty graphics commands that show `p`, after the `G` that begins each: its
pixels as 24-bit RGB, in base64, in pieces of at most 4096 characters. -/
def bodies (p : Pixels) : List (List Char) :=
  let data := base64 (p.data.toList.flatMap fun c => [c.r, c.g, c.b])
  let rec chunks (l : List Char) (fuel : Nat) : List (List Char) :=
    match fuel with
    | 0 => []
    | fuel + 1 => if l.length ≤ 4096 then [l] else l.take 4096 :: chunks (l.drop 4096) fuel
  let cs := chunks data (data.length / 4096 + 1)
  cs.zipIdx.map fun (c, i) =>
    let more := if i + 1 < cs.length then "1" else "0"
    let keys := if i == 0 then s!"a=T,f=24,s={p.w},v={p.h},m={more};" else s!"m={more};"
    keys.toList ++ c

end Kitty

end Tessera
