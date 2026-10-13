# Tessera

Terminal user interfaces in Lean 4. Its widgets and box layout are inspired by Haskell's
[Brick](https://github.com/jtdaugherty/brick); applications follow the Elm architecture, a state
with a function that draws it and a function that updates it for each message. Terminal input and
control come from [crossterm-lean-ffi](https://github.com/katzenpost/crossterm-lean-ffi).

```lean
import Tessera
open Tessera Widget

def draw (n : Nat) : Widget :=
  center (borderWithLabel " Counter " (padAll 1 (str s!"{n}   + adds one, Esc quits")))

def update : Msg Unit → Nat → IO (Nat × Bool)
  | .input (.key (.char '+') _), n => pure (n + 1, false)
  | .input (.key .esc _), n => pure (n, true)
  | _, n => pure (n, false)

def main : IO Unit := discard <| App.run { draw, update } 0
```

- **Widgets** draw themselves into the space they are given: `str`, `txt` (wrapped), `fill`,
  `hBox`, `vBox`, `border`, `borderWithLabel`, `pad`, `hLimit`, `vLimit`, `center`, `viewport`
  and `withStyle`. A widget is fixed or greedy on each axis; a box gives its fixed children their
  room first and shares the rest among the greedy ones.
- **Styles** set colors (16, 256 or RGB) and bold, dim, italic, underline and reverse.
- **Drawing** keeps the last frame and writes only the cells that changed.
- **Applications** get input events, optional timer ticks, and events of their own, sent from
  any task through the function `App.run` passes to `start`.

Building needs `cargo` on the `PATH`, for crossterm.

## Try it

    lake exe tessera-demo

## Tests

    lake exe tessera-test

## License

AGPL-3.0-only
