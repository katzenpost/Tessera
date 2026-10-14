# Tessera

Terminal user interfaces in Lean 4. Its widgets and box layout are inspired by Haskell's
[Brick](https://github.com/jtdaugherty/brick); applications follow the Elm architecture, a state
with a function that draws it and a function that updates it for each message. Terminal input and
control come from [crossterm-lean-ffi](https://github.com/katzenpost/crossterm-lean-ffi).

```lean
import Tessera
open Tessera Widget

def draw (n : Nat) : Widget .standard .remote :=
  center (borderWithLabel t!" Counter " (padAll 1 (str (.ofNat n ++ t!"   + adds one, Esc quits"))))

def update : Msg Unit → Nat → IO (Nat × Bool)
  | .input (.key (.char '+') _), n => pure (n + 1, false)
  | .input (.key .esc _), n => pure (n, true)
  | _, n => pure (n, false)

def main : IO Unit := discard <| App.run { draw, update } 0
```

- **Widgets** draw themselves into the space they are given, and their results carry the proof
  that they fit: `str`, `strs`, `txt` (wrapped), `fill`, `hBox`, `vBox`, `border`,
  `borderWithLabel`, `pad`, `hLimit`, `vLimit`, `center`, `viewport` and `withStyle`. A widget is
  fixed or greedy on each axis; a box gives its fixed children their room first and shares the
  rest among the greedy ones.
- **Styles** set colors (16, 256 or RGB) and bold, dim, italic, underline and reverse.
- **Drawing** keeps the last frame and writes only the cells that changed. A cell holds a glyph,
  a character the charset allows, so nothing a terminal would act on can reach one.
- **Text** that widgets draw is a `Text`, which cannot hold a control character, a bidi control
  or an invisible character, and so cannot hold an escape sequence. Text the program wrote comes
  from `t!"…"` literals, checked when the program compiles. Text from elsewhere (a chat message,
  a file name, a name someone chose) goes through `Untrusted.line` or `Untrusted.lines`, which keep
  characters by an allowlist of those the terminal and Tessera agree on the width of, and show
  anything else as a visible stand-in (`␛` for ESC, `␦` for the rest) so that an attempt to steer
  the terminal shows. `Untrusted.Ident` is a name that cannot fake a badge, and its `skeleton` and
  `mixedScript` tell names that look alike. `Untrusted.pasted` removes bracketed paste's markers
  from a paste, and `withoutControls` takes controls and bidi controls out of text passed on.
  [docs/TUI_SECURITY_GUIDELINES.md](docs/TUI_SECURITY_GUIDELINES.md) says what else a TUI showing
  such text should do, and [docs/DESIGN.md](docs/DESIGN.md) how Tessera is built to do it.
- **Applications** get input events, optional timer ticks, and events of their own, sent from
  any task through the function `App.run` passes to `start`.

Building needs `cargo` on the `PATH`, for crossterm.

## Try it

    lake exe tessera-demo

## Tests

    lake exe tessera-test

## License

AGPL-3.0-only
