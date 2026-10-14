# Tessera design

Tessera is a library for terminal user interfaces in Lean 4.
- Applications follow the Elm architecture: a state, a function that draws it, and a function that updates it for each message.
- Widgets and box layout follow Haskell's [Brick](https://github.com/jtdaugherty/brick).
- Terminal input and control come from [crossterm-lean-ffi](https://github.com/katzenpost/crossterm-lean-ffi).

Tessera's security properties are types that the compiler checks:
- text from elsewhere cannot steer the terminal;
- a widget stays within the space it is given;
- remote parties cannot take over the parts of the screen that tell the user who said what;
- remote events cannot act for the user.

[TUI_SECURITY_GUIDELINES.md](TUI_SECURITY_GUIDELINES.md) gives the rules. This document describes how Tessera is built to enforce them.

## From event to screen

Each frame passes through the same stages:

1. An **event** arrives: a key, a paste or a resize from the terminal, a timer tick, or an event of the application's own, such as a message from the network.
2. The application's **update** function returns the new state.
3. Its **draw** function returns a **widget** tree for that state.
4. The tree is **rendered** into a **buffer** the size of the screen: a grid of cells.
5. The buffer is **diffed** against the previous frame, giving a list of terminal **operations**: move the cursor, set the style, print a character.
6. The operations are **encoded** as bytes and written to the terminal in one write.

The stages share one set of types. A character that may reach the terminal is a `Glyph`, and text that may reach it is a `Text`. Neither type has a value the terminal would act on. Each stage accepts only these types from the stage before it, so no stage needs to filter what the previous one produced.

## Characters

A `Charset` decides which characters may be drawn and how wide each one is. It is a structure holding those decisions together with the laws they must satisfy:

```lean
structure Charset where
  Printable : Char → Prop
  [decPrintable : DecidablePred Printable]
  width : Char → Nat
  printable_width   : ∀ c, Printable c → width c = 1 ∨ width c = 2
  printable_not_c0  : ∀ c, Printable c → 0x20 ≤ c.toNat
  printable_not_del : ∀ c, Printable c → c.toNat ≠ 0x7F
  printable_not_c1  : ∀ c, Printable c → ¬ (0x80 ≤ c.toNat ∧ c.toNat < 0xA0)
  printable_not_bidi      : ∀ c, Printable c → ¬ Bidi c
  printable_not_invisible : ∀ c, Printable c → ¬ Invisible c
  printable_not_combining : ∀ c, Printable c → ¬ Combining c
```

`Printable` is an allowlist. A character is in it only when it is not a control or format character and Tessera and terminals agree on its width. `Charset.standard` holds:
- the scripts and symbols terminals draw one cell wide;
- the East Asian wide and fullwidth characters, and emoji drawn as pictures, which take two cells;
- East Asian ambiguous-width characters, as one cell.

`Charset.cjk` takes the ambiguous-width characters as two cells, as terminals in CJK locales draw them.

Both charsets allow the same characters and differ only in width, so both are built by `Charset.ofPrintable`, which proves the laws once. The characters are defined by tables of code point ranges. Each law is proved by checking it on every range in the table, a finite check, and lifting the result to all characters.

### The terminal assumption

Tessera cannot prove anything about a terminal it does not control. The one thing it assumes is stated as a structure:

```lean
structure Emulator (cs : Charset) where
  width : Char → Nat
  agrees : ∀ c, cs.Printable c → width c = cs.width c
```

Theorems about where text ends and where the cursor stands take an `Emulator` as an argument. Theorems about control characters do not take one: they hold for any terminal.

## Text

```lean
inductive Origin | app | remote

structure Text (cs : Charset) (o : Origin) where
  private mk ::
  text    : String
  charsOk : ∀ c ∈ text.toList, cs.Printable c ∨ Combining c
  seqOk   : WellFormedSeq text
```

A `Text` is one line that may be drawn. Its proof fields hold at two levels:
- **`charsOk`** checks each character. It rules out C0, DEL and C1 controls, newlines, bidi controls and invisible characters, which rules out every escape sequence. Concatenation preserves it.
- **`seqOk`** checks rules about neighbouring characters:
  - each base character carries at most a fixed number of combining marks;
  - no mark appears without a base;
  - a zero-width joiner appears only between emoji.

  `Text.append` re-establishes these rules where two texts meet, since marks at the start of the right-hand text attach to the last character of the left-hand one.

The constructor is private, and a `Text` comes from one of four places:
- **`Untrusted.line`** filters a string from elsewhere. It keeps the characters the charset allows and replaces every other one with a visible stand-in: a control character becomes its Control Picture (`␛` for ESC), DEL becomes `␡`, and anything else refused becomes `␦`. Its result has origin `.remote`.
- **`Untrusted.lines`** splits a text into such lines, expanding tabs and capping the number of lines.
- **`t!"…"`** makes a `Text cs .app` from a string literal. The proof is checked when the program compiles, so a literal containing a control character does not compile.
- **Operations that preserve the proofs**, such as `++` and the conversion from numbers.

### Names

An `Ident` is a `Text` for names: nicknames, room names, file names. It adds proof fields saying it holds:
- no bidi controls;
- no invisible characters;
- none of the glyphs a name could use to fake a badge: locks, check marks, shields, and Private Use Area icons.

`skeleton` maps a name to what it looks like, ignoring case, accents, separators and letters of other scripts that pass for Latin ones. `mixedScript` tells whether a name mixes Latin with Greek or Cyrillic letters.

### Text passed on

Two functions produce strings rather than `Text`, for text that leaves Tessera instead of reaching the screen:
- `Untrusted.pasted` returns a `Pasted`: a paste with a proof that it contains neither of bracketed paste's markers.
- `withoutControls` returns a string with a proof that it contains no controls other than newline and tab, and no bidi controls. It is meant for a message about to be sent.

## Cells and buffers

```lean
structure Glyph (cs : Charset) where
  char : Char
  printable : cs.Printable char

inductive Cell (cs : Charset)
  | glyph (g : Glyph cs) (style : Style)
  | wideRight (style : Style)
  | blank (style : Style)

structure Row (cs : Charset) (w : Nat) where
  cells : List (Cell cs)
  length_eq : cells.length = w
  wf : Cell.wellFormed cells = true

structure Buffer (cs : Charset) (w h : Nat) where
  rows : Vector (Row cs w) h
```

A cell holds a glyph, the right half of a two-cell glyph, or nothing. A space is always a blank, so that two buffers that look the same are equal.

The buffer's size is part of its type, so every frame of one size has one type. Each row carries two proofs:
- it has exactly `w` cells;
- it is well formed: every two-cell glyph is followed by its right half, and a right half follows nothing else.

Every write goes through `Row.splice`, which writes a well-formed run of cells from a column, clipped at the right edge. It keeps the cells before the run with `Cell.cut`, and the cells after it with `Cell.skip`. Each of these turns a two-cell glyph it splits in half into a blank. `wellFormed_cut`, `wellFormed_skip` and `wellFormed_append` show that the result is well formed again, and the lengths add up to `w`.

The writing functions are built on `splice`:
- `putString` writes glyphs from a column and returns the column after them, a number no greater than `w`.
- `blit` copies each row of one buffer onto another, clipped at the edges.
- `crop` takes part of a buffer with `Row.slice`, blanking a two-cell glyph cut by either edge.

## Widgets and layout

```lean
structure Image (cs : Charset) (maxW maxH : Nat) where
  w : Nat
  h : Nat
  w_le : w ≤ maxW
  h_le : h ≤ maxH
  buf : Buffer cs w h

structure Widget (cs : Charset) (o : Origin) where
  hPolicy : Policy := .fixed
  vPolicy : Policy := .fixed
  render : (ctx : Context) → Image cs ctx.width ctx.height
```

A widget draws itself into the space it is given, and its result type says it fits in that space.

On each axis a widget is either **fixed**, taking only the room it needs, or **greedy**, taking all the room it is given. A box gives its fixed children their room first and shares what is left among the greedy ones. This way `hBox [str label, txt body]` keeps the label whole and wraps the body in the rest of the line.

The widgets are:
- **text:** `str` draws one row and `txt` wraps. Both take a `Text`, never a `String`;
- **space:** `fill`;
- **layout:** `hBox` and `vBox`;
- **frames:** `border` and `borderWithLabel`;
- **size:** `pad`, `hLimit` and `vLimit`;
- **position:** `center` and `viewport`;
- **style:** `withStyle`.

Each widget proves that its image fits from the proofs its children's images carry, so the bound for a whole tree follows from the bound for each node. `Widget.draw w width height` returns a `Buffer cs width height`: a frame exactly the size of the screen.

A widget's origin says what text it may contain. `Widget cs .app` holds only text the program wrote, and `Widget cs .remote` may hold text from elsewhere. Every app widget can be used as a remote one (`Widget.lift`). The reverse is possible only through the functions in the next section.

## The trusted path

Some parts of the screen tell the user who said something, where they are, and whether it is safe: the sender column, the status bar, the room header and the input prompt. The program draws them, and their types say so:

```lean
structure Frame (cs : Charset) where
  header       : Widget cs .app
  statusBar    : Widget cs .app
  prompt       : Widget cs .app
  senderColumn : Widget cs .app
  body         : Widget cs .remote
```

Remote text reaches a reserved region in two ways:
- **`Widget.delimited budget t`** truncates `t` to `budget` cells, puts visible delimiters around it, and proves the result is at most `budget + 2` cells wide. A room topic in the header is shown this way.
- **`SenderLabel.widget`** draws a sender. A `SenderLabel` is one of the following:
  - **verified:** a petname the user chose, bound to a key;
  - **unverified:** an `Ident`, drawn as `~nick`.

A message body of several lines is drawn by `Frame.message`. It puts the sender's label on the first row and a continuation gutter on the rest, so a line in a body cannot pass for another message.

A `Roster` holds the labels of a room's members with a proof that no two of them share a skeleton. `Roster.build` appends a short key fingerprint to each name that collides with another.

### Reserved styles

Senders may style their text only with a `RemoteStyle`: one of eight foreground colours, bold, italic and underline. A remote style cannot set reverse video or a background. A `Theme` maps remote styles to styles, lists the styles the program reserves for itself, and proves the two never meet:

```lean
structure Theme where
  reserved : List Style
  ofRemote : RemoteStyle → Style
  disjoint : ∀ r, ofRemote r ∉ reserved
```

`withStyle` on a `Widget cs .remote` takes a `RemoteStyle`. `withStyle` on a `Widget cs .app` takes any `Style`.

## Drawing

```lean
inductive Op (cs : Charset)
  | moveTo (x y : Nat)
  | sgr (s : Style)
  | clear
  | reset
  | print (g : Glyph cs)
  | setTitle (t : Text cs .app)
  | copy (t : Text cs .app) (d : Designation t)
```

Everything Tessera writes to the terminal is an `Op`, and `Op.encode` gives its bytes:
- Text reaches the terminal only through `print`, which takes a glyph.
- The only operations that place text inside an escape sequence are `setTitle` and `copy`, and both take text the program wrote.
- No operation asks the terminal a question, so none can make the terminal type a reply into the program.

`diff old new` returns the operations that turn a terminal showing `old` into one showing `new`. Both frames are buffers of the same type, so they have the same size. A two-cell glyph is written again when either of its halves changed. It writes only the cells that changed, moves the cursor once per run of them, and sets the style only when it differs from the last cell written. When the screen changes size, `redraw new` clears it and draws the whole frame.

### The VT model

`VT.tokens` splits a stream of characters into what a terminal makes of it, following ECMA-48:
- printed characters;
- CSI, OSC, DCS and other escape sequences;
- C0 and C1 controls.

`VT.apply` runs the printing and cursor tokens on a model screen. Three theorems state Tessera's guarantees against this model:
- **`text_tokens_print`:** the characters of any `Text` split into printed characters only. It assumes nothing about the terminal.
- **`output_only_own`:** encoding a list of operations and splitting the result gives back exactly those operations, each as a printed character or one of Tessera's own sequences.
- **`diff_correct`:** for any `em : Emulator cs`, applying `diff old new` to a screen showing `old` leaves it showing `new`. The cursor ends every run where Tessera computed, so text cannot drift into the cell beside it.

## Applications

```lean
structure App (cs : Charset) (σ ε : Type) where
  draw : σ → Widget cs .remote
  update : Msg ε → σ → IO (σ × Bool)
  tickMs : Option UInt32 := none
```

`App.run` sets up the terminal, runs the application, and restores the terminal afterwards. It does the following:
- Enters raw mode and the alternate screen, hides the cursor, and enables bracketed paste.
- Reads terminal events on one task and timer ticks on another.
- Gives `start` a function that sends the application events of its own from any task.
- Draws the first frame, then updates and draws again for each message.
- In a `finally`, restores the terminal state, so a crash or an exception still leaves a usable shell, and filters any error text through `Untrusted.line` before printing it.

### Consent

```lean
inductive Msg (ε : Type)
  | input (e : Event) (u : UserInput)
  | tick
  | custom (e : ε)
```

`UserInput` has a private constructor, called only by `App.run` for events read from the terminal. Events from the network arrive as `custom` and carry no `UserInput`.

An action that grants authority takes a `Designation` of the object it acts on, and a `Designation` can be made only from a `UserInput`. This covers:
- `openLink`: opening a link;
- `saveFile`: saving a file;
- `trustKey`: trusting a key;
- `copy`: copying to the clipboard.

A `Url` carries a proof that its scheme is `https` or `http`, and `openLink` runs the opener with an argv array and `--` before the URL.

A `Modal` opens only with a `UserInput`, so a remote event cannot take the keyboard's focus. A `Confirmation` states its consequence as `Text cs .app` and records when it was shown. Confirming it takes a proof that the delay has passed, obtained with `if h : now - shownAt ≥ delay then …`.

A paste arrives as a `Pasted`. Commands are parsed only from typed input, so a pasted `/command` is message text, and an unknown command is an error rather than a message sent.

## Proofs

- No proof uses `sorry`, `native_decide`, or an axiom beyond Lean's standard `propext`, `Quot.sound` and `Classical.choice`. `Tests/Axioms.lean` prints the axioms of each main theorem.
- `Tests/Rejects.lean` holds programs that must not compile:
  - a `String` passed to `Widget.str`;
  - a control character in a `t!` literal;
  - remote text in a `Frame`'s status bar;
  - `openLink` without a `Designation`.
- The randomized and corpus tests in `Tests/` drive the compiled code, including the FFI, with hostile input. The theorems cover Tessera's model of the terminal; the tests cover the code as it runs.
