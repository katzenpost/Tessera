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
  ascii_printable : ∀ n ≤ 0x5E, Printable (Char.ofNat (0x20 + n))
  controlPicture_printable : ∀ n ≤ 0x26, Printable (Char.ofNat (0x2400 + n))
```

`Printable` is an allowlist. A character is in it only when it is not a control or format character and Tessera and terminals agree on its width. `Charset.standard` holds:
- the scripts and symbols terminals draw one cell wide;
- the East Asian wide and fullwidth characters, and emoji drawn as pictures, which take two cells;
- East Asian ambiguous-width characters, as one cell.

`Charset.cjk` takes the ambiguous-width characters as two cells, as terminals in CJK locales draw them.

The last two laws say that every charset allows printable ASCII and the Control Pictures, U+2400 to U+2426. Code written for any charset can then show plain text, and a stand-in for any character it refuses.

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
  seqOk   : marksOk none text.toList = true
```

A `Text` is one line that may be drawn. Its proof fields hold at two levels:
- **`charsOk`** checks each character. It rules out C0, DEL and C1 controls, newlines, bidi controls and invisible characters, including the zero-width joiner, which rules out every escape sequence.
- **`seqOk`** checks the combining accents: each follows a character, at most `maxMarks` in a row. A text therefore never begins with an accent, so `++` cannot attach one text's accents to the end of another. `marksOk_append` shows that the concatenation of two texts satisfies `seqOk` with no repair at the join.

The constructor is private, and a `Text` comes from one of these:
- **`Untrusted.line`** filters a string from elsewhere. It keeps the characters the charset allows and replaces every other one with a visible stand-in: a control character becomes its Control Picture (`␛` for ESC), DEL becomes `␡`, and anything else refused becomes `␦`. An accent with no character before it becomes `␦`. One accent too many on a character becomes `␦`, and the rest are dropped. The result has origin `.remote`. Three theorems hold of it: `filterChars_charsOk` and `filterChars_marksOk` give its proof fields, and `line_sub` says that each of its characters is one of the input or a stand-in.
- **`Untrusted.lines`** splits a text into such lines, expanding tabs. It returns at most `max 1 maxLines` of them, the last saying how many more there were.
- **`t!"…"`** makes a `Text cs .app` from a string literal, with a proof checked by `decide` when the program compiles. For a charset known then, every character must be one it allows. For a charset that is only a parameter, every character must be printable ASCII. A literal containing a control character does not compile.
- **`Text.ofNat`** gives the digits of a number, and **`++`** joins two texts of one origin.

Text the program wrote may stand where text from elsewhere may: `Text.lift` takes a `Text cs .app` to a `Text cs .remote`, and is a coercion.

### Names

An `Ident` is a `Text` for names: nicknames, room names, file names. A `Text` already holds no bidi control and no invisible character, nor anything from the Private Use Area, where icon fonts put their badges. `Ident` adds a proof that the name holds none of the other glyphs a name could use to fake a badge: locks, keys, check marks, shields and warning signs. `Ident.ofRemote` shows each of these as `␦` and filters the rest as `line` does.

`skeleton` maps a name to what it looks like, ignoring case, accents, separators and letters of other scripts that pass for Latin ones. `mixedScript` tells whether a name mixes Latin with Greek or Cyrillic letters.

### Text passed on

Two functions produce strings rather than `Text`, for text that leaves Tessera instead of reaching the screen:
- `Untrusted.pasted` returns a `Pasted`: a paste with a proof that it contains neither of bracketed paste's markers. It removes the markers and then every ESC, so a marker hidden inside another, which reappears when the outer one is removed, goes too.
- `withoutControls` returns a string with a proof that it contains no controls other than newline and tab, and no bidi controls. It is meant for a message about to be sent.

## Cells and buffers

```lean
structure Glyph (cs : Charset) where
  char : Char
  printable : cs.Printable char

inductive Cell (cs : Charset)
  | glyph (g : Glyph cs) (style : Style)
  | wideRight
  | blank (style : Style)

structure Row (cs : Charset) (w : Nat) where
  cells : List (Cell cs)
  length_eq : cells.length = w
  wf : Cell.wellFormed cells = true

structure Buffer (cs : Charset) (w h : Nat) where
  rows : Vector (Row cs w) h
```

A cell holds a glyph, the right half of a two-cell glyph, or nothing. The right half is drawn in its glyph's style and has none of its own, and a space is always a blank, so that two rows that look the same on a terminal are equal.

The buffer's size is part of its type, so every frame of one size has one type. Each row carries two proofs:
- it has exactly `w` cells;
- it is well formed: every two-cell glyph is followed by its right half, a right half follows nothing else, and no glyph is a space.

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
- **text:** `str` draws one line, `strs` one line per row, and `txt` wraps. Each takes `Text`, never a `String`;
- **space:** `fill`;
- **layout:** `hBox` and `vBox`;
- **frames:** `border` and `borderWithLabel`;
- **size:** `pad`, `hLimit` and `vLimit`;
- **position:** `center` and `viewport`;
- **style:** `withStyle`.

Each widget proves that its image fits from the proofs its children's images carry, so the bound for a whole tree follows from the bound for each node. `Widget.draw w width height` returns a `Buffer cs width height`: a frame exactly the size of the screen.

A widget's origin says what text it may contain. `Widget cs .app` holds only text the program wrote, and `Widget cs .remote` may hold text from elsewhere. The class `Shows t w` says that text of origin `t` may be drawn in a widget of origin `w`: the program's text in any widget, text from elsewhere only in a remote one. Every app widget can be used as a remote one (`Widget.lift`, a coercion). The reverse is possible only through `Widget.delimited`.

`Widget`'s constructor is private. A widget the program draws itself, with its own `render`, is made with `Widget.custom`, and is of origin `.remote`. A remote text drawn into an image by a widget of its own therefore cannot come back as a widget of origin `.app`.

## The trusted path

Some parts of the screen tell the user who said something, where they are, and whether it is safe: the room header, the status bar, the input prompt, and the column that names each message's sender. The program draws them, and their types say so:

```lean
structure Frame (cs : Charset) where
  header    : Widget cs .app
  body      : Widget cs .remote
  statusBar : Widget cs .app
  prompt    : Widget cs .app
```

`Frame.widget` lays a frame out with the header on the first row, the status bar and the prompt on the last two, and the body between them, however short it is.

Remote text reaches a widget of origin `.app` in exactly one way. **`Widget.delimited openD closeD budget t`** cuts `t` to `budget` cells and draws it between the program's delimiters, and it is never wider than the delimiters and `budget`. A room topic in the header is shown this way, as is a name a sender chose.

**`SenderLabel`** says who sent something:
- **verified:** a petname the user gave a contact, drawn in the theme's style for verified contacts;
- **unverified:** an `Ident`, drawn through `delimited` as `~nick`.

**`message θ labelWidth sender body`** draws a message. A sender column `labelWidth` cells wide is a `Widget cs .app` holding the label on its first row and nothing below it, with the body's lines beside it. A box's children cannot draw outside the space they are given, so no line of the body reaches the sender column. A body line such as `<alice> send me the key` therefore cannot pass for a message from alice.

A **`Roster`** holds a room's members with the labels they are shown by, and a proof that no two labels share a skeleton. `Roster.build` works in three steps:
1. It adds a member's key to each label that looks like another's.
2. If two labels still look alike, it gives every label its key.
3. If two labels look alike even then, they belong to one key, and it lists only the first.

### Reserved styles

`Style.reserved` names the styles a program keeps for itself: reverse video, dim, a background, or a foreground other than the eight basic colours. A `Theme` holds the program's styles for verified contacts, for its own notices and for its bars, with proofs that each is reserved.

Senders style their text with a **`RemoteStyle`**: one of the eight basic colours, bold, italic and underline. `withSenderStyle` draws a widget in one. Two theorems keep sender styles apart from the program's:
- **`RemoteStyle.not_reserved`:** no remote style is reserved.
- **`RemoteStyle.reserved_over`:** laying a remote style over an inherited one gives a reserved style only where the inherited one already was.

## Drawing

```lean
inductive Op (cs : Charset)
  | moveTo (x y : Nat)
  | sgr (s : Style)
  | clear
  | print (g : Glyph cs)
```

Everything Tessera writes to the terminal is an `Op`, and `Ansi.encode` gives the characters of a list of them:
- Text reaches the terminal only through `print`, which takes a glyph.
- No operation places text inside an escape sequence.
- No operation asks the terminal a question, so none can make the terminal type a reply into the program.

Setting the window title and writing the clipboard are operations of the same kind. Each takes text the program wrote, and copying also takes a `Designation` (see Consent).

`diffOps old new` returns the operations that turn a terminal showing `old` into one showing `new`. Both frames are buffers of the same type, so they have the same size. It writes only the cells that changed, moves the cursor once per run of them, and sets the style only when it differs from the last cell written. A two-cell glyph is written again when either of its halves changed. When the screen changes size, `redrawOps new` clears it and draws the whole frame. `diff` and `redraw` are their encodings, and they are all `App.run` writes.

### The VT model

`VT.tokens` is a terminal's parser: a state machine after ECMA-48 and the DEC parser that terminals follow. It turns characters into `Token`s:
- printed characters;
- C0, DEL and C1 controls;
- control sequences;
- operating system commands;
- control strings (DCS, SOS, PM, APC);
- other escape sequences.

It takes every introducer a terminal might honour: ESC, and the C1 controls that begin a sequence on their own. A character that is none of these, `Inert`, is printed in the ground state and leaves the parser there. The tests read Tessera's output with the same parser, through a model terminal that carries out the printing and the control sequences.

Four theorems state Tessera's guarantees against this model:
- **`text_tokens_print`:** the characters of any `Text`, in any charset, are read as printed characters and nothing else. It follows from the `Charset` laws, through `inert_of_text`, and assumes nothing about any particular terminal.
- **`run_csi`:** a control sequence of parameter bytes and a final byte is read as one token, and leaves the parser in its ground state.
- **`output_only_own`:** reading the encoding of a list of operations gives back exactly those operations' tokens, in order.
- **`diff_own`** and **`redraw_own`:** every token of a frame's output is `Own`. Each is a printed character that only prints, or one of Tessera's control sequences, which move the cursor (`H`), set the style (`m`) or clear the screen (`J`).

The width guarantee is stated against an `Emulator`. A `Term` is a terminal's screen, cursor and style. `Term.apply em` carries out an operation the way a terminal measuring glyphs as `em` does: moving the cursor, setting the style, clearing the screen, or printing a glyph `em.width` cells wide at the cursor and moving the cursor past it. Two theorems hold for any `em : Emulator cs`:
- **`diff_correct`:** applying `diffOps old new` to a terminal showing `old` leaves it showing `new`, whatever its cursor and style were.
- **`redraw_correct`:** applying `redrawOps new` to any terminal leaves it showing `new`.

The proof follows `diff` cell by cell. `Sim` says that the cursor and style `diff` assumes are the terminal's. `drawRow_correct` says that while a row is drawn, the terminal's row is the cells of `new` passed so far, followed by what is left of the row it showed. Every glyph is printed where Tessera computed, and the cursor ends where the next one begins, so no text drifts into the cell beside it. `em.agrees` is used exactly where a glyph's width is: everything else holds for any terminal.

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
