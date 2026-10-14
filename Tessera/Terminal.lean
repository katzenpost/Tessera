/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Diff

/-! # Drawing is correct

A model of a terminal that measures glyphs as an `Emulator` does, and the proof that drawing a
frame leaves it showing that frame: `diff_correct` and `redraw_correct`. -/

namespace Tessera

variable {cs : Charset}

namespace Cell

theorem wellFormed_glyph_cons {g : Glyph cs} {s : Style} {l : List (Cell cs)}
    (hl : ∀ t, l ≠ .wideRight :: t) (h : wellFormed (.glyph g s :: l)) : Narrow g ∧ wellFormed l := by
  match l, hl with
  | [], _ => simpa [wellFormed] using h
  | .blank _ :: _, _ => simpa [wellFormed] using h
  | .glyph _ _ :: _, _ => simpa [wellFormed] using h
  | .wideRight :: t, hl => exact absurd rfl (hl t)

theorem wellFormed_pair {g : Glyph cs} {s : Style} {l : List (Cell cs)}
    (h : wellFormed (.glyph g s :: .wideRight :: l)) : g.wide ∧ wellFormed l := by
  simpa [wellFormed] using h

theorem head_ne_wideRight {l : List (Cell cs)} (h : wellFormed l) : ∀ t, l ≠ .wideRight :: t := by
  rintro t rfl; simp [wellFormed] at h

/-- After a cell that is not the left half of a pair, the rest is well formed. -/
theorem wellFormed_tail {c : Cell cs} {l : List (Cell cs)} (h : wellFormed (c :: l))
    (hp : ∀ g s t, c = .glyph g s → l ≠ .wideRight :: t) : wellFormed l := by
  match c with
  | .wideRight => simp [wellFormed] at h
  | .blank _ => simpa [wellFormed] using h
  | .glyph g s => exact (wellFormed_glyph_cons (fun t => hp g s t rfl) h).2

theorem cut_self {n : Nat} {l : List (Cell cs)} (h : l.length ≤ n) : cut n l = l := by
  induction n, l using cut.induct with
  | case1 t => simp at h; subst h; simp [cut]
  | case2 x hx => simp [cut.eq_2 x hx]
  | case3 => simp at h
  | case4 n g s rest hn ih =>
    simp only [List.length_cons] at h
    simp [cut, hn, ih (by omega)]
  | case5 n c rest hp ih =>
    rw [cut.eq_4 _ _ _ hp]
    simp only [List.length_cons] at h
    rw [ih (by omega)]

/-- Cutting at the end of a well-formed prefix keeps exactly the prefix. -/
theorem cut_append {a b : List (Cell cs)} (ha : wellFormed a) (hb : wellFormed b) :
    cut a.length (a ++ b) = a := by
  induction a using wellFormed.induct with
  | case1 => simp [cut]
  | case2 => simp [wellFormed] at ha
  | case3 s rest ih =>
    simp only [List.length_cons, List.cons_append]
    rw [cut.eq_4 _ _ _ (by intro g s' t h; cases h)]
    rw [ih (by simpa [wellFormed] using ha)]
  | case4 g s rest ih =>
    obtain ⟨_, hr⟩ := wellFormed_pair ha
    simp only [List.length_cons, List.cons_append]
    rw [show rest.length + 1 + 1 = (rest.length + 1) + 1 from rfl, cut.eq_3]
    simp [ih hr]
  | case5 g s rest hrest ih =>
    obtain ⟨_, hr⟩ := wellFormed_glyph_cons (fun t h => hrest t h) ha
    simp only [List.length_cons, List.cons_append]
    rw [cut.eq_4 _ _ _ (by
      intro g' s' t he hr'
      cases rest with
      | nil => exact head_ne_wideRight hb t (by simpa using hr')
      | cons c r =>
        simp only [List.cons_append, List.cons.injEq] at hr'
        exact hrest r (by rw [hr'.1]))]
    rw [ih hr]

/-- Skipping past a well-formed prefix skips it exactly. -/
theorem skip_append {a b : List (Cell cs)} (ha : wellFormed a) (hb : wellFormed b) (m : Nat) :
    skip (a.length + m) (a ++ b) = skip m b := by
  induction a using wellFormed.induct with
  | case1 => simp
  | case2 => simp [wellFormed] at ha
  | case3 s rest ih =>
    simp only [List.length_cons, List.cons_append]
    rw [show rest.length + 1 + m = (rest.length + m) + 1 by omega,
      skip.eq_4 _ _ _ (by intro g s' t h; cases h)]
    exact ih (by simpa [wellFormed] using ha)
  | case4 g s rest ih =>
    obtain ⟨_, hr⟩ := wellFormed_pair ha
    simp only [List.length_cons, List.cons_append]
    rw [show rest.length + 1 + 1 + m = (rest.length + 1 + m) + 1 by omega, skip.eq_3]
    simp only [show rest.length + 1 + m ≠ 0 by omega, ↓reduceIte,
      show rest.length + 1 + m - 1 = rest.length + m by omega]
    exact ih hr
  | case5 g s rest hrest ih =>
    obtain ⟨_, hr⟩ := wellFormed_glyph_cons (fun t h => hrest t h) ha
    simp only [List.length_cons, List.cons_append]
    rw [show rest.length + 1 + m = (rest.length + m) + 1 by omega, skip.eq_4 _ _ _ (by
      intro g' s' t he hr'
      cases rest with
      | nil => exact head_ne_wideRight hb t (by simpa using hr')
      | cons c r =>
        simp only [List.cons_append, List.cons.injEq] at hr'
        exact hrest r (by rw [hr'.1]))]
    exact ih hr

theorem skip_skip {n : Nat} {l : List (Cell cs)} (h : wellFormed l) (m : Nat) :
    skip m (skip n l) = skip (n + m) l := by
  induction n, l using skip.induct with
  | case1 t => simp [skip]
  | case2 x hx => simp [skip.eq_2 x hx]
  | case3 g s rest =>
    cases m with
    | zero => simp [skip]
    | succ m =>
      rw [show Nat.succ 0 + (m + 1) = (m + 1) + 1 by omega, skip.eq_3]
      simp only [skip, ↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
  | case4 n g s rest hn ih =>
    obtain ⟨_, hr⟩ := wellFormed_pair h
    rw [skip.eq_3, if_neg hn, ih hr, show n.succ + m = (n + m) + 1 by omega, skip.eq_3,
      if_neg (by omega), show n - 1 + m = n + m - 1 by omega]
  | case5 n c rest hp ih =>
    rw [skip.eq_4 _ _ _ hp, ih (wellFormed_tail h fun g s t hc ht => hp g s t hc ht),
      show n.succ + m = (n + m) + 1 by omega, skip.eq_4 _ _ _ hp]

/-- Skipping to a cell that is not a right half drops the cells before it, and changes none. -/
theorem skip_eq_drop {n : Nat} {l : List (Cell cs)} (h : wellFormed l)
    (hd : ∀ t, l.drop n ≠ .wideRight :: t) : skip n l = l.drop n := by
  induction n, l using skip.induct with
  | case1 t => simp [skip]
  | case2 x hx => simp [skip.eq_2 x hx]
  | case3 g s rest => exact absurd rfl (hd rest)
  | case4 n g s rest hn ih =>
    obtain ⟨_, hr⟩ := wellFormed_pair h
    rw [skip.eq_3, if_neg hn]
    have : n.succ = (n - 1) + 1 + 1 := by omega
    rw [this, List.drop_succ_cons, List.drop_succ_cons] at hd ⊢
    exact ih hr hd
  | case5 n c rest hp ih =>
    rw [skip.eq_4 _ _ _ hp, List.drop_succ_cons]
    exact ih (wellFormed_tail h fun g s t hc ht => hp g s t hc ht) (by simpa using hd)

theorem skip_length {l : List (Cell cs)} : skip l.length l = [] :=
  List.eq_nil_of_length_eq_zero (by simp [length_skip])

end Cell

open Cell Ansi

/-- The cells a terminal draws for `g` in style `s`, measuring it as `em` does. A space is a
blank. -/
def Emulator.cells (em : Emulator cs) (g : Glyph cs) (s : Style) : List (Cell cs) :=
  if g.char = ' ' then [.blank s]
  else if em.width g.char = 2 then [.glyph g s, .wideRight]
  else [.glyph g s]

theorem Emulator.cells_eq (em : Emulator cs) (g : Glyph cs) (s : Style) :
    em.cells g s = ofGlyphs s [g] := by
  simp only [Emulator.cells, ofGlyphs, em.agrees g.char g.printable, Glyph.wide, beq_iff_eq]

theorem Emulator.wellFormed_cells (em : Emulator cs) (g : Glyph cs) (s : Style) :
    wellFormed (em.cells g s) := by
  rw [em.cells_eq]; exact wellFormed_ofGlyphs s [g]

/-- A terminal: what it shows, where its cursor is, and the style it prints in. -/
structure Term (cs : Charset) (w h : Nat) where
  screen : Buffer cs w h
  cursor : Nat × Nat
  style : Style

namespace Term

variable {w h : Nat} (em : Emulator cs)

/-- What a terminal measuring glyphs as `em` does does with an operation. -/
def apply (t : Term cs w h) : Op cs → Term cs w h
  | .moveTo x y => { t with cursor := (x, y) }
  | .sgr s => { t with style := s }
  | .clear => { t with screen := .blank w h { bg := t.style.bg } }
  | .print g =>
    { t with
      screen := t.screen.putCells t.cursor.1 t.cursor.2 (em.cells g t.style)
        (em.wellFormed_cells g t.style)
      cursor := (t.cursor.1 + em.width g.char, t.cursor.2) }
  | .title _ => t

def exec (t : Term cs w h) (ops : List (Op cs)) : Term cs w h := ops.foldl (apply em) t

@[simp] theorem exec_nil (t : Term cs w h) : t.exec em [] = t := rfl

@[simp] theorem exec_append (t : Term cs w h) (a b : List (Op cs)) :
    t.exec em (a ++ b) = (t.exec em a).exec em b := by
  simp [exec, List.foldl_append]

@[simp] theorem exec_cons (t : Term cs w h) (op : Op cs) (ops : List (Op cs)) :
    t.exec em (op :: ops) = (t.apply em op).exec em ops := rfl

end Term

/-- The cursor and style `diff` takes the terminal to have are the ones it has. -/
def Sim {w h : Nat} (st : DiffState cs) (t : Term cs w h) : Prop :=
  (∀ p, st.cursor = some p → t.cursor = p) ∧ (∀ s, st.style = some s → t.style = s)

theorem Row.ext' {w : Nat} {a b : Row cs w} (h : a.cells = b.cells) : a = b := by
  cases a; cases b; simp_all

theorem Buffer.ext' {w h : Nat} {a b : Buffer cs w h} (hr : ∀ y (hy : y < h), a.rows[y] = b.rows[y]) :
    a = b := by
  cases a; cases b; congr 1; exact Vector.ext hr

theorem Buffer.putCells_rows {w h : Nat} (b : Buffer cs w h) (x y : Nat) (seg : List (Cell cs))
    (hseg : wellFormed seg) (y' : Nat) (hy' : y' < h) :
    (b.putCells x y seg hseg).rows[y'] = if y = y' then b.rows[y'].splice x seg hseg else b.rows[y'] := by
  unfold Buffer.putCells Buffer.modifyRow
  split
  · simp only [Vector.getElem_set]
    split <;> simp_all
  · have : y ≠ y' := by omega
    simp [this]

theorem Row.splice_prefix {w : Nat} (r : Row cs w) {P S seg : List (Cell cs)} (hr : r.cells = P ++ S)
    (hP : wellFormed P) (hS : wellFormed S) (hseg : wellFormed seg)
    (hfit : P.length + seg.length ≤ w) :
    (r.splice P.length seg hseg).cells = P ++ seg ++ skip seg.length S := by
  have hx : P.length ≤ w := by omega
  simp only [Row.splice, hx, ↓reduceDIte]
  rw [cut_self (n := w - P.length) (by omega), hr, cut_append hP hS, skip_append hP hS]

section Correct

variable {w h : Nat} (em : Emulator cs) (t0 : Term cs w h)

/-- The terminal after the operations `st` has written. -/
abbrev model (st : DiffState cs) : Term cs w h := t0.exec em st.ops.toList

theorem model_write (st : DiffState cs) (hsim : Sim st (model em t0 st)) (x y : Nat) (g : Glyph cs)
    (k : Nat) (s : Style) :
    (model em t0 (st.write x y g k s)).screen =
        (model em t0 st).screen.putCells x y (em.cells g s) (em.wellFormed_cells g s) ∧
      (model em t0 (st.write x y g k s)).cursor = (x + em.width g.char, y) ∧
      (model em t0 (st.write x y g k s)).style = s := by
  obtain ⟨hc, hs⟩ := hsim
  simp only [model] at hc hs ⊢
  simp only [DiffState.write, Array.toList_append, Term.exec_append]
  generalize t0.exec em st.ops.toList = T at hc hs ⊢
  by_cases h1 : st.cursor = some (x, y)
  · have hT := hc _ h1
    by_cases h2 : st.style = some s
    · have hS := hs _ h2
      simp [h1, h2, hT, hS, Term.exec, Term.apply]
    · simp [h1, h2, hT, Term.exec, Term.apply]
  · by_cases h2 : st.style = some s
    · have hS := hs _ h2
      simp [h1, h2, hS, Term.exec, Term.apply]
    · simp [h1, h2, Term.exec, Term.apply]

/-- What `drawRow` does to the terminal: row `y` ends as `N`, and no other row changes. While it
draws, the row is the cells of `N` it has passed, `P`, then what is left of the row it began
with, `R`. -/
theorem drawRow_correct (y : Nat) (hy : y < h) (all : Bool) (R O N : List (Cell cs))
    (hR : wellFormed R) (hRl : R.length = w) (hOl : O.length = w) (hNl : N.length = w)
    (hO : all = false → O = R) (S0 : Buffer cs w h) :
    ∀ x ns os st, ∀ P, P ++ ns = N → P.length = x → wellFormed P → wellFormed ns →
      os = O.drop x → Sim st (model em t0 st) →
      (model em t0 st).screen.rows[y].cells = P ++ skip x R →
      (∀ y' (hy' : y' < h), y' ≠ y → (model em t0 st).screen.rows[y'] = S0.rows[y']) →
      Sim (drawRow y all x ns os st) (model em t0 (drawRow y all x ns os st)) ∧
      (model em t0 (drawRow y all x ns os st)).screen.rows[y].cells = N ∧
      (∀ y' (hy' : y' < h), y' ≠ y →
        (model em t0 (drawRow y all x ns os st)).screen.rows[y'] = S0.rows[y']) := by
  intro x ns os st
  induction x, ns, os, st using drawRow.induct y all with
  | case1 x g s ns o₁ o₂ os st st₁ ih =>
    intro P hPN hPl hP hns hos hsim hrow hother
    obtain ⟨hg, hns'⟩ := wellFormed_pair hns
    have hlen : x + 2 + ns.length = w := by
      have := congrArg List.length hPN; simp at this; omega
    have hos' : os = O.drop (x + 2) := by
      have : (O.drop x).drop 2 = O.drop (x + 2) := by simp [List.drop_drop]
      rw [← this, ← hos]; rfl
    have hP' : wellFormed (P ++ [.glyph g s, .wideRight]) :=
      wellFormed_append hP (wellFormed_cons_wide hg rfl)
    have hPN' : (P ++ [.glyph g s, .wideRight]) ++ ns = N := by simpa using hPN
    have hPl' : (P ++ [Cell.glyph g s, .wideRight]).length = x + 2 := by simp [hPl]
    have hd : drawRow y all x (.glyph g s :: .wideRight :: ns) (o₁ :: o₂ :: os) st =
        drawRow y all (x + 2) ns os st₁ := by rw [drawRow]
    rw [hd]
    simp only [st₁] at ih ⊢
    by_cases hc : (all || Cell.glyph g s != o₁ || Cell.wideRight != o₂) = true
    · -- Changed: the glyph is written, two cells wide.
      rw [if_pos hc] at ih ⊢
      have hw2 : cs.width g.char = 2 := by simpa [Glyph.wide] using hg
      have hw : em.width g.char = 2 := by rw [em.agrees g.char g.printable]; exact hw2
      have hsp : g.char ≠ ' ' := fun he => by
        have := cs.space_width; rw [← he, hw2] at this; omega
      have hcells : em.cells g s = [.glyph g s, .wideRight] := by simp [Emulator.cells, hsp, hw]
      obtain ⟨hscr, hcur, hsty⟩ := model_write em t0 st hsim x y g 2 s
      apply ih (P ++ [.glyph g s, .wideRight]) hPN' hPl' hP' hns' hos'
      · exact ⟨fun p hp => by simp [DiffState.write] at hp; rw [hcur, hw, ← hp],
          fun s' hs' => by simp [DiffState.write] at hs'; rw [hsty, hs']⟩
      · rw [hscr, Buffer.putCells_rows _ _ _ _ _ _ hy, if_pos rfl]
        simp only [hcells]
        rw [← hPl, Row.splice_prefix _ hrow hP (wellFormed_skip x hR) _ (by simp; omega),
          hPl, skip_skip hR]
        simp
      · intro y' hy' hne
        rw [hscr, Buffer.putCells_rows _ _ _ _ _ _ hy', if_neg (Ne.symm hne)]
        exact hother y' hy' hne
    · -- Unchanged: the terminal already shows it.
      rw [if_neg hc] at ih ⊢
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not,
        Bool.not_eq_true] at hc
      obtain ⟨⟨hall, h1⟩, h2⟩ := hc
      subst h1 h2
      have hOR := hO hall
      subst hOR
      have hdrop : skip x O = O.drop x := skip_eq_drop hR (by rw [← hos]; intro t h; cases h)
      apply ih (P ++ [.glyph g s, .wideRight]) hPN' hPl' hP' hns' hos' hsim
      · rw [hrow, ← skip_skip hR, hdrop, ← hos]
        simp [skip]
      · exact hother
  | case2 x c ns o os st hp st₁ ih =>
    intro P hPN hPl hP hns hos hsim hrow hother
    have hlen : x + 1 + ns.length = w := by
      have := congrArg List.length hPN; simp at this; omega
    have hoslen : os.length = ns.length := by
      have := congrArg List.length hos; simp [hOl] at this; omega
    -- A glyph here is not the left half of a pair: the old row would have ended first.
    have hnp : ∀ g s t, c = .glyph g s → ns ≠ .wideRight :: t := by
      intro g s t hc hn
      cases os with
      | nil => subst hn; simp at hoslen
      | cons o₂ os' => exact hp g s t o₂ os' hc hn rfl
    have hns' : wellFormed ns := wellFormed_tail hns hnp
    have hos' : os = O.drop (x + 1) := by
      have : (O.drop x).drop 1 = O.drop (x + 1) := by simp [List.drop_drop]
      rw [← this, ← hos]; rfl
    have hP' : wellFormed (P ++ [c]) := by
      refine wellFormed_append hP ?_
      match c, hns with
      | .wideRight, h => simp [wellFormed] at h
      | .blank s, _ => exact wellFormed_cons_blank rfl
      | .glyph g s, h =>
        exact wellFormed_cons_narrow (wellFormed_glyph_cons (hnp g s · rfl) h).1 rfl
    have hPN' : (P ++ [c]) ++ ns = N := by simpa using hPN
    have hPl' : (P ++ [c]).length = x + 1 := by simp [hPl]
    have hd : drawRow y all x (c :: ns) (o :: os) st = drawRow y all (x + 1) ns os st₁ := by
      cases c with
      | glyph g s =>
        rw [drawRow.eq_2 _ _ _ _ _ _ _ g s fun g' s' n o' os' he hn ho => hp g' s' n o' os' he hn ho]
      | blank s => rw [drawRow.eq_3]
      | wideRight => rw [drawRow.eq_4]
    rw [hd]
    simp only [st₁] at ih ⊢
    by_cases hc : (all || c != o) = true
    · -- Changed: one cell is written.
      rw [if_pos hc] at ih ⊢
      have step : ∀ (g : Glyph cs) (k : Nat) (s : Style), em.cells g s = [c] →
          em.width g.char = k → k = 1 →
          Sim (st.write x y g k s) (model em t0 (st.write x y g k s)) ∧
          (model em t0 (st.write x y g k s)).screen.rows[y].cells = P ++ [c] ++ skip (x + 1) R ∧
          (∀ y' (hy' : y' < h), y' ≠ y →
            (model em t0 (st.write x y g k s)).screen.rows[y'] = S0.rows[y']) := by
        intro g k s hcells hw hk
        subst hk
        obtain ⟨hscr, hcur, hsty⟩ := model_write em t0 st hsim x y g 1 s
        refine ⟨⟨fun p hp => by simp [DiffState.write] at hp; rw [hcur, hw, ← hp],
          fun s' hs' => by simp [DiffState.write] at hs'; rw [hsty, hs']⟩, ?_, ?_⟩
        · rw [hscr, Buffer.putCells_rows _ _ _ _ _ _ hy, if_pos rfl]
          simp only [hcells]
          rw [← hPl, Row.splice_prefix _ hrow hP (wellFormed_skip x hR) _ (by simp; omega),
            hPl, skip_skip hR]
          simp
        · intro y' hy' hne
          rw [hscr, Buffer.putCells_rows _ _ _ _ _ _ hy', if_neg (Ne.symm hne)]
          exact hother y' hy' hne
      match c, hnp, hns, hP', hPN', hPl', step, ih with
      | .wideRight, _, h, _, _, _, _, _ => simp [wellFormed] at h
      | .blank s, _, _, hP', hPN', hPl', step, ih =>
        have hw : em.width (Glyph.space (cs := cs)).char = 1 := by
          rw [em.agrees _ Glyph.space.printable]; exact cs.space_width
        obtain ⟨h1, h2, h3⟩ := step .space 1 s (by simp [Emulator.cells, Glyph.space]) hw rfl
        exact ih (P ++ [.blank s]) hPN' hPl' hP' hns' hos' h1 h2 h3
      | .glyph g s, hnp, h, hP', hPN', hPl', step, ih =>
        have hn := (wellFormed_glyph_cons (hnp g s · rfl) h).1
        simp only [Narrow, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hn
        have hw1 : cs.width g.char = 1 := by
          rcases cs.printable_width g.char g.printable with h | h
          · exact h
          · simp [Glyph.wide, h] at hn
        have hw : em.width g.char = g.width := by
          rw [em.agrees g.char g.printable]; rfl
        have hcells : em.cells g s = [.glyph g s] := by
          simp [Emulator.cells, hn.2, em.agrees g.char g.printable, hw1]
        obtain ⟨h1, h2, h3⟩ := step g g.width s hcells hw (by simpa [Glyph.width] using hw1)
        exact ih (P ++ [.glyph g s]) hPN' hPl' hP' hns' hos' h1 h2 h3
    · -- Unchanged: the terminal already shows it.
      rw [if_neg hc] at ih ⊢
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not,
        Bool.not_eq_true] at hc
      obtain ⟨hall, hco⟩ := hc
      subst hco
      have hOR := hO hall
      subst hOR
      have hhead : ∀ t, O.drop x ≠ .wideRight :: t := by
        rw [← hos]; intro t h
        cases h; simp [wellFormed] at hns
      have hdrop : skip x O = O.drop x := skip_eq_drop hR hhead
      have hpair : ∀ g s t, c = .glyph g s → os ≠ .wideRight :: t := by
        intro g s t hc hn
        have hw := wellFormed_skip x hR
        rw [hdrop, ← hos, hc, hn] at hw
        have hnar := (wellFormed_glyph_cons (hnp g s · hc) (hc ▸ hns)).1
        simp [wellFormed, Narrow] at hw hnar
        simp_all
      apply ih (P ++ [c]) hPN' hPl' hP' hns' hos' hsim
      · rw [hrow, ← skip_skip hR, hdrop, ← hos,
          show (1 : Nat) = Nat.succ 0 from rfl, skip.eq_4 _ _ _ hpair]
        simp [skip]
      · exact hother
  | case3 t x old st h1 h2 =>
    intro P hPN hPl hP hns hos hsim hrow hother
    have ht : t = [] := by
      cases t with
      | nil => rfl
      | cons c ns =>
        have hlen := congrArg List.length hPN
        have hol := congrArg List.length hos
        simp [hOl] at hlen hol
        cases old with
        | nil => simp at hol; omega
        | cons o os => exact (h2 c ns o os rfl rfl).elim
    subst ht
    simp only [List.append_nil] at hPN
    subst hPN
    have hdr : drawRow y all x [] old st = st := by
      cases old <;> simp [drawRow]
    rw [hdr]
    refine ⟨hsim, ?_, hother⟩
    rw [hrow, ← hPl, show P.length = R.length by omega, skip_length]
    simp

/-- The rows `drawRows` has drawn after the first `k`. -/
def rowsDrawn (old new : Buffer cs w h) (all : Bool) (start : DiffState cs) (k : Nat) :
    DiffState cs :=
  (List.range k).foldl (init := start) fun s y =>
    drawRow y all 0 (new.rows[y]?.map (·.cells) |>.getD []) (old.rows[y]?.map (·.cells) |>.getD []) s

theorem rowsDrawn_correct (old new : Buffer cs w h) (all : Bool) (start : DiffState cs)
    (hsim : Sim start (model em t0 start)) (hO : all = false → old = (model em t0 start).screen) :
    ∀ k, k ≤ h →
      Sim (rowsDrawn old new all start k) (model em t0 (rowsDrawn old new all start k)) ∧
      ∀ y (hy : y < h), (model em t0 (rowsDrawn old new all start k)).screen.rows[y] =
        if y < k then new.rows[y] else (model em t0 start).screen.rows[y] := by
  intro k
  induction k with
  | zero => intro _; exact ⟨hsim, fun y hy => by simp [rowsDrawn]⟩
  | succ k ih =>
    intro hk
    obtain ⟨hsim', hrows⟩ := ih (by omega)
    have hkh : k < h := by omega
    have hstep : rowsDrawn old new all start (k + 1) =
        drawRow k all 0 new.rows[k].cells old.rows[k].cells (rowsDrawn old new all start k) := by
      simp [rowsDrawn, List.range_succ, List.foldl_append, hkh]
    rw [hstep]
    have hRk : (model em t0 (rowsDrawn old new all start k)).screen.rows[k] =
        (model em t0 start).screen.rows[k] := by
      rw [hrows k hkh]; simp
    obtain ⟨h1, h2, h3⟩ := drawRow_correct em t0 k hkh all
      (model em t0 start).screen.rows[k].cells old.rows[k].cells new.rows[k].cells
      (model em t0 start).screen.rows[k].wf (model em t0 start).screen.rows[k].length_eq
      old.rows[k].length_eq new.rows[k].length_eq (fun h => by rw [hO h])
      (model em t0 (rowsDrawn old new all start k)).screen
      0 new.rows[k].cells old.rows[k].cells (rowsDrawn old new all start k) [] rfl rfl rfl
      new.rows[k].wf rfl hsim' (by rw [hRk]; simp [skip]) (fun _ _ _ => rfl)
    refine ⟨h1, fun y hy => ?_⟩
    by_cases hyk : y = k
    · subst hyk
      simpa using Row.ext' h2
    · rw [h3 y hy hyk, hrows y hy]
      by_cases hlt : y < k
      · simp [hlt, show y < k + 1 by omega]
      · simp [hlt, show ¬ y < k + 1 by omega]

theorem drawRows_correct (old new : Buffer cs w h) (all : Bool) (start : DiffState cs)
    (hsim : Sim start (model em t0 start)) (hO : all = false → old = (model em t0 start).screen) :
    (t0.exec em (drawRows old new all start).toList).screen = new := by
  obtain ⟨_, hrows⟩ := rowsDrawn_correct em t0 old new all start hsim hO h (Nat.le_refl _)
  have hd : drawRows old new all start = (rowsDrawn old new all start h).ops := rfl
  rw [hd]
  exact Buffer.ext' fun y hy => by simpa [hy] using hrows y hy

/-- On a terminal that measures glyphs as Tessera does, drawing the difference between two frames
on a terminal showing the first leaves it showing the second. -/
theorem diff_correct (old new : Buffer cs w h) (ht : t0.screen = old) :
    (t0.exec em (diffOps old new)).screen = new := by
  have hrows := drawRows_correct em t0 old new false {} ⟨by simp, by simp⟩
    (fun _ => by show old = (t0.exec em []).screen; simp [ht])
  dsimp only [diffOps]
  split
  · rename_i he
    simp only [Term.exec_nil]
    simp only [Array.isEmpty_iff] at he
    simpa [he] using hrows
  · simp only [Term.exec_append]
    simpa [Term.exec, Term.apply] using hrows

/-- On a terminal that measures glyphs as Tessera does, redrawing a frame leaves it showing that
frame, whatever it showed before. -/
theorem redraw_correct (new : Buffer cs w h) : (t0.exec em (redrawOps new)).screen = new := by
  have hrows := drawRows_correct em t0 new new true { ops := #[.sgr {}, .clear] }
    ⟨by simp, by simp⟩ (by simp)
  unfold redrawOps
  simp only [Term.exec_append]
  simpa [Term.exec, Term.apply] using hrows

end Correct

end Tessera
