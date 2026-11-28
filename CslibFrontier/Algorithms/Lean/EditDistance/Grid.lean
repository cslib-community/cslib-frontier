/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Dynamic programs over pairs of suffixes

The common skeleton of the Wagner–Fischer edit-distance program
[Wagner and Fischer][WagnerFischer1974] and the longest-common-subsequence program
[CLRS, Section 15.4][CLRS2009]. Both fill a table indexed by pairs of suffixes of two words `x` and
`y`. The entry for two empty suffixes is a constant. An entry with one empty suffix depends on its
neighbour along that border. Every other entry depends on three neighbours: the entry dropping the
first letter of both suffixes, the entry dropping only the first letter of the suffix of `x`, and
the entry dropping only the first letter of the suffix of `y`. (The textbook tables are indexed by
prefixes; indexing by suffixes is the same program run on the reversed words, and it lets the
recursion follow the list structure.)

A `GridDP` records the four rules. `GridDP.value D x y` is the entry for the whole words, computed
row by row: `GridDP.row D y x` lists the entries for `x` against every suffix of `y`, longest
first, and the row for `a :: x` is computed from the row for `x` alone (`GridDP.stepRow`). This is
the usual two-row scheme, in which only the previous row is kept. Checked Word-RAM running-time
bounds for the concrete edit-distance and longest-common-subsequence instances live in
`CslibFrontier.Algorithms.WordRAM.EditDistance`.

## Main definitions

* `Cslib.Algorithms.Lean.EditDistance.GridDP`: the four rules of a table over pairs of suffixes.
* `Cslib.Algorithms.Lean.EditDistance.GridDP.value`: the entry for the whole words.

## Main results

* `Cslib.Algorithms.Lean.EditDistance.GridDP.value_nil_nil`, `value_cons_nil`, `value_nil_cons`,
  `value_cons_cons`: `value` satisfies the four rules.

## References

* [R. A. Wagner and M. J. Fischer, *The string-to-string correction problem*][WagnerFischer1974]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.EditDistance

/-- The rules of a dynamic program over pairs of suffixes of two words over `α`, with entries in
`β`. The entry for `(a :: x, b :: y)` is `consCons a b d u l`, where `d`, `u` and `l` are the
entries for `(x, y)`, `(x, b :: y)` and `(a :: x, y)`. -/
structure GridDP (α β : Type*) where
  /-- The entry for two empty words. -/
  nilNil : β
  /-- The entry for `(a :: x, [])` from the entry for `(x, [])`. -/
  consNil : α → β → β
  /-- The entry for `([], b :: y)` from the entry for `([], y)`. -/
  nilCons : α → β → β
  /-- The entry for `(a :: x, b :: y)` from the entries for `(x, y)`, `(x, b :: y)` and
  `(a :: x, y)`. -/
  consCons : α → α → β → β → β → β

namespace GridDP

variable {α β : Type*} (D : GridDP α β)

/-- The row of the empty word: the entries for `([], y')`, for every suffix `y'` of `y`, longest
first. -/
@[expose] def nilRow : List α → List β
  | [] => [D.nilNil]
  | b :: y =>
    let r := nilRow y
    D.nilCons b (r.headD D.nilNil) :: r

/-- The row of `a :: x` computed from the row `r` of `x`: the entries for `(a :: x, y')`, for every
suffix `y'` of `y`, longest first. -/
@[expose] def stepRow (a : α) : List α → List β → List β
  | [], r => [D.consNil a (r.headD D.nilNil)]
  | b :: y, r =>
    let s := stepRow a y r.tail
    D.consCons a b (r.tail.headD D.nilNil) (r.headD D.nilNil) (s.headD D.nilNil) :: s

/-- The row of `x`: the entries for `(x, y')`, for every suffix `y'` of `y`, longest first. -/
@[expose] def row (y : List α) : List α → List β
  | [] => D.nilRow y
  | a :: x => D.stepRow a y (row y x)

/-- The entry for the whole words `x` and `y`. -/
@[expose] def value (x y : List α) : β :=
  (D.row y x).headD D.nilNil

theorem tail_nilRow (b : α) (y : List α) : (D.nilRow (b :: y)).tail = D.nilRow y := rfl

theorem tail_stepRow (a b : α) (y : List α) (r : List β) :
    (D.stepRow a (b :: y) r).tail = D.stepRow a y r.tail := rfl

/-- Dropping the head of the row of `x` against `b :: y` gives the row of `x` against `y`. -/
theorem tail_row (b : α) (y : List α) : ∀ x : List α, (D.row (b :: y) x).tail = D.row y x
  | [] => rfl
  | a :: x => by
    rw [row, tail_stepRow, tail_row b y x]
    rfl

/-- A row contains one entry for each suffix, including the empty suffix. -/
@[simp] theorem length_row (y x : List α) : (D.row y x).length = y.length + 1 := by
  induction y with
  | nil => cases x <;> rfl
  | cons b y ih =>
    have h := congrArg List.length (D.tail_row b y x)
    have hn : D.row (b :: y) x ≠ [] := by cases x <;> simp [row, nilRow, stepRow]
    simpa [List.length_tail, hn, ih] using (show (D.row (b :: y) x).length = y.length + 2 by
      have := List.length_pos_iff.mpr hn
      rw [List.length_tail, ih] at h
      omega)

/-- Column `k` holds the value for the suffix starting at position `k`. -/
theorem getElem_row (y x : List α) (k : ℕ) (hk : k < (D.row y x).length) :
    (D.row y x)[k] = D.value x (y.drop k) := by
  induction y generalizing k with
  | nil =>
    have : k = 0 := by simpa using hk
    subst k
    cases x <;> rfl
  | cons b y ih =>
    cases k with
    | zero =>
      cases x <;> rfl
    | succ k =>
      have ht := D.tail_row b y x
      have hlt : k < ((D.row (b :: y) x).tail).length := by
        rw [List.length_tail]; omega
      simpa only [List.drop_succ_cons, ← ht, List.getElem_tail] using
        (ih k (ht ▸ hlt))

@[simp] theorem value_nil_nil : D.value [] [] = D.nilNil := rfl

theorem value_cons_nil (a : α) (x : List α) :
    D.value (a :: x) [] = D.consNil a (D.value x []) := rfl

theorem value_nil_cons (b : α) (y : List α) :
    D.value [] (b :: y) = D.nilCons b (D.value [] y) := rfl

theorem value_cons_cons (a b : α) (x y : List α) :
    D.value (a :: x) (b :: y) =
      D.consCons a b (D.value x y) (D.value x (b :: y)) (D.value (a :: x) y) := by
  simp only [value, row, stepRow, List.headD_cons]
  rw [← tail_row D b y x]

end GridDP

end Cslib.Algorithms.Lean.EditDistance
