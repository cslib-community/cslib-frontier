/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Sort.Bitonic.ZeroOne
import Cslib.Foundations.Data.Fin.Tuple
import CslibFrontier.Tactic.FinIndex

/-!
# Correctness of Batcher sorting

Bitonic merge orders the projected keys, while the permutation theorems in `Basic` preserve
complete records. Sorting the two halves in opposite directions supplies the bitonic invariant.

## Main results

* `Cslib.BitonicSort.monotone_sort`: ascending sorting orders the keys.
* `Cslib.BitonicSort.antitone_sort`: descending sorting orders the keys.

## References

* Adapted from MassProduction/SortingSemantics/Internal.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

public section

namespace Cslib.BitonicSort

variable {α κ : Type*}

/-- Every minimum half-entry lies below every maximum half-entry of a bitonic tuple. -/
theorem IsBitonic.min_le_max_halves [LinearOrder κ] {n : ℕ} (first second : Fin n → κ)
    (h : IsBitonic (Fin.append first second)) (i j : Fin n) :
    min (first i) (second i) ≤ max (first j) (second j) := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have h' := h (Fin.castAdd n i) (Fin.castAdd n j) (Fin.natAdd n i) (Fin.natAdd n j)
      hij (by fin_index) (by fin_index)
    simpa only [Fin.append_left, Fin.append_right] using h'.1
  · subst j
    exact (min_le_left _ _).trans (le_max_left _ _)
  · have h' := h (Fin.castAdd n j) (Fin.castAdd n i) (Fin.natAdd n j) (Fin.natAdd n i)
      hij (by fin_index) (by fin_index)
    simpa only [Fin.append_left, Fin.append_right] using h'.2

/-- An increasing tuple followed by a decreasing tuple is bitonic. -/
theorem isBitonic_append [LinearOrder κ] {n m : ℕ} {first : Fin n → κ}
    {second : Fin m → κ} (hfirst : Monotone first) (hsecond : Antitone second) :
    IsBitonic (Fin.append first second) := by
  have hpeak (i j k : Fin (n + m)) (hij : i < j) (hjk : j < k) :
      min (Fin.append first second i) (Fin.append first second k) ≤
        Fin.append first second j := by
    cases j using Fin.addCases with
    | left j =>
      cases i using Fin.addCases with
      | left i =>
        exact (min_le_left _ _).trans (by simpa only [Fin.append_left] using hfirst (le_of_lt hij))
      | right _ => fin_index
    | right j =>
      cases k using Fin.addCases with
      | left _ => fin_index
      | right k =>
        exact (min_le_right _ _).trans (by
          simpa only [Fin.append_right] using hsecond (Nat.le_of_add_le_add_left (le_of_lt hjk)))
  intro i j k l hij hjk hkl
  exact ⟨(hpeak i j k hij hjk).trans (le_max_left _ _),
    (hpeak j k l hjk hkl).trans (le_max_right _ _)⟩

private theorem monotone_append [Preorder κ] {n m : ℕ} {first : Fin n → κ}
    {second : Fin m → κ} (hfirst : Monotone first) (hsecond : Monotone second)
    (hcross : ∀ i j, first i ≤ second j) : Monotone (Fin.append first second) := by
  intro i j hij
  cases i using Fin.addCases <;> cases j using Fin.addCases <;> rename_i i j
  · simpa only [Fin.append_left] using hfirst hij
  · simpa only [Fin.append_left, Fin.append_right] using hcross _ _
  · fin_index
  · simpa only [Fin.append_right] using hsecond (Nat.le_of_add_le_add_left hij)

/-- Projected keys of the two halves after one layer are the pointwise minima and maxima. -/
private theorem compareLayer_halves [LinearOrder κ] (key : α → κ) {n : ℕ} (ascending : Bool)
    (input : Fin (n + n) → α) :
    let first := key ∘ input ∘ Fin.castAdd n
    let second := key ∘ input ∘ Fin.natAdd n
    key ∘ compareLayer key ascending input ∘ Fin.castAdd n =
      (if ascending then min first second else max first second) ∧
    key ∘ compareLayer key ascending input ∘ Fin.natAdd n =
      (if ascending then max first second else min first second) := by
  constructor <;> funext i <;> cases ascending <;>
    dsimp only [compareLayer, compareLayer.source, Function.comp_def] <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Fin.addCases_left, Fin.addCases_right] <;>
    split_ifs <;> simp_all [min_def, max_def, -Fin.natAdd_eq_addNat]

private theorem perm_cross [Preorder κ] (key : α → κ) {n m : ℕ}
    {first first' : Fin n → α} {second second' : Fin m → α}
    (hfirst : (List.ofFn first').Perm (List.ofFn first))
    (hsecond : (List.ofFn second').Perm (List.ofFn second))
    (hcross : ∀ i j, key (first i) ≤ key (second j)) (i : Fin n) (j : Fin m) :
    key (first' i) ≤ key (second' j) := by
  obtain ⟨p, hp⟩ := List.mem_ofFn.mp (hfirst.mem_iff.mp (List.mem_ofFn.mpr ⟨i, rfl⟩))
  obtain ⟨q, hq⟩ := List.mem_ofFn.mp (hsecond.mem_iff.mp (List.mem_ofFn.mpr ⟨j, rfl⟩))
  rw [← hp, ← hq]
  exact hcross p q

/-- Merging a bitonic tuple orders its keys in the chosen direction. -/
theorem merge_sorted [LinearOrder κ] (key : α → κ) (depth : ℕ) (ascending : Bool)
    (input : Fin (arity depth) → α) (hbitonic : IsBitonic (key ∘ input)) :
    if ascending then Monotone (key ∘ merge key depth ascending input)
    else Antitone (key ∘ merge key depth ascending input) := by
  induction depth generalizing ascending with
  | zero =>
    cases ascending <;> intro i j _ <;>
      have h : i = j := Subsingleton.elim (α := Fin 1) i j <;> simp [h]
  | succ depth ih =>
    change Fin (arity depth + arity depth) → α at input
    change IsBitonic (n := arity depth + arity depth) (key ∘ input) at hbitonic
    let left := key ∘ input ∘ Fin.castAdd (arity depth)
    let right := key ∘ input ∘ Fin.natAdd (arity depth)
    have hpairs : IsBitonic (Fin.append left right) := by
      rwa [show Fin.append left right = key ∘ input from
        Fin.append_castAdd_natAdd (f := key ∘ input)]
    let compared := compareLayer key (n := arity depth) ascending input
    let first := compared ∘ Fin.castAdd (arity depth)
    let second := compared ∘ Fin.natAdd (arity depth)
    obtain ⟨hfirst, hsecond⟩ := compareLayer_halves key ascending input
    change if ascending then Monotone (key ∘ Fin.append
      (merge key depth ascending first) (merge key depth ascending second)) else
      Antitone (key ∘ Fin.append
        (merge key depth ascending first) (merge key depth ascending second))
    rw [Fin.comp_append]
    cases ascending with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hfirst hsecond
      refine monotone_append (κ := OrderDual κ)
        (ih false first (hfirst ▸ hpairs.max_halves left right))
        (ih false second (hsecond ▸ hpairs.min_halves left right))
        (perm_cross (κ := OrderDual κ) key (merge_perm ..) (merge_perm ..) fun i j => ?_)
      change (key ∘ second) j ≤ (key ∘ first) i
      rw [hfirst, hsecond]
      exact hpairs.min_le_max_halves left right j i
    | true =>
      simp only [↓reduceIte] at hfirst hsecond
      refine monotone_append
        (ih true first (hfirst ▸ hpairs.min_halves left right))
        (ih true second (hsecond ▸ hpairs.max_halves left right))
        (perm_cross key (merge_perm ..) (merge_perm ..) fun i j => ?_)
      change (key ∘ first) i ≤ (key ∘ second) j
      rw [hfirst, hsecond]
      exact hpairs.min_le_max_halves left right i j

/-- Batcher sorting orders the keys in either direction on every input. -/
theorem sort_sorted [LinearOrder κ] (key : α → κ) (depth : ℕ) (ascending : Bool)
    (input : Fin (arity depth) → α) :
    if ascending then Monotone (key ∘ sort key depth ascending input)
    else Antitone (key ∘ sort key depth ascending input) := by
  induction depth generalizing ascending with
  | zero =>
    cases ascending <;> intro i j _ <;>
      have h : i = j := Subsingleton.elim (α := Fin 1) i j <;> simp [h]
  | succ depth ih =>
    apply merge_sorted
    change IsBitonic (n := arity depth + arity depth) (key ∘ Fin.append
      (sort key depth true (input ∘ Fin.castAdd (arity depth)))
      (sort key depth false (input ∘ Fin.natAdd (arity depth))))
    rw [Fin.comp_append]
    exact isBitonic_append (ih true _) (ih false _)

/-- Ascending Batcher sorting gives nondecreasing keys. -/
theorem monotone_sort [LinearOrder κ] (key : α → κ) (depth : ℕ)
    (input : Fin (arity depth) → α) : Monotone (key ∘ sort key depth true input) :=
  sort_sorted key depth true input

/-- Descending Batcher sorting gives nonincreasing keys. -/
theorem antitone_sort [LinearOrder κ] (key : α → κ) (depth : ℕ)
    (input : Fin (arity depth) → α) : Antitone (key ∘ sort key depth false input) :=
  sort_sorted key depth false input

end Cslib.BitonicSort
