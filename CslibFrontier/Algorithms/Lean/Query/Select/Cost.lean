/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.Select.Correctness
public import CslibFrontier.Algorithms.Lean.Query.Sort.Merge.CountBound
public import Cslib.Algorithms.Lean.Query.Bounds

/-!
# A linear comparison bound for deterministic selection

`Cslib.Query.select k xs` makes at most `32 * xs.length` comparisons, for every oracle
(`Cslib.Query.select_upperBound`). The proof solves the median-of-medians recurrence
`T(n) ≤ (6n + 1)/5 + T(⌈n/5⌉) + 2n + T(selectSideBound n)` by strong induction on `n`:

* each full group uses exactly six comparisons. A final group of four can use five, so computing
  all group medians costs at most `(6n + 1)/5` comparisons (`Cslib.Query.medians_countQueries_le`);
* the three-way partition takes at most `2n` comparisons
  (`Cslib.Query.partition3_countQueries_le`);
* the recursive calls are on the `⌈n/5⌉` medians and on one side of the partition, which has at
  most `selectSideBound n ≤ 7n/10 + 2` elements (checked by `select` itself, so the bound holds
  for every oracle, not only for those implementing a total preorder);
* lists of at most `selectCutoff = 730` elements are merge-sorted with at most
  `n * ⌈log₂ n⌉ ≤ 10n` comparisons.

To absorb rounding in the recursive sizes, the induction bounds `T(n)` by the larger of
`10n` and `32n - 64`. For a large split, the two subproblem bounds absorb the rounding loss
of at most 64 comparisons. The refined `PICK` algorithm uses at most `5.4305n` comparisons
[BlumFloydPrattRivestTarjan1973].

## Main results

* `Cslib.Query.partition3_countQueries_le`: the partition makes at most `2n` comparisons.
* `Cslib.Query.groupMedian_countQueries_le`: the sorting-based group helper costs at most
  `mergeSortCountBound` of its input length.
* `Cslib.Query.medians_countQueries_le`: computing the medians of all blocks costs at most
  `(6n + 1)/5` comparisons.
* `Cslib.Query.select_countQueries_le`, `Cslib.Query.select_upperBound`: selection makes at most
  `32n` comparisons.

## References

* [M. Blum, R. W. Floyd, V. Pratt, R. L. Rivest and R. E. Tarjan, *Time bounds for
  selection*][BlumFloydPrattRivestTarjan1973].
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 9.3.
-/

public section

namespace Cslib.Query

variable {α : Type}

/-- The three-way partition makes at most two comparisons per element. -/
theorem partition3_countQueries_le (oracle : {ι : Type} → LEQuery α ι → ι) (p : α)
    (xs : List α) : (partition3 p xs).countQueries oracle ≤ 2 * xs.length := by
  fun_induction partition3 p xs with
  | case1 => simp -- []
  | case2 x xs ih =>
    rcases hpart : (partition3 p xs).eval oracle with ⟨L, E, G⟩
    simp only [FreeM.countQueries_bind, hpart, LEQuery.ask, FreeM.countQueries_lift,
      FreeM.eval_lift, List.length_cons]
    by_cases h1 : oracle (.le x p) <;> by_cases h2 : oracle (.le p x) <;>
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, FreeM.countQueries_bind,
        FreeM.countQueries_lift, FreeM.eval_lift, FreeM.countQueries_pure] <;>
      omega

/-- The median of a group of `xs.length + 1` elements costs at most
`mergeSortCountBound (xs.length + 1)` comparisons. -/
theorem groupMedian_countQueries_le (oracle : {ι : Type} → LEQuery α ι → ι) (x : α)
    (xs : List α) :
    (groupMedian x xs).countQueries oracle ≤ mergeSortCountBound (xs.length + 1) := by
  simp only [groupMedian, FreeM.countQueries_bind, FreeM.countQueries_pure, Nat.add_zero]
  exact mergeSort_countQueries_le_countBound oracle (x :: xs)

/-- Each full group uses six comparisons. Merge sort on a possible final group of four uses
at most five, giving the uniform bound `5 * cost ≤ 6 * n + 1`. -/
theorem medians_countQueries_le (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    5 * (medians xs).countQueries oracle ≤ 6 * xs.length + 1 := by
  fun_induction medians xs with
  | case1 a b c d e rest ih =>
    simp only [FreeM.countQueries_bind, FreeM.countQueries_pure, Nat.add_zero,
      medianFive_countQueries, List.length_cons]
    omega
  | case2 x xs hn =>
    simp only [FreeM.countQueries_bind, FreeM.countQueries_pure, Nat.add_zero]
    have hg := groupMedian_countQueries_le oracle x xs
    rcases xs with _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩
    all_goals first | exact (hn _ _ _ _ _ rfl).elim |
      (simp [mergeSortCountBound_add_two] at hg ⊢; omega)
  | case3 => simp

/-- Lists of at most `selectCutoff` elements are sorted with at most `10` comparisons per
element. -/
private theorem mergeSort_countQueries_le_of_le_selectCutoff
    (oracle : {ι : Type} → LEQuery α ι → ι) {xs : List α} (h : xs.length ≤ selectCutoff) :
    (mergeSort xs).countQueries oracle ≤ 10 * xs.length := by
  calc (mergeSort xs).countQueries oracle ≤ xs.length * Nat.clog 2 xs.length :=
        mergeSort_countQueries_le oracle xs
    _ ≤ xs.length * 10 := Nat.mul_le_mul_left _ (Nat.clog_le_of_le_pow (h.trans (by decide)))
    _ = 10 * xs.length := Nat.mul_comm _ _

/-- The constant offset in the recursive branch pays for rounding the two subproblem sizes. -/
private theorem select_countQueries_bound (oracle : {ι : Type} → LEQuery α ι → ι)
    (k : ℕ) (xs : List α) :
    (select k xs).countQueries oracle ≤ max (10 * xs.length) (32 * xs.length - 64) := by
  fun_induction select k xs with
  | case1 k xs hsmall => -- short list: sort it
    simp only [FreeM.countQueries_bind, FreeM.countQueries_pure, Nat.add_zero]
    have := mergeSort_countQueries_le_of_le_selectCutoff oracle hsmall
    omega
  | case2 k xs hsmall ihM ihL ihG => -- median of medians
    have hmed := medians_countQueries_le oracle xs
    have hMlen := length_eval_medians oracle xs
    have hM : ((medians xs).eval oracle).length < xs.length := by
      simp only [selectCutoff] at hsmall; omega
    have ihM := ihM _ hM
    simp only [FreeM.countQueries_bind]
    rw [dite_eq_left hM]
    simp only [FreeM.countQueries_bind]
    rcases hp : (select ((((medians xs).eval oracle).length - 1) / 2)
      ((medians xs).eval oracle)).eval oracle with _ | p
    · simp only [FreeM.countQueries_pure, selectCutoff] at hsmall ⊢; omega
    have hpart := partition3_countQueries_le oracle p xs
    rcases hLEG : (partition3 p xs).eval oracle with ⟨L, E, G⟩
    simp only [FreeM.countQueries_bind, hLEG]
    by_cases hL : L.length ≤ selectSideBound xs.length
    · by_cases hG : G.length ≤ selectSideBound xs.length
      · have ihG := ihG _ hM L E G hG
        rw [dite_eq_left hL, dite_eq_left hG]
        simp only [selectSideBound, selectCutoff] at hL hG hsmall
        split_ifs with hk
        · have := ihL [] L G hL hk
          omega
        · simp only [FreeM.countQueries_pure]; omega
        · omega
      · rw [dite_eq_left hL, dite_eq_right hG]
        simp only [FreeM.countQueries_pure, selectCutoff] at hsmall ⊢; omega
    · rw [dite_eq_right hL]
      simp only [FreeM.countQueries_pure, selectCutoff] at hsmall ⊢; omega

/-- Deterministic selection makes at most `32n` comparisons against every oracle. -/
theorem select_countQueries_le (oracle : {ι : Type} → LEQuery α ι → ι) (k : ℕ) (xs : List α) :
    (select k xs).countQueries oracle ≤ 32 * xs.length := by
  have := select_countQueries_bound oracle k xs
  omega

/-- **Linear comparison bound for selection**, as a query upper bound: on lists of length at most
`n`, `select k` makes at most `32 * n` comparisons for every oracle. -/
theorem select_upperBound (k : ℕ) : UpperBound (select (α := α) k) List.length (32 * ·) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.mul_le_mul_left 32 h)
    fun oracle xs => select_countQueries_le oracle k xs

end Cslib.Query
