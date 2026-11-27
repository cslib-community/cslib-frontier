/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.Sort.Merge.Lemmas
-- `import all` only for the functional induction principles `List.mergeM.induct` and
-- `List.mergeSortM.induct`; CSLib does not expose the bodies of these definitions.
import all Cslib.Algorithms.Lean.Sort.Merge

/-!
# A sharper comparison bound for merge sort and arbitrary comparators

CSLib bounds the comparisons of `Cslib.Query.mergeSort` by `n * ⌈log₂ n⌉`, charging
`xs.length + ys.length` comparisons to each merge. A merge of two nonempty lists in fact stops
after at most `xs.length + ys.length - 1` comparisons, because the last element is placed without
one. Moreover, clients that sort by a key or through another query monad `FreeM F` call
`List.mergeM` and `List.mergeSortM` directly with a custom monadic comparator
`le : α → α → FreeM F Bool`.

This file evaluates `List.mergeM` and `List.mergeSortM` against pure `List.merge` and
`List.mergeSort`, proves the sharper `xs.length + ys.length - 1` merge bound and
`mergeSortCountBound n` (as well as `n * ⌈log₂ n⌉`) merge-sort query bounds for any one-query
comparator, and specializes them to `Cslib.Query.merge` and `Cslib.Query.mergeSort`. For short
lists the sharper recurrence saves substantially: five elements take at most `8` comparisons rather
than `15`, which is what the median-of-medians selection algorithm pays per group of five.

## Main definitions

* `Cslib.Query.mergeSortCountBound`: the recurrence `C(n) = C(⌈n/2⌉) + C(⌊n/2⌋) + n - 1` for
  `n ≥ 2`, with `C(0) = C(1) = 0`.

## Main results

* `Cslib.Query.eval_mergeM`, `Cslib.Query.eval_mergeSortM`: evaluation of custom-comparator
  `List.mergeM` and `List.mergeSortM` agrees with `List.merge` and `List.mergeSort`.
* `Cslib.Query.mergeM_countQueries_le_sub_one`, `Cslib.Query.merge_countQueries_le_sub_one`: merging
  takes at most `xs.length + ys.length - 1` queries (for any one-query comparator, and for
  `Cslib.Query.merge`).
* `Cslib.Query.mergeSortCountBound_le_mul_clog`, `Cslib.Query.mergeSortCountBound_five`:
  `mergeSortCountBound n ≤ n * ⌈log₂ n⌉` and five elements take at most `8` comparisons.
* `Cslib.Query.mergeSortM_countQueries_le_countBound`,
  `Cslib.Query.mergeSort_countQueries_le_countBound`, `Cslib.Query.mergeSortM_countQueries_le`:
  merge sort takes at most `mergeSortCountBound n` (and `n * ⌈log₂ n⌉`) queries.

## References

* [D. E. Knuth, *The Art of Computer Programming, Volume 3: Sorting and Searching*][Knuth1998],
  Section 5.2.4.
-/

public section

namespace Cslib.Query

open Cslib.FreeM

variable {α : Type}

/-- Evaluating `List.mergeM` against an `oracle` equals pure `List.merge` using the oracle's
comparison answer. -/
@[simp] theorem eval_mergeM {F : Type → Type*} (oracle : {ι : Type} → F ι → ι)
    (xs ys : List α) (le : α → α → FreeM F Bool) :
    (List.mergeM xs ys le).eval oracle = xs.merge ys (fun x y => (le x y).eval oracle) :=
  Id.pure_injective <| by
    simp [(FreeM.isMonadHom_pure_eval oracle).map_listMergeM xs ys]

/-- Evaluating `List.mergeSortM` against an `oracle` equals pure `List.mergeSort` using the
oracle's comparison answer. -/
@[simp] theorem eval_mergeSortM {F : Type → Type*} (oracle : {ι : Type} → F ι → ι)
    (xs : List α) (le : α → α → FreeM F Bool) :
    (List.mergeSortM xs le).eval oracle = xs.mergeSort (fun x y => (le x y).eval oracle) :=
  Id.pure_injective <| by
    simp [(FreeM.isMonadHom_pure_eval oracle).map_listMergeSortM xs]

/-- Merging two lists with a comparator that makes at most one query per call makes at most
`xs.length + ys.length - 1` queries: when one list is empty no queries are made, and otherwise the
last element is placed without a query. -/
theorem mergeM_countQueries_le_sub_one {F : Type → Type*} (oracle : {ι : Type} → F ι → ι)
    (xs ys : List α) (le : α → α → FreeM F Bool)
    (hle : ∀ x y, (le x y).countQueries oracle ≤ 1) :
    (List.mergeM xs ys le).countQueries oracle ≤ xs.length + ys.length - 1 := by
  induction xs, ys using List.mergeM.induct (α := α) with
  | case1 _ | case2 _ => simp
  | case3 x xs' y ys' ih_true ih_false =>
    simp only [List.mergeM, countQueries_bind, countQueries_ite, countQueries_pure, add_zero,
      List.length_cons]
    have hxy := hle x y
    split
    · rcases xs' with _ | ⟨x', xs''⟩
      · simp; omega
      · simp only [List.length_cons] at ih_true ⊢; omega
    · rcases ys' with _ | ⟨y', ys''⟩
      · simp; omega
      · simp only [List.length_cons] at ih_false ⊢; omega

/-- Merging two lists makes at most `xs.length + ys.length - 1` comparisons. -/
theorem merge_countQueries_le_sub_one (oracle : {ι : Type} → LEQuery α ι → ι)
    (xs ys : List α) :
    (merge xs ys).countQueries oracle ≤ xs.length + ys.length - 1 :=
  mergeM_countQueries_le_sub_one oracle xs ys LEQuery.ask fun _ _ => le_rfl

/-- The comparison bound of merge sort with the sharper merge bound: `0` for at most one element,
and otherwise the bounds for the two halves plus `n - 1` for the merge. -/
def mergeSortCountBound : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => mergeSortCountBound ((n + 3) / 2) + mergeSortCountBound ((n + 2) / 2) + (n + 1)

@[simp] theorem mergeSortCountBound_zero : mergeSortCountBound 0 = 0 := by
  rw [mergeSortCountBound]

@[simp] theorem mergeSortCountBound_one : mergeSortCountBound 1 = 0 := by
  rw [mergeSortCountBound]

theorem mergeSortCountBound_add_two (n : ℕ) :
    mergeSortCountBound (n + 2) =
      mergeSortCountBound ((n + 3) / 2) + mergeSortCountBound ((n + 2) / 2) + (n + 1) := by
  rw [mergeSortCountBound]

/-- Merge sort of five elements takes at most `8` comparisons. -/
theorem mergeSortCountBound_five : mergeSortCountBound 5 = 8 := by
  simp [mergeSortCountBound_add_two]

/-- The sharper recurrence `mergeSortCountBound n` never exceeds `n * ⌈log₂ n⌉`. -/
theorem mergeSortCountBound_le_mul_clog (n : ℕ) :
    mergeSortCountBound n ≤ n * Nat.clog 2 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | k
    · simp
    · simp
    · have hceil : Nat.clog 2 ((k + 3) / 2) + 1 ≤ Nat.clog 2 (k + 2) :=
        (Nat.clog_of_one_lt Nat.one_lt_two (by omega : 2 ≤ k + 2)).symm.le
      have hpart (m : ℕ) (hm : m < k + 2) (hl : Nat.clog 2 m + 1 ≤ Nat.clog 2 (k + 2)) :
          mergeSortCountBound m + m ≤ m * Nat.clog 2 (k + 2) :=
        (Nat.add_le_add_right (ih m hm) m).trans
          (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hl)
      have h1 := hpart ((k + 3) / 2) (by omega) hceil
      have h2 := hpart ((k + 2) / 2) (by omega)
        ((Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1).trans hceil)
      have hadd : (k + 3) / 2 * Nat.clog 2 (k + 2) + (k + 2) / 2 * Nat.clog 2 (k + 2) =
          (k + 2) * Nat.clog 2 (k + 2) := by
        rw [← Nat.add_mul, show (k + 3) / 2 + (k + 2) / 2 = k + 2 by omega]
      rw [mergeSortCountBound_add_two, show k + 1 + 1 = k + 2 by omega]
      omega

/-- Merge sort with a comparator that makes at most one query per call takes at most
`mergeSortCountBound xs.length` queries. -/
theorem mergeSortM_countQueries_le_countBound {F : Type → Type*}
    (oracle : {ι : Type} → F ι → ι) (xs : List α) (le : α → α → FreeM F Bool)
    (hle : ∀ x y, (le x y).countQueries oracle ≤ 1) :
    (List.mergeSortM xs le).countQueries oracle ≤ mergeSortCountBound xs.length := by
  induction xs using List.mergeSortM.induct (α := α) with
  | case1 | case2 _ => simp
  | case3 x y zs halves ih_l ih_r =>
    subst halves
    simp only [List.mergeSortM, List.splitInTwo_fst, List.splitInTwo_snd, countQueries_bind,
      eval_mergeSortM] at ih_l ih_r ⊢
    have hml := mergeM_countQueries_le_sub_one oracle
      ((x :: y :: zs).split.1.mergeSort fun a b => (le a b).eval oracle)
      ((x :: y :: zs).split.2.mergeSort fun a b => (le a b).eval oracle) le hle
    simp only [List.length_mergeSort, List.split_fst_length_eq, List.split_snd_length_eq,
      List.length_cons] at ih_l ih_r hml ⊢
    rw [show zs.length + 1 + 1 + 1 = zs.length + 3 by omega] at ih_l hml
    rw [show zs.length + 1 + 1 = zs.length + 2 by omega] at ih_r hml ⊢
    rw [mergeSortCountBound]
    omega

/-- Merge sort takes at most `mergeSortCountBound n` comparisons on a list of length `n`. -/
theorem mergeSort_countQueries_le_countBound (oracle : {ι : Type} → LEQuery α ι → ι)
    (xs : List α) :
    (mergeSort xs).countQueries oracle ≤ mergeSortCountBound xs.length :=
  mergeSortM_countQueries_le_countBound oracle xs LEQuery.ask fun _ _ => le_rfl

/-- Merge sort with a comparator that makes at most one query per call makes at most
`n * ⌈log₂ n⌉` queries on a list of length `n`. -/
theorem mergeSortM_countQueries_le {F : Type → Type*} (oracle : {ι : Type} → F ι → ι)
    (xs : List α) (le : α → α → FreeM F Bool)
    (hle : ∀ x y, (le x y).countQueries oracle ≤ 1) :
    (List.mergeSortM xs le).countQueries oracle ≤ xs.length * Nat.clog 2 xs.length :=
  (mergeSortM_countQueries_le_countBound oracle xs le hle).trans
    (mergeSortCountBound_le_mul_clog xs.length)

end Cslib.Query
