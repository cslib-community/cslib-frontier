/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.Sort.Merge.Lemmas
public import CslibFrontier.Algorithms.Lean.Query.Sort.Merge.CountBound
-- `import all` only for functional induction on `List.mergeM` and `List.mergeSortM`, whose bodies
-- CSLib does not expose.
import all Cslib.Algorithms.Lean.Sort.Merge

/-!
# Query counts of merge sort with any comparator

CSLib bounds the query complexity of `Cslib.Query.mergeSort`, which compares elements using
`Cslib.Query.LEQuery.ask` (`≤` in the oracle's order). Clients that sort by a key, or via another
query monad `FreeM F`, call `List.mergeM` and `List.mergeSortM` with their own monadic comparator
`le : α → α → FreeM F Bool`. This file shows that evaluating those calls against an `oracle` agrees
with `List.merge` and `List.mergeSort`, and proves that whenever `le` uses at most one query per
comparison, merging makes at most `xs.length + ys.length - 1` (hence `xs.length + ys.length`)
queries and merge sort makes at most `mergeSortCountBound xs.length` (hence `n * ⌈log₂ n⌉`) queries.

## Main results

* `Cslib.Query.eval_mergeM`, `Cslib.Query.eval_mergeSortM`: evaluation of custom-comparator
  `List.mergeM` and `List.mergeSortM` matches pure `List.merge` and `List.mergeSort`.
* `Cslib.Query.mergeM_countQueries_le_sub_one`, `Cslib.Query.mergeM_countQueries_le`: custom
  comparator merge makes at most `xs.length + ys.length - 1` (and `xs.length + ys.length`)
  queries.
* `Cslib.Query.mergeSortM_countQueries_le_countBound`, `Cslib.Query.mergeSortM_countQueries_le`:
  custom-comparator merge sort makes at most `mergeSortCountBound xs.length` (and `n * ⌈log₂ n⌉`)
  queries.
-/

public section

namespace Cslib.Query

open Cslib.FreeM

variable {F : Type → Type*} {α : Type}

/-- Evaluating `List.mergeM` against an `oracle` equals pure `List.merge` using the oracle's
comparison answer. -/
@[simp] theorem eval_mergeM (oracle : {ι : Type} → F ι → ι) (le : α → α → FreeM F Bool)
    (xs ys : List α) :
    (List.mergeM xs ys le).eval oracle = xs.merge ys (fun x y => (le x y).eval oracle) :=
  Id.pure_injective <| by
    simp [(FreeM.isMonadHom_pure_eval oracle).map_listMergeM xs ys]

/-- Evaluating `List.mergeSortM` against an `oracle` equals pure `List.mergeSort` using the
oracle's comparison answer. -/
@[simp] theorem eval_mergeSortM (oracle : {ι : Type} → F ι → ι) (le : α → α → FreeM F Bool)
    (xs : List α) :
    (List.mergeSortM xs le).eval oracle = xs.mergeSort (fun x y => (le x y).eval oracle) :=
  Id.pure_injective <| by
    simp [(FreeM.isMonadHom_pure_eval oracle).map_listMergeSortM xs]

/-- Merging with a comparator that makes at most one query per call makes at most
`xs.length + ys.length - 1` queries. -/
theorem mergeM_countQueries_le_sub_one (oracle : {ι : Type} → F ι → ι)
    (xs ys : List α) (le : α → α → FreeM F Bool)
    (hle : ∀ x y, (le x y).countQueries oracle ≤ 1) :
    (List.mergeM xs ys le).countQueries oracle ≤ xs.length + ys.length - 1 := by
  induction xs, ys using List.mergeM.induct (α := α) with
  | case1 ys => simp
  | case2 xs => simp
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

/-- Merging with a comparator that makes at most one query per call makes at most
`xs.length + ys.length` queries. -/
theorem mergeM_countQueries_le (oracle : {ι : Type} → F ι → ι)
    (xs ys : List α) (le : α → α → FreeM F Bool)
    (hle : ∀ x y, (le x y).countQueries oracle ≤ 1) :
    (List.mergeM xs ys le).countQueries oracle ≤ xs.length + ys.length :=
  (mergeM_countQueries_le_sub_one oracle xs ys le hle).trans (Nat.sub_le _ 1)

/-- The sharper recurrence `mergeSortCountBound n` never exceeds `n * ⌈log₂ n⌉`. -/
theorem mergeSortCountBound_le_mul_clog (n : ℕ) :
    mergeSortCountBound n ≤ n * Nat.clog 2 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | k
    · simp
    · simp
    · have hclog : Nat.clog 2 ((k + 3) / 2) + 1 = Nat.clog 2 (k + 2) :=
        (Nat.clog_of_one_lt (by omega : 1 < 2) (by omega : 2 ≤ k + 2)).symm
      have hceil : Nat.clog 2 ((k + 3) / 2) + 1 ≤ Nat.clog 2 (k + 2) := hclog.le
      have hfloor : Nat.clog 2 ((k + 2) / 2) + 1 ≤ Nat.clog 2 (k + 2) :=
        (Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1).trans hceil
      have hpart (m : ℕ) (hm : m < k + 2) (hl : Nat.clog 2 m + 1 ≤ Nat.clog 2 (k + 2)) :
          mergeSortCountBound m + m ≤ m * Nat.clog 2 (k + 2) :=
        (Nat.add_le_add_right (ih m hm) m).trans
          (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hl)
      have h1 := hpart ((k + 3) / 2) (by omega) hceil
      have h2 := hpart ((k + 2) / 2) (by omega) hfloor
      rw [mergeSortCountBound_add_two]
      have hadd : (k + 3) / 2 * Nat.clog 2 (k + 2) + (k + 2) / 2 * Nat.clog 2 (k + 2) =
          (k + 2) * Nat.clog 2 (k + 2) := by
        rw [← Nat.add_mul, show (k + 3) / 2 + (k + 2) / 2 = k + 2 by omega]
      rw [show k + 1 + 1 = k + 2 by omega]
      omega

/-- Merge sort with a comparator that makes at most one query per call stays within
`mergeSortCountBound xs.length`. -/
theorem mergeSortM_countQueries_le_countBound (oracle : {ι : Type} → F ι → ι)
    (xs : List α) (le : α → α → FreeM F Bool)
    (hle : ∀ x y, (le x y).countQueries oracle ≤ 1) :
    (List.mergeSortM xs le).countQueries oracle ≤ mergeSortCountBound xs.length := by
  induction xs using List.mergeSortM.induct (α := α) with
  | case1 => simp
  | case2 x => simp
  | case3 x y zs halves ih_l ih_r =>
    subst halves
    simp only [List.splitInTwo_fst, List.splitInTwo_snd] at ih_l ih_r
    simp only [List.mergeSortM, List.splitInTwo_fst, List.splitInTwo_snd, countQueries_bind,
      eval_mergeSortM]
    have hml := mergeM_countQueries_le_sub_one oracle
      ((x :: y :: zs).split.1.mergeSort fun a b => (le a b).eval oracle)
      ((x :: y :: zs).split.2.mergeSort fun a b => (le a b).eval oracle)
      le hle
    rw [List.length_mergeSort, List.length_mergeSort,
      List.split_fst_length_eq, List.split_snd_length_eq] at hml
    rw [List.split_fst_length_eq] at ih_l
    rw [List.split_snd_length_eq] at ih_r
    simp only [List.length_cons] at ih_l ih_r hml ⊢
    rw [show zs.length + 1 + 1 + 1 = zs.length + 3 by omega] at ih_l hml
    rw [show zs.length + 1 + 1 = zs.length + 2 by omega] at ih_r hml ⊢
    rw [mergeSortCountBound_add_two]
    omega

/-- Merge sort with a comparator that makes at most one query per call makes at most
`n * ⌈log₂ n⌉` queries on a list of length `n`. -/
theorem mergeSortM_countQueries_le (oracle : {ι : Type} → F ι → ι)
    (xs : List α) (le : α → α → FreeM F Bool)
    (hle : ∀ x y, (le x y).countQueries oracle ≤ 1) :
    (List.mergeSortM xs le).countQueries oracle ≤ xs.length * Nat.clog 2 xs.length :=
  (mergeSortM_countQueries_le_countBound oracle xs le hle).trans
    (mergeSortCountBound_le_mul_clog xs.length)

end Cslib.Query
