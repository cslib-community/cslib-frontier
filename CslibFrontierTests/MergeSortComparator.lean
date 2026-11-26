/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.Query.Sort.Merge.CountBound

/-!
# Tests for `List.mergeM` and `List.mergeSortM` Custom-Comparator Query Bounds
-/

public section

namespace CslibFrontierTests.MergeSortComparator

open Cslib Cslib.Query Cslib.FreeM

/-- One-query comparator ordering pairs by their second coordinate via `LEQuery ℕ`. -/
@[expose] def cmpSnd (x y : ℕ × ℕ) : FreeM (LEQuery ℕ) Bool :=
  LEQuery.ask x.2 y.2

private def natOracle : {ι : Type} → LEQuery ℕ ι → ι :=
  LEQuery.oracleOf (fun a b => decide (a ≤ b))

private theorem cmpSnd_count (x y : ℕ × ℕ) :
    (cmpSnd x y).countQueries natOracle ≤ 1 := by
  simp [cmpSnd]

example :
    let m : FreeM (LEQuery ℕ) (List (ℕ × ℕ)) :=
      List.mergeSortM [(1, 30), (2, 10), (3, 20), (4, 10)] cmpSnd
    eval natOracle (List.mergeSortM ([] : List (ℕ × ℕ)) cmpSnd) = [] ∧
      countQueries natOracle (List.mergeSortM ([] : List (ℕ × ℕ)) cmpSnd) ≤ 0 ∧
      eval natOracle (List.mergeSortM [(1, 5)] cmpSnd) = [(1, 5)] ∧
      countQueries natOracle (List.mergeSortM [(1, 5)] cmpSnd) ≤ 0 ∧
      eval natOracle (List.mergeSortM [(1, 10), (2, 10), (3, 20)] cmpSnd) =
        [(1, 10), (2, 10), (3, 20)] ∧
      countQueries natOracle (List.mergeSortM [(1, 10), (2, 10), (3, 20)] cmpSnd) ≤
        mergeSortCountBound 3 ∧
      eval natOracle (List.mergeSortM [(1, 30), (2, 10)] cmpSnd) = [(2, 10), (1, 30)] ∧
      (m.eval natOracle).Perm [(1, 30), (2, 10), (3, 20), (4, 10)] ∧
      m.eval natOracle = [(2, 10), (4, 10), (3, 20), (1, 30)] ∧
      m.countQueries natOracle ≤ mergeSortCountBound 4 ∧
      m.countQueries natOracle ≤ 4 * Nat.clog 2 4 ∧
      countQueries natOracle (List.mergeM [(2, 10), (3, 20)] [(4, 10), (1, 30)] cmpSnd) ≤
        2 + 2 - 1 := by
  have h2 : [(1, 30), (2, 10)].mergeSort (fun x y => decide (x.2 ≤ y.2)) = [(2, 10), (1, 30)] := by
    rw [show [(1, 30), (2, 10)] = [(1, 30)] ++ [(2, 10)] from rfl,
      List.mergeSort_append [(1, 30)] [(2, 10)] (by decide) (by decide)]
    simp
  have h3 : [(1, 10), (2, 10), (3, 20)].mergeSort (fun x y => decide (x.2 ≤ y.2)) =
      [(1, 10), (2, 10), (3, 20)] := by
    rw [show [(1, 10), (2, 10), (3, 20)] = [(1, 10), (2, 10)] ++ [(3, 20)] from rfl,
      List.mergeSort_append [(1, 10), (2, 10)] [(3, 20)] (by decide) (by decide),
      show [(1, 10), (2, 10)] = [(1, 10)] ++ [(2, 10)] from rfl,
      List.mergeSort_append [(1, 10)] [(2, 10)] (by decide) (by decide)]
    simp
  refine ⟨by simp,
    (mergeSortM_countQueries_le_countBound natOracle _ cmpSnd cmpSnd_count).trans_eq
      mergeSortCountBound_zero,
    by simp,
    (mergeSortM_countQueries_le_countBound natOracle _ cmpSnd cmpSnd_count).trans_eq
      mergeSortCountBound_one,
    ?_,
    mergeSortM_countQueries_le_countBound natOracle _ cmpSnd cmpSnd_count,
    ?_, ?_, ?_,
    mergeSortM_countQueries_le_countBound natOracle _ cmpSnd cmpSnd_count,
    mergeSortM_countQueries_le natOracle _ cmpSnd cmpSnd_count,
    mergeM_countQueries_le_sub_one natOracle _ _ cmpSnd cmpSnd_count⟩
  · simpa only [eval_mergeSortM, cmpSnd, natOracle, LEQuery.eval_ask, LEQuery.oracleOf_le] using h3
  · simpa only [eval_mergeSortM, cmpSnd, natOracle, LEQuery.eval_ask, LEQuery.oracleOf_le] using h2
  · simp only [eval_mergeSortM]
    exact List.mergeSort_perm _ _
  · simp only [eval_mergeSortM, cmpSnd, natOracle, LEQuery.eval_ask, LEQuery.oracleOf_le]
    rw [show [(1, 30), (2, 10), (3, 20), (4, 10)] = [(1, 30), (2, 10)] ++ [(3, 20), (4, 10)]
        from rfl,
      List.mergeSort_append [(1, 30), (2, 10)] [(3, 20), (4, 10)] (by decide) (by decide), h2,
      show [(3, 20), (4, 10)] = [(3, 20)] ++ [(4, 10)] from rfl,
      List.mergeSort_append [(3, 20)] [(4, 10)] (by decide) (by decide)]
    simp

end CslibFrontierTests.MergeSortComparator
