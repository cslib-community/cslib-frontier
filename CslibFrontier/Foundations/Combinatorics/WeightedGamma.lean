/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List.PrefixFree
public import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Elias gamma codes for weighted sequences

Positive integers at distinct positive ranks admit a short concatenation of Elias gamma codes.
The sum of their code lengths is at most eight times the square root of twice their total
rank-weighted mass. Dividing every entry by four halves the square-root bound, while the
discarded low digits cost at most four bits per occupied rank.
-/

public section

namespace Cslib.BitString

open Finset

private theorem card_sq_le_two_mul_sum_succ (s : Finset ℕ) :
    s.card ^ 2 ≤ 2 * ∑ i ∈ s, (i + 1) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hnot : a ∉ s := fun h => Nat.lt_irrefl _ (ha a h)
    have hcard : s.card ≤ a := by
      simpa using Finset.card_le_card (t := range a) (fun i hi => mem_range.mpr (ha i hi))
    rw [card_insert_of_notMem hnot, sum_insert hnot]
    nlinarith

/-- The gamma words of positive entries at distinct ranks have total length
`O(√N)`, where `N` is the sum of the entries times their one-based ranks. -/
theorem sum_length_eliasGamma_le (s : Finset ℕ) (x : ℕ → ℕ) (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, (eliasGamma (x i)).length ≤ 8 * Nat.sqrt (2 * ∑ i ∈ s, (i + 1) * x i) := by
  classical
  generalize hN : ∑ i ∈ s, (i + 1) * x i = N
  induction N using Nat.strong_induction_on generalizing s x with
  | ind N ih =>
    have hmass : ∑ i ∈ s, (i + 1) ≤ N := by
      rw [← hN]
      exact sum_le_sum fun i hi => Nat.le_mul_of_pos_right _ (hx i hi)
    have hcard : s.card ≤ Nat.sqrt (2 * N) :=
      Nat.le_sqrt'.mpr ((card_sq_le_two_mul_sum_succ s).trans (by omega))
    by_cases hz : N = 0
    · have hempty : s = ∅ := Finset.card_eq_zero.mp (by simpa [hz] using hcard)
      simp [hempty, hz]
    let t := s.filter (fun i => 4 ≤ x i)
    let y := fun i => x i / 4
    let M := ∑ i ∈ t, (i + 1) * y i
    have hM : 4 * M ≤ N := by
      rw [← hN, show 4 * M = ∑ i ∈ t, 4 * ((i + 1) * y i) by rw [← mul_sum]]
      calc
        _ ≤ ∑ i ∈ t, (i + 1) * x i := by
          apply sum_le_sum
          intro i _
          rw [mul_left_comm]
          exact Nat.mul_le_mul_left _ (by dsimp [y]; omega)
        _ ≤ ∑ i ∈ s, (i + 1) * x i :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; omega)
    have hsmall := ih M (by omega) t y (fun i hi => by
      have := (mem_filter.mp hi).2
      dsimp [y]
      omega) rfl
    have hsqrt : 2 * Nat.sqrt (2 * M) ≤ Nat.sqrt (2 * N) := by
      apply Nat.le_sqrt'.mpr
      have := Nat.sqrt_le' (2 * M)
      nlinarith
    have hcost : ∑ i ∈ s, (eliasGamma (x i)).length ≤
        4 * s.card + ∑ i ∈ t, (eliasGamma (y i)).length := by
      rw [show 4 * s.card = ∑ _ ∈ s, 4 by simp [mul_comm], sum_filter, ← sum_add_distrib]
      apply sum_le_sum
      intro i hi
      by_cases h4 : 4 ≤ x i
      · have hlog := Nat.log_div_base_pow 2 (x i) 2
        simp only [h4, ite_true, length_eliasGamma, y]
        norm_num at hlog
        omega
      · have hlog : Nat.log 2 (x i) < 2 :=
          Nat.log_lt_of_lt_pow (hx i hi).ne' (by omega)
        simp [h4, length_eliasGamma]
        omega
    omega

end Cslib.BitString
