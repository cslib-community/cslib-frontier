/-
Copyright (c) 2026 Samuel Schlesinger, Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Sums of indicators over lists

Indicator sums over `List.range n` reduce to the finite-sum indicator API through
`List.sum_map_range`: the indicator of a single index sums to whether the index is in range
(`List.sum_map_range_ite_eq`). A condition that does not depend on the element comes out of the
sum (`List.sum_map_ite_and`).

## Main results

* `List.sum_map_range_ite_eq`: the indicator of `i₀` sums to `b` over `List.range n` when
  `i₀ < n`, and to `0` otherwise.
* `List.sum_map_ite_and`: a constant conjunct of an indicator comes out of the sum.
* `List.countP_range_eq_sum`: counting successful Boolean tests over a range is summing their
  zero-or-one values.
-/

public section

namespace List

/-- Counting a Boolean predicate on a range equals the finite sum of its indicator values. -/
theorem countP_range_eq_sum (n : ℕ) (f : ℕ → Bool) :
    (List.range n).countP f = ∑ j ∈ Finset.range n, (f j).toNat := by
  rw [List.countP_range_eq_card_filter, Finset.card_eq_sum_ones, Finset.sum_filter,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  cases f i <;> rfl

variable {M : Type*} [AddCommMonoid M]

/-- The indicator of a single index sums over `List.range n` to `b` when the index is below `n`,
and to `0` otherwise. -/
theorem sum_map_range_ite_eq (n i₀ : ℕ) (b : M) :
    ((List.range n).map fun i => if i = i₀ then b else 0).sum = if i₀ < n then b else 0 := by
  rw [List.sum_map_range, ← Finset.sum_range (fun i => if i = i₀ then b else 0),
    Finset.sum_ite_eq']
  simp only [Finset.mem_range]

/-- A conjunct of an indicator that does not depend on the element comes out of the sum. -/
theorem sum_map_ite_and {α : Type*} (l : List α) (P : Prop) [Decidable P] (Q : α → Prop)
    [DecidablePred Q] (b : M) :
    (l.map fun a => if P ∧ Q a then b else 0).sum =
      if P then (l.map fun a => if Q a then b else 0).sum else 0 := by
  by_cases hP : P <;> simp [hP]

end List
