/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, sign approximation)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Sign.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Squared-error scores for finite sign tests

Approximate values within `1 / (4 * (m + 1))` of their true signs give a score
separated from zero by at least one half. The score is positive exactly when
all `m` target signs agree with the true signs. The empty family is included.

Adapted from `RootLabelScore` and `RationalSignMargin` in lean-canny at commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. The larger tolerance still gives
the same score margin and permits fewer repetitions of the dyadic product.
-/

public section

namespace SignType

/-- Subtract four times the total squared distance from the target signs from one. -/
@[expose] noncomputable def labelScore {m : ℕ} (a : Fin m → ℝ) (target : Fin m → SignType) : ℝ :=
  1 - 4 * ∑ i, (a i - (target i : ℝ)) ^ 2

private theorem one_le_abs_sub_of_ne (s t : SignType) (h : s ≠ t) :
    (1 : ℝ) ≤ |(s : ℝ) - (t : ℝ)| := by
  cases s <;> cases t <;> norm_num at *

/-- With uniformly accurate approximations, the score is at least one half
on agreement and at most minus one half on mismatch. Its sign characterizes agreement. -/
theorem labelScore_margin {m : ℕ} (a : Fin m → ℝ) (s target : Fin m → SignType)
    (ha : ∀ i, |a i - (s i : ℝ)| ≤ (4 * ((m : ℝ) + 1))⁻¹) :
    ((1 : ℝ) / 2 ≤ labelScore a target ∨ labelScore a target ≤ -(1 : ℝ) / 2) ∧
      (0 < labelScore a target ↔ ∀ i, s i = target i) := by
  let δ : ℝ := (4 * ((m : ℝ) + 1))⁻¹
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hm : 0 ≤ (m : ℝ) := by positivity
  have hδ₁ : δ ≤ (1 : ℝ) / 4 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) (show (4 : ℝ) ≤ 4 * ((m : ℝ) + 1) by linarith)
  by_cases hmatch : ∀ i, s i = target i
  · have hmul : (m : ℝ) * δ ≤ (1 : ℝ) / 4 := by
      dsimp only [δ]
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      linarith
    have hsum : (∑ i, (a i - (target i : ℝ)) ^ 2) ≤ (1 : ℝ) / 16 := by
      calc
        _ ≤ ∑ _i : Fin m, δ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hi := pow_le_pow_left₀ (abs_nonneg _) (ha i) 2
          simpa only [hmatch i, sq_abs, δ] using hi
        _ = ((m : ℝ) * δ) * δ := by simp [pow_two, mul_assoc]
        _ ≤ (1 : ℝ) / 4 * (1 / 4) := mul_le_mul hmul hδ₁ hδ (by norm_num)
        _ = _ := by norm_num
    have hscore : (1 : ℝ) / 2 ≤ labelScore a target := by
      unfold labelScore
      linarith
    exact ⟨Or.inl hscore, ⟨fun _ => hmatch, fun _ => by linarith⟩⟩
  · obtain ⟨i, hi⟩ := not_forall.mp hmatch
    have hgap := one_le_abs_sub_of_ne (s i) (target i) hi
    have htri := abs_sub_le (s i : ℝ) (a i) (target i : ℝ)
    rw [abs_sub_comm (s i : ℝ) (a i)] at htri
    have hdist : (3 : ℝ) / 4 ≤ |a i - (target i : ℝ)| := by
      have he : |a i - (s i : ℝ)| ≤ δ := ha i
      linarith
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) hdist 2
    rw [sq_abs] at hsq
    have hsum : (a i - (target i : ℝ)) ^ 2 ≤ ∑ j, (a j - (target j : ℝ)) ^ 2 :=
      Finset.single_le_sum (f := fun j : Fin m => (a j - (target j : ℝ)) ^ 2)
        (fun j _ => sq_nonneg (a j - (target j : ℝ))) (Finset.mem_univ i)
    have hscore : labelScore a target ≤ -(1 : ℝ) / 2 := by
      unfold labelScore
      linarith
    exact ⟨Or.inr hscore, ⟨fun h => by linarith, fun h => (hmatch h).elim⟩⟩

end SignType
