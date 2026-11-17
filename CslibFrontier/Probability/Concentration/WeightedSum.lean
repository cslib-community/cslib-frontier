/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.BoundedDifferences
import CslibFrontier.Probability.PMF.Event
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.Linarith

/-!
# Weighted sums of centered bounded independent scores

Independent centered scores with oscillation at most two have the same elementary
sub-Gaussian tail bound as independent signs. The coordinate laws need not be uniform or
identical. The variance proxy is any upper bound for the sum of the squared weights.

## Main results

* `Cslib.Probability.PMF.pi_abs_sum_mul_ge_le_of_centered`: a two-sided Hoeffding bound.
-/

public section

open Finset ProbabilityTheory MeasureTheory

namespace Cslib.Probability.PMF

variable {ι : Type*} [Fintype ι] {α : ι → Type*}
  [∀ i, Fintype (α i)]

/-- A weighted sum of independent centered scores of oscillation at most two has a
sub-Gaussian tail with any variance proxy bounding the sum of the squared weights. -/
theorem pi_abs_sum_mul_ge_le_of_centered (p : ∀ i, PMF (α i))
    (score : ∀ i, α i → ℝ) (a : ι → ℝ)
    (hmean : ∀ i, ∑ x, (p i x).toReal * score i x = 0)
    (hosc : ∀ i x y, |score i x - score i y| ≤ 2)
    {V ε : ℝ} (hV : 0 ≤ V) (ha : ∑ i, a i ^ 2 ≤ V) (hε : 0 ≤ ε) :
    ((pi p).toOuterMeasure {x | ε ≤ |∑ i, a i * score i (x i)|}).toReal ≤
      2 * Real.exp (-ε ^ 2 / (2 * V)) := by
  classical
  let (i : ι) : MeasurableSpace (α i) := ⊤
  let f : (∀ i, α i) → ℝ := fun x => ∑ i, a i * score i (x i)
  have hf : HasBoundedDifferences f (fun i => 2 * |a i|) := by
    dsimp only [f]
    apply hasBoundedDifferences_sum (score := fun i x => a i * score i x)
    intro i x y
    rw [← mul_sub, abs_mul, mul_comm 2]
    exact mul_le_mul_of_nonneg_left (hosc i x y) (abs_nonneg _)
  have hm : ∑ x, (pi p x).toReal * f x = 0 := by
    dsimp only [f]
    rw [sum_pi_mul_sum p (fun i x => a i * score i x)]
    simp only [mul_left_comm _ (a _), ← mul_sum, hmean, mul_zero, sum_const_zero]
  have hs : HasSubgaussianMGF f ⟨V, hV⟩ (pi p).toMeasure := {
    integrable_exp_mul := fun _ => Integrable.of_finite
    mgf_le := fun t => by
      rw [mgf, _root_.PMF.integral_eq_sum]
      have h := hf.sum_pi_mul_exp_le p t
      simp only [hm, sub_zero] at h
      apply h.trans
      apply Real.exp_le_exp.mpr
      change t ^ 2 * (∑ i, (2 * |a i|) ^ 2) / 8 ≤ V * t ^ 2 / 2
      simp only [mul_pow, sq_abs, ← mul_sum]
      nlinarith [mul_le_mul_of_nonneg_left ha (sq_nonneg t)] }
  have hu := hs.measure_ge_le hε
  have hl := hs.neg.measure_ge_le hε
  rw [measureReal_def, _root_.PMF.toMeasure_apply_eq_toOuterMeasure_apply _
    ((Set.to_countable _).measurableSet)] at hu hl
  have hevent : {x : ∀ i, α i | ε ≤ (-f) x} = {x | f x ≤ 0 - ε} := by
    ext x
    simp only [Set.mem_ofPred_eq, Pi.neg_apply]
    constructor <;> intro h <;> linarith
  rw [hevent] at hl
  have hb := toOuterMeasure_abs_sub_ge_toReal_le (pi p) f 0 ε
  change ((pi p).toOuterMeasure {ω | ε ≤ f ω}).toReal ≤
    Real.exp (-ε ^ 2 / (2 * V)) at hu
  change ((pi p).toOuterMeasure {x | f x ≤ 0 - ε}).toReal ≤
    Real.exp (-ε ^ 2 / (2 * V)) at hl
  simp only [sub_zero, zero_add] at hb
  exact hb.trans (by linarith)

end Cslib.Probability.PMF
