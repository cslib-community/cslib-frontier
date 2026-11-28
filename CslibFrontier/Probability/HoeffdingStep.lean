/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import CslibFrontier.Probability.PMF.ToMeasure
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.Ring

/-!
# Hoeffding's centered moment-generating function bound on `PMF`s

If a real score `g : α → ℝ` lies in `[a, b]` on the support of a discrete distribution `q : PMF α`,
its centered exponential moment at any `t : ℝ` is at most `exp (t² (b - a)² / 8)`. Equip `α`
with the discrete measurable space `⊤` so the support bound holds almost everywhere for
`q.toMeasure`. This gives the hypotheses of Mathlib's
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` without
requiring `[Fintype α]` or a caller-supplied `[MeasurableSpace α]`.

## Main results

* `Cslib.Probability.PMF.tsum_mul_exp_sub_mean_le`: Hoeffding's centered moment-generating function
  bound on arbitrary `PMF`s, written with `tsum` and `ENNReal.ofReal`.
* `Cslib.Probability.PMF.sum_mul_exp_sub_mean_le`: finite-type specialization written with ordinary
  `Finset` sums in `ℝ`.

## References

* [W. Hoeffding, *Probability inequalities for sums of bounded random
  variables*][Hoeffding1963]
-/

public section

namespace Cslib.Probability.PMF

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

variable {α : Type*}

/-- **Hoeffding's lemma** for a discrete `PMF`: if `g` takes values in `[a, b]` on `q.support`,
its centered exponential moment at `t` is at most `exp (t² (b - a)² / 8)`. -/
theorem tsum_mul_exp_sub_mean_le (q : PMF α) (g : α → ℝ) {a b : ℝ}
    (hg : ∀ x ∈ q.support, g x ∈ Set.Icc a b) (t : ℝ) :
    ∑' x, q x * ENNReal.ofReal (Real.exp (t * (g x - ∑' y, (q y).toReal * g y))) ≤
      ENNReal.ofReal (Real.exp (t ^ 2 * (b - a) ^ 2 / 8)) := by
  let _ : MeasurableSpace α := ⊤
  have hmeas : Measurable g := fun _ _ => trivial
  have hsupport : ∀ᵐ x ∂q.toMeasure, x ∈ q.support := by
    rw [ae_iff]
    exact (q.toMeasure_apply_eq_zero_iff (s := q.supportᶜ) (by trivial)).mpr
      (Set.disjoint_left.2 fun _ hx hxc => hxc hx)
  have hbound := hsupport.mono hg
  have hgint : Integrable g q.toMeasure :=
    Integrable.of_mem_Icc a b hmeas.aemeasurable hbound
  have hsub := hasSubgaussianMGF_of_mem_Icc (μ := q.toMeasure) hmeas.aemeasurable hbound
  have hmean : ∫ x, g x ∂q.toMeasure = ∑' y, (q y).toReal * g y := by
    simp only [_root_.PMF.integral_eq_tsum q g hgint, smul_eq_mul]
  rw [← hmean, ← _root_.PMF.lintegral_toMeasure q (fun _ _ => trivial),
    ← ofReal_integral_eq_lintegral_ofReal (hsub.integrable_exp_mul t)
      (ae_of_all _ fun x => (Real.exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ((hsub.mgf_le t).trans_eq (congrArg Real.exp ?_))
  simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnNorm, Real.norm_eq_abs, NNReal.coe_ofNat,
    div_pow, sq_abs]
  ring

/-- Finite-type specialization of `tsum_mul_exp_sub_mean_le`, written with ordinary `Finset`
sums. -/
theorem sum_mul_exp_sub_mean_le [Fintype α] (q : PMF α) (g : α → ℝ) {a b : ℝ}
    (hg : ∀ x ∈ q.support, g x ∈ Set.Icc a b) (t : ℝ) :
    ∑ x, (q x).toReal * Real.exp (t * (g x - ∑ y, (q y).toReal * g y)) ≤
      Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by
  have h := tsum_mul_exp_sub_mean_le q g hg t
  rw [tsum_fintype, tsum_fintype] at h
  rw [← ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
  refine (Finset.sum_congr rfl fun x _ => ?_).trans_le h
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (q.apply_ne_top x)]

end Cslib.Probability.PMF
