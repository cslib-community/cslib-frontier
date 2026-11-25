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
import CslibFrontier.Probability.PMF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Hoeffding's centered moment-generating function bound on `PMF`s

If a real score `g : α → ℝ` lies in `[a, b]` on the support of a discrete distribution `q : PMF α`,
its centered exponential moment at any `t : ℝ` is at most `exp (t² (b - a)² / 8)`. Clamping `g`
into `[a, b]` outside `q.support` and equipping `α` with the discrete measurable space `⊤` reduces
the estimate to Mathlib's `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` without requiring
`[Fintype α]` or a caller-supplied `[MeasurableSpace α]`.

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

/-- Clamp `g` into `[a, b]` outside `q.support` so boundedness holds everywhere without changing
values on `q.support`. -/
private noncomputable def clampToSupport (q : PMF α) (g : α → ℝ) (a : ℝ) (x : α) : ℝ :=
  open Classical in if x ∈ q.support then g x else a

private theorem clampToSupport_mem_Icc {q : PMF α} {g : α → ℝ} {a b : ℝ}
    (hg : ∀ x ∈ q.support, g x ∈ Set.Icc a b) (x : α) :
    clampToSupport q g a x ∈ Set.Icc a b := by
  obtain ⟨x₀, hx₀⟩ := q.support_nonempty
  unfold clampToSupport
  split_ifs with hx
  exacts [hg x hx, ⟨le_rfl, (hg x₀ hx₀).1.trans (hg x₀ hx₀).2⟩]

private theorem tsum_toReal_mul_clampToSupport (q : PMF α) (g : α → ℝ) (a : ℝ) :
    (∑' x, (q x).toReal * clampToSupport q g a x) = ∑' x, (q x).toReal * g x := by
  refine tsum_congr fun x => ?_
  unfold clampToSupport
  split_ifs with hx
  · rfl
  · simp [(q.apply_eq_zero_iff x).mpr hx]

/-- **Hoeffding's lemma** for a discrete `PMF`: if `g` takes values in `[a, b]` on `q.support`,
its centered exponential moment at `t` is at most `exp (t² (b - a)² / 8)`. -/
theorem tsum_mul_exp_sub_mean_le (q : PMF α) (g : α → ℝ) {a b : ℝ}
    (hg : ∀ x ∈ q.support, g x ∈ Set.Icc a b) (t : ℝ) :
    ∑' x, q x * ENNReal.ofReal (Real.exp (t * (g x - ∑' y, (q y).toReal * g y))) ≤
      ENNReal.ofReal (Real.exp (t ^ 2 * (b - a) ^ 2 / 8)) := by
  let _ : MeasurableSpace α := ⊤
  set g' := clampToSupport q g a
  have hg' : ∀ x, g' x ∈ Set.Icc a b := clampToSupport_mem_Icc hg
  have hmeas : Measurable g' := fun _ _ => trivial
  have hint_g' : Integrable g' q.toMeasure :=
    Integrable.of_mem_Icc a b hmeas.aemeasurable (ae_of_all _ hg')
  have hmean : ∫ x, g' x ∂q.toMeasure = ∑' y, (q y).toReal * g y := by
    rw [_root_.PMF.integral_eq_tsum q g' hint_g']
    exact tsum_toReal_mul_clampToSupport q g a
  have hsub := hasSubgaussianMGF_of_mem_Icc (μ := q.toMeasure) hmeas.aemeasurable
    (ae_of_all _ hg')
  have hmgf := hsub.mgf_le t
  have hint_exp : Integrable (fun x => Real.exp (t * (g' x - ∫ y, g' y ∂q.toMeasure)))
      q.toMeasure := hsub.integrable_exp_mul t
  rw [mgf, _root_.PMF.integral_eq_tsum q _ hint_exp] at hmgf
  simp only [smul_eq_mul, hmean] at hmgf
  have htsum_eq :
      (∑' x, q x * ENNReal.ofReal (Real.exp (t * (g x - ∑' y, (q y).toReal * g y)))) =
        ENNReal.ofReal
          (∑' x, (q x).toReal * Real.exp (t * (g' x - ∑' y, (q y).toReal * g y))) := by
    set B := Real.exp (|t| * (|a| + |b| + |∑' y, (q y).toReal * g y|))
    have M_le (x : α) : Real.exp (t * (g' x - ∑' y, (q y).toReal * g y)) ≤ B := by
      rw [Real.exp_le_exp]
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)
      have hgx : |g' x| ≤ |a| + |b| := abs_le.mpr
        ⟨by linarith [(hg' x).1, neg_abs_le a, abs_nonneg b],
          by linarith [(hg' x).2, le_abs_self b, abs_nonneg a]⟩
      linarith [abs_sub (g' x) (∑' y, (q y).toReal * g y)]
    have hsumm :
        Summable fun x => (q x).toReal * Real.exp (t * (g' x - ∑' y, (q y).toReal * g y)) :=
      ((summable_toReal q).mul_right B).of_nonneg_of_le
        (fun _ => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
        fun x => mul_le_mul_of_nonneg_left (M_le x) ENNReal.toReal_nonneg
    rw [ENNReal.ofReal_tsum_of_nonneg
      (fun _ => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) hsumm]
    refine tsum_congr fun x => ?_
    classical
    by_cases hx : x ∈ q.support
    · have hgx : g' x = g x := ite_eq_left hx
      rw [hgx, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (_root_.PMF.apply_ne_top q x)]
    · simp [(q.apply_eq_zero_iff x).mpr hx]
  rw [htsum_eq]
  refine ENNReal.ofReal_le_ofReal (hmgf.trans_eq (congrArg Real.exp ?_))
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
