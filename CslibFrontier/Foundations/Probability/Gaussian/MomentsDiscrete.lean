/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.Lattice.Dual
public import CslibFrontier.Foundations.Probability.Gaussian.SmoothingParameter
public import CslibFrontier.Foundations.Probability.IndependentSumNorm

import CslibFrontier.Foundations.Probability.Gaussian.ShiftBounds
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Discrete Gaussian moments on lattices

This module establishes the first and second moment bounds for discrete Gaussian distributions
on lattices and the corresponding `MemLp 2` and Bochner integral bridges. The general Hilbert-space
second-moment bound for linear combinations of independent random vectors ([MicciancioRegev2007],
Lemma 2.11) lives in `CslibFrontier.Foundations.Probability.IndependentSumNorm`.

## Main results

* `ZLattice.summable_discreteGaussian_mul_inner_sub`,
  `ZLattice.summable_discreteGaussian_mul_inner_sub_sq`: summability of directional first and
  second moments for any discrete `ℤ`-submodule at positive width.
* `ZLattice.abs_tsum_discreteGaussian_mul_inner_sub_le`,
  `ZLattice.abs_tsum_discreteGaussian_mul_inner_sub_sq_sub_le`,
  `ZLattice.abs_tsum_discreteGaussian_mul_inner_sub_le_of_smoothingParameter_le`,
  `ZLattice.abs_tsum_discreteGaussian_mul_inner_sub_sq_sub_le_of_smoothingParameter_le`:
  [MicciancioRegev2007], Lemma 4.2 (pp. 13–14), bounding directional mean and second moment
  around `s² / (2π)` in both dual-mass form (`ρ_{2/s}(L* \ {0}) ≤ ε < 1`) and
  smoothing-parameter form (`2 * η_ε(L) ≤ s`, `0 < ε < 1`).
* `ZLattice.norm_tsum_discreteGaussian_smul_sub_sq_le`,
  `ZLattice.tsum_discreteGaussian_mul_norm_sub_sq_le`,
  `ZLattice.norm_tsum_discreteGaussian_smul_sub_sq_le_of_smoothingParameter_le`,
  `ZLattice.tsum_discreteGaussian_mul_norm_sub_sq_le_of_smoothingParameter_le`:
  [MicciancioRegev2007], Lemma 4.3 (p. 14), bounding the squared norm of the mean vector and
  the expected squared norm in both dual-mass and `2 * η_ε(L) ≤ s` forms.
* `ZLattice.memLp_sub_discreteGaussian`, `ZLattice.integral_sub_discreteGaussian_eq_tsum`,
  `ZLattice.integral_norm_sub_sq_discreteGaussian_eq_tsum`: `MemLp 2` and Bochner integral
  bridges for `(discreteGaussian L s hs c).toMeasure`.

## References

* [MicciancioRegev2007], Definition 3.1 (p. 10), Lemma 4.2 (pp. 13–14), and Lemma 4.3 (p. 14) of
  the December 27, 2005 author version.

The moment bounds are provided in both dual-mass form `gaussianMass D (2 / s) 0 - 1 ≤ ε` (which
also covers `ε = 0` in dimension zero) and smoothing-parameter form
`2 * smoothingParameter L ε ≤ s` (for `0 < ε < 1`).
-/

public section

noncomputable section

open Module MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace ZLattice

section PointwiseDomination

variable {E : Type*} [NormedAddCommGroup E]

private theorem real_le_exp_three_quarters_pi_sq (r : ℝ) :
    r ≤ Real.exp (3 * Real.pi / 4 * r ^ 2) := by
  linarith [sq_nonneg r, sq_nonneg (r - 1 / 2), Real.add_one_le_exp (3 * Real.pi / 4 * r ^ 2),
    mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg r)]

private theorem sq_le_exp_three_quarters_pi_sq (r : ℝ) :
    r ^ 2 ≤ Real.exp (3 * Real.pi / 4 * r ^ 2) := by
  linarith [sq_nonneg r, Real.add_one_le_exp (3 * Real.pi / 4 * r ^ 2),
    mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg r)]

private theorem gaussianWeight_le_gaussianWeight_two_mul (s : ℝ) (x : E) :
    gaussianWeight s x ≤ gaussianWeight (2 * s) x := by
  unfold gaussianWeight
  apply Real.exp_le_exp.mpr
  by_cases hs : s = 0
  · simp [hs]
  · simp only [neg_mul, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_ne_zero hs)
      (by rw [mul_pow]; linarith [sq_nonneg s])

private theorem gaussianWeight_mul_exp_three_quarters (s : ℝ) (hs : 0 < s) (x : E) :
    Real.exp (3 * Real.pi / 4 * (‖x‖ / s) ^ 2) * gaussianWeight s x =
      gaussianWeight (2 * s) x := by
  unfold gaussianWeight
  rw [← Real.exp_add]
  congr 1
  have hs0 : s ≠ 0 := hs.ne'
  field_simp
  ring

private theorem norm_mul_gaussianWeight_le (s : ℝ) (hs : 0 < s) (x : E) :
    ‖x‖ * gaussianWeight s x ≤ s * gaussianWeight (2 * s) x := by
  calc ‖x‖ * gaussianWeight s x = s * ((‖x‖ / s) * gaussianWeight s x) := by
        rw [← mul_assoc, mul_div_cancel₀ _ hs.ne']
    _ ≤ s * (Real.exp (3 * Real.pi / 4 * (‖x‖ / s) ^ 2) * gaussianWeight s x) := by
        have := (gaussianWeight_pos s x).le; have := hs.le
        gcongr; exact real_le_exp_three_quarters_pi_sq _
    _ = s * gaussianWeight (2 * s) x := by rw [gaussianWeight_mul_exp_three_quarters s hs x]

private theorem norm_sq_mul_gaussianWeight_le (s : ℝ) (hs : 0 < s) (x : E) :
    ‖x‖ ^ 2 * gaussianWeight s x ≤ s ^ 2 * gaussianWeight (2 * s) x := by
  calc ‖x‖ ^ 2 * gaussianWeight s x = s ^ 2 * ((‖x‖ / s) ^ 2 * gaussianWeight s x) := by
        rw [div_pow, ← mul_assoc, mul_div_cancel₀ _ (sq_pos_of_pos hs).ne']
    _ ≤ s ^ 2 * (Real.exp (3 * Real.pi / 4 * (‖x‖ / s) ^ 2) * gaussianWeight s x) := by
        have := (gaussianWeight_pos s x).le; have := sq_nonneg s
        gcongr; exact sq_le_exp_three_quarters_pi_sq _
    _ = s ^ 2 * gaussianWeight (2 * s) x := by rw [gaussianWeight_mul_exp_three_quarters s hs x]

private theorem gaussianWeight_sub_smul_le [NormedSpace ℝ E]
    (s : ℝ) (hs : 0 < s) (x u : E) {t : ℝ} (ht : |t| ≤ 1) :
    gaussianWeight s (x - t • u) ≤
      Real.exp (Real.pi * ‖u‖ ^ 2 / s ^ 2) * gaussianWeight (2 * s) x := by
  unfold gaussianWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have htri : ‖x‖ ≤ ‖x - t • u‖ + ‖u‖ := by
    calc ‖x‖ = ‖(x - t • u) + t • u‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - t • u‖ + ‖t • u‖ := norm_add_le _ _
      _ ≤ ‖x - t • u‖ + ‖u‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          linarith [mul_le_of_le_one_left (norm_nonneg u) ht]
  have hsq : ‖x‖ ^ 2 ≤ 4 * ‖x - t • u‖ ^ 2 + 4 * ‖u‖ ^ 2 := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) htri 2
    linarith [sq_nonneg (‖x - t • u‖ - ‖u‖), sq_nonneg ‖x - t • u‖, sq_nonneg ‖u‖]
  have hs0 : s ≠ 0 := hs.ne'
  rw [show Real.pi * ‖u‖ ^ 2 / s ^ 2 + -Real.pi * ‖x‖ ^ 2 / (2 * s) ^ 2 =
      -Real.pi * ‖x - t • u‖ ^ 2 / s ^ 2 +
        Real.pi * (4 * ‖x - t • u‖ ^ 2 + 4 * ‖u‖ ^ 2 - ‖x‖ ^ 2) / (4 * s ^ 2) by
    field_simp; ring]
  exact le_add_of_nonneg_right (div_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hsq))
    (by positivity))

end PointwiseDomination

section SummabilityAndBridges

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem summable_gaussianWeight_mul_norm_sub
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) (c : E) :
    Summable fun x : L ↦ gaussianWeight s ((x : E) - c) * ‖(x : E) - c‖ := by
  refine Summable.of_nonneg_of_le (fun x ↦ mul_nonneg (gaussianWeight_pos _ _).le (norm_nonneg _))
    (fun x ↦ ?_) ((summable_gaussianWeight L (2 * s) (by positivity) c).mul_left s)
  rw [mul_comm]
  exact norm_mul_gaussianWeight_le s hs ((x : E) - c)

private theorem summable_gaussianWeight_mul_norm_sub_sq
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) (c : E) :
    Summable fun x : L ↦ gaussianWeight s ((x : E) - c) * ‖(x : E) - c‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun x ↦ mul_nonneg (gaussianWeight_pos _ _).le (sq_nonneg _))
    (fun x ↦ ?_) ((summable_gaussianWeight L (2 * s) (by positivity) c).mul_left (s ^ 2))
  rw [mul_comm]
  exact norm_sq_mul_gaussianWeight_le s hs ((x : E) - c)

private theorem summable_discreteGaussian_smul_sub
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) (c : E) :
    Summable fun x : L ↦ (discreteGaussian L s hs c x).toReal • ((x : E) - c) := by
  apply Summable.of_norm
  have hsum := (summable_gaussianWeight_mul_norm_sub L s hs c).div_const (gaussianMass L s c)
  refine hsum.congr fun x ↦ ?_
  rw [norm_smul, Real.norm_of_nonneg ENNReal.toReal_nonneg, discreteGaussian_apply_toReal,
    div_mul_eq_mul_div]

private theorem summable_discreteGaussian_mul_norm_sub_sq
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) (c : E) :
    Summable fun x : L ↦ (discreteGaussian L s hs c x).toReal * ‖(x : E) - c‖ ^ 2 := by
  have hsum := (summable_gaussianWeight_mul_norm_sub_sq L s hs c).div_const (gaussianMass L s c)
  refine hsum.congr fun x ↦ ?_
  rw [discreteGaussian_apply_toReal, div_mul_eq_mul_div]

/-- Directional first moments of a discrete Gaussian are summable for every discrete
`ℤ`-submodule `L` and positive width `s`. -/
theorem summable_discreteGaussian_mul_inner_sub
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) (c u : E) :
    Summable fun x : L ↦ (discreteGaussian L s hs c x).toReal * ⟪(x : E) - c, u⟫ := by
  have h := (innerSL ℝ u).summable (summable_discreteGaussian_smul_sub L s hs c)
  refine h.congr fun x ↦ ?_
  simp only [innerSL_apply_apply, inner_smul_right, real_inner_comm]

private theorem inner_sq_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x u : E) :
    ⟪x, u⟫ ^ 2 ≤ ‖x‖ ^ 2 * ‖u‖ ^ 2 := by
  rw [← mul_pow, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2

/-- Directional second moments of a discrete Gaussian are summable for every discrete
`ℤ`-submodule `L` and positive width `s`. -/
theorem summable_discreteGaussian_mul_inner_sub_sq
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) (c u : E) :
    Summable fun x : L ↦ (discreteGaussian L s hs c x).toReal * ⟪(x : E) - c, u⟫ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun x ↦ mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
    (fun x ↦ ?_) ((summable_discreteGaussian_mul_norm_sub_sq L s hs c).mul_right (‖u‖ ^ 2))
  calc (discreteGaussian L s hs c x).toReal * ⟪(x : E) - c, u⟫ ^ 2
      ≤ (discreteGaussian L s hs c x).toReal * (‖(x : E) - c‖ ^ 2 * ‖u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (inner_sq_le _ _) ENNReal.toReal_nonneg
    _ = (discreteGaussian L s hs c x).toReal * ‖(x : E) - c‖ ^ 2 * ‖u‖ ^ 2 := by ring

private theorem integrable_of_summable_discreteGaussian [MeasurableSpace E] [BorelSpace E]
    {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F]
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) (c : E)
    {f : L → F} (hcont : Continuous f)
    (hsum : Summable fun x : L ↦ (discreteGaussian L s hs c x).toReal * ‖f x‖) :
    Integrable f (discreteGaussian L s hs c).toMeasure := by
  have _ : Countable L := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  refine ⟨hcont.measurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm, lintegral_countable']
  have heq :
      (∑' x : L, ENNReal.ofReal ‖f x‖ * (discreteGaussian L s hs c).toMeasure {x}) =
        ENNReal.ofReal (∑' x : L, (discreteGaussian L s hs c x).toReal * ‖f x‖) := by
    rw [ENNReal.ofReal_tsum_of_nonneg
      (fun x ↦ mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)) hsum]
    refine tsum_congr fun x ↦ ?_
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (PMF.apply_ne_top _ _), mul_comm]
  exact heq ▸ ENNReal.ofReal_lt_top

/-- The centered displacement `x ↦ (x : E) - c` is square-integrable (`MemLp 2`) under
`(discreteGaussian L s hs c).toMeasure` for every discrete `ℤ`-submodule `L`. -/
theorem memLp_sub_discreteGaussian [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) (c : E) :
    MemLp (fun x : L ↦ (x : E) - c) 2 (discreteGaussian L s hs c).toMeasure := by
  have hcont : Continuous (fun x : L ↦ (x : E) - c) := continuous_subtypeVal.sub continuous_const
  rw [memLp_two_iff_integrable_sq_norm hcont.measurable.aestronglyMeasurable]
  refine integrable_of_summable_discreteGaussian L s hs c ((hcont.norm).pow 2) ?_
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using
    summable_discreteGaussian_mul_norm_sub_sq L s hs c

/-- The Bochner expectation of `(x : E) - c` under `(discreteGaussian L s hs c).toMeasure`
equals the probability-weighted `tsum`. -/
theorem integral_sub_discreteGaussian_eq_tsum [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) (c : E) :
    ∫ x : L, ((x : E) - c) ∂(discreteGaussian L s hs c).toMeasure =
      ∑' x : L, (discreteGaussian L s hs c x).toReal • ((x : E) - c) := by
  have hint : Integrable (fun x : L ↦ (x : E) - c) (discreteGaussian L s hs c).toMeasure :=
    (memLp_sub_discreteGaussian L s hs c).integrable one_le_two
  exact PMF.integral_eq_tsum (discreteGaussian L s hs c) _ hint

/-- The Bochner expectation of `‖(x : E) - c‖ ^ 2` under `(discreteGaussian L s hs c).toMeasure`
equals the probability-weighted `tsum`. -/
theorem integral_norm_sub_sq_discreteGaussian_eq_tsum [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) (c : E) :
    ∫ x : L, ‖(x : E) - c‖ ^ 2 ∂(discreteGaussian L s hs c).toMeasure =
      ∑' x : L, (discreteGaussian L s hs c x).toReal * ‖(x : E) - c‖ ^ 2 := by
  have hint :
      Integrable (fun x : L ↦ ‖(x : E) - c‖ ^ 2) (discreteGaussian L s hs c).toMeasure := by
    have hcont : Continuous (fun x : L ↦ (x : E) - c) :=
      continuous_subtypeVal.sub continuous_const
    exact (memLp_two_iff_integrable_sq_norm hcont.measurable.aestronglyMeasurable).mp
      (memLp_sub_discreteGaussian L s hs c)
  simpa only [smul_eq_mul] using PMF.integral_eq_tsum (discreteGaussian L s hs c) _ hint

end SummabilityAndBridges

section DiscreteMoments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem gaussianMass_eq_tsum_dual_cos [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c : E) :
    gaussianMass L s c = s ^ finrank ℝ E / covolume L *
      ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
        gaussianWeight (1 / s) (w : E) * Real.cos (2 * Real.pi * ⟪c, (w : E)⟫) := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have _ : DiscreteTopology D := discreteTopology_dualSubmodule L
  have hsum :
      Summable (fun w : D ↦ (gaussianWeight (1 / s) (w : E) : ℂ) *
        (Real.fourierChar (-⟪c, (w : E)⟫) : ℂ)) := by
    apply summable_norm_iff.mp
    simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gaussianWeight_pos _ _).le,
      Circle.norm_coe, mul_one, sub_zero] using
        summable_gaussianWeight D (1 / s) (one_div_pos.mpr hs) 0
  have h := congrArg Complex.re (gaussianMass_eq_tsum_dual L s hs c)
  have hpre :
      ((s : ℂ) ^ finrank ℝ E / (covolume L : ℂ)) =
        (((s ^ finrank ℝ E / covolume L : ℝ) : ℂ)) := by
    push_cast
    rfl
  rw [Complex.ofReal_re, hpre, Complex.re_ofReal_mul] at h
  rw [h]
  congr 1
  rw [← Complex.reCLM_apply, Complex.reCLM.map_tsum hsum]
  refine tsum_congr fun w ↦ ?_
  rw [Complex.reCLM_apply, Real.fourierChar_apply, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, show 2 * Real.pi * -⟪c, (w : E)⟫ = -(2 * Real.pi * ⟪c, (w : E)⟫)
      by ring, Real.cos_neg]

omit [FiniteDimensional ℝ E] in
private theorem hasDerivAt_gaussianWeight_sub_smul (s : ℝ) (x u : E) (t : ℝ) :
    HasDerivAt (fun y : ℝ ↦ gaussianWeight s (x - y • u))
      (2 * Real.pi / s ^ 2 * ⟪x - t • u, u⟫ * gaussianWeight s (x - t • u)) t := by
  have hquad : ∀ y : ℝ, gaussianWeight s (x - y • u) =
      Real.exp (-Real.pi * (‖x‖ ^ 2 - 2 * ⟪x, u⟫ * y + ‖u‖ ^ 2 * y ^ 2) / s ^ 2) := fun y ↦ by
    unfold gaussianWeight; congr 2
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]; ring
  simp_rw [hquad]
  have hd_inner : HasDerivAt (fun y : ℝ ↦ ‖x‖ ^ 2 - 2 * ⟪x, u⟫ * y + ‖u‖ ^ 2 * y ^ 2)
      (-(2 * ⟪x, u⟫) + ‖u‖ ^ 2 * (2 * t)) t := by
    have h1 : HasDerivAt (fun y : ℝ ↦ 2 * ⟪x, u⟫ * y) (2 * ⟪x, u⟫) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * ⟪x, u⟫)
    have h2 : HasDerivAt (fun y : ℝ ↦ ‖u‖ ^ 2 * y ^ 2) (‖u‖ ^ 2 * (2 * t)) t := by
      simpa using (hasDerivAt_pow 2 t).const_mul (‖u‖ ^ 2)
    convert ((hasDerivAt_const t (‖x‖ ^ 2)).sub h1).add h2 using 1; ring
  convert ((hd_inner.const_mul (-Real.pi)).div_const (s ^ 2)).exp using 1
  rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, RCLike.conj_to_real]; ring

omit [FiniteDimensional ℝ E] in
private theorem hasDerivAt_inner_mul_gaussianWeight_sub_smul (s : ℝ) (x u : E) (t : ℝ) :
    HasDerivAt (fun y : ℝ ↦ 2 * Real.pi / s ^ 2 * ⟪x - y • u, u⟫ * gaussianWeight s (x - y • u))
      (((2 * Real.pi / s ^ 2) ^ 2 * ⟪x - t • u, u⟫ ^ 2 - 2 * Real.pi / s ^ 2 * ‖u‖ ^ 2) *
        gaussianWeight s (x - t • u)) t := by
  have hd1 : HasDerivAt (fun y : ℝ ↦ 2 * Real.pi / s ^ 2 * ⟪x - y • u, u⟫)
      (-(2 * Real.pi / s ^ 2 * ‖u‖ ^ 2)) t := by
    simp_rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, RCLike.conj_to_real]
    have h0 : HasDerivAt (fun y : ℝ ↦ ⟪x, u⟫ - y * ‖u‖ ^ 2) (0 - ‖u‖ ^ 2) t :=
      (hasDerivAt_const t ⟪x, u⟫).sub (by simpa using (hasDerivAt_id t).mul_const (‖u‖ ^ 2))
    convert h0.const_mul (2 * Real.pi / s ^ 2) using 1; ring
  convert hd1.mul (hasDerivAt_gaussianWeight_sub_smul s x u t) using 1; ring

private theorem hasDerivAt_primal_first
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) (c u : E)
    {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y : ℝ ↦ gaussianMass L s (c + y • u))
      (∑' z : L, 2 * Real.pi / s ^ 2 * ⟪(z : E) - c - t • u, u⟫ *
        gaussianWeight s ((z : E) - c - t • u)) t := by
  have hrew : (fun y : ℝ ↦ gaussianMass L s (c + y • u)) =
      fun y : ℝ ↦ ∑' z : L, gaussianWeight s ((z : E) - c - y • u) := by
    funext y; exact tsum_congr fun z ↦ by rw [sub_add_eq_sub_sub]
  rw [hrew]
  let C : ℝ := 2 * Real.pi / s * ‖u‖ * Real.exp (Real.pi * ‖u‖ ^ 2 / (2 * s) ^ 2)
  refine hasDerivAt_tsum_of_isPreconnected
    ((summable_gaussianWeight L (4 * s) (by positivity) c).mul_left C) isOpen_Ioo isPreconnected_Ioo
    (fun z y _ ↦ hasDerivAt_gaussianWeight_sub_smul s ((z : E) - c) u y) (fun z y hy ↦ ?_)
    (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)
    (by simpa only [zero_smul, sub_zero] using summable_gaussianWeight L s hs c) ht
  have hyabs : |y| ≤ 1 := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
  have h1 := abs_real_inner_le_norm ((z : E) - c - y • u) u
  have h2 := norm_mul_gaussianWeight_le s hs ((z : E) - c - y • u)
  have h3 := gaussianWeight_sub_smul_le (2 * s) (by positivity) ((z : E) - c) u hyabs
  rw [show 2 * (2 * s) = 4 * s by ring] at h3
  have hw := (gaussianWeight_pos s ((z : E) - c - y • u)).le
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi / s ^ 2),
    abs_of_nonneg hw]
  calc 2 * Real.pi / s ^ 2 * |⟪(z : E) - c - y • u, u⟫| * gaussianWeight s ((z : E) - c - y • u)
      ≤ 2 * Real.pi / s ^ 2 * (‖(z : E) - c - y • u‖ * ‖u‖) *
          gaussianWeight s ((z : E) - c - y • u) := by gcongr
    _ = 2 * Real.pi / s ^ 2 * ‖u‖ *
          (‖(z : E) - c - y • u‖ * gaussianWeight s ((z : E) - c - y • u)) := by ring
    _ ≤ 2 * Real.pi / s ^ 2 * ‖u‖ *
          (s * (Real.exp (Real.pi * ‖u‖ ^ 2 / (2 * s) ^ 2) *
            gaussianWeight (4 * s) ((z : E) - c))) :=
        mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hs.le)) (by positivity)
    _ = C * gaussianWeight (4 * s) ((z : E) - c) := by
        dsimp only [C]; have hs0 := hs.ne'; field_simp

private theorem hasDerivAt_primal_second
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) (c u : E) :
    HasDerivAt
      (fun y : ℝ ↦ ∑' z : L, 2 * Real.pi / s ^ 2 * ⟪(z : E) - c - y • u, u⟫ *
        gaussianWeight s ((z : E) - c - y • u))
      (∑' z : L,
        ((2 * Real.pi / s ^ 2) ^ 2 * ⟪(z : E) - c, u⟫ ^ 2 - 2 * Real.pi / s ^ 2 * ‖u‖ ^ 2) *
          gaussianWeight s ((z : E) - c)) 0 := by
  let C : ℝ := ((2 * Real.pi / s) ^ 2 * ‖u‖ ^ 2 + 2 * Real.pi / s ^ 2 * ‖u‖ ^ 2) *
    Real.exp (Real.pi * ‖u‖ ^ 2 / (2 * s) ^ 2)
  have h := hasDerivAt_tsum_of_isPreconnected
    ((summable_gaussianWeight L (4 * s) (by positivity) c).mul_left C) isOpen_Ioo isPreconnected_Ioo
    (fun z y _ ↦ hasDerivAt_inner_mul_gaussianWeight_sub_smul s ((z : E) - c) u y) (fun z y hy ↦ ?_)
    (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num) ?_
    (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)
  · simpa only [zero_smul, sub_zero] using h
  · have hyabs : |y| ≤ 1 := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
    set v := (z : E) - c - y • u
    have hw := (gaussianWeight_pos s v).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    have habs : |(2 * Real.pi / s ^ 2) ^ 2 * ⟪v, u⟫ ^ 2 - 2 * Real.pi / s ^ 2 * ‖u‖ ^ 2| ≤
        (2 * Real.pi / s ^ 2) ^ 2 * ⟪v, u⟫ ^ 2 + 2 * Real.pi / s ^ 2 * ‖u‖ ^ 2 := by
      refine (abs_sub _ _).trans_eq ?_
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have ht1 : (2 * Real.pi / s ^ 2) ^ 2 * ⟪v, u⟫ ^ 2 * gaussianWeight s v ≤
        (2 * Real.pi / s) ^ 2 * ‖u‖ ^ 2 * gaussianWeight (2 * s) v := calc
      (2 * Real.pi / s ^ 2) ^ 2 * ⟪v, u⟫ ^ 2 * gaussianWeight s v
          ≤ (2 * Real.pi / s ^ 2) ^ 2 * (‖v‖ ^ 2 * ‖u‖ ^ 2) * gaussianWeight s v := by
            have := inner_sq_le v u; gcongr
      _ = (2 * Real.pi / s ^ 2) ^ 2 * ‖u‖ ^ 2 * (‖v‖ ^ 2 * gaussianWeight s v) := by ring
      _ ≤ (2 * Real.pi / s ^ 2) ^ 2 * ‖u‖ ^ 2 * (s ^ 2 * gaussianWeight (2 * s) v) :=
            mul_le_mul_of_nonneg_left (norm_sq_mul_gaussianWeight_le s hs v) (by positivity)
      _ = (2 * Real.pi / s) ^ 2 * ‖u‖ ^ 2 * gaussianWeight (2 * s) v := by
            have hs0 := hs.ne'; field_simp
    have ht2 : 2 * Real.pi / s ^ 2 * ‖u‖ ^ 2 * gaussianWeight s v ≤
        2 * Real.pi / s ^ 2 * ‖u‖ ^ 2 * gaussianWeight (2 * s) v :=
      mul_le_mul_of_nonneg_left (gaussianWeight_le_gaussianWeight_two_mul s v) (by positivity)
    have h3 := gaussianWeight_sub_smul_le (2 * s) (by positivity) ((z : E) - c) u hyabs
    rw [show 2 * (2 * s) = 4 * s by ring] at h3
    calc |(2 * Real.pi / s ^ 2) ^ 2 * ⟪v, u⟫ ^ 2 - 2 * Real.pi / s ^ 2 * ‖u‖ ^ 2| *
          gaussianWeight s v
        ≤ ((2 * Real.pi / s ^ 2) ^ 2 * ⟪v, u⟫ ^ 2 + 2 * Real.pi / s ^ 2 * ‖u‖ ^ 2) *
            gaussianWeight s v := mul_le_mul_of_nonneg_right habs hw
      _ ≤ ((2 * Real.pi / s) ^ 2 * ‖u‖ ^ 2 + 2 * Real.pi / s ^ 2 * ‖u‖ ^ 2) *
            gaussianWeight (2 * s) v := by rw [add_mul, add_mul]; exact add_le_add ht1 ht2
      _ ≤ C * gaussianWeight (4 * s) ((z : E) - c) := by
          dsimp only [C]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h3 (by positivity)
  · exact ((summable_discreteGaussian_mul_inner_sub L s hs c u).mul_left
      (2 * Real.pi / s ^ 2 * gaussianMass L s c)).congr fun z ↦ by
        simp only [zero_smul, sub_zero, discreteGaussian_apply_toReal]
        have hm := (gaussianMass_pos L s hs c).ne'; field_simp

omit [FiniteDimensional ℝ E] in
private theorem hasDerivAt_dual_phase (c u w : E) (y : ℝ) :
    HasDerivAt (fun z : ℝ ↦ 2 * Real.pi * ⟪c, w⟫ + 2 * Real.pi * ⟪u, w⟫ * z)
      (2 * Real.pi * ⟪u, w⟫) y := by
  simpa only [mul_one] using
    ((hasDerivAt_id' y).const_mul (2 * Real.pi * ⟪u, w⟫)).const_add (2 * Real.pi * ⟪c, w⟫)

omit [FiniteDimensional ℝ E] in
private theorem norm_dual_moment_term_le
    {C a b trig gw gw2 : ℝ} (hC : 0 ≤ C) (ha : |a| ≤ b) (htrig : |trig| ≤ 1)
    (hgw : 0 ≤ gw) (hdom : b * gw ≤ gw2) :
    ‖C * a * gw * trig‖ ≤ C * gw2 := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hC, abs_of_nonneg hgw]
  have hb : 0 ≤ b := (abs_nonneg a).trans ha
  calc C * |a| * gw * |trig| ≤ C * (b * gw) := by
        calc _ ≤ C * b * gw * 1 := by gcongr
          _ = C * (b * gw) := by ring
    _ ≤ C * gw2 := mul_le_mul_of_nonneg_left hdom hC

omit [FiniteDimensional ℝ E] in
private theorem norm_dual_first_term_le (s : ℝ) (hs : 0 < s) (c u w : E) (y : ℝ) :
    ‖-(2 * Real.pi * ⟪u, w⟫) * gaussianWeight (1 / s) w *
        Real.sin (2 * Real.pi * ⟪c, w⟫ + 2 * Real.pi * ⟪u, w⟫ * y)‖ ≤
      (2 * Real.pi * ‖u‖ / s) * gaussianWeight (2 / s) w := by
  have hdom := norm_mul_gaussianWeight_le (1 / s) (one_div_pos.mpr hs) w
  rw [show 2 * (1 / s) = 2 / s by ring] at hdom
  rw [neg_mul, neg_mul, norm_neg]
  exact (norm_dual_moment_term_le (by positivity : 0 ≤ 2 * Real.pi)
    (abs_real_inner_le_norm u w) (Real.abs_sin_le_one _) (gaussianWeight_pos _ _).le
    (gw2 := ‖u‖ * (1 / s * gaussianWeight (2 / s) w))
    (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hdom (norm_nonneg u))).trans_eq
    (by ring)

private theorem hasDerivAt_dual_first
    (D : Submodule ℤ E) [DiscreteTopology D] (s : ℝ) (hs : 0 < s) (c u : E) (t : ℝ) :
    HasDerivAt
      (fun y : ℝ ↦ ∑' w : D, gaussianWeight (1 / s) (w : E) *
        Real.cos (2 * Real.pi * ⟪c, (w : E)⟫ + 2 * Real.pi * ⟪u, (w : E)⟫ * y))
      (∑' w : D, -(2 * Real.pi * ⟪u, (w : E)⟫) * gaussianWeight (1 / s) (w : E) *
        Real.sin (2 * Real.pi * ⟪c, (w : E)⟫ + 2 * Real.pi * ⟪u, (w : E)⟫ * t)) t := by
  have hu_sum : Summable fun w : D ↦ (2 * Real.pi * ‖u‖ / s) * gaussianWeight (2 / s) (w : E) := by
    simpa only [sub_zero] using
      (summable_gaussianWeight D (2 / s) (by positivity) 0).mul_left (2 * Real.pi * ‖u‖ / s)
  refine hasDerivAt_tsum (F := ℝ) (y₀ := (0 : ℝ))
    (g := fun w : D ↦ fun y : ℝ ↦ gaussianWeight (1 / s) (w : E) *
      Real.cos (2 * Real.pi * ⟪c, (w : E)⟫ + 2 * Real.pi * ⟪u, (w : E)⟫ * y))
    (g' := fun w : D ↦ fun y : ℝ ↦ -(2 * Real.pi * ⟪u, (w : E)⟫) * gaussianWeight (1 / s) (w : E) *
      Real.sin (2 * Real.pi * ⟪c, (w : E)⟫ + 2 * Real.pi * ⟪u, (w : E)⟫ * y))
    hu_sum (fun w y ↦ ?_) (fun w y ↦ norm_dual_first_term_le s hs c u (w : E) y) ?_ t
  · convert ((hasDerivAt_dual_phase c u (w : E) y).cos).const_mul
      (gaussianWeight (1 / s) (w : E)) using 1
    ring
  · refine Summable.of_norm_bounded (g := fun w : D ↦ gaussianWeight (1 / s) (w : E))
      (by simpa only [sub_zero] using summable_gaussianWeight D (1 / s) (one_div_pos.mpr hs) 0)
      fun w ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianWeight_pos _ _).le]
    exact mul_le_of_le_one_right (gaussianWeight_pos _ _).le (Real.abs_cos_le_one _)

private theorem hasDerivAt_dual_second
    (D : Submodule ℤ E) [DiscreteTopology D] (s : ℝ) (hs : 0 < s) (c u : E) :
    HasDerivAt
      (fun y : ℝ ↦ ∑' w : D, -(2 * Real.pi * ⟪u, (w : E)⟫) * gaussianWeight (1 / s) (w : E) *
        Real.sin (2 * Real.pi * ⟪c, (w : E)⟫ + 2 * Real.pi * ⟪u, (w : E)⟫ * y))
      (∑' w : D, -((2 * Real.pi * ⟪u, (w : E)⟫) ^ 2) * gaussianWeight (1 / s) (w : E) *
        Real.cos (2 * Real.pi * ⟪c, (w : E)⟫)) 0 := by
  have hu_sum :
      Summable fun w : D ↦ ((2 * Real.pi * ‖u‖) ^ 2 / s ^ 2) * gaussianWeight (2 / s) (w : E) := by
    simpa only [sub_zero] using
      (summable_gaussianWeight D (2 / s) (by positivity) 0).mul_left
        ((2 * Real.pi * ‖u‖) ^ 2 / s ^ 2)
  have h := hasDerivAt_tsum (F := ℝ) (y₀ := (0 : ℝ))
    (g := fun w : D ↦ fun y : ℝ ↦ -(2 * Real.pi * ⟪u, (w : E)⟫) * gaussianWeight (1 / s) (w : E) *
      Real.sin (2 * Real.pi * ⟪c, (w : E)⟫ + 2 * Real.pi * ⟪u, (w : E)⟫ * y))
    (g' := fun w : D ↦ fun y : ℝ ↦ -((2 * Real.pi * ⟪u, (w : E)⟫) ^ 2) *
      gaussianWeight (1 / s) (w : E) *
      Real.cos (2 * Real.pi * ⟪c, (w : E)⟫ + 2 * Real.pi * ⟪u, (w : E)⟫ * y))
    hu_sum (fun w y ↦ ?_) (fun w y ↦ ?_) ?_ (0 : ℝ)
  · simpa only [mul_zero, add_zero] using h
  · convert ((hasDerivAt_dual_phase c u (w : E) y).sin).const_mul
      (-(2 * Real.pi * ⟪u, (w : E)⟫) * gaussianWeight (1 / s) (w : E)) using 1
    ring
  · have hdom := norm_sq_mul_gaussianWeight_le (1 / s) (one_div_pos.mpr hs) (w : E)
    rw [show 2 * (1 / s) = 2 / s by ring] at hdom
    rw [neg_mul, neg_mul, norm_neg, mul_pow]
    refine (norm_dual_moment_term_le (by positivity : 0 ≤ (2 * Real.pi) ^ 2)
      ((abs_of_nonneg (sq_nonneg _)).trans_le (inner_sq_le u (w : E)))
      (Real.abs_cos_le_one _) (gaussianWeight_pos _ _).le
      ((mul_assoc _ _ _).trans_le (mul_le_mul_of_nonneg_left hdom (sq_nonneg _)))).trans_eq ?_
    rw [div_pow, one_pow]; ring
  · exact Summable.of_norm_bounded
      (by simpa only [sub_zero] using
        (summable_gaussianWeight D (2 / s) (by positivity) 0).mul_left (2 * Real.pi * ‖u‖ / s))
      fun w ↦ norm_dual_first_term_le s hs c u (w : E) 0

private theorem primal_eq_dual_first_deriv [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c u : E) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    (∑' z : L, 2 * Real.pi / s ^ 2 * ⟪(z : E) - c - t • u, u⟫ *
        gaussianWeight s ((z : E) - c - t • u)) =
      s ^ finrank ℝ E / covolume L *
        ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
          -(2 * Real.pi * ⟪u, (w : E)⟫) * gaussianWeight (1 / s) (w : E) *
            Real.sin (2 * Real.pi * ⟪c, (w : E)⟫ + 2 * Real.pi * ⟪u, (w : E)⟫ * t) := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have _ : DiscreteTopology D := discreteTopology_dualSubmodule L
  have h1 := hasDerivAt_primal_first L s hs c u ht
  have h2 := (hasDerivAt_dual_first D s hs c u t).const_mul (s ^ finrank ℝ E / covolume L)
  have heq :
      (fun y : ℝ ↦ gaussianMass L s (c + y • u)) =
        fun y : ℝ ↦ s ^ finrank ℝ E / covolume L *
          ∑' w : D, gaussianWeight (1 / s) (w : E) *
            Real.cos (2 * Real.pi * ⟪c, (w : E)⟫ + 2 * Real.pi * ⟪u, (w : E)⟫ * y) := by
    funext y
    rw [gaussianMass_eq_tsum_dual_cos L s hs (c + y • u)]
    congr 1
    exact tsum_congr fun w ↦ by
      rw [inner_add_left, inner_smul_left, RCLike.conj_to_real]; congr 2; ring
  rw [heq] at h1
  exact h1.unique h2

private theorem primal_eq_dual_second_deriv [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c u : E) :
    (∑' z : L,
        ((2 * Real.pi / s ^ 2) ^ 2 * ⟪(z : E) - c, u⟫ ^ 2 - 2 * Real.pi / s ^ 2 * ‖u‖ ^ 2) *
          gaussianWeight s ((z : E) - c)) =
      s ^ finrank ℝ E / covolume L *
        ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
          -((2 * Real.pi * ⟪u, (w : E)⟫) ^ 2) * gaussianWeight (1 / s) (w : E) *
            Real.cos (2 * Real.pi * ⟪c, (w : E)⟫) := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have _ : DiscreteTopology D := discreteTopology_dualSubmodule L
  have h1 := hasDerivAt_primal_second L s hs c u
  have h2 := (hasDerivAt_dual_second D s hs c u).const_mul (s ^ finrank ℝ E / covolume L)
  have hcongr :
      (fun y : ℝ ↦ ∑' z : L, 2 * Real.pi / s ^ 2 * ⟪(z : E) - c - y • u, u⟫ *
          gaussianWeight s ((z : E) - c - y • u)) =ᶠ[nhds 0]
        fun y : ℝ ↦ s ^ finrank ℝ E / covolume L *
          ∑' w : D, -(2 * Real.pi * ⟪u, (w : E)⟫) * gaussianWeight (1 / s) (w : E) *
            Real.sin (2 * Real.pi * ⟪c, (w : E)⟫ + 2 * Real.pi * ⟪u, (w : E)⟫ * y) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with y hy
    exact primal_eq_dual_first_deriv L s hs c u hy
  exact (h1.congr_of_eventuallyEq hcongr.symm).unique h2

private theorem abs_tsum_dual_le_of_bound [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c : E) (ε : ℝ) (hε : ε < 1)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (2 / s) 0 - 1 ≤ ε)
    {C : ℝ} (hC : 0 ≤ C)
    (g : LinearMap.BilinForm.dualSubmodule (innerₗ E) L → ℝ)
    (hg0 : g 0 = 0)
    (hbound : ∀ w, ‖g w‖ ≤ C * gaussianWeight (2 / s) (w : E)) :
    |(s ^ finrank ℝ E / covolume L / gaussianMass L s c) * ∑' w, g w| ≤
      ε / (1 - ε) * C := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have _ : DiscreteTopology D := discreteTopology_dualSubmodule L
  set cv : ℝ := covolume L
  have hcv : 0 < cv := covolume_pos L volume
  set sp : ℝ := s ^ finrank ℝ E
  have hsp : 0 < sp := pow_pos hs _
  set m : ℝ := gaussianMass L s c
  have hm : 0 < m := gaussianMass_pos L s hs c
  have hmono : gaussianMass D (1 / s) 0 - 1 ≤ gaussianMass D (2 / s) 0 - 1 := by
    have hs1 : Summable fun w : D ↦ gaussianWeight (1 / s) (w : E) := by
      simpa only [sub_zero] using summable_gaussianWeight D (1 / s) (one_div_pos.mpr hs) 0
    have hs2 : Summable fun w : D ↦ gaussianWeight (2 / s) (w : E) := by
      simpa only [sub_zero] using summable_gaussianWeight D (2 / s) (by positivity) 0
    rw [gaussianMass_zero_sub_one_eq_tsum D (1 / s) (one_div_pos.mpr hs),
      gaussianMass_zero_sub_one_eq_tsum D (2 / s) (by positivity)]
    refine Summable.tsum_le_tsum (fun w ↦ ?_) (hs1.subtype _) (hs2.subtype _)
    simpa only [show 2 * (1 / s) = 2 / s by ring] using
      gaussianWeight_le_gaussianWeight_two_mul (1 / s) (w : E)
  have h1 := (abs_le.mp ((abs_gaussianMass_normalized_sub_one_le L s hs c).trans
    (hmono.trans hdual))).1
  have hlo : 1 - ε ≤ cv / sp * m := by linarith
  have h1m : 0 < 1 - ε := sub_pos.mpr hε
  have hscale : sp / cv / m ≤ 1 / (1 - ε) := by
    have hinv := one_div_le_one_div_of_le h1m hlo
    rwa [div_mul_eq_mul_div, one_div_div, ← div_div] at hinv
  have hsum_dom : Summable fun w : D ↦ C * gaussianWeight (2 / s) (w : E) := by
    simpa only [sub_zero] using (summable_gaussianWeight D (2 / s) (by positivity) 0).mul_left C
  have hsum_g : Summable g := Summable.of_norm_bounded hsum_dom hbound
  have hsum_abs : |∑' w : D, g w| ≤ C * (gaussianMass D (2 / s) 0 - 1) := by
    rw [← tsum_subtype_eq_of_support_subset (s := {w : D | w ≠ 0}) fun w hw h ↦ hw (h ▸ hg0),
      ← Real.norm_eq_abs, gaussianMass_zero_sub_one_eq_tsum D (2 / s) (by positivity),
      ← tsum_mul_left]
    exact (norm_tsum_le_tsum_norm (hsum_g.norm.subtype _)).trans
      (Summable.tsum_le_tsum (fun w ↦ hbound w) (hsum_g.norm.subtype _) (hsum_dom.subtype _))
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ sp / cv / m)]
  calc
    (sp / cv / m) * |∑' w : D, g w| ≤
        (1 / (1 - ε)) * (C * (gaussianMass D (2 / s) 0 - 1)) :=
      mul_le_mul hscale hsum_abs (abs_nonneg _) (by positivity)
    _ ≤ (1 / (1 - ε)) * (C * ε) := by gcongr
    _ = ε / (1 - ε) * C := by ring

private theorem tsum_mul_gaussianWeight_eq
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) (c : E) (f : L → ℝ) :
    (∑' z : L, f z * gaussianWeight s ((z : E) - c)) =
      gaussianMass L s c * ∑' z : L, (discreteGaussian L s hs c z).toReal * f z := by
  rw [← tsum_mul_left]
  exact tsum_congr fun z ↦ by
    have hm := (gaussianMass_pos L s hs c).ne'
    rw [discreteGaussian_apply_toReal]; field_simp

/-- Dual-mass step toward [MicciancioRegev2007], Lemma 4.2 (first moment, pp. 13–14 of the
December 27, 2005 author version), stated directly under `ρ_{2/s}(L* \ {0}) ≤ ε < 1` rather than
the `2 * η_ε(L) ≤ s` endpoint: for any full-rank discrete lattice `L`, width `s > 0`, center `c`,
unit vector `u`, and `ε < 1` with `ρ_{2/s}(L* \ {0}) ≤ ε` (which automatically implies `0 ≤ ε`),
the directional expectation `|𝔼_{x ~ D_{L,s,c}}[⟪x - c, u⟫]|` is at most `ε / (1 - ε) * s`.
Holds in all dimensions including `0`. -/
theorem abs_tsum_discreteGaussian_mul_inner_sub_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c u : E) (hu : ‖u‖ = 1) (ε : ℝ) (hε : ε < 1)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (2 / s) 0 - 1 ≤ ε) :
    |∑' x : L, (discreteGaussian L s hs c x).toReal * ⟪(x : E) - c, u⟫| ≤
      ε / (1 - ε) * s := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have _ : DiscreteTopology D := discreteTopology_dualSubmodule L
  have h0 := primal_eq_dual_first_deriv L s hs c u (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)
  simp only [zero_smul, sub_zero, mul_zero, add_zero] at h0
  set α : ℝ := s ^ finrank ℝ E / covolume L
  set m : ℝ := gaussianMass L s c
  have hm := (gaussianMass_pos L s hs c).ne'
  have hlhs :
      (∑' z : L, 2 * Real.pi / s ^ 2 * ⟪(z : E) - c, u⟫ * gaussianWeight s ((z : E) - c)) =
        2 * Real.pi / s ^ 2 * m *
          ∑' z : L, (discreteGaussian L s hs c z).toReal * ⟪(z : E) - c, u⟫ := by
    simp_rw [mul_assoc, tsum_mul_left, tsum_mul_gaussianWeight_eq L s hs c]; ring
  rw [hlhs] at h0
  have hval :
      (∑' z : L, (discreteGaussian L s hs c z).toReal * ⟪(z : E) - c, u⟫) =
        (α / m) * ∑' w : D, -(s ^ 2 * ⟪u, (w : E)⟫ * gaussianWeight (1 / s) (w : E) *
          Real.sin (2 * Real.pi * ⟪c, (w : E)⟫)) := by
    have hdiv := congrArg (· / (2 * Real.pi / s ^ 2 * m)) h0
    rw [mul_div_cancel_left₀ _ (mul_ne_zero (by positivity) hm)] at hdiv
    rw [hdiv, show ∀ T : ℝ, α * T / (2 * Real.pi / s ^ 2 * m) =
        (α / m) * (T * (2 * Real.pi / s ^ 2)⁻¹) from fun T ↦ by ring, ← tsum_mul_right]
    congr 1; exact tsum_congr fun w ↦ by have hpi := Real.pi_pos.ne'; have hs0 := hs.ne'; field_simp
  rw [hval]
  refine abs_tsum_dual_le_of_bound L s hs c ε hε hdual hs.le _ (by simp) fun w ↦ ?_
  have hdom := norm_mul_gaussianWeight_le (1 / s) (one_div_pos.mpr hs) (w : E)
  rw [show 2 * (1 / s) = 2 / s by ring] at hdom
  rw [norm_neg]
  exact (norm_dual_moment_term_le (sq_nonneg s)
    (by simpa only [hu, one_mul] using abs_real_inner_le_norm u (w : E))
    (Real.abs_sin_le_one _) (gaussianWeight_pos _ _).le hdom).trans_eq
    (by have hs0 := hs.ne'; field_simp)

/-- Dual-mass step toward [MicciancioRegev2007], Lemma 4.2 (second moment, pp. 13–14 of the
December 27, 2005 author version), stated directly under `ρ_{2/s}(L* \ {0}) ≤ ε < 1` rather than
the `2 * η_ε(L) ≤ s` endpoint: for any full-rank discrete lattice `L`, width `s > 0`, center `c`,
unit vector `u`, and `ε < 1` with `ρ_{2/s}(L* \ {0}) ≤ ε` (which automatically implies `0 ≤ ε`),
`|𝔼_{x ~ D_{L,s,c}}[⟪x - c, u⟫²] - s² / (2π)| ≤ ε / (1 - ε) * s²`.
Holds in all dimensions including `0`. -/
theorem abs_tsum_discreteGaussian_mul_inner_sub_sq_sub_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c u : E) (hu : ‖u‖ = 1) (ε : ℝ) (hε : ε < 1)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (2 / s) 0 - 1 ≤ ε) :
    |(∑' x : L, (discreteGaussian L s hs c x).toReal * ⟪(x : E) - c, u⟫ ^ 2) -
        s ^ 2 / (2 * Real.pi)| ≤
      ε / (1 - ε) * s ^ 2 := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have _ : DiscreteTopology D := discreteTopology_dualSubmodule L
  have h0 := primal_eq_dual_second_deriv L s hs c u
  rw [hu, one_pow, mul_one] at h0
  set α : ℝ := s ^ finrank ℝ E / covolume L
  set m : ℝ := gaussianMass L s c
  have hm := (gaussianMass_pos L s hs c).ne'
  have hsum_sq : Summable fun z : L ↦ ⟪(z : E) - c, u⟫ ^ 2 * gaussianWeight s ((z : E) - c) :=
    ((summable_discreteGaussian_mul_inner_sub_sq L s hs c u).mul_left m).congr fun z ↦ by
      rw [discreteGaussian_apply_toReal]; dsimp only [m] at hm ⊢; field_simp
  have hlhs :
      (∑' z : L, ((2 * Real.pi / s ^ 2) ^ 2 * ⟪(z : E) - c, u⟫ ^ 2 - 2 * Real.pi / s ^ 2) *
          gaussianWeight s ((z : E) - c)) =
        (2 * Real.pi / s ^ 2) ^ 2 * m *
          ((∑' z : L, (discreteGaussian L s hs c z).toReal * ⟪(z : E) - c, u⟫ ^ 2) -
            s ^ 2 / (2 * Real.pi)) := by
    simp_rw [sub_mul, mul_assoc]
    rw [(hsum_sq.mul_left _).tsum_sub ((summable_gaussianWeight L s hs c).mul_left _),
      tsum_mul_left, tsum_mul_left, tsum_mul_gaussianWeight_eq L s hs c]
    change (2 * Real.pi / s ^ 2) ^ 2 * (m * _) - 2 * Real.pi / s ^ 2 * m = _
    have hpi := Real.pi_pos.ne'; have hs0 := hs.ne'; field_simp
  rw [hlhs] at h0
  have hval :
      (∑' z : L, (discreteGaussian L s hs c z).toReal * ⟪(z : E) - c, u⟫ ^ 2) -
          s ^ 2 / (2 * Real.pi) =
        (α / m) * ∑' w : D, -(s ^ 4 * ⟪u, (w : E)⟫ ^ 2 * gaussianWeight (1 / s) (w : E) *
          Real.cos (2 * Real.pi * ⟪c, (w : E)⟫)) := by
    have hdiv := congrArg (· / ((2 * Real.pi / s ^ 2) ^ 2 * m)) h0
    rw [mul_div_cancel_left₀ _ (mul_ne_zero (by positivity) hm)] at hdiv
    rw [hdiv, show ∀ T : ℝ, α * T / ((2 * Real.pi / s ^ 2) ^ 2 * m) =
        (α / m) * (T * ((2 * Real.pi / s ^ 2) ^ 2)⁻¹) from fun T ↦ by ring, ← tsum_mul_right]
    congr 1; exact tsum_congr fun w ↦ by have hpi := Real.pi_pos.ne'; have hs0 := hs.ne'; field_simp
  rw [hval]
  refine abs_tsum_dual_le_of_bound L s hs c ε hε hdual (sq_nonneg s) _ (by simp) fun w ↦ ?_
  have hdom := norm_sq_mul_gaussianWeight_le (1 / s) (one_div_pos.mpr hs) (w : E)
  rw [show 2 * (1 / s) = 2 / s by ring] at hdom
  rw [norm_neg]
  exact (norm_dual_moment_term_le (by positivity : 0 ≤ s ^ 4)
    (by rw [abs_of_nonneg (sq_nonneg _)]; simpa only [hu, one_pow, one_mul] using
      inner_sq_le u (w : E))
    (Real.abs_cos_le_one _) (gaussianWeight_pos _ _).le hdom).trans_eq
    (by have hs0 := hs.ne'; field_simp)

/-- Dual-mass step toward [MicciancioRegev2007], Lemma 4.3 (squared norm of mean, p. 14 of the
December 27, 2005 author version), stated directly under `ρ_{2/s}(L* \ {0}) ≤ ε < 1` rather than
the `2 * η_ε(L) ≤ s` endpoint: `‖𝔼_{x ~ D_{L,s,c}}[x - c]‖² ≤ (ε / (1 - ε))² * s² * finrank ℝ E`.
Holds in all dimensions including `0`. -/
theorem norm_tsum_discreteGaussian_smul_sub_sq_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c : E) (ε : ℝ) (hε : ε < 1)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (2 / s) 0 - 1 ≤ ε) :
    ‖∑' x : L, (discreteGaussian L s hs c x).toReal • ((x : E) - c)‖ ^ 2 ≤
      (ε / (1 - ε)) ^ 2 * s ^ 2 * finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  have hsum_v := summable_discreteGaussian_smul_sub L s hs c
  rw [← b.sum_sq_inner_left]
  have hcoord (i : Fin (finrank ℝ E)) :
      ⟪∑' x : L, (discreteGaussian L s hs c x).toReal • ((x : E) - c), b i⟫ ^ 2 ≤
        (ε / (1 - ε) * s) ^ 2 := by
    have hmap : ⟪∑' x : L, (discreteGaussian L s hs c x).toReal • ((x : E) - c), b i⟫ =
        ∑' x : L, (discreteGaussian L s hs c x).toReal * ⟪(x : E) - c, b i⟫ := by
      rw [real_inner_comm, ← innerSL_apply_apply (𝕜 := ℝ) (b i),
        (innerSL ℝ (b i)).map_tsum hsum_v]
      exact tsum_congr fun x ↦ by
        simp only [innerSL_apply_apply, real_inner_comm, inner_smul_left, RCLike.conj_to_real]
    rw [hmap, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (abs_tsum_discreteGaussian_mul_inner_sub_le L s hs c (b i) (b.orthonormal.1 i) ε hε hdual) 2
  refine (Finset.sum_le_sum fun i _ ↦ hcoord i).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Dual-mass step toward [MicciancioRegev2007], Lemma 4.3 (expected squared norm, p. 14 of the
December 27, 2005 author version), stated directly under `ρ_{2/s}(L* \ {0}) ≤ ε < 1` rather than
the `2 * η_ε(L) ≤ s` endpoint:
`𝔼_{x ~ D_{L,s,c}}[‖x - c‖²] ≤ (1 / (2π) + ε / (1 - ε)) * s² * finrank ℝ E`.
Holds in all dimensions including `0`. -/
theorem tsum_discreteGaussian_mul_norm_sub_sq_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c : E) (ε : ℝ) (hε : ε < 1)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (2 / s) 0 - 1 ≤ ε) :
    (∑' x : L, (discreteGaussian L s hs c x).toReal * ‖(x : E) - c‖ ^ 2) ≤
      (1 / (2 * Real.pi) + ε / (1 - ε)) * s ^ 2 * finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  have hrew : (fun x : L ↦ (discreteGaussian L s hs c x).toReal * ‖(x : E) - c‖ ^ 2) =
      fun x : L ↦ ∑ i : Fin (finrank ℝ E),
        (discreteGaussian L s hs c x).toReal * ⟪(x : E) - c, b i⟫ ^ 2 := by
    funext x; rw [← b.sum_sq_inner_left, Finset.mul_sum]
  rw [hrew, Summable.tsum_finsetSum fun i _ ↦
    summable_discreteGaussian_mul_inner_sub_sq L s hs c (b i)]
  have hcoord (i : Fin (finrank ℝ E)) :
      (∑' x : L, (discreteGaussian L s hs c x).toReal * ⟪(x : E) - c, b i⟫ ^ 2) ≤
        (1 / (2 * Real.pi) + ε / (1 - ε)) * s ^ 2 := by
    have := (abs_le.mp (abs_tsum_discreteGaussian_mul_inner_sub_sq_sub_le L s hs c (b i)
      (b.orthonormal.1 i) ε hε hdual)).2
    linarith [show s ^ 2 / (2 * Real.pi) + ε / (1 - ε) * s ^ 2 =
      (1 / (2 * Real.pi) + ε / (1 - ε)) * s ^ 2 by ring]
  refine (Finset.sum_le_sum fun i _ ↦ hcoord i).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

private theorem dual_mass_two_div_le_of_two_mul_smoothingParameter_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {s ε : ℝ} (hs : 0 < s) (hε0 : 0 < ε) (hη : 2 * smoothingParameter L ε ≤ s) :
    gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (2 / s) 0 - 1 ≤ ε := by
  have h := (smoothingParameter_le_iff L (half_pos hs) hε0).mp (by linarith)
  simpa only [one_div_div] using h

/-- Micciancio–Regev Lemma 4.2 (first directional moment, [MicciancioRegev2007], pp. 13–14 of
the December 27, 2005 author version): for any full-rank discrete lattice `L`, width `s > 0`,
center `c`, unit vector `u`, and `0 < ε < 1` with `2 * η_ε(L) ≤ s`,
`|𝔼_{x ~ D_{L,s,c}}[⟪x - c, u⟫]| ≤ ε / (1 - ε) * s`. Holds in all dimensions including `0`. -/
theorem abs_tsum_discreteGaussian_mul_inner_sub_le_of_smoothingParameter_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c u : E) (hu : ‖u‖ = 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1) (hη : 2 * smoothingParameter L ε ≤ s) :
    |∑' x : L, (discreteGaussian L s hs c x).toReal * ⟪(x : E) - c, u⟫| ≤
      ε / (1 - ε) * s :=
  abs_tsum_discreteGaussian_mul_inner_sub_le L s hs c u hu ε hε
    (dual_mass_two_div_le_of_two_mul_smoothingParameter_le L hs hε0 hη)

/-- Micciancio–Regev Lemma 4.2 (second directional moment, [MicciancioRegev2007], pp. 13–14 of
the December 27, 2005 author version): for any full-rank discrete lattice `L`, width `s > 0`,
center `c`, unit vector `u`, and `0 < ε < 1` with `2 * η_ε(L) ≤ s`,
`|𝔼_{x ~ D_{L,s,c}}[⟪x - c, u⟫²] - s² / (2π)| ≤ ε / (1 - ε) * s²`. Holds in all dimensions
including `0`. -/
theorem abs_tsum_discreteGaussian_mul_inner_sub_sq_sub_le_of_smoothingParameter_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c u : E) (hu : ‖u‖ = 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1) (hη : 2 * smoothingParameter L ε ≤ s) :
    |(∑' x : L, (discreteGaussian L s hs c x).toReal * ⟪(x : E) - c, u⟫ ^ 2) -
        s ^ 2 / (2 * Real.pi)| ≤
      ε / (1 - ε) * s ^ 2 :=
  abs_tsum_discreteGaussian_mul_inner_sub_sq_sub_le L s hs c u hu ε hε
    (dual_mass_two_div_le_of_two_mul_smoothingParameter_le L hs hε0 hη)

/-- Micciancio–Regev Lemma 4.3 (squared norm of mean, [MicciancioRegev2007], p. 14 of the
December 27, 2005 author version): for any full-rank discrete lattice `L`, width `s > 0`,
center `c`, and `0 < ε < 1` with `2 * η_ε(L) ≤ s`,
`‖𝔼_{x ~ D_{L,s,c}}[x - c]‖² ≤ (ε / (1 - ε))² * s² * finrank ℝ E`. Holds in all dimensions
including `0`. -/
theorem norm_tsum_discreteGaussian_smul_sub_sq_le_of_smoothingParameter_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c : E)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1) (hη : 2 * smoothingParameter L ε ≤ s) :
    ‖∑' x : L, (discreteGaussian L s hs c x).toReal • ((x : E) - c)‖ ^ 2 ≤
      (ε / (1 - ε)) ^ 2 * s ^ 2 * finrank ℝ E :=
  norm_tsum_discreteGaussian_smul_sub_sq_le L s hs c ε hε
    (dual_mass_two_div_le_of_two_mul_smoothingParameter_le L hs hε0 hη)

/-- Micciancio–Regev Lemma 4.3 (expected squared norm, [MicciancioRegev2007], p. 14 of the
December 27, 2005 author version): for any full-rank discrete lattice `L`, width `s > 0`,
center `c`, and `0 < ε < 1` with `2 * η_ε(L) ≤ s`,
`𝔼_{x ~ D_{L,s,c}}[‖x - c‖²] ≤ (1 / (2π) + ε / (1 - ε)) * s² * finrank ℝ E`. Holds in all
dimensions including `0`. -/
theorem tsum_discreteGaussian_mul_norm_sub_sq_le_of_smoothingParameter_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c : E)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1) (hη : 2 * smoothingParameter L ε ≤ s) :
    (∑' x : L, (discreteGaussian L s hs c x).toReal * ‖(x : E) - c‖ ^ 2) ≤
      (1 / (2 * Real.pi) + ε / (1 - ε)) * s ^ 2 * finrank ℝ E :=
  tsum_discreteGaussian_mul_norm_sub_sq_le L s hs c ε hε
    (dual_mass_two_div_le_of_two_mul_smoothingParameter_le L hs hε0 hη)

end DiscreteMoments

end ZLattice
