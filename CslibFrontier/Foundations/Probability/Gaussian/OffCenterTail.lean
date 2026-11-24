/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.Lattice.Dual
public import CslibFrontier.Foundations.Probability.Gaussian.SmoothingParameter
public import Mathlib.Probability.Moments.SubGaussian

import CslibFrontier.Foundations.Probability.Gaussian.DiscreteTail
import CslibFrontier.Foundations.Probability.Gaussian.MassBounds
import CslibFrontier.Foundations.Probability.Gaussian.ShiftBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Off-center Banaszczyk tails and one-dimensional discrete Gaussian bounds

## Main results

* `ZLattice.banaszczykConstant_lt_one`: for `c > 1 / √(2π)`, the base constant
  `c * √(2πe) * exp (-π c²)` is strictly less than `1`.
* `ZLattice.tsum_gaussianWeight_norm_sub_gt_lt`: shifted Banaszczyk tail bound on unnormalized
  lattice Gaussian mass outside radius `c * s * √(finrank ℝ E)` (sharpening
  [MicciancioRegev2007], Lemma 2.10, eq. (6), by removing the factor of `2`).
* `ZLattice.tsum_gaussianWeight_norm_sub_gt_sqrt_lt`: shifted [Regev2009], Lemma 2.5 (`c = 1`),
  bounding the tail mass strictly below `(1 / 4) ^ (finrank ℝ E) * gaussianMass L s 0`.
* `ZLattice.gaussianMass_div_le_of_dual_mass_le`,
  `ZLattice.gaussianMass_div_le_of_smoothingParameter_le`: under `ρ_{1/s}(L* \ {0}) ≤ ε < 1`
  (or `η_ε(L) ≤ s` with `0 < ε < 1`), the ratio of Gaussian masses at any two centers is at most
  `(1 + ε) / (1 - ε)`.
* `ZLattice.discreteGaussian_norm_sub_gt_lt_of_dual_mass_le`,
  `ZLattice.discreteGaussian_norm_sub_gt_sqrt_lt_of_dual_mass_le`,
  `ZLattice.discreteGaussian_norm_sub_gt_lt_of_smoothingParameter_le`,
  `ZLattice.discreteGaussian_norm_sub_gt_sqrt_lt_of_smoothingParameter_le`: dual-mass and
  `η_ε`-parameterized forms of [MicciancioRegev2007], Lemma 4.4 (p. 15), sharpening `(1 / 2) ^ n`
  to strict `(1 / 4) ^ n`.
* `ZLattice.summable_gaussianWeight_mul_exp_inner`, `ZLattice.tsum_gaussianWeight_mul_exp_inner`:
  exact directional exponential moment by completing the square.
* `ZLattice.hasSubgaussianMGF_inner_discreteGaussian_zero`: any linear projection of a centered
  discrete Gaussian has sub-Gaussian MGF with variance proxy `(s * ‖u‖)² / (2π)`.
* `ZLattice.tsum_gaussianWeight_abs_inner_sub_ge_le`,
  `ZLattice.discreteGaussian_zero_abs_inner_ge_le`,
  `ZLattice.discreteGaussian_abs_inner_sub_ge_le_of_dual_mass_le`,
  `ZLattice.discreteGaussian_real_abs_sub_ge_le_of_dual_mass_le`,
  `ZLattice.discreteGaussian_abs_inner_sub_ge_le_of_smoothingParameter_le`,
  `ZLattice.discreteGaussian_real_abs_sub_ge_le_of_smoothingParameter_le`: one-dimensional
  directional and scalar discrete Gaussian Chernoff tails in both dual-mass and `η_ε(L) ≤ s`
  forms.

## References

* [Banaszczyk1993], Lemma 1.5(ii) (printed p. 630).
* [MicciancioRegev2007], Lemma 2.9 (p. 9), Lemma 2.10 (p. 9), Definition 3.1 (p. 10), and
  Lemma 4.4 (p. 15) of the December 27, 2005 author version.
* [Regev2009], Lemmas 2.4–2.5 (p. 16 of the May 2, 2009 author version).

The smoothing hypotheses are stated in both dual-mass form `gaussianMass D (1 / s) 0 - 1 ≤ ε`
(which also covers `ε = 0` in dimension zero) and smoothing-parameter form
`smoothingParameter L ε ≤ s` (for `0 < ε < 1`). Both sample-norm tail forms strengthen the
constant of [MicciancioRegev2007], Lemma 4.4 from `2 ^ (-n)` to strict `(1 / 4) ^ n`, matching
`Gaussian.CenteredTail`.
-/

public section

noncomputable section

open Module ProbabilityTheory MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace ZLattice

section Constants

/-- For `c > 1 / √(2π)`, Banaszczyk's base constant `c * √(2πe) * exp (-π c²)` is strictly
less than `1` ([MicciancioRegev2007], Lemma 2.10, p. 9). -/
theorem banaszczykConstant_lt_one {c : ℝ} (hc : 1 / Real.sqrt (2 * Real.pi) < c) :
    c * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * c ^ 2) < 1 := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hcpos : 0 < c := lt_trans (by positivity) hc
  have h1 : 1 < c * Real.sqrt (2 * Real.pi) := by
    rw [div_lt_iff₀ (Real.sqrt_pos.mpr h2pi)] at hc
    linarith
  have hu : 1 < 2 * Real.pi * c ^ 2 := by
    have hsq : 1 ^ 2 < (c * Real.sqrt (2 * Real.pi)) ^ 2 :=
      pow_lt_pow_left₀ h1 zero_le_one (by decide : 2 ≠ 0)
    rw [one_pow, mul_pow, Real.sq_sqrt h2pi.le] at hsq
    linarith
  have hexp : 2 * Real.pi * c ^ 2 < Real.exp (2 * Real.pi * c ^ 2 - 1) := by
    have h := Real.add_one_lt_exp (sub_ne_zero.mpr hu.ne')
    linarith
  have hsq_lt :
      (c * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * c ^ 2)) ^ 2 < 1 ^ 2 := by
    rw [one_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
    have hmul :
        Real.exp 1 * Real.exp ((2 : ℕ) * (-Real.pi * c ^ 2)) =
          Real.exp (1 - 2 * Real.pi * c ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    have hcomb :
        c ^ 2 * (2 * Real.pi * Real.exp 1) * Real.exp ((2 : ℕ) * (-Real.pi * c ^ 2)) =
          2 * Real.pi * c ^ 2 * Real.exp (1 - 2 * Real.pi * c ^ 2) := by
      calc
        c ^ 2 * (2 * Real.pi * Real.exp 1) * Real.exp ((2 : ℕ) * (-Real.pi * c ^ 2)) =
            2 * Real.pi * c ^ 2 * (Real.exp 1 * Real.exp ((2 : ℕ) * (-Real.pi * c ^ 2))) := by
          ring
        _ = 2 * Real.pi * c ^ 2 * Real.exp (1 - 2 * Real.pi * c ^ 2) := by rw [hmul]
    rw [hcomb, show 1 - 2 * Real.pi * c ^ 2 = -(2 * Real.pi * c ^ 2 - 1) by ring, Real.exp_neg,
      ← div_eq_mul_inv]
    exact (div_lt_one (Real.exp_pos _)).mpr hexp
  exact lt_of_pow_lt_pow_left₀ 2 zero_le_one hsq_lt

private theorem one_div_sqrt_two_pi_lt_one : 1 / Real.sqrt (2 * Real.pi) < 1 := by
  rw [div_lt_one (Real.sqrt_pos.mpr (by positivity))]
  exact Real.lt_sqrt_of_sq_lt (by linarith [Real.pi_gt_three])

private theorem banaszczykConstant_one_lt_quarter :
    1 * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * 1 ^ 2) < 1 / 4 := by
  have hpi_gt : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have he_gt : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have he5 : (2.7 : ℝ) ^ 5 < Real.exp 5 := by
    have hp := pow_lt_pow_left₀ he_gt (by norm_num : (0 : ℝ) ≤ 2.7) (by decide : 5 ≠ 0)
    rwa [← Real.exp_nat_mul, show ((5 : ℕ) : ℝ) * 1 = 5 by norm_num] at hp
  have he_exp : 32 * Real.pi < Real.exp (2 * Real.pi - 1) := by
    have h5 : Real.exp 5 < Real.exp (2 * Real.pi - 1) := Real.exp_lt_exp.mpr (by linarith)
    have hnum : (32 : ℝ) * 3.15 < (2.7 : ℝ) ^ 5 := by norm_num
    linarith
  have hsq :
      (1 * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * 1 ^ 2)) ^ 2 <
        (1 / 4 : ℝ) ^ 2 := by
    rw [one_mul, mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
    have hcomb :
        2 * Real.pi * Real.exp 1 * Real.exp ((2 : ℕ) * (-Real.pi * 1 ^ 2)) =
          2 * Real.pi / Real.exp (2 * Real.pi - 1) := by
      rw [mul_assoc, ← Real.exp_add, show 1 + ((2 : ℕ) : ℝ) * (-Real.pi * 1 ^ 2) =
        -(2 * Real.pi - 1) by push_cast; ring, Real.exp_neg, ← div_eq_mul_inv]
    rw [hcomb, div_lt_iff₀ (Real.exp_pos _)]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

end Constants

section DiscreteHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem discreteGaussian_toOuterMeasure_eq
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) (v : E) (S : Set L) :
    (discreteGaussian L s hs v).toOuterMeasure S =
      ENNReal.ofReal ((∑' z : S, gaussianWeight s ((z : E) - v)) / gaussianMass L s v) := by
  rw [PMF.toOuterMeasure_apply, ← tsum_subtype S (discreteGaussian L s hs v)]
  have hm := gaussianMass_pos L s hs v
  have hsum : Summable (fun z : S ↦ gaussianWeight s ((z : E) - v) / gaussianMass L s v) :=
    ((summable_gaussianWeight L s hs v).subtype (· ∈ S)).div_const _
  calc
    (∑' z : S, discreteGaussian L s hs v z) =
        ∑' z : S, ENNReal.ofReal (gaussianWeight s ((z : E) - v) / gaussianMass L s v) := by
      apply tsum_congr
      intro z
      rw [discreteGaussian_apply, ENNReal.ofReal_div_of_pos hm]
    _ = ENNReal.ofReal (∑' z : S, gaussianWeight s ((z : E) - v) / gaussianMass L s v) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun z ↦ div_nonneg (gaussianWeight_pos _ _).le hm.le) hsum).symm
    _ = ENNReal.ofReal ((∑' z : S, gaussianWeight s ((z : E) - v)) / gaussianMass L s v) := by
      rw [tsum_div_const]

end DiscreteHelpers

section BanaszczykTail

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Banaszczyk's shifted Gaussian tail bound** ([Banaszczyk1993], Lemma 1.5(ii), printed p. 630;
[MicciancioRegev2007], Lemma 2.10, p. 9 of the December 27, 2005 author version): for any
full-rank lattice `L`, width `s > 0`, center `v`, and `c > 1 / √(2π)`, the unnormalized Gaussian
mass of `L - v` strictly outside radius `c * s * √(finrank ℝ E)` is strictly less than
`(c * √(2πe) * exp (-π c²)) ^ (finrank ℝ E) * gaussianMass L s 0`.

This sharpens eq. (6) of [MicciancioRegev2007], Lemma 2.10 by removing the factor of `2`; the
centered case ([Banaszczyk1993], Lemma 1.5(i), eq. (5)) is `v = 0`. Holds in dimension zero as
well, where the strict tail event is empty. -/
theorem tsum_gaussianWeight_norm_sub_gt_lt
    (s : ℝ) (hs : 0 < s) (v : E) (c : ℝ) (hc : 1 / Real.sqrt (2 * Real.pi) < c) :
    (∑' z : ↥{z : L | c * s * Real.sqrt (finrank ℝ E) < ‖(z : E) - v‖},
      gaussianWeight s ((z : E) - v)) <
      (c * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * c ^ 2)) ^ finrank ℝ E *
        gaussianMass L s 0 := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hcpos : 0 < c := lt_trans (by positivity) hc
  have hCpos :
      0 < c * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * c ^ 2) := by
    positivity
  set S : Set L := {z : L | c * s * Real.sqrt (finrank ℝ E) < ‖(z : E) - v‖}
  by_cases hS : S.Nonempty
  · let t : ℝ := c * Real.sqrt (2 * Real.pi) * s
    have hc_sqrt : 1 < c * Real.sqrt (2 * Real.pi) := by
      rw [div_lt_iff₀ (Real.sqrt_pos.mpr h2pi)] at hc
      linarith
    have hst : s < t := by
      dsimp only [t]
      nlinarith
    have ht : 0 < t := hs.trans hst
    let R : ℝ := c * s * Real.sqrt (finrank ℝ E)
    have hR : 0 ≤ R := by positivity
    let κ : ℝ := Real.pi * (1 / s ^ 2 - 1 / t ^ 2)
    have hκ : 0 < κ := by
      apply mul_pos Real.pi_pos
      apply sub_pos.mpr
      apply one_div_lt_one_div_of_lt (sq_pos_of_pos hs)
      nlinarith
    have hpoint (z : S) :
        gaussianWeight s ((z : E) - v) <
          Real.exp (-κ * R ^ 2) * gaussianWeight t ((z : E) - v) := by
      have hgt : R < ‖(z : E) - v‖ := z.property
      have hsq : R ^ 2 < ‖(z : E) - v‖ ^ 2 := by
        nlinarith [norm_nonneg ((z : E) - v)]
      have hmul := gaussianWeight_mul_exp s t ((z : E) - v)
      have hexp_lt :
          Real.exp (-κ * ‖(z : E) - v‖ ^ 2) < Real.exp (-κ * R ^ 2) := by
        apply Real.exp_lt_exp.mpr
        nlinarith
      have hrewrite :
          gaussianWeight s ((z : E) - v) =
            Real.exp (-κ * ‖(z : E) - v‖ ^ 2) * gaussianWeight t ((z : E) - v) := by
        rw [← hmul, mul_comm (gaussianWeight s _), ← mul_assoc, ← Real.exp_add]
        have hzero : -κ * ‖(z : E) - v‖ ^ 2 + Real.pi * (1 / s ^ 2 - 1 / t ^ 2) *
            ‖(z : E) - v‖ ^ 2 = 0 := by
          dsimp only [κ]
          ring
        rw [hzero, Real.exp_zero, one_mul]
      rw [hrewrite]
      exact mul_lt_mul_of_pos_right hexp_lt (gaussianWeight_pos _ _)
    obtain ⟨z₀, hz₀⟩ := hS
    have hsum_s : Summable (fun z : S ↦ gaussianWeight s ((z : E) - v)) :=
      (summable_gaussianWeight L s hs v).subtype (· ∈ S)
    have hsum_t :
        Summable (fun z : S ↦ Real.exp (-κ * R ^ 2) * gaussianWeight t ((z : E) - v)) :=
      ((summable_gaussianWeight L t ht v).subtype (· ∈ S)).mul_left _
    have hlt :
        (∑' z : S, gaussianWeight s ((z : E) - v)) <
          Real.exp (-κ * R ^ 2) * (∑' z : S, gaussianWeight t ((z : E) - v)) := by
      rw [← tsum_mul_left]
      exact Summable.tsum_lt_tsum (i := ⟨z₀, hz₀⟩) (fun z ↦ (hpoint z).le) (hpoint ⟨z₀, hz₀⟩)
        hsum_s hsum_t
    have hsub_le : (∑' z : S, gaussianWeight t ((z : E) - v)) ≤ gaussianMass L t v :=
      ((summable_gaussianWeight L t ht v).subtype (· ∈ S)).tsum_le_tsum_of_inj Subtype.val
        Subtype.val_injective (fun _ _ ↦ (gaussianWeight_pos _ _).le) (fun _ ↦ le_rfl)
        (summable_gaussianWeight L t ht v)
    have hmass_t : gaussianMass L t v ≤ (t / s) ^ finrank ℝ E * gaussianMass L s 0 := by
      let _ : MeasurableSpace E := borel E
      have _ : BorelSpace E := ⟨rfl⟩
      have hdiv := gaussianMass_zero_div_le L s hs t hst.le
      have hzero : gaussianMass L t 0 ≤ (t / s) ^ finrank ℝ E * gaussianMass L s 0 :=
        (div_le_iff₀ (gaussianMass_pos L s hs 0)).mp hdiv
      exact (gaussianMass_le_gaussianMass_zero L t ht v).trans hzero
    have hconst :
        Real.exp (-κ * R ^ 2) * (t / s) ^ finrank ℝ E =
          (c * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * c ^ 2)) ^
            finrank ℝ E := by
      have hts : t / s = c * Real.sqrt (2 * Real.pi) := by
        dsimp only [t]
        field_simp
      have hRsq : R ^ 2 = c ^ 2 * s ^ 2 * (finrank ℝ E : ℝ) := by
        dsimp only [R]
        rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      have htsq : t ^ 2 = c ^ 2 * (2 * Real.pi) * s ^ 2 := by
        dsimp only [t]
        rw [mul_pow, mul_pow, Real.sq_sqrt h2pi.le]
      have hexp_arg : -κ * R ^ 2 = (finrank ℝ E : ℝ) * (1 / 2 - Real.pi * c ^ 2) := by
        dsimp only [κ]
        rw [hRsq, htsq]
        have hpi0 : Real.pi ≠ 0 := Real.pi_pos.ne'
        field_simp
        ring
      have hsqrt_e : Real.exp (1 / 2) = Real.sqrt (Real.exp 1) := by
        symm
        rw [Real.sqrt_eq_iff_eq_sq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_nat_mul]
        norm_num
      rw [hts, hexp_arg, Real.exp_nat_mul, ← mul_pow]
      congr 1
      rw [sub_eq_add_neg, Real.exp_add, hsqrt_e, Real.sqrt_mul h2pi.le, neg_mul]
      ring
    calc
      (∑' z : S, gaussianWeight s ((z : E) - v)) <
          Real.exp (-κ * R ^ 2) * (∑' z : S, gaussianWeight t ((z : E) - v)) := hlt
      _ ≤ Real.exp (-κ * R ^ 2) * gaussianMass L t v :=
        mul_le_mul_of_nonneg_left hsub_le (Real.exp_pos _).le
      _ ≤ Real.exp (-κ * R ^ 2) * ((t / s) ^ finrank ℝ E * gaussianMass L s 0) :=
        mul_le_mul_of_nonneg_left hmass_t (Real.exp_pos _).le
      _ = (Real.exp (-κ * R ^ 2) * (t / s) ^ finrank ℝ E) * gaussianMass L s 0 := by ring
      _ = (c * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * c ^ 2)) ^
            finrank ℝ E * gaussianMass L s 0 := by rw [hconst]
  · rw [Set.not_nonempty_iff_eq_empty] at hS
    have : IsEmpty S := by rw [hS]; infer_instance
    rw [tsum_empty]
    exact mul_pos (pow_pos hCpos _) (gaussianMass_pos L s hs 0)

/-- **Shifted Regev Lemma 2.5** ([Regev2009], Lemma 2.5, p. 16, extended to arbitrary center `v`
via [Banaszczyk1993], Lemma 1.5(ii), printed p. 630 / [MicciancioRegev2007], Lemma 2.10): for any
full-rank lattice `L`, width `s > 0`, and center `v`, the unnormalized Gaussian mass strictly
outside radius `s * √(finrank ℝ E)` is strictly less than
`(1 / 4) ^ (finrank ℝ E) * gaussianMass L s 0`. Setting `v = 0` recovers the centered bound in
`Gaussian.CenteredTail`. -/
theorem tsum_gaussianWeight_norm_sub_gt_sqrt_lt
    (s : ℝ) (hs : 0 < s) (v : E) :
    (∑' z : ↥{z : L | s * Real.sqrt (finrank ℝ E) < ‖(z : E) - v‖},
      gaussianWeight s ((z : E) - v)) <
      (1 / 4 : ℝ) ^ finrank ℝ E * gaussianMass L s 0 := by
  have h := tsum_gaussianWeight_norm_sub_gt_lt L s hs v 1 one_div_sqrt_two_pi_lt_one
  have hset : {z : L | 1 * s * Real.sqrt (finrank ℝ E) < ‖(z : E) - v‖} =
      {z : L | s * Real.sqrt (finrank ℝ E) < ‖(z : E) - v‖} := by
    ext z
    simp only [Set.mem_ofPred_eq, one_mul]
  rw [hset] at h
  have hpow :
      (1 * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * 1 ^ 2)) ^ finrank ℝ E ≤
        (1 / 4 : ℝ) ^ finrank ℝ E :=
    pow_le_pow_left₀ (by positivity) banaszczykConstant_one_lt_quarter.le _
  exact h.trans_le (mul_le_mul_of_nonneg_right hpow (gaussianMass_pos L s hs 0).le)

/-- Under a dual-mass bound `ρ_{1/s}(L* \ {0}) ≤ ε < 1`, the ratio of Gaussian masses at any two
centers is at most `(1 + ε) / (1 - ε)`. Nonnegativity of `ε` follows automatically from
`0 ≤ ρ_{1/s}(L* \ {0})`. -/
theorem gaussianMass_div_le_of_dual_mass_le
    (s : ℝ) (hs : 0 < s) (ε : ℝ) (hεlt : ε < 1)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ≤ ε)
    (c₁ c₂ : E) :
    gaussianMass L s c₁ / gaussianMass L s c₂ ≤ (1 + ε) / (1 - ε) := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have _ : DiscreteTopology (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) :=
    discreteTopology_dualSubmodule L
  have hε0 : 0 ≤ ε :=
    (gaussianMass_zero_sub_one_nonneg _ (1 / s) (one_div_pos.mpr hs)).trans hdual
  have h1 := (abs_le.mp ((abs_gaussianMass_normalized_sub_one_le L s hs c₁).trans hdual)).2
  have h2 := (abs_le.mp ((abs_gaussianMass_normalized_sub_one_le L s hs c₂).trans hdual)).1
  set α : ℝ := covolume L / s ^ finrank ℝ E
  have hα : 0 < α := div_pos (covolume_pos L volume) (pow_pos hs _)
  have h1m : 0 < 1 - ε := sub_pos.mpr hεlt
  have h1p : 0 ≤ 1 + ε := by linarith
  have hm1 : α * gaussianMass L s c₁ ≤ 1 + ε := by linarith
  have hm2 : 1 - ε ≤ α * gaussianMass L s c₂ := by linarith
  calc
    gaussianMass L s c₁ / gaussianMass L s c₂ =
        (α * gaussianMass L s c₁) / (α * gaussianMass L s c₂) :=
      (mul_div_mul_left _ _ hα.ne').symm
    _ ≤ (1 + ε) / (1 - ε) := div_le_div₀ h1p hm1 h1m hm2

/-- General-radius off-center discrete Gaussian sample-norm tail bound in dual-mass form (the
dual-mass step toward the `η_ε`-parameterized tail bound, not the `η_ε` endpoint itself),
combining [Banaszczyk1993], Lemma 1.5(ii) (printed p. 630) / [MicciancioRegev2007], Lemma 2.10
with `ρ_{1/s}(L* \ {0}) ≤ ε < 1`. -/
theorem discreteGaussian_norm_sub_gt_lt_of_dual_mass_le
    (s : ℝ) (hs : 0 < s) (v : E) (c : ℝ) (hc : 1 / Real.sqrt (2 * Real.pi) < c)
    (ε : ℝ) (hεlt : ε < 1)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ≤ ε) :
    (discreteGaussian L s hs v).toOuterMeasure
      {z : L | c * s * Real.sqrt (finrank ℝ E) < ‖(z : E) - v‖} <
      ENNReal.ofReal ((1 + ε) / (1 - ε) *
        (c * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * c ^ 2)) ^
          finrank ℝ E) := by
  have _ : DiscreteTopology (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) :=
    discreteTopology_dualSubmodule L
  have hε0 : 0 ≤ ε :=
    (gaussianMass_zero_sub_one_nonneg _ (1 / s) (one_div_pos.mpr hs)).trans hdual
  have hcpos : 0 < c := lt_trans (by positivity) hc
  have hCpos :
      0 < c * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * c ^ 2) := by
    positivity
  have h1m : 0 < 1 - ε := sub_pos.mpr hεlt
  have h1p : 0 < 1 + ε := by linarith
  have hm := gaussianMass_pos L s hs v
  rw [discreteGaussian_toOuterMeasure_eq]
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
  have htail := tsum_gaussianWeight_norm_sub_gt_lt L s hs v c hc
  have hratio := gaussianMass_div_le_of_dual_mass_le L s hs ε hεlt hdual 0 v
  calc
    (∑' z : ↥{z : L | c * s * Real.sqrt (finrank ℝ E) < ‖(z : E) - v‖},
        gaussianWeight s ((z : E) - v)) / gaussianMass L s v <
      ((c * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * c ^ 2)) ^ finrank ℝ E *
        gaussianMass L s 0) / gaussianMass L s v :=
      div_lt_div_of_pos_right htail hm
    _ = (gaussianMass L s 0 / gaussianMass L s v) *
        (c * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * c ^ 2)) ^ finrank ℝ E := by
      ring
    _ ≤ (1 + ε) / (1 - ε) *
        (c * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * c ^ 2)) ^ finrank ℝ E :=
      mul_le_mul_of_nonneg_right hratio (pow_pos hCpos _).le

/-- Dual-mass step toward [MicciancioRegev2007], Lemma 4.4 (p. 15 of the December 27, 2005
author version), stated directly under `ρ_{1/s}(L* \ {0}) ≤ ε < 1` rather than the `η_ε(L) ≤ s`
endpoint. This strengthens the source's `≤ ((1 + ε) / (1 - ε)) * 2 ^ (-n)` constant to strict
`< ((1 + ε) / (1 - ε)) * (1 / 4) ^ n` via Poisson positivity, matching `Gaussian.CenteredTail`.
Holds in dimension zero as well, where the strict tail event is empty. -/
theorem discreteGaussian_norm_sub_gt_sqrt_lt_of_dual_mass_le
    (s : ℝ) (hs : 0 < s) (v : E) (ε : ℝ) (hεlt : ε < 1)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ≤ ε) :
    (discreteGaussian L s hs v).toOuterMeasure
      {z : L | s * Real.sqrt (finrank ℝ E) < ‖(z : E) - v‖} <
      ENNReal.ofReal ((1 + ε) / (1 - ε) * (1 / 4 : ℝ) ^ finrank ℝ E) := by
  have h := discreteGaussian_norm_sub_gt_lt_of_dual_mass_le L s hs v 1 one_div_sqrt_two_pi_lt_one
    ε hεlt hdual
  have hset : {z : L | 1 * s * Real.sqrt (finrank ℝ E) < ‖(z : E) - v‖} =
      {z : L | s * Real.sqrt (finrank ℝ E) < ‖(z : E) - v‖} := by
    ext z
    simp only [Set.mem_ofPred_eq, one_mul]
  rw [hset] at h
  have _ : DiscreteTopology (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) :=
    discreteTopology_dualSubmodule L
  have hε0 : 0 ≤ ε :=
    (gaussianMass_zero_sub_one_nonneg _ (1 / s) (one_div_pos.mpr hs)).trans hdual
  have hratio_nn : 0 ≤ (1 + ε) / (1 - ε) := div_nonneg (by linarith) (sub_pos.mpr hεlt).le
  exact h.trans_le (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) banaszczykConstant_one_lt_quarter.le _) hratio_nn))

/-- Above the smoothing parameter `η_ε(L) ≤ s` with `0 < ε < 1`, the ratio of Gaussian masses at
any two centers is at most `(1 + ε) / (1 - ε)`. -/
theorem gaussianMass_div_le_of_smoothingParameter_le
    (s : ℝ) (hs : 0 < s) (ε : ℝ) (hε0 : 0 < ε) (hεlt : ε < 1)
    (hη : smoothingParameter L ε ≤ s) (c₁ c₂ : E) :
    gaussianMass L s c₁ / gaussianMass L s c₂ ≤ (1 + ε) / (1 - ε) :=
  gaussianMass_div_le_of_dual_mass_le L s hs ε hεlt
    ((smoothingParameter_le_iff L hs hε0).mp hη) c₁ c₂

/-- General-radius off-center discrete Gaussian norm tail bound above the smoothing parameter
`η_ε(L) ≤ s` (`0 < ε < 1`, `c > 1 / √(2π)`). -/
theorem discreteGaussian_norm_sub_gt_lt_of_smoothingParameter_le
    (s : ℝ) (hs : 0 < s) (v : E) (c : ℝ) (hc : 1 / Real.sqrt (2 * Real.pi) < c)
    (ε : ℝ) (hε0 : 0 < ε) (hεlt : ε < 1) (hη : smoothingParameter L ε ≤ s) :
    (discreteGaussian L s hs v).toOuterMeasure
      {z : L | c * s * Real.sqrt (finrank ℝ E) < ‖(z : E) - v‖} <
      ENNReal.ofReal ((1 + ε) / (1 - ε) *
        (c * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * c ^ 2)) ^
          finrank ℝ E) :=
  discreteGaussian_norm_sub_gt_lt_of_dual_mass_le L s hs v c hc ε hεlt
    ((smoothingParameter_le_iff L hs hε0).mp hη)

/-- Off-center discrete Gaussian norm tail bound above the smoothing parameter `η_ε(L) ≤ s`
([MicciancioRegev2007], Lemma 4.4, p. 15 of the December 27, 2005 author's copy, sharpened from
`2 ^ (-n)` to strict `(1 / 4) ^ n`). -/
theorem discreteGaussian_norm_sub_gt_sqrt_lt_of_smoothingParameter_le
    (s : ℝ) (hs : 0 < s) (v : E) (ε : ℝ) (hε0 : 0 < ε) (hεlt : ε < 1)
    (hη : smoothingParameter L ε ≤ s) :
    (discreteGaussian L s hs v).toOuterMeasure
      {z : L | s * Real.sqrt (finrank ℝ E) < ‖(z : E) - v‖} <
      ENNReal.ofReal ((1 + ε) / (1 - ε) * (1 / 4 : ℝ) ^ finrank ℝ E) :=
  discreteGaussian_norm_sub_gt_sqrt_lt_of_dual_mass_le L s hs v ε hεlt
    ((smoothingParameter_le_iff L hs hε0).mp hη)

end BanaszczykTail

section OneDimensionalTails

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem gaussianWeight_mul_exp_inner (s : ℝ) (hs : 0 < s) (x u : E) (t : ℝ) :
    gaussianWeight s x * Real.exp (t * ⟪x, u⟫) =
      Real.exp ((s * ‖u‖) ^ 2 / (2 * Real.pi) * t ^ 2 / 2) *
        gaussianWeight s (x - (t * s ^ 2 / (2 * Real.pi)) • u) := by
  unfold gaussianWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hs0 : s ≠ 0 := hs.ne'
  field_simp
  ring

omit [FiniteDimensional ℝ E] in
private theorem gaussianWeight_mul_exp_inner_fun (L : Submodule ℤ E) (s : ℝ) (hs : 0 < s)
    (c u : E) (t : ℝ) :
    (fun z : L ↦ gaussianWeight s ((z : E) - c) * Real.exp (t * ⟪(z : E) - c, u⟫)) =
      (fun z : L ↦ Real.exp ((s * ‖u‖) ^ 2 / (2 * Real.pi) * t ^ 2 / 2) *
        gaussianWeight s ((z : E) - (c + (t * s ^ 2 / (2 * Real.pi)) • u))) := by
  funext z
  rw [gaussianWeight_mul_exp_inner s hs ((z : E) - c) u t, sub_sub]

/-- The directional exponential moment of a lattice Gaussian is summable for every discrete
subgroup `L` and real tilt `t`. -/
theorem summable_gaussianWeight_mul_exp_inner
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) (c u : E) (t : ℝ) :
    Summable (fun z : L ↦ gaussianWeight s ((z : E) - c) * Real.exp (t * ⟪(z : E) - c, u⟫)) := by
  rw [gaussianWeight_mul_exp_inner_fun L s hs c u t]
  exact (summable_gaussianWeight L s hs _).mul_left _

omit [FiniteDimensional ℝ E] in
/-- Exact directional exponential moment of a lattice Gaussian by completing the square. -/
theorem tsum_gaussianWeight_mul_exp_inner
    (L : Submodule ℤ E) (s : ℝ) (hs : 0 < s) (c u : E) (t : ℝ) :
    (∑' z : L, gaussianWeight s ((z : E) - c) * Real.exp (t * ⟪(z : E) - c, u⟫)) =
      Real.exp ((s * ‖u‖) ^ 2 / (2 * Real.pi) * t ^ 2 / 2) *
        gaussianMass L s (c + (t * s ^ 2 / (2 * Real.pi)) • u) := by
  rw [gaussianWeight_mul_exp_inner_fun L s hs c u t, tsum_mul_left]
  rfl

/-- Any linear projection `z ↦ ⟪(z : E), u⟫` under the centered discrete Gaussian `D_{L, s, 0}`
has sub-Gaussian MGF with variance proxy `(s * ‖u‖)² / (2π)`. This follows directly from the
completing-the-square MGF identity (`tsum_gaussianWeight_mul_exp_inner`) and shifted-vs-centered
mass monotonicity ([MicciancioRegev2007], Lemma 2.9, p. 9). -/
theorem hasSubgaussianMGF_inner_discreteGaussian_zero
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L]
    (s : ℝ) (hs : 0 < s) (u : E) :
    HasSubgaussianMGF (fun z : L ↦ ⟪(z : E), u⟫)
      (((s * ‖u‖) ^ 2 / (2 * Real.pi)).toNNReal)
      (discreteGaussian L s hs 0).toMeasure := by
  have _ : Countable L := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hm := gaussianMass_pos L s hs 0
  have hint (t : ℝ) :
      Integrable (fun z : L ↦ Real.exp (t * ⟪(z : E), u⟫))
        (discreteGaussian L s hs 0).toMeasure := by
    have hcont : Continuous (fun z : L ↦ Real.exp (t * ⟪(z : E), u⟫)) :=
      Real.continuous_exp.comp
        (continuous_const.mul (continuous_subtype_val.inner continuous_const))
    refine ⟨hcont.measurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun z ↦ (Real.exp_pos _).le)),
      lintegral_countable']
    have hsum :
        Summable (fun z : L ↦ (discreteGaussian L s hs 0 z).toReal *
          Real.exp (t * ⟪(z : E), u⟫)) := by
      simpa only [discreteGaussian_apply_toReal, sub_zero, div_mul_eq_mul_div] using
        (summable_gaussianWeight_mul_exp_inner L s hs 0 u t).div_const (gaussianMass L s 0)
    have heq :
        (∑' z : L, ENNReal.ofReal (Real.exp (t * ⟪(z : E), u⟫)) *
            (discreteGaussian L s hs 0).toMeasure {z}) =
          ENNReal.ofReal (∑' z : L, (discreteGaussian L s hs 0 z).toReal *
            Real.exp (t * ⟪(z : E), u⟫)) := by
      rw [ENNReal.ofReal_tsum_of_nonneg
        (fun z ↦ mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) hsum]
      apply tsum_congr
      intro z
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (PMF.apply_ne_top _ _), mul_comm]
    rw [heq]
    exact ENNReal.ofReal_lt_top
  refine ⟨hint, fun t ↦ ?_⟩
  rw [mgf, PMF.integral_eq_tsum _ _ (hint t)]
  simp only [smul_eq_mul, discreteGaussian_apply_toReal, sub_zero, div_mul_eq_mul_div]
  rw [tsum_div_const]
  have htsum := tsum_gaussianWeight_mul_exp_inner L s hs 0 u t
  simp only [sub_zero, zero_add] at htsum
  rw [htsum, Real.coe_toNNReal _ (by positivity), mul_div_assoc]
  exact mul_le_of_le_one_right (Real.exp_pos _).le
    ((div_le_one hm).mpr (gaussianMass_le_gaussianMass_zero L s hs _))

private theorem tsum_gaussianWeight_inner_sub_ge_le
    (L : Submodule ℤ E) [DiscreteTopology L]
    (s : ℝ) (hs : 0 < s) (c : E) {u : E} (hu : u ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (∑' z : ↥{z : L | t * s * ‖u‖ ≤ ⟪(z : E) - c, u⟫}, gaussianWeight s ((z : E) - c)) ≤
      Real.exp (-Real.pi * t ^ 2) * gaussianMass L s 0 := by
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let lam : ℝ := 2 * Real.pi * t / (s * ‖u‖)
  have hlam : 0 ≤ lam := by positivity
  set S : Set L := {z : L | t * s * ‖u‖ ≤ ⟪(z : E) - c, u⟫}
  have hpoint (z : S) :
      gaussianWeight s ((z : E) - c) ≤
        Real.exp (-2 * Real.pi * t ^ 2) *
          (gaussianWeight s ((z : E) - c) * Real.exp (lam * ⟪(z : E) - c, u⟫)) := by
    have hz : t * s * ‖u‖ ≤ ⟪(z : E) - c, u⟫ := z.property
    have hmul : 2 * Real.pi * t ^ 2 ≤ lam * ⟪(z : E) - c, u⟫ := by
      have h1 := mul_le_mul_of_nonneg_left hz hlam
      have h2 : lam * (t * s * ‖u‖) = 2 * Real.pi * t ^ 2 := by
        dsimp only [lam]
        field_simp
      linarith
    have hexp : 1 ≤ Real.exp (-2 * Real.pi * t ^ 2) * Real.exp (lam * ⟪(z : E) - c, u⟫) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      linarith
    calc
      gaussianWeight s ((z : E) - c) = gaussianWeight s ((z : E) - c) * 1 := (mul_one _).symm
      _ ≤ gaussianWeight s ((z : E) - c) *
          (Real.exp (-2 * Real.pi * t ^ 2) * Real.exp (lam * ⟪(z : E) - c, u⟫)) :=
        mul_le_mul_of_nonneg_left hexp (gaussianWeight_pos _ _).le
      _ = Real.exp (-2 * Real.pi * t ^ 2) *
          (gaussianWeight s ((z : E) - c) * Real.exp (lam * ⟪(z : E) - c, u⟫)) := by ring
  have hsum_full := summable_gaussianWeight_mul_exp_inner L s hs c u lam
  have h1 :
      (∑' z : S, gaussianWeight s ((z : E) - c)) ≤
        Real.exp (-2 * Real.pi * t ^ 2) *
          (∑' z : S, gaussianWeight s ((z : E) - c) * Real.exp (lam * ⟪(z : E) - c, u⟫)) := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hpoint ((summable_gaussianWeight L s hs c).subtype (· ∈ S))
      ((hsum_full.subtype (· ∈ S)).mul_left _)
  have h2 :
      (∑' z : S, gaussianWeight s ((z : E) - c) * Real.exp (lam * ⟪(z : E) - c, u⟫)) ≤
        ∑' z : L, gaussianWeight s ((z : E) - c) * Real.exp (lam * ⟪(z : E) - c, u⟫) :=
    (hsum_full.subtype (· ∈ S)).tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
      (fun _ _ ↦ mul_nonneg (gaussianWeight_pos _ _).le (Real.exp_pos _).le) (fun _ ↦ le_rfl)
      hsum_full
  have h3 :
      Real.exp (-2 * Real.pi * t ^ 2) *
          Real.exp ((s * ‖u‖) ^ 2 / (2 * Real.pi) * lam ^ 2 / 2) =
        Real.exp (-Real.pi * t ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [lam]
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hs0 : s ≠ 0 := hs.ne'
    have hu0 : ‖u‖ ≠ 0 := hun.ne'
    field_simp
    ring
  calc
    (∑' z : S, gaussianWeight s ((z : E) - c)) ≤
        Real.exp (-2 * Real.pi * t ^ 2) *
          (∑' z : L, gaussianWeight s ((z : E) - c) * Real.exp (lam * ⟪(z : E) - c, u⟫)) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
    _ = (Real.exp (-2 * Real.pi * t ^ 2) *
          Real.exp ((s * ‖u‖) ^ 2 / (2 * Real.pi) * lam ^ 2 / 2)) *
          gaussianMass L s (c + (lam * s ^ 2 / (2 * Real.pi)) • u) := by
      rw [tsum_gaussianWeight_mul_exp_inner L s hs c u lam, ← mul_assoc]
    _ = Real.exp (-Real.pi * t ^ 2) *
          gaussianMass L s (c + (lam * s ^ 2 / (2 * Real.pi)) • u) := by rw [h3]
    _ ≤ Real.exp (-Real.pi * t ^ 2) * gaussianMass L s 0 :=
      mul_le_mul_of_nonneg_left (gaussianMass_le_gaussianMass_zero L s hs _) (Real.exp_pos _).le

/-- Unnormalized two-sided one-dimensional directional tail of a shifted lattice Gaussian:
for any nonzero `u` and `t ≥ 0`, the mass of `{z ∈ L | t * s * ‖u‖ ≤ |⟪z - c, u⟫|}` is at most
`2 * exp (-π * t²) * gaussianMass L s 0`. -/
theorem tsum_gaussianWeight_abs_inner_sub_ge_le
    (L : Submodule ℤ E) [DiscreteTopology L]
    (s : ℝ) (hs : 0 < s) (c : E) {u : E} (hu : u ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (∑' z : ↥{z : L | t * s * ‖u‖ ≤ |⟪(z : E) - c, u⟫|}, gaussianWeight s ((z : E) - c)) ≤
      2 * Real.exp (-Real.pi * t ^ 2) * gaussianMass L s 0 := by
  classical
  set S : Set L := {z : L | t * s * ‖u‖ ≤ |⟪(z : E) - c, u⟫|}
  set S₁ : Set L := {z : L | t * s * ‖u‖ ≤ ⟪(z : E) - c, u⟫}
  set S₂ : Set L := {z : L | t * s * ‖-u‖ ≤ ⟪(z : E) - c, -u⟫}
  let g : L → ℝ := fun w ↦ gaussianWeight s ((w : E) - c)
  have hsum : Summable g := summable_gaussianWeight L s hs c
  have hpoint (z : L) : S.indicator g z ≤ S₁.indicator g z + S₂.indicator g z := by
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]
      have habs : t * s * ‖u‖ ≤ |⟪(z : E) - c, u⟫| := hz
      rcases le_or_gt 0 ⟪(z : E) - c, u⟫ with hpos | hneg
      · have hz1 : z ∈ S₁ := by
          change t * s * ‖u‖ ≤ ⟪(z : E) - c, u⟫
          rwa [abs_of_nonneg hpos] at habs
        rw [Set.indicator_of_mem hz1]
        have hnn : 0 ≤ S₂.indicator g z :=
          Set.indicator_nonneg (fun w _ ↦ (gaussianWeight_pos _ _).le) z
        linarith
      · have hz2 : z ∈ S₂ := by
          change t * s * ‖-u‖ ≤ ⟪(z : E) - c, -u⟫
          rw [norm_neg, inner_neg_right]
          rwa [abs_of_neg hneg] at habs
        rw [Set.indicator_of_mem hz2]
        have hnn : 0 ≤ S₁.indicator g z :=
          Set.indicator_nonneg (fun w _ ↦ (gaussianWeight_pos _ _).le) z
        linarith
    · rw [Set.indicator_of_notMem hz]
      exact add_nonneg
        (Set.indicator_nonneg (fun w _ ↦ (gaussianWeight_pos _ _).le) z)
        (Set.indicator_nonneg (fun w _ ↦ (gaussianWeight_pos _ _).le) z)
  have htsum_le : (∑' z : S, g z) ≤ (∑' z : S₁, g z) + (∑' z : S₂, g z) := by
    rw [tsum_subtype S g, tsum_subtype S₁ g, tsum_subtype S₂ g,
      ← Summable.tsum_add (hsum.indicator S₁) (hsum.indicator S₂)]
    exact Summable.tsum_le_tsum hpoint (hsum.indicator S)
      ((hsum.indicator S₁).add (hsum.indicator S₂))
  have hb1 := tsum_gaussianWeight_inner_sub_ge_le L s hs c hu ht
  have hb2 := tsum_gaussianWeight_inner_sub_ge_le L s hs c (neg_ne_zero.mpr hu) ht
  change (∑' z : S, g z) ≤ _
  linarith

/-- Two-sided one-dimensional directional tail of a centered discrete Gaussian (no smoothing
hypothesis needed). -/
theorem discreteGaussian_zero_abs_inner_ge_le
    (L : Submodule ℤ E) [DiscreteTopology L]
    (s : ℝ) (hs : 0 < s) {u : E} (hu : u ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (discreteGaussian L s hs 0).toOuterMeasure
      {z : L | t * s * ‖u‖ ≤ |⟪(z : E), u⟫|} ≤
      ENNReal.ofReal (2 * Real.exp (-Real.pi * t ^ 2)) := by
  have h := tsum_gaussianWeight_abs_inner_sub_ge_le L s hs 0 hu ht
  have hset : {z : L | t * s * ‖u‖ ≤ |⟪(z : E) - 0, u⟫|} =
      {z : L | t * s * ‖u‖ ≤ |⟪(z : E), u⟫|} := by
    ext z
    simp only [Set.mem_ofPred_eq, sub_zero]
  rw [hset] at h
  simp only [sub_zero] at h
  have heq := discreteGaussian_toOuterMeasure_eq L s hs 0 {z : L | t * s * ‖u‖ ≤ |⟪(z : E), u⟫|}
  simp only [sub_zero] at heq
  rw [heq]
  apply ENNReal.ofReal_le_ofReal
  exact (div_le_iff₀ (gaussianMass_pos L s hs 0)).mpr h

/-- Two-sided one-dimensional directional tail of an off-center discrete Gaussian under a
dual-mass bound `ρ_{1/s}(L* \ {0}) ≤ ε < 1`. -/
theorem discreteGaussian_abs_inner_sub_ge_le_of_dual_mass_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c : E) {u : E} (hu : u ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (ε : ℝ) (hεlt : ε < 1)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ≤ ε) :
    (discreteGaussian L s hs c).toOuterMeasure
      {z : L | t * s * ‖u‖ ≤ |⟪(z : E) - c, u⟫|} ≤
      ENNReal.ofReal ((1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * t ^ 2))) := by
  rw [discreteGaussian_toOuterMeasure_eq]
  apply ENNReal.ofReal_le_ofReal
  have hm := gaussianMass_pos L s hs c
  have htail := tsum_gaussianWeight_abs_inner_sub_ge_le L s hs c hu ht
  have hratio := gaussianMass_div_le_of_dual_mass_le L s hs ε hεlt hdual 0 c
  calc
    (∑' z : ↥{z : L | t * s * ‖u‖ ≤ |⟪(z : E) - c, u⟫|},
        gaussianWeight s ((z : E) - c)) / gaussianMass L s c ≤
      (2 * Real.exp (-Real.pi * t ^ 2) * gaussianMass L s 0) / gaussianMass L s c := by gcongr
    _ = (gaussianMass L s 0 / gaussianMass L s c) * (2 * Real.exp (-Real.pi * t ^ 2)) := by
      ring
    _ ≤ (1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * t ^ 2)) := by gcongr

/-- One-dimensional off-center discrete Gaussian tail on a lattice `L ⊆ ℝ` under a dual-mass
bound `ρ_{1/s}(L* \ {0}) ≤ ε < 1`. -/
theorem discreteGaussian_real_abs_sub_ge_le_of_dual_mass_le
    (L : Submodule ℤ ℝ) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (ε : ℝ) (hεlt : ε < 1)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) L) (1 / s) 0 - 1 ≤ ε) :
    (discreteGaussian L s hs c).toOuterMeasure {z : L | t * s ≤ |(z : ℝ) - c|} ≤
      ENNReal.ofReal ((1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * t ^ 2))) := by
  have h := discreteGaussian_abs_inner_sub_ge_le_of_dual_mass_le L s hs c
    (u := (1 : ℝ)) one_ne_zero ht ε hεlt hdual
  have hset : {z : L | t * s * ‖(1 : ℝ)‖ ≤ |⟪(z : ℝ) - c, (1 : ℝ)⟫|} =
      {z : L | t * s ≤ |(z : ℝ) - c|} := by
    ext z
    simp only [Set.mem_ofPred_eq, norm_one, mul_one, RCLike.inner_apply, conj_trivial, one_mul]
  rwa [hset] at h

/-- One-dimensional directional off-center discrete Gaussian tail bound above `η_ε(L) ≤ s`
(`0 < ε < 1`, `u ≠ 0`, `t ≥ 0`). -/
theorem discreteGaussian_abs_inner_sub_ge_le_of_smoothingParameter_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c : E) {u : E} (hu : u ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (ε : ℝ) (hε0 : 0 < ε) (hεlt : ε < 1) (hη : smoothingParameter L ε ≤ s) :
    (discreteGaussian L s hs c).toOuterMeasure
      {z : L | t * s * ‖u‖ ≤ |⟪(z : E) - c, u⟫|} ≤
      ENNReal.ofReal ((1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * t ^ 2))) :=
  discreteGaussian_abs_inner_sub_ge_le_of_dual_mass_le L s hs c hu ht ε hεlt
    ((smoothingParameter_le_iff L hs hε0).mp hη)

/-- Scalar one-dimensional off-center discrete Gaussian tail bound above `η_ε(L) ≤ s`
(`0 < ε < 1`, `t ≥ 0`). -/
theorem discreteGaussian_real_abs_sub_ge_le_of_smoothingParameter_le
    (L : Submodule ℤ ℝ) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (ε : ℝ) (hε0 : 0 < ε) (hεlt : ε < 1) (hη : smoothingParameter L ε ≤ s) :
    (discreteGaussian L s hs c).toOuterMeasure {z : L | t * s ≤ |(z : ℝ) - c|} ≤
      ENNReal.ofReal ((1 + ε) / (1 - ε) * (2 * Real.exp (-Real.pi * t ^ 2))) :=
  discreteGaussian_real_abs_sub_ge_le_of_dual_mass_le L s hs c ht ε hεlt
    ((smoothingParameter_le_iff L hs hε0).mp hη)

end OneDimensionalTails

end ZLattice
