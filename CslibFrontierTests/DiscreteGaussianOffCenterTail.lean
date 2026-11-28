/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.MeasureTheory.Group.FundamentalDomain
import CslibFrontier.Foundations.Probability.Gaussian.OffCenterTail
import CslibFrontier.Foundations.Probability.Gaussian.Quotient
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Non-vacuous `module` client tests for off-center Banaszczyk tails, one-dimensional discrete
Gaussian bounds, MR07 Lemma 4.4 (both dual-mass and `η_ε(L) ≤ s` forms), and arbitrary-center
quotient uniformity (MR07 Lemma 4.1, both dual-mass and `η_ε(L) ≤ s` forms) on concrete lattices
in dimensions 1, 2, and 0.
-/

set_option linter.privateModule false

open Module ProbabilityTheory MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace CslibFrontierTests.DiscreteGaussianOffCenterTail

private theorem basis_domain_op {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Finite ι]
    (b : Basis ι ℝ E) :
    IsAddFundamentalDomain (Submodule.span ℤ (Set.range b)).toAddSubgroup.op
      (ZSpan.fundamentalDomain b) volume :=
  isAddFundamentalDomain_op_iff.mpr (ZSpan.isAddFundamentalDomain' b volume)

/-! ### Dimension 1: non-unit lattice `2ℤ ⊂ ℝ` at off-lattice center `1` -/

/-- One-dimensional basis of length `2` spanning `2ℤ ⊂ ℝ`. -/
private def twoBasis : Basis Unit ℝ ℝ :=
  (Basis.singleton Unit ℝ).isUnitSMul (fun _ => (show (2 : ℝ) ≠ 0 by norm_num).isUnit)

/-- The non-unit one-dimensional lattice `2ℤ ⊂ ℝ`. -/
private abbrev L1 := Submodule.span ℤ (Set.range twoBasis)
private abbrev D1 := LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) L1

private instance : DiscreteTopology D1 := ZLattice.discreteTopology_dualSubmodule L1
private instance : IsZLattice ℝ D1 := ZLattice.isZLattice_dualSubmodule L1

private theorem dual_gap1 (w : D1) (hw : w ≠ 0) : (1 / 2 : ℝ) ≤ ‖(w : ℝ)‖ := by
  have hm := w.property (twoBasis ()) (Submodule.subset_span (Set.mem_range_self ()))
  obtain ⟨k, hk⟩ := Submodule.mem_one.mp hm
  have hk' : (k : ℝ) = (w : ℝ) * 2 := by
    simpa [twoBasis, Basis.isUnitSMul_apply, real_inner_comm, mul_comm] using hk
  have hkn : k ≠ 0 := by
    intro h
    apply hw
    apply Subtype.ext
    change (w : ℝ) = 0
    rw [h, Int.cast_zero] at hk'
    linarith
  have ha : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast (Int.one_le_abs hkn)
  rw [hk', abs_mul] at ha
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ha
  rw [Real.norm_eq_abs]
  linarith

private theorem dual_small1 : ZLattice.gaussianMass D1 (1 / 2) 0 - 1 ≤ 1 / 2 := by
  apply ZLattice.gaussianMass_dual_sub_one_le_of_gap L1 2 (by norm_num)
    (1 / 2) (by norm_num) dual_gap1 (1 / 2) (by norm_num)
  have hpi : 4 * Real.log 2 < Real.pi := by linarith [Real.log_two_lt_d9, Real.pi_gt_three]
  have he := Real.exp_lt_exp.mpr (show -3 * Real.pi / 4 < -3 * Real.log 2 by linarith)
  have hr : Real.exp (-3 * Real.log 2) = (1 / 8 : ℝ) := by
    rw [show -3 * Real.log 2 = -((3 : ℕ) * Real.log 2) by ring, Real.exp_neg,
      Real.exp_natCast_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hr] at he
  have hbound : (2 : ℝ) * Real.exp (-3 * Real.pi / 4) ≤ 1 / 3 := by linarith
  have hexp : -3 * Real.pi * (2 : ℝ) ^ 2 * (1 / 2) ^ 2 / 4 = -3 * Real.pi / 4 := by ring
  simpa only [finrank_self, pow_one, hexp,
    show (1 / 2 : ℝ) / (1 + 1 / 2) = 1 / 3 by norm_num] using hbound

/-- The center `1` genuinely lies outside `2ℤ`. -/
example : (1 : ℝ) ∉ L1 := by
  intro h
  obtain ⟨k, hk⟩ := (twoBasis.mem_span_iff_repr_mem ℤ 1).mp h ()
  have he : (k : ℝ) = 1 / 2 := by
    simpa [twoBasis, Basis.repr_isUnitSMul, Units.smul_def] using hk
  have h0 : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
  have h1 : k < 1 := by exact_mod_cast (show (k : ℝ) < 1 by linarith)
  omega

/-- Banaszczyk's base constant is strictly below `1` at `c = 1` and `c = 2`. -/
example : 1 * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * 1 ^ 2) < 1 := by
  apply ZLattice.banaszczykConstant_lt_one
  rw [div_lt_one (Real.sqrt_pos.mpr (by positivity))]
  exact Real.lt_sqrt_of_sq_lt (by linarith [Real.pi_gt_three])

example : 2 * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * 2 ^ 2) < 1 := by
  apply ZLattice.banaszczykConstant_lt_one
  have h1 : 1 / Real.sqrt (2 * Real.pi) < 1 := by
    rw [div_lt_one (Real.sqrt_pos.mpr (by positivity))]
    exact Real.lt_sqrt_of_sq_lt (by linarith [Real.pi_gt_three])
  linarith

/-- Shifted Banaszczyk tail on `2ℤ` at off-lattice center `1` and radius `4` (`c = 2, s = 2`). -/
example :
    (∑' z : ↥{z : L1 | 4 < ‖(z : ℝ) - 1‖}, gaussianWeight 2 ((z : ℝ) - 1)) <
      2 * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * 2 ^ 2) *
        ZLattice.gaussianMass L1 2 0 := by
  have hc : 1 / Real.sqrt (2 * Real.pi) < 2 := by
    have h1 : 1 / Real.sqrt (2 * Real.pi) < 1 := by
      rw [div_lt_one (Real.sqrt_pos.mpr (by positivity))]
      exact Real.lt_sqrt_of_sq_lt (by linarith [Real.pi_gt_three])
    linarith
  have h := ZLattice.tsum_gaussianWeight_norm_sub_gt_lt L1 2 (by norm_num) 1 2 hc
  have hset : {z : L1 | 2 * 2 * Real.sqrt (finrank ℝ ℝ) < ‖(z : ℝ) - 1‖} =
      {z : L1 | 4 < ‖(z : ℝ) - 1‖} := by
    ext z
    simp only [Set.mem_ofPred_eq, finrank_self, Nat.cast_one, Real.sqrt_one, mul_one,
      show (2 : ℝ) * 2 = 4 by norm_num]
  rw [hset] at h
  simpa only [finrank_self, pow_one] using h

/-- Shifted Regev Lemma 2.5 on `2ℤ` at off-lattice center `1`. -/
example :
    (∑' z : ↥{z : L1 | 2 < ‖(z : ℝ) - 1‖}, gaussianWeight 2 ((z : ℝ) - 1)) <
      (1 / 4 : ℝ) * ZLattice.gaussianMass L1 2 0 := by
  have h := ZLattice.tsum_gaussianWeight_norm_sub_gt_sqrt_lt L1 2 (by norm_num) 1
  have hset : {z : L1 | 2 * Real.sqrt (finrank ℝ ℝ) < ‖(z : ℝ) - 1‖} =
      {z : L1 | 2 < ‖(z : ℝ) - 1‖} := by
    ext z
    simp only [Set.mem_ofPred_eq, finrank_self, Nat.cast_one, Real.sqrt_one, mul_one]
  rw [hset] at h
  simpa only [finrank_self, pow_one] using h

/-- Shifted-mass ratio on `2ℤ` at `ε = 1 / 2` is at most `(1 + 1/2) / (1 - 1/2) = 3`. -/
example : ZLattice.gaussianMass L1 2 0 / ZLattice.gaussianMass L1 2 1 ≤ 3 := by
  have h := ZLattice.gaussianMass_div_le_of_dual_mass_le L1 2 (by norm_num)
    (1 / 2) (by norm_num) dual_small1 0 1
  norm_num at h
  exact h

/-- Off-center MR07 Lemma 4.4 (dual-mass form) on `2ℤ` at `v = 1, s = 2, ε = 1 / 2`:
gives the nontrivial bound `< 3 / 4 < 1`. -/
example :
    (ZLattice.discreteGaussian L1 2 (by norm_num) 1).toOuterMeasure {z : L1 | 2 < ‖(z : ℝ) - 1‖} <
      ENNReal.ofReal (3 / 4) := by
  have h := ZLattice.discreteGaussian_norm_sub_gt_sqrt_lt_of_dual_mass_le L1 2 (by norm_num) 1
    (1 / 2) (by norm_num) dual_small1
  have hnum : (1 + (1 / 2 : ℝ)) / (1 - 1 / 2) * (1 / 4 : ℝ) ^ finrank ℝ ℝ = 3 / 4 := by
    norm_num [finrank_self]
  rw [hnum] at h
  simpa only [finrank_self, Nat.cast_one, Real.sqrt_one, mul_one] using h

/-- General-radius off-center tail on `2ℤ` at `c = 2, s = 2, v = 1, ε = 1 / 2`. -/
example :
    (ZLattice.discreteGaussian L1 2 (by norm_num) 1).toOuterMeasure {z : L1 | 4 < ‖(z : ℝ) - 1‖} <
      ENNReal.ofReal
        (3 * (2 * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * 2 ^ 2))) := by
  have hc : 1 / Real.sqrt (2 * Real.pi) < 2 := by
    have h1 : 1 / Real.sqrt (2 * Real.pi) < 1 := by
      rw [div_lt_one (Real.sqrt_pos.mpr (by positivity))]
      exact Real.lt_sqrt_of_sq_lt (by linarith [Real.pi_gt_three])
    linarith
  have h := ZLattice.discreteGaussian_norm_sub_gt_lt_of_dual_mass_le L1 2 (by norm_num) 1 2 hc
    (1 / 2) (by norm_num) dual_small1
  have h3 : (1 + (1 / 2 : ℝ)) / (1 - 1 / 2) = 3 := by norm_num
  simpa only [finrank_self, Nat.cast_one, Real.sqrt_one, mul_one, pow_one, h3,
    show (2 : ℝ) * 2 = 4 by norm_num] using h

/-- Exact 1-D directional exponential moment on `2ℤ`. -/
example :
    (∑' z : L1, gaussianWeight 2 ((z : ℝ) - 1) * Real.exp (1 * ⟪(z : ℝ) - 1, (1 : ℝ)⟫)) =
      Real.exp (1 / Real.pi) * ZLattice.gaussianMass L1 2 (1 + 2 / Real.pi) := by
  have h := ZLattice.tsum_gaussianWeight_mul_exp_inner L1 2 (by norm_num) 1 (1 : ℝ) 1
  have h1 : (2 * ‖(1 : ℝ)‖) ^ 2 / (2 * Real.pi) * 1 ^ 2 / 2 = 1 / Real.pi := by
    rw [norm_one]; field_simp
  have h2 : (1 * (2 : ℝ) ^ 2 / (2 * Real.pi)) • (1 : ℝ) = 2 / Real.pi := by
    rw [smul_eq_mul, mul_one]; field_simp
  rw [h1, h2] at h
  exact h

/-- Centered `HasSubgaussianMGF` yields a concrete one-sided Chernoff tail via Mathlib. -/
example :
    ((ZLattice.discreteGaussian L1 2 (by norm_num) 0).toMeasure).real {z : L1 | 2 ≤ (z : ℝ)} ≤
      Real.exp (-Real.pi) := by
  have hsub := ZLattice.hasSubgaussianMGF_inner_discreteGaussian_zero L1 2 (by norm_num) (1 : ℝ)
  have h := hsub.measure_ge_le (ε := 2) (by norm_num)
  have hset : {z : L1 | (2 : ℝ) ≤ ⟪(z : ℝ), (1 : ℝ)⟫} = {z : L1 | (2 : ℝ) ≤ (z : ℝ)} := by
    ext z
    simp only [Set.mem_ofPred_eq, RCLike.inner_apply, conj_trivial, one_mul]
  rw [hset] at h
  have hv :
      -2 ^ 2 / (2 * ((((2 * ‖(1 : ℝ)‖) ^ 2 / (2 * Real.pi)).toNNReal : ℝ))) = -Real.pi := by
    rw [Real.coe_toNNReal _ (by positivity), norm_one]
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp
  rwa [hv] at h

/-- Centered two-sided 1-D discrete Gaussian tail on `2ℤ` without any smoothing premise. -/
example :
    (ZLattice.discreteGaussian L1 2 (by norm_num) 0).toOuterMeasure {z : L1 | 2 ≤ |(z : ℝ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-Real.pi)) := by
  have h := ZLattice.discreteGaussian_zero_abs_inner_ge_le L1 2 (by norm_num)
    (u := (1 : ℝ)) one_ne_zero (t := 1) (by norm_num)
  have hset : {z : L1 | 1 * 2 * ‖(1 : ℝ)‖ ≤ |⟪(z : ℝ), (1 : ℝ)⟫|} =
      {z : L1 | (2 : ℝ) ≤ |(z : ℝ)|} := by
    ext z
    simp only [Set.mem_ofPred_eq, one_mul, norm_one, mul_one, RCLike.inner_apply, conj_trivial]
  simpa only [hset, one_pow, mul_one] using h

/-- Off-center 1-D scalar tail on `2ℤ` at `c = 1, s = 2, t = 2, ε = 1 / 2`. -/
example :
    (ZLattice.discreteGaussian L1 2 (by norm_num) 1).toOuterMeasure {z : L1 | 4 ≤ |(z : ℝ) - 1|} ≤
      ENNReal.ofReal (6 * Real.exp (-4 * Real.pi)) := by
  have h := ZLattice.discreteGaussian_real_abs_sub_ge_le_of_dual_mass_le L1 2 (by norm_num) 1
    (t := 2) (by norm_num) (1 / 2) (by norm_num) dual_small1
  have hnum : (1 + (1 / 2 : ℝ)) / (1 - 1 / 2) * (2 * Real.exp (-Real.pi * 2 ^ 2)) =
      6 * Real.exp (-4 * Real.pi) := by
    ring_nf
  simpa only [show (2 : ℝ) * 2 = 4 by norm_num, hnum] using h

/-- MR07 Lemma 4.1 on `2ℤ` at off-lattice center `c = 1` and width `s = 2`: `tvDist ≤ 1 / 2`. -/
example :
    tvDist
      (Measure.map (QuotientAddGroup.mk : ℝ → ℝ ⧸ L1.toAddSubgroup)
        (volume.withDensity (fun x : ℝ ↦ ENNReal.ofReal (gaussianWeight 2 (x - 1) / 2))))
      ((ENNReal.ofReal (ZLattice.covolume L1))⁻¹ •
        Measure.map (QuotientAddGroup.mk : ℝ → ℝ ⧸ L1.toAddSubgroup)
          (volume.restrict (ZSpan.fundamentalDomain twoBasis))) ≤
      1 / 2 := by
  have h := (ZLattice.tvDist_gaussian_shift_quotient_le L1 2 (by norm_num) 1
    (basis_domain_op twoBasis)).trans dual_small1
  simpa only [finrank_self, pow_one] using h

private theorem eta_half_le_two_L1 : ZLattice.smoothingParameter L1 (1 / 2) ≤ 2 :=
  ZLattice.smoothingParameter_le_of_dual_mass_le L1 (by norm_num) dual_small1

/-- Smoothing-parameter (`η_ε`) corollaries on `2ℤ` at `v = 1, s = 2, ε = 1 / 2` (mass ratio,
MR07 Lemma 4.4, general-radius Banaszczyk tail, 1-D scalar tail, and MR07 Lemma 4.1). -/
example : ZLattice.gaussianMass L1 2 0 / ZLattice.gaussianMass L1 2 1 ≤ 3 := by
  have h := ZLattice.gaussianMass_div_le_of_smoothingParameter_le L1 2 (by norm_num)
    (1 / 2) (by norm_num) (by norm_num) eta_half_le_two_L1 0 1
  norm_num at h
  exact h

example :
    (ZLattice.discreteGaussian L1 2 (by norm_num) 1).toOuterMeasure {z : L1 | 2 < ‖(z : ℝ) - 1‖} <
      ENNReal.ofReal (3 / 4) := by
  have h := ZLattice.discreteGaussian_norm_sub_gt_sqrt_lt_of_smoothingParameter_le L1 2
    (by norm_num) 1 (1 / 2) (by norm_num) (by norm_num) eta_half_le_two_L1
  have hnum : (1 + (1 / 2 : ℝ)) / (1 - 1 / 2) * (1 / 4 : ℝ) ^ finrank ℝ ℝ = 3 / 4 := by
    norm_num [finrank_self]
  rw [hnum] at h
  simpa only [finrank_self, Nat.cast_one, Real.sqrt_one, mul_one] using h

example :
    (ZLattice.discreteGaussian L1 2 (by norm_num) 1).toOuterMeasure {z : L1 | 4 < ‖(z : ℝ) - 1‖} <
      ENNReal.ofReal
        (3 * (2 * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * 2 ^ 2))) := by
  have hc : 1 / Real.sqrt (2 * Real.pi) < 2 := by
    have h1 : 1 / Real.sqrt (2 * Real.pi) < 1 :=
      (div_lt_one (Real.sqrt_pos.mpr (by positivity))).mpr
        (Real.lt_sqrt_of_sq_lt (by linarith [Real.pi_gt_three]))
    linarith
  have h := ZLattice.discreteGaussian_norm_sub_gt_lt_of_smoothingParameter_le L1 2 (by norm_num)
    1 2 hc (1 / 2) (by norm_num) (by norm_num) eta_half_le_two_L1
  have h3 : (1 + (1 / 2 : ℝ)) / (1 - 1 / 2) = 3 := by norm_num
  simpa only [finrank_self, Nat.cast_one, Real.sqrt_one, mul_one, pow_one, h3,
    show (2 : ℝ) * 2 = 4 by norm_num] using h

example :
    (ZLattice.discreteGaussian L1 2 (by norm_num) 1).toOuterMeasure {z : L1 | 4 ≤ |(z : ℝ) - 1|} ≤
      ENNReal.ofReal (6 * Real.exp (-4 * Real.pi)) := by
  have h := ZLattice.discreteGaussian_real_abs_sub_ge_le_of_smoothingParameter_le L1 2
    (by norm_num) 1 (t := 2) (by norm_num) (1 / 2) (by norm_num) (by norm_num) eta_half_le_two_L1
  have hnum : (1 + (1 / 2 : ℝ)) / (1 - 1 / 2) * (2 * Real.exp (-Real.pi * 2 ^ 2)) =
      6 * Real.exp (-4 * Real.pi) := by ring_nf
  simpa only [show (2 : ℝ) * 2 = 4 by norm_num, hnum] using h

example :
    tvDist
      (Measure.map (QuotientAddGroup.mk : ℝ → ℝ ⧸ L1.toAddSubgroup)
        (volume.withDensity (fun x : ℝ ↦ ENNReal.ofReal (gaussianWeight 2 (x - 1) / 2))))
      ((ENNReal.ofReal (ZLattice.covolume L1))⁻¹ •
        Measure.map (QuotientAddGroup.mk : ℝ → ℝ ⧸ L1.toAddSubgroup)
          (volume.restrict (ZSpan.fundamentalDomain twoBasis))) ≤
      1 / 2 := by
  have h := ZLattice.tvDist_gaussian_shift_quotient_le_of_smoothingParameter_le L1 2 (by norm_num)
    1 (basis_domain_op twoBasis) (1 / 2) (by norm_num) eta_half_le_two_L1
  simpa only [finrank_self, pow_one] using h

/-! ### Dimension 2: `ℤ² ⊂ EuclideanSpace ℝ (Fin 2)` at off-lattice center `(1/2, 1/3)` -/

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev stdBasis2 : Basis (Fin 2) ℝ E2 := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
private abbrev L2 := Submodule.span ℤ (Set.range stdBasis2)
private abbrev D2 := LinearMap.BilinForm.dualSubmodule (innerₗ E2) L2

private instance : DiscreteTopology D2 := ZLattice.discreteTopology_dualSubmodule L2
private instance : IsZLattice ℝ D2 := ZLattice.isZLattice_dualSubmodule L2

private theorem dual_gap2 (w : D2) (hw : w ≠ 0) : (1 : ℝ) ≤ ‖(w : E2)‖ := by
  have hne : (w : E2) ≠ 0 := fun h ↦ hw (Subtype.ext h)
  have hex : ∃ i : Fin 2, (w : E2) i ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hne
    ext i
    exact hall i
  obtain ⟨i, hi⟩ := hex
  have hm := w.property (stdBasis2 i) (Submodule.subset_span (Set.mem_range_self i))
  obtain ⟨k, hk⟩ := Submodule.mem_one.mp hm
  have hcoord : (w : E2) i = (k : ℝ) := by
    have hinner : ⟪stdBasis2 i, (w : E2)⟫ = (w : E2) i := by
      simp [stdBasis2, EuclideanSpace.inner_single_left]
    have hk' : ⟪(w : E2), stdBasis2 i⟫ = (k : ℝ) := by
      simpa only [innerₗ_apply_apply, eq_intCast] using hk.symm
    rw [real_inner_comm, hinner] at hk'
    exact hk'
  have hkn : k ≠ 0 := by
    intro h0
    apply hi
    rw [hcoord, h0, Int.cast_zero]
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast (Int.one_le_abs hkn)
  have hle : |(w : E2) i| ≤ ‖(w : E2)‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (w : E2) i
  rw [hcoord] at hle
  exact hk1.trans hle

private theorem dual_small2 : ZLattice.gaussianMass D2 (1 / 2) 0 - 1 ≤ 1 / 4 := by
  apply ZLattice.gaussianMass_dual_sub_one_le_of_gap L2 2 (by norm_num)
    1 (by norm_num) dual_gap2 (1 / 4) (by norm_num)
  have hdim : finrank ℝ E2 = 2 := by simp [E2]
  have he_gt : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have he9 : (2.7 : ℝ) ^ 9 < Real.exp 9 := by
    have hp := pow_lt_pow_left₀ he_gt (by norm_num : (0 : ℝ) ≤ 2.7) (by decide : 9 ≠ 0)
    rwa [← Real.exp_natCast_mul, show ((9 : ℕ) : ℝ) * 1 = 9 by norm_num] at hp
  have h3pi : (9 : ℝ) < 3 * Real.pi := by linarith [Real.pi_gt_three]
  have h20 : (20 : ℝ) < Real.exp (3 * Real.pi) := by
    have hnum : (20 : ℝ) < (2.7 : ℝ) ^ 9 := by norm_num
    have hexp : Real.exp 9 < Real.exp (3 * Real.pi) := Real.exp_lt_exp.mpr h3pi
    linarith
  have hexp_eq : -3 * Real.pi * (2 : ℝ) ^ 2 * 1 ^ 2 / 4 = -(3 * Real.pi) := by ring
  rw [hdim, hexp_eq, Real.exp_neg]
  have hrhs : (1 / 4 : ℝ) / (1 + 1 / 4) = 1 / 5 := by norm_num
  rw [hrhs, show (2 : ℝ) ^ 2 * (Real.exp (3 * Real.pi))⁻¹ = 4 / Real.exp (3 * Real.pi) by
    rw [div_eq_mul_inv]; norm_num, div_le_iff₀ (Real.exp_pos _)]
  linarith

private def v2 : E2 := WithLp.toLp 2 ![1 / 2, 1 / 3]
private def u2 : E2 := WithLp.toLp 2 ![1, 1]

private theorem u2_ne_zero : u2 ≠ 0 := by
  intro h
  have h0 : u2 0 = (0 : E2) 0 := congrArg (fun x : E2 ↦ x 0) h
  norm_num [u2] at h0

private theorem norm_u2 : ‖u2‖ = Real.sqrt 2 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [u2, Fin.sum_univ_two]

/-- The 2-D center `(1/2, 1/3)` genuinely lies outside `ℤ²`. -/
example : v2 ∉ L2 := by
  intro h
  obtain ⟨k, hk⟩ := (stdBasis2.mem_span_iff_repr_mem ℤ v2).mp h 0
  have he : (k : ℝ) = 1 / 2 := by
    simpa [stdBasis2, v2] using hk
  have h0 : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
  have h1 : k < 1 := by exact_mod_cast (show (k : ℝ) < 1 by linarith)
  omega

/-- MR07 Lemma 4.4 (dual-mass form) on `ℤ²` at off-lattice center `(1/2, 1/3)`, `s = 2`,
`ε = 1 / 4`: sharp bound `< 5 / 48` (and immediately `≤ 5 / 12`, MR07's `((1+ε)/(1-ε)) 2⁻²`). -/
example :
    (ZLattice.discreteGaussian L2 2 (by norm_num) v2).toOuterMeasure
      {z : L2 | 2 * Real.sqrt 2 < ‖(z : E2) - v2‖} < ENNReal.ofReal (5 / 48) := by
  have h := ZLattice.discreteGaussian_norm_sub_gt_sqrt_lt_of_dual_mass_le L2 2 (by norm_num) v2
    (1 / 4) (by norm_num) dual_small2
  have hdim : finrank ℝ E2 = 2 := by simp [E2]
  have hnum : (1 + (1 / 4 : ℝ)) / (1 - 1 / 4) * (1 / 4 : ℝ) ^ 2 = 5 / 48 := by norm_num
  simpa only [hdim, Nat.cast_ofNat, hnum] using h

example :
    (ZLattice.discreteGaussian L2 2 (by norm_num) v2).toOuterMeasure
      {z : L2 | 2 * Real.sqrt 2 < ‖(z : E2) - v2‖} ≤
      ENNReal.ofReal ((1 + (1 / 4 : ℝ)) / (1 - 1 / 4) * (1 / 2 : ℝ) ^ 2) := by
  have h := ZLattice.discreteGaussian_norm_sub_gt_sqrt_lt_of_dual_mass_le L2 2 (by norm_num) v2
    (1 / 4) (by norm_num) dual_small2
  have hdim : finrank ℝ E2 = 2 := by simp [E2]
  rw [hdim] at h
  refine (le_of_lt (by simpa only [Nat.cast_ofNat] using h)).trans (ENNReal.ofReal_le_ofReal ?_)
  norm_num

/-- Non-axis 1-D directional off-center tail on `ℤ²` along `u2 = (1, 1)` at `t = 2, s = 2`. -/
example :
    (ZLattice.discreteGaussian L2 2 (by norm_num) v2).toOuterMeasure
      {z : L2 | 4 * Real.sqrt 2 ≤ |⟪(z : E2) - v2, u2⟫|} ≤
      ENNReal.ofReal (10 / 3 * Real.exp (-4 * Real.pi)) := by
  have h := ZLattice.discreteGaussian_abs_inner_sub_ge_le_of_dual_mass_le L2 2 (by norm_num) v2
    u2_ne_zero (t := 2) (by norm_num) (1 / 4) (by norm_num) dual_small2
  have hrad : (2 : ℝ) * 2 * ‖u2‖ = 4 * Real.sqrt 2 := by rw [norm_u2]; ring
  have hnum : (1 + (1 / 4 : ℝ)) / (1 - 1 / 4) * (2 * Real.exp (-Real.pi * 2 ^ 2)) =
      10 / 3 * Real.exp (-4 * Real.pi) := by ring_nf
  simpa only [hrad, hnum] using h

/-- MR07 Lemma 4.1 on `ℤ²` at off-lattice center `(1/2, 1/3)` and `s = 2`: `tvDist ≤ 1 / 4`. -/
example :
    tvDist
      (Measure.map (QuotientAddGroup.mk : E2 → E2 ⧸ L2.toAddSubgroup)
        (volume.withDensity
          (fun x : E2 ↦ ENNReal.ofReal (gaussianWeight 2 (x - v2) / 2 ^ finrank ℝ E2))))
      ((ENNReal.ofReal (ZLattice.covolume L2))⁻¹ •
        Measure.map (QuotientAddGroup.mk : E2 → E2 ⧸ L2.toAddSubgroup)
          (volume.restrict (ZSpan.fundamentalDomain stdBasis2))) ≤
      1 / 4 :=
  (ZLattice.tvDist_gaussian_shift_quotient_le L2 2 (by norm_num) v2
    (basis_domain_op stdBasis2)).trans dual_small2

private theorem eta_quarter_le_two_L2 : ZLattice.smoothingParameter L2 (1 / 4) ≤ 2 :=
  ZLattice.smoothingParameter_le_of_dual_mass_le L2 (by norm_num) dual_small2

/-- End-to-end `η_ε` corollaries on `ℤ²` at off-lattice center `(1/2, 1/3)`, `s = 2`,
`ε = 1 / 4`: MR07 Lemma 4.4, non-axis directional 1-D tail, and MR07 Lemma 4.1. -/
example :
    (ZLattice.discreteGaussian L2 2 (by norm_num) v2).toOuterMeasure
      {z : L2 | 2 * Real.sqrt 2 < ‖(z : E2) - v2‖} < ENNReal.ofReal (5 / 48) := by
  have h := ZLattice.discreteGaussian_norm_sub_gt_sqrt_lt_of_smoothingParameter_le L2 2
    (by norm_num) v2 (1 / 4) (by norm_num) (by norm_num) eta_quarter_le_two_L2
  have hdim : finrank ℝ E2 = 2 := by simp [E2]
  have hnum : (1 + (1 / 4 : ℝ)) / (1 - 1 / 4) * (1 / 4 : ℝ) ^ 2 = 5 / 48 := by norm_num
  simpa only [hdim, Nat.cast_ofNat, hnum] using h

example :
    (ZLattice.discreteGaussian L2 2 (by norm_num) v2).toOuterMeasure
      {z : L2 | 4 * Real.sqrt 2 ≤ |⟪(z : E2) - v2, u2⟫|} ≤
      ENNReal.ofReal (10 / 3 * Real.exp (-4 * Real.pi)) := by
  have h := ZLattice.discreteGaussian_abs_inner_sub_ge_le_of_smoothingParameter_le L2 2
    (by norm_num) v2 u2_ne_zero (t := 2) (by norm_num) (1 / 4) (by norm_num) (by norm_num)
    eta_quarter_le_two_L2
  have hrad : (2 : ℝ) * 2 * ‖u2‖ = 4 * Real.sqrt 2 := by rw [norm_u2]; ring
  have hnum : (1 + (1 / 4 : ℝ)) / (1 - 1 / 4) * (2 * Real.exp (-Real.pi * 2 ^ 2)) =
      10 / 3 * Real.exp (-4 * Real.pi) := by ring_nf
  simpa only [hrad, hnum] using h

example :
    tvDist
      (Measure.map (QuotientAddGroup.mk : E2 → E2 ⧸ L2.toAddSubgroup)
        (volume.withDensity
          (fun x : E2 ↦ ENNReal.ofReal (gaussianWeight 2 (x - v2) / 2 ^ finrank ℝ E2))))
      ((ENNReal.ofReal (ZLattice.covolume L2))⁻¹ •
        Measure.map (QuotientAddGroup.mk : E2 → E2 ⧸ L2.toAddSubgroup)
          (volume.restrict (ZSpan.fundamentalDomain stdBasis2))) ≤
      1 / 4 :=
  ZLattice.tvDist_gaussian_shift_quotient_le_of_smoothingParameter_le L2 2 (by norm_num) v2
    (basis_domain_op stdBasis2) (1 / 4) (by norm_num) eta_quarter_le_two_L2

/-! ### Dimension 0: `EuclideanSpace ℝ (Fin 0)` -/

private abbrev E0 := EuclideanSpace ℝ (Fin 0)
private abbrev stdBasis0 : Basis (Fin 0) ℝ E0 := (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis
private abbrev L0 := Submodule.span ℤ (Set.range stdBasis0)
private abbrev D0 := LinearMap.BilinForm.dualSubmodule (innerₗ E0) L0

private instance : DiscreteTopology D0 := ZLattice.discreteTopology_dualSubmodule L0

private theorem dual_zero0 (s : ℝ) (hs : 0 < s) : ZLattice.gaussianMass D0 s 0 - 1 = 0 := by
  rw [ZLattice.gaussianMass_zero_sub_one_eq_tsum D0 s hs]
  have : IsEmpty ↥{w : D0 | w ≠ 0} := ⟨fun w ↦ w.property (Subsingleton.elim _ _)⟩
  exact tsum_empty

/-- In dimension zero, MR07 Lemma 4.4 holds strictly even at `ε = 0`. -/
example (s : ℝ) (hs : 0 < s) (v : E0) :
    (ZLattice.discreteGaussian L0 s hs v).toOuterMeasure {z : L0 | 0 < ‖(z : E0) - v‖} < 1 := by
  have hdual : ZLattice.gaussianMass D0 (1 / s) 0 - 1 ≤ 0 :=
    (dual_zero0 (1 / s) (one_div_pos.mpr hs)).le
  have h := ZLattice.discreteGaussian_norm_sub_gt_sqrt_lt_of_dual_mass_le L0 s hs v
    0 (by norm_num) hdual
  have hdim : finrank ℝ E0 = 0 := by simp [E0]
  simpa only [hdim, Nat.cast_zero, Real.sqrt_zero, mul_zero, pow_zero, add_zero, sub_zero,
    div_one, mul_one, ENNReal.ofReal_one] using h

/-- In dimension zero, `HasSubgaussianMGF` holds with parameter `0`. -/
example (s : ℝ) (hs : 0 < s) (u : E0) :
    HasSubgaussianMGF (fun z : L0 ↦ ⟪(z : E0), u⟫) 0
      (ZLattice.discreteGaussian L0 s hs 0).toMeasure := by
  have hu : u = 0 := Subsingleton.elim _ _
  have h := ZLattice.hasSubgaussianMGF_inner_discreteGaussian_zero L0 s hs u
  simpa only [hu, norm_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
    Real.toNNReal_zero] using h

/-- In dimension zero, MR07 Lemma 4.1 gives exact zero total variation at every center. -/
example (s : ℝ) (hs : 0 < s) (c : E0) :
    tvDist
      (Measure.map (QuotientAddGroup.mk : E0 → E0 ⧸ L0.toAddSubgroup)
        (volume.withDensity
          (fun x : E0 ↦ ENNReal.ofReal (gaussianWeight s (x - c) / s ^ finrank ℝ E0))))
      ((ENNReal.ofReal (ZLattice.covolume L0))⁻¹ •
        Measure.map (QuotientAddGroup.mk : E0 → E0 ⧸ L0.toAddSubgroup)
          (volume.restrict (ZSpan.fundamentalDomain stdBasis0))) = 0 := by
  apply le_antisymm _ tvDist_nonneg
  have h := ZLattice.tvDist_gaussian_shift_quotient_le L0 s hs c (basis_domain_op stdBasis0)
  rwa [dual_zero0 (1 / s) (one_div_pos.mpr hs)] at h

end CslibFrontierTests.DiscreteGaussianOffCenterTail
