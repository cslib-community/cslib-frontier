/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Probability.Gaussian.MomentsDiscrete
import CslibFrontier.Foundations.Probability.Gaussian.Smoothing
import CslibFrontier.Foundations.Probability.IndependentSumNorm
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

/-!
Non-vacuous `module` client tests for discrete Gaussian moments ([MicciancioRegev2007], Lemmas 4.2
and 4.3, in both dual-mass and `2 * η_ε(L) ≤ s` forms), `MemLp 2` and Bochner integral bridges,
and the independent-vector linear-combination second-moment bound ([MicciancioRegev2007],
Lemma 2.11), including an end-to-end `Measure.pi` composition of Lemmas 4.2, 4.3, and 2.11 on
the non-isotropic 2-D lattice `ℤ × 2ℤ` at an off-lattice center.
-/

set_option linter.privateModule false

open Module MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace CslibFrontierTests.DiscreteGaussianMoments

/-! ### Shared exponential bound helper -/

private theorem exp_neg_three_pi_lt_one_sixteenth : Real.exp (-3 * Real.pi) < 1 / 16 := by
  have hpi : 4 * Real.log 2 < 3 * Real.pi := by linarith [Real.log_two_lt_d9, Real.pi_gt_three]
  have hlt : Real.exp (-3 * Real.pi) < Real.exp (-4 * Real.log 2) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hval : Real.exp (-4 * Real.log 2) = 1 / 16 := by
    rw [show (-4 : ℝ) * Real.log 2 = -((4 : ℕ) * Real.log 2) by norm_num, Real.exp_neg,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rwa [hval] at hlt

/-! ### Dimension 0: `EuclideanSpace ℝ (Fin 0)` -/

private abbrev E0 := EuclideanSpace ℝ (Fin 0)
private abbrev L0 : Submodule ℤ E0 :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis)
private abbrev D0 := LinearMap.BilinForm.dualSubmodule (innerₗ E0) L0

private theorem dual_zero_dim0 : ZLattice.gaussianMass D0 (2 / 1) 0 - 1 ≤ 0 := by
  have hmass : ZLattice.gaussianMass D0 (2 / 1) 0 = 1 := by
    rw [ZLattice.gaussianMass, tsum_eq_single (0 : D0)]
    · simp [gaussianWeight]
    · intro z hz
      exact False.elim (hz (Subsingleton.elim z 0))
  linarith

/-- Dual-mass step toward MR07 Lemma 4.3 (both mean-norm and squared-norm bounds) holds in
dimension `0` with exact zero upper bound. -/
example :
    ‖∑' x : L0, (ZLattice.discreteGaussian L0 1 (by norm_num) 0 x).toReal • ((x : E0) - 0)‖ ^ 2 ≤
      0 := by
  have h := ZLattice.norm_tsum_discreteGaussian_smul_sub_sq_le L0 1 (by norm_num) 0 0
    (by norm_num) dual_zero_dim0
  simpa using h

example :
    (∑' x : L0, (ZLattice.discreteGaussian L0 1 (by norm_num) 0 x).toReal * ‖(x : E0) - 0‖ ^ 2) ≤
      0 := by
  have h := ZLattice.tsum_discreteGaussian_mul_norm_sub_sq_le L0 1 (by norm_num) 0 0
    (by norm_num) dual_zero_dim0
  simpa using h

/-- Smoothing-parameter (`2 * η_ε(L) ≤ s`) MR07 Lemma 4.3 bounds hold in dimension `0`. -/
example :
    ‖∑' x : L0, (ZLattice.discreteGaussian L0 1 (by norm_num) 0 x).toReal • ((x : E0) - 0)‖ ^ 2 ≤
      0 := by
  have hη : 2 * ZLattice.smoothingParameter L0 (1 / 2) ≤ 1 := by
    rw [ZLattice.smoothingParameter_eq_zero_of_subsingleton]; norm_num
  have h := ZLattice.norm_tsum_discreteGaussian_smul_sub_sq_le_of_smoothingParameter_le L0 1
    (by norm_num) 0 (1 / 2) (by norm_num) (by norm_num) hη
  simpa using h

example :
    (∑' x : L0, (ZLattice.discreteGaussian L0 1 (by norm_num) 0 x).toReal * ‖(x : E0) - 0‖ ^ 2) ≤
      0 := by
  have hη : 2 * ZLattice.smoothingParameter L0 (1 / 2) ≤ 1 := by
    rw [ZLattice.smoothingParameter_eq_zero_of_subsingleton]; norm_num
  have h := ZLattice.tsum_discreteGaussian_mul_norm_sub_sq_le_of_smoothingParameter_le L0 1
    (by norm_num) 0 (1 / 2) (by norm_num) (by norm_num) hη
  simpa using h

/-- `MemLp 2` and Bochner integral bridges hold in dimension `0`. -/
example :
    MemLp (fun x : L0 ↦ (x : E0) - 0) 2
      (ZLattice.discreteGaussian L0 1 (by norm_num) 0).toMeasure :=
  ZLattice.memLp_sub_discreteGaussian L0 1 (by norm_num) 0

example :
    (∫ x : L0, ((x : E0) - 0) ∂(ZLattice.discreteGaussian L0 1 (by norm_num) 0).toMeasure) =
      ∑' x : L0, (ZLattice.discreteGaussian L0 1 (by norm_num) 0 x).toReal • ((x : E0) - 0) :=
  ZLattice.integral_sub_discreteGaussian_eq_tsum L0 1 (by norm_num) 0

example :
    (∫ x : L0, ‖(x : E0) - 0‖ ^ 2 ∂(ZLattice.discreteGaussian L0 1 (by norm_num) 0).toMeasure) =
      ∑' x : L0, (ZLattice.discreteGaussian L0 1 (by norm_num) 0 x).toReal * ‖(x : E0) - 0‖ ^ 2 :=
  ZLattice.integral_norm_sub_sq_discreteGaussian_eq_tsum L0 1 (by norm_num) 0

/-! ### Dimension 1: `ℤ ⊂ ℝ` at off-lattice center `c1 = 1 / 3` -/

/-- Standard unit basis of `ℝ` spanning `ℤ ⊂ ℝ`. -/
private def unitBasis1 : Basis Unit ℝ ℝ := Basis.singleton Unit ℝ

/-- The one-dimensional integer lattice `ℤ ⊂ ℝ`. -/
private abbrev L1 := Submodule.span ℤ (Set.range unitBasis1)
private abbrev D1 := LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) L1

private instance : DiscreteTopology D1 := ZLattice.discreteTopology_dualSubmodule L1
private instance : IsZLattice ℝ D1 := ZLattice.isZLattice_dualSubmodule L1

private theorem dual_gap1 (w : D1) (hw : w ≠ 0) : (1 : ℝ) ≤ ‖(w : ℝ)‖ := by
  have hm := w.property (unitBasis1 ()) (Submodule.subset_span (Set.mem_range_self ()))
  obtain ⟨k, hk⟩ := Submodule.mem_one.mp hm
  have hk' : (k : ℝ) = (w : ℝ) := by
    simpa [unitBasis1, real_inner_comm] using hk
  have hkn : k ≠ 0 := by
    intro h
    apply hw
    apply Subtype.ext
    change (w : ℝ) = 0
    rw [h, Int.cast_zero] at hk'
    exact hk'.symm
  have ha : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast (Int.one_le_abs hkn)
  rwa [hk', ← Real.norm_eq_abs] at ha

private theorem dual_small1 : ZLattice.gaussianMass D1 (2 / 4) 0 - 1 ≤ 1 / 2 := by
  have h := ZLattice.gaussianMass_dual_sub_one_le_of_gap L1 2 (by norm_num)
    1 (by norm_num) dual_gap1 (1 / 2) (by norm_num) (by
      have hdim : finrank ℝ ℝ = 1 := finrank_self ℝ
      have hexp : -3 * Real.pi * (2 : ℝ) ^ 2 * 1 ^ 2 / 4 = -3 * Real.pi := by ring
      rw [hdim, pow_one, hexp]
      linarith [exp_neg_three_pi_lt_one_sixteenth])
  simpa only [show (1 / 2 : ℝ) = 2 / 4 by norm_num] using h

private def c1 : ℝ := 1 / 3

/-- The center `1 / 3` genuinely lies outside `ℤ`. -/
example : c1 ∉ L1 := by
  intro h
  obtain ⟨k, hk⟩ := (unitBasis1.mem_span_iff_repr_mem ℤ c1).mp h ()
  have he : (k : ℝ) = 1 / 3 := by simpa [unitBasis1, c1] using hk
  have h0 : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
  have h1 : k < 1 := by exact_mod_cast (show (k : ℝ) < 1 by linarith)
  omega

/-- Summability of directional first and second moments on `ℤ ⊂ ℝ` at `c = 1 / 3`. -/
example :
    Summable fun x : L1 ↦
      (ZLattice.discreteGaussian L1 4 (by norm_num) c1 x).toReal * ⟪(x : ℝ) - c1, 1⟫ :=
  ZLattice.summable_discreteGaussian_mul_inner_sub L1 4 (by norm_num) c1 1

example :
    Summable fun x : L1 ↦
      (ZLattice.discreteGaussian L1 4 (by norm_num) c1 x).toReal * ⟪(x : ℝ) - c1, 1⟫ ^ 2 :=
  ZLattice.summable_discreteGaussian_mul_inner_sub_sq L1 4 (by norm_num) c1 1

/-- Dual-mass step toward MR07 Lemma 4.2 (first and second moments) on `ℤ ⊂ ℝ` at off-lattice
center `1 / 3`, width `s = 4`, and `ε = 1 / 2`. -/
example :
    |∑' x : L1, (ZLattice.discreteGaussian L1 4 (by norm_num) c1 x).toReal *
        ⟪(x : ℝ) - c1, 1⟫| ≤ 4 := by
  have h := ZLattice.abs_tsum_discreteGaussian_mul_inner_sub_le L1 4 (by norm_num) c1 1
    (by simp) (1 / 2) (by norm_num) dual_small1
  simpa only [show (1 / 2 : ℝ) / (1 - 1 / 2) * 4 = 4 by norm_num] using h

example :
    |(∑' x : L1, (ZLattice.discreteGaussian L1 4 (by norm_num) c1 x).toReal *
        ⟪(x : ℝ) - c1, 1⟫ ^ 2) - 8 / Real.pi| ≤ 16 := by
  have h := ZLattice.abs_tsum_discreteGaussian_mul_inner_sub_sq_sub_le L1 4 (by norm_num) c1 1
    (by simp) (1 / 2) (by norm_num) dual_small1
  have h1 : (4 : ℝ) ^ 2 / (2 * Real.pi) = 8 / Real.pi := by ring
  have h2 : (1 / 2 : ℝ) / (1 - 1 / 2) * 4 ^ 2 = 16 := by norm_num
  rwa [h1, h2] at h

/-- Dual-mass step toward MR07 Lemma 4.3 (mean norm and expected squared norm) and Bochner
integral bridges on `ℤ ⊂ ℝ` at off-lattice center `1 / 3`. -/
example :
    ‖∫ x : L1, ((x : ℝ) - c1) ∂(ZLattice.discreteGaussian L1 4 (by norm_num) c1).toMeasure‖ ^ 2 ≤
      16 := by
  rw [ZLattice.integral_sub_discreteGaussian_eq_tsum]
  have h := ZLattice.norm_tsum_discreteGaussian_smul_sub_sq_le L1 4 (by norm_num) c1
    (1 / 2) (by norm_num) dual_small1
  simpa only [finrank_self, Nat.cast_one, mul_one,
    show ((1 / 2 : ℝ) / (1 - 1 / 2)) ^ 2 * 4 ^ 2 = 16 by norm_num] using h

example :
    (∫ x : L1, ‖(x : ℝ) - c1‖ ^ 2 ∂(ZLattice.discreteGaussian L1 4 (by norm_num) c1).toMeasure) ≤
      (1 / (2 * Real.pi) + 1) * 16 := by
  rw [ZLattice.integral_norm_sub_sq_discreteGaussian_eq_tsum]
  have h := ZLattice.tsum_discreteGaussian_mul_norm_sub_sq_le L1 4 (by norm_num) c1
    (1 / 2) (by norm_num) dual_small1
  have hnum :
      (1 / (2 * Real.pi) + (1 / 2 : ℝ) / (1 - 1 / 2)) * 4 ^ 2 * (finrank ℝ ℝ : ℝ) =
        (1 / (2 * Real.pi) + 1) * 16 := by
    rw [finrank_self]
    norm_num
  rwa [hnum] at h

private theorem two_mul_eta_half_le_four_L1 : 2 * ZLattice.smoothingParameter L1 (1 / 2) ≤ 4 := by
  have h := ZLattice.smoothingParameter_le_of_dual_mass_le L1 (by norm_num : (0 : ℝ) < 2)
    (by simpa only [show (1 / 2 : ℝ) = 2 / 4 by norm_num] using dual_small1)
  linarith

/-- Smoothing-parameter (`2 * η_ε(L) ≤ s`) MR07 Lemmas 4.2 and 4.3 on `ℤ ⊂ ℝ` at off-lattice
center `1 / 3`, width `s = 4`, and `ε = 1 / 2`. -/
example :
    |∑' x : L1, (ZLattice.discreteGaussian L1 4 (by norm_num) c1 x).toReal *
        ⟪(x : ℝ) - c1, 1⟫| ≤ 4 := by
  have h := ZLattice.abs_tsum_discreteGaussian_mul_inner_sub_le_of_smoothingParameter_le L1 4
    (by norm_num) c1 1 (by simp) (1 / 2) (by norm_num) (by norm_num) two_mul_eta_half_le_four_L1
  simpa only [show (1 / 2 : ℝ) / (1 - 1 / 2) * 4 = 4 by norm_num] using h

example :
    |(∑' x : L1, (ZLattice.discreteGaussian L1 4 (by norm_num) c1 x).toReal *
        ⟪(x : ℝ) - c1, 1⟫ ^ 2) - 8 / Real.pi| ≤ 16 := by
  have h := ZLattice.abs_tsum_discreteGaussian_mul_inner_sub_sq_sub_le_of_smoothingParameter_le L1
    4 (by norm_num) c1 1 (by simp) (1 / 2) (by norm_num) (by norm_num)
    two_mul_eta_half_le_four_L1
  have h1 : (4 : ℝ) ^ 2 / (2 * Real.pi) = 8 / Real.pi := by ring
  have h2 : (1 / 2 : ℝ) / (1 - 1 / 2) * 4 ^ 2 = 16 := by norm_num
  rwa [h1, h2] at h

example :
    ‖∫ x : L1, ((x : ℝ) - c1) ∂(ZLattice.discreteGaussian L1 4 (by norm_num) c1).toMeasure‖ ^ 2 ≤
      16 := by
  rw [ZLattice.integral_sub_discreteGaussian_eq_tsum]
  have h := ZLattice.norm_tsum_discreteGaussian_smul_sub_sq_le_of_smoothingParameter_le L1 4
    (by norm_num) c1 (1 / 2) (by norm_num) (by norm_num) two_mul_eta_half_le_four_L1
  simpa only [finrank_self, Nat.cast_one, mul_one,
    show ((1 / 2 : ℝ) / (1 - 1 / 2)) ^ 2 * 4 ^ 2 = 16 by norm_num] using h

example :
    (∫ x : L1, ‖(x : ℝ) - c1‖ ^ 2 ∂(ZLattice.discreteGaussian L1 4 (by norm_num) c1).toMeasure) ≤
      (1 / (2 * Real.pi) + 1) * 16 := by
  rw [ZLattice.integral_norm_sub_sq_discreteGaussian_eq_tsum]
  have h := ZLattice.tsum_discreteGaussian_mul_norm_sub_sq_le_of_smoothingParameter_le L1 4
    (by norm_num) c1 (1 / 2) (by norm_num) (by norm_num) two_mul_eta_half_le_four_L1
  have hnum :
      (1 / (2 * Real.pi) + (1 / 2 : ℝ) / (1 - 1 / 2)) * 4 ^ 2 * (finrank ℝ ℝ : ℝ) =
        (1 / (2 * Real.pi) + 1) * 16 := by rw [finrank_self]; norm_num
  rwa [hnum] at h

/-! ### Dimension 2: non-isotropic `ℤ × 2ℤ` and composition into MR07 Lemma 2.11 -/

private abbrev E2 := EuclideanSpace ℝ (Fin 2)

private def nonIsoBasis2 : Basis (Fin 2) ℝ E2 :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.isUnitSMul (w := ![1, 2]) (fun i ↦ by
    fin_cases i <;> norm_num)

private abbrev L2 := Submodule.span ℤ (Set.range nonIsoBasis2)
private abbrev D2 := LinearMap.BilinForm.dualSubmodule (innerₗ E2) L2

private instance : DiscreteTopology D2 := ZLattice.discreteTopology_dualSubmodule L2
private instance : IsZLattice ℝ D2 := ZLattice.isZLattice_dualSubmodule L2

private theorem dual_gap2 (w : D2) (hw : w ≠ 0) : (1 / 2 : ℝ) ≤ ‖(w : E2)‖ := by
  have hne : (w : E2) ≠ 0 := fun h ↦ hw (Subtype.ext h)
  have hex : ∃ i : Fin 2, (w : E2) i ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hne
    ext i
    exact hall i
  obtain ⟨i, hi⟩ := hex
  have hm := w.property (nonIsoBasis2 i) (Submodule.subset_span (Set.mem_range_self i))
  obtain ⟨k, hk⟩ := Submodule.mem_one.mp hm
  have hinner : ⟪nonIsoBasis2 i, (w : E2)⟫ = (![1, 2] i : ℝ) * (w : E2) i := by
    simp [nonIsoBasis2, Basis.isUnitSMul_apply, inner_smul_left, EuclideanSpace.inner_single_left]
  have hk' : (![1, 2] i : ℝ) * (w : E2) i = (k : ℝ) := by
    have h1 : ⟪(w : E2), nonIsoBasis2 i⟫ = (k : ℝ) := by
      simpa only [innerₗ_apply_apply, eq_intCast] using hk.symm
    rwa [real_inner_comm, hinner] at h1
  have hscale_pos : (0 : ℝ) < ![1, 2] i := by fin_cases i <;> norm_num
  have hscale_le : (![1, 2] i : ℝ) ≤ 2 := by fin_cases i <;> norm_num
  have hkn : k ≠ 0 := by
    intro h0
    apply hi
    rw [h0, Int.cast_zero] at hk'
    exact (mul_eq_zero.mp hk').resolve_left hscale_pos.ne'
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast (Int.one_le_abs hkn)
  have hcoord : 1 / 2 ≤ |(w : E2) i| := by
    rw [← hk', abs_mul, abs_of_pos hscale_pos] at hk1
    nlinarith [abs_nonneg ((w : E2) i)]
  have hle : |(w : E2) i| ≤ ‖(w : E2)‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (w : E2) i
  exact hcoord.trans hle

private theorem dual_small2 : ZLattice.gaussianMass D2 (2 / 8) 0 - 1 ≤ 1 / 2 := by
  have h := ZLattice.gaussianMass_dual_sub_one_le_of_gap L2 4 (by norm_num)
    (1 / 2) (by norm_num) dual_gap2 (1 / 2) (by norm_num) (by
      have hdim : finrank ℝ E2 = 2 := by simp [E2]
      have hexp : -3 * Real.pi * (4 : ℝ) ^ 2 * (1 / 2) ^ 2 / 4 = -3 * Real.pi := by ring
      rw [hdim, hexp]
      linarith [exp_neg_three_pi_lt_one_sixteenth])
  simpa only [show (1 / 4 : ℝ) = 2 / 8 by norm_num] using h

private def c2 : E2 := WithLp.toLp 2 ![1 / 3, 1 / 2]
private def u2 : E2 := WithLp.toLp 2 ![3 / 5, 4 / 5]

private theorem norm_u2 : ‖u2‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [u2, Fin.sum_univ_two]

/-- The 2-D center `(1/3, 1/2)` genuinely lies outside `ℤ × 2ℤ`. -/
example : c2 ∉ L2 := by
  intro h
  obtain ⟨k, hk⟩ := (nonIsoBasis2.mem_span_iff_repr_mem ℤ c2).mp h 0
  have he : (k : ℝ) = 1 / 3 := by
    simpa [nonIsoBasis2, Basis.repr_isUnitSMul, Units.smul_def, c2] using hk
  have h0 : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
  have h1 : k < 1 := by exact_mod_cast (show (k : ℝ) < 1 by linarith)
  omega

/-- Dual-mass step toward MR07 Lemma 4.2 along the tilted unit direction `u2 = (3/5, 4/5)` on
`ℤ × 2ℤ` at off-lattice center `(1/3, 1/2)`, width `s = 8`, `ε = 1 / 2`. -/
example :
    |∑' x : L2, (ZLattice.discreteGaussian L2 8 (by norm_num) c2 x).toReal *
        ⟪(x : E2) - c2, u2⟫| ≤ 8 := by
  have h := ZLattice.abs_tsum_discreteGaussian_mul_inner_sub_le L2 8 (by norm_num) c2 u2
    norm_u2 (1 / 2) (by norm_num) dual_small2
  simpa only [show (1 / 2 : ℝ) / (1 - 1 / 2) * 8 = 8 by norm_num] using h

example :
    |(∑' x : L2, (ZLattice.discreteGaussian L2 8 (by norm_num) c2 x).toReal *
        ⟪(x : E2) - c2, u2⟫ ^ 2) - 32 / Real.pi| ≤ 64 := by
  have h := ZLattice.abs_tsum_discreteGaussian_mul_inner_sub_sq_sub_le L2 8 (by norm_num) c2 u2
    norm_u2 (1 / 2) (by norm_num) dual_small2
  have h1 : (8 : ℝ) ^ 2 / (2 * Real.pi) = 32 / Real.pi := by ring
  have h2 : (1 / 2 : ℝ) / (1 - 1 / 2) * 8 ^ 2 = 64 := by norm_num
  rwa [h1, h2] at h

private theorem two_mul_eta_half_le_eight_L2 : 2 * ZLattice.smoothingParameter L2 (1 / 2) ≤ 8 := by
  have h := ZLattice.smoothingParameter_le_of_dual_mass_le L2 (by norm_num : (0 : ℝ) < 4)
    (by simpa only [show (1 / 4 : ℝ) = 2 / 8 by norm_num] using dual_small2)
  linarith

/-- Smoothing-parameter (`2 * η_ε(L) ≤ s`) MR07 Lemmas 4.2 and 4.3 on the non-isotropic 2-D
lattice `ℤ × 2ℤ` along `u2 = (3/5, 4/5)` at off-lattice center `(1/3, 1/2)`. -/
example :
    |∑' x : L2, (ZLattice.discreteGaussian L2 8 (by norm_num) c2 x).toReal *
        ⟪(x : E2) - c2, u2⟫| ≤ 8 := by
  have h := ZLattice.abs_tsum_discreteGaussian_mul_inner_sub_le_of_smoothingParameter_le L2 8
    (by norm_num) c2 u2 norm_u2 (1 / 2) (by norm_num) (by norm_num) two_mul_eta_half_le_eight_L2
  simpa only [show (1 / 2 : ℝ) / (1 - 1 / 2) * 8 = 8 by norm_num] using h

example :
    |(∑' x : L2, (ZLattice.discreteGaussian L2 8 (by norm_num) c2 x).toReal *
        ⟪(x : E2) - c2, u2⟫ ^ 2) - 32 / Real.pi| ≤ 64 := by
  have h := ZLattice.abs_tsum_discreteGaussian_mul_inner_sub_sq_sub_le_of_smoothingParameter_le L2
    8 (by norm_num) c2 u2 norm_u2 (1 / 2) (by norm_num) (by norm_num)
    two_mul_eta_half_le_eight_L2
  have h1 : (8 : ℝ) ^ 2 / (2 * Real.pi) = 32 / Real.pi := by ring
  have h2 : (1 / 2 : ℝ) / (1 - 1 / 2) * 8 ^ 2 = 64 := by norm_num
  rwa [h1, h2] at h

example :
    ‖∑' x : L2, (ZLattice.discreteGaussian L2 8 (by norm_num) c2 x).toReal • ((x : E2) - c2)‖ ^ 2 ≤
      128 := by
  have h := ZLattice.norm_tsum_discreteGaussian_smul_sub_sq_le_of_smoothingParameter_le L2 8
    (by norm_num) c2 (1 / 2) (by norm_num) (by norm_num) two_mul_eta_half_le_eight_L2
  have hdim : finrank ℝ E2 = 2 := by simp [E2]
  simpa only [hdim, show ((1 / 2 : ℝ) / (1 - 1 / 2)) ^ 2 * 8 ^ 2 * (2 : ℕ) = 128 by norm_num]
    using h

example :
    (∑' x : L2, (ZLattice.discreteGaussian L2 8 (by norm_num) c2 x).toReal *
        ‖(x : E2) - c2‖ ^ 2) ≤ (1 / (2 * Real.pi) + 1) * 128 := by
  have h := ZLattice.tsum_discreteGaussian_mul_norm_sub_sq_le_of_smoothingParameter_le L2 8
    (by norm_num) c2 (1 / 2) (by norm_num) (by norm_num) two_mul_eta_half_le_eight_L2
  have hdim : finrank ℝ E2 = 2 := by simp [E2]
  have hnum : (1 / (2 * Real.pi) + (1 / 2 : ℝ) / (1 - 1 / 2)) * 8 ^ 2 * (finrank ℝ E2 : ℝ) =
      (1 / (2 * Real.pi) + 1) * 128 := by rw [hdim]; norm_num; ring
  rwa [hnum] at h

/-- End-to-end composition of MR07 Lemmas 4.2, 4.3, and 2.11: two independent off-center discrete
Gaussian samples on the non-isotropic 2-D lattice `ℤ × 2ℤ` combined with concrete weights
`z = ![2, -1]` satisfy `integral_norm_sum_smul_sq_le_of_iIndepFun`. -/
example :
    let μ0 : Measure L2 := (ZLattice.discreteGaussian L2 8 (by norm_num) c2).toMeasure
    let ν : Measure (Fin 2 → L2) := Measure.pi (fun _ : Fin 2 ↦ μ0)
    let X : Fin 2 → (Fin 2 → L2) → E2 := fun i ω ↦ (ω i : E2) - c2
    let z : Fin 2 → ℝ := ![2, -1]
    ∫ ω, ‖∑ i : Fin 2, z i • X i ω‖ ^ 2 ∂ν ≤
      ((1 / (2 * Real.pi) + 1) * 128 + 128 * 2) * 5 := by
  intro μ0 ν X z
  have hY_meas : Measurable (fun x : L2 ↦ (x : E2) - c2) :=
    continuous_subtype_val.sub continuous_const |>.measurable
  have hind : iIndepFun X ν := iIndepFun_pi (fun _ ↦ hY_meas.aemeasurable)
  have hL2 (i : Fin 2) : MemLp (X i) 2 ν :=
    (ZLattice.memLp_sub_discreteGaussian L2 8 (by norm_num) c2).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin 2 ↦ μ0) i)
  have hdim : finrank ℝ E2 = 2 := by simp [E2]
  have hsq (i : Fin 2) : ∫ ω, ‖X i ω‖ ^ 2 ∂ν ≤ (1 / (2 * Real.pi) + 1) * 128 := by
    have hcomp :
        (∫ ω, ‖(ω i : E2) - c2‖ ^ 2 ∂ν) = ∫ x : L2, ‖(x : E2) - c2‖ ^ 2 ∂μ0 := by
      rw [← (measurePreserving_eval (fun _ : Fin 2 ↦ μ0) i).map_eq,
        integral_map (measurable_pi_apply i).aemeasurable
          (hY_meas.norm.pow_const 2).aestronglyMeasurable]
    change (∫ ω, ‖(ω i : E2) - c2‖ ^ 2 ∂ν) ≤ _
    rw [hcomp, ZLattice.integral_norm_sub_sq_discreteGaussian_eq_tsum]
    have h43 := ZLattice.tsum_discreteGaussian_mul_norm_sub_sq_le L2 8 (by norm_num) c2
      (1 / 2) (by norm_num) dual_small2
    have hnum :
        (1 / (2 * Real.pi) + (1 / 2 : ℝ) / (1 - 1 / 2)) * 8 ^ 2 * (finrank ℝ E2 : ℝ) =
          (1 / (2 * Real.pi) + 1) * 128 := by
      rw [hdim]
      norm_num
      ring
    rwa [hnum] at h43
  have hmean (i : Fin 2) : ‖∫ ω, X i ω ∂ν‖ ^ 2 ≤ 128 := by
    have hcomp : (∫ ω, ((ω i : E2) - c2) ∂ν) = ∫ x : L2, ((x : E2) - c2) ∂μ0 := by
      rw [← (measurePreserving_eval (fun _ : Fin 2 ↦ μ0) i).map_eq,
        integral_map (measurable_pi_apply i).aemeasurable hY_meas.aestronglyMeasurable]
    change ‖∫ ω, ((ω i : E2) - c2) ∂ν‖ ^ 2 ≤ _
    rw [hcomp, ZLattice.integral_sub_discreteGaussian_eq_tsum]
    have h43 := ZLattice.norm_tsum_discreteGaussian_smul_sub_sq_le L2 8 (by norm_num) c2
      (1 / 2) (by norm_num) dual_small2
    have hnum :
        ((1 / 2 : ℝ) / (1 - 1 / 2)) ^ 2 * 8 ^ 2 * (finrank ℝ E2 : ℝ) = 128 := by
      rw [hdim]
      norm_num
    rwa [hnum] at h43
  have h211 := ProbabilityTheory.integral_norm_sum_smul_sq_le_of_iIndepFun hind hL2 hsq hmean z
  have hz : (∑ i : Fin 2, z i ^ 2) = 5 := by
    simp [z, Fin.sum_univ_two]
    norm_num
  simpa only [Fintype.card_fin, Nat.cast_ofNat, hz] using h211

/-! ### Empty index set (`Fin 0`) for MR07 Lemma 2.11 -/

/-- MR07 Lemma 2.11 holds trivially when the index type is empty (`Fin 0`). -/
example :
    let μ : Measure Unit := Measure.dirac ()
    let X : Fin 0 → Unit → ℝ := fun i ↦ Fin.elim0 i
    let z : Fin 0 → ℝ := fun i ↦ Fin.elim0 i
    ∫ ω, ‖∑ i : Fin 0, z i • X i ω‖ ^ 2 ∂μ ≤ (0 + 0 * (Fintype.card (Fin 0) : ℝ)) *
      ∑ i : Fin 0, z i ^ 2 := by
  intro μ X z
  exact ProbabilityTheory.integral_norm_sum_smul_sq_le_of_iIndepFun
    (by
      rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
      intro s sets _
      rw [Finset.eq_empty_of_isEmpty s]
      simp)
    (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i) z

end CslibFrontierTests.DiscreteGaussianMoments
