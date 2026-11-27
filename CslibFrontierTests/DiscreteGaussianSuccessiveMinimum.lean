/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.MeasureTheory.Group.FundamentalDomain
import CslibFrontier.Foundations.Probability.Gaussian.Quotient
import CslibFrontier.Foundations.Probability.Gaussian.ShiftBounds
import CslibFrontier.Foundations.Probability.Gaussian.SuccessiveMinimum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Clients of `ZLattice.exists_linearIndependent_norm_le_successiveMinimum`,
`ZLattice.gaussianMass_le_gaussianMass_zero`,
`ZLattice.gaussianMass_dual_sub_one_le_of_successiveMinimum`, and
`ZLattice.smoothingParameter_le_sqrt_log_mul_successiveMinimum` under module encapsulation.

Covers dimension 0, the 1-D lattice `2ℤ`, the non-isotropic 2-D lattice `ℤ × 3ℤ` (with
`λ₁ = 1 < λ₂ = 3`, discharging both `ZLattice.tvDist_gaussian_quotient_le` and
`ZLattice.tvDist_gaussian_shift_quotient_le_of_smoothingParameter_le`), and the lower-rank
discrete lattice `ℤ × {0} ⊂ ℝ²` with an off-span center.
-/

set_option linter.privateModule false

open Module ProbabilityTheory MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace CslibFrontierTests.DiscreteGaussianSuccessiveMinimum

/-! ### Dimension 0 -/

private abbrev Point := EuclideanSpace ℝ (Fin 0)
private abbrev pointBasis := (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis
private abbrev pointLattice := Submodule.span ℤ (Set.range pointBasis)
private abbrev pointDual := LinearMap.BilinForm.dualSubmodule (innerₗ Point) pointLattice

/-- `ZLattice.gaussianMass_dual_sub_one_le_of_successiveMinimum` holds in dimension zero for
every positive `ε` and `s`, using only ordinary module imports. -/
example (ε : ℝ) (hε : 0 < ε) (s : ℝ) (hs : 0 < s) :
    ZLattice.gaussianMass pointDual (1 / s) 0 - 1 ≤ ε := by
  apply ZLattice.gaussianMass_dual_sub_one_le_of_successiveMinimum _ ε hε s hs
  simp [hs.le]

example (s : ℝ) (hs : 0 < s) (c : Point) :
    ZLattice.gaussianMass pointLattice s c ≤ ZLattice.gaussianMass pointLattice s 0 :=
  ZLattice.gaussianMass_le_gaussianMass_zero pointLattice s hs c

/-- MR07 Lemma 3.3 (`smoothingParameter_le_sqrt_log_mul_successiveMinimum`) holds in dimension
zero (`η_ε(pointLattice) ≤ 0`). -/
example (ε : ℝ) (hε : 0 < ε) : ZLattice.smoothingParameter pointLattice ε ≤ 0 := by
  have h := ZLattice.smoothingParameter_le_sqrt_log_mul_successiveMinimum pointLattice ε hε
  simpa [Point] using h

/-! ### Dimension 1: `2ℤ ⊂ ℝ` -/

private def twoBasis : Basis Unit ℝ ℝ :=
  (Basis.singleton Unit ℝ).isUnitSMul (fun _ ↦ (show (2 : ℝ) ≠ 0 by norm_num).isUnit)

private abbrev L1 := Submodule.span ℤ (Set.range twoBasis)
private abbrev D1 := LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) L1

private theorem L1_ne_bot : L1 ≠ ⊥ := by
  refine (Submodule.ne_bot_iff _).2 ⟨2, ?_, by norm_num⟩
  have h : twoBasis () = (2 : ℝ) := by norm_num [twoBasis, Basis.isUnitSMul_apply]
  exact h ▸ Submodule.subset_span (Set.mem_range_self ())

private theorem L1_minimum : ZLattice.minimum L1 = 2 := by
  apply le_antisymm
  · have hmem : (2 : ℝ) ∈ L1 := by
      have h : twoBasis () = (2 : ℝ) := by norm_num [twoBasis, Basis.isUnitSMul_apply]
      exact h ▸ Submodule.subset_span (Set.mem_range_self ())
    simpa only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      ZLattice.minimum_le_norm hmem (by norm_num)
  · rw [ZLattice.le_minimum_iff L1_ne_bot]
    intro v hv hv0
    obtain ⟨k, hk⟩ := (twoBasis.mem_span_iff_repr_mem ℤ v).1 hv ()
    have hv_eq : v = 2 * (k : ℝ) := by
      have hr : twoBasis.repr v () = v / 2 := by
        simp [twoBasis, Basis.repr_isUnitSMul, Units.smul_def, div_eq_inv_mul]
      rw [hr] at hk
      have : (k : ℝ) = v / 2 := by simpa only [algebraMap_int_eq, eq_intCast] using hk
      linarith
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hv0
      simpa using hv_eq
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
    rw [hv_eq, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

private theorem L1_successiveMinimum : ZLattice.successiveMinimum L1 1 = 2 := by
  rw [ZLattice.successiveMinimum_one L1 L1_ne_bot, L1_minimum]

example : ∃ v : Fin 1 → ℝ, LinearIndependent ℝ v ∧ (∀ i, v i ∈ L1) ∧ ∀ i, ‖v i‖ = 2 := by
  obtain ⟨v, hli, hmem, hle⟩ :=
    ZLattice.exists_linearIndependent_norm_le_successiveMinimum L1 (k := 1) (by simp)
  refine ⟨v, hli, hmem, fun i ↦ le_antisymm (L1_successiveMinimum ▸ hle i) ?_⟩
  rw [← L1_minimum]
  exact ZLattice.minimum_le_norm (hmem i) (hli.ne_zero i)

example : ZLattice.gaussianMass L1 1 1 ≤ ZLattice.gaussianMass L1 1 0 :=
  ZLattice.gaussianMass_le_gaussianMass_zero L1 1 (by norm_num) 1

private theorem log_six_div_pi_le : Real.log 6 / Real.pi ≤ (3 / 2 : ℝ) ^ 2 := by
  have he : (6 : ℝ) < Real.exp 2 := by
    have h1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have hlog : Real.log 6 < 2 := by
    have h := Real.log_lt_log (by norm_num) he
    rwa [Real.log_exp] at h
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hdiv : Real.log 6 / Real.pi < 2 / 3 := by
    rw [div_lt_div_iff₀ Real.pi_pos (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  linarith

private theorem L1_dual_small_at_three : ZLattice.gaussianMass D1 (1 / 3) 0 - 1 ≤ 1 / 2 := by
  apply ZLattice.gaussianMass_dual_sub_one_le_of_successiveMinimum L1
    (1 / 2) (by norm_num) 3 (by norm_num)
  simp only [finrank_self, Nat.cast_one, L1_successiveMinimum]
  have harg : (2 : ℝ) * 1 * (1 + 1 / (1 / 2 : ℝ)) = 6 := by norm_num
  rw [harg]
  have hsqrt : Real.sqrt (Real.log 6 / Real.pi) ≤ 3 / 2 := by
    calc
      Real.sqrt (Real.log 6 / Real.pi) ≤ Real.sqrt ((3 / 2 : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt log_six_div_pi_le
      _ = 3 / 2 := Real.sqrt_sq (by norm_num)
  linarith

/-- Representative client: `gaussianMass_dual_sub_one_le_of_successiveMinimum` discharges
`ZLattice.gaussianMass_mem_Icc_of_dual_mass_le` on `2ℤ`. -/
example : ZLattice.gaussianMass L1 3 1 ∈
    Set.Icc (3 / ZLattice.covolume L1 * (1 - 1 / 2)) (3 / ZLattice.covolume L1 * (1 + 1 / 2)) := by
  simpa only [finrank_self, pow_one] using
    ZLattice.gaussianMass_mem_Icc_of_dual_mass_le L1 3 (by norm_num) (1 / 2)
      L1_dual_small_at_three 1

/-- MR07 Lemma 3.3 (`smoothingParameter_le_sqrt_log_mul_successiveMinimum`) on `2ℤ`:
`η_{1/2}(2ℤ) ≤ 2 * √(ln 6 / π) ≤ 3`, discharging `gaussianMass_mem_Icc_of_smoothingParameter_le`. -/
private theorem L1_eta_half_le_three : ZLattice.smoothingParameter L1 (1 / 2) ≤ 3 := by
  have h := ZLattice.smoothingParameter_le_sqrt_log_mul_successiveMinimum L1 (1 / 2) (by norm_num)
  simp only [finrank_self, Nat.cast_one, L1_successiveMinimum] at h
  have harg : (2 : ℝ) * 1 * (1 + 1 / (1 / 2 : ℝ)) = 6 := by norm_num
  rw [harg] at h
  have hsqrt : Real.sqrt (Real.log 6 / Real.pi) ≤ 3 / 2 := by
    calc
      Real.sqrt (Real.log 6 / Real.pi) ≤ Real.sqrt ((3 / 2 : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt log_six_div_pi_le
      _ = 3 / 2 := Real.sqrt_sq (by norm_num)
  linarith

example : ZLattice.gaussianMass L1 3 1 ∈
    Set.Icc (3 / ZLattice.covolume L1 * (1 - 1 / 2)) (3 / ZLattice.covolume L1 * (1 + 1 / 2)) := by
  simpa only [finrank_self, pow_one] using
    ZLattice.gaussianMass_mem_Icc_of_smoothingParameter_le L1 3 (by norm_num) (1 / 2) (by norm_num)
      L1_eta_half_le_three 1

/-! ### Dimension 2 non-isotropic: `ℤ × 3ℤ ⊂ EuclideanSpace ℝ (Fin 2)` (`λ₁ = 1 < λ₂ = 3`) -/

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private def rectBasis : Basis (Fin 2) ℝ Plane :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.isUnitSMul
    (fun i ↦ isUnit_iff_ne_zero.mpr (by fin_cases i <;> norm_num : (![1, 3] : Fin 2 → ℝ) i ≠ 0))

private abbrev L2 := Submodule.span ℤ (Set.range rectBasis)
private abbrev D2 := LinearMap.BilinForm.dualSubmodule (innerₗ Plane) L2

private theorem norm_rectBasis_zero : ‖rectBasis 0‖ = 1 := by
  simp [rectBasis, Basis.isUnitSMul_apply]

private theorem norm_rectBasis_one : ‖rectBasis 1‖ = 3 := by
  simp [rectBasis, Basis.isUnitSMul_apply, EuclideanSpace.norm_eq]

private theorem L2_ne_bot : L2 ≠ ⊥ := by
  refine (Submodule.ne_bot_iff _).2 ⟨rectBasis 0, Submodule.subset_span (Set.mem_range_self 0), ?_⟩
  intro h
  have := norm_rectBasis_zero
  rw [h, norm_zero] at this
  norm_num at this

private theorem L2_mem_coords {v : Plane} (hv : v ∈ L2) :
    ∃ a b : ℤ, v 0 = a ∧ v 1 = 3 * b := by
  have hrepr := (rectBasis.mem_span_iff_repr_mem ℤ v).1 hv
  obtain ⟨a, ha⟩ := hrepr 0
  obtain ⟨b, hb⟩ := hrepr 1
  refine ⟨a, b, ?_, ?_⟩
  · have h0 : rectBasis.repr v 0 = v 0 := by
      simp [rectBasis, Basis.repr_isUnitSMul]
    rw [h0] at ha
    simpa only [algebraMap_int_eq, eq_intCast] using ha.symm
  · have h1 : rectBasis.repr v 1 = v 1 / 3 := by
      simp [rectBasis, Basis.repr_isUnitSMul, Units.smul_def, div_eq_inv_mul]
    rw [h1] at hb
    have h1' : (b : ℝ) = v 1 / 3 := by simpa only [algebraMap_int_eq, eq_intCast] using hb
    linarith

private theorem L2_minimum : ZLattice.minimum L2 = 1 := by
  apply le_antisymm
  · have hv0 : rectBasis 0 ≠ 0 := by
      intro h; have := norm_rectBasis_zero; rw [h, norm_zero] at this; norm_num at this
    exact norm_rectBasis_zero ▸ ZLattice.minimum_le_norm (Submodule.subset_span ⟨0, rfl⟩) hv0
  · rw [ZLattice.le_minimum_iff L2_ne_bot]
    intro v hv hv0
    obtain ⟨a, b, ha, hb⟩ := L2_mem_coords hv
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push Not at h
      apply hv0
      ext i
      fin_cases i
      · simp [ha, h.1]
      · simp [hb, h.2]
    have hsq : (1 : ℝ) ≤ ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      rcases hab with ha0 | hb0
      · have h1 : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast Int.one_le_abs ha0
        rw [Real.norm_eq_abs, Real.norm_eq_abs, ha]
        nlinarith [sq_nonneg |v 1|]
      · have h1 : (1 : ℝ) ≤ |(b : ℝ)| := by exact_mod_cast Int.one_le_abs hb0
        rw [Real.norm_eq_abs, Real.norm_eq_abs, hb, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 3)]
        nlinarith [sq_nonneg |v 0|]
    nlinarith [norm_nonneg v]

private theorem L2_successiveMinimum_two : ZLattice.successiveMinimum L2 2 = 3 := by
  apply le_antisymm
  · refine ZLattice.successiveMinimum_le_of_linearIndependent rectBasis.linearIndependent
      (fun i ↦ Submodule.subset_span (Set.mem_range_self i)) (by norm_num) fun i ↦ ?_
    fin_cases i
    · simpa only [Fin.zero_eta, norm_rectBasis_zero] using (by norm_num : (1 : ℝ) ≤ 3)
    · simpa only [Fin.mk_one, norm_rectBasis_one] using le_rfl
  · by_contra hlt
    push Not at hlt
    obtain ⟨v, hli, hmem, hle⟩ :=
      ZLattice.exists_linearIndependent_norm_le_successiveMinimum L2 (k := 2)
        (by rw [finrank_euclideanSpace_fin])
    have hsub : Set.range v ⊆ (Submodule.span ℝ ({rectBasis 0} : Set Plane) : Set Plane) := by
      rintro _ ⟨i, rfl⟩
      obtain ⟨a, b, ha, hb⟩ := L2_mem_coords (hmem i)
      have hb0 : b = 0 := by
        by_contra hbn
        have h1 : (1 : ℝ) ≤ |(b : ℝ)| := by exact_mod_cast Int.one_le_abs hbn
        have hcoord : |v i 1| ≤ ‖v i‖ := by
          simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (v i) 1
        rw [hb, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at hcoord
        linarith [hle i]
      have hv_eq : v i = (a : ℝ) • rectBasis 0 := by
        ext j
        fin_cases j
        · simp [ha, rectBasis, Basis.isUnitSMul_apply]
        · simp [hb, hb0, rectBasis, Basis.isUnitSMul_apply]
      rw [hv_eq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    have hle1 : 2 ≤ 1 := by
      have hne0 : rectBasis 0 ≠ 0 := by
        intro h; have := norm_rectBasis_zero; rw [h, norm_zero] at this; norm_num at this
      calc
        2 = finrank ℝ (Submodule.span ℝ (Set.range v)) := by
          rw [finrank_span_eq_card hli, Fintype.card_fin]
        _ ≤ finrank ℝ (Submodule.span ℝ ({rectBasis 0} : Set Plane)) :=
          Submodule.finrank_mono (Submodule.span_le.2 hsub)
        _ = 1 := finrank_span_singleton hne0
    omega

/-- On `ℤ × 3ℤ`, `λ₁ = 1 < λ₂ = 3` strictly separates the two successive minima. -/
example : ZLattice.minimum L2 < ZLattice.successiveMinimum L2 2 := by
  rw [L2_minimum, L2_successiveMinimum_two]
  norm_num

private theorem log_twelve_div_pi_le_one : Real.log 12 / Real.pi ≤ 1 := by
  have he : (12 : ℝ) < Real.exp 3 := by
    have h1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    nlinarith
  have hlog : Real.log 12 < 3 := by
    have h := Real.log_lt_log (by norm_num) he
    rwa [Real.log_exp] at h
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  rw [div_le_one Real.pi_pos]
  linarith

private theorem L2_dual_small_at_three : ZLattice.gaussianMass D2 (1 / 3) 0 - 1 ≤ 1 / 2 := by
  apply ZLattice.gaussianMass_dual_sub_one_le_of_successiveMinimum L2
    (1 / 2) (by norm_num) 3 (by norm_num)
  rw [finrank_euclideanSpace_fin, L2_successiveMinimum_two]
  have harg : (2 : ℝ) * (2 : ℕ) * (1 + 1 / (1 / 2 : ℝ)) = 12 := by norm_num
  rw [harg]
  have hsqrt : Real.sqrt (Real.log 12 / Real.pi) ≤ 1 := by
    calc
      Real.sqrt (Real.log 12 / Real.pi) ≤ Real.sqrt 1 :=
        Real.sqrt_le_sqrt log_twelve_div_pi_le_one
      _ = 1 := Real.sqrt_one
  linarith

/-- Representative client: `gaussianMass_dual_sub_one_le_of_successiveMinimum` on `ℤ × 3ℤ`
discharges `ZLattice.tvDist_gaussian_quotient_le` at width `s = 3 = λ₂(L2)`. -/
example :
    tvDist
      (Measure.map (QuotientAddGroup.mk : Plane → Plane ⧸ L2.toAddSubgroup)
        (volume.withDensity (fun x : Plane ↦
          ENNReal.ofReal (gaussianWeight 3 x / 3 ^ finrank ℝ Plane))))
      ((ENNReal.ofReal (ZLattice.covolume L2))⁻¹ •
        Measure.map (QuotientAddGroup.mk : Plane → Plane ⧸ L2.toAddSubgroup)
          (volume.restrict (ZSpan.fundamentalDomain rectBasis))) ≤ 1 / 2 := by
  have hF : IsAddFundamentalDomain L2.toAddSubgroup.op (ZSpan.fundamentalDomain rectBasis) volume :=
    isAddFundamentalDomain_op_iff.mpr (ZSpan.isAddFundamentalDomain' rectBasis volume)
  exact (ZLattice.tvDist_gaussian_quotient_le L2 3 (by norm_num) hF).trans L2_dual_small_at_three

/-- MR07 Lemma 3.3 (`smoothingParameter_le_sqrt_log_mul_successiveMinimum`) on `ℤ × 3ℤ`:
`η_{1/2}(L2) ≤ 3`, chaining into `tvDist_gaussian_shift_quotient_le_of_smoothingParameter_le` at
an off-lattice center. -/
private theorem L2_eta_half_le_three : ZLattice.smoothingParameter L2 (1 / 2) ≤ 3 := by
  have h := ZLattice.smoothingParameter_le_sqrt_log_mul_successiveMinimum L2 (1 / 2) (by norm_num)
  rw [finrank_euclideanSpace_fin, L2_successiveMinimum_two] at h
  have harg : (2 : ℝ) * (2 : ℕ) * (1 + 1 / (1 / 2 : ℝ)) = 12 := by norm_num
  rw [harg] at h
  have hsqrt : Real.sqrt (Real.log 12 / Real.pi) ≤ 1 := by
    calc
      Real.sqrt (Real.log 12 / Real.pi) ≤ Real.sqrt 1 :=
        Real.sqrt_le_sqrt log_twelve_div_pi_le_one
      _ = 1 := Real.sqrt_one
  linarith

example :
    tvDist
      (Measure.map (QuotientAddGroup.mk : Plane → Plane ⧸ L2.toAddSubgroup)
        (volume.withDensity (fun x : Plane ↦
          ENNReal.ofReal
            (gaussianWeight 3 (x - !₂[(1 / 2 : ℝ), 1]) / 3 ^ finrank ℝ Plane))))
      ((ENNReal.ofReal (ZLattice.covolume L2))⁻¹ •
        Measure.map (QuotientAddGroup.mk : Plane → Plane ⧸ L2.toAddSubgroup)
          (volume.restrict (ZSpan.fundamentalDomain rectBasis))) ≤ 1 / 2 := by
  have hF : IsAddFundamentalDomain L2.toAddSubgroup.op (ZSpan.fundamentalDomain rectBasis) volume :=
    isAddFundamentalDomain_op_iff.mpr (ZSpan.isAddFundamentalDomain' rectBasis volume)
  exact ZLattice.tvDist_gaussian_shift_quotient_le_of_smoothingParameter_le L2 3 (by norm_num)
    !₂[(1 / 2 : ℝ), 1] hF (1 / 2) (by norm_num) L2_eta_half_le_three

/-! ### Lower-rank discrete lattice `ℤ × {0} ⊂ ℝ²` with off-span center -/

private abbrev Lsub : Submodule ℤ Plane :=
  Submodule.span ℤ ({rectBasis 0} : Set Plane)

private instance : DiscreteTopology Lsub :=
  DiscreteTopology.of_subset (inferInstance : DiscreteTopology L2)
    (Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨0, rfl⟩))

/-- `ZLattice.gaussianMass_le_gaussianMass_zero` applies to lower-rank discrete lattices and
centers outside their real span. -/
example : ZLattice.gaussianMass Lsub 1 (!₂[(1 / 2 : ℝ), 1]) ≤
    ZLattice.gaussianMass Lsub 1 0 :=
  ZLattice.gaussianMass_le_gaussianMass_zero Lsub 1 (by norm_num) !₂[(1 / 2 : ℝ), 1]

end CslibFrontierTests.DiscreteGaussianSuccessiveMinimum
