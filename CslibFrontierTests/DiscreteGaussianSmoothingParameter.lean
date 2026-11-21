/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.MeasureTheory.Group.FundamentalDomain
import CslibFrontier.Foundations.Probability.Gaussian.Convolution
import CslibFrontier.Foundations.Probability.Gaussian.Projection
import CslibFrontier.Foundations.Probability.Gaussian.Quotient
import CslibFrontier.Foundations.Probability.Gaussian.ShiftBounds
import CslibFrontier.Foundations.Probability.Gaussian.SmoothingParameter
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Concrete Nonvacuous Tests for `ZLattice.smoothingParameter`

Exercises the opaque `ZLattice.smoothingParameter` API from an ordinary `module` client (no
`import all`):

1. **1-D lattice `2ℤ ⊂ ℝ` (`D = (1/2)ℤ`, `λ₁(D) = 1/2`, `covolume = 2`):** strict positivity,
   exact attainment `ρ_{1 / η_{1/2}(2ℤ)}(D \ {0}) = 1/2`, Micciancio–Regev Lemma 3.2 upper bound
   `η_{1/2}(2ℤ) ≤ 2`, explicit lower bound `1/2 < η_{1/2}(2ℤ)` via `le_smoothingParameter_iff`
   and `smoothingParameter_le_iff` (non-vacuous on both sides), strict antitonicity, positive and
   negative scaling (`3 • L`, `(-2) • L`), and concrete instantiations of all five bridge lemmas
   (`ShiftBounds`, `Quotient`, `Convolution`, `Projection` real & `UnitAddCircle`) using the
   Pythagorean triple `(5, 12, 13)`.
2. **2-D self-dual lattice `ℤ² ⊂ EuclideanSpace ℝ (Fin 2)`:** Micciancio–Regev Lemma 3.2 gives
   `η_{1/4}(ℤ²) ≤ √2`.
3. **Dimension-0 lattice in `EuclideanSpace ℝ (Fin 0)`:** `smoothingParameter = 0` for all `ε`
   (positive and negative), order characterizations, and Lemma 3.2.
-/

set_option linter.privateModule false

open Module ProbabilityTheory MeasureTheory
open scoped ENNReal Pointwise RealInnerProductSpace

noncomputable section

namespace CslibFrontierTests.DiscreteGaussianSmoothingParameter

/-! ### 1. One-dimensional lattice `2ℤ ⊂ ℝ` -/

private def twoBasis : Basis Unit ℝ ℝ :=
  (Basis.singleton Unit ℝ).isUnitSMul (fun _ ↦ (show (2 : ℝ) ≠ 0 by norm_num).isUnit)

private abbrev L := Submodule.span ℤ (Set.range twoBasis)
private abbrev D := LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) L

private instance : DiscreteTopology D := ZLattice.discreteTopology_dualSubmodule L
private instance : IsZLattice ℝ D := ZLattice.isZLattice_dualSubmodule L

private theorem covolume_two : ZLattice.covolume L = 2 := by
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume (twoBasis.restrictScalars ℤ)
    (Basis.singleton Unit ℝ)]
  have hs : ZSpan.fundamentalDomain (Basis.singleton Unit ℝ) = Set.Ico (0 : ℝ) 1 := by
    ext x
    simp [ZSpan.fundamentalDomain, Basis.singleton_repr]
  rw [hs]
  norm_num [twoBasis, Basis.det_apply, Matrix.det_unique, Function.comp_def]

private theorem half_mem_D : (1 / 2 : ℝ) ∈ D := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    apply Submodule.mem_one.mpr
    exact ⟨1, by norm_num [twoBasis, Basis.isUnitSMul_apply]⟩
  | zero => simp
  | add x y _ _ hx' hy' => simpa only [map_add] using add_mem hx' hy'
  | smul n x _ hx' => simpa only [LinearMap.map_smul_of_tower] using Submodule.smul_mem _ n hx'

private theorem neg_half_mem_D : (-1 / 2 : ℝ) ∈ D := by
  simpa only [neg_div] using D.neg_mem half_mem_D

private theorem dual_gap (w : D) (hw : w ≠ 0) : (1 / 2 : ℝ) ≤ ‖(w : ℝ)‖ := by
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

private theorem minimum_D : ZLattice.minimum D = 1 / 2 := by
  apply le_antisymm
  · have hle := ZLattice.minimum_le_norm half_mem_D (by norm_num)
    simpa only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hle
  · have hDne : D ≠ ⊥ := by
      intro hbot
      have hmem : (1 / 2 : ℝ) ∈ (⊥ : Submodule ℤ ℝ) := hbot ▸ half_mem_D
      have h0 : (1 / 2 : ℝ) = 0 := (Submodule.mem_bot ℤ).mp hmem
      norm_num at h0
    rw [ZLattice.le_minimum_iff hDne]
    intro v hv hv0
    exact dual_gap ⟨v, hv⟩ (fun h ↦ hv0 (congrArg Subtype.val h))

/-- Positivity of `η_{1/2}(2ℤ)`. -/
example : 0 < ZLattice.smoothingParameter L (1 / 2) :=
  ZLattice.smoothingParameter_pos L (by norm_num)

/-- Attainment: the nonzero dual Gaussian mass at `η_{1/2}(2ℤ)` equals `1/2` exactly. -/
example : ZLattice.gaussianMass D (1 / ZLattice.smoothingParameter L (1 / 2)) 0 - 1 = 1 / 2 :=
  ZLattice.gaussianMass_dual_smoothingParameter L (by norm_num)

/-- Micciancio–Regev Lemma 3.2 on `2ℤ ⊂ ℝ`: `η_{1/2}(2ℤ) ≤ 2`. -/
private theorem eta_half_le_two : ZLattice.smoothingParameter L (1 / 2) ≤ 2 := by
  have h := ZLattice.smoothingParameter_le_sqrt_div_minimum_dual L
  rw [finrank_self, pow_one, Nat.cast_one, Real.sqrt_one, minimum_D] at h
  norm_num at h
  exact h

/-- Explicit lower bound on the nonzero dual mass at width `s = 1/2`: the two points `±1/2 ∈ D`
already contribute more than `3/2`, proving `1/2 < η_{1/2}(2ℤ)` and `1/2 ≤ η_1(2ℤ)`. -/
private theorem dualMass_half_gt :
    (3 / 2 : ℝ) < ZLattice.gaussianMass D (1 / (1 / 2 : ℝ)) 0 - 1 := by
  classical
  rw [ZLattice.gaussianMass_zero_sub_one_eq_tsum D (1 / (1 / 2 : ℝ)) (by norm_num)]
  have hsum : Summable (fun w : ↥{w : D | w ≠ 0} ↦ gaussianWeight (1 / (1 / 2 : ℝ)) (w : ℝ)) := by
    simpa only [Function.comp_def, sub_zero] using
      (ZLattice.summable_gaussianWeight D (1 / (1 / 2 : ℝ)) (by norm_num) 0).comp_injective
        (Subtype.val_injective (p := (· ∈ ({w : D | w ≠ 0} : Set D))))
  let w₁ : ↥{w : D | w ≠ 0} :=
    ⟨⟨(1 / 2 : ℝ), half_mem_D⟩, fun h ↦ by
      have h0 : (1 / 2 : ℝ) = 0 := congrArg Subtype.val h
      norm_num at h0⟩
  let w₂ : ↥{w : D | w ≠ 0} :=
    ⟨⟨(-1 / 2 : ℝ), neg_half_mem_D⟩, fun h ↦ by
      have h0 : (-1 / 2 : ℝ) = 0 := congrArg Subtype.val h
      norm_num at h0⟩
  have hne : w₁ ≠ w₂ := by
    intro h
    have h0 : (1 / 2 : ℝ) = -1 / 2 := congrArg (fun u : ↥{w : D | w ≠ 0} ↦ (u.val : ℝ)) h
    norm_num at h0
  have hfin := hsum.sum_le_tsum ({w₁, w₂} : Finset ↥{w : D | w ≠ 0})
    fun w _ ↦ (gaussianWeight_pos _ _).le
  rw [Finset.sum_pair hne] at hfin
  have hw₁ : (3 / 4 : ℝ) < gaussianWeight (1 / (1 / 2 : ℝ)) (w₁.val : ℝ) := by
    have hnorm : ‖(w₁.val : ℝ)‖ = 1 / 2 := by
      change ‖(1 / 2 : ℝ)‖ = 1 / 2
      norm_num
    have hexp : -Real.pi * ‖(w₁.val : ℝ)‖ ^ 2 / (1 / (1 / 2 : ℝ)) ^ 2 = -Real.pi / 16 := by
      rw [hnorm]
      ring
    rw [gaussianWeight, hexp]
    have h1 := Real.add_one_le_exp (-Real.pi / 16)
    linarith [Real.pi_lt_four]
  have hw₂ : (3 / 4 : ℝ) < gaussianWeight (1 / (1 / 2 : ℝ)) (w₂.val : ℝ) := by
    have hnorm : ‖(w₂.val : ℝ)‖ = 1 / 2 := by
      change ‖(-1 / 2 : ℝ)‖ = 1 / 2
      norm_num
    have hexp : -Real.pi * ‖(w₂.val : ℝ)‖ ^ 2 / (1 / (1 / 2 : ℝ)) ^ 2 = -Real.pi / 16 := by
      rw [hnorm]
      ring
    rw [gaussianWeight, hexp]
    have h1 := Real.add_one_le_exp (-Real.pi / 16)
    linarith [Real.pi_lt_four]
  linarith

/-- Non-vacuity on the lower side via `le_smoothingParameter_iff`: `1/2 ≤ η_{1/2}(2ℤ)` and
`1/2 ≤ η_1(2ℤ)`. -/
example : (1 / 2 : ℝ) ≤ ZLattice.smoothingParameter L (1 / 2) :=
  (ZLattice.le_smoothingParameter_iff L (by norm_num) (by norm_num)).mpr
    (by linarith [dualMass_half_gt])

example : (1 / 2 : ℝ) ≤ ZLattice.smoothingParameter L 1 :=
  (ZLattice.le_smoothingParameter_iff L (by norm_num) (by norm_num)).mpr
    (by linarith [dualMass_half_gt])

/-- Two-sided concrete bracket `1/2 < η_{1/2}(2ℤ) ≤ 2`, exercising both directions of
`smoothingParameter_le_iff` and MR07 Lemma 3.2. -/
example :
    (1 / 2 : ℝ) < ZLattice.smoothingParameter L (1 / 2) ∧
      ZLattice.smoothingParameter L (1 / 2) ≤ 2 := by
  refine ⟨?_, eta_half_le_two⟩
  by_contra hle
  have hmass := (ZLattice.smoothingParameter_le_iff L (by norm_num) (by norm_num)).mp
    (le_of_not_gt hle)
  linarith [dualMass_half_gt]

/-- Strict antitonicity and antitonicity in `ε`. -/
example : ZLattice.smoothingParameter L 1 < ZLattice.smoothingParameter L (1 / 2) :=
  ZLattice.smoothingParameter_strictAnti L (by norm_num) (by norm_num)

example : ZLattice.smoothingParameter L 1 ≤ ZLattice.smoothingParameter L (1 / 2) :=
  ZLattice.smoothingParameter_anti L (by norm_num) (by norm_num)

/-- Positive and negative scaling of `smoothingParameter`, combined with MR07 Lemma 3.2. -/
example : ZLattice.smoothingParameter ((3 : ℝ) • L) (1 / 2) =
    3 * ZLattice.smoothingParameter L (1 / 2) := by
  rw [ZLattice.smoothingParameter_smul L (by norm_num), abs_of_pos (by norm_num)]

example : ZLattice.smoothingParameter ((-2 : ℝ) • L) (1 / 2) =
    2 * ZLattice.smoothingParameter L (1 / 2) := by
  rw [ZLattice.smoothingParameter_smul L (by norm_num)]
  norm_num

example : ZLattice.smoothingParameter ((3 : ℝ) • L) (1 / 2) ≤ 6 := by
  rw [ZLattice.smoothingParameter_smul L (by norm_num), abs_of_pos (by norm_num)]
  linarith [eta_half_le_two]

/-- Bridge 1 (`ShiftBounds`, Regev09 Claim 3.8): shifted mass interval at off-lattice center `1`. -/
example : ZLattice.gaussianMass L 2 1 ∈ Set.Icc (1 / 2) (3 / 2) := by
  have h := ZLattice.gaussianMass_mem_Icc_of_smoothingParameter_le L 2 (by norm_num)
    (1 / 2) (by norm_num) eta_half_le_two 1
  norm_num [covolume_two] at h ⊢
  exact h

private theorem basis_domain_op {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Finite ι]
    (b : Basis ι ℝ E) :
    IsAddFundamentalDomain (Submodule.span ℤ (Set.range b)).toAddSubgroup.op
      (ZSpan.fundamentalDomain b) volume :=
  isAddFundamentalDomain_op_iff.mpr (ZSpan.isAddFundamentalDomain' b volume)

/-- Bridge 2 (`Quotient`, MR07 Lemma 4.1 at `c = 0`): full-`L¹` distance of the centered Gaussian
mod `2ℤ` from uniform above `η_{1/2}(2ℤ) ≤ 2`. -/
example : tvDist
    (Measure.map (QuotientAddGroup.mk : ℝ → ℝ ⧸ L.toAddSubgroup)
      (volume.withDensity (fun x : ℝ ↦ ENNReal.ofReal (gaussianWeight 2 x / 2))))
    ((1 / 2 : ℝ≥0∞) • Measure.map (QuotientAddGroup.mk : ℝ → ℝ ⧸ L.toAddSubgroup)
      (volume.restrict (ZSpan.fundamentalDomain twoBasis))) ≤ 1 / 2 := by
  have h := ZLattice.tvDist_gaussian_shift_quotient_le_of_smoothingParameter_le L 2 (by norm_num) 0
    (basis_domain_op twoBasis) (1 / 2) (by norm_num) eta_half_le_two
  simpa [covolume_two] using h

/-- Bridge 2b (`Quotient`, MR07 Lemma 4.1): full-`L¹` distance of an off-center Gaussian
(`c = 1 / 3`) mod `2ℤ` from uniform above `η_{1/2}(2ℤ) ≤ 2`. -/
example : tvDist
    (Measure.map (QuotientAddGroup.mk : ℝ → ℝ ⧸ L.toAddSubgroup)
      (volume.withDensity (fun x : ℝ ↦ ENNReal.ofReal (gaussianWeight 2 (x - 1 / 3) / 2))))
    ((1 / 2 : ℝ≥0∞) • Measure.map (QuotientAddGroup.mk : ℝ → ℝ ⧸ L.toAddSubgroup)
      (volume.restrict (ZSpan.fundamentalDomain twoBasis))) ≤ 1 / 2 := by
  have h := ZLattice.tvDist_gaussian_shift_quotient_le_of_smoothingParameter_le L 2 (by norm_num)
    (1 / 3) (basis_domain_op twoBasis) (1 / 2) (by norm_num) eta_half_le_two
  simpa [covolume_two] using h

/-- Concrete bound `η_{1/4}(2ℤ) ≤ 3` (discharging `ε < 1/2` for Bridges 3–5). -/
private theorem eta_quarter_le_three : ZLattice.smoothingParameter L (1 / 4) ≤ 3 := by
  apply ZLattice.smoothingParameter_le_of_dual_mass_le L (by norm_num)
  apply ZLattice.gaussianMass_dual_sub_one_le_of_gap L 3 (by norm_num) (1 / 2) (by norm_num)
    dual_gap (1 / 4) (by norm_num)
  rw [finrank_self, pow_one]
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hexp5 : (10 : ℝ) < Real.exp (27 * Real.pi / 16) := by
    have hpi : (5 : ℝ) < 27 * Real.pi / 16 := by linarith [Real.pi_gt_three]
    calc
      (10 : ℝ) < (2.7 : ℝ) ^ 5 := by norm_num
      _ < (Real.exp 1) ^ 5 := pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
      _ = Real.exp 5 := by rw [← Real.exp_nat_mul]; norm_num
      _ < Real.exp (27 * Real.pi / 16) := Real.exp_lt_exp.mpr hpi
  have hneg : Real.exp (-3 * Real.pi * (3 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ 2 / 4) < 1 / 10 := by
    rw [show -3 * Real.pi * (3 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ 2 / 4 = -(27 * Real.pi / 16) by ring,
      Real.exp_neg, inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) hexp5
  linarith

/-- Bridge 3 (`Convolution`, Regev09 Claim 3.9) with Pythagorean widths `(5, 12, 13)`. -/
example : tvDist
    (Measure.conv ((ZLattice.discreteGaussian L 5 (by norm_num) (-1)).toMeasure.map
      (fun z : L ↦ (z : ℝ) + 1))
      (volume.withDensity (fun x : ℝ ↦ ENNReal.ofReal (gaussianWeight 12 x / 12))))
    (volume.withDensity (fun x : ℝ ↦ ENNReal.ofReal (gaussianWeight 13 x / 13))) ≤ 1 := by
  have hη : ZLattice.smoothingParameter L (1 / 4) ≤ 5 * 12 / 13 :=
    eta_quarter_le_three.trans (by norm_num)
  have h := ZLattice.tvDist_conv_discreteGaussian_le_of_smoothingParameter_le L 5 12 13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 (1 / 4) (by norm_num) (by norm_num) hη
  simpa using h

/-- Bridges 4 & 5 (`Projection`, Regev09 Corollary 3.10 real & `UnitAddCircle`) with `r = 5`,
`α = 12`, `z = 1`. -/
private theorem eta_quarter_le_proj_width :
    ZLattice.smoothingParameter L (1 / 4) ≤
      1 / Real.sqrt (1 / (5 : ℝ) ^ 2 + (‖(1 : ℝ)‖ / 12) ^ 2) := by
  have hsqrt : Real.sqrt (1 / (5 : ℝ) ^ 2 + (‖(1 : ℝ)‖ / 12) ^ 2) = 13 / 60 := by
    rw [norm_one, show 1 / (5 : ℝ) ^ 2 + (1 / 12 : ℝ) ^ 2 = (13 / 60 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [hsqrt]
  exact eta_quarter_le_three.trans (by norm_num)

example : tvDist
    (Measure.conv
      (((ZLattice.discreteGaussian L 5 (by norm_num) (-1)).toMeasure.map
        (fun v : L ↦ (v : ℝ) + 1)).map (fun x ↦ ⟪(1 : ℝ), x⟫))
      (gaussianReal 0 (((12 : ℝ) ^ 2 / (2 * Real.pi)).toNNReal)))
    (gaussianReal 0 ((((5 * ‖(1 : ℝ)‖) ^ 2 + 12 ^ 2) / (2 * Real.pi)).toNNReal)) ≤ 1 := by
  have h := ZLattice.tvDist_conv_map_inner_discreteGaussian_le_of_smoothingParameter_le L 5 12
    (by norm_num) (by norm_num) 1 1 (1 / 4) (by norm_num) (by norm_num) eta_quarter_le_proj_width
  linarith

example : tvDist
    ((Measure.conv
      (((ZLattice.discreteGaussian L 5 (by norm_num) (-1)).toMeasure.map
        (fun v : L ↦ (v : ℝ) + 1)).map (fun x ↦ ⟪(1 : ℝ), x⟫))
      (gaussianReal 0 (((12 : ℝ) ^ 2 / (2 * Real.pi)).toNNReal))).map
        (fun x : ℝ ↦ (x : UnitAddCircle)))
    ((gaussianReal 0 ((((5 * ‖(1 : ℝ)‖) ^ 2 + 12 ^ 2) / (2 * Real.pi)).toNNReal)).map
      (fun x : ℝ ↦ (x : UnitAddCircle))) ≤ 1 := by
  have h := ZLattice.tvDist_map_mod_one_conv_map_inner_discreteGaussian_le_of_smoothingParameter_le
    L 5 12 (by norm_num) (by norm_num) 1 1 (1 / 4) (by norm_num) (by norm_num)
    eta_quarter_le_proj_width
  linarith

/-! ### 2. Two-dimensional self-dual lattice `ℤ² ⊂ EuclideanSpace ℝ (Fin 2)` -/

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev b2 : Basis (Fin 2) ℝ E2 := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
private abbrev Z2 := Submodule.span ℤ (Set.range b2)
private abbrev Z2Dual := LinearMap.BilinForm.dualSubmodule (innerₗ E2) Z2

private instance : DiscreteTopology Z2Dual := ZLattice.discreteTopology_dualSubmodule Z2
private instance : IsZLattice ℝ Z2Dual := ZLattice.isZLattice_dualSubmodule Z2

private theorem e0_mem_Z2Dual : b2 0 ∈ Z2Dual := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    apply Submodule.mem_one.mpr
    fin_cases i
    · exact ⟨1, by simp [b2, EuclideanSpace.basisFun_apply]⟩
    · exact ⟨0, by simp [b2, EuclideanSpace.basisFun_apply, PiLp.inner_apply]⟩
  | zero => simp
  | add x y _ _ hx' hy' => simpa only [map_add] using add_mem hx' hy'
  | smul n x _ hx' => simpa only [LinearMap.map_smul_of_tower] using Submodule.smul_mem _ n hx'

private theorem minimum_Z2Dual : ZLattice.minimum Z2Dual = 1 := by
  apply le_antisymm
  · have hle := ZLattice.minimum_le_norm e0_mem_Z2Dual (b2.ne_zero 0)
    have hn : ‖b2 0‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp [b2, EuclideanSpace.basisFun_apply]
    rwa [hn] at hle
  · have hne : Z2Dual ≠ ⊥ := by
      intro hbot
      have h0 : b2 0 = 0 := (Submodule.mem_bot ℤ).mp (hbot ▸ e0_mem_Z2Dual)
      exact b2.ne_zero 0 h0
    rw [ZLattice.le_minimum_iff hne]
    intro v hv hv0
    have hcoord : ∀ i : Fin 2, ∃ k : ℤ, (k : ℝ) = v.ofLp i := by
      intro i
      have hm := hv (b2 i) (Submodule.subset_span (Set.mem_range_self i))
      obtain ⟨k, hk⟩ := Submodule.mem_one.mp hm
      refine ⟨k, ?_⟩
      simpa [b2, EuclideanSpace.basisFun_apply, PiLp.inner_apply, Fin.sum_univ_two,
        real_inner_comm] using hk
    obtain ⟨k₀, hk₀⟩ := hcoord 0
    obtain ⟨k₁, hk₁⟩ := hcoord 1
    have hkne : k₀ ≠ 0 ∨ k₁ ≠ 0 := by
      by_contra hboth
      push Not at hboth
      apply hv0
      ext i
      fin_cases i
      · simp [← hk₀, hboth.1]
      · simp [← hk₁, hboth.2]
    have hsq : (1 : ℝ) ≤ ∑ i : Fin 2, ‖v.ofLp i‖ ^ 2 := by
      rw [Fin.sum_univ_two, ← hk₀, ← hk₁, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
      rcases hkne with h0 | h1
      · have hge : (1 : ℝ) ≤ |(k₀ : ℝ)| := by exact_mod_cast (Int.one_le_abs h0)
        nlinarith [sq_abs (k₀ : ℝ), sq_nonneg (k₁ : ℝ)]
      · have hge : (1 : ℝ) ≤ |(k₁ : ℝ)| := by exact_mod_cast (Int.one_le_abs h1)
        nlinarith [sq_abs (k₁ : ℝ), sq_nonneg (k₀ : ℝ)]
    rw [EuclideanSpace.norm_eq]
    exact Real.one_le_sqrt.mpr hsq

/-- Micciancio–Regev Lemma 3.2 in dimension 2: `η_{1/4}(ℤ²) ≤ √2`. -/
example : ZLattice.smoothingParameter Z2 (1 / 4) ≤ Real.sqrt 2 := by
  have h := ZLattice.smoothingParameter_le_sqrt_div_minimum_dual Z2
  rw [finrank_euclideanSpace_fin, minimum_Z2Dual, div_one] at h
  norm_num at h
  exact h

/-! ### 3. Dimension-zero lattice in `EuclideanSpace ℝ (Fin 0)` -/

private abbrev Point := EuclideanSpace ℝ (Fin 0)
private abbrev pointBasis := (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis
private abbrev pointLattice := Submodule.span ℤ (Set.range pointBasis)

example (ε : ℝ) : ZLattice.smoothingParameter pointLattice ε = 0 :=
  ZLattice.smoothingParameter_eq_zero_of_subsingleton pointLattice ε

example : ZLattice.smoothingParameter pointLattice (-1) = 0 :=
  ZLattice.smoothingParameter_eq_zero_of_subsingleton pointLattice (-1)

example (s : ℝ) (hs : 0 < s) (ε : ℝ) (hε : 0 < ε) :
    ZLattice.smoothingParameter pointLattice ε ≤ s ∧
      ¬ s ≤ ZLattice.smoothingParameter pointLattice ε := by
  refine ⟨?_, ?_⟩
  · rw [ZLattice.smoothingParameter_eq_zero_of_subsingleton]
    exact hs.le
  · rw [ZLattice.le_smoothingParameter_iff pointLattice hs hε]
    have hsub : ZLattice.gaussianMass
        (LinearMap.BilinForm.dualSubmodule (innerₗ Point) pointLattice) (1 / s) 0 - 1 = 0 := by
      let D0 := LinearMap.BilinForm.dualSubmodule (innerₗ Point) pointLattice
      change ZLattice.gaussianMass D0 (1 / s) 0 - 1 = 0
      rw [ZLattice.gaussianMass, tsum_eq_single (0 : D0)
        (fun w hw ↦ absurd (Subsingleton.elim w 0) hw)]
      simp [gaussianWeight]
    linarith

example : ZLattice.smoothingParameter pointLattice ((1 / 2 : ℝ) ^ finrank ℝ Point) ≤
    Real.sqrt (finrank ℝ Point) /
      ZLattice.minimum (LinearMap.BilinForm.dualSubmodule (innerₗ Point) pointLattice) :=
  ZLattice.smoothingParameter_le_sqrt_div_minimum_dual pointLattice

end CslibFrontierTests.DiscreteGaussianSmoothingParameter
