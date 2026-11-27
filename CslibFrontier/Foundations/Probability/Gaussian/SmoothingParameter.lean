/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.Lattice.Minimum
public import CslibFrontier.Foundations.Probability.Gaussian.Discrete
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice

import CslibFrontier.Foundations.Analysis.Lattice.Dual
import CslibFrontier.Foundations.Probability.Gaussian.CenteredTail
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Basic.Real.Pointwise

/-!
# The smoothing parameter of a lattice

The smoothing parameter `η_ε(L)` of a lattice `L` at positive error `ε > 0` is the smallest
positive width `s` such that the nonzero reciprocal-width dual Gaussian mass
`ρ_{1/s}(L* \ {0})` is at most `ε` ([MicciancioRegev2007], Definition 3.1).

For a full-rank discrete lattice in positive dimension, `s ↦ ρ_{1/s}(L* \ {0})` is continuous and
strictly decreasing on `(0, ∞)` with limits `∞` at `0⁺` and `0` at `∞`, so `η_ε(L)` is strictly
positive, attained with exact equality `ρ_{1 / η_ε(L)}(L* \ {0}) = ε`, and strictly decreasing in
`ε`. In dimension zero, `L* \ {0}` is empty and `η_ε(L) = 0` for all `ε`; the order
characterizations `η_ε(L) ≤ s ↔ ρ_{1/s}(L* \ {0}) ≤ ε` and `s ≤ η_ε(L) ↔ ε ≤ ρ_{1/s}(L* \ {0})`
hold uniformly in every dimension (including dimension zero) for all `s > 0` and `ε > 0`.

Smoothing-parameter conversions for the shifted-mass, quotient, convolution, and scalar-projection
bounds live alongside their consuming theorems in `Gaussian.ShiftBounds`, `Gaussian.Quotient`,
`Gaussian.Convolution`, and `Gaussian.Projection`.

## Main definitions

* `ZLattice.smoothingParameter`: the smoothing parameter `η_ε(L)` ([MicciancioRegev2007],
  Definition 3.1).

## Main results

* `ZLattice.smoothingParameter_pos`: strict positivity of `η_ε(L)` for full-rank discrete lattices
  in positive dimension and `ε > 0`.
* `ZLattice.gaussianMass_dual_smoothingParameter`: attainment of the minimum with equality
  `ρ_{1 / η_ε(L)}(L* \ {0}) = ε` in positive dimension.
* `ZLattice.smoothingParameter_le_iff` and `ZLattice.le_smoothingParameter_iff`: exact order
  characterizations of `η_ε(L)` against `ρ_{1/s}(L* \ {0})` in all dimensions (including zero).
* `ZLattice.smoothingParameter_anti` and `ZLattice.smoothingParameter_strictAnti`: monotonicity
  (and strict monotonicity in positive dimension) in `ε`.
* `ZLattice.smoothingParameter_smul`: scaling `η_ε(c • L) = |c| * η_ε(L)` for `c ≠ 0`.
* `ZLattice.smoothingParameter_le_sqrt_div_minimum_dual`: Micciancio–Regev Lemma 3.2,
  `η_{2^{-n}}(L) ≤ √n / λ₁(L*)` for every full-rank discrete lattice of dimension `n`.

## References

* [MicciancioRegev2007], Definition 3.1 (p. 10) and Lemma 3.2 (pp. 10–11) of the December 27, 2005
  author's copy (`SIAM J. Comput.` 37(1):267–302, 2007).
-/

public section

noncomputable section

open Filter Module ProbabilityTheory
open scoped Pointwise RealInnerProductSpace Topology

namespace ZLattice

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (L : Submodule ℤ E)

/-- The smoothing parameter `η_ε(L)` of a lattice `L` at error `ε > 0`
([MicciancioRegev2007], Definition 3.1, p. 10 of the author's copy): the infimum of all
positive widths `s` such that the nonzero reciprocal-width dual Gaussian mass
`ρ_{1/s}(L* \ {0})` is at most `ε`.

For a full-rank discrete lattice in positive dimension and `ε > 0`, this infimum is strictly
positive and attained with equality (`smoothingParameter_pos`,
`gaussianMass_dual_smoothingParameter`). In dimension zero, `L* \ {0}` is empty and
`smoothingParameter L ε = 0` for all `ε`. -/
def smoothingParameter (ε : ℝ) : ℝ :=
  sInf {s : ℝ | 0 < s ∧
    gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ≤ ε}

/-- The smoothing parameter is always nonnegative. -/
theorem smoothingParameter_nonneg (ε : ℝ) : 0 ≤ smoothingParameter L ε :=
  Real.sInf_nonneg fun _ hs ↦ hs.1.le

/-- Any positive width at which the nonzero dual Gaussian mass is at most `ε` upper-bounds
`η_ε(L)`. -/
theorem smoothingParameter_le_of_dual_mass_le {s ε : ℝ} (hs : 0 < s)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ≤ ε) :
    smoothingParameter L ε ≤ s :=
  csInf_le ⟨0, fun _ h ↦ h.1.le⟩ ⟨hs, hdual⟩

private theorem dualMass_eq_zero_of_subsingleton [Subsingleton E] (s : ℝ) :
    gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 = 0 := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  change gaussianMass D (1 / s) 0 - 1 = 0
  rw [gaussianMass, tsum_eq_single (0 : D) (fun w hw ↦ absurd (Subsingleton.elim w 0) hw)]
  simp [gaussianWeight]

/-- In dimension zero, the dual lattice has no nonzero points, so `η_ε(L) = 0` for all `ε`.
(For `ε ≥ 0` the admissible set is `(0, ∞)` with infimum `0`; for `ε < 0` it is empty.) -/
theorem smoothingParameter_eq_zero_of_subsingleton [Subsingleton E] (ε : ℝ) :
    smoothingParameter L ε = 0 := by
  by_cases hε : 0 ≤ ε
  · have hset :
        {s : ℝ | 0 < s ∧
          gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ≤ ε} =
        Set.Ioi 0 := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_Ioi, dualMass_eq_zero_of_subsingleton L s, hε, and_true]
    rw [smoothingParameter, hset, csInf_Ioi]
  · have hset :
        {s : ℝ | 0 < s ∧
          gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ≤ ε} =
        ∅ := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, dualMass_eq_zero_of_subsingleton L s,
        hε, and_false]
    rw [smoothingParameter, hset, Real.sInf_empty]

private theorem dualSubmodule_smul {c : ℝ} (hc : c ≠ 0) :
    LinearMap.BilinForm.dualSubmodule (innerₗ E) (c • L) =
      c⁻¹ • LinearMap.BilinForm.dualSubmodule (innerₗ E) L := by
  ext w
  rw [LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · intro hw
    refine ⟨c • w, fun y hy ↦ ?_, by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
    have hcy : c • y ∈ c • L := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y, hy, rfl⟩
    have h := hw (c • y) hcy
    simpa only [innerₗ_apply_apply, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real] using h
  · rintro ⟨u, hu, rfl⟩ x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    have h := hu y hy
    simpa only [innerₗ_apply_apply, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, ← mul_assoc, mul_inv_cancel₀ hc, one_mul] using h

private theorem gaussianMass_smul_zero (M : Submodule ℤ E) {c : ℝ} (hc : c ≠ 0) (s : ℝ) :
    gaussianMass (c • M) s 0 = gaussianMass M (s / |c|) 0 := by
  let e : M ≃ ↥(c • M) :=
    { toFun := fun v ↦ ⟨c • (v : E),
        (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨(v : E), v.property, rfl⟩⟩
      invFun := fun w ↦ ⟨c⁻¹ • (w : E), by
        obtain ⟨y, hy, hwy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp w.property
        have h : c⁻¹ • (w : E) = y := by rw [← hwy, inv_smul_smul₀ hc]
        rwa [h]⟩
      left_inv := fun v ↦ Subtype.ext (inv_smul_smul₀ hc (v : E))
      right_inv := fun w ↦ Subtype.ext (smul_inv_smul₀ hc (w : E)) }
  unfold gaussianMass
  rw [← e.tsum_eq]
  apply tsum_congr
  intro v
  simp only [e, Equiv.coe_fn_mk, sub_zero, gaussianWeight, norm_smul, Real.norm_eq_abs]
  congr 1
  by_cases hs : s = 0
  · simp [hs]
  · have habs : |c| ≠ 0 := abs_ne_zero.mpr hc
    rw [mul_pow, div_pow]
    field_simp

/-- Scaling a lattice by a nonzero real scalar `c` scales its smoothing parameter by `|c|`. -/
theorem smoothingParameter_smul {c : ℝ} (hc : c ≠ 0) (ε : ℝ) :
    smoothingParameter (c • L) ε = |c| * smoothingParameter L ε := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have habs_pos : 0 < |c| := abs_pos.mpr hc
  have hset :
      {s : ℝ | 0 < s ∧
        gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) (c • L)) (1 / s) 0 - 1 ≤ ε} =
      |c| • {t : ℝ | 0 < t ∧ gaussianMass D (1 / t) 0 - 1 ≤ ε} := by
    ext s
    rw [dualSubmodule_smul L hc]
    change (0 < s ∧ gaussianMass (c⁻¹ • D) (1 / s) 0 - 1 ≤ ε) ↔
      s ∈ |c| • {t : ℝ | 0 < t ∧ gaussianMass D (1 / t) 0 - 1 ≤ ε}
    rw [gaussianMass_smul_zero D (inv_ne_zero hc) (1 / s), abs_inv, Set.mem_smul_set]
    have hdiv : (1 / s) / |c|⁻¹ = 1 / (s / |c|) := by
      rw [div_inv_eq_mul, one_div_div, one_div_mul_eq_div]
    rw [hdiv]
    constructor
    · rintro ⟨hs, hle⟩
      refine ⟨s / |c|, ⟨div_pos hs habs_pos, hle⟩, ?_⟩
      change |c| * (s / |c|) = s
      exact mul_div_cancel₀ s habs_pos.ne'
    · rintro ⟨t, ⟨ht, hle⟩, rfl⟩
      change 0 < |c| * t ∧ gaussianMass D (1 / (|c| * t / |c|)) 0 - 1 ≤ ε
      rw [mul_div_cancel_left₀ t habs_pos.ne']
      exact ⟨mul_pos habs_pos ht, hle⟩
  rw [smoothingParameter, hset, Real.sInf_smul_of_nonneg (abs_nonneg c)]
  rfl

end Basic

section FullRank

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem gaussianWeight_one_div (s : ℝ) (x : E) :
    gaussianWeight (1 / s) x = Real.exp (-Real.pi * ‖x‖ ^ 2 * s ^ 2) := by
  unfold gaussianWeight
  by_cases hs : s = 0
  · simp [hs]
  · congr 1
    field_simp

private theorem summable_dual_nonzero {s : ℝ} (hs : 0 < s) :
    Summable (fun w : ↥{w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L | w ≠ 0} ↦
      gaussianWeight (1 / s) (w : E)) := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  simpa only [Function.comp_def, sub_zero] using
    (summable_gaussianWeight D (1 / s) (one_div_pos.mpr hs) 0).comp_injective
      (Subtype.val_injective (p := (· ∈ ({w : D | w ≠ 0} : Set D))))

private theorem exists_dual_ne_zero [Nontrivial E] :
    ∃ w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L, w ≠ 0 := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  have hlat : IsZLattice ℝ D := isZLattice_dualSubmodule L
  by_contra h
  push Not at h
  have hbot : Submodule.span ℝ (D : Set E) = ⊥ := by
    rw [Submodule.span_eq_bot]
    intro x hx
    exact congrArg Subtype.val (h ⟨x, hx⟩)
  exact bot_ne_top (hbot.symm.trans hlat.span_top)

private theorem dualMass_antitone {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (h : s₁ ≤ s₂) :
    gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s₂) 0 - 1 ≤
      gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s₁) 0 - 1 := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  have hs₂ : 0 < s₂ := hs₁.trans_le h
  have hm := gaussianMass_le_of_le D (one_div_pos.mpr hs₂) (one_div_le_one_div_of_le hs₁ h) 0
  linarith

private theorem dualMass_strictAnti [Nontrivial E] {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (h : s₁ < s₂) :
    gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s₂) 0 - 1 <
      gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s₁) 0 - 1 := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  have hs₂ : 0 < s₂ := hs₁.trans h
  rw [gaussianMass_zero_sub_one_eq_tsum D (1 / s₂) (one_div_pos.mpr hs₂),
    gaussianMass_zero_sub_one_eq_tsum D (1 / s₁) (one_div_pos.mpr hs₁)]
  obtain ⟨w₀, hw₀⟩ := exists_dual_ne_zero L
  have hle : ∀ w : ↥{w : D | w ≠ 0},
      gaussianWeight (1 / s₂) (w : E) ≤ gaussianWeight (1 / s₁) (w : E) :=
    fun w ↦ gaussianWeight_le_of_le (one_div_pos.mpr hs₂) (one_div_le_one_div_of_le hs₁ h.le) _
  have hlt : gaussianWeight (1 / s₂) ((⟨w₀, hw₀⟩ : ↥{w : D | w ≠ 0}) : E) <
      gaussianWeight (1 / s₁) ((⟨w₀, hw₀⟩ : ↥{w : D | w ≠ 0}) : E) := by
    rw [gaussianWeight_one_div, gaussianWeight_one_div]
    apply Real.exp_lt_exp.mpr
    have hnorm : 0 < ‖(w₀ : E)‖ := norm_pos_iff.mpr fun h0 ↦ hw₀ (Subtype.ext h0)
    have hsq : s₁ ^ 2 < s₂ ^ 2 := by nlinarith
    have hc : 0 < Real.pi * ‖(w₀ : E)‖ ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hnorm)
    nlinarith
  exact (summable_dual_nonzero L hs₂).tsum_lt_tsum hle hlt (summable_dual_nonzero L hs₁)

private theorem continuousAt_dualMass {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ContinuousAt
      (fun s : ℝ ↦ gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1)
      s₀ := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  let a := s₀ / 2
  have ha : 0 < a := half_pos hs₀
  have hcont_tsum : ContinuousOn
      (fun s : ℝ ↦ ∑' w : ↥{w : D | w ≠ 0}, gaussianWeight (1 / s) (w : E)) (Set.Ici a) := by
    refine continuousOn_tsum (u := fun w : ↥{w : D | w ≠ 0} ↦ gaussianWeight (1 / a) (w : E))
      (fun w ↦ ?_) (summable_dual_nonzero L ha) (fun w s hs ↦ ?_)
    · have hc : Continuous (fun s : ℝ ↦ gaussianWeight (1 / s) (w : E)) := by
        simp_rw [gaussianWeight_one_div]
        fun_prop
      exact hc.continuousOn
    · rw [Real.norm_of_nonneg (gaussianWeight_pos _ _).le]
      exact gaussianWeight_le_of_le (one_div_pos.mpr (ha.trans_le hs))
        (one_div_le_one_div_of_le ha hs) (w : E)
  have hnhds : Set.Ici a ∈ 𝓝 s₀ := Filter.mem_of_superset (Ioi_mem_nhds (half_lt_self hs₀))
    Set.Ioi_subset_Ici_self
  have hca : ContinuousAt
      (fun s : ℝ ↦ ∑' w : ↥{w : D | w ≠ 0}, gaussianWeight (1 / s) (w : E)) s₀ :=
    hcont_tsum.continuousAt hnhds
  refine hca.congr ?_
  filter_upwards [hnhds] with s hs
  exact (gaussianMass_zero_sub_one_eq_tsum D (1 / s) (one_div_pos.mpr (ha.trans_le hs))).symm

private theorem tendsto_dualMass_atTop :
    Tendsto
      (fun s : ℝ ↦ gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1)
      atTop (𝓝 0) := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  have hsum : Summable (fun w : ↥{w : D | w ≠ 0} ↦ gaussianWeight 1 (w : E)) := by
    simpa only [one_div_one] using summable_dual_nonzero L one_pos
  have hlim : Tendsto
      (fun s : ℝ ↦ ∑' w : ↥{w : D | w ≠ 0}, gaussianWeight (1 / s) (w : E))
      atTop (𝓝 (∑' _ : ↥{w : D | w ≠ 0}, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun w ↦ ?_) ?_
    · simp_rw [gaussianWeight_one_div]
      have hnorm : 0 < ‖(w : E)‖ := norm_pos_iff.mpr fun h0 ↦ w.property (Subtype.ext h0)
      have hc : -Real.pi * ‖(w : E)‖ ^ 2 < 0 :=
        mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) (sq_pos_of_pos hnorm)
      have hexp : Tendsto (fun s : ℝ ↦ -Real.pi * ‖(w : E)‖ ^ 2 * s ^ 2) atTop atBot :=
        (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg hc
      exact Real.tendsto_exp_atBot.comp hexp
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs w
      rw [Real.norm_of_nonneg (gaussianWeight_pos _ _).le]
      have hle : 1 / s ≤ 1 := by
        simpa only [one_div_one] using one_div_le_one_div_of_le one_pos hs
      exact gaussianWeight_le_of_le (one_div_pos.mpr (zero_lt_one.trans_le hs)) hle (w : E)
  rw [tsum_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  exact (gaussianMass_zero_sub_one_eq_tsum D (1 / s) (one_div_pos.mpr hs)).symm

private theorem nonempty_smoothingSet {ε : ℝ} (hε : 0 < ε) :
    {s : ℝ | 0 < s ∧
      gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ≤
        ε}.Nonempty := by
  have hev := (tendsto_dualMass_atTop L).eventually (gt_mem_nhds hε)
  obtain ⟨s, hs, hle⟩ := ((eventually_gt_atTop (0 : ℝ)).and hev).exists
  exact ⟨s, hs, hle.le⟩

private theorem exists_pos_lt_dualMass [Nontrivial E] (ε : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s ≤ δ →
      ε < gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 := by
  classical
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  obtain ⟨w₀, hw₀⟩ := exists_dual_ne_zero L
  have hnorm₀ : 0 < ‖(w₀ : E)‖ := norm_pos_iff.mpr fun h0 ↦ hw₀ (Subtype.ext h0)
  let N : ℕ := Nat.floor (2 * ε) + 1
  have hN_gt : 2 * ε < (N : ℝ) := by
    simpa only [N, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (2 * ε)
  let M : ℝ := Real.sqrt (2 * Real.pi) * (N : ℝ) * ‖(w₀ : E)‖ + 1
  have hM : 0 < M := by positivity
  let δ : ℝ := 1 / M
  refine ⟨δ, one_div_pos.mpr hM, fun s hs hsδ ↦ ?_⟩
  rw [gaussianMass_zero_sub_one_eq_tsum D (1 / s) (one_div_pos.mpr hs)]
  let emb : Fin N → ↥{w : D | w ≠ 0} := fun k ↦
    ⟨(k.1 + 1) • w₀, by
      intro h0
      have h0' : ((k.1 + 1 : ℕ) : ℝ) • (w₀ : E) = 0 := by
        have hcoe : (((k.1 + 1) • w₀ : D) : E) = (k.1 + 1) • (w₀ : E) :=
          AddSubmonoidClass.coe_nsmul w₀ (k.1 + 1)
        rw [Nat.cast_smul_eq_nsmul ℝ, ← hcoe, h0, Submodule.coe_zero]
      rcases smul_eq_zero.mp h0' with hc | hw
      · exact (Nat.cast_pos.mpr (Nat.succ_pos k.1)).ne' hc
      · exact hw₀ (Subtype.ext hw)⟩
  have hemb_inj : Function.Injective emb := by
    intro k₁ k₂ hk
    have hval := congrArg (fun u : ↥{w : D | w ≠ 0} ↦ (u.val : E)) hk
    have hval' : ((k₁.1 + 1 : ℕ) : ℝ) • (w₀ : E) = ((k₂.1 + 1 : ℕ) : ℝ) • (w₀ : E) := by
      have h1 : (((k₁.1 + 1) • w₀ : D) : E) = ((k₁.1 + 1 : ℕ) : ℝ) • (w₀ : E) := by
        rw [AddSubmonoidClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℝ]
      have h2 : (((k₂.1 + 1) • w₀ : D) : E) = ((k₂.1 + 1 : ℕ) : ℝ) • (w₀ : E) := by
        rw [AddSubmonoidClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℝ]
      simpa only [emb, h1, h2] using hval
    have heq : ((k₁.1 + 1 : ℕ) : ℝ) = ((k₂.1 + 1 : ℕ) : ℝ) :=
      smul_left_injective ℝ (fun h0 ↦ hw₀ (Subtype.ext h0)) hval'
    have hnat : k₁.1 + 1 = k₂.1 + 1 := by exact_mod_cast heq
    exact Fin.ext (Nat.succ.inj hnat)
  have hterm : ∀ k : Fin N, (1 / 2 : ℝ) ≤ gaussianWeight (1 / s) ((emb k).val : E) := by
    intro k
    rw [gaussianWeight_one_div]
    have hkn : ((k.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast k.isLt
    have hnormk : ‖((emb k).val : E)‖ = ((k.1 + 1 : ℕ) : ℝ) * ‖(w₀ : E)‖ := by
      change ‖(((k.1 + 1) • w₀ : D) : E)‖ = _
      rw [AddSubmonoidClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul,
        Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have hsM : s * (Real.sqrt (2 * Real.pi) * (N : ℝ) * ‖(w₀ : E)‖) ≤ 1 := by
      have h1 : s * M ≤ 1 := by
        calc
          s * M ≤ δ * M := mul_le_mul_of_nonneg_right hsδ hM.le
          _ = 1 := one_div_mul_cancel hM.ne'
      nlinarith
    have hsq : Real.pi * ‖((emb k).val : E)‖ ^ 2 * s ^ 2 ≤ 1 / 2 := by
      have hle1 : (s * (Real.sqrt (2 * Real.pi) * (N : ℝ) * ‖(w₀ : E)‖)) ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg hs.le
          (show 0 ≤ Real.sqrt (2 * Real.pi) * (N : ℝ) * ‖(w₀ : E)‖ by positivity)]
      have hsq2 : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi :=
        Real.sq_sqrt (by positivity)
      have hle2 : 2 * Real.pi * ((N : ℝ) * ‖(w₀ : E)‖) ^ 2 * s ^ 2 ≤ 1 := by
        have heq : (s * (Real.sqrt (2 * Real.pi) * (N : ℝ) * ‖(w₀ : E)‖)) ^ 2 =
            2 * Real.pi * ((N : ℝ) * ‖(w₀ : E)‖) ^ 2 * s ^ 2 := by
          calc
            (s * (Real.sqrt (2 * Real.pi) * (N : ℝ) * ‖(w₀ : E)‖)) ^ 2
                = s ^ 2 * ((Real.sqrt (2 * Real.pi)) ^ 2 * ((N : ℝ) * ‖(w₀ : E)‖) ^ 2) := by ring
            _ = 2 * Real.pi * ((N : ℝ) * ‖(w₀ : E)‖) ^ 2 * s ^ 2 := by rw [hsq2]; ring
        linarith
      have hkn2 : ‖((emb k).val : E)‖ ^ 2 ≤ ((N : ℝ) * ‖(w₀ : E)‖) ^ 2 := by
        rw [hnormk]
        exact pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_right hkn hnorm₀.le) 2
      have h3 : Real.pi * ‖((emb k).val : E)‖ ^ 2 * s ^ 2 ≤
          Real.pi * ((N : ℝ) * ‖(w₀ : E)‖) ^ 2 * s ^ 2 := by
        gcongr
      linarith
    have hexp := Real.add_one_le_exp (-Real.pi * ‖((emb k).val : E)‖ ^ 2 * s ^ 2)
    linarith
  have hfin_le : ∑ u ∈ Finset.univ.image emb, gaussianWeight (1 / s) (u.val : E) ≤
      ∑' w : ↥{w : D | w ≠ 0}, gaussianWeight (1 / s) (w.val : E) :=
    (summable_dual_nonzero L hs).sum_le_tsum (Finset.univ.image emb)
      fun w _ ↦ (gaussianWeight_pos _ _).le
  rw [Finset.sum_image (fun a _ b _ h ↦ hemb_inj h)] at hfin_le
  have hsum_half : (N : ℝ) / 2 ≤ ∑ k : Fin N, gaussianWeight (1 / s) ((emb k).val : E) := by
    calc
      (N : ℝ) / 2 = ∑ _k : Fin N, (1 / 2 : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ ∑ k : Fin N, gaussianWeight (1 / s) ((emb k).val : E) :=
        Finset.sum_le_sum fun k _ ↦ hterm k
  linarith

/-- For a full-rank discrete lattice in positive dimension, the smoothing parameter is strictly
positive at every positive error `ε > 0`. -/
theorem smoothingParameter_pos [Nontrivial E] {ε : ℝ} (hε : 0 < ε) :
    0 < smoothingParameter L ε := by
  obtain ⟨δ, hδ, hgt⟩ := exists_pos_lt_dualMass L ε
  have hle : δ ≤ smoothingParameter L ε := by
    refine le_csInf (nonempty_smoothingSet L hε) ?_
    rintro s ⟨hs, hmass⟩
    by_contra hlt
    exact (hgt s hs (le_of_not_ge hlt)).not_ge hmass
  exact hδ.trans_le hle

/-- In positive dimension, the smoothing parameter attains the defining inequality of
[MicciancioRegev2007], Definition 3.1 with exact equality: `ρ_{1 / η_ε(L)}(L* \ {0}) = ε`. -/
theorem gaussianMass_dual_smoothingParameter [Nontrivial E] {ε : ℝ} (hε : 0 < ε) :
    gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L)
      (1 / smoothingParameter L ε) 0 - 1 = ε := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  let S := {s : ℝ | 0 < s ∧ gaussianMass D (1 / s) 0 - 1 ≤ ε}
  let s₀ := smoothingParameter L ε
  have hs₀ : 0 < s₀ := smoothingParameter_pos L hε
  have hne : S.Nonempty := nonempty_smoothingSet L hε
  have hcont := continuousAt_dualMass L hs₀
  apply le_antisymm
  · by_contra hgt
    push Not at hgt
    obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.mp hcont (gaussianMass D (1 / s₀) 0 - 1 - ε)
      (sub_pos.mpr hgt)
    obtain ⟨s, hsS, hslt⟩ := Real.lt_sInf_add_pos hne hr
    change s < s₀ + r at hslt
    have hle : s₀ ≤ s := csInf_le ⟨0, fun _ h ↦ h.1.le⟩ hsS
    have hdist : dist s s₀ < r := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle)]
      linarith
    have hfd := hball hdist
    rw [Real.dist_eq] at hfd
    have h1 := (abs_lt.mp hfd).1
    linarith [hsS.2]
  · by_contra hlt
    push Not at hlt
    obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.mp hcont (ε - (gaussianMass D (1 / s₀) 0 - 1))
      (sub_pos.mpr hlt)
    let δ := min r s₀ / 2
    have hδ : 0 < δ := half_pos (lt_min hr hs₀)
    have hδr : δ < r := by
      calc
        δ < min r s₀ := half_lt_self (lt_min hr hs₀)
        _ ≤ r := min_le_left _ _
    have hδs : δ < s₀ := by
      calc
        δ < min r s₀ := half_lt_self (lt_min hr hs₀)
        _ ≤ s₀ := min_le_right _ _
    let s' := s₀ - δ
    have hs'_pos : 0 < s' := sub_pos.mpr hδs
    have hdist : dist s' s₀ < r := by
      rw [Real.dist_eq, show s' - s₀ = -δ by ring, abs_neg, abs_of_pos hδ]
      exact hδr
    have hfd := hball hdist
    rw [Real.dist_eq] at hfd
    have h2 := (abs_lt.mp hfd).2
    have hs'S : s' ∈ S := ⟨hs'_pos, by linarith⟩
    have hle : s₀ ≤ s' := csInf_le ⟨0, fun _ h ↦ h.1.le⟩ hs'S
    linarith

/-- Exact upper-bound characterization of `η_ε(L)` in terms of the nonzero dual Gaussian mass,
valid in all dimensions (including dimension zero) for all `s > 0` and `ε > 0`. -/
theorem smoothingParameter_le_iff {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    smoothingParameter L ε ≤ s ↔
      gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ≤ ε := by
  refine ⟨fun hle ↦ ?_, smoothingParameter_le_of_dual_mass_le L hs⟩
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · rw [dualMass_eq_zero_of_subsingleton L s]
    exact hε.le
  · have hpos := smoothingParameter_pos L hε
    have hat := gaussianMass_dual_smoothingParameter L hε
    exact (dualMass_antitone L hpos hle).trans hat.le

/-- Exact lower-bound characterization of `η_ε(L)` in terms of the nonzero dual Gaussian mass,
valid in all dimensions (including dimension zero) for all `s > 0` and `ε > 0`. -/
theorem le_smoothingParameter_iff {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    s ≤ smoothingParameter L ε ↔
      ε ≤ gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 := by
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · rw [smoothingParameter_eq_zero_of_subsingleton L ε, dualMass_eq_zero_of_subsingleton L s]
    exact ⟨fun h ↦ absurd h (not_le_of_gt hs), fun h ↦ absurd h (not_le_of_gt hε)⟩
  · have hpos := smoothingParameter_pos L hε
    have hat := gaussianMass_dual_smoothingParameter L hε
    constructor
    · intro hle
      exact hat.symm.le.trans (dualMass_antitone L hs hle)
    · intro hge
      by_contra hlt
      have hstrict := dualMass_strictAnti L hpos (lt_of_not_ge hlt)
      linarith

/-- The smoothing parameter is antitone in the error parameter `ε > 0` (in all dimensions). -/
theorem smoothingParameter_anti {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (h : ε₁ ≤ ε₂) :
    smoothingParameter L ε₂ ≤ smoothingParameter L ε₁ :=
  csInf_le_csInf ⟨0, fun _ hx ↦ hx.1.le⟩ (nonempty_smoothingSet L hε₁)
    fun _ hs ↦ ⟨hs.1, hs.2.trans h⟩

/-- In positive dimension, the smoothing parameter is strictly decreasing in `ε > 0`
([MicciancioRegev2007], §3, p. 10 of the author's copy). -/
theorem smoothingParameter_strictAnti [Nontrivial E] {ε₁ ε₂ : ℝ}
    (hε₁ : 0 < ε₁) (h : ε₁ < ε₂) :
    smoothingParameter L ε₂ < smoothingParameter L ε₁ := by
  have hε₂ : 0 < ε₂ := hε₁.trans h
  have hpos₁ : 0 < smoothingParameter L ε₁ := smoothingParameter_pos L hε₁
  by_contra hge
  have hle : smoothingParameter L ε₁ ≤ smoothingParameter L ε₂ := le_of_not_gt hge
  have hm := dualMass_antitone L hpos₁ hle
  rw [gaussianMass_dual_smoothingParameter L hε₁, gaussianMass_dual_smoothingParameter L hε₂] at hm
  linarith

private theorem two_pow_mul_exp_le_half_pow_div (n : ℕ) (hn : 0 < n) :
    (2 : ℝ) ^ n * Real.exp (-3 * Real.pi * n / 4) ≤
      (1 / 2 : ℝ) ^ n / (1 + (1 / 2 : ℝ) ^ n) := by
  have hexp8 : (8 : ℝ) < Real.exp (3 * Real.pi / 4) := by
    have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have heq : (5 / 4 : ℝ) ≤ Real.exp (1 / 4) := by
      linarith [Real.add_one_le_exp (1 / 4 : ℝ)]
    have hpi : (9 / 4 : ℝ) < 3 * Real.pi / 4 := by linarith [Real.pi_gt_three]
    calc
      (8 : ℝ) < 2.7 ^ 2 * (5 / 4) := by norm_num
      _ < Real.exp 1 ^ 2 * Real.exp (1 / 4) := by nlinarith [Real.exp_pos (1 / 4)]
      _ = Real.exp (9 / 4) := by
        rw [sq, ← Real.exp_add, ← Real.exp_add]
        norm_num
      _ < Real.exp (3 * Real.pi / 4) := Real.exp_lt_exp.mpr hpi
  have hstep : (2 : ℝ) * Real.exp (-3 * Real.pi / 4) ≤ 1 / 4 := by
    have hinv : Real.exp (-3 * Real.pi / 4) < 1 / 8 := by
      rw [show -3 * Real.pi / 4 = -(3 * Real.pi / 4) by ring, Real.exp_neg, inv_eq_one_div]
      exact one_div_lt_one_div_of_lt (by norm_num) hexp8
    linarith
  have hpow : (2 : ℝ) ^ n * Real.exp (-3 * Real.pi * n / 4) ≤ (1 / 4 : ℝ) ^ n := by
    have hp := pow_le_pow_left₀ (by positivity) hstep n
    rw [mul_pow, ← Real.exp_nat_mul] at hp
    convert hp using 1
    congr 2
    ring
  have h2pow : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h4ge : (2 : ℝ) ^ n + 1 ≤ (4 : ℝ) ^ n := by
    have h4 : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
      rw [← mul_pow]
      norm_num
    nlinarith
  have hrhs : (1 / 2 : ℝ) ^ n / (1 + (1 / 2 : ℝ) ^ n) = 1 / ((2 : ℝ) ^ n + 1) := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    rw [one_div_pow]
    field_simp
  have hq : (1 / 4 : ℝ) ^ n ≤ 1 / ((2 : ℝ) ^ n + 1) := by
    rw [one_div_pow]
    exact one_div_le_one_div_of_le (by positivity) h4ge
  linarith

/-- Micciancio–Regev ([MicciancioRegev2007], Lemma 3.2, pp. 10–11 of the author's copy):
for every full-rank discrete lattice `L` in a finite-dimensional real inner product space of
dimension `n`, `η_{2^{-n}}(L) ≤ √n / λ₁(L*)`. In dimension zero both sides vanish (`0 ≤ 0 / 0`). -/
theorem smoothingParameter_le_sqrt_div_minimum_dual :
    smoothingParameter L ((1 / 2 : ℝ) ^ finrank ℝ E) ≤
      Real.sqrt (finrank ℝ E) /
        minimum (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) := by
  by_cases hn : finrank ℝ E = 0
  · have : Subsingleton E := Module.finrank_zero_iff.mp hn
    rw [smoothingParameter_eq_zero_of_subsingleton L _, hn, Nat.cast_zero,
      Real.sqrt_zero, zero_div]
  · have hnpos : 0 < finrank ℝ E := Nat.pos_of_ne_zero hn
    have : Nontrivial E := Module.nontrivial_of_finrank_pos hnpos
    let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
    have : DiscreteTopology D := discreteTopology_dualSubmodule L
    have hDne : D ≠ ⊥ := by
      obtain ⟨w, hw⟩ := exists_dual_ne_zero L
      intro hbot
      apply hw
      apply Subtype.ext
      have hmem : (w : E) ∈ (⊥ : Submodule ℤ E) := hbot ▸ w.property
      exact (Submodule.mem_bot ℤ).mp hmem
    have ha : 0 < minimum D := minimum_pos hDne
    let s := Real.sqrt (finrank ℝ E) / minimum D
    have hs : 0 < s := div_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hnpos)) ha
    have hgap : ∀ w : D, w ≠ 0 → minimum D ≤ ‖(w : E)‖ := fun w hw ↦
      minimum_le_norm w.property (fun h0 ↦ hw (Subtype.ext h0))
    let _ : MeasurableSpace E := borel E
    have : BorelSpace E := ⟨rfl⟩
    have hsq : s ^ 2 * minimum D ^ 2 = (finrank ℝ E : ℝ) := by
      dsimp only [s]
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), div_mul_cancel₀ _ (sq_pos_of_pos ha).ne']
    have hwidth : 2 ^ finrank ℝ E * Real.exp (-3 * Real.pi * s ^ 2 * minimum D ^ 2 / 4) ≤
        (1 / 2 : ℝ) ^ finrank ℝ E / (1 + (1 / 2 : ℝ) ^ finrank ℝ E) := by
      rw [mul_assoc (-3 * Real.pi), hsq]
      exact two_pow_mul_exp_le_half_pow_div (finrank ℝ E) hnpos
    have hdual := gaussianMass_dual_sub_one_le_of_gap L s hs (minimum D) ha hgap
      ((1 / 2 : ℝ) ^ finrank ℝ E) (by positivity) hwidth
    exact smoothingParameter_le_of_dual_mass_le L hs hdual

end FullRank

end ZLattice
