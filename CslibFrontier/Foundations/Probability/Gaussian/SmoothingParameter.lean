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
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  obtain ⟨w₀, hw₀⟩ := exists_dual_ne_zero L
  have hnorm₀ : 0 < ‖(w₀ : E)‖ := norm_pos_iff.mpr fun h0 ↦ hw₀ (Subtype.ext h0)
  -- The multiples `k • w₀`, `k < N`, each have weight at least `1 / 2` at width `1 / δ`.
  let N : ℕ := ⌊2 * ε⌋₊ + 3
  have hN : 2 * ε + 2 < N := by
    have := Nat.lt_floor_add_one (2 * ε)
    push_cast [N]
    linarith
  let δ := 1 / (3 * N * ‖(w₀ : E)‖)
  have hδ : 0 < δ := by positivity
  have hδN : δ * (3 * N * ‖(w₀ : E)‖) = 1 := one_div_mul_cancel (by positivity)
  refine ⟨δ, hδ, fun s hs hsδ ↦ lt_of_lt_of_le ?_ (dualMass_antitone L hs hsδ)⟩
  have hnorm (k : ℕ) : ‖((k • w₀ : D) : E)‖ = k * ‖(w₀ : E)‖ := by
    rw [AddSubmonoidClass.coe_nsmul, RCLike.norm_nsmul ℝ, nsmul_eq_mul]
  have hinj : Function.Injective fun k : Fin N ↦ (k : ℕ) • w₀ := fun a b h ↦ by
    have := congrArg (fun z : D ↦ ‖(z : E)‖) h
    simp only [hnorm] at this
    exact Fin.ext (by exact_mod_cast mul_right_cancel₀ hnorm₀.ne' this)
  have hterm (k : Fin N) : 1 / 2 ≤ gaussianWeight (1 / δ) ((((k : ℕ) • w₀ : D) : E) - 0) := by
    rw [sub_zero, gaussianWeight_one_div, hnorm]
    have hk : (k : ℝ) * ‖(w₀ : E)‖ * δ ≤ 1 / 3 := by
      have : (k : ℝ) ≤ N := by exact_mod_cast k.isLt.le
      nlinarith [mul_le_mul_of_nonneg_right this (by positivity : 0 ≤ ‖(w₀ : E)‖ * δ)]
    nlinarith [Real.add_one_le_exp (-Real.pi * ((k : ℝ) * ‖(w₀ : E)‖) ^ 2 * δ ^ 2),
      Real.pi_lt_four, pow_le_pow_left₀ (by positivity) hk 2, Real.pi_pos]
  have := Summable.tsum_le_tsum_of_inj (f := fun _ : Fin N ↦ (1 / 2 : ℝ))
    (g := fun z : D ↦ gaussianWeight (1 / δ) ((z : E) - 0)) _ hinj
    (fun _ _ ↦ (gaussianWeight_pos _ _).le) hterm Summable.of_finite
    (summable_gaussianWeight D _ (by positivity) 0)
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at this
  unfold gaussianMass
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
  have hlim := (continuousAt_dualMass L hs₀).tendsto
  apply le_antisymm
  · refine le_of_tendsto (hlim.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s (hs : s ∈ Set.Ioi s₀) ↦ ?_)
    obtain ⟨s', hs'S, hs's⟩ := exists_lt_of_csInf_lt hne (show sInf S < s from hs)
    exact (dualMass_antitone L hs'S.1 hs's.le).trans hs'S.2
  · refine ge_of_tendsto (hlim.mono_left nhdsWithin_le_nhds)
      (Filter.eventually_of_mem (Ioo_mem_nhdsLT hs₀) fun s hs ↦ ?_)
    by_contra! h
    exact (csInf_le (⟨0, fun _ h ↦ h.1.le⟩ : BddBelow S) ⟨hs.1, h.le⟩).not_gt hs.2

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
  have hstep : (2 : ℝ) * Real.exp (-3 * Real.pi / 4) ≤ 1 / 4 := by
    have h8 : 8 < Real.exp (3 * Real.pi / 4) := by
      rw [← Real.log_lt_iff_lt_exp (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num,
        Real.log_pow]
      push_cast
      linarith [Real.log_two_lt_d9, Real.pi_gt_three]
    rw [show -3 * Real.pi / 4 = -(3 * Real.pi / 4) by ring, Real.exp_neg,
      mul_inv_le_iff₀ (Real.exp_pos _)]
    linarith
  have hpow : (2 : ℝ) ^ n * Real.exp (-3 * Real.pi * n / 4) ≤ (1 / 4 : ℝ) ^ n := by
    have hp := pow_le_pow_left₀ (by positivity) hstep n
    rw [mul_pow, ← Real.exp_natCast_mul] at hp
    convert hp using 3
    ring
  have hx : (1 / 2 : ℝ) ^ n ≤ 1 / 2 := pow_le_of_le_one (by norm_num) (by norm_num) hn.ne'
  have h4 : (1 / 4 : ℝ) ^ n = (1 / 2) ^ n * (1 / 2) ^ n := by rw [← mul_pow]; norm_num
  rw [le_div_iff₀ (by positivity)]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]

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
