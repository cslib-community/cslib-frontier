/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Probability/Distributions/Gaussian/`
-- `Plackett.lean`)

public import CslibFrontier.Foundations.Probability.Gaussian.Quadrant
public import Mathlib.Analysis.InnerProductSpace.PiL2
import CslibFrontier.Foundations.Probability.Gaussian.Borell
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.Gaussian.Real

/-!
# Plackett monotonicity and threshold crossing identities for correlated Gaussians

For `ρ ∈ [0, 1]`, increasing the correlation increases every lower-quadrant probability
`P_ρ[z ≤ a ∧ z' ≤ b]` (`measureReal_correlatedGaussian_le_and_le_mono`) and decreases every
asymmetric threshold-crossing probability `P_ρ[a < z ∧ z' ≤ b]`
(`measureReal_correlatedGaussian_gt_and_le_anti`).

Rather than differentiating bivariate Gaussian integrals with respect to `ρ`, we couple both pairs
in `EuclideanSpace ℝ (Fin 1 ⊕ Fin 2)` with shared first coordinate `√ρ₁ ω₀`. Conditioned on `ω₀`,
the `ρ₁`-pair becomes independent (`gaussianQuadrant 0 α β = α β`), while the `ρ₂`-pair has
residual correlation `r = (ρ₂ - ρ₁) / (1 - ρ₁) ∈ [0, 1]`, which dominates `α β` slice by slice via
`mul_le_gaussianQuadrant`.

We also record the decomposition `P_ρ[a < z ∧ z' ≤ b] = Φ b - P_ρ[z ≤ a ∧ z' ≤ b]`, the negation
symmetry `P_ρ[-d < z ∧ z' ≤ -d] = P_ρ[d < z ∧ z' ≤ d]`, and the box-excess inequality
`2 P_ρ[d < z ∧ z' ≤ d] ≤ P_ρ[d < z ∧ z' ≤ -d] + P_ρ[-d < z ∧ z' ≤ d]` for `0 ≤ d`.

## Main results

* `ProbabilityTheory.measureReal_pi_inner_prod_eq_correlatedGaussian`: joint law of two unit
  projections under `Measure.pi (gaussianReal 0 1)`.
* `ProbabilityTheory.measureReal_correlatedGaussian_le_and_le_mono`: Plackett quadrant monotonicity
  on `[0, 1]`.
* `ProbabilityTheory.measureReal_correlatedGaussian_gt_and_le`,
  `ProbabilityTheory.measureReal_correlatedGaussian_gt_and_le_anti`: crossing decomposition and
  antitonicity in correlation.
* `ProbabilityTheory.measureReal_correlatedGaussian_gt_neg_le_neg`,
  `ProbabilityTheory.two_mul_correlatedGaussian_gt_le_diag_le`: diagonal symmetry and box-excess
  inequality for shifted thresholds.
-/

public section

open Set Filter MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace NNReal ENNReal

namespace ProbabilityTheory

local notation "Φ" => cdf (gaussianReal 0 1)

/-- Under `Measure.pi (gaussianReal 0 1)`, the joint law of two unit inner-product projections is
`correlatedGaussian ⟪u, v⟫`. -/
theorem measureReal_pi_inner_prod_eq_correlatedGaussian {ι : Type*} [Fintype ι]
    {u v : EuclideanSpace ℝ ι} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
        {ω | (⟪u, WithLp.toLp 2 ω⟫, ⟪v, WithLp.toLp 2 ω⟫) ∈ S} =
      (correlatedGaussian ⟪u, v⟫).real S := by
  have hmp : Measurable fun x : EuclideanSpace ℝ ι => (⟪u, x⟫, ⟪v, x⟫) := by fun_prop
  change (Measure.pi fun _ : ι => gaussianReal 0 1).real
    {ω | WithLp.toLp 2 ω ∈ (fun x => (⟪u, x⟫, ⟪v, x⟫)) ⁻¹' S} = _
  rw [measureReal_pi_gaussianReal_eq (hmp hS),
    ← stdGaussian_map_inner_prod_eq_correlatedGaussian hu hv,
    map_measureReal_apply hmp hS]

/-- **Plackett quadrant monotonicity on `[0, 1]`.** Increasing the correlation `0 ≤ ρ₁ ≤ ρ₂ ≤ 1`
increases the lower-quadrant probability `P_ρ[z ≤ a ∧ z' ≤ b]` for all `a, b ∈ ℝ`. -/
theorem measureReal_correlatedGaussian_le_and_le_mono {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 ≤ ρ₁) (h12 : ρ₁ ≤ ρ₂) (hρ₂ : ρ₂ ≤ 1) (a b : ℝ) :
    (correlatedGaussian ρ₁).real {p | p.1 ≤ a ∧ p.2 ≤ b} ≤
      (correlatedGaussian ρ₂).real {p | p.1 ≤ a ∧ p.2 ≤ b} := by
  rcases eq_or_lt_of_le (h12.trans hρ₂) with rfl | hρ₁_lt
  · obtain rfl : 1 = ρ₂ := le_antisymm h12 hρ₂
    exact le_rfl
  set ac := √ρ₁
  set s := √(1 - ρ₁)
  have hs_pos : 0 < s := sqrt_pos.mpr (by linarith)
  have hac_sq : ac ^ 2 = ρ₁ := sq_sqrt hρ₁
  have hs_sq : s ^ 2 = 1 - ρ₁ := sq_sqrt (by linarith)
  set r := (ρ₂ - ρ₁) / (1 - ρ₁)
  have hr0 : 0 ≤ r := div_nonneg (by linarith) (by linarith)
  have hr1 : r ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hr_sq : √(1 - r ^ 2) ^ 2 = 1 - r ^ 2 := sq_sqrt (by nlinarith)
  let u : EuclideanSpace ℝ (Fin 1 ⊕ Fin 2) :=
    WithLp.toLp 2 (Sum.elim (fun _ => ac) ![s, 0])
  let v : ℝ → EuclideanSpace ℝ (Fin 1 ⊕ Fin 2) := fun t =>
    WithLp.toLp 2 (Sum.elim (fun _ => ac) ![s * t, s * √(1 - t ^ 2)])
  have hu_norm : ‖u‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_two]
    simp only [u, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, sq_abs]
    have : ac ^ 2 + (s ^ 2 + 0 ^ 2) = 1 := by linarith [hac_sq, hs_sq]
    rw [this, sqrt_one]
  have hv_norm (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ‖v t‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_two]
    simp only [v, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, sq_abs]
    have ht_sq : √(1 - t ^ 2) ^ 2 = 1 - t ^ 2 := sq_sqrt (by nlinarith)
    have : ac ^ 2 + ((s * t) ^ 2 + (s * √(1 - t ^ 2)) ^ 2) = 1 := by
      calc ac ^ 2 + ((s * t) ^ 2 + (s * √(1 - t ^ 2)) ^ 2)
          = ac ^ 2 + s ^ 2 * (t ^ 2 + √(1 - t ^ 2) ^ 2) := by ring
        _ = ac ^ 2 + s ^ 2 * 1 := by rw [ht_sq]; ring
        _ = 1 := by linarith [hac_sq, hs_sq]
    rw [this, sqrt_one]
  have huv_inner (t : ℝ) : ⟪u, v t⟫ = ρ₁ + (1 - ρ₁) * t := by
    rw [PiLp.inner_apply, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_two]
    simp only [u, v, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      RCLike.inner_apply, conj_trivial]
    linear_combination hac_sq + t * hs_sq
  have huv0 : ⟪u, v 0⟫ = ρ₁ := by rw [huv_inner]; ring
  have huvr : ⟪u, v r⟫ = ρ₂ := by
    rw [huv_inner, show (1 - ρ₁) * r = ρ₂ - ρ₁ from mul_div_cancel₀ _ (by linarith)]
    ring
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≤ a ∧ p.2 ≤ b} :=
    (measurableSet_Iic.preimage measurable_fst).inter (measurableSet_Iic.preimage measurable_snd)
  rw [← huv0, ← huvr, ← measureReal_pi_inner_prod_eq_correlatedGaussian hu_norm
      (hv_norm 0 le_rfl zero_le_one) hS,
    ← measureReal_pi_inner_prod_eq_correlatedGaussian hu_norm (hv_norm r hr0 hr1) hS]
  set γ₁ := Measure.pi fun _ : Fin 1 => gaussianReal 0 1
  set γ₂ := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
  have hγ₂_map : γ₂.map (fun q : Fin 2 → ℝ => (q 0, q 1)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
    have hind : IndepFun (fun q : Fin 2 → ℝ => q 0) (fun q : Fin 2 → ℝ => q 1) γ₂ :=
      (iIndepFun_pi fun _ : Fin 2 => measurable_id.aemeasurable).indepFun (by decide)
    rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable
        (measurable_pi_apply 1).aemeasurable).mp hind,
      (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) 0).map_eq,
      (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) 1).map_eq]
  have hslice (t : ℝ) (q₁ : Fin 1 → ℝ) :
      γ₂ {q₂ | (⟪u, WithLp.toLp 2 (Sum.elim q₁ q₂)⟫,
          ⟪v t, WithLp.toLp 2 (Sum.elim q₁ q₂)⟫) ∈ {p : ℝ × ℝ | p.1 ≤ a ∧ p.2 ≤ b}} =
        ENNReal.ofReal (gaussianQuadrant t (Φ ((a - ac * q₁ 0) / s))
          (Φ ((b - ac * q₁ 0) / s))) := by
    set A := (a - ac * q₁ 0) / s
    set B := (b - ac * q₁ 0) / s
    have hset : {q₂ : Fin 2 → ℝ | (⟪u, WithLp.toLp 2 (Sum.elim q₁ q₂)⟫,
          ⟪v t, WithLp.toLp 2 (Sum.elim q₁ q₂)⟫) ∈ {p : ℝ × ℝ | p.1 ≤ a ∧ p.2 ≤ b}} =
        (fun q : Fin 2 → ℝ => (q 0, q 1)) ⁻¹'
          ((fun g : ℝ × ℝ => (g.1, t * g.1 + √(1 - t ^ 2) * g.2)) ⁻¹'
            {p : ℝ × ℝ | p.1 ≤ A ∧ p.2 ≤ B}) := by
      ext q₂
      simp only [mem_ofPred_eq, mem_preimage, PiLp.inner_apply, Fintype.sum_sum_type,
        Fin.sum_univ_one, Fin.sum_univ_two, u, v, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, RCLike.inner_apply, conj_trivial, A, B,
        le_div_iff₀ hs_pos]
      constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨by linarith, by linarith⟩
    have hAB : MeasurableSet {p : ℝ × ℝ | p.1 ≤ A ∧ p.2 ≤ B} :=
      (measurableSet_Iic.preimage measurable_fst).inter (measurableSet_Iic.preimage measurable_snd)
    rw [hset, ← Measure.map_apply ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
        (hAB.preimage (by fun_prop)),
      hγ₂_map, ← Measure.map_apply (by fun_prop) hAB, ← correlatedGaussian_def,
      gaussianQuadrant_cdf_cdf, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hSE : Measurable fun q : (Fin 1 → ℝ) × (Fin 2 → ℝ) => Sum.elim q.1 q.2 :=
    (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin 1 ⊕ Fin 2 => ℝ).symm.measurable
  have hmeas_ev (t : ℝ) : MeasurableSet {ω : Fin 1 ⊕ Fin 2 → ℝ |
      (⟪u, WithLp.toLp 2 ω⟫, ⟪v t, WithLp.toLp 2 ω⟫) ∈ {p : ℝ × ℝ | p.1 ≤ a ∧ p.2 ≤ b}} :=
    hS.preimage ((by fun_prop : Measurable fun ω => ⟪u, WithLp.toLp 2 ω⟫).prodMk
      (by fun_prop : Measurable fun ω => ⟪v t, WithLp.toLp 2 ω⟫))
  rw [measureReal_def, measureReal_def]
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  rw [pi_gaussianReal_sum,
    Measure.map_apply hSE (hmeas_ev 0),
    Measure.map_apply hSE (hmeas_ev r),
    Measure.prod_apply ((hmeas_ev 0).preimage hSE),
    Measure.prod_apply ((hmeas_ev r).preimage hSE)]
  refine lintegral_mono fun q₁ => ?_
  change γ₂ {q₂ | (⟪u, WithLp.toLp 2 (Sum.elim q₁ q₂)⟫,
      ⟪v 0, WithLp.toLp 2 (Sum.elim q₁ q₂)⟫) ∈ {p | p.1 ≤ a ∧ p.2 ≤ b}} ≤
    γ₂ {q₂ | (⟪u, WithLp.toLp 2 (Sum.elim q₁ q₂)⟫,
      ⟪v r, WithLp.toLp 2 (Sum.elim q₁ q₂)⟫) ∈ {p | p.1 ≤ a ∧ p.2 ≤ b}}
  rw [hslice 0 q₁, hslice r q₁]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [gaussianQuadrant_zero (cdf_nonneg _ _) (cdf_le_one _ _) (cdf_nonneg _ _) (cdf_le_one _ _)]
  exact mul_le_gaussianQuadrant hr0 hr1 (cdf_nonneg _ _) (cdf_le_one _ _)
    (cdf_nonneg _ _) (cdf_le_one _ _)

/-- Decomposition `P_ρ[a < z ∧ z' ≤ b] = Φ b - P_ρ[z ≤ a ∧ z' ≤ b]` for `|ρ| ≤ 1`. -/
theorem measureReal_correlatedGaussian_gt_and_le {ρ : ℝ} (hρ : |ρ| ≤ 1) (a b : ℝ) :
    (correlatedGaussian ρ).real {p | a < p.1 ∧ p.2 ≤ b} =
      Φ b - (correlatedGaussian ρ).real {p | p.1 ≤ a ∧ p.2 ≤ b} := by
  have hsub : {p : ℝ × ℝ | p.1 ≤ a ∧ p.2 ≤ b} ⊆ {p | p.2 ≤ b} := fun _ hp => hp.2
  have hdiff : {p : ℝ × ℝ | p.2 ≤ b} \ {p | p.1 ≤ a ∧ p.2 ≤ b} = {p | a < p.1 ∧ p.2 ≤ b} := by
    ext p
    simp only [Set.mem_sdiff, mem_ofPred_eq]
    exact ⟨fun ⟨hb, hna⟩ => ⟨lt_of_not_ge fun ha => hna ⟨ha, hb⟩, hb⟩,
      fun ⟨ha, hb⟩ => ⟨hb, fun ⟨ha', _⟩ => not_lt_of_ge ha' ha⟩⟩
  have hsnd : (correlatedGaussian ρ).real {p | p.2 ≤ b} = Φ b := by
    have h := map_measureReal_apply (μ := correlatedGaussian ρ) measurable_snd
      (measurableSet_Iic (a := b))
    rw [correlatedGaussian_map_snd hρ, ← cdf_eq_real] at h
    exact h.symm
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 ≤ a ∧ p.2 ≤ b} :=
    (measurableSet_Iic.preimage measurable_fst).inter (measurableSet_Iic.preimage measurable_snd)
  rw [← hdiff, measureReal_sdiff hsub hmeas, hsnd]

/-- **Plackett antitonicity of crossing probabilities.** Increasing `0 ≤ ρ₁ ≤ ρ₂ ≤ 1` *decreases*
`P_ρ[a < z ∧ z' ≤ b]` for all thresholds `a, b ∈ ℝ`. -/
theorem measureReal_correlatedGaussian_gt_and_le_anti {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 ≤ ρ₁) (h12 : ρ₁ ≤ ρ₂) (hρ₂ : ρ₂ ≤ 1) (a b : ℝ) :
    (correlatedGaussian ρ₂).real {p | a < p.1 ∧ p.2 ≤ b} ≤
      (correlatedGaussian ρ₁).real {p | a < p.1 ∧ p.2 ≤ b} := by
  rw [measureReal_correlatedGaussian_gt_and_le (abs_le.mpr ⟨by linarith, hρ₂⟩),
    measureReal_correlatedGaussian_gt_and_le (abs_le.mpr ⟨by linarith, h12.trans hρ₂⟩)]
  linarith [measureReal_correlatedGaussian_le_and_le_mono hρ₁ h12 hρ₂ a b]

/-- Symmetry `P_ρ[-d < z ∧ z' ≤ -d] = P_ρ[d < z ∧ z' ≤ d]` for `|ρ| ≤ 1`. -/
theorem measureReal_correlatedGaussian_gt_neg_le_neg {ρ : ℝ} (hρ : |ρ| ≤ 1) (d : ℝ) :
    (correlatedGaussian ρ).real {p | -d < p.1 ∧ p.2 ≤ -d} =
      (correlatedGaussian ρ).real {p | d < p.1 ∧ p.2 ≤ d} := by
  rw [measureReal_correlatedGaussian_gt_and_le hρ, measureReal_correlatedGaussian_gt_and_le hρ]
  have hneg : (correlatedGaussian ρ).real {p | p.1 ≤ -d ∧ p.2 ≤ -d} =
      (correlatedGaussian ρ).real {p | d ≤ p.1 ∧ d ≤ p.2} := by
    have hm : MeasurableSet {p : ℝ × ℝ | p.1 ≤ -d ∧ p.2 ≤ -d} :=
      (measurableSet_Iic.preimage measurable_fst).inter (measurableSet_Iic.preimage measurable_snd)
    conv_lhs => rw [← correlatedGaussian_map_neg hρ,
      map_measureReal_apply (f := fun p : ℝ × ℝ => -p) measurable_neg hm]
    congr 1
    ext p
    simp
  have hae1 : ∀ᵐ p ∂correlatedGaussian ρ, p.1 ≠ d := by
    refine ae_of_ae_map (p := (· ≠ d)) measurable_fst.aemeasurable ?_
    rw [correlatedGaussian_map_fst]
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    exact measure_eq_zero_iff_ae_notMem.mp (measure_singleton d)
  have hae2 : ∀ᵐ p ∂correlatedGaussian ρ, p.2 ≠ d := by
    refine ae_of_ae_map (p := (· ≠ d)) measurable_snd.aemeasurable ?_
    rw [correlatedGaussian_map_snd hρ]
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    exact measure_eq_zero_iff_ae_notMem.mp (measure_singleton d)
  have hstrict : (correlatedGaussian ρ).real {p | d ≤ p.1 ∧ d ≤ p.2} =
      (correlatedGaussian ρ).real {p | d < p.1 ∧ d < p.2} := by
    refine measureReal_congr (Filter.eventuallyEqSet_iff.mpr ((hae1.and hae2).mono fun p hp => ?_))
    simp only [mem_ofPred_eq, lt_iff_le_and_ne, ne_eq]
    exact ⟨fun h => ⟨⟨h.1, hp.1.symm⟩, ⟨h.2, hp.2.symm⟩⟩, fun h => ⟨h.1.1, h.2.1⟩⟩
  have hu : {p : ℝ × ℝ | d < p.1 ∧ d < p.2} = ({p | p.1 ≤ d} ∪ {p | p.2 ≤ d})ᶜ := by
    ext p
    simp
  have h1m : MeasurableSet {p : ℝ × ℝ | p.1 ≤ d} := measurableSet_Iic.preimage measurable_fst
  have h2m : MeasurableSet {p : ℝ × ℝ | p.2 ≤ d} := measurableSet_Iic.preimage measurable_snd
  have hp1 : (correlatedGaussian ρ).real {p | p.1 ≤ d} = Φ d := by
    have h := map_measureReal_apply (μ := correlatedGaussian ρ) measurable_fst
      (measurableSet_Iic (a := d))
    rw [correlatedGaussian_map_fst, ← cdf_eq_real] at h
    exact h.symm
  have hp2 : (correlatedGaussian ρ).real {p | p.2 ≤ d} = Φ d := by
    have h := map_measureReal_apply (μ := correlatedGaussian ρ) measurable_snd
      (measurableSet_Iic (a := d))
    rw [correlatedGaussian_map_snd hρ, ← cdf_eq_real] at h
    exact h.symm
  have hunion : (correlatedGaussian ρ).real ({p | p.1 ≤ d} ∪ {p | p.2 ≤ d}) =
      2 * Φ d - (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ d} := by
    have h := measureReal_union_add_inter (μ := correlatedGaussian ρ)
      (s := {p : ℝ × ℝ | p.1 ≤ d}) h2m
    change (correlatedGaussian ρ).real ({p | p.1 ≤ d} ∪ {p | p.2 ≤ d}) +
        (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ d} = _ at h
    linarith [h, hp1, hp2]
  rw [hneg, hstrict, hu, probReal_compl_eq_one_sub (h1m.union h2m), hunion,
    cdf_gaussianReal_neg one_ne_zero]
  ring

/-- Exact convex-excess identity `p_{+-} + p_{-+} - 2 p_{dd} ≥ 0` for `0 ≤ d` and `|ρ| ≤ 1`:
`p_{+-} + p_{-+} - 2 p_{dd} = P_ρ[-d < z ≤ d ∧ -d < z' ≤ d] ≥ 0`. -/
theorem two_mul_correlatedGaussian_gt_le_diag_le {ρ d : ℝ} (hρ : |ρ| ≤ 1) (hd : 0 ≤ d) :
    2 * (correlatedGaussian ρ).real {p | d < p.1 ∧ p.2 ≤ d} ≤
      (correlatedGaussian ρ).real {p | d < p.1 ∧ p.2 ≤ -d} +
        (correlatedGaussian ρ).real {p | -d < p.1 ∧ p.2 ≤ d} := by
  rw [measureReal_correlatedGaussian_gt_and_le hρ d d,
    measureReal_correlatedGaussian_gt_and_le hρ d (-d),
    measureReal_correlatedGaussian_gt_and_le hρ (-d) d]
  have hsymm : (correlatedGaussian ρ).real {p | p.1 ≤ -d ∧ p.2 ≤ d} =
      (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ -d} := by
    rw [← gaussianQuadrant_cdf_cdf, ← gaussianQuadrant_cdf_cdf, gaussianQuadrant_comm hρ]
  have hcdf : Φ (-d) + Φ d = 1 := by
    rw [cdf_gaussianReal_neg one_ne_zero]
    ring
  have hbox : 0 ≤ 1 - 2 * Φ d + 2 * (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ d} -
      2 * (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ -d} := by
    have hsub1 : {p : ℝ × ℝ | p.1 ≤ d ∧ p.2 ≤ -d} ⊆ {p | p.1 ≤ d ∧ p.2 ≤ d} :=
      fun _ hp => ⟨hp.1, hp.2.trans (by linarith)⟩
    have hm_dd : MeasurableSet {p : ℝ × ℝ | p.1 ≤ d ∧ p.2 ≤ -d} :=
      (measurableSet_Iic.preimage measurable_fst).inter (measurableSet_Iic.preimage measurable_snd)
    have hdiff1 : {p : ℝ × ℝ | p.1 ≤ d ∧ p.2 ≤ d} \ {p | p.1 ≤ d ∧ p.2 ≤ -d} =
        {p | p.1 ≤ d ∧ -d < p.2 ∧ p.2 ≤ d} := by
      ext p
      simp only [Set.mem_sdiff, mem_ofPred_eq]
      exact ⟨fun ⟨⟨h1, h2⟩, hn⟩ => ⟨h1, lt_of_not_ge fun hle => hn ⟨h1, hle⟩, h2⟩,
        fun ⟨h1, hgt, h2⟩ => ⟨⟨h1, h2⟩, fun ⟨_, hle⟩ => not_lt_of_ge hle hgt⟩⟩
    have hs1 : (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ -d < p.2 ∧ p.2 ≤ d} =
        (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ d} -
          (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ -d} := by
      rw [← hdiff1, measureReal_sdiff hsub1 hm_dd]
    have hae2 : ∀ᵐ p ∂correlatedGaussian ρ, p.2 ≠ -d ∧ p.2 ≠ d := by
      have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
      refine Filter.Eventually.and ?_ ?_
      · refine ae_of_ae_map (p := (· ≠ -d)) measurable_snd.aemeasurable ?_
        rw [correlatedGaussian_map_snd hρ]
        exact measure_eq_zero_iff_ae_notMem.mp (measure_singleton (-d))
      · refine ae_of_ae_map (p := (· ≠ d)) measurable_snd.aemeasurable ?_
        rw [correlatedGaussian_map_snd hρ]
        exact measure_eq_zero_iff_ae_notMem.mp (measure_singleton d)
    have hneg_strip : (correlatedGaussian ρ).real {p | d < p.1 ∧ -d < p.2 ∧ p.2 ≤ d} ≤
        (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ -d < p.2 ∧ p.2 ≤ d} := by
      have hm_strip : MeasurableSet {p : ℝ × ℝ | d < p.1 ∧ -d < p.2 ∧ p.2 ≤ d} :=
        (measurableSet_Ioi.preimage measurable_fst).inter
          ((measurableSet_Ioi.preimage measurable_snd).inter
            (measurableSet_Iic.preimage measurable_snd))
      have heq_neg : (correlatedGaussian ρ).real {p | d < p.1 ∧ -d < p.2 ∧ p.2 ≤ d} =
          (correlatedGaussian ρ).real {p | p.1 < -d ∧ -d ≤ p.2 ∧ p.2 < d} := by
        conv_lhs => rw [← correlatedGaussian_map_neg hρ,
          map_measureReal_apply (f := fun p : ℝ × ℝ => -p) measurable_neg hm_strip]
        congr 1
        ext p
        simp only [mem_preimage, mem_ofPred_eq, Prod.fst_neg, Prod.snd_neg]
        constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨by linarith, by linarith, by linarith⟩
      have hae_eq : (correlatedGaussian ρ).real {p | p.1 < -d ∧ -d ≤ p.2 ∧ p.2 < d} =
          (correlatedGaussian ρ).real {p | p.1 < -d ∧ -d < p.2 ∧ p.2 ≤ d} := by
        refine measureReal_congr (Filter.eventuallyEqSet_iff.mpr (hae2.mono fun p hp => ?_))
        simp only [mem_ofPred_eq]
        exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, lt_of_le_of_ne h2 hp.1.symm, h3.le⟩,
          fun ⟨h1, h2, h3⟩ => ⟨h1, h2.le, lt_of_le_of_ne h3 hp.2⟩⟩
      rw [heq_neg, hae_eq]
      exact measureReal_mono fun p hp => ⟨hp.1.le.trans (by linarith), hp.2⟩
    have htot_strip : (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ -d < p.2 ∧ p.2 ≤ d} +
        (correlatedGaussian ρ).real {p | d < p.1 ∧ -d < p.2 ∧ p.2 ≤ d} = 2 * Φ d - 1 := by
      have hun : {p : ℝ × ℝ | p.1 ≤ d ∧ -d < p.2 ∧ p.2 ≤ d} ∪
          {p | d < p.1 ∧ -d < p.2 ∧ p.2 ≤ d} = {p | p.2 ≤ d} \ {p | p.2 ≤ -d} := by
        ext p
        simp only [mem_union, mem_ofPred_eq, Set.mem_sdiff, not_le]
        exact ⟨fun h => h.elim (fun h1 => ⟨h1.2.2, h1.2.1⟩) (fun h2 => ⟨h2.2.2, h2.2.1⟩),
          fun ⟨h1, h2⟩ => (le_or_gt p.1 d).imp (fun ha => ⟨ha, h2, h1⟩) (fun ha => ⟨ha, h2, h1⟩)⟩
      have hdisj : Disjoint {p : ℝ × ℝ | p.1 ≤ d ∧ -d < p.2 ∧ p.2 ≤ d}
          {p | d < p.1 ∧ -d < p.2 ∧ p.2 ≤ d} :=
        disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1.1 h2.1
      have hm2 : MeasurableSet {p : ℝ × ℝ | d < p.1 ∧ -d < p.2 ∧ p.2 ≤ d} :=
        (measurableSet_Ioi.preimage measurable_fst).inter
          ((measurableSet_Ioi.preimage measurable_snd).inter
            (measurableSet_Iic.preimage measurable_snd))
      have hp_le (t : ℝ) : (correlatedGaussian ρ).real {p | p.2 ≤ t} = Φ t := by
        have h := map_measureReal_apply (μ := correlatedGaussian ρ) measurable_snd
          (measurableSet_Iic (a := t))
        rw [correlatedGaussian_map_snd hρ, ← cdf_eq_real] at h
        exact h.symm
      have hsub_p : {p : ℝ × ℝ | p.2 ≤ -d} ⊆ {p | p.2 ≤ d} :=
        fun _ (hp : _ ≤ -d) => hp.trans (by linarith)
      rw [← measureReal_union hdisj hm2, hun,
        measureReal_sdiff hsub_p (measurableSet_Iic.preimage measurable_snd),
        hp_le d, hp_le (-d), cdf_gaussianReal_neg one_ne_zero]
      ring
    linarith [hs1, hneg_strip, htot_strip]
  linarith [hsymm, hcdf, hbox]

end ProbabilityTheory
