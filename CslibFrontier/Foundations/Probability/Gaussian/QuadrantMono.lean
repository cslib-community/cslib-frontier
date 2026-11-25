/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Probability/Distributions/Gaussian/`
-- `QuadrantMono.lean`)

public import CslibFrontier.Foundations.Probability.Gaussian.Quadrant
public import Mathlib.Analysis.InnerProductSpace.PiL2
import CslibFrontier.Foundations.Probability.Gaussian.Borell
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.Gaussian.Quantile

/-!
# Correlation monotonicity and threshold crossing identities for Gaussian quadrants

For `ρ ∈ [-1, 1]`, increasing the correlation increases every lower-quadrant probability
`P_ρ[z ≤ a ∧ z' ≤ b]` (`measureReal_correlatedGaussian_le_and_le_mono`), equivalently `Λ_ρ(α, β)` is
monotone in `ρ` on `[-1, 1]` (`monotoneOn_gaussianQuadrant`), and decreases every asymmetric
threshold-crossing probability `P_ρ[a < z ∧ z' ≤ b]`
(`measureReal_correlatedGaussian_gt_and_le_anti`).

On `[0, 1]`, rather than differentiating bivariate Gaussian integrals with respect to `ρ`, we couple
both pairs in `EuclideanSpace ℝ (Fin 1 ⊕ Fin 2)` with shared first coordinate `√ρ₁ ω₀`. Conditioned
on `ω₀`, the `ρ₁`-pair becomes independent (`gaussianQuadrant 0 α β = α β`), while the `ρ₂`-pair has
residual correlation `r = (ρ₂ - ρ₁) / (1 - ρ₁) ∈ [0, 1]`, which dominates `α β` slice by slice via
`mul_le_gaussianQuadrant` ([O'Donnell, Exercise 11.19(c)][ODonnell2014]). Reflection in the second
coordinate (`gaussianQuadrant_neg`, [O'Donnell, Exercise 11.19(b)][ODonnell2014]) transfers
monotonicity to `[-1, 0]`, and transitivity through `0` covers `[-1, 1]`.

We also record the double-reflection identity `Λ_ρ(1 - α, 1 - β) = 1 - α - β + Λ_ρ(α, β)`
(`gaussianQuadrant_one_sub_one_sub`), the crossing decomposition
`P_ρ[a < z ∧ z' ≤ b] = Φ b - P_ρ[z ≤ a ∧ z' ≤ b]`, the negation symmetry
`P_ρ[-d < z ∧ z' ≤ -d] = P_ρ[d < z ∧ z' ≤ d]`, and the box-excess inequality
`2 P_ρ[d < z ∧ z' ≤ d] ≤ P_ρ[d < z ∧ z' ≤ -d] + P_ρ[-d < z ∧ z' ≤ d]` for `0 ≤ d`.

## Main results

* `ProbabilityTheory.measureReal_pi_inner_prod_eq_correlatedGaussian`: joint law of two unit
  projections under `Measure.pi (gaussianReal 0 1)`.
* `ProbabilityTheory.measureReal_correlatedGaussian_le_and_le_mono`,
  `ProbabilityTheory.monotoneOn_gaussianQuadrant`: correlation monotonicity of bivariate Gaussian
  quadrants on `[-1, 1]`.
* `ProbabilityTheory.measureReal_correlatedGaussian_gt_and_le`,
  `ProbabilityTheory.measureReal_correlatedGaussian_gt_and_le_anti`: crossing decomposition and
  correlation antitonicity on `[-1, 1]`.
* `ProbabilityTheory.gaussianQuadrant_one_sub_one_sub`,
  `ProbabilityTheory.measureReal_correlatedGaussian_gt_neg_le_neg`,
  `ProbabilityTheory.two_mul_correlatedGaussian_gt_le_diag_le`: double reflection, diagonal
  symmetry, and box-excess inequality for shifted thresholds.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Exercise 11.19(b)–(c).
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

private theorem measureReal_correlatedGaussian_le_and_le_mono_nonneg {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 ≤ ρ₁) (h12 : ρ₁ ≤ ρ₂) (hρ₂ : ρ₂ ≤ 1) (a b : ℝ) :
    (correlatedGaussian ρ₁).real {p | p.1 ≤ a ∧ p.2 ≤ b} ≤
      (correlatedGaussian ρ₂).real {p | p.1 ≤ a ∧ p.2 ≤ b} := by
  rcases eq_or_lt_of_le (h12.trans hρ₂) with rfl | hρ₁_lt
  · rw [le_antisymm hρ₂ h12]
  set ac := √ρ₁
  set s := √(1 - ρ₁)
  have hs_pos : 0 < s := sqrt_pos.mpr (by linarith)
  have hac_sq : ac ^ 2 = ρ₁ := sq_sqrt hρ₁
  have hs_sq : s ^ 2 = 1 - ρ₁ := sq_sqrt (by linarith)
  set r := (ρ₂ - ρ₁) / (1 - ρ₁)
  have hr0 : 0 ≤ r := div_nonneg (by linarith) (by linarith)
  have hr1 : r ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  let u : EuclideanSpace ℝ (Fin 1 ⊕ Fin 2) :=
    WithLp.toLp 2 (Sum.elim (fun _ => ac) ![s, 0])
  let v : ℝ → EuclideanSpace ℝ (Fin 1 ⊕ Fin 2) := fun t =>
    WithLp.toLp 2 (Sum.elim (fun _ => ac) ![s * t, s * √(1 - t ^ 2)])
  have hu_norm : ‖u‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_two]
    simp only [u, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, sq_abs]
    rw [sqrt_eq_one]
    linear_combination hac_sq + hs_sq
  have hv_norm (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ‖v t‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_two]
    simp only [v, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, sq_abs]
    rw [sqrt_eq_one, mul_pow, mul_pow, sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - t ^ 2)]
    linear_combination hac_sq + hs_sq
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

private theorem measureReal_correlatedGaussian_le_and_le_mono_nonpos {ρ₁ ρ₂ : ℝ}
    (hρ₁ : -1 ≤ ρ₁) (h12 : ρ₁ ≤ ρ₂) (hρ₂ : ρ₂ ≤ 0) (a b : ℝ) :
    (correlatedGaussian ρ₁).real {p | p.1 ≤ a ∧ p.2 ≤ b} ≤
      (correlatedGaussian ρ₂).real {p | p.1 ≤ a ∧ p.2 ≤ b} := by
  have hneg (ρ : ℝ) (hρ : |ρ| ≤ 1) :
      (correlatedGaussian ρ).real {p | p.1 ≤ a ∧ p.2 ≤ b} =
        Φ a - (correlatedGaussian (-ρ)).real {p | p.1 ≤ a ∧ p.2 ≤ -b} := by
    conv_lhs => rw [← gaussianQuadrant_cdf_cdf, ← neg_neg ρ]
    rw [gaussianQuadrant_neg (by rwa [abs_neg]) (cdf_nonneg _ a) (cdf_le_one _ a),
      ← cdf_gaussianReal_neg one_ne_zero b, gaussianQuadrant_cdf_cdf]
  rw [hneg ρ₁ (abs_le.mpr ⟨hρ₁, h12.trans (hρ₂.trans zero_le_one)⟩),
    hneg ρ₂ (abs_le.mpr ⟨hρ₁.trans h12, hρ₂.trans zero_le_one⟩)]
  have hm := measureReal_correlatedGaussian_le_and_le_mono_nonneg
    (neg_nonneg.mpr hρ₂) (neg_le_neg h12) (by linarith) a (-b)
  linarith

/-- **Correlation monotonicity of bivariate Gaussian quadrants.** Increasing `-1 ≤ ρ₁ ≤ ρ₂ ≤ 1`
increases the lower-quadrant probability `P_ρ[z ≤ a ∧ z' ≤ b]` for all `a, b ∈ ℝ`. -/
theorem measureReal_correlatedGaussian_le_and_le_mono {ρ₁ ρ₂ : ℝ}
    (hρ₁ : -1 ≤ ρ₁) (h12 : ρ₁ ≤ ρ₂) (hρ₂ : ρ₂ ≤ 1) (a b : ℝ) :
    (correlatedGaussian ρ₁).real {p | p.1 ≤ a ∧ p.2 ≤ b} ≤
      (correlatedGaussian ρ₂).real {p | p.1 ≤ a ∧ p.2 ≤ b} := by
  rcases le_total 0 ρ₁ with h01 | h10
  · exact measureReal_correlatedGaussian_le_and_le_mono_nonneg h01 h12 hρ₂ a b
  · rcases le_total ρ₂ 0 with h20 | h02
    · exact measureReal_correlatedGaussian_le_and_le_mono_nonpos hρ₁ h12 h20 a b
    · exact (measureReal_correlatedGaussian_le_and_le_mono_nonpos hρ₁ h10 le_rfl a b).trans
        (measureReal_correlatedGaussian_le_and_le_mono_nonneg le_rfl h02 hρ₂ a b)

/-- `ρ ↦ Λ_ρ(α, β)` is monotone on `[-1, 1]` for all `α, β ∈ ℝ`. -/
theorem monotoneOn_gaussianQuadrant (α β : ℝ) :
    MonotoneOn (fun ρ => gaussianQuadrant ρ α β) (Icc (-1) 1) := by
  intro ρ₁ hρ₁ ρ₂ hρ₂ h12
  dsimp only
  rw [gaussianQuadrant_eq_clamp_left ρ₁, gaussianQuadrant_eq_clamp_right ρ₁,
    gaussianQuadrant_eq_clamp_left ρ₂, gaussianQuadrant_eq_clamp_right ρ₂]
  set α' := max (min α 1) 0
  set β' := max (min β 1) 0
  have hα0 : 0 ≤ α' := le_max_right _ _
  have hα1 : α' ≤ 1 := max_le (min_le_right _ _) zero_le_one
  have hβ0 : 0 ≤ β' := le_max_right _ _
  have hβ1 : β' ≤ 1 := max_le (min_le_right _ _) zero_le_one
  rcases hα0.eq_or_lt with h0 | hα0'
  · rw [← h0, gaussianQuadrant_zero_left, gaussianQuadrant_zero_left]
  rcases hα1.eq_or_lt with h1 | hα1'
  · rw [h1, gaussianQuadrant_one_left (abs_le.mpr hρ₁) hβ0 hβ1,
      gaussianQuadrant_one_left (abs_le.mpr hρ₂) hβ0 hβ1]
  rcases hβ0.eq_or_lt with h0 | hβ0'
  · rw [← h0, gaussianQuadrant_zero_right, gaussianQuadrant_zero_right]
  rcases hβ1.eq_or_lt with h1 | hβ1'
  · rw [h1, gaussianQuadrant_one_right _ hα0 hα1, gaussianQuadrant_one_right _ hα0 hα1]
  rw [← cdf_gaussianQuantile ⟨hα0', hα1'⟩, ← cdf_gaussianQuantile ⟨hβ0', hβ1'⟩,
    gaussianQuadrant_cdf_cdf, gaussianQuadrant_cdf_cdf]
  exact measureReal_correlatedGaussian_le_and_le_mono hρ₁.1 h12 hρ₂.2 _ _

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

/-- **Correlation antitonicity of crossing probabilities.** Increasing `-1 ≤ ρ₁ ≤ ρ₂ ≤ 1`
*decreases* `P_ρ[a < z ∧ z' ≤ b]` for all thresholds `a, b ∈ ℝ`. -/
theorem measureReal_correlatedGaussian_gt_and_le_anti {ρ₁ ρ₂ : ℝ}
    (hρ₁ : -1 ≤ ρ₁) (h12 : ρ₁ ≤ ρ₂) (hρ₂ : ρ₂ ≤ 1) (a b : ℝ) :
    (correlatedGaussian ρ₂).real {p | a < p.1 ∧ p.2 ≤ b} ≤
      (correlatedGaussian ρ₁).real {p | a < p.1 ∧ p.2 ≤ b} := by
  rw [measureReal_correlatedGaussian_gt_and_le (abs_le.mpr ⟨hρ₁.trans h12, hρ₂⟩),
    measureReal_correlatedGaussian_gt_and_le (abs_le.mpr ⟨hρ₁, h12.trans hρ₂⟩)]
  linarith [measureReal_correlatedGaussian_le_and_le_mono hρ₁ h12 hρ₂ a b]

/-- **Double reflection** ([O'Donnell, Exercise 11.19(b)][ODonnell2014]):
`Λ_ρ(1 - α, 1 - β) = 1 - α - β + Λ_ρ(α, β)` for `|ρ| ≤ 1` and `α, β ∈ [0, 1]`. -/
theorem gaussianQuadrant_one_sub_one_sub {ρ : ℝ} (hρ : |ρ| ≤ 1) {α β : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    gaussianQuadrant ρ (1 - α) (1 - β) = 1 - α - β + gaussianQuadrant ρ α β := by
  have h1 := gaussianQuadrant_neg (ρ := -ρ) (by rwa [abs_neg])
    (sub_nonneg.mpr hα1) (sub_le_self 1 hα0) (1 - β)
  have h2 := gaussianQuadrant_neg_eq_sub_one_sub_left hρ (1 - α) hβ0 hβ1
  rw [neg_neg, sub_sub_cancel] at h1
  rw [sub_sub_cancel] at h2
  linarith

/-- Symmetry `P_ρ[-d < z ∧ z' ≤ -d] = P_ρ[d < z ∧ z' ≤ d]` for `|ρ| ≤ 1`. -/
theorem measureReal_correlatedGaussian_gt_neg_le_neg {ρ : ℝ} (hρ : |ρ| ≤ 1) (d : ℝ) :
    (correlatedGaussian ρ).real {p | -d < p.1 ∧ p.2 ≤ -d} =
      (correlatedGaussian ρ).real {p | d < p.1 ∧ p.2 ≤ d} := by
  rw [measureReal_correlatedGaussian_gt_and_le hρ, measureReal_correlatedGaussian_gt_and_le hρ,
    ← gaussianQuadrant_cdf_cdf, ← gaussianQuadrant_cdf_cdf, cdf_gaussianReal_neg one_ne_zero d,
    gaussianQuadrant_one_sub_one_sub hρ (cdf_nonneg _ d) (cdf_le_one _ d)
      (cdf_nonneg _ d) (cdf_le_one _ d)]
  ring

/-- Box-excess inequality `2 P_ρ[d < z ∧ z' ≤ d] ≤ P_ρ[d < z ∧ z' ≤ -d] + P_ρ[-d < z ∧ z' ≤ d]`
for `0 ≤ d` and `|ρ| ≤ 1` (the difference equals `P_ρ[-d < z ≤ d ∧ -d < z' ≤ d] ≥ 0`). -/
theorem two_mul_correlatedGaussian_gt_le_diag_le {ρ d : ℝ} (hρ : |ρ| ≤ 1) (hd : 0 ≤ d) :
    2 * (correlatedGaussian ρ).real {p | d < p.1 ∧ p.2 ≤ d} ≤
      (correlatedGaussian ρ).real {p | d < p.1 ∧ p.2 ≤ -d} +
        (correlatedGaussian ρ).real {p | -d < p.1 ∧ p.2 ≤ d} := by
  have hstrip (a : ℝ) : (correlatedGaussian ρ).real {p | p.1 ≤ a ∧ -d < p.2 ∧ p.2 ≤ d} =
      gaussianQuadrant ρ (Φ a) (Φ d) - gaussianQuadrant ρ (Φ a) (Φ (-d)) := by
    have hsub : {p : ℝ × ℝ | p.1 ≤ a ∧ p.2 ≤ -d} ⊆ {p | p.1 ≤ a ∧ p.2 ≤ d} :=
      fun _ hp => ⟨hp.1, hp.2.trans (by linarith)⟩
    have hm : MeasurableSet {p : ℝ × ℝ | p.1 ≤ a ∧ p.2 ≤ -d} :=
      (measurableSet_Iic.preimage measurable_fst).inter (measurableSet_Iic.preimage measurable_snd)
    have hdiff : {p : ℝ × ℝ | p.1 ≤ a ∧ p.2 ≤ d} \ {p | p.1 ≤ a ∧ p.2 ≤ -d} =
        {p | p.1 ≤ a ∧ -d < p.2 ∧ p.2 ≤ d} := by
      ext p
      simp only [Set.mem_sdiff, mem_ofPred_eq]
      exact ⟨fun ⟨⟨h1, h2⟩, hn⟩ => ⟨h1, lt_of_not_ge fun hle => hn ⟨h1, hle⟩, h2⟩,
        fun ⟨h1, hgt, h2⟩ => ⟨⟨h1, h2⟩, fun ⟨_, hle⟩ => not_lt_of_ge hle hgt⟩⟩
    rw [← hdiff, measureReal_sdiff hsub hm, ← gaussianQuadrant_cdf_cdf, ← gaussianQuadrant_cdf_cdf]
  have hmono : gaussianQuadrant ρ (Φ (-d)) (Φ d) - gaussianQuadrant ρ (Φ (-d)) (Φ (-d)) ≤
      gaussianQuadrant ρ (Φ d) (Φ d) - gaussianQuadrant ρ (Φ d) (Φ (-d)) := by
    rw [← hstrip (-d), ← hstrip d]
    exact measureReal_mono fun _ hp => ⟨hp.1.trans (by linarith), hp.2⟩
  rw [measureReal_correlatedGaussian_gt_and_le hρ d d,
    measureReal_correlatedGaussian_gt_and_le hρ d (-d),
    measureReal_correlatedGaussian_gt_and_le hρ (-d) d,
    ← gaussianQuadrant_cdf_cdf, ← gaussianQuadrant_cdf_cdf, ← gaussianQuadrant_cdf_cdf]
  rw [gaussianQuadrant_comm hρ (Φ (-d)) (Φ d)] at hmono ⊢
  rw [cdf_gaussianReal_neg one_ne_zero d,
    gaussianQuadrant_one_sub_one_sub hρ (cdf_nonneg _ d) (cdf_le_one _ d)
      (cdf_nonneg _ d) (cdf_le_one _ d)] at hmono
  rw [cdf_gaussianReal_neg one_ne_zero d]
  linarith [hmono]

end ProbabilityTheory
