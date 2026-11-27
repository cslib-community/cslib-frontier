/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import CslibFrontier.Foundations.Analysis.Calculus.LipschitzSmoothing
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.CDF

/-!
# Lévy-distance bounds from smooth test functions

Two real random variables `X` and `Y` have **Lévy distance** at most `δ` when
`Pr[Y ≤ u - δ] - δ ≤ Pr[X ≤ u] ≤ Pr[Y ≤ u + δ] + δ` for every `u`. This file turns a comparison
of `E[φ(X)]` and `E[φ(Y)]` for smooth tests `φ` into such a bound, as in
[O'Donnell, Corollaries 11.61 and 11.70][ODonnell2014] and Exercises 11.41 and 11.42.

Suppose that `|E[φ(X)] - E[φ(Y)]| ≤ C B` for every `φ` of class `Cᵐ` with `|φ⁽ᵐ⁾| ≤ C`. The
smoothed step `Real.stepSmoothing m u (η / (m + 1))` is `1` on `(-∞, u]`, `0` on `[u + η, ∞)`,
takes values in `[0, 1]` and has `|φ⁽ᵐ⁾| ≤ 2ᵐ⁻¹ (m + 1)ᵐ / ηᵐ`, so
`Pr[X ≤ u] ≤ E[φ(X)] ≤ E[φ(Y)] + 2ᵐ⁻¹ (m + 1)ᵐ B / ηᵐ ≤ Pr[Y ≤ u + η] + 2ᵐ⁻¹ (m + 1)ᵐ B / ηᵐ`
(`measureReal_le_le_add_div_pow_of_forall_contDiff`). Taking `η = δ` with
`2ᵐ⁻¹ (m + 1)ᵐ B ≤ δᵐ⁺¹` bounds the Lévy distance by `δ`
(`measureReal_le_le_add_of_forall_contDiff`, `measureReal_le_sub_le_of_forall_contDiff`); when
`δ = 0` the right-continuity of distribution functions finishes the argument.

## Main results

* `ProbabilityTheory.measureReal_le_le_integral_comp`,
  `ProbabilityTheory.integral_comp_le_measureReal_le`: `[0, 1]`-valued tests sandwich
  `Pr[X ≤ v]`.
* `ProbabilityTheory.le_measureReal_le_of_forall_lt`: right-continuity of `v ↦ Pr[X ≤ v]`.
* `ProbabilityTheory.measureReal_le_le_add_div_pow_of_forall_contDiff`: the bound with an
  explicit shift `η > 0`.
* `ProbabilityTheory.measureReal_le_le_add_of_forall_contDiff`,
  `ProbabilityTheory.measureReal_le_sub_le_of_forall_contDiff`: the Lévy-distance pair.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Sections 11.5 and 11.6.
-/

public section

open MeasureTheory Real
open Set (Iic Icc)

namespace ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {Q : Measure Ω'}

/-! ### Distribution functions and bounded tests -/

/-- `Pr[X ≤ v] - E[φ(X)]` is the integral of `1_{(-∞, v]} - φ` against the law of `X`, for a
continuous `[0, 1]`-valued `φ`. -/
private theorem measureReal_le_sub_integral_comp [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : AEMeasurable X P) {φ : ℝ → ℝ} (hφ : Continuous φ) (h01 : ∀ x, φ x ∈ Icc 0 1) (v : ℝ) :
    P.real {ω | X ω ≤ v} - ∫ ω, φ (X ω) ∂P = ∫ x, ((Iic v).indicator 1 x - φ x) ∂P.map X := by
  rw [show {ω | X ω ≤ v} = X ⁻¹' Iic v from rfl,
    ← map_measureReal_apply_of_aemeasurable hX measurableSet_Iic,
    ← integral_indicator_one measurableSet_Iic, ← integral_map hX hφ.aestronglyMeasurable]
  exact (integral_sub ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)
    (Integrable.of_bound hφ.aestronglyMeasurable 1 (ae_of_all _ fun x =>
      abs_le.2 ⟨by linarith [(h01 x).1], (h01 x).2⟩))).symm

/-- If `0 ≤ φ ≤ 1` and `φ = 1` on `(-∞, v]`, then `Pr[X ≤ v] ≤ E[φ(X)]`. -/
theorem measureReal_le_le_integral_comp [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : AEMeasurable X P) {φ : ℝ → ℝ} (hφ : Continuous φ) (h01 : ∀ x, φ x ∈ Icc 0 1) {v : ℝ}
    (hv : ∀ x ≤ v, φ x = 1) : P.real {ω | X ω ≤ v} ≤ ∫ ω, φ (X ω) ∂P := by
  have h := measureReal_le_sub_integral_comp hX hφ h01 v
  have h0 : ∫ x, ((Iic v).indicator 1 x - φ x) ∂P.map X ≤ 0 := integral_nonpos fun x => by
    simp only [Set.indicator_apply, Set.mem_Iic, Pi.one_apply, Pi.zero_apply]
    split_ifs with hx
    · rw [hv x hx, sub_self]
    · linarith [(h01 x).1]
  linarith

/-- If `0 ≤ φ ≤ 1` and `φ = 0` on `(v, ∞)`, then `E[φ(X)] ≤ Pr[X ≤ v]`. -/
theorem integral_comp_le_measureReal_le [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : AEMeasurable X P) {φ : ℝ → ℝ} (hφ : Continuous φ) (h01 : ∀ x, φ x ∈ Icc 0 1) {v : ℝ}
    (hv : ∀ x, v < x → φ x = 0) : ∫ ω, φ (X ω) ∂P ≤ P.real {ω | X ω ≤ v} := by
  have h := measureReal_le_sub_integral_comp hX hφ h01 v
  have h0 : 0 ≤ ∫ x, ((Iic v).indicator 1 x - φ x) ∂P.map X := integral_nonneg fun x => by
    simp only [Set.indicator_apply, Set.mem_Iic, Pi.one_apply, Pi.zero_apply]
    split_ifs with hx
    · linarith [(h01 x).2]
    · rw [hv x (not_le.1 hx), sub_self]
  linarith

/-- **Right-continuity of distribution functions**: if `a ≤ Pr[X ≤ v]` for all `v > u`, then
`a ≤ Pr[X ≤ u]`. -/
theorem le_measureReal_le_of_forall_lt [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : AEMeasurable X P) {a u : ℝ} (h : ∀ v, u < v → a ≤ P.real {ω | X ω ≤ v}) :
    a ≤ P.real {ω | X ω ≤ u} := by
  have hmap (v : ℝ) : P.real {ω | X ω ≤ v} = (P.map X).real (Iic v) :=
    (map_measureReal_apply_of_aemeasurable hX measurableSet_Iic).symm
  simp only [hmap, ← cdf_eq_real] at h ⊢
  exact ge_of_tendsto (((cdf (P.map X)).right_continuous u).mono Set.Ioi_subset_Ici_self)
    (eventually_nhdsWithin_of_forall (s := Set.Ioi u) fun v hv => h v hv)

/-! ### From `Cᵐ` tests to the Lévy distance -/

variable [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {X : Ω → ℝ} {Y : Ω' → ℝ} {m : ℕ}
  {B : ℝ}

/-- **From `Cᵐ` tests to distribution functions**: suppose that
`|E[φ(X)] - E[φ(Y)]| ≤ C B` for every `φ` of class `Cᵐ` with `|φ⁽ᵐ⁾| ≤ C`. Then for every `u`
and `η > 0`, `Pr[X ≤ u] ≤ Pr[Y ≤ u + η] + 2ᵐ⁻¹ (m + 1)ᵐ B / ηᵐ`. This is the main step of
[O'Donnell, Corollary 11.61][ODonnell2014] (Exercise 11.42), with the smoothed step
`Real.stepSmoothing m u (η / (m + 1))` as the test. -/
theorem measureReal_le_le_add_div_pow_of_forall_contDiff (hX : AEMeasurable X P)
    (hY : AEMeasurable Y Q)
    (h : ∀ (φ : ℝ → ℝ) (C : ℝ), ContDiff ℝ m φ → (∀ s, |iteratedDeriv m φ s| ≤ C) →
      |∫ ω, φ (X ω) ∂P - ∫ ω, φ (Y ω) ∂Q| ≤ C * B) (u : ℝ) {η : ℝ} (hη : 0 < η) :
    P.real {ω | X ω ≤ u} ≤
      Q.real {ω | Y ω ≤ u + η} + 2 ^ (m - 1) * (m + 1) ^ m * B / η ^ m := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hh : 0 < η / (m + 1) := by positivity
  have hw : u + (m + 1) * (η / (m + 1)) = u + η := by field_simp
  have hφ := (contDiff_stepSmoothing m u (η / (m + 1))).continuous
  have hlo := measureReal_le_le_integral_comp hX hφ (stepSmoothing_mem_Icc m u hh) fun x hx =>
    stepSmoothing_eq_one_of_le hh hx
  have hhi := integral_comp_le_measureReal_le (v := u + η) hY hφ (stepSmoothing_mem_Icc m u hh)
    fun x hx => stepSmoothing_eq_zero_of_le hh (hw.trans_le hx.le)
  have hXY := (le_abs_self _).trans (h _ _ (contDiff_stepSmoothing m u _)
    (abs_iteratedDeriv_stepSmoothing_le m u hh))
  have hC : 2 ^ (m - 1) / (η / (m + 1)) ^ m * B = 2 ^ (m - 1) * (m + 1) ^ m * B / η ^ m := by
    rw [div_pow]
    field_simp
  linarith

/-- **From `Cᵐ` tests to the Lévy distance**, upper bound: in the setting of
`measureReal_le_le_add_div_pow_of_forall_contDiff`, if `δ ≥ 0` satisfies
`2ᵐ⁻¹ (m + 1)ᵐ B ≤ δᵐ⁺¹`, then `Pr[X ≤ u] ≤ Pr[Y ≤ u + δ] + δ` for every `u`
[O'Donnell, Corollary 11.61][ODonnell2014]. -/
theorem measureReal_le_le_add_of_forall_contDiff (hX : AEMeasurable X P)
    (hY : AEMeasurable Y Q)
    (h : ∀ (φ : ℝ → ℝ) (C : ℝ), ContDiff ℝ m φ → (∀ s, |iteratedDeriv m φ s| ≤ C) →
      |∫ ω, φ (X ω) ∂P - ∫ ω, φ (Y ω) ∂Q| ≤ C * B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hB : 2 ^ (m - 1) * (m + 1) ^ m * B ≤ δ ^ (m + 1)) (u : ℝ) :
    P.real {ω | X ω ≤ u} ≤ Q.real {ω | Y ω ≤ u + δ} + δ := by
  have key (η : ℝ) (hη : 0 < η) := measureReal_le_le_add_div_pow_of_forall_contDiff hX hY h u hη
  rcases hδ.eq_or_lt with rfl | hδ
  · rw [zero_pow m.succ_ne_zero] at hB
    rw [add_zero, add_zero]
    refine le_measureReal_le_of_forall_lt hY fun v hv => ?_
    have h0 : 2 ^ (m - 1) * (m + 1) ^ m * B / (v - u) ^ m ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hB (pow_nonneg (sub_pos.2 hv).le _)
    have := key _ (sub_pos.2 hv)
    rw [add_sub_cancel] at this
    linarith
  · refine (key δ hδ).trans (add_le_add le_rfl ?_)
    rw [div_le_iff₀ (pow_pos hδ m), ← pow_succ']
    exact hB

/-- **From `Cᵐ` tests to the Lévy distance**, lower bound: in the setting of
`measureReal_le_le_add_of_forall_contDiff`, `Pr[Y ≤ u - δ] - δ ≤ Pr[X ≤ u]` for every `u`
[O'Donnell, Corollary 11.61][ODonnell2014]. Together, the two bound the Lévy distance between
`X` and `Y` by `δ`. -/
theorem measureReal_le_sub_le_of_forall_contDiff (hX : AEMeasurable X P)
    (hY : AEMeasurable Y Q)
    (h : ∀ (φ : ℝ → ℝ) (C : ℝ), ContDiff ℝ m φ → (∀ s, |iteratedDeriv m φ s| ≤ C) →
      |∫ ω, φ (X ω) ∂P - ∫ ω, φ (Y ω) ∂Q| ≤ C * B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hB : 2 ^ (m - 1) * (m + 1) ^ m * B ≤ δ ^ (m + 1)) (u : ℝ) :
    Q.real {ω | Y ω ≤ u - δ} - δ ≤ P.real {ω | X ω ≤ u} := by
  have := measureReal_le_le_add_of_forall_contDiff hY hX
    (fun φ C hφ hC => (abs_sub_comm _ _).trans_le (h φ C hφ hC)) hδ hB (u - δ)
  rw [sub_add_cancel] at this
  linarith

end ProbabilityTheory
