/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, `Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`)

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Weak convergence and functions of at most linear growth

Weak convergence of probability measures on `ℝ` gives convergence of `∫ g` for bounded continuous
`g` only. If the second moments are bounded uniformly, it also gives convergence of `∫ h` for a
continuous `h` of at most linear growth, `h(z)² ≤ a z² + b`
(`MeasureTheory.ProbabilityMeasure.tendsto_integral_of_integral_sq_le`). Clamping `h` to
`[-M, M]` changes each integral by at most `(max a 0 · C + b) / M`, where `C` bounds the second
moments, since `|h - clamp h| ≤ h² / M`; this is uniform integrability of `h` from the second
moments. The clamping estimate holds on any measurable space, for `h² ≤ a Φ + b` with a weight
`Φ ≥ 0` whose integral is at most `C`
(`MeasureTheory.abs_integral_sub_integral_max_neg_min_le`); here `Φ z = z²`.

## Main results

* `abs_sub_max_neg_min_le_sq_div`, `MeasureTheory.abs_integral_sub_integral_max_neg_min_le`:
  clamping to `[-M, M]` moves a number by at most its square over `M`, and the integral of a
  function `h` with `h² ≤ a Φ + b` by at most `(max a 0 · C + b) / M`, where `C` bounds `∫ Φ`.
* `MeasureTheory.ProbabilityMeasure.tendsto_integral_of_integral_sq_le`: weak convergence with
  bounded second moments gives convergence of integrals of continuous functions of at most
  linear growth.
-/

public section

open Filter Topology
open scoped BoundedContinuousFunction

/-- Clamping to `[-M, M]` moves a number by at most its square over `M`. -/
theorem abs_sub_max_neg_min_le_sq_div {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {M : α} (hM : 0 < M) (x : α) :
    |x - max (-M) (min x M)| ≤ x ^ 2 / M := by
  rw [le_div_iff₀ hM]
  rcases le_total x M with hx | hx
  · rcases le_total x (-M) with hx' | hx'
    · rw [min_eq_left hx, max_eq_left hx', abs_of_nonpos (by linarith)]; nlinarith
    · rw [min_eq_left hx, max_eq_right hx', sub_self, abs_zero, zero_mul]; positivity
  · rw [min_eq_right hx, max_eq_right (by linarith), abs_of_nonneg (by linarith)]; nlinarith

namespace MeasureTheory

/-- For `h` with `h² ≤ a Φ + b` and a probability measure under which `Φ ≥ 0` has integral at
most `C`, clamping `h` to `[-M, M]` changes its integral by at most `(max a 0 · C + b) / M`. -/
theorem abs_integral_sub_integral_max_neg_min_le {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {Φ : Ω → ℝ} (hΦ0 : ∀ z, 0 ≤ Φ z) (hΦ : Integrable Φ ν) {C : ℝ}
    (hC : ∫ z, Φ z ∂ν ≤ C) {h : Ω → ℝ} (hc : AEStronglyMeasurable h ν) {a b : ℝ}
    (hab : ∀ z, h z ^ 2 ≤ a * Φ z + b) {M : ℝ} (hM : 0 < M) :
    |∫ z, h z ∂ν - ∫ z, max (-M) (min (h z) M) ∂ν| ≤ (max a 0 * C + b) / M := by
  have hquad : Integrable (fun z => max a 0 * Φ z + b) ν :=
    (hΦ.const_mul _).add (integrable_const b)
  have hab' (z : Ω) : h z ^ 2 ≤ max a 0 * Φ z + b :=
    (hab z).trans (by gcongr; exacts [hΦ0 z, le_max_left _ _])
  have hint : Integrable h ν := by
    refine MemLp.integrable one_le_two ((memLp_two_iff_integrable_sq hc).2
      (hquad.mono' (hc.pow 2) (ae_of_all _ fun z => ?_)))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hab' z
  have hclamp : Integrable (fun z => max (-M) (min (h z) M)) ν :=
    (integrable_const M).mono' (by fun_prop) (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩)
  rw [← integral_sub hint hclamp]
  calc |∫ z, (h z - max (-M) (min (h z) M)) ∂ν|
      ≤ ∫ z, |h z - max (-M) (min (h z) M)| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ z, (max a 0 * Φ z + b) / M ∂ν :=
        integral_mono (hint.sub hclamp).abs (hquad.div_const M) fun z =>
          (abs_sub_max_neg_min_le_sq_div hM _).trans (by gcongr; exact hab' z)
    _ ≤ (max a 0 * C + b) / M := by
        rw [integral_div, integral_add (hΦ.const_mul _) (integrable_const b), integral_const_mul]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        gcongr

namespace ProbabilityMeasure

/-- **Weak convergence with bounded second moments.** If probability measures `μs i` on `ℝ`
converge weakly to `μ`, and `μ` and every `μs i` have second moment at most `C`, then
`∫ h ∂μs i → ∫ h ∂μ` for every continuous `h` of at most linear growth, `h(z)² ≤ a z² + b`. -/
theorem tendsto_integral_of_integral_sq_le {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} (hμ : Tendsto μs l (𝓝 μ)) {C : ℝ}
    (hsq : ∀ i, Integrable (fun z => z ^ 2) (μs i : Measure ℝ))
    (hC : ∀ i, ∫ z, z ^ 2 ∂(μs i : Measure ℝ) ≤ C)
    (hsq' : Integrable (fun z => z ^ 2) (μ : Measure ℝ)) (hC' : ∫ z, z ^ 2 ∂(μ : Measure ℝ) ≤ C)
    {h : ℝ → ℝ} (hc : Continuous h) {a b : ℝ} (hab : ∀ z, h z ^ 2 ≤ a * z ^ 2 + b) :
    Tendsto (fun i => ∫ z, h z ∂(μs i : Measure ℝ)) l (𝓝 (∫ z, h z ∂(μ : Measure ℝ))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Clamp at a height `M` with `(max a 0 * C + b) / M < ε / 3`.
  set D := max a 0 * C + b
  set M := 3 * (|D| + 1) / ε
  have hM : 0 < M := by positivity
  have hδ : D / M < ε / 3 := by
    rw [div_lt_iff₀ hM, show ε / 3 * M = |D| + 1 by simp only [M]; field_simp]
    linarith [le_abs_self D]
  let g : ℝ →ᵇ ℝ := .mkOfBound ⟨fun z => max (-M) (min (h z) M), by fun_prop⟩ (2 * M)
    fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq, abs_le]
      constructor <;> linarith [min_le_right (h x) M, min_le_right (h y) M,
        le_max_left (-M) (min (h x) M), le_max_left (-M) (min (h y) M),
        max_le (by linarith : -M ≤ M) (min_le_right (h x) M),
        max_le (by linarith : -M ≤ M) (min_le_right (h y) M)]
  have hg := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hμ g).eventually
    (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 3))
  filter_upwards [hg] with i hi
  have h1 := abs_integral_sub_integral_max_neg_min_le (Φ := (· ^ 2)) sq_nonneg (hsq i) (hC i)
    hc.aestronglyMeasurable hab hM
  have h2 := abs_integral_sub_integral_max_neg_min_le (Φ := (· ^ 2)) sq_nonneg hsq' hC'
    hc.aestronglyMeasurable hab hM
  rw [Real.dist_eq] at hi ⊢
  change |∫ z, max (-M) (min (h z) M) ∂(μs i : Measure ℝ) -
    ∫ z, max (-M) (min (h z) M) ∂(μ : Measure ℝ)| < _ at hi
  rw [abs_le] at h1 h2
  rw [abs_lt] at hi ⊢
  constructor <;> linarith

end ProbabilityMeasure

end MeasureTheory
