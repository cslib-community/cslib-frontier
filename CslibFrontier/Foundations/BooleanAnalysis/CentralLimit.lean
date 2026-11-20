/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
import CslibFrontier.Foundations.BooleanAnalysis.Invariance
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.MeasureTheory.Measure.WeakConvergenceMoments
import CslibFrontier.Foundations.Probability.Gaussian.Moments
import CslibFrontier.Probability.BitString.Rademacher
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.InfinitePi

/-!
# The central limit theorem on the cube

For a uniformly random `x : Fin n → Bool`, read as signs `xᵢ = signVal (x i)`, the normalized sum
`Zₙ = ∑ᵢ xᵢ / √n` converges in distribution to a standard Gaussian `Z`. This is Mathlib's central
limit theorem (`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`) for a sequence of
independent uniform signs under `Measure.infinitePi`, carried to the cube by
`integral_pi_rademacher`. It is stated here as convergence of expectations on the cube:

* for bounded continuous `g`, `E[g(Zₙ)] → E[g(Z)]`
  (`tendsto_expect_inv_sqrt_mul_sum_signVal`);
* for the indicator of a measurable set whose frontier is Gaussian-null, by the portmanteau theorem
  (`tendsto_expect_indicator_inv_sqrt_mul_sum_signVal`);
* for continuous `h` of at most linear growth, `h(z)² ≤ a z² + b`, since `E[Zₙ²] ≤ 1`
  (`tendsto_expect_inv_sqrt_mul_sum_signVal_of_sq_le`, through
  `MeasureTheory.ProbabilityMeasure.tendsto_integral_of_integral_sq_le`).

In particular `E[|Zₙ|] → E[|Z|] = √(2 / π)` (`tendsto_expect_abs_inv_sqrt_mul_sum_signVal`), the
estimate (5.4) of [O'Donnell, Section 5.2][ODonnell2014] behind `I[Majₙ] ∼ √(2 / π) √n`.

## Main results

* `Cslib.BitString.tendsto_expect_inv_sqrt_mul_sum_signVal`,
  `Cslib.BitString.tendsto_expect_indicator_inv_sqrt_mul_sum_signVal`,
  `Cslib.BitString.tendsto_expect_inv_sqrt_mul_sum_signVal_of_sq_le`: the central limit theorem on
  the cube for bounded continuous functions, events and functions of at most linear growth.
* `Cslib.BitString.tendsto_expect_abs_inv_sqrt_mul_sum_signVal`: `E[|∑ᵢ xᵢ / √n|] → √(2 / π)`.

## Usage

The statements match an expectation written exactly as
`𝔼 x : Fin n → Bool, g ((√n)⁻¹ * ∑ i, signVal (x i))`, with `n` cast to `ℝ`; for another finite
index type, reindex to `Fin n` first, for example with `Fintype.expect_comp_arrowCongr`. The
form for functions of at most linear growth admits unbounded `h` of either sign; the second
moments it uses are `expect_sq_inv_sqrt_card_mul_sum_signVal_le`. The checked clients in
[CslibFrontierTests/BooleanAnalysisHammingBallWeight.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisHammingBallWeight.lean)
apply it to `z - |z|`, which is unbounded below, and derive that `E[|∑ᵢ xᵢ / √n|]` is eventually
below `1`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 5.2.
-/

public section

open MeasureTheory ProbabilityTheory Finset Filter Topology Real
open scoped BigOperators BoundedContinuousFunction

namespace Cslib.BitString

/-- The product of countably many uniform random signs. -/
private noncomputable abbrev signSeq : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => rademacher

/-- The normalized partial sums of the sign sequence have the laws of the normalized sign sums on
the cube. -/
private theorem integral_signSeq (g : ℝ → ℝ) (hg : Measurable g) (n : ℕ) :
    ∫ ω, g ((√n)⁻¹ * ∑ k ∈ range n, ω k) ∂signSeq =
      𝔼 x : Fin n → Bool, g ((√n)⁻¹ * ∑ i, signVal (x i)) := by
  have h := integral_map (μ := signSeq) (measurable_restrict (range n)).aemeasurable
    (f := fun z : range n → ℝ => g ((√n)⁻¹ * ∑ i, z i))
    (hg.comp (by fun_prop)).aestronglyMeasurable
  rw [Measure.infinitePi_map_restrict, integral_pi_rademacher] at h
  have he : range n ≃ Fin n := Fintype.equivFinOfCardEq (by simp)
  have hsum (x : range n → Bool) : ∑ j, signVal (x (he.symm j)) = ∑ i, signVal (x i) :=
    he.symm.sum_comp fun i => signVal (x i)
  rw [← Fintype.expect_comp_arrowCongr he]
  simp only [hsum]
  refine (integral_congr_ae (ae_of_all _ fun ω => ?_)).trans h.symm
  rw [← Finset.sum_coe_sort]
  rfl

/-- **The central limit theorem for the sign sequence.** -/
private theorem tendstoInDistribution_signSeq :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√n)⁻¹ * ∑ k ∈ range n, ω k) atTop id
      (fun _ ↦ signSeq) (gaussianReal 0 1) := by
  have hmap (k : ℕ) : signSeq.map (fun ω => ω k) = rademacher := Measure.infinitePi_map_eval _ k
  have hint {g : ℝ → ℝ} (hg : Measurable g) : ∫ ω, g (ω 0) ∂signSeq = (g 1 + g (-1)) / 2 := by
    rw [← integral_rademacher, ← hmap 0, integral_map (measurable_pi_apply 0).aemeasurable
      hg.aestronglyMeasurable]
  refine tendstoInDistribution_inv_sqrt_mul_sum (X := fun (k : ℕ) (ω : ℕ → ℝ) => ω k) HasLaw.id
    ?_ ?_ (iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id) fun k => ?_
  · rw [hint (g := fun s => s) (by fun_prop)]; norm_num
  · simp only [Pi.pow_apply]; rw [hint (g := fun s => s ^ 2) (by fun_prop)]; norm_num
  · exact ⟨(measurable_pi_apply k).aemeasurable, (measurable_pi_apply 0).aemeasurable,
      by rw [hmap, hmap]⟩

/-- **The central limit theorem on the cube.** For a bounded continuous `g`, the expectation of
`g (∑ᵢ xᵢ / √n)` at a uniform `x ∈ {-1, 1}ⁿ` tends to `E[g(Z)]` for a standard Gaussian `Z`. -/
theorem tendsto_expect_inv_sqrt_mul_sum_signVal (g : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => 𝔼 x : Fin n → Bool, g ((√n)⁻¹ * ∑ i, signVal (x i))) atTop
      (𝓝 (∫ z, g z ∂gaussianReal 0 1)) := by
  have h := tendstoInDistribution_signSeq
  have := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ h.forall_aemeasurable
    h.aemeasurable_limit).1 h g
  exact this.congr fun n => integral_signSeq g g.continuous.measurable n

/-- **The central limit theorem on the cube, for events.** For a measurable `E` whose frontier is
null for the standard Gaussian, `Pr_x[∑ᵢ xᵢ / √n ∈ E]` tends to `Pr[Z ∈ E]`. -/
theorem tendsto_expect_indicator_inv_sqrt_mul_sum_signVal {E : Set ℝ} (hE : MeasurableSet E)
    (h0 : gaussianReal 0 1 (frontier E) = 0) :
    Tendsto (fun n : ℕ => 𝔼 x : Fin n → Bool, E.indicator 1 ((√n)⁻¹ * ∑ i, signVal (x i)))
      atTop (𝓝 ((gaussianReal 0 1).real E)) := by
  have h := tendstoInDistribution_signSeq
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h.tendsto (E := E)
    (by simpa using h0)
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at key
  refine ((ENNReal.tendsto_toReal (measure_ne_top _ E)).comp key).congr fun n => ?_
  rw [Function.comp_apply, ← measureReal_def, ← integral_indicator_one hE,
    integral_map (f := E.indicator 1) (h.forall_aemeasurable n)
    (measurable_const.indicator hE).aestronglyMeasurable]
  exact integral_signSeq _ (measurable_const.indicator hE) n

/-- A coordinate of the sign sequence has a finite second moment. -/
private theorem memLp_two_signSeq (k : ℕ) : MemLp (fun ω : ℕ → ℝ => ω k) 2 signSeq := by
  have h := hasInvarianceMoments_rademacher.memLp_four.mono_exponent (p := 2) (by norm_num)
  rw [← Measure.infinitePi_map_eval (fun _ : ℕ => rademacher) k] at h
  exact (memLp_map_measure_iff aestronglyMeasurable_id (measurable_pi_apply k).aemeasurable).1 h

/-- **The central limit theorem on the cube, for functions of at most linear growth.** For a
continuous `h` with `h(z)² ≤ a z² + b`, the expectation of `h (∑ᵢ xᵢ / √n)` at a uniform
`x ∈ {-1, 1}ⁿ` tends to `E[h(Z)]` for a standard Gaussian `Z`. The second moments are at most one,
which makes `h` uniformly integrable. -/
theorem tendsto_expect_inv_sqrt_mul_sum_signVal_of_sq_le {h : ℝ → ℝ} (hc : Continuous h)
    {a b : ℝ} (hab : ∀ z, h z ^ 2 ≤ a * z ^ 2 + b) :
    Tendsto (fun n : ℕ => 𝔼 x : Fin n → Bool, h ((√n)⁻¹ * ∑ i, signVal (x i))) atTop
      (𝓝 (∫ z, h z ∂gaussianReal 0 1)) := by
  have hT := tendstoInDistribution_signSeq
  have hmem (n : ℕ) : MemLp (fun ω : ℕ → ℝ => (√n)⁻¹ * ∑ k ∈ range n, ω k) 2 signSeq :=
    (memLp_finsetSum (range n) fun k _ => memLp_two_signSeq k).const_mul _
  have hint (n : ℕ) :
      Integrable (fun z : ℝ => z ^ 2) (signSeq.map fun ω => (√n)⁻¹ * ∑ k ∈ range n, ω k) := by
    rw [integrable_map_measure (by fun_prop) (hT.forall_aemeasurable n)]
    exact (hmem n).integrable_sq
  have hlaw {g : ℝ → ℝ} (hg : Continuous g) (n : ℕ) :
      ∫ z, g z ∂(signSeq.map fun ω => (√n)⁻¹ * ∑ k ∈ range n, ω k) =
        𝔼 x : Fin n → Bool, g ((√n)⁻¹ * ∑ i, signVal (x i)) := by
    rw [integral_map (hT.forall_aemeasurable n) hg.aestronglyMeasurable]
    exact integral_signSeq g hg.measurable n
  have := ProbabilityMeasure.tendsto_integral_of_integral_sq_le hT.tendsto (C := 1) hint
    (fun n => (hlaw (continuous_pow 2) n).trans_le <| by
      simpa only [Fintype.card_fin] using expect_sq_inv_sqrt_card_mul_sum_signVal_le (ι := Fin n))
    (by simpa using (memLp_id_gaussianReal 2).integrable_sq)
    (by simp [integral_sq_gaussianReal]) hc hab
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at this
  exact this.congr fun n => hlaw hc n

/-- The mean absolute value of the normalized sign sum tends to that of a standard Gaussian,
`E[|∑ᵢ xᵢ / √n|] → E[|Z|] = √(2 / π)` [O'Donnell, Section 5.2, equation (5.4)][ODonnell2014]. -/
theorem tendsto_expect_abs_inv_sqrt_mul_sum_signVal :
    Tendsto (fun n : ℕ => 𝔼 x : Fin n → Bool, |(√n)⁻¹ * ∑ i, signVal (x i)|) atTop
      (𝓝 √(2 / π)) := by
  rw [← integral_abs_gaussianReal]
  exact tendsto_expect_inv_sqrt_mul_sum_signVal_of_sq_le continuous_abs (a := 1) (b := 0)
    fun z => by simp [sq_abs]

end Cslib.BitString
