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
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Topology.EMetricSpace.Lipschitz
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate
import CslibFrontier.Foundations.Probability.Gaussian.Real
import CslibFrontier.Foundations.Probability.LevyDistance
import CslibFrontier.Foundations.Probability.SmoothTests

/-!
# The Invariance Principle for sums of random variables

Let `X₁, …, Xₙ` and `Y₁, …, Yₙ` be independent real random variables in `L³` with laws `μ i` and
`ν i`, and with `E[Xᵢ] = E[Yᵢ]` and `E[Xᵢ²] = E[Yᵢ²]`. Write `S_X = ∑ Xᵢ`, `S_Y = ∑ Yᵢ` and
`γ_XY = ∑ (E|Xᵢ|³ + E|Yᵢ|³)`. The **Invariance Principle for Sums of Random Variables**
[O'Donnell, Section 11.5, Invariance Principle for Sums of Random Variables][ODonnell2014]
says that `|E[ψ(S_X)] - E[ψ(S_Y)]| ≤ ‖ψ'''‖∞ / 6 · γ_XY` for every `ψ` of class `C³`. Here the
vectors `X` and `Y` have the product laws `Measure.pi μ` and `Measure.pi ν`, and need not live on
one probability space.

The proof is the Replacement Method: `MeasureTheory.abs_integral_pi_sub_le_sum` telescopes over
the hybrids, and replacing coordinate `t` costs at most `C / 6 · (E|Xₜ|³ + E|Yₜ|³)` by the
second-order replacement step `ProbabilityTheory.abs_integral_sub_integral_le_of_moments`.
Smoothing Lipschitz tests by a three-fold moving average
(`ProbabilityTheory.abs_integral_comp_sub_le_of_lipschitzWith`) gives Corollary 11.59,
`|E[ψ(S_X)] - E[ψ(S_Y)]| ≤ 6 K γ_XY^(1/3)` for `K`-Lipschitz `ψ`. Smoothing the indicator of
`(-∞, u]` the same way (`ProbabilityTheory.measureReal_le_le_add_of_forall_contDiff`) gives
Corollary 11.61, a bound on the Lévy distance: `Pr[S_X ≤ u] ≤ Pr[S_Y ≤ u + ε] + ε` and
`Pr[S_Y ≤ u - ε] - ε ≤ Pr[S_X ≤ u]` with `ε = 3 γ_XY^(1/4)`. When `S_Y` is a standard Gaussian,
its anticoncentration gives Corollary 11.62 in the form with `γ_XY`,
`|Pr[S_X ≤ u] - Φ(u)| ≤ 9/2 · γ_XY^(1/4)`.

The tools come from `CslibFrontier.Foundations.Probability.SmoothTests` and
`CslibFrontier.Foundations.Probability.LevyDistance`.

Not proved here: the Berry–Esseen Theorem of Section 11.5, with the error `O(∑ E|Xᵢ|³)` instead
of `O(γ_XY^(1/4))`; and the Variant Berry–Esseen Theorem and the book's (`X`-only) form of
Corollary 11.62, which need `Yᵢ ∼ N(0, Var[Xᵢ])` and the bound
`γ_XY ≤ (1 + 2 √(2/π)) ∑ E|Xᵢ|³` of (11.28).

## Main results

* `ProbabilityTheory.abs_integral_comp_sum_sub_le`: the Invariance Principle for sums.
* `ProbabilityTheory.abs_integral_comp_sum_sub_le_of_lipschitzWith`: Corollary 11.59.
* `ProbabilityTheory.measureReal_sum_le_le_add_div_pow`: `Pr[S_X ≤ u]` is at most
  `Pr[S_Y ≤ u + η] + 128 γ_XY / (3 η³)` for every `η > 0`.
* `ProbabilityTheory.measureReal_sum_le_le_add`, `ProbabilityTheory.measureReal_sum_le_sub_le`:
  Corollary 11.61.
* `ProbabilityTheory.abs_measureReal_sum_le_sub_cdf_le`: Corollary 11.62, in the form with
  `γ_XY`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 11.5.
-/

public section

open MeasureTheory Finset Real
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- If every coordinate law is in `Lᵖ`, then the sum of the coordinates is in `Lᵖ` under the
product law. -/
private theorem memLp_sum_pi {p : ℝ≥0∞} (P : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (P i)]
    (hP : ∀ i, MemLp id p (P i)) : MemLp (fun z : ι → ℝ => ∑ i, z i) p (Measure.pi P) :=
  memLp_finsetSum (f := fun i (z : ι → ℝ) => z i) _ fun i _ =>
    (hP i).comp_measurePreserving (measurePreserving_eval P i)

/-- `γ_XY = ∑ᵢ (E|Xᵢ|³ + E|Yᵢ|³)` is nonnegative. -/
private theorem sum_integral_abs_pow_three_nonneg (μ ν : ι → Measure ℝ) :
    0 ≤ ∑ i, (∫ s, |s| ^ 3 ∂μ i + ∫ s, |s| ^ 3 ∂ν i) :=
  sum_nonneg fun _ _ => add_nonneg (integral_nonneg fun _ => by positivity)
    (integral_nonneg fun _ => by positivity)

variable (μ ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]

/-! ### The Invariance Principle for sums -/

/-- **The Invariance Principle for Sums of Random Variables**
[O'Donnell, Section 11.5, Invariance Principle for Sums of Random Variables][ODonnell2014]: let
`X` and `Y` be vectors of independent random variables with laws `μ i` and `ν i` in `L³`, with
`E[Xᵢ] = E[Yᵢ]` and `E[Xᵢ²] = E[Yᵢ²]`. If `ψ : ℝ → ℝ` is of class `C³` with `|ψ'''| ≤ C`, then
`|E[ψ(∑ Xᵢ)] - E[ψ(∑ Yᵢ)]| ≤ C / 6 · ∑ᵢ (E|Xᵢ|³ + E|Yᵢ|³)`. -/
theorem abs_integral_comp_sum_sub_le (hμ : ∀ i, MemLp id 3 (μ i)) (hν : ∀ i, MemLp id 3 (ν i))
    (h₁ : ∀ i, ∫ s, s ∂μ i = ∫ s, s ∂ν i) (h₂ : ∀ i, ∫ s, s ^ 2 ∂μ i = ∫ s, s ^ 2 ∂ν i)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 3 ψ) {C : ℝ} (hC : ∀ y, |iteratedDeriv 3 ψ y| ≤ C) :
    |∫ z, ψ (∑ i, z i) ∂Measure.pi μ - ∫ z, ψ (∑ i, z i) ∂Measure.pi ν| ≤
      C / 6 * ∑ i, (∫ s, |s| ^ 3 ∂μ i + ∫ s, |s| ^ 3 ∂ν i) := by
  classical
  have hint (s : Finset ι) :
      Integrable (fun z : ι → ℝ => ψ (∑ i, z i)) (Measure.pi (s.piecewise ν μ)) := by
    have := isProbabilityMeasure_piecewise μ ν s
    refine integrable_comp_of_memLp (n := 2) hψ hC (memLp_sum_pi _ fun i => ?_)
    by_cases h : i ∈ s
    · rw [Finset.piecewise_eq_of_mem _ _ _ h]; exact_mod_cast hν i
    · rw [Finset.piecewise_eq_of_notMem _ _ _ h]; exact_mod_cast hμ i
  rw [mul_sum]
  refine abs_integral_pi_sub_le_sum μ ν _ fun s t ht => ?_
  have := isProbabilityMeasure_piecewise μ ν s
  rw [integral_pi_piecewise_insert_sub μ ν ht hint, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (ae_of_all _ fun v => ?_)).trans_eq
    (by rw [probReal_univ, mul_one])
  have hsum (z : ℝ) : ∑ i, Function.update v t z i = ∑ i ∈ univ \ {t}, v i + z * 1 := by
    rw [sum_update_of_mem (mem_univ t), mul_one, add_comm]
  simp only [hsum, Real.norm_eq_abs]
  refine (abs_integral_sub_integral_le_of_moments (n := 2) (by exact_mod_cast hν t)
    (by exact_mod_cast hμ t) (fun j hj => ?_) hψ hC _ 1).trans_eq ?_
  · interval_cases j
    · simp
    · simpa using (h₁ t).symm
    · exact (h₂ t).symm
  · have h6 : ((2 + 1).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h6, abs_one, one_pow, mul_one, add_comm (∫ s, |s| ^ (2 + 1) ∂ν t)]

/-- The Invariance Principle for sums in the form used by the smoothing arguments: every `C³`
test `φ` with `|φ'''| ≤ C` satisfies `|E[φ(∑ Xᵢ)] - E[φ(∑ Yᵢ)]| ≤ C · γ_XY / 6`. -/
private theorem abs_integral_comp_sum_sub_le_mul_div_six (hμ : ∀ i, MemLp id 3 (μ i))
    (hν : ∀ i, MemLp id 3 (ν i)) (h₁ : ∀ i, ∫ s, s ∂μ i = ∫ s, s ∂ν i)
    (h₂ : ∀ i, ∫ s, s ^ 2 ∂μ i = ∫ s, s ^ 2 ∂ν i) (φ : ℝ → ℝ) (C : ℝ)
    (hφ : ContDiff ℝ (3 : ℕ) φ) (hC : ∀ y, |iteratedDeriv 3 φ y| ≤ C) :
    |∫ z, φ (∑ i, z i) ∂Measure.pi μ - ∫ z, φ (∑ i, z i) ∂Measure.pi ν| ≤
      C * ((∑ i, (∫ s, |s| ^ 3 ∂μ i + ∫ s, |s| ^ 3 ∂ν i)) / 6) :=
  (abs_integral_comp_sum_sub_le μ ν hμ hν h₁ h₂ hφ hC).trans_eq
    ((div_mul_eq_mul_div _ _ _).trans (mul_div_assoc _ _ _))

/-! ### Lipschitz tests: Corollary 11.59 -/

/-- **Corollary 11.59** [O'Donnell, Corollary 11.59][ODonnell2014]: in the setting of the
Invariance Principle for sums, if `ψ : ℝ → ℝ` is `K`-Lipschitz, then
`|E[ψ(∑ Xᵢ)] - E[ψ(∑ Yᵢ)]| ≤ 6 K · γ_XY^(1/3)` with `γ_XY = ∑ᵢ (E|Xᵢ|³ + E|Yᵢ|³)`. -/
theorem abs_integral_comp_sum_sub_le_of_lipschitzWith (hμ : ∀ i, MemLp id 3 (μ i))
    (hν : ∀ i, MemLp id 3 (ν i)) (h₁ : ∀ i, ∫ s, s ∂μ i = ∫ s, s ∂ν i)
    (h₂ : ∀ i, ∫ s, s ^ 2 ∂μ i = ∫ s, s ^ 2 ∂ν i) {ψ : ℝ → ℝ} {K : ℝ≥0}
    (hψ : LipschitzWith K ψ) :
    |∫ z, ψ (∑ i, z i) ∂Measure.pi μ - ∫ z, ψ (∑ i, z i) ∂Measure.pi ν| ≤
      6 * K * (∑ i, (∫ s, |s| ^ 3 ∂μ i + ∫ s, |s| ^ 3 ∂ν i)) ^ (1 / 3 : ℝ) := by
  set γ := ∑ i, (∫ s, |s| ^ 3 ∂μ i + ∫ s, |s| ^ 3 ∂ν i)
  have hγ : 0 ≤ γ := sum_integral_abs_pow_three_nonneg μ ν
  have h3 (P : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (P i)] (hP : ∀ i, MemLp id 3 (P i)) :
      MemLp (fun z : ι → ℝ => ∑ i, z i) (2 + 1 : ℕ) (Measure.pi P) := by
    exact_mod_cast memLp_sum_pi P hP
  refine (abs_integral_comp_sub_le_of_lipschitzWith (X := fun z : ι → ℝ => ∑ i, z i)
    (Y := fun z : ι → ℝ => ∑ i, z i) (m := 3) three_ne_zero (τ := 3 / 5 * γ ^ (1 / 3 : ℝ))
    (by positivity) (fun φ C hφ hC => ⟨integrable_comp_of_memLp (n := 2) hφ hC (h3 μ hμ),
      integrable_comp_of_memLp (n := 2) hφ hC (h3 ν hν), ?_⟩) hψ).trans_eq (by norm_num; ring)
  refine (abs_integral_comp_sum_sub_le μ ν hμ hν h₁ h₂ hφ hC).trans ?_
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have he : (γ ^ (1 / 3 : ℝ)) ^ 3 = γ := by
    simpa using Real.rpow_inv_natCast_pow hγ (n := 3) (by norm_num)
  rw [mul_pow, he]
  nlinarith [mul_nonneg hC0 hγ]

/-! ### The Lévy distance: Corollary 11.61 -/

/-- In the setting of the Invariance Principle for sums, for every `u` and `η > 0`,
`Pr[∑ Xᵢ ≤ u] ≤ Pr[∑ Yᵢ ≤ u + η] + 128 γ_XY / (3 η³)` with `γ_XY = ∑ᵢ (E|Xᵢ|³ + E|Yᵢ|³)`. This is
the main step of [O'Donnell, Corollary 11.61][ODonnell2014] (Exercise 11.42). -/
theorem measureReal_sum_le_le_add_div_pow (hμ : ∀ i, MemLp id 3 (μ i))
    (hν : ∀ i, MemLp id 3 (ν i)) (h₁ : ∀ i, ∫ s, s ∂μ i = ∫ s, s ∂ν i)
    (h₂ : ∀ i, ∫ s, s ^ 2 ∂μ i = ∫ s, s ^ 2 ∂ν i) (u : ℝ) {η : ℝ} (hη : 0 < η) :
    (Measure.pi μ).real {z | ∑ i, z i ≤ u} ≤ (Measure.pi ν).real {z | ∑ i, z i ≤ u + η} +
      128 / 3 * (∑ i, (∫ s, |s| ^ 3 ∂μ i + ∫ s, |s| ^ 3 ∂ν i)) / η ^ 3 := by
  refine (measureReal_le_le_add_div_pow_of_forall_contDiff (by fun_prop) (by fun_prop)
    (abs_integral_comp_sum_sub_le_mul_div_six μ ν hμ hν h₁ h₂) u hη).trans_eq ?_
  norm_num
  ring

/-- The arithmetic of Corollary 11.61: `2² · 4³ · γ / 6 ≤ (3 γ^(1/4))⁴` for `γ ≥ 0`. -/
private theorem pow_mul_div_six_le {γ : ℝ} (hγ : 0 ≤ γ) :
    2 ^ (3 - 1) * ((3 : ℕ) + 1 : ℝ) ^ 3 * (γ / 6) ≤ (3 * γ ^ (1 / 4 : ℝ)) ^ (3 + 1) := by
  have he : (γ ^ (1 / 4 : ℝ)) ^ 4 = γ := by
    simpa using Real.rpow_inv_natCast_pow hγ (n := 4) (by norm_num)
  rw [mul_pow, he]
  norm_num
  linarith

/-- **Corollary 11.61**, upper bound [O'Donnell, Corollary 11.61][ODonnell2014]: in the setting of
the Invariance Principle for sums, `Pr[∑ Xᵢ ≤ u] ≤ Pr[∑ Yᵢ ≤ u + ε] + ε` for every `u`, with
`ε = 3 γ_XY^(1/4)` and `γ_XY = ∑ᵢ (E|Xᵢ|³ + E|Yᵢ|³)`. -/
theorem measureReal_sum_le_le_add (hμ : ∀ i, MemLp id 3 (μ i)) (hν : ∀ i, MemLp id 3 (ν i))
    (h₁ : ∀ i, ∫ s, s ∂μ i = ∫ s, s ∂ν i) (h₂ : ∀ i, ∫ s, s ^ 2 ∂μ i = ∫ s, s ^ 2 ∂ν i)
    (u : ℝ) :
    (Measure.pi μ).real {z | ∑ i, z i ≤ u} ≤ (Measure.pi ν).real {z | ∑ i, z i ≤
      u + 3 * (∑ i, (∫ s, |s| ^ 3 ∂μ i + ∫ s, |s| ^ 3 ∂ν i)) ^ (1 / 4 : ℝ)} +
      3 * (∑ i, (∫ s, |s| ^ 3 ∂μ i + ∫ s, |s| ^ 3 ∂ν i)) ^ (1 / 4 : ℝ) :=
  have hγ := sum_integral_abs_pow_three_nonneg μ ν
  measureReal_le_le_add_of_forall_contDiff (by fun_prop) (by fun_prop)
    (abs_integral_comp_sum_sub_le_mul_div_six μ ν hμ hν h₁ h₂) (by positivity)
    (pow_mul_div_six_le hγ) u

/-- **Corollary 11.61**, lower bound [O'Donnell, Corollary 11.61][ODonnell2014]: in the setting of
the Invariance Principle for sums, `Pr[∑ Yᵢ ≤ u - ε] - ε ≤ Pr[∑ Xᵢ ≤ u]` for every `u`, with
`ε = 3 γ_XY^(1/4)` and `γ_XY = ∑ᵢ (E|Xᵢ|³ + E|Yᵢ|³)`. Together with
`measureReal_sum_le_le_add`, the Lévy distance between `∑ Xᵢ` and `∑ Yᵢ` is at most `ε`. -/
theorem measureReal_sum_le_sub_le (hμ : ∀ i, MemLp id 3 (μ i)) (hν : ∀ i, MemLp id 3 (ν i))
    (h₁ : ∀ i, ∫ s, s ∂μ i = ∫ s, s ∂ν i) (h₂ : ∀ i, ∫ s, s ^ 2 ∂μ i = ∫ s, s ^ 2 ∂ν i)
    (u : ℝ) :
    (Measure.pi ν).real {z | ∑ i, z i ≤
      u - 3 * (∑ i, (∫ s, |s| ^ 3 ∂μ i + ∫ s, |s| ^ 3 ∂ν i)) ^ (1 / 4 : ℝ)} -
      3 * (∑ i, (∫ s, |s| ^ 3 ∂μ i + ∫ s, |s| ^ 3 ∂ν i)) ^ (1 / 4 : ℝ) ≤
      (Measure.pi μ).real {z | ∑ i, z i ≤ u} :=
  have hγ := sum_integral_abs_pow_three_nonneg μ ν
  measureReal_le_sub_le_of_forall_contDiff (by fun_prop) (by fun_prop)
    (abs_integral_comp_sum_sub_le_mul_div_six μ ν hμ hν h₁ h₂) (by positivity)
    (pow_mul_div_six_le hγ) u

/-! ### Comparison with a Gaussian: Corollary 11.62 -/

/-- **Corollary 11.62**, in the form with `γ_XY` [O'Donnell, Corollary 11.62][ODonnell2014]: in
the setting of the Invariance Principle for sums, if `∑ Yᵢ` is a standard Gaussian, then
`|Pr[∑ Xᵢ ≤ u] - Φ(u)| ≤ 9/2 · γ_XY^(1/4)` for every `u`, where `Φ = cdf (gaussianReal 0 1)` and
`γ_XY = ∑ᵢ (E|Xᵢ|³ + E|Yᵢ|³)`. For instance, `Yᵢ` may be independent Gaussians with mean `E[Xᵢ]`
and variance `Var[Xᵢ]` when `∑ E[Xᵢ] = 0` and `∑ Var[Xᵢ] = 1`. The book's form, with only `X`
given and `γ = ∑ E|Xᵢ|³`, follows via (11.28), which is not formalized. -/
theorem abs_measureReal_sum_le_sub_cdf_le (hμ : ∀ i, MemLp id 3 (μ i))
    (hν : ∀ i, MemLp id 3 (ν i)) (h₁ : ∀ i, ∫ s, s ∂μ i = ∫ s, s ∂ν i)
    (h₂ : ∀ i, ∫ s, s ^ 2 ∂μ i = ∫ s, s ^ 2 ∂ν i)
    (hG : HasLaw (fun z : ι → ℝ => ∑ i, z i) (gaussianReal 0 1) (Measure.pi ν)) (u : ℝ) :
    |(Measure.pi μ).real {z | ∑ i, z i ≤ u} - cdf (gaussianReal 0 1) u| ≤
      9 / 2 * (∑ i, (∫ s, |s| ^ 3 ∂μ i + ∫ s, |s| ^ 3 ∂ν i)) ^ (1 / 4 : ℝ) := by
  have hΦ (v : ℝ) : (Measure.pi ν).real {z | ∑ i, z i ≤ v} = cdf (gaussianReal 0 1) v := by
    rw [cdf_eq_real, ← hG.map_eq, map_measureReal_apply (by fun_prop) measurableSet_Iic]
    rfl
  have hanti (v : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
      cdf (gaussianReal 0 1) (v + ε) ≤ cdf (gaussianReal 0 1) v + ε / 2 := by
    have h2 : 2 ≤ √(2 * π * ((1 : ℝ≥0) : ℝ)) := by
      rw [NNReal.coe_one, mul_one]
      exact Real.le_sqrt_of_sq_le (by nlinarith [Real.two_le_pi])
    rw [cdf_eq_real, cdf_eq_real]
    exact (gaussianReal_real_Iic_add_le 0 v one_ne_zero hε).trans
      (add_le_add le_rfl (div_le_div_of_nonneg_left hε two_pos h2))
  set ε := 3 * (∑ i, (∫ s, |s| ^ 3 ∂μ i + ∫ s, |s| ^ 3 ∂ν i)) ^ (1 / 4 : ℝ) with hε
  have hε0 : 0 ≤ ε := by
    have := sum_integral_abs_pow_three_nonneg μ ν
    positivity
  have hup := measureReal_sum_le_le_add μ ν hμ hν h₁ h₂ u
  have hlo := measureReal_sum_le_sub_le μ ν hμ hν h₁ h₂ u
  rw [← hε, hΦ] at hup hlo
  have ha := hanti u hε0
  have hb := hanti (u - ε) hε0
  rw [sub_add_cancel] at hb
  rw [abs_sub_le_iff]
  constructor <;> linarith

end ProbabilityTheory
