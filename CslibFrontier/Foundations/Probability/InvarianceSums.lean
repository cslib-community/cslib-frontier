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
import CslibFrontier.Foundations.MeasureTheory.Integral.CauchySchwarz
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate
import CslibFrontier.Foundations.Probability.Gaussian.Moments
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
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
its anticoncentration gives `|Pr[S_X ≤ u] - Φ(u)| ≤ 9/2 · γ_XY^(1/4)`. Corollary 11.62 is the
Berry–Esseen setting, where only `X` is given, with `E[Xᵢ] = 0` and `∑ Var[Xᵢ] = 1`: as in the
book, take independent `Yᵢ ∼ N(0, Var[Xᵢ])`, so that `S_Y` is a standard Gaussian, and bound
`γ_XY ≤ 3 γ` with `γ = ∑ E|Xᵢ|³` as in (11.28), giving `|Pr[S_X ≤ u] - Φ(u)| ≤ 6 γ^(1/4)`. The
book's bound `E|Yᵢ|³ ≤ 2 √(2/π) E|Xᵢ|³` is replaced by `E|Yᵢ|³ ≤ 2 E|Xᵢ|³`, from
`ProbabilityTheory.integral_abs_pow_three_gaussianReal_le` and Lyapunov's inequality
`MeasureTheory.sqrt_integral_sq_pow_three_le`.

The tools come from `CslibFrontier.Foundations.Probability.SmoothTests` and
`CslibFrontier.Foundations.Probability.LevyDistance`.

Not proved here: the Berry–Esseen Theorem of Section 11.5, with the error `O(∑ E|Xᵢ|³)` instead
of `O(γ^(1/4))`; and the Variant Berry–Esseen Theorem, which compares `E[ψ(S_X)]` with
`E[ψ(Z)]` for `C³` tests.

## Main results

* `ProbabilityTheory.abs_integral_comp_sum_sub_le`: the Invariance Principle for sums.
* `ProbabilityTheory.abs_integral_comp_sum_sub_le_of_lipschitzWith`: Corollary 11.59.
* `ProbabilityTheory.measureReal_sum_le_le_add_div_pow`: `Pr[S_X ≤ u]` is at most
  `Pr[S_Y ≤ u + η] + 128 γ_XY / (3 η³)` for every `η > 0`.
* `ProbabilityTheory.measureReal_sum_le_le_add`, `ProbabilityTheory.measureReal_sum_le_sub_le`:
  Corollary 11.61.
* `ProbabilityTheory.abs_measureReal_sum_le_sub_cdf_le_of_hasLaw`: `|Pr[S_X ≤ u] - Φ(u)|` is at
  most `9/2 · γ_XY^(1/4)` when `S_Y` is a standard Gaussian.
* `ProbabilityTheory.abs_measureReal_sum_le_sub_cdf_le`: Corollary 11.62.

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
  · interval_cases j <;> simp [(h₁ t).symm, (h₂ t).symm]
  · have h6 : (Nat.factorial (2 + 1) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h6, abs_one, one_pow, mul_one, add_comm (∫ s, |s| ^ (2 + 1) ∂ν t)]

/-- The Invariance Principle for sums in the form used by the smoothing arguments: every `C³`
test `φ` with `|φ'''| ≤ C` satisfies `|E[φ(∑ Xᵢ)] - E[φ(∑ Yᵢ)]| ≤ C · γ_XY / 6`. -/
private theorem abs_integral_comp_sum_sub_le_mul_div_six (hμ : ∀ i, MemLp id 3 (μ i))
    (hν : ∀ i, MemLp id 3 (ν i)) (h₁ : ∀ i, ∫ s, s ∂μ i = ∫ s, s ∂ν i)
    (h₂ : ∀ i, ∫ s, s ^ 2 ∂μ i = ∫ s, s ^ 2 ∂ν i) (φ : ℝ → ℝ) (C : ℝ)
    (hφ : ContDiff ℝ (3 : ℕ) φ) (hC : ∀ y, |iteratedDeriv 3 φ y| ≤ C) :
    |∫ z, φ (∑ i, z i) ∂Measure.pi μ - ∫ z, φ (∑ i, z i) ∂Measure.pi ν| ≤
      C * ((∑ i, (∫ s, |s| ^ 3 ∂μ i + ∫ s, |s| ^ 3 ∂ν i)) / 6) :=
  (abs_integral_comp_sum_sub_le μ ν hμ hν h₁ h₂ hφ hC).trans_eq (by ring)

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
      integrable_comp_of_memLp (n := 2) hφ hC (h3 ν hν),
      (abs_integral_comp_sum_sub_le μ ν hμ hν h₁ h₂ hφ hC).trans ?_⟩) hψ).trans_eq (by ring)
  have he : (γ ^ (1 / 3 : ℝ)) ^ 3 = γ := by
    simpa using Real.rpow_inv_natCast_pow hγ (n := 3) (by norm_num)
  rw [mul_pow, he]; nlinarith [mul_nonneg ((abs_nonneg _).trans (hC 0)) hγ]

/-! ### The Lévy distance: Corollary 11.61 -/

/-- In the setting of the Invariance Principle for sums, for every `u` and `η > 0`,
`Pr[∑ Xᵢ ≤ u] ≤ Pr[∑ Yᵢ ≤ u + η] + 128 γ_XY / (3 η³)` with `γ_XY = ∑ᵢ (E|Xᵢ|³ + E|Yᵢ|³)`. This is
the main step of [O'Donnell, Corollary 11.61][ODonnell2014] (Exercise 11.42). -/
theorem measureReal_sum_le_le_add_div_pow (hμ : ∀ i, MemLp id 3 (μ i))
    (hν : ∀ i, MemLp id 3 (ν i)) (h₁ : ∀ i, ∫ s, s ∂μ i = ∫ s, s ∂ν i)
    (h₂ : ∀ i, ∫ s, s ^ 2 ∂μ i = ∫ s, s ^ 2 ∂ν i) (u : ℝ) {η : ℝ} (hη : 0 < η) :
    (Measure.pi μ).real {z | ∑ i, z i ≤ u} ≤ (Measure.pi ν).real {z | ∑ i, z i ≤ u + η} +
      128 / 3 * (∑ i, (∫ s, |s| ^ 3 ∂μ i + ∫ s, |s| ^ 3 ∂ν i)) / η ^ 3 :=
  (measureReal_le_le_add_div_pow_of_forall_contDiff (by fun_prop) (by fun_prop)
    (abs_integral_comp_sum_sub_le_mul_div_six μ ν hμ hν h₁ h₂) u hη).trans_eq (by ring)

/-- The arithmetic of Corollary 11.61: `2² · 4³ · γ / 6 ≤ (3 γ^(1/4))⁴` for `γ ≥ 0`. -/
private theorem pow_mul_div_six_le {γ : ℝ} (hγ : 0 ≤ γ) :
    2 ^ (3 - 1) * ((3 : ℕ) + 1 : ℝ) ^ 3 * (γ / 6) ≤ (3 * γ ^ (1 / 4 : ℝ)) ^ (3 + 1) := by
  have he : (γ ^ (1 / 4 : ℝ)) ^ (3 + 1) = γ := by
    simpa using Real.rpow_inv_natCast_pow hγ (n := 4) (by norm_num)
  rw [mul_pow, he]; linarith

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

/-- A step of [O'Donnell, Corollary 11.62][ODonnell2014], not the corollary itself (which is
`abs_measureReal_sum_le_sub_cdf_le`): in the setting of the Invariance Principle for sums, if
`∑ Yᵢ` is a standard Gaussian, then `|Pr[∑ Xᵢ ≤ u] - Φ(u)| ≤ 9/2 · γ_XY^(1/4)` for every `u`,
where `Φ = cdf (gaussianReal 0 1)` and `γ_XY = ∑ᵢ (E|Xᵢ|³ + E|Yᵢ|³)`. -/
theorem abs_measureReal_sum_le_sub_cdf_le_of_hasLaw (hμ : ∀ i, MemLp id 3 (μ i))
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
  have hε0 : 0 ≤ ε :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (sum_integral_abs_pow_three_nonneg μ ν) _)
  have hup := measureReal_sum_le_le_add μ ν hμ hν h₁ h₂ u
  have hlo := measureReal_sum_le_sub_le μ ν hμ hν h₁ h₂ u
  rw [← hε, hΦ] at hup hlo
  have hb := sub_add_cancel u ε ▸ hanti (u - ε) hε0
  rw [abs_sub_le_iff]
  constructor <;> linarith [hanti u hε0]

/-! ### The Gaussian comparison family -/

/-- The law of `σ g` for a standard Gaussian `g` is in `L³`. -/
private theorem memLp_map_gaussianReal_const_mul (σ : ℝ) :
    MemLp id 3 ((gaussianReal 0 1).map (σ * ·)) :=
  (memLp_map_measure_iff aestronglyMeasurable_id (measurable_const_mul σ).aemeasurable).2
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 3).const_mul σ)

/-- The integral of a continuous `g` against the law of `σ z` is the integral of `g (σ z)`. -/
private theorem integral_map_gaussianReal_const_mul (σ : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ s, g s ∂(gaussianReal 0 1).map (σ * ·) = ∫ s, g (σ * s) ∂gaussianReal 0 1 :=
  integral_map (measurable_const_mul σ).aemeasurable hg.aestronglyMeasurable

/-- If the `σ i` have `∑ σᵢ² = 1`, then the sum of independent `Yᵢ ∼ σᵢ · N(0, 1)` is a standard
Gaussian. -/
private theorem hasLaw_sum_pi_map_gaussianReal {σ : ι → ℝ} (hσ : ∑ i, σ i ^ 2 = 1) :
    HasLaw (fun z : ι → ℝ => ∑ i, z i) (gaussianReal 0 1)
      (Measure.pi fun i => (gaussianReal 0 1).map (σ i * ·)) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← Measure.pi_map_pi fun i => (measurable_const_mul (σ i)).aemeasurable,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have he : ((fun z : ι → ℝ => ∑ i, z i) ∘ fun z i => σ i * z i) = (σ ⬝ᵥ ·) :=
    funext fun _ => by simp [dotProduct]
  have hσσ : σ ⬝ᵥ σ = 1 := by simpa [dotProduct, sq] using hσ
  simp [he, pi_gaussianReal_map_dotProduct_eq_map_const_mul, hσσ]

/-- `9/2 · a^(1/4) ≤ 6 γ^(1/4)` when `0 ≤ a ≤ 3 γ`, as `3^(1/4) ≤ 4/3`. -/
private theorem nine_div_two_mul_rpow_le {a γ : ℝ} (ha : 0 ≤ a) (h : a ≤ 3 * γ) :
    9 / 2 * a ^ (1 / 4 : ℝ) ≤ 6 * γ ^ (1 / 4 : ℝ) := by
  have hγ : 0 ≤ γ := by linarith
  have h4 : (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
  have h3 : (3 : ℝ) ^ (1 / 4 : ℝ) ≤ 4 / 3 :=
    h4.symm ▸ (Real.rpow_le_rpow zero_le_three (by norm_num : (3 : ℝ) ≤ (4 / 3) ^ 4)
      (inv_nonneg.2 (Nat.cast_nonneg 4))).trans_eq
      (Real.pow_rpow_inv_natCast (by positivity) (Nat.succ_ne_zero 3))
  calc 9 / 2 * a ^ (1 / 4 : ℝ) ≤ 9 / 2 * (3 * γ) ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha h (by norm_num)) (by norm_num)
    _ = 9 / 2 * 3 ^ (1 / 4 : ℝ) * γ ^ (1 / 4 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hγ, mul_assoc]
    _ ≤ 9 / 2 * (4 / 3) * γ ^ (1 / 4 : ℝ) := by gcongr
    _ = 6 * γ ^ (1 / 4 : ℝ) := by norm_num

/-- **Corollary 11.62** [O'Donnell, Corollary 11.62][ODonnell2014]: in the setting of the
Berry–Esseen Theorem, let `X₁, …, Xₙ` be independent real random variables with laws `μ i` in
`L³`, with `E[Xᵢ] = 0` and `∑ᵢ Var[Xᵢ] = ∑ᵢ E[Xᵢ²] = 1`, and let `γ = ∑ᵢ E|Xᵢ|³`. Then
`|Pr[∑ Xᵢ ≤ u] - Φ(u)| ≤ 6 γ^(1/4)` for every `u`, where `Φ = cdf (gaussianReal 0 1)`. The book
hides the constant in `O(γ^(1/4))`.

The proof follows the book: it compares `X` with independent `Yᵢ ∼ N(0, Var[Xᵢ])`, whose sum is
a standard Gaussian (`abs_measureReal_sum_le_sub_cdf_le_of_hasLaw`), and bounds
`γ_XY ≤ 3 γ` as in (11.28), using `E|Yᵢ|³ ≤ 2 Var[Xᵢ]^(3/2) ≤ 2 E|Xᵢ|³`. -/
theorem abs_measureReal_sum_le_sub_cdf_le (hμ : ∀ i, MemLp id 3 (μ i))
    (h₁ : ∀ i, ∫ s, s ∂μ i = 0) (h₂ : ∑ i, ∫ s, s ^ 2 ∂μ i = 1) (u : ℝ) :
    |(Measure.pi μ).real {z | ∑ i, z i ≤ u} - cdf (gaussianReal 0 1) u| ≤
      6 * (∑ i, ∫ s, |s| ^ 3 ∂μ i) ^ (1 / 4 : ℝ) := by
  set σ : ι → ℝ := fun i => √(∫ s, s ^ 2 ∂μ i)
  have hσ2 (i : ι) : σ i ^ 2 = ∫ s, s ^ 2 ∂μ i :=
    Real.sq_sqrt (integral_nonneg fun s => sq_nonneg s)
  have hY1 (i : ι) : ∫ s, s ∂(gaussianReal 0 1).map (σ i * ·) = 0 := by
    rw [integral_map_gaussianReal_const_mul (g := fun s => s) _ continuous_id, integral_const_mul,
      integral_id_gaussianReal, mul_zero]
  have hY2 (i : ι) : ∫ s, s ^ 2 ∂(gaussianReal 0 1).map (σ i * ·) = ∫ s, s ^ 2 ∂μ i := by
    rw [integral_map_gaussianReal_const_mul (g := fun s => s ^ 2) _ (continuous_pow 2)]
    simp only [mul_pow, integral_const_mul, integral_sq_gaussianReal, mul_one, hσ2]
  have hY3 (i : ι) : ∫ s, |s| ^ 3 ∂(gaussianReal 0 1).map (σ i * ·) ≤ 2 * ∫ s, |s| ^ 3 ∂μ i := by
    rw [integral_map_gaussianReal_const_mul (g := fun s => |s| ^ 3) _ (continuous_abs.pow 3)]
    simp only [abs_mul, mul_pow, integral_const_mul]
    rw [abs_of_nonneg (Real.sqrt_nonneg _), mul_comm]
    exact mul_le_mul integral_abs_pow_three_gaussianReal_le
      (sqrt_integral_sq_pow_three_le (hμ i)) (by positivity) (by norm_num)
  refine (abs_measureReal_sum_le_sub_cdf_le_of_hasLaw μ _ hμ
    (fun i => memLp_map_gaussianReal_const_mul (σ i)) (fun i => (h₁ i).trans (hY1 i).symm)
    (fun i => (hY2 i).symm) (hasLaw_sum_pi_map_gaussianReal ((sum_congr rfl
      fun i _ => hσ2 i).trans h₂)) u).trans
    (nine_div_two_mul_rpow_le (sum_integral_abs_pow_three_nonneg _ _) ?_)
  rw [mul_sum]
  exact sum_le_sum fun i _ => by linarith [hY3 i]

end ProbabilityTheory
