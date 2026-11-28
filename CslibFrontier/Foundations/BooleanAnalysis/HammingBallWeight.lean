/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.LevelWeight
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
import CslibFrontier.Foundations.BooleanAnalysis.CentralLimit
import CslibFrontier.Foundations.Probability.Gaussian.Moments

/-!
# The degree-one weight of Hamming balls

Fix `t : ℝ` and let `fₙ : {-1, 1}ⁿ → {0, 1}` be `fₙ(x) = 1` iff `∑ᵢ xᵢ / √n > t`, the indicator
of a Hamming ball centered at the all-ones point. Then `E[fₙ] → 1 - Φ(t)` and
`W¹[fₙ] → φ(t)²` as `n → ∞`, where `φ` and `Φ` are the density and cdf of a standard Gaussian
[O'Donnell, Proposition 5.25][ODonnell2014]. Here a point of the cube is `x : Fin n → Bool` with
`xᵢ = signVal (x i)`, so `false ↦ 1` and `true ↦ -1`; `fₙ` is the real function
`if t < (√n)⁻¹ * ∑ i, signVal (x i) then 1 else 0`, `φ = gaussianPDFReal 0 1` and
`Φ = cdf (gaussianReal 0 1)`.

The proof is the one of [O'Donnell, Exercise 5.30][ODonnell2014].

* **Symmetry.** A function invariant under permutations of the coordinates has equal degree-one
  coefficients, so `W¹[f] = E[f(x) ∑ᵢ xᵢ / √n]²`
  (`levelWeight_one_eq_sq_expect_mul_of_comp_perm`, in `BooleanAnalysis.LevelWeight`).
* **Central limit theorem.** Write `z · 1{z > t} = (z - t)⁺ + t · 1{z > t}`. The central limit
  theorem on the cube (`CslibFrontier.Foundations.BooleanAnalysis.CentralLimit`) takes the
  expectation of the event (`tendsto_expect_indicator_inv_sqrt_mul_sum_signVal`) and of `(z - t)⁺`,
  which grows at most linearly (`tendsto_expect_inv_sqrt_mul_sum_signVal_of_sq_le`), to their
  Gaussian limits.
* **Limit.** The limit is `E[Z · 1{Z > t}] = φ(t)`
  (`ProbabilityTheory.setIntegral_Ioi_id_gaussianReal`).

The book goes on to read the result as `W¹[fₙ] → U(α)²` with `α = lim E[fₙ]` and the Gaussian
isoperimetric function `U = φ ∘ Φ⁻¹` (Definition 5.26); that form is not stated here.

## Main results

* `Cslib.BitString.levelWeight_one_hammingBall`: `W¹[fₙ] = E[fₙ(x) ∑ᵢ xᵢ / √n]²` exactly.
* `Cslib.BitString.tendsto_expect_hammingBall`: `E[fₙ] → 1 - Φ(t)`.
* `Cslib.BitString.tendsto_levelWeight_one_hammingBall`: `W¹[fₙ] → φ(t)²`.

## Usage

The limits are `Tendsto … atTop (𝓝 _)` in `n` for `fₙ` written exactly as above. The book writes
the limit of the mean as the complementary cdf `Φ̄(t)` (Notation 5.14), which is `1 - Φ(t)` here.
For another function invariant under permutations of the coordinates, apply
`levelWeight_one_eq_sq_expect_mul_of_comp_perm` directly. The checked clients in
[CslibFrontierTests/BooleanAnalysisHammingBallWeight.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisHammingBallWeight.lean)
evaluate the exact identity at `n = 2`, `t = 0` against the two degree-one coefficients, and
specialize the limits at `t = 0` and `t = 1`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 5.4.
-/

public section

open MeasureTheory ProbabilityTheory Finset Filter Topology Real
open scoped BigOperators

namespace Cslib.BitString

/-! ### Hamming balls -/

/-- **The mean of a Hamming ball indicator** [O'Donnell, Proposition 5.25][ODonnell2014]. For
`fₙ(x) = 1` iff `∑ᵢ xᵢ / √n > t`, where `xᵢ = signVal (x i)`, `E[fₙ] → 1 - Φ(t)`. -/
theorem tendsto_expect_hammingBall (t : ℝ) :
    Tendsto (fun n : ℕ => 𝔼 x : Fin n → Bool,
        if t < (√n)⁻¹ * ∑ i, signVal (x i) then (1 : ℝ) else 0) atTop
      (𝓝 (1 - cdf (gaussianReal 0 1) t)) := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic, Set.compl_Iic]
  refine (tendsto_expect_indicator_inv_sqrt_mul_sum_signVal measurableSet_Ioi
    (by simp)).congr fun n => expect_congr rfl fun x _ => ?_
  simp [Set.indicator_apply]

/-- **The degree-one weight of a Hamming ball indicator, exactly.** For `fₙ(x) = 1` iff
`∑ᵢ xᵢ / √n > t`, where `xᵢ = signVal (x i)`, `W¹[fₙ] = E[fₙ(x) ∑ᵢ xᵢ / √n]²`
[O'Donnell, Exercise 5.30][ODonnell2014]. -/
theorem levelWeight_one_hammingBall (n : ℕ) (t : ℝ) :
    (levelWeight 1 fun x : Fin n → Bool =>
        if t < (√n)⁻¹ * ∑ i, signVal (x i) then (1 : ℝ) else 0) =
      (𝔼 x : Fin n → Bool, (if t < (√n)⁻¹ * ∑ i, signVal (x i) then (1 : ℝ) else 0) *
        ((√n)⁻¹ * ∑ i, signVal (x i))) ^ 2 := by
  rw [levelWeight_one_eq_sq_expect_mul_of_comp_perm fun σ x => ?_, Fintype.card_fin]
  simp only [Function.comp_apply, Equiv.sum_comp σ fun i => signVal (x i)]

/-- **The degree-one weight of a Hamming ball indicator**
[O'Donnell, Proposition 5.25][ODonnell2014]. For `fₙ(x) = 1` iff `∑ᵢ xᵢ / √n > t`, where
`xᵢ = signVal (x i)`, `W¹[fₙ] → φ(t)²`. By symmetry `W¹[fₙ] = E[fₙ(x) ∑ᵢ xᵢ / √n]²`
[O'Donnell, Exercise 5.30][ODonnell2014], and the central limit theorem sends this to
`E[Z · 1{Z > t}]² = φ(t)²`. -/
theorem tendsto_levelWeight_one_hammingBall (t : ℝ) :
    Tendsto (fun n : ℕ => levelWeight 1 fun x : Fin n → Bool =>
        if t < (√n)⁻¹ * ∑ i, signVal (x i) then (1 : ℝ) else 0) atTop
      (𝓝 (gaussianPDFReal 0 1 t ^ 2)) := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  -- `z · 1{z > t} = (z - t)⁺ + t · 1{z > t}`, a function of at most linear growth plus an event.
  have hpos := tendsto_expect_inv_sqrt_mul_sum_signVal_of_sq_le (h := fun z => max (z - t) 0)
    (by fun_prop) (a := 2) (b := 2 * t ^ 2) fun z => by
      rcases le_total (z - t) 0 with hz | hz
      · rw [max_eq_right hz]; nlinarith [sq_nonneg z, sq_nonneg t]
      · rw [max_eq_left hz]; nlinarith [sq_nonneg (z + t)]
  have hind := tendsto_expect_indicator_inv_sqrt_mul_sum_signVal (E := Set.Ioi t)
    measurableSet_Ioi (by simp)
  have hval : ∫ z, max (z - t) 0 ∂gaussianReal 0 1 + t * (gaussianReal 0 1).real (Set.Ioi t) =
      gaussianPDFReal 0 1 t := by
    have hmax : (fun z => max (z - t) 0) = (Set.Ioi t).indicator fun z => z - t := by
      ext z
      by_cases hz : t < z
      · simp [hz, hz.le]
      · simp [hz, not_lt.1 hz]
    have hint : IntegrableOn (fun z => z) (Set.Ioi t) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal 1).integrable le_rfl |>.integrableOn
    rw [hmax, integral_indicator measurableSet_Ioi, integral_sub hint (integrable_const t),
      setIntegral_const, setIntegral_Ioi_id_gaussianReal, smul_eq_mul]
    ring
  rw [← hval]
  refine ((hpos.add (hind.const_mul t)).pow 2).congr fun n => ?_
  rw [levelWeight_one_hammingBall, mul_expect, ← expect_add_distrib]
  congr 1
  refine expect_congr rfl fun x _ => ?_
  by_cases hz : t < (√n)⁻¹ * ∑ i, signVal (x i)
  · simp [hz, hz.le]
  · simp [hz, not_lt.1 hz]

end Cslib.BitString
