/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.WeightedMatching
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Matching
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Arccos
import CslibFrontier.Foundations.Geometry.Euclidean.Angle.Cap
import CslibFrontier.Foundations.Probability.Gaussian.Sheppard
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hilbert-space two-cap bound on `cost_λ` and `U₂` Gaussian coefficients

For a clean matched pair `e = {u, v}` in a `U₂` cubic quotient with outer incident edge pairs
`{a, b}` at `u` and `{c, d}` at `v`, a 3-state pair-compressed branching program pays
`log₂ 3 = 1 + λ` bits (`λ = log₂ 3 - 1 ≈ 0.5849625`) on `(1, 1)` splits where both outer pairs
straddle the threshold `t`, and `1` bit on all other straddling outer splits. Thus its expected
threshold cost under Gaussian edge scores `edgeScore G q R` is `𝔼[cost_λ]` where
`cost_λ = 1_{PairStraddlesAny} + λ · 1_{PairStraddlesBoth}`.

This module bounds `𝔼[cost_λ]` universally over all loopless cubic graphs (with no girth
assumption) and evaluates the resulting rational `U₂` coefficients:

1. **Exact `cost_{1/2}` identity and `cost_λ` convex mix.** On all `16` outer Boolean masks,
   `cost_{1/2}(a, b, c, d)` equals `(1/2)(1_{a ≠ b} + 1_{c ≠ d})` plus
   `(1/4)(1_{a ≠ c} + 1_{a ≠ d} + 1_{b ≠ c} + 1_{b ≠ d})`. Combining with the 32-mask inequality
   `cost_1 ≤ starCost(a, b, m) + starCost(c, d, m)` (`twoVertexCost_le_starCost_add`) gives, for
   every `λ ∈ [1/2, 1]`,
   `𝔼[cost_λ] ≤ (2 - 2λ) 𝔼[cost_{1/2}] + (2λ - 1) · 2 straddleBound(ρ₀)`.
2. **Sheppard + Hilbert-space two-cap sum of squares.** By Sheppard's inequality, `𝔼[cost_{1/2}]`
   is bounded by `((1/2)(θ_{ab} + θ_{cd}) + (1/4)(θ_{ac} + θ_{ad} + θ_{bc} + θ_{bd})) / π`. For
   adjacent unit kernel rows `u, v` with `⟪u, v⟫ ≥ ρ₀ ≥ 9/10`, all six inner products lie in
   `[0, 1]`. Linearizing concave `arccos` at the Pythagorean tangent points `(672/697, 185/697)`
   and `(624/745, 407/745)` and completing the square in the ambient inner-product space against
   `u ± v` with multiplier `μ = 1133/250` yields `𝔼[cost_{1/2}] ≤ 269265 / 1000000` for all
   `ρ₀ ≥ 94280904 / 100000000` (`measureReal_pairHalf_le`), and hence
   `U2CubicPairBound gaussianCoefficient (271212 / 1000000)` (`u2CubicPairBound_gaussian`).
3. **Explicit rational `U₂` coefficients.** Evaluates rational lower bounds on the resulting `7/8`
   `U₂` circuit-size (`≥ 4.6362`) and quadratic-form correlation (`≥ 2.8007`) coefficients
   (consumed by `CslibFrontier.Computability.Circuit.Frontier.Basis.U2` and
   `CslibFrontier.Computability.Circuit.Frontier.Correlation.RealRank`).

The Hilbert-space two-cap sum-of-squares bound on `𝔼[cost_{1/2}]` (`measureReal_pairHalf_le`) and
the resulting `U₂` Gaussian pair bound (`u2CubicPairBound_gaussian`) are original to this library.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.measureReal_pairHalf_le`: universal two-cap Gaussian bound
  `𝔼[cost_{1/2}] ≤ 269265 / 1000000`.
* `Cslib.Circuits.Frontier.Gaussian.u2CubicPairBound_gaussian`:
  `U2CubicPairBound gaussianCoefficient (271212 / 1000000)`.
* `Cslib.Circuits.Frontier.Gaussian.u2CircuitCoefficient_ge_46362`,
  `Cslib.Circuits.Frontier.Gaussian.u2CorrelationThreshold_ge_28007`: rational lower bounds on the
  `U₂` gate-count and quadratic-form correlation coefficients.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Filter Asymptotics
open scoped RealInnerProductSpace Interval

namespace Cslib.Circuits.Frontier.Gaussian

/-! ### Boolean `cost_{1/2}` identity and `cost_λ` convex mix -/

private def anyDiff (a b c d : Bool) : ℝ :=
  if a = b ∧ b = c ∧ c = d then 0 else 1

private def bothDiff (a b c d : Bool) : ℝ :=
  if a ≠ b ∧ c ≠ d then 1 else 0

private def neqInd (x y : Bool) : ℝ :=
  if x = y then 0 else 1

/-- Exact 16-mask identity decomposing `cost_{1/2}` into `(1/2)` times same-end disagreement
indicators plus `(1/4)` times cross-end disagreement indicators. -/
private theorem costHalf_eq (a b c d : Bool) :
    anyDiff a b c d + (1 / 2) * bothDiff a b c d =
      (1 / 2) * (neqInd a b + neqInd c d) +
        (1 / 4) * (neqInd a c + neqInd a d + neqInd b c + neqInd b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [anyDiff, bothDiff, neqInd]

/-- Exact 32-mask inequality bounding `cost_1 = twoVertexCost` by the sum of the two endpoint
`starCost`s for any shared-edge color `m`. -/
private theorem costOne_le_starCost_add (a b c d m : Bool) :
    anyDiff a b c d + bothDiff a b c d ≤ (starCost a b m : ℝ) + (starCost c d m : ℝ) := by
  have h := twoVertexCost_le_starCost_add a b c d m
  have hcast : ((twoVertexCost a b c d : ℕ) : ℝ) ≤
      ((starCost a b m + starCost c d m : ℕ) : ℝ) := by exact_mod_cast h
  cases a <;> cases b <;> cases c <;> cases d <;> cases m <;>
    norm_num [anyDiff, bothDiff, twoVertexCost, starCost] at hcast ⊢

/-! ### Concave tangent bound for `arccos` and Hilbert-space two-cap SOS -/

/-- Concave tangent upper bound on `arccos` over `[0, 1]` at any Pythagorean point `(x₀, s₀)` in
`(0, 1)` with `x₀ ^ 2 + s₀ ^ 2 = 1`: `arccos x ≤ arccos x₀ - (x - x₀) / s₀`. -/
private theorem arccos_le_tangent {x x₀ s₀ : ℝ} (hx : x ∈ Icc 0 1)
    (hx₀_pos : 0 < x₀) (hx₀_lt : x₀ < 1) (hs₀_pos : 0 < s₀) (hpyth : x₀ ^ 2 + s₀ ^ 2 = 1) :
    arccos x ≤ arccos x₀ - (x - x₀) / s₀ := by
  have hs_eq : √(1 - x₀ ^ 2) = s₀ := by
    have : 1 - x₀ ^ 2 = s₀ ^ 2 := by linarith
    rw [this, sqrt_sq hs₀_pos.le]
  rcases lt_trichotomy x x₀ with hlt | rfl | hgt
  · have hdiff : DifferentiableOn ℝ arccos (Ioo x x₀) :=
      differentiableOn_arccos.mono fun z hz => by
        simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
        exact ⟨by linarith [hx.1, hz.1], by linarith [hz.2, hx₀_lt]⟩
    obtain ⟨c, ⟨hxc, hcx₀⟩, hc⟩ :=
      exists_deriv_eq_slope arccos hlt continuous_arccos.continuousOn hdiff
    rw [deriv_arccos] at hc
    have hc0 : 0 ≤ c := le_trans hx.1 hxc.le
    have h1c : 1 - x₀ ^ 2 < 1 - c ^ 2 := by nlinarith
    have h1x₀ : 0 < 1 - x₀ ^ 2 := by nlinarith
    have hsqrt_lt : s₀ < √(1 - c ^ 2) := by
      rw [← hs_eq]
      exact sqrt_lt_sqrt h1x₀.le h1c
    have hinv : 1 / √(1 - c ^ 2) ≤ 1 / s₀ := one_div_le_one_div_of_le hs₀_pos hsqrt_lt.le
    have hslope : -(1 / s₀) ≤ (arccos x₀ - arccos x) / (x₀ - x) := by linarith
    have hmul := (le_div_iff₀ (sub_pos.mpr hlt)).mp hslope
    rw [neg_mul, one_div_mul_eq_div] at hmul
    have hrew : -((x₀ - x) / s₀) = (x - x₀) / s₀ := by ring
    linarith
  · simp
  · have hdiff : DifferentiableOn ℝ arccos (Ioo x₀ x) :=
      differentiableOn_arccos.mono fun z hz => by
        simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
        exact ⟨by linarith [hx₀_pos, hz.1], by linarith [hz.2, hx.2]⟩
    obtain ⟨c, ⟨hx₀c, hcx⟩, hc⟩ :=
      exists_deriv_eq_slope arccos hgt continuous_arccos.continuousOn hdiff
    rw [deriv_arccos] at hc
    have hc1 : c < 1 := lt_of_lt_of_le hcx hx.2
    have h1c : 0 < 1 - c ^ 2 := by nlinarith
    have h1lt : 1 - c ^ 2 < 1 - x₀ ^ 2 := by nlinarith
    have hsqrt_lt : √(1 - c ^ 2) < s₀ := by
      rw [← hs_eq]
      exact sqrt_lt_sqrt h1c.le h1lt
    have hinv : 1 / s₀ ≤ 1 / √(1 - c ^ 2) :=
      one_div_le_one_div_of_le (sqrt_pos.mpr h1c) hsqrt_lt.le
    have hslope : (arccos x - arccos x₀) / (x - x₀) ≤ -(1 / s₀) := by linarith
    have hmul := (div_le_iff₀ (sub_pos.mpr hgt)).mp hslope
    rw [neg_mul, one_div_mul_eq_div] at hmul
    linarith

/-- Cross-cap inner product positivity: when `‖u‖ = ‖v‖ = ‖y₁‖ = ‖y₂‖ = 1` and all three chain
inner products `⟪y₁, u⟫`, `⟪u, v⟫`, `⟪y₂, v⟫` are at least `9 / 10`, each chain angle is at most
`1 / 2` radian, so `angle y₁ y₂ ≤ 3 / 2 < π / 2` and `0 ≤ ⟪y₁, y₂⟫`. -/
private theorem inner_nonneg_of_two_caps {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u v y₁ y₂ : F} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hy₁ : ‖y₁‖ = 1) (hy₂ : ‖y₂‖ = 1)
    (huv : 9 / 10 ≤ ⟪u, v⟫) (hy₁u : 9 / 10 ≤ ⟪y₁, u⟫) (hy₂v : 9 / 10 ≤ ⟪y₂, v⟫) :
    0 ≤ ⟪y₁, y₂⟫ := by
  have hcos_half : cos (1 / 2 : ℝ) ≤ 9 / 10 := by
    have hb := cos_bound (x := (1 / 2 : ℝ)) (by norm_num)
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hb
    linarith [(abs_le.mp hb).2]
  have hang_le {a b : F} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : 9 / 10 ≤ ⟪a, b⟫) :
      InnerProductGeometry.angle a b ≤ 1 / 2 := by
    rw [InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one ha hb]
    exact (arccos_le_arccos (hcos_half.trans hab)).trans_eq
      (arccos_cos (by norm_num) (by linarith [pi_gt_three]))
  have h1 := hang_le hy₁ hu hy₁u
  have h2 := hang_le hu hv huv
  have h3 : InnerProductGeometry.angle v y₂ ≤ 1 / 2 := by
    rw [InnerProductGeometry.angle_comm]
    exact hang_le hy₂ hv hy₂v
  have htri : InnerProductGeometry.angle y₁ y₂ ≤ 3 / 2 := by
    have ht1 := InnerProductGeometry.angle_le_angle_add_angle y₁ u y₂
    have ht2 := InnerProductGeometry.angle_le_angle_add_angle u v y₂
    linarith
  rw [InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hy₁ hy₂, ← cos_pi_div_two]
  exact cos_le_cos_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg _ _)
    (by linarith [pi_pos]) (by linarith [pi_gt_three])

/-- Hilbert-space completion of the square for `L = y_a + y_b` and `R = y_c + y_d` against `u ± v`:
for `0 < B < A`, `0 ≤ μ`, `‖u‖ = ‖v‖ = 1`, `ρ₀ ≤ ⟪u, v⟫`, and `4 κ ≤ ⟪L, u⟫ + ⟪R, v⟫`,
`4 μ κ - μ ^ 2 (A - B ρ₀) / (2 (A ^ 2 - B ^ 2)) ≤ A (‖L‖ ^ 2 + ‖R‖ ^ 2) + 2 B ⟪L, R⟫`. -/
private theorem hilbert_two_cap_sos {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u v L R : F} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {A B μ ρ₀ κ : ℝ}
    (hB : 0 < B) (hBA : B < A) (hμ : 0 ≤ μ)
    (huv : ρ₀ ≤ ⟪u, v⟫) (hcap : 4 * κ ≤ ⟪L, u⟫ + ⟪R, v⟫) :
    4 * μ * κ - μ ^ 2 * (A - B * ρ₀) / (2 * (A ^ 2 - B ^ 2)) ≤
      A * (‖L‖ ^ 2 + ‖R‖ ^ 2) + 2 * B * ⟪L, R⟫ := by
  have hApB : 0 < A + B := by linarith
  have hAmB : 0 < A - B := by linarith
  have hA2B2 : 0 < A ^ 2 - B ^ 2 := by nlinarith
  set sp : ℝ := μ / (2 * (A + B))
  set sm : ℝ := μ / (2 * (A - B))
  have hsos_nonneg : 0 ≤ ((A + B) / 2) * ‖(L + R) - sp • (u + v)‖ ^ 2 +
      ((A - B) / 2) * ‖(L - R) - sm • (u - v)‖ ^ 2 := by positivity
  have hnorm_uv_p : ‖u + v‖ ^ 2 = 2 + 2 * ⟪u, v⟫ := by
    rw [norm_add_sq_real, hu, hv]; ring
  have hnorm_uv_m : ‖u - v‖ ^ 2 = 2 - 2 * ⟪u, v⟫ := by
    rw [norm_sub_sq_real, hu, hv]; ring
  have hnorm_LR_p : ‖L + R‖ ^ 2 = ‖L‖ ^ 2 + 2 * ⟪L, R⟫ + ‖R‖ ^ 2 := norm_add_sq_real L R
  have hnorm_LR_m : ‖L - R‖ ^ 2 = ‖L‖ ^ 2 - 2 * ⟪L, R⟫ + ‖R‖ ^ 2 := norm_sub_sq_real L R
  have hexp_p : ‖(L + R) - sp • (u + v)‖ ^ 2 =
      ‖L + R‖ ^ 2 - 2 * sp * ⟪L + R, u + v⟫ + sp ^ 2 * ‖u + v‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hexp_m : ‖(L - R) - sm • (u - v)‖ ^ 2 =
      ‖L - R‖ ^ 2 - 2 * sm * ⟪L - R, u - v⟫ + sm ^ 2 * ‖u - v‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hinner_cancel : ⟪L + R, u + v⟫ + ⟪L - R, u - v⟫ = 2 * (⟪L, u⟫ + ⟪R, v⟫) := by
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
    ring
  have hsos_eq : ((A + B) / 2) * ‖(L + R) - sp • (u + v)‖ ^ 2 +
      ((A - B) / 2) * ‖(L - R) - sm • (u - v)‖ ^ 2 =
      A * (‖L‖ ^ 2 + ‖R‖ ^ 2) + 2 * B * ⟪L, R⟫ -
        (μ / 2) * (⟪L + R, u + v⟫ + ⟪L - R, u - v⟫) +
        μ ^ 2 * (A - B * ⟪u, v⟫) / (2 * (A ^ 2 - B ^ 2)) := by
    rw [hexp_p, hexp_m, hnorm_LR_p, hnorm_LR_m, hnorm_uv_p, hnorm_uv_m]
    dsimp only [sp, sm]
    field_simp
    ring
  rw [hinner_cancel] at hsos_eq
  have h1 : 4 * μ * κ ≤ (μ / 2) * (2 * (⟪L, u⟫ + ⟪R, v⟫)) := by
    have := mul_le_mul_of_nonneg_left hcap hμ
    linarith
  have h2 : μ ^ 2 * (A - B * ⟪u, v⟫) / (2 * (A ^ 2 - B ^ 2)) ≤
      μ ^ 2 * (A - B * ρ₀) / (2 * (A ^ 2 - B ^ 2)) := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg μ)
  linarith

/-- Rational upper bound `arccos (672 / 697) ≤ 268643 / 1000000` via `cos_bound` and six
`cos_two_mul_le` doublings. -/
private theorem arccos_672_div_697_le :
    arccos (672 / 697 : ℝ) ≤ 268643 / 1000000 := by
  have hb := cos_bound (x := 268643 / 64000000) (by norm_num)
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 268643 / 64000000)] at hb
  have h0 : cos (268643 / 64000000) ≤ 999991190317 / 1000000000000 := by
    linarith [(abs_le.mp hb).2]
  have h1 := cos_two_mul_le (by norm_num) h0 (v := 62497797589 / 62500000000) (by norm_num)
  have h2 := cos_two_mul_le (by norm_num) h1 (v := 49992952409 / 50000000000) (by norm_num)
  have h3 := cos_two_mul_le (by norm_num) h2 (v := 199887246491 / 200000000000) (by norm_num)
  have h4 := cos_two_mul_le (by norm_num) h3 (v := 62359097843 / 62500000000) (by norm_num)
  have h5 := cos_two_mul_le (by norm_num) h4 (v := 495496213451 / 500000000000) (by norm_num)
  have h6 := cos_two_mul_le (by norm_num) h5 (v := 672 / 697) (by norm_num)
  norm_num only at h6
  exact (arccos_le_arccos h6).trans_eq (arccos_cos (by norm_num) (by linarith [pi_gt_three]))

/-- Rational upper bound `arccos (624 / 745) ≤ 2889757 / 5000000` via `cos_bound` and six
`cos_two_mul_le` doublings. -/
private theorem arccos_624_div_745_le :
    arccos (624 / 745 : ℝ) ≤ 2889757 / 5000000 := by
  have hb := cos_bound (x := 2889757 / 320000000) (by norm_num)
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2889757 / 320000000)] at hb
  have h0 : cos (2889757 / 320000000) ≤ 499979612733 / 500000000000 := by
    linarith [(abs_le.mp hb).2]
  have h1 := cos_two_mul_le (by norm_num) h0 (v := 99983690519 / 100000000000) (by norm_num)
  have h2 := cos_two_mul_le (by norm_num) h1 (v := 24983691849 / 25000000000) (by norm_num)
  have h3 := cos_two_mul_le (by norm_num) h2 (v := 997391546899 / 1000000000000) (by norm_num)
  have h4 := cos_two_mul_le (by norm_num) h3 (v := 247394948913 / 250000000000) (by norm_num)
  have h5 := cos_two_mul_le (by norm_num) h4 (v := 479268171963 / 500000000000) (by norm_num)
  have h6 := cos_two_mul_le (by norm_num) h5 (v := 624 / 745) (by norm_num)
  norm_num only at h6
  exact (arccos_le_arccos h6).trans_eq (arccos_cos (by norm_num) (by linarith [pi_gt_three]))

/-- Pure Hilbert-space six-angle bound: for unit vectors `u, v, y_a, y_b, y_c, y_d` with
`94280904 / 100000000 ≤ ρ₀ ≤ ⟪u, v⟫` and `√((1 + ρ₀) / 2)` cap membership of `y_a, y_b` around `u`
and `y_c, y_d` around `v`,
`((1/2)(θ_{ab} + θ_{cd}) + (1/4)(θ_{ac} + θ_{ad} + θ_{bc} + θ_{bd})) / π ≤ 269265 / 1000000`. -/
private theorem two_cap_six_angle_bound {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u v ya yb yc yd : F} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hya : ‖ya‖ = 1) (hyb : ‖yb‖ = 1) (hyc : ‖yc‖ = 1) (hyd : ‖yd‖ = 1)
    {ρ₀ : ℝ} (hρ_lo : 94280904 / 100000000 ≤ ρ₀) (huv : ρ₀ ≤ ⟪u, v⟫)
    (hc_a : √((1 + ρ₀) / 2) ≤ ⟪ya, u⟫) (hc_b : √((1 + ρ₀) / 2) ≤ ⟪yb, u⟫)
    (hc_c : √((1 + ρ₀) / 2) ≤ ⟪yc, v⟫) (hc_d : √((1 + ρ₀) / 2) ≤ ⟪yd, v⟫) :
    ((1 / 2) * (InnerProductGeometry.angle ya yb + InnerProductGeometry.angle yc yd) +
      (1 / 4) * (InnerProductGeometry.angle ya yc + InnerProductGeometry.angle ya yd +
        InnerProductGeometry.angle yb yc + InnerProductGeometry.angle yb yd)) / π ≤
      269265 / 1000000 := by
  have h910_uv : 9 / 10 ≤ ⟪u, v⟫ := by linarith
  have hκ_lo : 985598559 / 1000000000 ≤ √((1 + ρ₀) / 2) := by
    refine (le_sqrt (by norm_num) (by linarith)).mpr ?_
    linarith
  have h910_κ : 9 / 10 ≤ √((1 + ρ₀) / 2) := by linarith
  have hmem_same {z₁ z₂ w : F} (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1) (hw : ‖w‖ = 1)
      (hc₁ : √((1 + ρ₀) / 2) ≤ ⟪z₁, w⟫) (hc₂ : √((1 + ρ₀) / 2) ≤ ⟪z₂, w⟫) :
      ⟪z₁, z₂⟫ ∈ Icc 0 1 := by
    refine ⟨?_, (real_inner_le_norm _ _).trans_eq (by rw [hz₁, hz₂, one_mul])⟩
    have h := InnerProductGeometry.two_mul_sq_sub_one_le_inner hw hz₁ hz₂ (sqrt_nonneg _) hc₁ hc₂
    rw [sq_sqrt (by linarith)] at h
    linarith
  have hmem_opp {z₁ z₂ : F} (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1)
      (hc₁ : √((1 + ρ₀) / 2) ≤ ⟪z₁, u⟫) (hc₂ : √((1 + ρ₀) / 2) ≤ ⟪z₂, v⟫) :
      ⟪z₁, z₂⟫ ∈ Icc 0 1 :=
    ⟨inner_nonneg_of_two_caps hu hv hz₁ hz₂ h910_uv (h910_κ.trans hc₁) (h910_κ.trans hc₂),
      (real_inner_le_norm _ _).trans_eq (by rw [hz₁, hz₂, one_mul])⟩
  rw [InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one hya hyb,
    InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one hyc hyd,
    InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one hya hyc,
    InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one hya hyd,
    InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one hyb hyc,
    InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one hyb hyd]
  have h_ab := arccos_le_tangent (hmem_same hya hyb hu hc_a hc_b) (x₀ := 672 / 697)
    (s₀ := 185 / 697) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h_cd := arccos_le_tangent (hmem_same hyc hyd hv hc_c hc_d) (x₀ := 672 / 697)
    (s₀ := 185 / 697) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h_ac := arccos_le_tangent (hmem_opp hya hyc hc_a hc_c) (x₀ := 624 / 745)
    (s₀ := 407 / 745) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h_ad := arccos_le_tangent (hmem_opp hya hyd hc_a hc_d) (x₀ := 624 / 745)
    (s₀ := 407 / 745) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h_bc := arccos_le_tangent (hmem_opp hyb hyc hc_b hc_c) (x₀ := 624 / 745)
    (s₀ := 407 / 745) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h_bd := arccos_le_tangent (hmem_opp hyb hyd hc_b hc_d) (x₀ := 624 / 745)
    (s₀ := 407 / 745) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  set L : F := ya + yb
  set R : F := yc + yd
  have hL_sq : ‖L‖ ^ 2 = 2 + 2 * ⟪ya, yb⟫ := by
    dsimp only [L]; rw [norm_add_sq_real, hya, hyb]; ring
  have hR_sq : ‖R‖ ^ 2 = 2 + 2 * ⟪yc, yd⟫ := by
    dsimp only [R]; rw [norm_add_sq_real, hyc, hyd]; ring
  have hLR_in : ⟪L, R⟫ = ⟪ya, yc⟫ + ⟪ya, yd⟫ + ⟪yb, yc⟫ + ⟪yb, yd⟫ := by
    dsimp only [L, R]; simp only [inner_add_left, inner_add_right]; ring
  have hcap4 : 4 * (985598559 / 1000000000 : ℝ) ≤ ⟪L, u⟫ + ⟪R, v⟫ := by
    dsimp only [L, R]
    simp only [inner_add_left]
    linarith
  have hsos := hilbert_two_cap_sos hu hv (A := 697 / 740) (B := 745 / 3256) (μ := 1133 / 250)
    (ρ₀ := 94280904 / 100000000) (κ := 985598559 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (hρ_lo.trans huv) hcap4
  have h_acs := arccos_672_div_697_le
  have h_aco := arccos_624_div_745_le
  have hpi_lo : (314159265 / 100000000 : ℝ) < π := by linarith [pi_gt_d20]
  rw [div_le_iff₀ pi_pos]
  linarith

/-! ### Sheppard expectations on matched pairs -/

section PairExpectations

variable {V E : Type*} [Fintype V] [Finite E] {G : Multigraph V E}

omit [Finite E] in
private theorem indicator_pairAnyEvent_le {M : Set E} {e ea eb ec ed : E} (he : e ∈ M)
    (hab_eq : G.incidenceSet (G.src e) \ {e} = {ea, eb})
    (hcd_eq : G.incidenceSet (G.tgt e) \ {e} = {ec, ed})
    (q : ℝ) (R : ℕ) (t : ℝ) (ω : V → ℝ) :
    (pairAnyEvent G M q R t e).indicator (1 : (V → ℝ) → ℝ) ω ≤
      anyDiff (decide (edgeScore G q R ω ea < t)) (decide (edgeScore G q R ω eb < t))
        (decide (edgeScore G q R ω ec < t)) (decide (edgeScore G q R ω ed < t)) := by
  classical
  set sc := edgeScore G q R ω
  set ba := decide (sc ea < t)
  set bb := decide (sc eb < t)
  set bc := decide (sc ec < t)
  set bd := decide (sc ed < t)
  simp only [indicator_apply, Pi.one_apply]
  split_ifs with hω
  · dsimp only [pairAnyEvent] at hω
    rw [ite_eq_left he] at hω
    obtain ⟨⟨f₁, hf₁, hlt⟩, ⟨f₂, hf₂, hge⟩⟩ := hω
    rw [hab_eq, hcd_eq] at hf₁ hf₂
    have hb₁ : decide (sc f₁ < t) = true := decide_eq_true hlt
    have hb₂ : decide (sc f₂ < t) = false := decide_eq_false (not_lt.mpr hge)
    have hnot : ¬(ba = bb ∧ bb = bc ∧ bc = bd) := by
      intro hall
      rcases hf₁ with (rfl | rfl) | (rfl | rfl) <;>
        rcases hf₂ with (rfl | rfl) | (rfl | rfl) <;>
        · dsimp only [ba, bb, bc, bd] at hall; grind
    simp [anyDiff, hnot]
  · unfold anyDiff; split_ifs <;> norm_num

omit [Finite E] in
private theorem indicator_pairBothEvent_le {M : Set E} {e ea eb ec ed : E} (he : e ∈ M)
    (hab_eq : G.incidenceSet (G.src e) \ {e} = {ea, eb})
    (hcd_eq : G.incidenceSet (G.tgt e) \ {e} = {ec, ed})
    (q : ℝ) (R : ℕ) (t : ℝ) (ω : V → ℝ) :
    (pairBothEvent G M q R t e).indicator (1 : (V → ℝ) → ℝ) ω ≤
      bothDiff (decide (edgeScore G q R ω ea < t)) (decide (edgeScore G q R ω eb < t))
        (decide (edgeScore G q R ω ec < t)) (decide (edgeScore G q R ω ed < t)) := by
  classical
  set sc := edgeScore G q R ω
  set ba := decide (sc ea < t)
  set bb := decide (sc eb < t)
  set bc := decide (sc ec < t)
  set bd := decide (sc ed < t)
  simp only [indicator_apply, Pi.one_apply]
  split_ifs with hω
  · dsimp only [pairBothEvent] at hω
    rw [ite_eq_left he] at hω
    obtain ⟨⟨⟨f₁, hf₁, hlt₁⟩, ⟨f₂, hf₂, hge₁⟩⟩, ⟨⟨g₁, hg₁, hlt₂⟩, ⟨g₂, hg₂, hge₂⟩⟩⟩ := hω
    rw [hab_eq] at hf₁ hf₂
    rw [hcd_eq] at hg₁ hg₂
    have hab_d : ba ≠ bb := by
      have hb₁ : decide (sc f₁ < t) = true := decide_eq_true hlt₁
      have hb₂ : decide (sc f₂ < t) = false := decide_eq_false (not_lt.mpr hge₁)
      rcases hf₁ with rfl | rfl <;> rcases hf₂ with rfl | rfl <;>
        · dsimp only [ba, bb]; grind
    have hcd_d : bc ≠ bd := by
      have hb₁ : decide (sc g₁ < t) = true := decide_eq_true hlt₂
      have hb₂ : decide (sc g₂ < t) = false := decide_eq_false (not_lt.mpr hge₂)
      rcases hg₁ with rfl | rfl <;> rcases hg₂ with rfl | rfl <;>
        · dsimp only [bc, bd]; grind
    simp [bothDiff, hab_d, hcd_d]
  · unfold bothDiff; split_ifs <;> norm_num

/-- At any matched edge `e ∈ M` in a loopless cubic multigraph, `pairAny + pairBoth` is bounded in
expectation by the sum of the two endpoint `straddleEvent` probabilities. -/
private theorem measureReal_pairOne_le_straddle_add (_hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) {M : Set E} {e : E} (he : e ∈ M)
    (q : ℝ) (R : ℕ) (t : ℝ) :
    let P := Measure.pi fun _ : V => gaussianReal 0 1
    P.real (pairAnyEvent G M q R t e) + P.real (pairBothEvent G M q R t e) ≤
      P.real (straddleEvent G q R t (G.src e)) + P.real (straddleEvent G q R t (G.tgt e)) := by
  classical
  intro P
  set u := G.src e
  set v := G.tgt e
  have hu2 : (G.incidenceSet u \ {e}).ncard = 2 := by
    have he_u : e ∈ G.incidenceSet u := Or.inl rfl
    have := ncard_sdiff_singleton_add_one he_u (toFinite _)
    have := h3 u; omega
  have hv2 : (G.incidenceSet v \ {e}).ncard = 2 := by
    have he_v : e ∈ G.incidenceSet v := Or.inr rfl
    have := ncard_sdiff_singleton_add_one he_v (toFinite _)
    have := h3 v; omega
  obtain ⟨ea, eb, _, hab_eq⟩ := ncard_eq_two.mp hu2
  obtain ⟨ec, ed, _, hcd_eq⟩ := ncard_eq_two.mp hv2
  have hea_u : ea ∈ G.incidenceSet u := (hab_eq ▸ mem_insert ea {eb}).1
  have heb_u : eb ∈ G.incidenceSet u := (hab_eq ▸ mem_insert_of_mem ea (mem_singleton eb)).1
  have hec_v : ec ∈ G.incidenceSet v := (hcd_eq ▸ mem_insert ec {ed}).1
  have hed_v : ed ∈ G.incidenceSet v := (hcd_eq ▸ mem_insert_of_mem ec (mem_singleton ed)).1
  set A_ev := pairAnyEvent G M q R t e
  set B_ev := pairBothEvent G M q R t e
  set Su := straddleEvent G q R t u
  set Sv := straddleEvent G q R t v
  have hSu_m : MeasurableSet Su := measurableSet_straddleEvent q R t u
  have hSv_m : MeasurableSet Sv := measurableSet_straddleEvent q R t v
  have hA_m : MeasurableSet A_ev := measurableSet_pairAnyEvent M q R t e
  have hB_m : MeasurableSet B_ev := measurableSet_pairBothEvent M q R t e
  have hint (C : Set (V → ℝ)) (hC : MeasurableSet C) : Integrable (C.indicator 1) P :=
    (integrable_const (1 : ℝ)).indicator hC
  have hpt (ω : V → ℝ) : A_ev.indicator (1 : (V → ℝ) → ℝ) ω +
      B_ev.indicator (1 : (V → ℝ) → ℝ) ω ≤
      Su.indicator (1 : (V → ℝ) → ℝ) ω + Sv.indicator (1 : (V → ℝ) → ℝ) ω := by
    set sc := edgeScore G q R ω
    set ba := decide (sc ea < t)
    set bb := decide (sc eb < t)
    set bc := decide (sc ec < t)
    set bd := decide (sc ed < t)
    set bm := decide (sc e < t)
    have hA_le := indicator_pairAnyEvent_le he hab_eq hcd_eq q R t ω
    have hB_le := indicator_pairBothEvent_le he hab_eq hcd_eq q R t ω
    have hstar_le {f₁ f₂ : E} {w : V} (hf₁ : f₁ ∈ G.incidenceSet w)
        (hf₂ : f₂ ∈ G.incidenceSet w) (hw : e ∈ G.incidenceSet w) :
        (starCost (decide (sc f₁ < t)) (decide (sc f₂ < t)) bm : ℝ) ≤
          (straddleEvent G q R t w).indicator (1 : (V → ℝ) → ℝ) ω := by
      simp only [starCost, indicator_apply, Pi.one_apply]
      by_cases heq : decide (sc f₁ < t) = decide (sc f₂ < t) ∧ decide (sc f₂ < t) = bm
      · rw [ite_eq_left heq, Nat.cast_zero]
        split_ifs <;> norm_num
      · rw [ite_eq_right heq, Nat.cast_one]
        by_cases hstr : ω ∈ straddleEvent G q R t w
        · simp [hstr]
        · exfalso; apply hstr
          by_cases h1 : sc f₁ < t <;> by_cases h2 : sc f₂ < t <;> by_cases hm : sc e < t
          · exfalso; apply heq; simp [bm, h1, h2, hm]
          · exact ⟨⟨f₁, hf₁, h1⟩, ⟨e, hw, not_lt.mp hm⟩⟩
          · exact ⟨⟨f₁, hf₁, h1⟩, ⟨f₂, hf₂, not_lt.mp h2⟩⟩
          · exact ⟨⟨f₁, hf₁, h1⟩, ⟨f₂, hf₂, not_lt.mp h2⟩⟩
          · exact ⟨⟨f₂, hf₂, h2⟩, ⟨f₁, hf₁, not_lt.mp h1⟩⟩
          · exact ⟨⟨f₂, hf₂, h2⟩, ⟨f₁, hf₁, not_lt.mp h1⟩⟩
          · exact ⟨⟨e, hw, hm⟩, ⟨f₁, hf₁, not_lt.mp h1⟩⟩
          · exfalso; apply heq; simp [bm, h1, h2, hm]
    have hsu := hstar_le hea_u heb_u (Or.inl rfl : e ∈ G.incidenceSet u)
    have hsv := hstar_le hec_v hed_v (Or.inr rfl : e ∈ G.incidenceSet v)
    have h1 := costOne_le_starCost_add ba bb bc bd bm
    linarith
  rw [← integral_indicator_one hA_m, ← integral_indicator_one hB_m,
    ← integral_indicator_one hSu_m, ← integral_indicator_one hSv_m,
    ← integral_add (hint _ hA_m) (hint _ hB_m),
    ← integral_add (hint _ hSu_m) (hint _ hSv_m)]
  exact integral_mono ((hint _ hA_m).add (hint _ hB_m)) ((hint _ hSu_m).add (hint _ hSv_m))
    (Pi.le_def.mpr hpt)

/-- **Universal two-cap bound on `𝔼[cost_{1/2}]`.** In any loopless cubic multigraph, when
`94280904 / 100000000 ≤ ρ₀ ≤ 2 q / (1 + q ^ 2) - 3 (2 q ^ 2) ^ R`, every matched edge `e ∈ M` and
threshold `t` satisfy
`P.real (pairAnyEvent G M q R t e) + (1/2) P.real (pairBothEvent G M q R t e) ≤ 269265 / 1000000`.
-/
theorem measureReal_pairHalf_le (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M : Set E} {e : E} (he : e ∈ M) {q ρ₀ : ℝ} (hq : 0 ≤ q) {R : ℕ}
    (hρ_lo : 94280904 / 100000000 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (t : ℝ) :
    let P := Measure.pi fun _ : V => gaussianReal 0 1
    P.real (pairAnyEvent G M q R t e) + (1 / 2) * P.real (pairBothEvent G M q R t e) ≤
      269265 / 1000000 := by
  classical
  intro P
  have hdeg : G.MaxDegreeLE 3 := fun w => (h3 w).le
  set u := G.src e
  set v := G.tgt e
  have hu2 : (G.incidenceSet u \ {e}).ncard = 2 := by
    have he_u : e ∈ G.incidenceSet u := Or.inl rfl
    have := ncard_sdiff_singleton_add_one he_u (toFinite _)
    have := h3 u; omega
  have hv2 : (G.incidenceSet v \ {e}).ncard = 2 := by
    have he_v : e ∈ G.incidenceSet v := Or.inr rfl
    have := ncard_sdiff_singleton_add_one he_v (toFinite _)
    have := h3 v; omega
  obtain ⟨ea, eb, -, hab_eq⟩ := ncard_eq_two.mp hu2
  obtain ⟨ec, ed, -, hcd_eq⟩ := ncard_eq_two.mp hv2
  have hea_u : ea ∈ G.incidenceSet u := (hab_eq ▸ mem_insert ea {eb}).1
  have heb_u : eb ∈ G.incidenceSet u := (hab_eq ▸ mem_insert_of_mem ea (mem_singleton eb)).1
  have hec_v : ec ∈ G.incidenceSet v := (hcd_eq ▸ mem_insert ec {ed}).1
  have hed_v : ed ∈ G.incidenceSet v := (hcd_eq ▸ mem_insert_of_mem ec (mem_singleton ed)).1
  set A_ev := pairAnyEvent G M q R t e
  set B_ev := pairBothEvent G M q R t e
  set Sep : E → E → Set (V → ℝ) := fun f₁ f₂ =>
    {ω | t ∈ Ι (edgeScore G q R ω f₁) (edgeScore G q R ω f₂)}
  have hA_m : MeasurableSet A_ev := measurableSet_pairAnyEvent M q R t e
  have hB_m : MeasurableSet B_ev := measurableSet_pairBothEvent M q R t e
  have hSep_m (f₁ f₂ : E) : MeasurableSet (Sep f₁ f₂) :=
    measurableSet_setOf_mem_uIoc (measurable_edgeScore q R _) (measurable_edgeScore q R _) t
  have hint (C : Set (V → ℝ)) (hC : MeasurableSet C) : Integrable (C.indicator 1) P :=
    (integrable_const (1 : ℝ)).indicator hC
  have hpt (ω : V → ℝ) : A_ev.indicator (1 : (V → ℝ) → ℝ) ω +
      (1 / 2) * B_ev.indicator (1 : (V → ℝ) → ℝ) ω ≤
      (1 / 2) * ((Sep ea eb).indicator 1 ω + (Sep ec ed).indicator 1 ω) +
        (1 / 4) * ((Sep ea ec).indicator 1 ω + (Sep ea ed).indicator 1 ω +
          (Sep eb ec).indicator 1 ω + (Sep eb ed).indicator 1 ω) := by
    set sc := edgeScore G q R ω
    set ba := decide (sc ea < t)
    set bb := decide (sc eb < t)
    set bc := decide (sc ec < t)
    set bd := decide (sc ed < t)
    have hA_le := indicator_pairAnyEvent_le he hab_eq hcd_eq q R t ω
    have hB_le := indicator_pairBothEvent_le he hab_eq hcd_eq q R t ω
    have hneq_eq (f₁ f₂ : E) :
        neqInd (decide (sc f₁ < t)) (decide (sc f₂ < t)) =
          (Sep f₁ f₂).indicator (1 : (V → ℝ) → ℝ) ω := by
      simp only [neqInd, Sep, indicator_apply, Pi.one_apply, mem_ofPred_eq, mem_uIoc]
      by_cases h1 : sc f₁ < t <;> by_cases h2 : sc f₂ < t <;>
        simp [sc, h1, h2, not_lt.mp]
    have hid := costHalf_eq ba bb bc bd
    rw [hneq_eq ea eb, hneq_eq ec ed, hneq_eq ea ec, hneq_eq ea ed, hneq_eq eb ec,
      hneq_eq eb ed] at hid
    linarith
  have hadd {f g : (V → ℝ) → ℝ} (hf : Integrable f P) (hg : Integrable g P) :
      Integrable (fun ω => f ω + g ω) P := hf.add hg
  have hint_lhs := hadd (hint _ hA_m) ((hint _ hB_m).const_mul (1 / 2))
  have hint_s1 := (hadd (hint _ (hSep_m ea eb)) (hint _ (hSep_m ec ed))).const_mul (1 / 2)
  have hint_s2 := (hadd (hadd (hadd (hint _ (hSep_m ea ec)) (hint _ (hSep_m ea ed)))
    (hint _ (hSep_m eb ec))) (hint _ (hSep_m eb ed))).const_mul (1 / 4)
  have hint_le : P.real A_ev + (1 / 2) * P.real B_ev ≤
      (1 / 2) * (P.real (Sep ea eb) + P.real (Sep ec ed)) +
        (1 / 4) * (P.real (Sep ea ec) + P.real (Sep ea ed) +
          P.real (Sep eb ec) + P.real (Sep eb ed)) := by
    rw [← integral_indicator_one hA_m, ← integral_indicator_one hB_m,
      ← integral_const_mul, ← integral_add (hint _ hA_m) ((hint _ hB_m).const_mul (1 / 2)),
      ← integral_indicator_one (hSep_m ea eb), ← integral_indicator_one (hSep_m ec ed),
      ← integral_indicator_one (hSep_m ea ec), ← integral_indicator_one (hSep_m ea ed),
      ← integral_indicator_one (hSep_m eb ec), ← integral_indicator_one (hSep_m eb ed),
      ← integral_add (hint _ (hSep_m ea eb)) (hint _ (hSep_m ec ed)),
      ← integral_add (hint _ (hSep_m ea ec)) (hint _ (hSep_m ea ed)),
      ← integral_add (hadd (hint _ (hSep_m ea ec)) (hint _ (hSep_m ea ed)))
        (hint _ (hSep_m eb ec)),
      ← integral_add (hadd (hadd (hint _ (hSep_m ea ec)) (hint _ (hSep_m ea ed)))
        (hint _ (hSep_m eb ec))) (hint _ (hSep_m eb ed)),
      ← integral_const_mul, ← integral_const_mul,
      ← integral_add hint_s1 hint_s2]
    exact integral_mono hint_lhs (hadd hint_s1 hint_s2) (Pi.le_def.mpr hpt)
  have hunit (f : E) : ‖edgeVector G q R f‖ = 1 :=
    norm_edgeVector hloop hdeg hq (by linarith) hρ f
  have hshep (f₁ f₂ : E) : P.real (Sep f₁ f₂) ≤
      InnerProductGeometry.angle (edgeVector G q R f₁) (edgeVector G q R f₂) / π :=
    measureReal_mem_uIoc_le ((hunit f₁).trans (hunit f₂).symm) t
  have hstep1 : P.real A_ev + (1 / 2) * P.real B_ev ≤
      ((1 / 2) * (InnerProductGeometry.angle (edgeVector G q R ea) (edgeVector G q R eb) +
          InnerProductGeometry.angle (edgeVector G q R ec) (edgeVector G q R ed)) +
        (1 / 4) * (InnerProductGeometry.angle (edgeVector G q R ea) (edgeVector G q R ec) +
          InnerProductGeometry.angle (edgeVector G q R ea) (edgeVector G q R ed) +
          InnerProductGeometry.angle (edgeVector G q R eb) (edgeVector G q R ec) +
          InnerProductGeometry.angle (edgeVector G q R eb) (edgeVector G q R ed))) / π := by
    have hs1 := hshep ea eb; have hs2 := hshep ec ed
    have hs3 := hshep ea ec; have hs4 := hshep ea ed
    have hs5 := hshep eb ec; have hs6 := hshep eb ed
    have hdiv_id : (1 / 2) * (InnerProductGeometry.angle (edgeVector G q R ea)
          (edgeVector G q R eb) / π +
        InnerProductGeometry.angle (edgeVector G q R ec) (edgeVector G q R ed) / π) +
      (1 / 4) * (InnerProductGeometry.angle (edgeVector G q R ea) (edgeVector G q R ec) / π +
        InnerProductGeometry.angle (edgeVector G q R ea) (edgeVector G q R ed) / π +
        InnerProductGeometry.angle (edgeVector G q R eb) (edgeVector G q R ec) / π +
        InnerProductGeometry.angle (edgeVector G q R eb) (edgeVector G q R ed) / π) =
      ((1 / 2) * (InnerProductGeometry.angle (edgeVector G q R ea) (edgeVector G q R eb) +
          InnerProductGeometry.angle (edgeVector G q R ec) (edgeVector G q R ed)) +
        (1 / 4) * (InnerProductGeometry.angle (edgeVector G q R ea) (edgeVector G q R ec) +
          InnerProductGeometry.angle (edgeVector G q R ea) (edgeVector G q R ed) +
          InnerProductGeometry.angle (edgeVector G q R eb) (edgeVector G q R ec) +
          InnerProductGeometry.angle (edgeVector G q R eb) (edgeVector G q R ed))) / π := by ring
    linarith
  have huv_corr : ρ₀ ≤
      ⟪unitKernelRow G.toSimpleGraph q R u, unitKernelRow G.toSimpleGraph q R v⟫ := by
    have h := le_inner_unitKernelRow_src_tgt hloop (d := 3) (by norm_num) hdeg hq R e
    norm_num at h
    linarith
  exact hstep1.trans (two_cap_six_angle_bound (norm_unitKernelRow q R u)
    (norm_unitKernelRow q R v) (hunit ea) (hunit eb) (hunit ec) (hunit ed) hρ_lo huv_corr
    (le_inner_edgeVector hloop hdeg hq (by linarith) hρ hea_u)
    (le_inner_edgeVector hloop hdeg hq (by linarith) hρ heb_u)
    (le_inner_edgeVector hloop hdeg hq (by linarith) hρ hec_v)
    (le_inner_edgeVector hloop hdeg hq (by linarith) hρ hed_v))

end PairExpectations

/-! ### Numerical bounds on `gaussianCoefficient`, `log₂ 3`, and `B_{U₂}` -/

/-- Upper bound `2 * gaussianCoefficient ≤ 100000 / 356249` (`≈ 0.28070254`), direct from
`circuitCoefficient_ge_456249`. -/
theorem two_mul_gaussianCoefficient_le :
    2 * gaussianCoefficient ≤ 100000 / 356249 := by
  have hc := circuitCoefficient_ge_456249
  rw [← one_add_inv_two_mul_gaussianCoefficient] at hc
  have hinv : (356249 / 100000 : ℝ) ≤ 1 / (2 * gaussianCoefficient) := by linarith
  have hp : 0 < 2 * gaussianCoefficient := mul_pos two_pos gaussianCoefficient_pos
  rw [le_div_iff₀ hp] at hinv
  linarith

/-- Lower bound `271212 / 1000000 ≤ 2 * gaussianCoefficient` (`0.271212 ≤ 0.2807025`). -/
theorem le_two_mul_gaussianCoefficient :
    (271212 / 1000000 : ℝ) ≤ 2 * gaussianCoefficient := by
  have hsq2 : √2 < 14142136 / 10000000 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hcos : (1 + 2 * √2) / 4 ≤ cos (29289 / 100000 : ℝ) := by
    have h1 := one_sub_sq_div_two_le_cos (x := (29289 / 100000 : ℝ))
    linarith
  have hθ : (29289 / 100000 : ℝ) ≤ arccos ((1 + 2 * √2) / 4) := by
    calc (29289 / 100000 : ℝ)
        = arccos (cos (29289 / 100000 : ℝ)) :=
          (arccos_cos (by norm_num) (by linarith [pi_gt_three])).symm
      _ ≤ arccos ((1 + 2 * √2) / 4) := arccos_le_arccos hcos
  have hpi : π < 31416 / 10000 := by linarith [pi_lt_d4]
  unfold gaussianCoefficient
  have hrew : 2 * (3 / (2 * π) * arccos ((1 + 2 * √2) / 4)) =
      3 * arccos ((1 + 2 * √2) / 4) / π := by field_simp
  rw [hrew, le_div_iff₀ pi_pos]
  linarith

private theorem logb_two_three_bounds :
    (3 / 2 : ℝ) ≤ Real.logb 2 3 ∧ Real.logb 2 3 ≤ 149 / 94 := by
  constructor
  · rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
    have hsq : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 ≤ (3 : ℝ) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (3 / 2 : ℝ)]
  · rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
    have hpow : (3 : ℝ) ^ (94 : ℕ) ≤ ((2 : ℝ) ^ (149 / 94 : ℝ)) ^ (94 : ℕ) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num)]
      norm_num
    by_contra! hlt
    have := pow_lt_pow_left₀ hlt (Real.rpow_nonneg (by norm_num) _) (by norm_num : 94 ≠ 0)
    linarith

/-- Convex-mix clean-pair bound at `λ = log₂ 3 - 1`:
`(2 - 2λ) · (269265 / 1000000) + (2λ - 1) · (2 gaussianCoefficient) ≤ 271212 / 1000000`. -/
private theorem clean_pair_convex_mix_le :
    let lam := Real.logb 2 3 - 1
    (2 - 2 * lam) * (269265 / 1000000 : ℝ) + (2 * lam - 1) * (2 * gaussianCoefficient) ≤
      271212 / 1000000 := by
  intro lam
  obtain ⟨hlo, hhi⟩ := logb_two_three_bounds
  have h2lam : 0 ≤ 2 * lam - 1 := by dsimp only [lam]; linarith
  have hlam_hi : lam ≤ 55 / 94 := by dsimp only [lam]; linarith
  have hp := two_mul_gaussianCoefficient_le
  have h1 : (2 - 2 * lam) * (269265 / 1000000 : ℝ) + (2 * lam - 1) * (2 * gaussianCoefficient) ≤
      (2 - 2 * lam) * (269265 / 1000000 : ℝ) + (2 * lam - 1) * (100000 / 356249 : ℝ) := by
    nlinarith
  linarith

/-! ### Concentration of `weightedMatchingCost` and `u2CubicPairBound_gaussian` -/

private theorem ncard_matchedVertices_eq_two_mul {V E : Type*}
    {G : Multigraph V E} (hloop : G.Loopless) {M : Set E} (hM : G.IsMatching M) :
    (G.matchedVertices M).ncard = 2 * M.ncard := by
  classical
  let f : M × Bool → G.matchedVertices M := fun ⟨e, b⟩ =>
    if b then ⟨G.src e.1, e.1, e.2, Or.inl rfl⟩ else ⟨G.tgt e.1, e.1, e.2, Or.inr rfl⟩
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨e₁, b₁⟩ ⟨e₂, b₂⟩ heq
      have hval := congrArg Subtype.val heq
      have he_eq : e₁ = e₂ := by
        by_contra hne
        have hdis := hM e₁.2 e₂.2 fun h => hne (Subtype.ext h)
        have hm₁ : (f ⟨e₁, b₁⟩).1 ∈ ({G.src e₁.1, G.tgt e₁.1} : Set V) := by
          cases b₁ <;> simp [f]
        have hm₂ : (f ⟨e₁, b₁⟩).1 ∈ ({G.src e₂.1, G.tgt e₂.1} : Set V) := by
          rw [hval]; cases b₂ <;> simp [f]
        exact Set.disjoint_left.mp hdis hm₁ hm₂
      subst he_eq
      cases b₁ <;> cases b₂
      · rfl
      · exfalso; exact hloop e₁.1 (by simpa [f] using hval.symm)
      · exfalso; exact hloop e₁.1 (by simpa [f] using hval)
      · rfl
    · rintro ⟨v, e, heM, hev⟩
      rcases hev with rfl | rfl
      · exact ⟨⟨⟨e, heM⟩, true⟩, rfl⟩
      · exact ⟨⟨⟨e, heM⟩, false⟩, rfl⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f hbij)
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hcard
  omega

/-- **Unconditional Gaussian `U2CubicPairBound` (`B_{U₂} = 271212 / 1000000`).** Every large cubic
graph `G` with matching `M` and clean sub-matching `M_clean ⊆ M` admits Gaussian edge scores and a
`PairNode` threshold layout whose `(2 - log₂ 3)`-discounted cut at every prefix is at most
`(|V| - 2 |M_clean|) gaussianCoefficient + |M_clean| · (271212 / 1000000) + ξ |V|`. -/
theorem u2CubicPairBound_gaussian :
    U2CubicPairBound gaussianCoefficient (271212 / 1000000) := by
  intro ξ hξ
  set g : ℝ := 2 * √2 / 3
  have hsqrt_lo : (141421356 / 100000000 : ℝ) < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  have hg_lo : (94280904 / 100000000 : ℝ) < g := by dsimp only [g]; linarith
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    ((continuous_arccos.comp (by fun_prop : Continuous fun ρ : ℝ => (1 + 3 * ρ) / 4)
      ).continuousAt (x := g)) (π * ξ / 12) (by positivity)
  set δ_ρ := min η (g - 94280904 / 100000000)
  have hδ_pos : 0 < δ_ρ := lt_min hη (by linarith)
  set ρ₀ := g - δ_ρ / 2
  have hρ_lt : ρ₀ < vertexCorrelation 3 := by
    have h3 : vertexCorrelation 3 = g := by norm_num [vertexCorrelation, g]
    rw [h3]; dsimp only [ρ₀]; linarith
  have hρ_lo : 94280904 / 100000000 ≤ ρ₀ := by
    dsimp only [ρ₀, δ_ρ]; linarith [min_le_right η (g - 94280904 / 100000000)]
  have hstrad_le : straddleBound ρ₀ ≤ gaussianCoefficient + ξ / 8 := by
    have hdist : dist ρ₀ g < η := by
      rw [Real.dist_eq, show ρ₀ - g = -(δ_ρ / 2) by dsimp only [ρ₀]; ring, abs_neg,
        abs_of_pos (by positivity)]
      dsimp only [δ_ρ]
      linarith [min_le_left η (g - 94280904 / 100000000)]
    have hc := hcont hdist
    simp only [Function.comp_apply, Real.dist_eq] at hc
    have hle := (le_abs_self _).trans hc.le
    rw [straddleBound, gaussianCoefficient_eq, show 2 * √2 / 3 = g from rfl, straddleBound]
    calc 3 / (2 * π) * arccos ((1 + 3 * ρ₀) / 4)
        ≤ 3 / (2 * π) * (arccos ((1 + 3 * g) / 4) + π * ξ / 12) := by gcongr; linarith
      _ = 3 / (2 * π) * arccos ((1 + 3 * g) / 4) + ξ / 8 := by
          have := pi_pos; field_simp; ring
  obtain ⟨q, R, hq, hρ_ker⟩ := exists_decay_radius_degree (by norm_num : 2 ≤ 3) hρ_lt
  norm_num at hρ_ker
  -- Grid and concentration parameters keeping tail + window + deviation slack within `(7/8) ξ`.
  let ε := ξ / 64
  have hε : 0 < ε := by positivity
  obtain ⟨T, K, hT, hK, htail_val, hwin_val⟩ := exists_tail_window_grid hξ
  refine ⟨⌈(7 * K + 3) * (vertexOverlap 3 (R + 1) : ℝ) / ε ^ 2⌉₊,
    fun V E _ _ G hloop _ h3 hN M M_clean hM hclean => ?_⟩
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  set P_meas := Measure.pi fun _ : V => gaussianReal 0 1
  set h : ℝ := (Fintype.card V : ℝ)
  set D : ℝ := ((vertexOverlap 3 (R + 1) : ℕ) : ℝ)
  set δ : ℝ := 2 * T / K
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hδpos : 0 < δ := div_pos (by positivity) hKpos
  have hlarge : (7 * K + 3) * D / ε ^ 2 < h := by
    rw [show h = (Nat.card V : ℝ) by dsimp only [h]; exact_mod_cast Nat.card_eq_fintype_card.symm]
    exact (Nat.le_ceil _).trans_lt (by exact_mod_cast hN)
  have hhpos : 0 < h := lt_of_le_of_lt (by positivity) hlarge
  set c : ℝ := ε * h
  have hcpos : 0 < c := mul_pos hε hhpos
  have hdeg : G.MaxDegreeLE 3 := fun v => (h3 v).le
  have hE : (Fintype.card E : ℝ) = 3 / 2 * h := card_edges_eq hloop h3
  let grid (i : ℕ) : ℝ := -T + i * δ
  let winEv (i : ℕ) : E → Set (V → ℝ) :=
    edgeScoreEvent G q R fun x => grid i ≤ x ∧ x < grid i + δ
  let badCost (i : ℕ) : Set (V → ℝ) :=
    deviation (unmatchedStraddleEvent G M q R (grid i)) c ∪
      deviation (pairAnyEvent G M q R (grid i)) c ∪
      deviation (pairBothEvent G (M \ M_clean) q R (grid i)) c ∪
      deviation (pairBothEvent G M_clean q R (grid i)) c
  let badWin (i : ℕ) : Set (V → ℝ) := deviation (winEv i) c
  let badLo : Set (V → ℝ) := deviation (edgeScoreEvent G q R (· < -T)) c
  let badHi : Set (V → ℝ) := deviation (edgeScoreEvent G q R (T ≤ ·)) c
  have hCost_le (i : ℕ) (_ : i < K) : P_meas.real (badCost i) ≤ (11 / 2) * h * D / c ^ 2 := by
    have h1 := measureReal_deviation_unmatchedStraddleEvent_le hdeg M q R (grid i) hcpos
    have h2 := measureReal_deviation_closedBall_src_le hloop h3 R
      (fun e => measurableSet_pairAnyEvent M q R (grid i) e)
      (fun e => dependsOn_pairAnyEvent hloop M q R (grid i) e) hcpos
    have h3' := measureReal_deviation_closedBall_src_le hloop h3 R
      (fun e => measurableSet_pairBothEvent (M \ M_clean) q R (grid i) e)
      (fun e => dependsOn_pairBothEvent hloop (M \ M_clean) q R (grid i) e) hcpos
    have h4 := measureReal_deviation_closedBall_src_le hloop h3 R
      (fun e => measurableSet_pairBothEvent M_clean q R (grid i) e)
      (fun e => dependsOn_pairBothEvent hloop M_clean q R (grid i) e) hcpos
    refine (measureReal_union_le _ _).trans ?_
    refine (add_le_add (measureReal_union_le _ _) h4).trans ?_
    refine (add_le_add (add_le_add (measureReal_union_le _ _) h3')
      (le_refl (3 / 2 * h * D / c ^ 2))).trans ?_
    have heq_sum : h * D / c ^ 2 + 3 / 2 * h * D / c ^ 2 + 3 / 2 * h * D / c ^ 2 +
        3 / 2 * h * D / c ^ 2 = (11 / 2) * h * D / c ^ 2 := by ring
    linarith only [h1, h2, h3', h4, heq_sum]
  have hWin_le (i : ℕ) (_ : i < K) : P_meas.real (badWin i) ≤ 3 / 2 * h * D / c ^ 2 :=
    measureReal_deviation_edgeScoreEvent_le hloop h3 q R
      (measurableSet_Ico : MeasurableSet (Ico (grid i) (grid i + δ))) hcpos
  have hLo_le : P_meas.real badLo ≤ 3 / 2 * h * D / c ^ 2 :=
    measureReal_deviation_edgeScoreEvent_le hloop h3 q R
      (measurableSet_Iio : MeasurableSet (Iio (-T))) hcpos
  have hHi_le : P_meas.real badHi ≤ 3 / 2 * h * D / c ^ 2 :=
    measureReal_deviation_edgeScoreEvent_le hloop h3 q R
      (measurableSet_Ici : MeasurableSet (Ici T)) hcpos
  have hsmall : K * ((11 / 2) * h * D / c ^ 2 + 3 / 2 * h * D / c ^ 2) +
      3 / 2 * h * D / c ^ 2 + 3 / 2 * h * D / c ^ 2 < 1 := by
    have hlt : (7 * (K : ℝ) + 3) * D < ε ^ 2 * h := by
      have htmp := (div_lt_iff₀ (by positivity : 0 < ε ^ 2)).mp hlarge
      linarith only [htmp]
    have heq : (K : ℝ) * ((11 / 2) * h * D / c ^ 2 + 3 / 2 * h * D / c ^ 2) +
        3 / 2 * h * D / c ^ 2 + 3 / 2 * h * D / c ^ 2 =
        (7 * (K : ℝ) + 3) * D / (ε ^ 2 * h) := by
      dsimp only [c]; field_simp; ring
    rw [heq, div_lt_one (by positivity)]; exact hlt
  obtain ⟨ω, hmid, hlo, hhi⟩ := exists_sample_of_grid_bounds hCost_le hWin_le hLo_le hHi_le hsmall
  have unit (e : E) : ‖edgeVector G q R e‖ = 1 :=
    norm_edgeVector hloop hdeg hq (by linarith only [hρ_lo]) hρ_ker e
  set lam := Real.logb 2 3 - 1
  obtain ⟨hlog_lo, hlog_hi⟩ := logb_two_three_bounds
  have hlam0 : 0 ≤ lam := by dsimp only [lam]; linarith only [hlog_lo]
  have hlam1 : lam ≤ 1 := by dsimp only [lam]; linarith only [hlog_hi]
  have hlam_half : 1 / 2 ≤ lam := by dsimp only [lam]; linarith only [hlog_lo]
  set B_tot : ℝ := ((Nat.card V : ℝ) - 2 * M_clean.ncard) * gaussianCoefficient +
    (M_clean.ncard : ℝ) * (271212 / 1000000) + ξ * Nat.card V
  have hcardV_eq : (Nat.card V : ℝ) = h := by
    dsimp only [h]; exact_mod_cast Nat.card_eq_fintype_card
  have hm_clean_le_half : 2 * (M_clean.ncard : ℝ) ≤ h := by
    have hmv := ncard_matchedVertices_eq_two_mul hloop (hM.mono hclean)
    have hle : (G.matchedVertices M_clean).ncard ≤ Fintype.card V := by
      rw [← Nat.card_eq_fintype_card]
      exact (ncard_le_ncard (subset_univ _) (toFinite _)).trans_eq (ncard_univ V)
    have : 2 * M_clean.ncard ≤ Fintype.card V := by omega
    dsimp only [h]; exact_mod_cast this
  have hbase_nonneg : 0 ≤ (h - 2 * M_clean.ncard) * gaussianCoefficient +
      (M_clean.ncard : ℝ) * (271212 / 1000000) := by
    have h1 : 0 ≤ (h - 2 * (M_clean.ncard : ℝ)) * gaussianCoefficient :=
      mul_nonneg (by linarith only [hm_clean_le_half]) gaussianCoefficient_pos.le
    have h2 : (0 : ℝ) ≤ (M_clean.ncard : ℝ) * (271212 / 1000000) := by positivity
    linarith only [h1, h2]
  have hB_tail : h * (18 / T ^ 2 + 12 * ε) ≤ B_tot := by
    have h1 : 18 / T ^ 2 + 12 * ε ≤ ξ := by dsimp only [ε]; linarith only [htail_val, hξ]
    have h2 := mul_le_mul_of_nonneg_left h1 hhpos.le
    dsimp only [B_tot]; rw [hcardV_eq]; linarith only [hbase_nonneg, h2]
  have tail (p : ℝ → Prop) (hp : ∀ x, p x → T ≤ |x|)
      (hdev : ω ∉ deviation (edgeScoreEvent G q R p) c) :
      12 * ({e | p (edgeScore G q R ω e)}.ncard : ℝ) ≤ B_tot := by
    refine (twelve_mul_ncard_edgeScore_tail_le hloop h3 unit hT hp hdev).trans ?_
    refine le_trans ?_ hB_tail
    dsimp only [c, h]
    linarith
  have htop_eq : -T + K * δ = T := by dsimp only [δ]; field_simp; ring
  refine ⟨edgeScore G q R ω, ?_⟩
  have hgrid_mid : ∀ i < K,
      G.weightedMatchingCost M M_clean lam (edgeScore G q R ω) (-T + i * δ) +
        12 * ({e | -T + i * δ ≤ edgeScore G q R ω e ∧
          edgeScore G q R ω e < -T + (i + 1) * δ}.ncard : ℝ) ≤ B_tot := by
    intro i hi
    have hthr : -T + ((i : ℝ) + 1) * δ = grid i + δ := by dsimp only [grid]; ring
    have hgrid_eq : -T + (i : ℝ) * δ = grid i := rfl
    rw [hgrid_eq, hthr]
    have hnm := hmid i hi
    have hU_nm : ω ∉ deviation (unmatchedStraddleEvent G M q R (grid i)) c :=
      fun h_in => hnm.1 (Or.inl (Or.inl (Or.inl h_in)))
    have hA_nm : ω ∉ deviation (pairAnyEvent G M q R (grid i)) c :=
      fun h_in => hnm.1 (Or.inl (Or.inl (Or.inr h_in)))
    have hBd_nm : ω ∉ deviation (pairBothEvent G (M \ M_clean) q R (grid i)) c :=
      fun h_in => hnm.1 (Or.inl (Or.inr h_in))
    have hBc_nm : ω ∉ deviation (pairBothEvent G M_clean q R (grid i)) c :=
      fun h_in => hnm.1 (Or.inr h_in)
    have hU := ncard_lt_of_notMem_deviation hU_nm
    have hA := ncard_lt_of_notMem_deviation hA_nm
    have hBd := ncard_lt_of_notMem_deviation hBd_nm
    have hBc := ncard_lt_of_notMem_deviation hBc_nm
    have hW := ncard_lt_of_notMem_deviation hnm.2
    have hU_eq : {v | ω ∈ unmatchedStraddleEvent G M q R (grid i) v} =
        {v | v ∉ G.matchedVertices M ∧ G.EdgeStraddles (edgeScore G q R ω) (grid i) v} := by
      ext v; simp [unmatchedStraddleEvent, straddleEvent]
    have hA_eq : {e | ω ∈ pairAnyEvent G M q R (grid i) e} =
        {e | e ∈ M ∧ G.PairStraddlesAny (edgeScore G q R ω) (grid i) e} := by
      ext e; simp [pairAnyEvent]
    have hBd_eq : {e | ω ∈ pairBothEvent G (M \ M_clean) q R (grid i) e} =
        {e | e ∈ M \ M_clean ∧ G.PairStraddlesBoth (edgeScore G q R ω) (grid i) e} := by
      ext e; simp [pairBothEvent]
    have hBc_eq : {e | ω ∈ pairBothEvent G M_clean q R (grid i) e} =
        {e | e ∈ M_clean ∧ G.PairStraddlesBoth (edgeScore G q R ω) (grid i) e} := by
      ext e; simp [pairBothEvent]
    have hW_eq : {e | ω ∈ winEv i e} =
        {e | grid i ≤ edgeScore G q R ω e ∧ edgeScore G q R ω e < grid i + δ} := rfl
    rw [hU_eq] at hU; rw [hA_eq] at hA; rw [hBd_eq] at hBd; rw [hBc_eq] at hBc; rw [hW_eq] at hW
    have hWmean : ∑ e, P_meas.real (winEv i e) ≤ 3 / 2 * h * (δ / √(2 * π)) := by
      refine (Finset.sum_le_sum fun e _ =>
        measureReal_window_le (unit e) (grid i) hδpos.le).trans_eq ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hE]
    set t0 := grid i
    have hmean_unm : ∑ v : V, P_meas.real (unmatchedStraddleEvent G M q R t0 v) ≤
        ({v : V | v ∉ G.matchedVertices M}.ncard : ℝ) * straddleBound ρ₀ := by
      have hsub : ∑ v : V, P_meas.real (unmatchedStraddleEvent G M q R t0 v) ≤
          ∑ v : V, if v ∉ G.matchedVertices M then straddleBound ρ₀ else 0 := by
        refine Finset.sum_le_sum fun v _ => ?_
        unfold unmatchedStraddleEvent
        by_cases hv : v ∈ G.matchedVertices M
        · simp [hv]
        · simp only [hv, not_false_eq_true, ↓reduceIte]
          exact measureReal_straddleEvent_le hloop h3 hq (by linarith only [hρ_lo]) hρ_ker t0 v
      refine hsub.trans_eq ?_
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      congr 1
      have hcoe : ((Finset.univ.filter (· ∉ G.matchedVertices M) : Finset V) : Set V) =
          {v | v ∉ G.matchedVertices M} := by ext v; simp
      rw [← ncard_coe_finset, hcoe]
    have hmean_edges : (∑ e : E, P_meas.real (pairAnyEvent G M q R t0 e)) +
        (∑ e : E, P_meas.real (pairBothEvent G (M \ M_clean) q R t0 e)) +
        lam * (∑ e : E, P_meas.real (pairBothEvent G M_clean q R t0 e)) ≤
        2 * ((M \ M_clean).ncard : ℝ) * straddleBound ρ₀ +
          (M_clean.ncard : ℝ) *
            ((2 - 2 * lam) * (269265 / 1000000) + (2 * lam - 1) * (2 * straddleBound ρ₀)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      set cd := 2 * straddleBound ρ₀
      set cc := (2 - 2 * lam) * (269265 / 1000000 : ℝ) + (2 * lam - 1) * (2 * straddleBound ρ₀)
      have hpt_e : ∀ e : E, P_meas.real (pairAnyEvent G M q R t0 e) +
          P_meas.real (pairBothEvent G (M \ M_clean) q R t0 e) +
          lam * P_meas.real (pairBothEvent G M_clean q R t0 e) ≤
          (if e ∈ M \ M_clean then cd else 0) + (if e ∈ M_clean then cc else 0) := by
        intro e
        by_cases heM : e ∈ M
        · by_cases heC : e ∈ M_clean
          · have heD : e ∉ M \ M_clean := fun h => h.2 heC
            have hboth0 : P_meas.real (pairBothEvent G (M \ M_clean) q R t0 e) = 0 := by
              simp [pairBothEvent, heD]
            have hboth_eq : pairBothEvent G M_clean q R t0 e = pairBothEvent G M q R t0 e := by
              simp [pairBothEvent, heC, heM]
            rw [hboth0, add_zero, hboth_eq, ite_eq_right heD, zero_add, ite_eq_left heC]
            have hhalf := measureReal_pairHalf_le hloop h3 heM hq hρ_lo hρ_ker t0
            have hone := (measureReal_pairOne_le_straddle_add hloop h3 heM q R t0).trans
              (add_le_add
                (measureReal_straddleEvent_le hloop h3 hq (by linarith only [hρ_lo]) hρ_ker t0 _)
                (measureReal_straddleEvent_le hloop h3 hq (by linarith only [hρ_lo]) hρ_ker t0 _))
            have hid : P_meas.real (pairAnyEvent G M q R t0 e) +
                lam * P_meas.real (pairBothEvent G M q R t0 e) =
                (2 - 2 * lam) * (P_meas.real (pairAnyEvent G M q R t0 e) +
                  (1 / 2) * P_meas.real (pairBothEvent G M q R t0 e)) +
                (2 * lam - 1) * (P_meas.real (pairAnyEvent G M q R t0 e) +
                  P_meas.real (pairBothEvent G M q R t0 e)) := by ring
            rw [hid]; dsimp only [cc]
            have hle1 := mul_le_mul_of_nonneg_left hhalf
              (show 0 ≤ 2 - 2 * lam by linarith only [hlam1])
            have hle2 := mul_le_mul_of_nonneg_left hone
              (show 0 ≤ 2 * lam - 1 by linarith only [hlam_half])
            linarith only [hle1, hle2]
          · have heD : e ∈ M \ M_clean := ⟨heM, heC⟩
            have hboth0 : P_meas.real (pairBothEvent G M_clean q R t0 e) = 0 := by
              simp [pairBothEvent, heC]
            have hboth_eq : pairBothEvent G (M \ M_clean) q R t0 e =
                pairBothEvent G M q R t0 e := by simp [pairBothEvent, heD, heM]
            rw [hboth0, mul_zero, add_zero, hboth_eq, ite_eq_left heD, ite_eq_right heC, add_zero]
            have hone := (measureReal_pairOne_le_straddle_add hloop h3 heM q R t0).trans
              (add_le_add
                (measureReal_straddleEvent_le hloop h3 hq (by linarith only [hρ_lo]) hρ_ker t0 _)
                (measureReal_straddleEvent_le hloop h3 hq (by linarith only [hρ_lo]) hρ_ker t0 _))
            dsimp only [cd]; linarith only [hone]
        · have heC : e ∉ M_clean := fun h => heM (hclean h)
          have heD : e ∉ M \ M_clean := fun h => heM h.1
          simp [pairAnyEvent, pairBothEvent, heM, heC, heD]
      refine (Finset.sum_le_sum fun e _ => hpt_e e).trans_eq ?_
      rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul]
      have hc1 : ((Finset.univ.filter (· ∈ M \ M_clean) : Finset E) : Set E) = M \ M_clean := by
        ext e; simp
      have hc2 : ((Finset.univ.filter (· ∈ M_clean) : Finset E) : Set E) = M_clean := by
        ext e; simp
      rw [← ncard_coe_finset, hc1, ← ncard_coe_finset, hc2]
      dsimp only [cd, cc]; ring
    have hcount_id : ({v : V | v ∉ G.matchedVertices M}.ncard : ℝ) +
        2 * ((M \ M_clean).ncard : ℝ) = h - 2 * (M_clean.ncard : ℝ) := by
      have hmv := ncard_matchedVertices_eq_two_mul hloop hM
      have hcompl : (G.matchedVertices M).ncard + {v : V | v ∉ G.matchedVertices M}.ncard =
          Fintype.card V := by
        have hc : (G.matchedVertices M)ᶜ = {v : V | v ∉ G.matchedVertices M} := rfl
        rw [← hc, ncard_add_ncard_compl, Nat.card_eq_fintype_card]
      have hsdiff := ncard_sdiff_add_ncard_of_subset hclean (toFinite M)
      have hnat : {v : V | v ∉ G.matchedVertices M}.ncard + 2 * (M \ M_clean).ncard +
          2 * M_clean.ncard = Fintype.card V := by omega
      have hR : (({v : V | v ∉ G.matchedVertices M}.ncard + 2 * (M \ M_clean).ncard +
          2 * M_clean.ncard : ℕ) : ℝ) = (Fintype.card V : ℝ) := by exact_mod_cast hnat
      push_cast at hR; dsimp only [h]; linarith only [hR]
    have hmix_clean : (2 - 2 * lam) * (269265 / 1000000 : ℝ) +
        (2 * lam - 1) * (2 * straddleBound ρ₀) ≤
        271212 / 1000000 + (2 * lam - 1) * (ξ / 4) := by
      have hbase := clean_pair_convex_mix_le
      dsimp only at hbase
      have hmul := mul_le_mul_of_nonneg_left
        (show 2 * straddleBound ρ₀ ≤ 2 * gaussianCoefficient + ξ / 4 by linarith only [hstrad_le])
        (show 0 ≤ 2 * lam - 1 by linarith only [hlam_half])
      linarith only [hbase, hmul]
    have hexp_le : (∑ v : V, P_meas.real (unmatchedStraddleEvent G M q R t0 v)) +
        (∑ e : E, P_meas.real (pairAnyEvent G M q R t0 e)) +
        (∑ e : E, P_meas.real (pairBothEvent G (M \ M_clean) q R t0 e)) +
        lam * (∑ e : E, P_meas.real (pairBothEvent G M_clean q R t0 e)) ≤
        (h - 2 * M_clean.ncard) * gaussianCoefficient +
          (M_clean.ncard : ℝ) * (271212 / 1000000) + (ξ / 8) * h := by
      have hdirty_nonneg : 0 ≤ h - 2 * (M_clean.ncard : ℝ) := by linarith only [hm_clean_le_half]
      have h1 := mul_le_mul_of_nonneg_left hstrad_le hdirty_nonneg
      have h2 := mul_le_mul_of_nonneg_left hmix_clean (Nat.cast_nonneg M_clean.ncard)
      have h2lam_le_one : 2 * lam - 1 ≤ 1 := by linarith only [hlam1]
      have h3 : (M_clean.ncard : ℝ) * ((2 * lam - 1) * (ξ / 4)) ≤
          (M_clean.ncard : ℝ) * (ξ / 4) := by
        have htmp : (2 * lam - 1) * (ξ / 4) ≤ 1 * (ξ / 4) := by gcongr
        exact mul_le_mul_of_nonneg_left (by linarith only [htmp]) (Nat.cast_nonneg _)
      have hslack_cancel : (h - 2 * (M_clean.ncard : ℝ)) * (ξ / 8) +
          (M_clean.ncard : ℝ) * (ξ / 4) = (ξ / 8) * h := by ring
      have hcomb : ({v : V | v ∉ G.matchedVertices M}.ncard : ℝ) * straddleBound ρ₀ +
          2 * ((M \ M_clean).ncard : ℝ) * straddleBound ρ₀ =
          (h - 2 * (M_clean.ncard : ℝ)) * straddleBound ρ₀ := by
        rw [← add_mul, hcount_id]
      linarith only [hmean_unm, hmean_edges, hcomb, h1, h2, h3, hslack_cancel]
    unfold Multigraph.weightedMatchingCost
    have hlam_bc : lam * ({e | e ∈ M_clean ∧
        G.PairStraddlesBoth (edgeScore G q R ω) (grid i) e}.ncard : ℝ) ≤
        lam * (∑ e : E, P_meas.real (pairBothEvent G M_clean q R t0 e)) + c := by
      have h1 := mul_le_mul_of_nonneg_left hBc.le hlam0
      have h2 : lam * c ≤ c := mul_le_of_le_one_left hcpos.le hlam1
      dsimp only [t0]
      rw [mul_add] at h1
      linarith only [h1, h2]
    have hwin12 : 12 * (3 / 2 * h * (δ / √(2 * π))) = h * (18 * δ / √(2 * π)) := by ring
    have hwin_h : h * (18 * δ / √(2 * π)) ≤ (ξ / 2) * h := by
      have htmp := mul_le_mul_of_nonneg_left hwin_val hhpos.le
      dsimp only [δ]; linarith only [htmp]
    have hc_eps : 16 * c = (ξ / 4) * h := by dsimp only [c, ε]; ring
    have hξh_pos : 0 < ξ * h := mul_pos hξ hhpos
    dsimp only [B_tot]
    dsimp only [t0] at hexp_le
    rw [hcardV_eq]
    linarith only [hU, hA, hBd, hlam_bc, hW, hWmean, hwin12, hwin_h, hexp_le, hc_eps, hξh_pos]
  obtain ⟨σ, hσ⟩ := G.exists_u2_pairNode_layout hloop h3 hM hclean hlam0 hlam1
    (edgeScore G q R ω) hδpos K (a := -T) (B := B_tot)
    (tail (· < -T) (fun x hx => by
      rw [abs_of_neg (by linarith only [hx, hT])]; linarith only [hx]) hlo)
    (by rw [htop_eq]; exact tail (T ≤ ·) (fun x hx => hx.trans (le_abs_self x)) hhi) hgrid_mid
  refine ⟨σ, fun s => ?_⟩
  have hs := hσ s
  rwa [show 1 - lam = 2 - Real.logb 2 3 by dsimp only [lam]; ring] at hs

/-! ### Explicit rational lower bounds on the `U₂` coefficients -/

/-- **The `U₂` circuit-size coefficient is at least `4.6362` (`46362 / 10000`).** -/
theorem u2CircuitCoefficient_ge_46362 :
    (46362 / 10000 : ℝ) ≤
      1 + (1 - (2 * gaussianCoefficient - 271212 / 1000000)) /
        ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * gaussianCoefficient)) := by
  have hp_hi := two_mul_gaussianCoefficient_le
  have hp_lo := le_two_mul_gaussianCoefficient
  have hden_pos : 0 < (7 / 8 : ℝ) * (271212 / 1000000) + (1 / 8) * (2 * gaussianCoefficient) := by
    linarith
  rw [ ← sub_le_iff_le_add', le_div_iff₀ hden_pos]
  linarith

/-- **The `U₂` quadratic-form correlation threshold is at least `2.8007` (`28007 / 10000`).** -/
theorem u2CorrelationThreshold_ge_28007 :
    (28007 / 10000 : ℝ) ≤
      1 + (1 / 2 - (2 * gaussianCoefficient - 271212 / 1000000)) /
        ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * gaussianCoefficient)) := by
  have hp_hi := two_mul_gaussianCoefficient_le
  have hp_lo := le_two_mul_gaussianCoefficient
  have hden_pos : 0 < (7 / 8 : ℝ) * (271212 / 1000000) + (1 / 8) * (2 * gaussianCoefficient) := by
    linarith
  rw [← sub_le_iff_le_add', le_div_iff₀ hden_pos]
  linarith

end Cslib.Circuits.Frontier.Gaussian
