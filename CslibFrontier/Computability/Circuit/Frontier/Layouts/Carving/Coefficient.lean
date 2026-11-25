/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Switched.Coefficient
public import CslibFrontier.Foundations.Probability.Gaussian.CDF
import CslibFrontier.Foundations.Probability.Gaussian.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The carving-width coefficient and its numerical bound `0.137432 < c₃`

At threshold `t ≤ 0`, an off-median Gaussian edge-score cut followed by greedy `1`-vertex flips and
symmetric (`t = 0`) Gaussian bisections achieves carving-width per vertex bounded by
`carvingAt t`, the larger of:

* the level-zero straddling cut `exp (-t ^ 2 / 2) * gaussianCoefficient`, and
* the depth-one Lyapunov potential
  `gaussianCoefficient * (1 - Φ(t)) + (1 / 2 - 2 / 3 * gaussianCoefficient) * exp (-t ^ 2 / 2) *
  gaussianCoefficient`,

where `Φ = cdf (gaussianReal 0 1)` and `gaussianCoefficient = (3 / (2π)) arccos ((1 + 2√2) / 4)`.
The *carving coefficient* `carvingCoefficient` is the infimum of `carvingAt t` over `t ≤ 0`.

Evaluating at `t₀ = -2050219 / 10000000` using Taylor bounds on `exp` and `Φ`, rational bounds on
`√2` and `π`, and cosine-doubling steps gives

`carvingCoefficient ≤ 137432 / 1000000 = 0.137432 < switchedCoefficient`
(`c₃ = (3 / (4π)) arccos (5 / 6)`).

## Main definitions

* `Cslib.Circuits.Frontier.Carving.carvingAt`: the carving-width bound per vertex at level-zero
  threshold `t`.
* `Cslib.Circuits.Frontier.Carving.carvingCoefficient`: `⨅ t : {t : ℝ // t ≤ 0}, carvingAt t`.

## Main results

* `Cslib.Circuits.Frontier.Carving.carvingCoefficient_pos`: `0 < carvingCoefficient`.
* `Cslib.Circuits.Frontier.Carving.carvingCoefficient_le_137432`:
  `carvingCoefficient ≤ 137432 / 1000000`.
* `Cslib.Circuits.Frontier.Carving.switchedCoefficient_ge_139821`:
  `139821 / 1000000 ≤ Switched.switchedCoefficient`.
* `Cslib.Circuits.Frontier.Carving.carvingCoefficient_lt_switchedCoefficient`:
  `carvingCoefficient < Switched.switchedCoefficient`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set

namespace Cslib.Circuits.Frontier.Carving

open Cslib.Circuits.Frontier.Gaussian Cslib.Circuits.Frontier.Switched

/-- The carving-width bound per vertex obtained by cutting at threshold `t` at level zero and
bisecting symmetrically at deeper levels. -/
@[expose] noncomputable def carvingAt (t : ℝ) : ℝ :=
  max (exp (-t ^ 2 / 2) * gaussianCoefficient)
    (gaussianCoefficient * (1 - cdf (gaussianReal 0 1) t) +
      (1 / 2 - 2 / 3 * gaussianCoefficient) * (exp (-t ^ 2 / 2) * gaussianCoefficient))

/-- The cubic carving-width coefficient: the infimum of `carvingAt t` over nonpositive thresholds
`t ≤ 0`. -/
noncomputable def carvingCoefficient : ℝ :=
  ⨅ t : {t : ℝ // t ≤ 0}, carvingAt t.1

/-- `carvingAt t` is bounded below by `(1 / 2) * gaussianCoefficient` for every `t ≤ 0`. -/
theorem half_mul_gaussianCoefficient_le_carvingAt {t : ℝ} (ht : t ≤ 0) :
    1 / 2 * gaussianCoefficient ≤ carvingAt t := by
  have hcdf : cdf (gaussianReal 0 1) t ≤ 1 / 2 := by
    have h0 : cdf (gaussianReal 0 1) 0 = 2⁻¹ := cdf_gaussianReal_zero_zero one_ne_zero
    have hmono := (strictMono_cdf_gaussianReal 0 one_ne_zero).monotone ht
    linarith
  have hp_pos := gaussianCoefficient_pos
  have hp_le : gaussianCoefficient ≤ 3 / 4 := by
    unfold gaussianCoefficient
    have harc : arccos ((1 + 2 * √2) / 4) ≤ π / 2 := arccos_le_pi_div_two.mpr (by positivity)
    have hpi := pi_pos
    calc 3 / (2 * π) * arccos ((1 + 2 * √2) / 4) ≤ 3 / (2 * π) * (π / 2) := by gcongr
      _ = 3 / 4 := by field_simp; ring
  have hnonneg : 0 ≤ (1 / 2 - 2 / 3 * gaussianCoefficient) *
      (exp (-t ^ 2 / 2) * gaussianCoefficient) :=
    mul_nonneg (by linarith) (mul_nonneg (exp_pos _).le hp_pos.le)
  refine le_trans ?_ (le_max_right _ _)
  nlinarith

/-- `carvingAt` is bounded below on `{t // t ≤ 0}`. -/
theorem bddBelow_carvingAt : BddBelow (range fun t : {t : ℝ // t ≤ 0} => carvingAt t.1) :=
  ⟨1 / 2 * gaussianCoefficient, by
    rintro _ ⟨t, rfl⟩; exact half_mul_gaussianCoefficient_le_carvingAt t.2⟩

/-- For any `t ≤ 0`, `carvingCoefficient ≤ carvingAt t`. -/
theorem carvingCoefficient_le_carvingAt {t : ℝ} (ht : t ≤ 0) :
    carvingCoefficient ≤ carvingAt t :=
  ciInf_le bddBelow_carvingAt ⟨t, ht⟩

/-- `carvingCoefficient` is strictly positive (at least `1 / 40`). -/
theorem carvingCoefficient_ge : 1 / 40 ≤ carvingCoefficient := by
  have : Nonempty {t : ℝ // t ≤ 0} := ⟨⟨0, le_rfl⟩⟩
  have h1 : (1 / 40 : ℝ) ≤ 1 / 2 * gaussianCoefficient := by linarith [gaussianCoefficient_ge]
  exact h1.trans (le_ciInf fun t => half_mul_gaussianCoefficient_le_carvingAt t.2)

/-- `carvingCoefficient > 0`. -/
theorem carvingCoefficient_pos : 0 < carvingCoefficient :=
  lt_of_lt_of_le (by norm_num) carvingCoefficient_ge

/-! ### Alternating Maclaurin envelopes and numerical bounds -/

/-- A function vanishing at `0` whose derivative is nonnegative on `[0, ∞)` is nonnegative there. -/
private theorem nonneg_of_hasDerivAt_of_nonneg {f g : ℝ → ℝ} (hd : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ t ≥ 0, 0 ≤ g t) (h0 : f 0 = 0) : ∀ t ≥ 0, 0 ≤ f t := by
  have hmono : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x hx => hg x (interior_subset hx))
  intro t ht
  exact h0 ▸ hmono (le_rfl : (0 : ℝ) ∈ Ici 0) ht ht

/-- Half-angle sine Maclaurin bounds on `[0, ∞)`:
`t - t^3/6 + t^5/120 - t^7/5040 ≤ sin t ≤ t - t^3/6 + t^5/120`. -/
private theorem sin_maclaurin_bounds {t : ℝ} (ht : 0 ≤ t) :
    t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 ≤ sin t ∧
      sin t ≤ t - t ^ 3 / 6 + t ^ 5 / 120 := by
  have hc4 : ∀ x ≥ 0, 0 ≤ (1 - x ^ 2 / 2 + x ^ 4 / 24) - cos x :=
    nonneg_of_hasDerivAt_of_nonneg
      (f := fun x => (1 - x ^ 2 / 2 + x ^ 4 / 24) - cos x)
      (g := fun x => sin x - (x - x ^ 3 / 6))
      (fun x => (((((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_pow 2 x).div_const 2)).add
        ((hasDerivAt_pow 4 x).div_const 24)).sub (hasDerivAt_cos x)).congr_deriv (by ring)))
      (fun x hx => by linarith [sin_ge_sub_cube hx]) (by simp)
  have hs5 : ∀ x ≥ 0, 0 ≤ (x - x ^ 3 / 6 + x ^ 5 / 120) - sin x :=
    nonneg_of_hasDerivAt_of_nonneg
      (f := fun x => (x - x ^ 3 / 6 + x ^ 5 / 120) - sin x)
      (g := fun x => (1 - x ^ 2 / 2 + x ^ 4 / 24) - cos x)
      (fun x => (((((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
        ((hasDerivAt_pow 5 x).div_const 120)).sub (hasDerivAt_sin x)).congr_deriv (by ring)))
      hc4 (by simp)
  have hc6 : ∀ x ≥ 0, 0 ≤ cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) :=
    nonneg_of_hasDerivAt_of_nonneg
      (f := fun x => cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720))
      (g := fun x => (x - x ^ 3 / 6 + x ^ 5 / 120) - sin x)
      (fun x => ((hasDerivAt_cos x).sub
        ((((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_pow 2 x).div_const 2)).add
          ((hasDerivAt_pow 4 x).div_const 24)).sub
          ((hasDerivAt_pow 6 x).div_const 720))).congr_deriv (by ring))
      hs5 (by simp)
  have hs7 : ∀ x ≥ 0, 0 ≤ sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) :=
    nonneg_of_hasDerivAt_of_nonneg
      (f := fun x => sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040))
      (g := fun x => cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720))
      (fun x => ((hasDerivAt_sin x).sub
        ((((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
          ((hasDerivAt_pow 5 x).div_const 120)).sub
          ((hasDerivAt_pow 7 x).div_const 5040))).congr_deriv (by ring))
      hc6 (by simp)
  exact ⟨by linarith [hs7 t ht], by linarith [hs5 t ht]⟩

private theorem arccos_le_of_sin_lo {r x : ℝ} (hx0 : 0 ≤ x) (hx3 : x ≤ 3)
    (h0 : 0 ≤ (x / 2) - (x / 2) ^ 3 / 6 + (x / 2) ^ 5 / 120 - (x / 2) ^ 7 / 5040)
    (h : 1 - 2 * ((x / 2) - (x / 2) ^ 3 / 6 + (x / 2) ^ 5 / 120 - (x / 2) ^ 7 / 5040) ^ 2 ≤ r) :
    arccos r ≤ x := by
  have hsq := pow_le_pow_left₀ h0 (sin_maclaurin_bounds (t := x / 2) (by linarith)).1 2
  have hcos : cos x ≤ r := by
    rw [show x = 2 * (x / 2) by ring, cos_two_mul']
    linarith [sin_sq_add_cos_sq (x / 2)]
  exact (arccos_le_arccos hcos).trans_eq (arccos_cos hx0 (by linarith [pi_gt_three]))

private theorem le_arccos_of_sin_hi {r x : ℝ} (hx0 : 0 ≤ x) (hx3 : x ≤ 3)
    (h : r ≤ 1 - 2 * ((x / 2) - (x / 2) ^ 3 / 6 + (x / 2) ^ 5 / 120) ^ 2) :
    x ≤ arccos r := by
  have hsin0 : 0 ≤ sin (x / 2) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_gt_three])
  have hsq := pow_le_pow_left₀ hsin0 (sin_maclaurin_bounds (t := x / 2) (by linarith)).2 2
  have hcos : r ≤ cos x := by
    rw [show x = 2 * (x / 2) by ring, cos_two_mul']
    linarith [sin_sq_add_cos_sq (x / 2)]
  exact (arccos_cos hx0 (by linarith [pi_gt_three])).symm.trans_le (arccos_le_arccos hcos)

/-- Sharp upper bound `arccos ((1 + 2√2) / 4) ≤ 2939503850 / 10^10`. -/
private theorem arccos_edgeCorr_le :
    arccos ((1 + 2 * √2) / 4) ≤ 2939503850 / 10000000000 := by
  have hsqrt : (141421356237309 : ℝ) / 100000000000000 < √2 :=
    (lt_sqrt (by norm_num)).mpr (by norm_num)
  refine arccos_le_of_sin_lo (by norm_num) (by norm_num) (by norm_num) ?_
  have hnum : 1 - 2 * ((2939503850 / 10000000000 : ℝ) / 2 -
      ((2939503850 / 10000000000 : ℝ) / 2) ^ 3 / 6 +
      ((2939503850 / 10000000000 : ℝ) / 2) ^ 5 / 120 -
      ((2939503850 / 10000000000 : ℝ) / 2) ^ 7 / 5040) ^ 2 ≤
      (1 + 2 * (141421356237309 / 100000000000000 : ℝ)) / 4 := by norm_num
  linarith

/-- Sharp lower bound `29395035 / 10^8 ≤ arccos ((1 + 2√2) / 4)`. -/
private theorem le_arccos_edgeCorr :
    (29395035 / 100000000 : ℝ) ≤ arccos ((1 + 2 * √2) / 4) := by
  have hsqrt : √2 < (141421356237310 : ℝ) / 100000000000000 :=
    (sqrt_lt' (by norm_num)).mpr (by norm_num)
  refine le_arccos_of_sin_hi (by norm_num) (by norm_num) ?_
  have hnum : (1 + 2 * (141421356237310 / 100000000000000 : ℝ)) / 4 ≤
      1 - 2 * ((29395035 / 100000000 : ℝ) / 2 -
        ((29395035 / 100000000 : ℝ) / 2) ^ 3 / 6 +
        ((29395035 / 100000000 : ℝ) / 2) ^ 5 / 120) ^ 2 := by norm_num
  linarith

/-- Sharp rational bounds on `gaussianCoefficient`:
`14035095 / 10^8 ≤ gaussianCoefficient ≤ 140350971 / 10^9`. -/
private theorem gaussianCoefficient_bounds :
    14035095 / 100000000 ≤ gaussianCoefficient ∧ gaussianCoefficient ≤ 140350971 / 1000000000 := by
  have hpi_lo : (314159265358979 : ℝ) / 100000000000000 < π := by linarith [pi_gt_d20]
  have hpi_hi : π < (314159265358980 : ℝ) / 100000000000000 := by linarith [pi_lt_d20]
  unfold gaussianCoefficient
  rw [div_mul_eq_mul_div]
  have hlo : 3 * (29395035 / 100000000) / (2 * (314159265358980 / 100000000000000)) ≤
      3 * arccos ((1 + 2 * √2) / 4) / (2 * π) :=
    div_le_div₀ (mul_nonneg (by norm_num) (arccos_nonneg _))
      (mul_le_mul_of_nonneg_left le_arccos_edgeCorr (by norm_num))
      (by linarith) (by linarith)
  have hhi : 3 * arccos ((1 + 2 * √2) / 4) / (2 * π) ≤
      3 * (2939503850 / 10000000000) / (2 * (314159265358979 / 100000000000000)) :=
    div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left arccos_edgeCorr_le (by norm_num))
      (by norm_num) (by linarith)
  exact ⟨by norm_num at hlo; linarith, by norm_num at hhi; linarith⟩

private noncomputable def expNegTaylor (n : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (-y) ^ k / k.factorial

private theorem hasDerivAt_expNegTaylor (n : ℕ) (t : ℝ) :
    HasDerivAt (expNegTaylor (n + 1)) (-expNegTaylor n t) t := by
  have hd : ∀ k ∈ Finset.range (n + 1),
      HasDerivAt (fun x : ℝ => (-x) ^ (k + 1) / (k + 1).factorial)
        (-((-t) ^ k / k.factorial)) t := fun k _ => by
    have h1 : HasDerivAt (fun x : ℝ => (-x) ^ (k + 1)) (-((k : ℝ) + 1) * (-t) ^ k) t :=
      ((hasDerivAt_neg t).pow (k + 1)).congr_deriv (by push_cast; ring)
    refine (h1.div_const ((k + 1).factorial : ℝ)).congr_deriv ?_
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hpos : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hpos]
  have hfun : expNegTaylor (n + 1) =
      fun x : ℝ => 1 + ∑ k ∈ Finset.range (n + 1), (-x) ^ (k + 1) / (k + 1).factorial := by
    funext x
    unfold expNegTaylor
    rw [Finset.sum_range_succ']
    simp [add_comm]
  rw [hfun]
  exact ((hasDerivAt_const t (1 : ℝ)).add (HasDerivAt.fun_sum hd)).congr_deriv
    (by unfold expNegTaylor; rw [Finset.sum_neg_distrib, zero_add])

/-- Alternating Maclaurin remainder sign for `exp (-y)` on `[0, ∞)`: odd-degree partial sums
under-approximate `exp (-y)` and even-degree partial sums over-approximate it. -/
private theorem exp_neg_taylor_nonneg : ∀ (n : ℕ) {y : ℝ}, 0 ≤ y →
    0 ≤ (-1 : ℝ) ^ (n + 1) * (exp (-y) - expNegTaylor n y)
  | 0, y, hy => by
    unfold expNegTaylor
    simp only [zero_add, Finset.sum_range_one, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, pow_one]
    linarith [exp_le_one_iff.mpr (neg_nonpos.mpr hy)]
  | n + 1, y, hy => by
    refine nonneg_of_hasDerivAt_of_nonneg
      (f := fun t => (-1 : ℝ) ^ (n + 2) * (exp (-t) - expNegTaylor (n + 1) t))
      (g := fun t => (-1 : ℝ) ^ (n + 1) * (exp (-t) - expNegTaylor n t)) (fun t => ?_)
      (fun t ht => exp_neg_taylor_nonneg n ht)
      (by unfold expNegTaylor; rw [Finset.sum_range_succ']; simp) y hy
    have hexp : HasDerivAt (fun x => exp (-x)) (-exp (-t)) t :=
      (hasDerivAt_neg t).exp.congr_deriv (by ring)
    exact (HasDerivAt.const_mul ((-1 : ℝ) ^ (n + 2))
      (hexp.sub (hasDerivAt_expNegTaylor n t))).congr_deriv
      (by rw [pow_succ (-1 : ℝ) (n + 1)]; ring)

private noncomputable def cdfTaylor (n : ℕ) (a : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (-2⁻¹ : ℝ) ^ k / ((k.factorial : ℝ) * (2 * k + 1)) * a ^ (2 * k + 1)

/-- Alternating polynomial envelope for `cdf (gaussianReal 0 1) a` on `0 ≤ a` obtained by
integrating `exp_neg_taylor_nonneg` at `y = u ^ 2 / 2`. -/
private theorem cdf_gaussianReal_taylor_nonneg (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ (-1 : ℝ) ^ (n + 1) *
      (cdf (gaussianReal 0 1) a - (1 / 2 + (√(2 * π))⁻¹ * cdfTaylor n a)) := by
  have hsplit : cdf (gaussianReal 0 1) a =
      1 / 2 + (√(2 * π))⁻¹ * ∫ u in (0 : ℝ)..a, exp (-u ^ 2 / 2) := by
    rw [cdf_gaussianReal_eq_integral 0 one_ne_zero a,
      ← Iic_union_Ioc_eq_Iic ha,
      setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
        (integrable_gaussianPDFReal 0 1).integrableOn
        (integrable_gaussianPDFReal 0 1).integrableOn,
      ← cdf_gaussianReal_eq_integral 0 one_ne_zero 0,
      cdf_gaussianReal_zero_zero one_ne_zero,
      ← intervalIntegral.integral_of_le ha]
    have hpdf : (fun u => gaussianPDFReal 0 1 u) = fun u => (√(2 * π))⁻¹ * exp (-u ^ 2 / 2) := by
      funext u; simp [gaussianPDFReal_def]
    rw [hpdf, intervalIntegral.integral_const_mul]
    ring
  have hQ_deriv : ∀ u ∈ uIcc 0 a, HasDerivAt (cdfTaylor n) (expNegTaylor n (u ^ 2 / 2)) u := by
    intro u _
    unfold cdfTaylor expNegTaylor
    refine HasDerivAt.fun_sum fun k _ => ?_
    have h1 := HasDerivAt.const_mul ((-2⁻¹ : ℝ) ^ k / ((k.factorial : ℝ) * (2 * k + 1)))
      (hasDerivAt_pow (2 * k + 1) u)
    refine h1.congr_deriv ?_
    have hpos : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have hpow : (-2⁻¹ : ℝ) ^ k * u ^ (2 * k) = (-(u ^ 2 / 2)) ^ k := by
      rw [pow_mul, ← mul_pow]; congr 1; ring
    push_cast
    calc (-2⁻¹ : ℝ) ^ k / ((k.factorial : ℝ) * (2 * k + 1)) * ((2 * k + 1) * u ^ (2 * k))
        = (-2⁻¹ : ℝ) ^ k * u ^ (2 * k) / k.factorial := by field_simp [hpos]
      _ = (-(u ^ 2 / 2)) ^ k / k.factorial := by rw [hpow]
  have hP_cont : Continuous fun u : ℝ => expNegTaylor n (u ^ 2 / 2) := by
    unfold expNegTaylor; fun_prop
  have hint_Q : ∫ u in (0 : ℝ)..a, expNegTaylor n (u ^ 2 / 2) = cdfTaylor n a := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hQ_deriv (hP_cont.intervalIntegrable 0 a)]
    unfold cdfTaylor; simp
  have hint_diff : ∫ u in (0 : ℝ)..a,
      (-1 : ℝ) ^ (n + 1) * (exp (-u ^ 2 / 2) - expNegTaylor n (u ^ 2 / 2)) =
      (-1 : ℝ) ^ (n + 1) * ((∫ u in (0 : ℝ)..a, exp (-u ^ 2 / 2)) - cdfTaylor n a) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub
        ((by fun_prop : Continuous fun u : ℝ => exp (-u ^ 2 / 2)).intervalIntegrable 0 a)
        (hP_cont.intervalIntegrable 0 a), hint_Q]
  have hnn : 0 ≤ ∫ u in (0 : ℝ)..a,
      (-1 : ℝ) ^ (n + 1) * (exp (-u ^ 2 / 2) - expNegTaylor n (u ^ 2 / 2)) := by
    refine intervalIntegral.integral_nonneg ha fun u _ => ?_
    simpa [neg_div] using exp_neg_taylor_nonneg n (show 0 ≤ u ^ 2 / 2 by positivity)
  rw [hint_diff] at hnn
  rw [hsplit]
  linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (√(2 * π))⁻¹) hnn]

/-- Upper bound on `cdf (gaussianReal 0 1) a` for `0 ≤ a` from the degree-`4` Taylor envelope. -/
private theorem cdf_gaussianReal_le_poly {a : ℝ} (ha : 0 ≤ a) :
    cdf (gaussianReal 0 1) a ≤
      1 / 2 + (√(2 * π))⁻¹ * (a - a ^ 3 / 6 + a ^ 5 / 40 - a ^ 7 / 336 + a ^ 9 / 3456) := by
  have h := cdf_gaussianReal_taylor_nonneg 4 ha
  have h4 : cdfTaylor 4 a = a - a ^ 3 / 6 + a ^ 5 / 40 - a ^ 7 / 336 + a ^ 9 / 3456 := by
    unfold cdfTaylor
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
    ring
  rw [h4, show (-1 : ℝ) ^ (4 + 1) = -1 by norm_num] at h
  linarith

/-- Quartic lower bound `1 + y + y^2/2 + y^3/6 + y^4/24 ≤ exp y` for `0 ≤ y`. -/
private theorem quartic_le_exp {y : ℝ} (hy : 0 ≤ y) :
    1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 ≤ exp y := by
  have h := Real.sum_le_exp_of_nonneg hy 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  linarith

/-- **The sharp rational bound on the carving coefficient:**
`carvingCoefficient ≤ 137432 / 1000000 = 0.137432`. -/
theorem carvingCoefficient_le_137432 : carvingCoefficient ≤ 137432 / 1000000 := by
  set a : ℝ := 2050219 / 10000000
  have ha_pos : 0 < a := by norm_num [a]
  refine (carvingCoefficient_le_carvingAt (t := -a) (by linarith)).trans ?_
  unfold carvingAt
  obtain ⟨hpg_lo, hpg_hi⟩ := gaussianCoefficient_bounds
  have hpg_pos := gaussianCoefficient_pos
  set y : ℝ := a ^ 2 / 2
  set E_lo : ℝ := 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24
  have hE_pos : 0 < E_lo := by norm_num [E_lo, y, a]
  have hexp_hi : exp (-(-a) ^ 2 / 2) ≤ E_lo⁻¹ := by
    rw [show -(-a) ^ 2 / 2 = -y by dsimp [y]; ring, exp_neg]
    exact inv_anti₀ hE_pos (quartic_le_exp (by positivity))
  have hcdf_symm : 1 - cdf (gaussianReal 0 1) (-a) = cdf (gaussianReal 0 1) a := by
    rw [cdf_gaussianReal_neg one_ne_zero a]; ring
  have hsqrt_2pi : (250662827463099 : ℝ) / 100000000000000 ≤ √(2 * π) :=
    (le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [pi_gt_d20])
  have hcdf_hi : 1 - cdf (gaussianReal 0 1) (-a) ≤
      1 / 2 + ((250662827463099 : ℝ) / 100000000000000)⁻¹ *
        (a - a ^ 3 / 6 + a ^ 5 / 40 - a ^ 7 / 336 + a ^ 9 / 3456) := by
    rw [hcdf_symm]
    refine (cdf_gaussianReal_le_poly ha_pos.le).trans ?_
    have hpoly_pos : 0 ≤ a - a ^ 3 / 6 + a ^ 5 / 40 - a ^ 7 / 336 + a ^ 9 / 3456 := by
      norm_num [a]
    gcongr
  have hprod_hi : exp (-(-a) ^ 2 / 2) * gaussianCoefficient ≤
      E_lo⁻¹ * (140350971 / 1000000000) :=
    mul_le_mul hexp_hi hpg_hi hpg_pos.le (inv_pos.mpr hE_pos).le
  refine max_le (hprod_hi.trans (by norm_num [E_lo, y, a])) ?_
  have hterm1 : gaussianCoefficient * (1 - cdf (gaussianReal 0 1) (-a)) ≤
      (140350971 / 1000000000) *
        (1 / 2 + ((250662827463099 : ℝ) / 100000000000000)⁻¹ *
          (a - a ^ 3 / 6 + a ^ 5 / 40 - a ^ 7 / 336 + a ^ 9 / 3456)) :=
    mul_le_mul hpg_hi hcdf_hi (by rw [hcdf_symm]; exact cdf_nonneg _ _) (by norm_num)
  have hterm2 : (1 / 2 - 2 / 3 * gaussianCoefficient) *
        (exp (-(-a) ^ 2 / 2) * gaussianCoefficient) ≤
      (1 / 2 - 2 / 3 * (14035095 / 100000000)) * (E_lo⁻¹ * (140350971 / 1000000000)) :=
    mul_le_mul (by linarith) hprod_hi (mul_nonneg (exp_pos _).le hpg_pos.le) (by norm_num)
  exact (add_le_add hterm1 hterm2).trans (by norm_num [E_lo, y, a])

/-- Lower bound `139821 / 1000000 ≤ Switched.switchedCoefficient` (`c₃ ≈ 0.13982212`). -/
theorem switchedCoefficient_ge_139821 : (139821 / 1000000 : ℝ) ≤ switchedCoefficient := by
  have harc : (585685 / 1000000 : ℝ) ≤ arccos (5 / 6) :=
    le_arccos_of_sin_hi (by norm_num) (by norm_num) (by norm_num)
  unfold switchedCoefficient
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith [pi_lt_d20]

/-- **Strict improvement over Gaspers' switched pathwidth constant `c₃`:**
`carvingCoefficient ≤ 0.137432 < 0.139821 ≤ switchedCoefficient`. -/
theorem carvingCoefficient_lt_switchedCoefficient :
    carvingCoefficient < switchedCoefficient :=
  carvingCoefficient_le_137432.trans_lt (lt_of_lt_of_le (by norm_num) switchedCoefficient_ge_139821)

/-! ### Localization of the optimal threshold to `[-3 / 10, 0]` -/

/-- Convenient strict upper bound `gaussianCoefficient < 3 / 20`. -/
theorem gaussianCoefficient_lt_three_twentieths : gaussianCoefficient < 3 / 20 :=
  gaussianCoefficient_bounds.2.trans_lt (by norm_num)

private noncomputable abbrev cdfPolyLo (a : ℝ) : ℝ :=
  a - a ^ 3 / 6 + a ^ 5 / 40 - a ^ 7 / 336 + a ^ 9 / 3456 - a ^ 11 / 42240 +
    a ^ 13 / 599040 - a ^ 15 / 9676800

private noncomputable abbrev expPolyLo (y : ℝ) : ℝ :=
  1 - y + y ^ 2 / 2 - y ^ 3 / 6 + y ^ 4 / 24 - y ^ 5 / 120 + y ^ 6 / 720 - y ^ 7 / 5040

/-- Alternating degree-`7` Taylor lower bound for `exp (-y)` on `0 ≤ y`. -/
private theorem exp_neg_ge_septic {y : ℝ} (hy : 0 ≤ y) : expPolyLo y ≤ exp (-y) := by
  have h := exp_neg_taylor_nonneg 7 hy
  have h7 : expNegTaylor 7 y = expPolyLo y := by
    unfold expNegTaylor expPolyLo
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
    ring
  rw [h7, show (-1 : ℝ) ^ (7 + 1) = 1 by norm_num] at h
  linarith

/-- Lower bound on `1 - cdf (gaussianReal 0 1) t` for `t ≤ b ≤ 0` via the degree-`7` envelope. -/
private theorem one_sub_cdf_ge_of_le {t b : ℝ} (htb : t ≤ b) (hb0 : b ≤ 0)
    (hc0 : 0 ≤ cdfPolyLo (-b)) :
    1 / 2 + (2506629 / 1000000 : ℝ)⁻¹ * cdfPolyLo (-b) ≤ 1 - cdf (gaussianReal 0 1) t := by
  have hcdf_ge : 1 / 2 + (√(2 * π))⁻¹ * cdfPolyLo (-b) ≤ cdf (gaussianReal 0 1) (-b) := by
    have h := cdf_gaussianReal_taylor_nonneg 7 (show 0 ≤ -b by linarith)
    have h7 : cdfTaylor 7 (-b) = cdfPolyLo (-b) := by
      unfold cdfTaylor cdfPolyLo
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num
      ring
    rw [h7, show (-1 : ℝ) ^ (7 + 1) = 1 by norm_num] at h
    linarith
  have hsqrt_pos : 0 < √(2 * π) := sqrt_pos.mpr (by positivity)
  have hsqrt_hi : √(2 * π) ≤ 2506629 / 1000000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [pi_lt_d20]⟩
  have hcdf_tb := (strictMono_cdf_gaussianReal 0 one_ne_zero).monotone htb
  have hsymm := cdf_gaussianReal_neg one_ne_zero (-b)
  rw [neg_neg] at hsymm
  calc 1 / 2 + (2506629 / 1000000 : ℝ)⁻¹ * cdfPolyLo (-b)
      ≤ 1 / 2 + (√(2 * π))⁻¹ * cdfPolyLo (-b) := by gcongr
    _ ≤ cdf (gaussianReal 0 1) (-b) := hcdf_ge
    _ ≤ 1 - cdf (gaussianReal 0 1) t := by linarith

private theorem carvingAt_gt_on_Icc {a b t : ℝ} (ht : t ∈ Icc a b)
    (hcert : b ≤ 0 ∧ 0 ≤ expPolyLo (a ^ 2 / 2) ∧ 0 ≤ cdfPolyLo (-b) ∧
      138 / 1000 <
        (140350 / 1000000) * (1 / 2 + (2506629 / 1000000)⁻¹ * cdfPolyLo (-b)) +
          (1 / 2 - 2 / 3 * (140352 / 1000000)) * (expPolyLo (a ^ 2 / 2) * (140350 / 1000000))) :
    138 / 1000 < carvingAt t := by
  rcases hcert with ⟨hb0, he0, hc0, hval⟩
  obtain ⟨hp_lo', hp_hi'⟩ := gaussianCoefficient_bounds
  have hp_lo : 140350 / 1000000 ≤ gaussianCoefficient := by linarith
  have hp_hi : gaussianCoefficient ≤ 140352 / 1000000 := by linarith
  have hcdf_lo := one_sub_cdf_ge_of_le ht.2 hb0 hc0
  have hexp_lo : expPolyLo (a ^ 2 / 2) ≤ exp (-t ^ 2 / 2) := by
    have hsq : t ^ 2 ≤ a ^ 2 := by nlinarith [ht.1, ht.2]
    exact (exp_neg_ge_septic (by positivity)).trans (exp_le_exp.mpr (by linarith))
  refine hval.trans_le ((add_le_add ?_ ?_).trans (le_max_right _ _))
  · exact mul_le_mul hp_lo hcdf_lo (by positivity) gaussianCoefficient_pos.le
  · have hprod : expPolyLo (a ^ 2 / 2) * (140350 / 1000000) ≤
        exp (-t ^ 2 / 2) * gaussianCoefficient :=
      mul_le_mul hexp_lo hp_lo (by norm_num) (exp_pos _).le
    exact mul_le_mul (by linarith) hprod (mul_nonneg he0 (by norm_num)) (by linarith)

/-- For every threshold `t < -3 / 10`, `138 / 1000 < carvingAt t` (`> carvingCoefficient`). -/
private theorem carvingAt_gt_of_lt_neg_three_tenths {t : ℝ} (ht : t < -3 / 10) :
    138 / 1000 < carvingAt t := by
  rcases le_or_gt t (-23 / 10) with h23 | h23
  · obtain ⟨hp_lo', hp_hi'⟩ := gaussianCoefficient_bounds
    have hp_lo : 140350 / 1000000 ≤ gaussianCoefficient := by linarith
    have hc0 : 0 ≤ cdfPolyLo (-(-23 / 10)) := by dsimp only [cdfPolyLo]; norm_num
    have hcdf_lo := one_sub_cdf_ge_of_le h23 (by norm_num) hc0
    have hnonneg : 0 ≤ (1 / 2 - 2 / 3 * gaussianCoefficient) *
        (exp (-t ^ 2 / 2) * gaussianCoefficient) :=
      mul_nonneg (by linarith) (mul_nonneg (exp_pos _).le gaussianCoefficient_pos.le)
    have hnum : (138 / 1000 : ℝ) <
        (140350 / 1000000) * (1 / 2 + (2506629 / 1000000)⁻¹ * cdfPolyLo (-(-23 / 10))) := by
      dsimp only [cdfPolyLo]; norm_num
    have hm := mul_le_mul hp_lo hcdf_lo (by positivity) gaussianCoefficient_pos.le
    exact hnum.trans_le ((show _ ≤ _ by linarith).trans (le_max_right _ _))
  rcases le_or_gt t (-2) with h20 | h20
  · exact carvingAt_gt_on_Icc ⟨h23.le, h20⟩ (by dsimp only [expPolyLo, cdfPolyLo]; norm_num)
  rcases le_or_gt t (-17 / 10) with h17 | h17
  · exact carvingAt_gt_on_Icc ⟨h20.le, h17⟩ (by dsimp only [expPolyLo, cdfPolyLo]; norm_num)
  rcases le_or_gt t (-7 / 5) with h14 | h14
  · exact carvingAt_gt_on_Icc ⟨h17.le, h14⟩ (by dsimp only [expPolyLo, cdfPolyLo]; norm_num)
  rcases le_or_gt t (-11 / 10) with h11 | h11
  · exact carvingAt_gt_on_Icc ⟨h14.le, h11⟩ (by dsimp only [expPolyLo, cdfPolyLo]; norm_num)
  rcases le_or_gt t (-4 / 5) with h08 | h08
  · exact carvingAt_gt_on_Icc ⟨h11.le, h08⟩ (by dsimp only [expPolyLo, cdfPolyLo]; norm_num)
  rcases le_or_gt t (-1 / 2) with h05 | h05
  · exact carvingAt_gt_on_Icc ⟨h08.le, h05⟩ (by dsimp only [expPolyLo, cdfPolyLo]; norm_num)
  rcases le_or_gt t (-21 / 50) with h042 | h042
  · exact carvingAt_gt_on_Icc ⟨h05.le, h042⟩ (by dsimp only [expPolyLo, cdfPolyLo]; norm_num)
  rcases le_or_gt t (-7 / 20) with h035 | h035
  · exact carvingAt_gt_on_Icc ⟨h042.le, h035⟩ (by dsimp only [expPolyLo, cdfPolyLo]; norm_num)
  · exact carvingAt_gt_on_Icc ⟨h035.le, ht.le⟩ (by dsimp only [expPolyLo, cdfPolyLo]; norm_num)

/-- Every `ξ > 0` admits a threshold `t₀ ∈ [-3 / 10, 0]` with
`carvingAt t₀ < carvingCoefficient + ξ`. -/
theorem exists_mem_Icc_carvingAt_lt {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ t₀ ∈ Icc (-3 / 10 : ℝ) 0, carvingAt t₀ < carvingCoefficient + ξ := by
  have : Nonempty {t : ℝ // t ≤ 0} := ⟨⟨0, le_rfl⟩⟩
  set δ := min ξ (1 / 2000)
  have hδ : 0 < δ := lt_min hξ (by norm_num)
  have hlt_inf : ⨅ t : {t : ℝ // t ≤ 0}, carvingAt t.1 < carvingCoefficient + δ := by
    rw [← carvingCoefficient]
    linarith
  obtain ⟨⟨t₀, ht₀⟩, hlt⟩ := exists_lt_of_ciInf_lt hlt_inf
  refine ⟨t₀, ⟨?_, ht₀⟩, by linarith [min_le_left ξ (1 / 2000)]⟩
  by_contra hneg
  have hgt := carvingAt_gt_of_lt_neg_three_tenths (not_le.mp hneg)
  have hle : carvingCoefficient + δ ≤ 137432 / 1000000 + 1 / 2000 :=
    add_le_add carvingCoefficient_le_137432 (min_le_right _ _)
  linarith

/-- On `[-3 / 10, 0]`, `134 / 1000 ≤ carvingAt t`. -/
theorem carvingAt_ge_134_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (-3 / 10 : ℝ) 0) :
    134 / 1000 ≤ carvingAt t := by
  have hp_lo : 140350 / 1000000 ≤ gaussianCoefficient := by linarith [gaussianCoefficient_bounds.1]
  have hexp : 191 / 200 ≤ exp (-t ^ 2 / 2) := by
    have hsq : t ^ 2 ≤ 9 / 100 := by nlinarith [ht.1, ht.2]
    linarith [add_one_le_exp (-t ^ 2 / 2)]
  refine le_trans ?_ (le_max_left _ _)
  calc (134 / 1000 : ℝ) ≤ (191 / 200) * (140350 / 1000000) := by norm_num
    _ ≤ exp (-t ^ 2 / 2) * gaussianCoefficient :=
      mul_le_mul hexp hp_lo (by norm_num) (exp_pos _).le

/-- On `[-3 / 10, ∞)`, `1 - Φ(t) ≤ 13 / 20`. -/
theorem one_sub_cdf_le_13_twentieths {t : ℝ} (ht : -3 / 10 ≤ t) :
    1 - cdf (gaussianReal 0 1) t ≤ 13 / 20 := by
  have h0 : cdf (gaussianReal 0 1) 0 = 2⁻¹ := cdf_gaussianReal_zero_zero one_ne_zero
  have hanti := gaussianReal_real_Iic_add_le 0 (-3 / 10) one_ne_zero (ε := 3 / 10) (by norm_num)
  simp only [NNReal.coe_one, mul_one] at hanti
  have hsum : (-3 / 10 + 3 / 10 : ℝ) = 0 := by norm_num
  rw [hsum, ← cdf_eq_real, ← cdf_eq_real, h0] at hanti
  have hsqrt : (2 : ℝ) ≤ √(2 * π) :=
    (le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [pi_gt_three])
  have hdiv : (3 / 10 : ℝ) / √(2 * π) ≤ 3 / 20 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hmono : cdf (gaussianReal 0 1) (-3 / 10) ≤ cdf (gaussianReal 0 1) t :=
    (strictMono_cdf_gaussianReal 0 one_ne_zero).monotone ht
  linarith

end Cslib.Circuits.Frontier.Carving
