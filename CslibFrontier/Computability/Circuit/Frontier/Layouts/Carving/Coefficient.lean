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

/-! ### Double-angle lower bound helper and numerical bounds -/

/-- Double-angle lower bound for `cos`: when `0 ≤ l ≤ cos x`, `v ≤ cos (2 * x)` whenever
`v ≤ 2 * l ^ 2 - 1`. -/
private theorem le_cos_two_mul {x l v : ℝ} (hl0 : 0 ≤ l) (hl : l ≤ cos x)
    (hv : v ≤ 2 * l ^ 2 - 1) : v ≤ cos (2 * x) := by
  have hsq := pow_le_pow_left₀ hl0 hl 2
  rw [cos_two_mul]
  linarith

/-- Sharp upper bound `arccos ((1 + 2√2) / 4) ≤ 2939503850 / 10^10`. -/
private theorem arccos_edgeCorr_le :
    arccos ((1 + 2 * √2) / 4) ≤ 2939503850 / 10000000000 := by
  have hsqrt : (141421356237309 : ℝ) / 100000000000000 < √2 :=
    (lt_sqrt (by norm_num)).mpr (by norm_num)
  have hcos : cos (2939503850 / 10000000000) ≤ (1 + 2 * √2) / 4 := by
    have hb := cos_bound (x := 2939503850 / 5120000000000) (by norm_num)
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2939503850 / 5120000000000)] at hb
    have h0 : cos (2939503850 / 5120000000000) ≤ 9999998351920589 / 10000000000000000 := by
      have h := (abs_le.mp hb).2
      norm_num at h ⊢
      linarith
    have h1 := cos_two_mul_le (by norm_num) h0
      (v := 99999934076829 / 100000000000000) (by norm_num)
    have h2 := cos_two_mul_le (by norm_num) h1
      (v := 2499993407685073 / 2500000000000000) (by norm_num)
    have h3 := cos_two_mul_le (by norm_num) h2
      (v := 2499973630775059 / 2500000000000000) (by norm_num)
    have h4 := cos_two_mul_le (by norm_num) h3
      (v := 499978904731301 / 500000000000000) (by norm_num)
    have h5 := cos_two_mul_le (by norm_num) h4
      (v := 9998312414104909 / 10000000000000000) (by norm_num)
    have h6 := cos_two_mul_le (by norm_num) h5
      (v := 9993250226008867 / 10000000000000000) (by norm_num)
    have h7 := cos_two_mul_le (by norm_num) h6
      (v := 1994602003185051 / 2000000000000000) (by norm_num)
    have h8 := cos_two_mul_le (by norm_num) h7
      (v := 9892185755549091 / 10000000000000000) (by norm_num)
    have h9 := cos_two_mul_le (by norm_num) h8
      (v := 9571067804457669 / 10000000000000000) (by norm_num)
    have hval : (2939503850 / 10000000000 : ℝ) =
        2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2939503850 / 5120000000000))))))))) := by
      norm_num
    rw [hval]
    linarith
  exact (arccos_le_arccos hcos).trans_eq (arccos_cos (by norm_num) (by linarith [pi_gt_three]))

/-- Sharp lower bound `29395035 / 10^8 ≤ arccos ((1 + 2√2) / 4)`. -/
private theorem le_arccos_edgeCorr :
    (29395035 / 100000000 : ℝ) ≤ arccos ((1 + 2 * √2) / 4) := by
  have hsqrt : √2 < (141421356237310 : ℝ) / 100000000000000 :=
    (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hcos : (1 + 2 * √2) / 4 ≤ cos (29395035 / 100000000) := by
    have h0 : 999999340768369 / 1000000000000000 ≤ cos (29395035 / 25600000000) := by
      have := one_sub_sq_div_two_le_cos (x := 29395035 / 25600000000)
      norm_num at this ⊢
      linarith
    have h1 := le_cos_two_mul (by norm_num) h0
      (v := 199999472614869 / 200000000000000) (by norm_num)
    have h2 := le_cos_two_mul (by norm_num) h1
      (v := 499994726155643 / 500000000000000) (by norm_num)
    have h3 := le_cos_two_mul (by norm_num) h2
      (v := 999957809467651 / 1000000000000000) (by norm_num)
    have h4 := le_cos_two_mul (by norm_num) h3
      (v := 499915620715343 / 500000000000000) (by norm_num)
    have h5 := le_cos_two_mul (by norm_num) h4
      (v := 999325022681653 / 1000000000000000) (by norm_num)
    have h6 := le_cos_two_mul (by norm_num) h5
      (v := 249325250478843 / 250000000000000) (by norm_num)
    have h7 := le_cos_two_mul (by norm_num) h6
      (v := 989218576842809 / 1000000000000000) (by norm_num)
    have h8 := le_cos_two_mul (by norm_num) h7
      (v := 14954793524091 / 15625000000000) (by norm_num)
    have hval : (29395035 / 100000000 : ℝ) =
        2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (29395035 / 25600000000)))))))) := by norm_num
    rw [hval]
    linarith
  calc (29395035 / 100000000 : ℝ) = arccos (cos (29395035 / 100000000)) :=
        (arccos_cos (by norm_num) (by linarith [pi_gt_three])).symm
    _ ≤ arccos ((1 + 2 * √2) / 4) := arccos_le_arccos hcos

/-- Alternating degree-`4` Taylor upper bound `exp (-y) ≤ 1 - y + y^2/2 - y^3/6 + y^4/24` for
`0 ≤ y`. -/
private theorem exp_neg_le_quartic {y : ℝ} (hy : 0 ≤ y) :
    exp (-y) ≤ 1 - y + y ^ 2 / 2 - y ^ 3 / 6 + y ^ 4 / 24 := by
  let f₁ : ℝ → ℝ := fun t => exp (-t) - (1 - t)
  have hf₁ : ∀ t ≥ 0, 0 ≤ f₁ t := fun t _ => by
    dsimp [f₁]; linarith [add_one_le_exp (-t)]
  have hexp_d : ∀ t : ℝ, HasDerivAt (fun x => exp (-x)) (-exp (-t)) t := fun t => by
    have := ((hasDerivAt_neg t).exp)
    exact this.congr_deriv (by ring)
  let f₂ : ℝ → ℝ := fun t => (1 - t + t ^ 2 / 2) - exp (-t)
  have hd₂ : ∀ t, HasDerivAt f₂ (f₁ t) t := fun t => by
    have hp : HasDerivAt (fun x => 1 - x + x ^ 2 / 2) (-1 + t) t := by
      have := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
        ((hasDerivAt_pow 2 t).div_const 2))
      exact this.congr_deriv (by ring)
    exact (hp.sub (hexp_d t)).congr_deriv (by dsimp [f₁]; ring)
  have hf₂ : ∀ t ≥ 0, 0 ≤ f₂ t := by
    have hmono : MonotoneOn f₂ (Ici 0) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        (fun x _ => (hd₂ x).continuousAt.continuousWithinAt)
        (fun x _ => (hd₂ x).hasDerivWithinAt)
        (fun x hx => hf₁ x (interior_subset hx))
    intro t ht
    have h0 : f₂ 0 = 0 := by simp [f₂]
    exact h0 ▸ hmono (le_rfl : (0 : ℝ) ∈ Ici 0) ht ht
  let f₃ : ℝ → ℝ := fun t => exp (-t) - (1 - t + t ^ 2 / 2 - t ^ 3 / 6)
  have hd₃ : ∀ t, HasDerivAt f₃ (f₂ t) t := fun t => by
    have hp : HasDerivAt (fun x => 1 - x + x ^ 2 / 2 - x ^ 3 / 6) (-1 + t - t ^ 2 / 2) t := by
      have := ((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
        ((hasDerivAt_pow 2 t).div_const 2)).sub ((hasDerivAt_pow 3 t).div_const 6))
      exact this.congr_deriv (by ring)
    exact ((hexp_d t).sub hp).congr_deriv (by dsimp [f₂]; ring)
  have hf₃ : ∀ t ≥ 0, 0 ≤ f₃ t := by
    have hmono : MonotoneOn f₃ (Ici 0) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        (fun x _ => (hd₃ x).continuousAt.continuousWithinAt)
        (fun x _ => (hd₃ x).hasDerivWithinAt)
        (fun x hx => hf₂ x (interior_subset hx))
    intro t ht
    have h0 : f₃ 0 = 0 := by simp [f₃]
    exact h0 ▸ hmono (le_rfl : (0 : ℝ) ∈ Ici 0) ht ht
  let f₄ : ℝ → ℝ := fun t => (1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24) - exp (-t)
  have hd₄ : ∀ t, HasDerivAt f₄ (f₃ t) t := fun t => by
    have hp : HasDerivAt (fun x => 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24)
        (-1 + t - t ^ 2 / 2 + t ^ 3 / 6) t := by
      have := (((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
        ((hasDerivAt_pow 2 t).div_const 2)).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 4 t).div_const 24))
      exact this.congr_deriv (by ring)
    exact (hp.sub (hexp_d t)).congr_deriv (by dsimp [f₃]; ring)
  have hmono : MonotoneOn f₄ (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hd₄ x).continuousAt.continuousWithinAt)
      (fun x _ => (hd₄ x).hasDerivWithinAt)
      (fun x hx => hf₃ x (interior_subset hx))
  have h0 : f₄ 0 = 0 := by simp [f₄]
  have hge := h0 ▸ hmono (le_rfl : (0 : ℝ) ∈ Ici 0) hy hy
  dsimp [f₄] at hge
  linarith

/-- Upper bound on `cdf (gaussianReal 0 1) a` for `0 ≤ a` from `exp_neg_le_quartic`. -/
private theorem cdf_gaussianReal_le_poly {a : ℝ} (ha : 0 ≤ a) :
    cdf (gaussianReal 0 1) a ≤
      1 / 2 + (√(2 * π))⁻¹ * (a - a ^ 3 / 6 + a ^ 5 / 40 - a ^ 7 / 336 + a ^ 9 / 3456) := by
  have hsplit : cdf (gaussianReal 0 1) a =
      cdf (gaussianReal 0 1) 0 + ∫ u in (0 : ℝ)..a, gaussianPDFReal 0 1 u := by
    rw [cdf_gaussianReal_eq_integral 0 one_ne_zero a,
      cdf_gaussianReal_eq_integral 0 one_ne_zero 0,
      intervalIntegral.integral_of_le ha]
    have huni : Iic a = Iic (0 : ℝ) ∪ Ioc 0 a := (Iic_union_Ioc_eq_Iic ha).symm
    rw [huni, setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
      (integrable_gaussianPDFReal 0 1).integrableOn
      (integrable_gaussianPDFReal 0 1).integrableOn]
  rw [hsplit, cdf_gaussianReal_zero_zero one_ne_zero]
  let P : ℝ → ℝ := fun u => 1 - u ^ 2 / 2 + u ^ 4 / 8 - u ^ 6 / 48 + u ^ 8 / 384
  let Q : ℝ → ℝ := fun u => u - u ^ 3 / 6 + u ^ 5 / 40 - u ^ 7 / 336 + u ^ 9 / 3456
  have hQ_deriv : ∀ u ∈ uIcc 0 a, HasDerivAt Q (P u) u := fun u _ => by
    dsimp [Q, P]
    have := (((((hasDerivAt_id u).sub ((hasDerivAt_pow 3 u).div_const 6)).add
      ((hasDerivAt_pow 5 u).div_const 40)).sub ((hasDerivAt_pow 7 u).div_const 336)).add
      ((hasDerivAt_pow 9 u).div_const 3456))
    exact this.congr_deriv (by ring)
  have hP_int : IntervalIntegrable P volume 0 a :=
    (by unfold P; fun_prop : Continuous P).intervalIntegrable 0 a
  have hint_Q : ∫ u in (0 : ℝ)..a, P u = Q a := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hQ_deriv hP_int]
    dsimp [Q]; ring
  have hpdf_le : ∀ u ∈ Icc 0 a, gaussianPDFReal 0 1 u ≤ (√(2 * π))⁻¹ * P u := by
    intro u _
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hq := exp_neg_le_quartic (y := u ^ 2 / 2) (by positivity)
    have heq : -(u ^ 2 / 2) = -u ^ 2 / 2 := by ring
    rw [heq] at hq
    refine hq.trans_eq ?_
    dsimp [P]; ring
  have hmono := intervalIntegral.integral_mono_on ha
    ((continuous_gaussianPDFReal 0 1).intervalIntegrable 0 a)
    (hP_int.const_mul (√(2 * π))⁻¹) hpdf_le
  rw [intervalIntegral.integral_const_mul, hint_Q] at hmono
  dsimp [Q] at hmono
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
  have hpi_lo : (314159265358979 : ℝ) / 100000000000000 < π := by linarith [pi_gt_d20]
  have hpi_hi : π < (314159265358980 : ℝ) / 100000000000000 := by linarith [pi_lt_d20]
  have hpi_pos : 0 < π := pi_pos
  have hpg_hi : gaussianCoefficient ≤
      3 * (2939503850 / 10000000000) / (2 * (314159265358979 / 100000000000000)) := by
    unfold gaussianCoefficient
    rw [div_mul_eq_mul_div]
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left arccos_edgeCorr_le (by norm_num))
      (by norm_num) (by linarith)
  have hpg_lo : 3 * (29395035 / 100000000) / (2 * (314159265358980 / 100000000000000)) ≤
      gaussianCoefficient := by
    unfold gaussianCoefficient
    rw [div_mul_eq_mul_div]
    exact div_le_div₀ (mul_nonneg (by norm_num) (arccos_nonneg _))
      (mul_le_mul_of_nonneg_left le_arccos_edgeCorr (by norm_num))
      (by linarith) (by linarith)
  have hpg_pos := gaussianCoefficient_pos
  set y : ℝ := a ^ 2 / 2
  have hy_nonneg : 0 ≤ y := by positivity
  have hexp_eq : exp (-(-a) ^ 2 / 2) = (exp y)⁻¹ := by
    rw [← exp_neg]
    congr 1
    dsimp [y]; ring
  set E_lo : ℝ := 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24
  have hE_pos : 0 < E_lo := by norm_num [E_lo, y, a]
  have hexp_hi : exp (-(-a) ^ 2 / 2) ≤ E_lo⁻¹ := by
    rw [hexp_eq]
    exact inv_anti₀ hE_pos (quartic_le_exp hy_nonneg)
  have hcdf_symm : 1 - cdf (gaussianReal 0 1) (-a) = cdf (gaussianReal 0 1) a := by
    rw [cdf_gaussianReal_neg one_ne_zero a]; ring
  have hsqrt_2pi : (250662827463099 : ℝ) / 100000000000000 ≤ √(2 * π) :=
    (le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith)
  have hcdf_hi : 1 - cdf (gaussianReal 0 1) (-a) ≤
      1 / 2 + ((250662827463099 : ℝ) / 100000000000000)⁻¹ *
        (a - a ^ 3 / 6 + a ^ 5 / 40 - a ^ 7 / 336 + a ^ 9 / 3456) := by
    rw [hcdf_symm]
    refine (cdf_gaussianReal_le_poly ha_pos.le).trans ?_
    have hpoly_pos : 0 ≤ a - a ^ 3 / 6 + a ^ 5 / 40 - a ^ 7 / 336 + a ^ 9 / 3456 := by
      norm_num [a]
    gcongr
  refine max_le ?_ ?_
  · calc exp (-(-a) ^ 2 / 2) * gaussianCoefficient
        ≤ E_lo⁻¹ * (3 * (2939503850 / 10000000000) /
            (2 * (314159265358979 / 100000000000000))) :=
          mul_le_mul hexp_hi hpg_hi hpg_pos.le (inv_pos.mpr hE_pos).le
      _ ≤ 137432 / 1000000 := by norm_num [E_lo, y, a]
  · have hcoef_hi : 1 / 2 - 2 / 3 * gaussianCoefficient ≤
        1 / 2 - 2 / 3 * (3 * (29395035 / 100000000) /
          (2 * (314159265358980 / 100000000000000))) := by linarith
    have hprod_hi : exp (-(-a) ^ 2 / 2) * gaussianCoefficient ≤
        E_lo⁻¹ * (3 * (2939503850 / 10000000000) /
          (2 * (314159265358979 / 100000000000000))) :=
      mul_le_mul hexp_hi hpg_hi hpg_pos.le (inv_pos.mpr hE_pos).le
    have hterm1 : gaussianCoefficient * (1 - cdf (gaussianReal 0 1) (-a)) ≤
        (3 * (2939503850 / 10000000000) / (2 * (314159265358979 / 100000000000000))) *
          (1 / 2 + ((250662827463099 : ℝ) / 100000000000000)⁻¹ *
            (a - a ^ 3 / 6 + a ^ 5 / 40 - a ^ 7 / 336 + a ^ 9 / 3456)) :=
      mul_le_mul hpg_hi hcdf_hi
        (by rw [hcdf_symm]; exact cdf_nonneg _ _) (by norm_num)
    have hterm2 : (1 / 2 - 2 / 3 * gaussianCoefficient) *
          (exp (-(-a) ^ 2 / 2) * gaussianCoefficient) ≤
        (1 / 2 - 2 / 3 * (3 * (29395035 / 100000000) /
          (2 * (314159265358980 / 100000000000000)))) *
          (E_lo⁻¹ * (3 * (2939503850 / 10000000000) /
            (2 * (314159265358979 / 100000000000000)))) :=
      mul_le_mul hcoef_hi hprod_hi (mul_nonneg (exp_pos _).le hpg_pos.le) (by norm_num)
    calc gaussianCoefficient * (1 - cdf (gaussianReal 0 1) (-a)) +
            (1 / 2 - 2 / 3 * gaussianCoefficient) *
              (exp (-(-a) ^ 2 / 2) * gaussianCoefficient)
        ≤ _ := add_le_add hterm1 hterm2
      _ ≤ 137432 / 1000000 := by norm_num [E_lo, y, a]

/-- Lower bound `139821 / 1000000 ≤ Switched.switchedCoefficient` (`c₃ ≈ 0.13982212`). -/
theorem switchedCoefficient_ge_139821 : (139821 / 1000000 : ℝ) ≤ switchedCoefficient := by
  have harc : (585685 / 1000000 : ℝ) ≤ arccos (5 / 6) := by
    have h0 : 499998691456149 / 500000000000000 ≤ cos (585685 / 256000000) := by
      have := one_sub_sq_div_two_le_cos (x := 585685 / 256000000)
      norm_num at this ⊢
      linarith
    have h1 := le_cos_two_mul (by norm_num) h0
      (v := 99998953166289 / 100000000000000) (by norm_num)
    have h2 := le_cos_two_mul (by norm_num) h1
      (v := 249989531717683 / 250000000000000) (by norm_num)
    have h3 := le_cos_two_mul (by norm_num) h2
      (v := 199966502197929 / 200000000000000) (by norm_num)
    have h4 := le_cos_two_mul (by norm_num) h3
      (v := 999330100063717 / 1000000000000000) (by norm_num)
    have h5 := le_cos_two_mul (by norm_num) h4
      (v := 997321297786717 / 1000000000000000) (by norm_num)
    have h6 := le_cos_two_mul (by norm_num) h5
      (v := 494649771018981 / 500000000000000) (by norm_num)
    have h7 := le_cos_two_mul (by norm_num) h6
      (v := 478713583876521 / 500000000000000) (by norm_num)
    have h8 := le_cos_two_mul (by norm_num) h7
      (v := 833333563103223 / 1000000000000000) (by norm_num)
    have hval : (585685 / 1000000 : ℝ) =
        2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (585685 / 256000000)))))))) := by norm_num
    have hcos : (5 / 6 : ℝ) ≤ cos (585685 / 1000000) := by rw [hval]; linarith
    calc (585685 / 1000000 : ℝ) = arccos (cos (585685 / 1000000)) :=
          (arccos_cos (by norm_num) (by linarith [pi_gt_three])).symm
      _ ≤ arccos (5 / 6) := arccos_le_arccos hcos
  have hpi_hi : π < (314159265358980 : ℝ) / 100000000000000 := by linarith [pi_lt_d20]
  unfold switchedCoefficient
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

/-- **Strict improvement over Gaspers' switched pathwidth constant `c₃`:**
`carvingCoefficient ≤ 0.137432 < 0.139821 ≤ switchedCoefficient`. -/
theorem carvingCoefficient_lt_switchedCoefficient :
    carvingCoefficient < switchedCoefficient :=
  carvingCoefficient_le_137432.trans_lt (lt_of_lt_of_le (by norm_num) switchedCoefficient_ge_139821)

/-! ### Localization of the optimal threshold to `[-3 / 10, 0]` -/

/-- Rational bounds `140350 / 1000000 ≤ gaussianCoefficient ≤ 140352 / 1000000`. -/
private theorem gaussianCoefficient_bounds :
    140350 / 1000000 ≤ gaussianCoefficient ∧ gaussianCoefficient ≤ 140352 / 1000000 := by
  have hpi_lo : (314159265358979 : ℝ) / 100000000000000 < π := by linarith [pi_gt_d20]
  have hpi_hi : π < (314159265358980 : ℝ) / 100000000000000 := by linarith [pi_lt_d20]
  have hlo : 3 * (29395035 / 100000000) / (2 * (314159265358980 / 100000000000000)) ≤
      gaussianCoefficient := by
    unfold gaussianCoefficient
    rw [div_mul_eq_mul_div]
    exact div_le_div₀ (mul_nonneg (by norm_num) (arccos_nonneg _))
      (mul_le_mul_of_nonneg_left le_arccos_edgeCorr (by norm_num))
      (by linarith) (by linarith)
  have hhi : gaussianCoefficient ≤
      3 * (2939503850 / 10000000000) / (2 * (314159265358979 / 100000000000000)) := by
    unfold gaussianCoefficient
    rw [div_mul_eq_mul_div]
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left arccos_edgeCorr_le (by norm_num))
      (by norm_num) (by linarith)
  exact ⟨by norm_num at hlo; linarith, by norm_num at hhi; linarith⟩

/-- Convenient strict upper bound `gaussianCoefficient < 3 / 20`. -/
theorem gaussianCoefficient_lt_three_twentieths : gaussianCoefficient < 3 / 20 :=
  gaussianCoefficient_bounds.2.trans_lt (by norm_num)

/-- Alternating degree-`7` Taylor lower bound for `exp (-y)` on `0 ≤ y`. -/
private theorem exp_neg_ge_septic {y : ℝ} (hy : 0 ≤ y) :
    1 - y + y ^ 2 / 2 - y ^ 3 / 6 + y ^ 4 / 24 - y ^ 5 / 120 + y ^ 6 / 720 - y ^ 7 / 5040 ≤
      exp (-y) := by
  have hexp_d : ∀ t : ℝ, HasDerivAt (fun x => exp (-x)) (-exp (-t)) t := fun t =>
    (hasDerivAt_neg t).exp.congr_deriv (by ring)
  let f₄ : ℝ → ℝ := fun t => (1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24) - exp (-t)
  have hf₄ : ∀ t ≥ 0, 0 ≤ f₄ t := fun t ht => by
    dsimp [f₄]; linarith [exp_neg_le_quartic ht]
  let f₅ : ℝ → ℝ := fun t =>
    exp (-t) - (1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - t ^ 5 / 120)
  have hd₅ : ∀ t, HasDerivAt f₅ (f₄ t) t := fun t => by
    have hp : HasDerivAt
        (fun x => 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120)
        (-1 + t - t ^ 2 / 2 + t ^ 3 / 6 - t ^ 4 / 24) t := by
      have := ((((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
        ((hasDerivAt_pow 2 t).div_const 2)).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 5 t).div_const 120))
      exact this.congr_deriv (by ring)
    exact ((hexp_d t).sub hp).congr_deriv (by dsimp [f₄]; ring)
  have hf₅ : ∀ t ≥ 0, 0 ≤ f₅ t := by
    have hmono : MonotoneOn f₅ (Ici 0) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        (fun x _ => (hd₅ x).continuousAt.continuousWithinAt)
        (fun x _ => (hd₅ x).hasDerivWithinAt)
        (fun x hx => hf₄ x (interior_subset hx))
    intro t ht
    have h0 : f₅ 0 = 0 := by simp [f₅]
    exact h0 ▸ hmono (le_rfl : (0 : ℝ) ∈ Ici 0) ht ht
  let f₆ : ℝ → ℝ := fun t =>
    (1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - t ^ 5 / 120 + t ^ 6 / 720) - exp (-t)
  have hd₆ : ∀ t, HasDerivAt f₆ (f₅ t) t := fun t => by
    have hp : HasDerivAt
        (fun x => 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120 + x ^ 6 / 720)
        (-1 + t - t ^ 2 / 2 + t ^ 3 / 6 - t ^ 4 / 24 + t ^ 5 / 120) t := by
      have := (((((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
        ((hasDerivAt_pow 2 t).div_const 2)).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 5 t).div_const 120)).add
        ((hasDerivAt_pow 6 t).div_const 720))
      exact this.congr_deriv (by ring)
    exact (hp.sub (hexp_d t)).congr_deriv (by dsimp [f₅]; ring)
  have hf₆ : ∀ t ≥ 0, 0 ≤ f₆ t := by
    have hmono : MonotoneOn f₆ (Ici 0) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        (fun x _ => (hd₆ x).continuousAt.continuousWithinAt)
        (fun x _ => (hd₆ x).hasDerivWithinAt)
        (fun x hx => hf₅ x (interior_subset hx))
    intro t ht
    have h0 : f₆ 0 = 0 := by simp [f₆]
    exact h0 ▸ hmono (le_rfl : (0 : ℝ) ∈ Ici 0) ht ht
  let f₇ : ℝ → ℝ := fun t =>
    exp (-t) -
      (1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - t ^ 5 / 120 + t ^ 6 / 720 - t ^ 7 / 5040)
  have hd₇ : ∀ t, HasDerivAt f₇ (f₆ t) t := fun t => by
    have hp : HasDerivAt
        (fun x => 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120 +
          x ^ 6 / 720 - x ^ 7 / 5040)
        (-1 + t - t ^ 2 / 2 + t ^ 3 / 6 - t ^ 4 / 24 + t ^ 5 / 120 - t ^ 6 / 720) t := by
      have := ((((((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
        ((hasDerivAt_pow 2 t).div_const 2)).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 5 t).div_const 120)).add
        ((hasDerivAt_pow 6 t).div_const 720)).sub ((hasDerivAt_pow 7 t).div_const 5040))
      exact this.congr_deriv (by ring)
    exact ((hexp_d t).sub hp).congr_deriv (by dsimp [f₆]; ring)
  have hmono : MonotoneOn f₇ (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hd₇ x).continuousAt.continuousWithinAt)
      (fun x _ => (hd₇ x).hasDerivWithinAt)
      (fun x hx => hf₆ x (interior_subset hx))
  have h0 : f₇ 0 = 0 := by simp [f₇]
  have hge := h0 ▸ hmono (le_rfl : (0 : ℝ) ∈ Ici 0) hy hy
  dsimp [f₇] at hge
  linarith

private noncomputable abbrev cdfPolyLo (a : ℝ) : ℝ :=
  a - a ^ 3 / 6 + a ^ 5 / 40 - a ^ 7 / 336 + a ^ 9 / 3456 - a ^ 11 / 42240 +
    a ^ 13 / 599040 - a ^ 15 / 9676800

/-- Lower bound on `cdf (gaussianReal 0 1) a` for `0 ≤ a` from `exp_neg_ge_septic`. -/
private theorem cdf_gaussianReal_ge_poly {a : ℝ} (ha : 0 ≤ a) :
    1 / 2 + (√(2 * π))⁻¹ * cdfPolyLo a ≤ cdf (gaussianReal 0 1) a := by
  have hsplit : cdf (gaussianReal 0 1) a =
      cdf (gaussianReal 0 1) 0 + ∫ u in (0 : ℝ)..a, gaussianPDFReal 0 1 u := by
    rw [cdf_gaussianReal_eq_integral 0 one_ne_zero a,
      cdf_gaussianReal_eq_integral 0 one_ne_zero 0,
      intervalIntegral.integral_of_le ha]
    have huni : Iic a = Iic (0 : ℝ) ∪ Ioc 0 a := (Iic_union_Ioc_eq_Iic ha).symm
    rw [huni, setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
      (integrable_gaussianPDFReal 0 1).integrableOn
      (integrable_gaussianPDFReal 0 1).integrableOn]
  rw [hsplit, cdf_gaussianReal_zero_zero one_ne_zero]
  let P : ℝ → ℝ := fun u =>
    1 - u ^ 2 / 2 + u ^ 4 / 8 - u ^ 6 / 48 + u ^ 8 / 384 - u ^ 10 / 3840 +
      u ^ 12 / 46080 - u ^ 14 / 645120
  have hQ_deriv : ∀ u ∈ uIcc 0 a, HasDerivAt cdfPolyLo (P u) u := fun u _ => by
    dsimp [cdfPolyLo, P]
    have := ((((((((hasDerivAt_id u).sub ((hasDerivAt_pow 3 u).div_const 6)).add
      ((hasDerivAt_pow 5 u).div_const 40)).sub ((hasDerivAt_pow 7 u).div_const 336)).add
      ((hasDerivAt_pow 9 u).div_const 3456)).sub ((hasDerivAt_pow 11 u).div_const 42240)).add
      ((hasDerivAt_pow 13 u).div_const 599040)).sub
      ((hasDerivAt_pow 15 u).div_const 9676800))
    exact this.congr_deriv (by ring)
  have hP_int : IntervalIntegrable P volume 0 a :=
    (by unfold P; fun_prop : Continuous P).intervalIntegrable 0 a
  have hint_Q : ∫ u in (0 : ℝ)..a, P u = cdfPolyLo a := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hQ_deriv hP_int]
    dsimp [cdfPolyLo]; ring
  have hpdf_ge : ∀ u ∈ Icc 0 a, (√(2 * π))⁻¹ * P u ≤ gaussianPDFReal 0 1 u := by
    intro u _
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hq := exp_neg_ge_septic (y := u ^ 2 / 2) (by positivity)
    have heq : -(u ^ 2 / 2) = -u ^ 2 / 2 := by ring
    rw [heq] at hq
    refine (le_of_eq ?_).trans hq
    dsimp [P]; ring
  have hmono := intervalIntegral.integral_mono_on ha
    (hP_int.const_mul (√(2 * π))⁻¹)
    ((continuous_gaussianPDFReal 0 1).intervalIntegrable 0 a) hpdf_ge
  rw [intervalIntegral.integral_const_mul, hint_Q] at hmono
  linarith

private noncomputable abbrev expPolyLo (y : ℝ) : ℝ :=
  1 - y + y ^ 2 / 2 - y ^ 3 / 6 + y ^ 4 / 24 - y ^ 5 / 120 + y ^ 6 / 720 - y ^ 7 / 5040

private theorem carvingAt_gt_on_Icc {a b t : ℝ} (ht : t ∈ Icc a b) (hb0 : b ≤ 0)
    (he0 : 0 ≤ expPolyLo (a ^ 2 / 2)) (hc0 : 0 ≤ cdfPolyLo (-b))
    (hval : 138 / 1000 <
      (140350 / 1000000) * (1 / 2 + (2506629 / 1000000)⁻¹ * cdfPolyLo (-b)) +
        (1 / 2 - 2 / 3 * (140352 / 1000000)) * (expPolyLo (a ^ 2 / 2) * (140350 / 1000000))) :
    138 / 1000 < carvingAt t := by
  obtain ⟨hp_lo, hp_hi⟩ := gaussianCoefficient_bounds
  have hsqrt_pos : 0 < √(2 * π) := sqrt_pos.mpr (by positivity)
  have hsqrt_hi : √(2 * π) ≤ 2506629 / 1000000 := by
    have hpi_hi : π < (314159265358980 : ℝ) / 100000000000000 := by linarith [pi_lt_d20]
    exact sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hcdf_tb : cdf (gaussianReal 0 1) t ≤ cdf (gaussianReal 0 1) b :=
    (strictMono_cdf_gaussianReal 0 one_ne_zero).monotone ht.2
  have hsymm : 1 - cdf (gaussianReal 0 1) b = cdf (gaussianReal 0 1) (-b) := by
    have := cdf_gaussianReal_neg one_ne_zero (-b)
    rw [neg_neg] at this
    linarith
  have hcdf_lo : 1 / 2 + (2506629 / 1000000 : ℝ)⁻¹ * cdfPolyLo (-b) ≤
      1 - cdf (gaussianReal 0 1) t := by
    calc 1 / 2 + (2506629 / 1000000 : ℝ)⁻¹ * cdfPolyLo (-b)
        ≤ 1 / 2 + (√(2 * π))⁻¹ * cdfPolyLo (-b) := by gcongr
      _ ≤ cdf (gaussianReal 0 1) (-b) := cdf_gaussianReal_ge_poly (by linarith)
      _ = 1 - cdf (gaussianReal 0 1) b := hsymm.symm
      _ ≤ 1 - cdf (gaussianReal 0 1) t := by linarith
  have hexp_lo : expPolyLo (a ^ 2 / 2) ≤ exp (-t ^ 2 / 2) := by
    have hsq : t ^ 2 ≤ a ^ 2 := by nlinarith [ht.1, ht.2]
    have h1 := exp_neg_ge_septic (y := a ^ 2 / 2) (by positivity)
    have h2 : exp (-(a ^ 2 / 2)) ≤ exp (-t ^ 2 / 2) := exp_le_exp.mpr (by linarith)
    exact h1.trans h2
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
  · obtain ⟨hp_lo, hp_hi⟩ := gaussianCoefficient_bounds
    have hsqrt_pos : 0 < √(2 * π) := sqrt_pos.mpr (by positivity)
    have hsqrt_hi : √(2 * π) ≤ 2506629 / 1000000 := by
      have hpi_hi : π < (314159265358980 : ℝ) / 100000000000000 := by linarith [pi_lt_d20]
      exact sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
    have hcdf_le : cdf (gaussianReal 0 1) t ≤ cdf (gaussianReal 0 1) (-23 / 10) :=
      (strictMono_cdf_gaussianReal 0 one_ne_zero).monotone h23
    have hsymm : 1 - cdf (gaussianReal 0 1) (-23 / 10) = cdf (gaussianReal 0 1) (23 / 10) := by
      have := cdf_gaussianReal_neg one_ne_zero (23 / 10)
      have hn : -(23 / 10 : ℝ) = -23 / 10 := by norm_num
      rw [hn] at this
      linarith
    have hc0 : 0 ≤ cdfPolyLo (23 / 10) := by norm_num [cdfPolyLo]
    have hcdf_lo : 1 / 2 + (2506629 / 1000000 : ℝ)⁻¹ * cdfPolyLo (23 / 10) ≤
        1 - cdf (gaussianReal 0 1) t := by
      calc 1 / 2 + (2506629 / 1000000 : ℝ)⁻¹ * cdfPolyLo (23 / 10)
          ≤ 1 / 2 + (√(2 * π))⁻¹ * cdfPolyLo (23 / 10) := by gcongr
        _ ≤ cdf (gaussianReal 0 1) (23 / 10) := cdf_gaussianReal_ge_poly (by norm_num)
        _ = 1 - cdf (gaussianReal 0 1) (-23 / 10) := hsymm.symm
        _ ≤ 1 - cdf (gaussianReal 0 1) t := by linarith
    have hnonneg : 0 ≤ (1 / 2 - 2 / 3 * gaussianCoefficient) *
        (exp (-t ^ 2 / 2) * gaussianCoefficient) :=
      mul_nonneg (by linarith) (mul_nonneg (exp_pos _).le gaussianCoefficient_pos.le)
    have hnum : (138 / 1000 : ℝ) <
        (140350 / 1000000) * (1 / 2 + (2506629 / 1000000)⁻¹ * cdfPolyLo (23 / 10)) := by
      norm_num [cdfPolyLo]
    refine hnum.trans_le (le_trans ?_ (le_max_right _ _))
    have hm := mul_le_mul hp_lo hcdf_lo (by positivity) gaussianCoefficient_pos.le
    linarith
  rcases le_or_gt t (-2) with h20 | h20
  · exact carvingAt_gt_on_Icc ⟨h23.le, h20⟩ (by norm_num) (by norm_num [expPolyLo])
      (by norm_num [cdfPolyLo]) (by norm_num [expPolyLo, cdfPolyLo])
  rcases le_or_gt t (-17 / 10) with h17 | h17
  · exact carvingAt_gt_on_Icc ⟨h20.le, h17⟩ (by norm_num) (by norm_num [expPolyLo])
      (by norm_num [cdfPolyLo]) (by norm_num [expPolyLo, cdfPolyLo])
  rcases le_or_gt t (-7 / 5) with h14 | h14
  · exact carvingAt_gt_on_Icc ⟨h17.le, h14⟩ (by norm_num) (by norm_num [expPolyLo])
      (by norm_num [cdfPolyLo]) (by norm_num [expPolyLo, cdfPolyLo])
  rcases le_or_gt t (-11 / 10) with h11 | h11
  · exact carvingAt_gt_on_Icc ⟨h14.le, h11⟩ (by norm_num) (by norm_num [expPolyLo])
      (by norm_num [cdfPolyLo]) (by norm_num [expPolyLo, cdfPolyLo])
  rcases le_or_gt t (-4 / 5) with h08 | h08
  · exact carvingAt_gt_on_Icc ⟨h11.le, h08⟩ (by norm_num) (by norm_num [expPolyLo])
      (by norm_num [cdfPolyLo]) (by norm_num [expPolyLo, cdfPolyLo])
  rcases le_or_gt t (-1 / 2) with h05 | h05
  · exact carvingAt_gt_on_Icc ⟨h08.le, h05⟩ (by norm_num) (by norm_num [expPolyLo])
      (by norm_num [cdfPolyLo]) (by norm_num [expPolyLo, cdfPolyLo])
  rcases le_or_gt t (-21 / 50) with h042 | h042
  · exact carvingAt_gt_on_Icc ⟨h05.le, h042⟩ (by norm_num) (by norm_num [expPolyLo])
      (by norm_num [cdfPolyLo]) (by norm_num [expPolyLo, cdfPolyLo])
  rcases le_or_gt t (-7 / 20) with h035 | h035
  · exact carvingAt_gt_on_Icc ⟨h042.le, h035⟩ (by norm_num) (by norm_num [expPolyLo])
      (by norm_num [cdfPolyLo]) (by norm_num [expPolyLo, cdfPolyLo])
  · exact carvingAt_gt_on_Icc ⟨h035.le, ht.le⟩ (by norm_num) (by norm_num [expPolyLo])
      (by norm_num [cdfPolyLo]) (by norm_num [expPolyLo, cdfPolyLo])

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
  obtain ⟨hp_lo, _⟩ := gaussianCoefficient_bounds
  have hexp : 191 / 200 ≤ exp (-t ^ 2 / 2) := by
    have hsq : t ^ 2 ≤ 9 / 100 := by nlinarith [ht.1, ht.2]
    have h1 := add_one_le_exp (-t ^ 2 / 2)
    linarith
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
