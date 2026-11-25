/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import CslibFrontier.Probability.Azuma
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bennett and Bernstein one-step moment-generating function bounds

Variance-sensitive exponential moment bounds for random variables bounded above, complementing the
variance-oblivious range bound in `CslibFrontier.Probability.HoeffdingStep`:

* **Scalar Bennett–Poisson inequalities**:
  * `Real.exp_sub_one_sub_le_mul_sq`: for `0 < b` and any `u ≤ b` (including arbitrarily negative
    `u`), `exp u - 1 - u ≤ (u ^ 2 / b ^ 2) * (exp b - 1 - b)`.
  * `Real.exp_sub_one_sub_le_div`: for `0 ≤ u < 3`, `exp u - 1 - u ≤ u ^ 2 / (2 * (1 - u / 3))`.
  * `InformationTheory.sq_div_two_mul_le_klFun_one_add`: Bennett's Poisson exponent
    `klFun (1 + u) = (1 + u) log (1 + u) - u` satisfies `u ^ 2 / (2 * (1 + u / 3)) ≤ klFun (1 + u)`
    for all `u ≥ 0`.
* **Measure-theoretic one-step Bennett MGF bound** (`ProbabilityTheory.mgf_le_exp_bennett_of_le`):
  if `X : Ω → ℝ` under a probability measure `μ` has `∫ X ∂μ ≤ 0`, `X ≤ b` a.e. (`b > 0`), and
  `∫ X² ∂μ ≤ v`, then `mgf X μ t ≤ exp ((v / b ^ 2) * (exp (t * b) - 1 - t * b))` for every
  `t ≥ 0`, and `ProbabilityTheory.measure_ge_le_bennett_of_mgf_le` optimizes `t` via Chernoff's
  bound to obtain `μ.real {ω | ε ≤ X ω} ≤ exp (-(v / b ^ 2) * klFun (1 + b * ε / v))`.
* **Discrete `PMF` one-step Bennett MGF bounds**
  (`Cslib.Probability.PMF.tsum_mul_exp_le_bennett`, `tsum_mul_exp_sub_mean_le_bennett`,
  `sum_mul_exp_sub_mean_le_bennett`): the corresponding bounds on arbitrary outcome types without
  `[Fintype α]` or `[MeasurableSpace α]`.

## Main results

* `Real.exp_sub_one_sub_le_mul_sq`, `Real.exp_sub_one_sub_le_div`: scalar Bennett and rational
  Bernstein MGF inequalities.
* `InformationTheory.sq_div_two_mul_le_klFun_one_add`: rational Bernstein lower bound on
  `klFun (1 + u)`.
* `Cslib.Probability.bennett_laplace_exponent_eq`,
  `Cslib.Probability.exp_neg_klFun_le_exp_bernstein`,
  `Cslib.Probability.exp_bernstein_le_of_sqrt_add`: Laplace optimization and Bernstein tail
  inversion identities.
* `ProbabilityTheory.mgf_le_exp_bennett_of_le`,
  `ProbabilityTheory.measure_ge_le_bennett_of_mgf_le`: one-sided measure-theoretic Bennett MGF and
  Chernoff tail bounds.
* `Cslib.Probability.PMF.tsum_mul_exp_le_bennett`,
  `Cslib.Probability.PMF.tsum_mul_exp_sub_mean_le_bennett`,
  `Cslib.Probability.PMF.sum_mul_exp_sub_mean_le_bennett`: discrete `PMF` Bennett MGF bounds.

## References

* [G. Bennett, *Probability inequalities for the sum of independent random variables*][Bennett1962]
* [D. A. Freedman, *On tail probabilities for martingales*][Freedman1975]
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped BigOperators ENNReal NNReal

/-! ### Scalar Bennett and Bernstein inequalities -/

namespace Real

private theorem monotoneOn_Ici_zero_of_hasDerivAt {f f' : ℝ → ℝ}
    (hd : ∀ x : ℝ, 0 ≤ x → HasDerivAt f (f' x) x) (hnn : ∀ x : ℝ, 0 < x → 0 ≤ f' x) :
    MonotoneOn f (Ici 0) :=
  monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (by rw [interior_Ici] at hx; exact hx.le)).differentiableAt
      |>.differentiableWithinAt)
    fun x hx => by
      rw [interior_Ici] at hx
      rw [(hd x hx.le).deriv]
      exact hnn x hx

private theorem nonneg_of_hasDerivAt_Ici_zero {f f' : ℝ → ℝ} (hf0 : f 0 = 0)
    (hd : ∀ x : ℝ, 0 ≤ x → HasDerivAt f (f' x) x) (hnn : ∀ x : ℝ, 0 < x → 0 ≤ f' x)
    {u : ℝ} (hu : 0 ≤ u) : 0 ≤ f u := by
  simpa only [hf0] using monotoneOn_Ici_zero_of_hasDerivAt hd hnn (le_rfl : (0 : ℝ) ≤ 0) hu hu

private theorem antitone_half_sq_sub_exp_sub_one_sub :
    Antitone fun u : ℝ => u ^ 2 / 2 - (exp u - 1 - u) := by
  have hd (u : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2 / 2 - (exp x - 1 - x)) (u + 1 - exp u) u :=
    (((hasDerivAt_pow 2 u).div_const 2).sub
      (((hasDerivAt_exp u).sub_const 1).sub (hasDerivAt_id' u))).congr_deriv (by ring)
  exact antitone_of_deriv_nonpos (fun u => (hd u).differentiableAt) fun u => by
    rw [(hd u).deriv]; linarith [add_one_le_exp u]

private theorem exp_sub_one_sub_le_half_sq_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    exp u - 1 - u ≤ u ^ 2 / 2 := by
  linarith [antitone_half_sq_sub_exp_sub_one_sub hu,
    show (0 : ℝ) ^ 2 / 2 - (exp 0 - 1 - 0) = 0 by norm_num]

private theorem half_sq_le_exp_sub_one_sub_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 / 2 ≤ exp u - 1 - u := by
  linarith [antitone_half_sq_sub_exp_sub_one_sub hu,
    show (0 : ℝ) ^ 2 / 2 - (exp 0 - 1 - 0) = 0 by norm_num]

private theorem sub_two_mul_exp_add_add_two_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ (u - 2) * exp u + u + 2 := by
  have hk1 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ (x - 1) * exp x + 1 :=
    nonneg_of_hasDerivAt_Ici_zero (by norm_num)
      (fun y _ => ((((hasDerivAt_id' y).sub_const 1).mul (hasDerivAt_exp y)).add_const 1)
        |>.congr_deriv (by ring))
      (fun y hy => mul_nonneg hy.le (exp_pos y).le) hx
  exact nonneg_of_hasDerivAt_Ici_zero (by norm_num)
    (fun y _ => (((((hasDerivAt_id' y).sub_const 2).mul (hasDerivAt_exp y)).add
      (hasDerivAt_id' y)).add_const 2).congr_deriv (by ring))
    (fun y hy => hk1 y hy.le) hu

/-- **Scalar Bennett inequality**: since `u ↦ (exp u - 1 - u) / u²` is nondecreasing on `ℝ`, for
every `b > 0` and every `u ≤ b` (including `u ≤ 0`),
`exp u - 1 - u ≤ (u² / b²) * (exp b - 1 - b)`. -/
theorem exp_sub_one_sub_le_mul_sq {b u : ℝ} (hb : 0 < b) (hu : u ≤ b) :
    exp u - 1 - u ≤ (u ^ 2 / b ^ 2) * (exp b - 1 - b) := by
  rcases le_or_gt u 0 with hu0 | hu0
  · calc exp u - 1 - u ≤ u ^ 2 / 2 := exp_sub_one_sub_le_half_sq_of_nonpos hu0
      _ = (u ^ 2 / b ^ 2) * (b ^ 2 / 2) := by field_simp
      _ ≤ (u ^ 2 / b ^ 2) * (exp b - 1 - b) :=
          mul_le_mul_of_nonneg_left (half_sq_le_exp_sub_one_sub_of_nonneg hb.le) (by positivity)
  · have hd (x : ℝ) (hx : 0 < x) :
        HasDerivAt (fun t => (exp t - 1 - t) / t ^ 2) (((x - 2) * exp x + x + 2) / x ^ 3) x :=
      ((((hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id' x)).div
        (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx.ne')).congr_deriv
          (by dsimp only [Pi.sub_apply]; field_simp [hx.ne']; ring)
    have hle := monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (by rwa [interior_Ioi] at hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [interior_Ioi] at hx; rw [(hd x hx).deriv]
        exact div_nonneg (sub_two_mul_exp_add_add_two_nonneg hx.le) (pow_nonneg hx.le 3))
      hu0 hb hu
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at hle
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith

/-- **Rational Bernstein MGF inequality**: for `0 ≤ u < 3`,
`exp u - 1 - u ≤ u² / (2 * (1 - u / 3))`. -/
theorem exp_sub_one_sub_le_div {u : ℝ} (hu0 : 0 ≤ u) (hu3 : u < 3) :
    exp u - 1 - u ≤ u ^ 2 / (2 * (1 - u / 3)) := by
  have hr2_nn (x : ℝ) (hx : 0 ≤ x) : 0 ≤ 2 - (2 - 2 * x) * exp x :=
    nonneg_of_hasDerivAt_Ici_zero (by norm_num)
      (fun y _ =>
        ((hasDerivAt_const y (2 : ℝ)).sub
          (((hasDerivAt_const y (2 : ℝ)).sub
            ((hasDerivAt_id' y).const_mul 2)).mul (hasDerivAt_exp y))).congr_deriv
            (by dsimp only [Pi.sub_apply]; ring))
      (fun y hy => mul_nonneg (mul_nonneg zero_le_two hy.le) (exp_pos y).le) hx
  have hr1_nn (x : ℝ) (hx : 0 ≤ x) : 0 ≤ 2 * x + 4 - (4 - 2 * x) * exp x :=
    nonneg_of_hasDerivAt_Ici_zero (by norm_num)
      (fun y _ =>
        ((((hasDerivAt_id' y).const_mul 2).add_const 4).sub
          (((hasDerivAt_const y (4 : ℝ)).sub
            ((hasDerivAt_id' y).const_mul 2)).mul (hasDerivAt_exp y))).congr_deriv
            (by dsimp only [Pi.sub_apply]; ring))
      (fun y hy => hr2_nn y hy.le) hx
  have hr0_nn : 0 ≤ u ^ 2 + 4 * u + 6 - (6 - 2 * u) * exp u :=
    nonneg_of_hasDerivAt_Ici_zero (by norm_num)
      (fun y _ =>
        ((((hasDerivAt_pow 2 y).add ((hasDerivAt_id' y).const_mul 4)).add_const 6).sub
          (((hasDerivAt_const y (6 : ℝ)).sub
            ((hasDerivAt_id' y).const_mul 2)).mul (hasDerivAt_exp y))).congr_deriv
            (by dsimp only [Pi.sub_apply]; ring))
      (fun y hy => hr1_nn y hy.le) hu0
  rw [le_div_iff₀ (by linarith)]
  nlinarith

end Real

namespace InformationTheory

/-- **Bernstein lower bound on Bennett's function**: for all `u ≥ 0`,
`u² / (2 * (1 + u / 3)) ≤ klFun (1 + u) = (1 + u) log (1 + u) - u`. -/
theorem sq_div_two_mul_le_klFun_one_add {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 / (2 * (1 + u / 3)) ≤ klFun (1 + u) := by
  have hq1_nn (x : ℝ) (hx : 0 ≤ x) :
      0 ≤ Real.log (1 + x) - 3 * x * (6 + x) / (2 * (3 + x) ^ 2) := by
    refine Real.nonneg_of_hasDerivAt_Ici_zero
      (f := fun t => Real.log (1 + t) - 3 * t * (6 + t) / (2 * (3 + t) ^ 2))
      (f' := fun t => 1 / (1 + t) - 27 / (3 + t) ^ 3) (by simp)
      (fun y hy => ?_) (fun y hy => ?_) hx
    · have h1y : 0 < 1 + y := by linarith
      have h3y : 0 < 3 + y := by linarith
      exact ((((hasDerivAt_id' y).const_add 1).log h1y.ne').sub
        ((((hasDerivAt_id' y).const_mul 3).mul ((hasDerivAt_id' y).const_add 6)).div
          ((((hasDerivAt_id' y).const_add 3).pow 2).const_mul 2)
          (by dsimp only [Pi.pow_apply]; positivity))).congr_deriv
            (by dsimp only [Pi.mul_apply, Pi.pow_apply]; field_simp [h1y.ne', h3y.ne']; ring)
    · have h1y : 0 < 1 + y := by linarith
      have h3y : 0 < 3 + y := by linarith
      rw [show 1 / (1 + y) - 27 / (3 + y) ^ 3 =
        y ^ 2 * (9 + y) / ((1 + y) * (3 + y) ^ 3) by field_simp [h1y.ne', h3y.ne']; ring]
      exact div_nonneg (mul_nonneg (sq_nonneg y) (by linarith)) (by positivity)
  have hq0_nn : 0 ≤ klFun (1 + u) - 3 * u ^ 2 / (2 * (3 + u)) :=
    Real.nonneg_of_hasDerivAt_Ici_zero
      (f := fun t => klFun (1 + t) - 3 * t ^ 2 / (2 * (3 + t)))
      (f' := fun t => Real.log (1 + t) - 3 * t * (6 + t) / (2 * (3 + t) ^ 2))
      (by simp [klFun_one])
      (fun x hx => by
        have h1x : 0 < 1 + x := by linarith
        have h3x : 0 < 3 + x := by linarith
        exact (((hasDerivAt_klFun h1x.ne').comp x ((hasDerivAt_id' x).const_add 1)).sub
          (((hasDerivAt_pow 2 x).const_mul 3).div
            (((hasDerivAt_id' x).const_add 3).const_mul 2) (by positivity))).congr_deriv
              (by field_simp [h3x.ne']; ring))
      (fun y hy => hq1_nn y hy.le) hu
  have h3u : 0 < 3 + u := by linarith
  linarith [show u ^ 2 / (2 * (1 + u / 3)) = 3 * u ^ 2 / (2 * (3 + u)) by field_simp [h3u.ne']]

end InformationTheory

namespace Cslib.Probability

/-- Exact Laplace-parameter evaluation at `s = (1 / b) log (1 + b ε / v)` (`b > 0, v > 0, ε ≥ 0`),
turning `(v / b²) (exp (s b) - 1 - s b) - s ε` into `-(v / b²) klFun (1 + b ε / v)`. -/
theorem bennett_laplace_exponent_eq {b v ε : ℝ} (hb : 0 < b) (hv : 0 < v) (hε : 0 ≤ ε) :
    let s := (1 / b) * Real.log (1 + b * ε / v)
    0 ≤ s ∧
      (v / b ^ 2) * (Real.exp (s * b) - 1 - s * b) - s * ε =
        -(v / b ^ 2) * klFun (1 + b * ε / v) := by
  intro s
  refine ⟨mul_nonneg (by positivity)
    (Real.log_nonneg (by linarith [show 0 ≤ b * ε / v by positivity])), ?_⟩
  rw [show s * b = Real.log (1 + b * ε / v) by dsimp only [s]; field_simp,
    Real.exp_log (by positivity), klFun_apply]
  dsimp only [s]
  field_simp
  ring

/-- Bennett's Poisson tail `exp (-(v / b²) klFun (1 + b ε / v))` is bounded above by Bernstein's
rational tail `exp (-ε² / (2 (v + b ε / 3)))` (`b > 0, v > 0, ε ≥ 0`). -/
theorem exp_neg_klFun_le_exp_bernstein {b v ε : ℝ} (hb : 0 < b) (hv : 0 < v) (hε : 0 ≤ ε) :
    Real.exp (-(v / b ^ 2) * klFun (1 + b * ε / v)) ≤
      Real.exp (-ε ^ 2 / (2 * (v + b * ε / 3))) := by
  have hden : 0 < v + b * ε / 3 := by positivity
  rw [Real.exp_le_exp, neg_div, neg_mul,
    ← show (v / b ^ 2) * ((b * ε / v) ^ 2 / (2 * (1 + (b * ε / v) / 3))) =
      ε ^ 2 / (2 * (v + b * ε / 3)) by field_simp [hb.ne', hv.ne', hden.ne']]
  exact neg_le_neg (mul_le_mul_of_nonneg_left
    (sq_div_two_mul_le_klFun_one_add (by positivity)) (by positivity))

/-- Quadratic Bernstein tail inversion: for `v, b ≥ 0`, `δ ∈ (0, 1)`, and `0 < v ∨ 0 < b`, setting
`ε = √(2 v log (1 / δ)) + 2 b log (1 / δ) / 3` gives `exp (-ε² / (2 (v + b ε / 3))) ≤ δ`. -/
theorem exp_bernstein_le_of_sqrt_add {v b δ : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hvb : 0 < v ∨ 0 < b) :
    let L := Real.log (1 / δ)
    let ε := Real.sqrt (2 * v * L) + 2 * b * L / 3
    0 < ε ∧ Real.exp (-ε ^ 2 / (2 * (v + b * ε / 3))) ≤ δ := by
  intro L ε
  have hL : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hε_pos : 0 < ε := hvb.elim
    (fun hv' => add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr (by positivity)) (by positivity))
    fun hb' => add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (by positivity)
  have hden : 0 < 2 * (v + b * ε / 3) := by rcases hvb with hv' | hb' <;> positivity
  have hdiv : -ε ^ 2 / (2 * (v + b * ε / 3)) ≤ -L := (div_le_iff₀ hden).mpr (by
    dsimp only [ε]
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 * v * L by positivity),
      show 0 ≤ b * L * Real.sqrt (2 * v * L) by positivity])
  refine ⟨hε_pos, (Real.exp_le_exp.mpr hdiv).trans_eq ?_⟩
  dsimp only [L]; rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ]

end Cslib.Probability

/-! ### Measure-theoretic one-step Bennett MGF bound -/

namespace ProbabilityTheory

/-- **Measure-theoretic one-step Bennett MGF bound**: if `X` is integrable with `∫ X ∂μ ≤ 0`,
`X ≤ b` a.e. (`b > 0`), and `∫ X² ∂μ ≤ v` (`X²` integrable) under a probability measure `μ`, then
`mgf X μ t ≤ exp ((v / b²) (exp (t b) - 1 - t b))` for every `t ≥ 0`. -/
theorem mgf_le_exp_bennett_of_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {b v t : ℝ}
    (hX : Integrable X μ) (hX2 : Integrable (fun ω => X ω ^ 2) μ)
    (hmean : ∫ ω, X ω ∂μ ≤ 0) (hb : 0 < b) (hupper : ∀ᵐ ω ∂μ, X ω ≤ b)
    (hvar : ∫ ω, X ω ^ 2 ∂μ ≤ v) (ht : 0 ≤ t) :
    mgf X μ t ≤ Real.exp ((v / b ^ 2) * (Real.exp (t * b) - 1 - t * b)) := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · simp [mgf]
  · set c := (Real.exp (t * b) - 1 - t * b) / b ^ 2
    have hc_nn : 0 ≤ c := div_nonneg (by linarith [Real.add_one_le_exp (t * b)]) (by positivity)
    have hint1 : Integrable (fun ω : Ω => (1 : ℝ) + t * X ω) μ :=
      (integrable_const (1 : ℝ)).add (hX.const_mul t)
    have hint2 : Integrable (fun ω : Ω => c * X ω ^ 2) μ := hX2.const_mul c
    have hint_le : ∫ ω, Real.exp (t * X ω) ∂μ ≤ 1 + t * ∫ ω, X ω ∂μ + c * ∫ ω, X ω ^ 2 ∂μ := by
      refine (integral_mono_ae (integrable_exp_mul_of_le t b ht hX.aemeasurable hupper)
        (g := fun ω => (1 + t * X ω) + c * X ω ^ 2) (hint1.add hint2) ?_).trans_eq ?_
      · filter_upwards [hupper] with ω hω
        linarith [Real.exp_sub_one_sub_le_mul_sq (mul_pos ht_pos hb)
          (mul_le_mul_of_nonneg_left hω ht),
          show (t * X ω) ^ 2 / (t * b) ^ 2 * (Real.exp (t * b) - 1 - t * b) = c * X ω ^ 2 by
            dsimp only [c]; field_simp [ht_pos.ne', hb.ne']]
      · rw [integral_add hint1 hint2, integral_add (integrable_const (1 : ℝ)) (hX.const_mul t),
          integral_const, probReal_univ, smul_eq_mul, mul_one, integral_const_mul,
          integral_const_mul]
    rw [mgf]
    have hmean_np := mul_nonpos_of_nonneg_of_nonpos ht hmean
    have hvar_le : c * ∫ ω, X ω ^ 2 ∂μ ≤ (v / b ^ 2) * (Real.exp (t * b) - 1 - t * b) :=
      (mul_le_mul_of_nonneg_left hvar hc_nn).trans_eq (by dsimp only [c]; ring)
    linarith [Real.add_one_le_exp ((v / b ^ 2) * (Real.exp (t * b) - 1 - t * b))]

/-- **Bennett Chernoff tail bound from a Bennett MGF estimate**: if `mgf X μ t` is bounded by
`exp ((v / b²) (exp (t b) - 1 - t b))` for every `t ≥ 0` (`b > 0, v > 0, ε ≥ 0`) and `X` is a.e.
bounded above so `exp (t X)` is integrable, then
`μ.real {ω | ε ≤ X ω} ≤ exp (-(v / b²) * klFun (1 + b ε / v))`. -/
theorem measure_ge_le_bennett_of_mgf_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {B b v ε : ℝ} (hX : AEMeasurable X μ)
    (hB : ∀ᵐ ω ∂μ, X ω ≤ B) (hb : 0 < b) (hv : 0 < v) (hε : 0 ≤ ε)
    (hmgf : ∀ t : ℝ, 0 ≤ t → mgf X μ t ≤ Real.exp ((v / b ^ 2) * (Real.exp (t * b) - 1 - t * b))) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-(v / b ^ 2) * klFun (1 + b * ε / v)) := by
  obtain ⟨hs, hexp⟩ := Cslib.Probability.bennett_laplace_exponent_eq hb hv hε
  set s := (1 / b) * Real.log (1 + b * ε / v)
  calc μ.real {ω | ε ≤ X ω}
      ≤ Real.exp (-s * ε) * mgf X μ s :=
        measure_ge_le_exp_mul_mgf ε hs (integrable_exp_mul_of_le s B hs hX hB)
    _ ≤ Real.exp (-s * ε) * Real.exp ((v / b ^ 2) * (Real.exp (s * b) - 1 - s * b)) :=
        mul_le_mul_of_nonneg_left (hmgf s hs) (Real.exp_pos _).le
    _ = Real.exp ((v / b ^ 2) * (Real.exp (s * b) - 1 - s * b) - s * ε) := by
        rw [← Real.exp_add]; congr 1; ring
    _ = Real.exp (-(v / b ^ 2) * klFun (1 + b * ε / v)) := congrArg Real.exp hexp

end ProbabilityTheory

/-! ### Discrete `PMF` one-step Bennett MGF bounds -/

namespace Cslib.Probability.PMF

variable {α : Type*}

/-- **One-sided discrete Bennett MGF step**: on an arbitrary `q : PMF α` (without `[Fintype α]` or
`[MeasurableSpace α]`), if an increment `d : α → ℝ` has summable first and second moments against
`(q ·).toReal`, nonpositive mean `∑' x, (q x).toReal * d x ≤ 0`, upper bound `d x ≤ b` (`b > 0`) on
`q.support`, and second moment `∑' x, (q x).toReal * d x ^ 2 ≤ v`, then for every `s ≥ 0`,
`∑' x, q x * ofReal (exp (s * d x)) ≤ ofReal (exp ((v / b²) (exp (s b) - 1 - s b)))`. -/
theorem tsum_mul_exp_le_bennett (q : PMF α) (d : α → ℝ) {b v : ℝ}
    (hd1 : Summable fun x => (q x).toReal * d x)
    (hd2 : Summable fun x => (q x).toReal * d x ^ 2)
    (hmean : ∑' x, (q x).toReal * d x ≤ 0)
    (hb : 0 < b) (hupper : ∀ x ∈ q.support, d x ≤ b)
    (hvar : ∑' x, (q x).toReal * d x ^ 2 ≤ v) {s : ℝ} (hs : 0 ≤ s) :
    ∑' x, q x * ENNReal.ofReal (Real.exp (s * d x)) ≤
      ENNReal.ofReal (Real.exp ((v / b ^ 2) * (Real.exp (s * b) - 1 - s * b))) := by
  classical
  rcases eq_or_lt_of_le hs with rfl | hs_pos
  · simp
  · let d' (x : α) : ℝ := if x ∈ q.support then d x else 0
    have hd'_le (x : α) : d' x ≤ b := by
      dsimp only [d']
      split_ifs with hx
      · exact hupper x hx
      exact hb.le
    have hmul (f : ℝ → ℝ) (hf : f 0 = 0) :
        (fun x => (q x).toReal * f (d' x)) = fun x => (q x).toReal * f (d x) := by
      ext x
      dsimp only [d']
      split_ifs with hx
      · rfl
      rw [(q.apply_eq_zero_iff x).mpr hx, ENNReal.toReal_zero, zero_mul, zero_mul]
    have hmul1 := hmul (fun z => z) rfl
    have hmul2 := hmul (· ^ 2) (by norm_num)
    have hsum_exp : Summable fun x => (q x).toReal * Real.exp (s * d' x) :=
      Summable.of_nonneg_of_le (fun _ => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
        (fun x => mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hd'_le x) hs)) ENNReal.toReal_nonneg)
        ((summable_toReal q).mul_right (Real.exp (s * b)))
    set c := (Real.exp (s * b) - 1 - s * b) / b ^ 2
    have hc_nn : 0 ≤ c := div_nonneg (by linarith [Real.add_one_le_exp (s * b)]) (by positivity)
    have hsd1 : Summable fun x => (q x).toReal * d' x := hmul1.symm ▸ hd1
    have hsd2 : Summable fun x => (q x).toReal * d' x ^ 2 := hmul2.symm ▸ hd2
    have hpt (x : α) : (q x).toReal * Real.exp (s * d' x) ≤
        (q x).toReal + s * ((q x).toReal * d' x) + c * ((q x).toReal * d' x ^ 2) := by
      have hexp : Real.exp (s * d' x) ≤ 1 + s * d' x + c * d' x ^ 2 := by
        linarith [Real.exp_sub_one_sub_le_mul_sq (mul_pos hs_pos hb)
          (mul_le_mul_of_nonneg_left (hd'_le x) hs),
          show (s * d' x) ^ 2 / (s * b) ^ 2 * (Real.exp (s * b) - 1 - s * b) = c * d' x ^ 2 by
            dsimp only [c]; field_simp [hs_pos.ne', hb.ne']]
      exact (mul_le_mul_of_nonneg_left hexp ENNReal.toReal_nonneg).trans_eq (by ring)
    have htsum_le := hsum_exp.tsum_le_tsum hpt
      (((summable_toReal q).add (hsd1.mul_left s)).add (hsd2.mul_left c))
    rw [((summable_toReal q).add (hsd1.mul_left s)).tsum_add (hsd2.mul_left c),
      (summable_toReal q).tsum_add (hsd1.mul_left s), tsum_toReal, tsum_mul_left, tsum_mul_left,
      hmul1, hmul2] at htsum_le
    have hmean_np := mul_nonpos_of_nonneg_of_nonpos hs hmean
    have hvar_le : c * ∑' x, (q x).toReal * d x ^ 2 ≤
        (v / b ^ 2) * (Real.exp (s * b) - 1 - s * b) :=
      (mul_le_mul_of_nonneg_left hvar hc_nn).trans_eq (by dsimp only [c]; ring)
    rw [show ∑' x, q x * ENNReal.ofReal (Real.exp (s * d x)) =
        ENNReal.ofReal (∑' x, (q x).toReal * Real.exp (s * d' x)) by
      rw [ENNReal.ofReal_tsum_of_nonneg
        (fun _ => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) hsum_exp]
      refine tsum_congr fun x => ?_
      dsimp only [d']; split_ifs with hx
      · rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top q x)]
      · rw [(q.apply_eq_zero_iff x).mpr hx, ENNReal.toReal_zero, zero_mul, zero_mul,
          ENNReal.ofReal_zero]]
    exact ENNReal.ofReal_le_ofReal (by
      linarith [Real.add_one_le_exp ((v / b ^ 2) * (Real.exp (s * b) - 1 - s * b))])

/-- **Centered Bennett MGF step** on an arbitrary `q : PMF α` when `g` is bounded in absolute value
on `q.support` (`g x - μ_g ≤ b`, `b > 0`) and has variance at most `v`. -/
theorem tsum_mul_exp_sub_mean_le_bennett (q : PMF α) (g : α → ℝ) {b v : ℝ} (hb : 0 < b)
    (hg_bdd : ∃ C : ℝ, ∀ x ∈ q.support, |g x| ≤ C)
    (hupper : ∀ x ∈ q.support, g x - (∑' y, (q y).toReal * g y) ≤ b)
    (hvar : ∑' x, (q x).toReal * (g x - ∑' y, (q y).toReal * g y) ^ 2 ≤ v)
    {s : ℝ} (hs : 0 ≤ s) :
    ∑' x, q x * ENNReal.ofReal (Real.exp (s * (g x - ∑' y, (q y).toReal * g y))) ≤
      ENNReal.ofReal (Real.exp ((v / b ^ 2) * (Real.exp (s * b) - 1 - s * b))) := by
  obtain ⟨C, hC⟩ := hg_bdd
  set μ := ∑' y, (q y).toReal * g y
  have hsum_g := summable_toReal_mul_of_abs_le q g hC
  have heq : (fun x => (q x).toReal * (g x - μ)) =
      fun x => (q x).toReal * g x - (q x).toReal * μ := funext fun x => by ring
  exact tsum_mul_exp_le_bennett q (fun x => g x - μ)
    (heq.symm ▸ hsum_g.sub ((summable_toReal q).mul_right μ))
    (summable_toReal_mul_of_abs_le q _ fun x hx => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add_left (hC x hx) _)) 2)
    (by rw [heq, hsum_g.tsum_sub ((summable_toReal q).mul_right μ), tsum_mul_right, tsum_toReal,
      one_mul, sub_self])
    hb hupper hvar hs

/-- Finite-type centered Bennett MGF bound on `q : PMF α`. -/
theorem sum_mul_exp_sub_mean_le_bennett [Fintype α] (q : PMF α) (g : α → ℝ) {b v : ℝ} (hb : 0 < b)
    (hupper : ∀ x ∈ q.support, g x - (∑ y, (q y).toReal * g y) ≤ b)
    (hvar : ∑ x, (q x).toReal * (g x - ∑ y, (q y).toReal * g y) ^ 2 ≤ v)
    {s : ℝ} (hs : 0 ≤ s) :
    ∑ x, (q x).toReal * Real.exp (s * (g x - ∑ y, (q y).toReal * g y)) ≤
      Real.exp ((v / b ^ 2) * (Real.exp (s * b) - 1 - s * b)) := by
  have hb_bdd : ∃ C : ℝ, ∀ x ∈ q.support, |g x| ≤ C :=
    ⟨∑ x : α, |g x|, fun x _ =>
      Finset.single_le_sum (fun y _ => abs_nonneg (g y)) (Finset.mem_univ x)⟩
  have h := tsum_mul_exp_sub_mean_le_bennett q g hb hb_bdd
    (by simpa only [tsum_fintype] using hupper)
    (by simpa only [tsum_fintype] using hvar) hs
  rw [tsum_fintype] at h
  have hm := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_sum fun x _ =>
    ENNReal.mul_ne_top (PMF.apply_ne_top q x) ENNReal.ofReal_ne_top] at hm
  simpa only [tsum_fintype, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using hm

end Cslib.Probability.PMF
