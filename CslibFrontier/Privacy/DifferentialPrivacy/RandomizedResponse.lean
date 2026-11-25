/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Privacy.DifferentialPrivacy.Hamming
public import CslibFrontier.Privacy.DifferentialPrivacy.Renyi
public import CslibFrontier.Languages.Probabilistic.Vector
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.Tactic.ENNRealToReal

/-!
# Randomized response

Randomized response [DworkRoth2014, §3.2] is a survey protocol for a yes/no question. The
respondent flips a coin. On tails they answer truthfully; on heads they flip a second coin and
answer "Yes" on heads and "No" on tails. `randomizedResponse truth` is this protocol as a
`ProbComp Bool` program over fair coins, with `true` for "Yes" and for a truthful answer. The
privacy statements apply `DifferentiallyPrivate` to its output law
`ProbComp.eval (randomizedResponse truth)`: the protocol is a finite program, and only its
semantics is a `PMF`.

The answer agrees with the truth with probability `3/4` (`eval_randomizedResponse_apply`), so
randomized response is `(ln 3, 0)`-differentially private for a single respondent
(`differentiallyPrivate_randomizedResponse`) [DworkRoth2014, Claim 3.5], and `ln 3` is optimal
(`differentiallyPrivate_randomizedResponse_iff`).

`randomizedResponseSurvey x` lets each of `n` respondents answer independently. It is
`(ln 3, 0)`-private for Hamming adjacency (`differentiallyPrivate_randomizedResponseSurvey`). The
expected number of "Yes" answers is `n / 4 + (number of true "Yes") / 2`
(`sum_eval_randomizedResponseSurvey_mul_card`), so twice the fraction of "Yes" answers minus
`1/2` is an unbiased estimator of the true fraction
(`sum_eval_randomizedResponseSurvey_mul_estimator`) [DworkRoth2014, §2.3].

## Main definitions

* `Cslib.Privacy.randomizedResponse`: one respondent's randomized response.
* `Cslib.Privacy.randomizedResponseSurvey`: `n` independent respondents.

## Main results

* `Cslib.Privacy.differentiallyPrivate_randomizedResponse`,
  `Cslib.Privacy.differentiallyPrivate_randomizedResponse_iff`: exactly `(ln 3, 0)`-private.
* `Cslib.Privacy.differentiallyPrivate_randomizedResponseSurvey`: the survey is
  `(ln 3, 0)`-private for Hamming adjacency.
* `Cslib.Privacy.renyiDifferentiallyPrivate_randomizedResponse`,
  `Cslib.Privacy.renyiDifferentiallyPrivate_randomizedResponseSurvey`: order-`α` Rényi
  differential privacy [Mironov2017, Proposition 5].
* `Cslib.Privacy.sum_eval_randomizedResponseSurvey_mul_estimator`: the unbiased estimator.

## References

* [DworkRoth2014]
* [Mironov2017]
-/

open scoped ENNReal

public section

namespace Cslib.Privacy

/-- Randomized response [DworkRoth2014, §3.2]: flip a coin; on tails (`truthful = true`) answer
truthfully, and on heads answer with a second fair coin. -/
noncomputable def randomizedResponse (truth : Bool) : ProbComp Bool := do
  let truthful ← ProbComp.uniform Bool
  if truthful then return truth else ProbComp.uniform Bool

/-- Randomized response agrees with the truth with probability `3/4`. -/
theorem eval_randomizedResponse_apply (truth answer : Bool) :
    ProbComp.eval (randomizedResponse truth) answer = if answer = truth then 3 / 4 else 1 / 4 := by
  simp only [randomizedResponse, ProbComp.eval_bind, ProbComp.eval_uniform, PMF.bind_apply,
    tsum_fintype, Fintype.sum_bool, Probability.PMF.uniformOfFintype_apply, Fintype.card_bool,
    ite_true, Bool.false_eq_true, ite_false, ProbComp.eval_pure, PMF.pure_apply]
  have h1 : (2 : ℝ≥0∞)⁻¹ * 2⁻¹ = 4⁻¹ := by
    rw [← ENNReal.mul_inv (by simp) (by simp)]; norm_num
  have h3 : (2 : ℝ≥0∞)⁻¹ + 4⁻¹ = 3 / 4 := by
    ennreal_to_real
    norm_num
  cases truth <;> cases answer <;> simp [h1, h3]

/-- Randomized response is `(ln 3, 0)`-differentially private for a single respondent, whose
datum may change arbitrarily [DworkRoth2014, Claim 3.5]. -/
theorem differentiallyPrivate_randomizedResponse :
    DifferentiallyPrivate (fun _ _ => True) (fun truth => ProbComp.eval (randomizedResponse truth))
      (Real.log 3) 0 := by
  refine DifferentiallyPrivate.of_apply_le fun x y _ r => ?_
  rw [Real.exp_log (by norm_num), ENNReal.ofReal_ofNat, eval_randomizedResponse_apply,
    eval_randomizedResponse_apply]
  split_ifs <;> ennreal_to_real <;> norm_num

/-- `ln 3` is optimal: randomized response is `(ε, 0)`-differentially private exactly when
`ln 3 ≤ ε`. -/
theorem differentiallyPrivate_randomizedResponse_iff {ε : ℝ} :
    DifferentiallyPrivate (fun _ _ => True) (fun truth => ProbComp.eval (randomizedResponse truth))
      ε 0 ↔ Real.log 3 ≤ ε := by
  refine ⟨fun h => ?_, fun h => differentiallyPrivate_randomizedResponse.mono h le_rfl⟩
  have key := DifferentiallyPrivate.iff_apply_le.mp h (x := true) (y := false) trivial true
  simp only [eval_randomizedResponse_apply, ite_true, Bool.true_eq_false, ite_false] at key
  ennreal_to_real at key
  exact (Real.log_le_iff_le_exp (by norm_num)).mpr (by linarith)

/-- The survey in which each of `n` respondents independently applies randomized response to
their own answer. -/
noncomputable def randomizedResponseSurvey {n : ℕ} (x : Fin n → Bool) : ProbComp (Fin n → Bool) :=
  OracleComp.pi fun i => randomizedResponse (x i)

/-- The survey's answers are independent randomized responses. -/
theorem eval_randomizedResponseSurvey {n : ℕ} (x : Fin n → Bool) :
    ProbComp.eval (randomizedResponseSurvey x) =
      Probability.PMF.pi fun i => ProbComp.eval (randomizedResponse (x i)) :=
  ProbComp.eval_pi _

/-- The randomized-response survey is `(ln 3, 0)`-differentially private for Hamming
adjacency. -/
theorem differentiallyPrivate_randomizedResponseSurvey (n : ℕ) :
    DifferentiallyPrivate HammingAdjacent
      (fun x : Fin n → Bool => ProbComp.eval (randomizedResponseSurvey x)) (Real.log 3) 0 := by
  simp only [eval_randomizedResponseSurvey]
  exact DifferentiallyPrivate.pi (M := fun _ truth => ProbComp.eval (randomizedResponse truth))
    (Real.log_nonneg (by norm_num)) fun _ => differentiallyPrivate_randomizedResponse

private theorem renyiMoment_randomizedResponse_ne {α : ℝ} {x y : Bool} (hxy : x ≠ y) :
    Probability.renyiMoment α (ProbComp.eval (randomizedResponse x))
      (ProbComp.eval (randomizedResponse y)) =
      ENNReal.ofReal ((3 / 4) * (3 : ℝ) ^ (α - 1) + (1 / 4) * (3 : ℝ) ^ (1 - α)) := by
  have hc34 : (3 : ℝ≥0∞) / 4 = ENNReal.ofReal (3 / 4) := by ennreal_to_real
  have hc14 : (1 : ℝ≥0∞) / 4 = ENNReal.ofReal (1 / 4) := by ennreal_to_real
  have h1 : ((3 : ℝ≥0∞) / 4) * (((3 : ℝ≥0∞) / 4) / (1 / 4)) ^ (α - 1) =
      ENNReal.ofReal ((3 / 4) * (3 : ℝ) ^ (α - 1)) := by
    rw [hc34, hc14, ← ENNReal.ofReal_div_of_pos (by norm_num),
      show (3 / 4 : ℝ) / (1 / 4) = 3 by norm_num, ENNReal.ofReal_rpow_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
  have h2 : ((1 : ℝ≥0∞) / 4) * (((1 : ℝ≥0∞) / 4) / (3 / 4)) ^ (α - 1) =
      ENNReal.ofReal ((1 / 4) * (3 : ℝ) ^ (1 - α)) := by
    rw [hc14, hc34, ← ENNReal.ofReal_div_of_pos (by norm_num),
      ENNReal.ofReal_rpow_of_pos (by norm_num),
      show ((1 / 4 : ℝ) / (3 / 4)) = 3⁻¹ by norm_num, Real.inv_rpow (by norm_num),
      ← Real.rpow_neg (by norm_num), show -(α - 1) = 1 - α by ring,
      ← ENNReal.ofReal_mul (by norm_num)]
  rw [Probability.renyiMoment, tsum_fintype, Fintype.sum_bool]
  cases x <;> cases y <;> try exact absurd rfl hxy
  · simp only [eval_randomizedResponse_apply, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
      h1, h2]
    rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))]
    exact congrArg ENNReal.ofReal (add_comm _ _)
  · simp only [eval_randomizedResponse_apply, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
      h1, h2]
    rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))]

/-- Randomized response satisfies
`(α, log ((3 / 4) · 3 ^ (α - 1) + (1 / 4) · 3 ^ (1 - α)) / (α - 1))`-Rényi differential privacy
for every `1 < α` [Mironov2017, Proposition 5]. -/
theorem renyiDifferentiallyPrivate_randomizedResponse {α : ℝ} (hα : 1 < α) :
    RenyiDifferentiallyPrivate (fun _ _ => True)
      (fun truth => ProbComp.eval (randomizedResponse truth)) α
      (Real.log ((3 / 4) * (3 : ℝ) ^ (α - 1) + (1 / 4) * (3 : ℝ) ^ (1 - α)) / (α - 1)) := by
  set M : ℝ := (3 / 4) * (3 : ℝ) ^ (α - 1) + (1 / 4) * (3 : ℝ) ^ (1 - α)
  have hM1 : 1 ≤ M := ENNReal.one_le_ofReal.mp <| by
    simpa only [renyiMoment_randomizedResponse_ne (by decide : true ≠ false)] using
      Probability.PMF.one_le_renyiMoment hα
        (ProbComp.eval (randomizedResponse true)) (ProbComp.eval (randomizedResponse false))
  have hε_nn : 0 ≤ Real.log M / (α - 1) := div_nonneg (Real.log_nonneg hM1) (sub_pos.mpr hα).le
  refine ⟨hα, hε_nn, fun x y _ => ?_⟩
  rcases eq_or_ne x y with rfl | hxy
  · simp
  · rw [Probability.PMF.renyiDiv_le_ofReal_iff hα _ _ hε_nn, renyiMoment_randomizedResponse_ne hxy,
      mul_div_cancel₀ _ (sub_pos.mpr hα).ne', Real.exp_log (by positivity)]

/-- The `n`-respondent randomized-response survey satisfies the same order-`α` Rényi differential
privacy bound under `HammingAdjacent` for every `1 < α`. -/
theorem renyiDifferentiallyPrivate_randomizedResponseSurvey (n : ℕ) {α : ℝ} (hα : 1 < α) :
    RenyiDifferentiallyPrivate HammingAdjacent
      (fun x : Fin n → Bool => ProbComp.eval (randomizedResponseSurvey x)) α
      (Real.log ((3 / 4) * (3 : ℝ) ^ (α - 1) + (1 / 4) * (3 : ℝ) ^ (1 - α)) / (α - 1)) := by
  simp only [eval_randomizedResponseSurvey]
  exact RenyiDifferentiallyPrivate.pi (M := fun _ truth => ProbComp.eval (randomizedResponse truth))
    hα (renyiDifferentiallyPrivate_randomizedResponse hα).2.1
    fun _ => renyiDifferentiallyPrivate_randomizedResponse hα

/-- The expected number of "Yes" answers is `n / 4 + (number of true "Yes") / 2`
[DworkRoth2014, §2.3]. -/
theorem sum_eval_randomizedResponseSurvey_mul_card {n : ℕ} (x : Fin n → Bool) :
    ∑ answers, (ProbComp.eval (randomizedResponseSurvey x) answers).toReal *
        (Finset.univ.filter fun i => answers i = true).card =
      n / 4 + (Finset.univ.filter fun i => x i = true).card / 2 := by
  have hcard (a : Fin n → Bool) : ((Finset.univ.filter fun i => a i = true).card : ℝ) =
      ∑ i, if a i = true then 1 else 0 := by
    rw [Finset.card_filter]
    push_cast; rfl
  simp only [hcard, eval_randomizedResponseSurvey]
  rw [Probability.PMF.sum_pi_mul_sum (fun i => ProbComp.eval (randomizedResponse (x i)))
    (fun _ b => if b = true then (1 : ℝ) else 0)]
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false, mul_one, mul_zero, add_zero,
    eval_randomizedResponse_apply]
  rw [show (n : ℝ) / 4 + (∑ i, if x i = true then (1 : ℝ) else 0) / 2 =
      ∑ i, (1 / 4 + (if x i = true then (1 : ℝ) else 0) / 2) by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_div]
    ring]
  exact Finset.sum_congr rfl fun i _ => by cases x i <;> norm_num

/-- The estimator `2 · (fraction of "Yes" answers) - 1/2` is unbiased for the fraction of
respondents whose true answer is "Yes" [DworkRoth2014, §2.3]. -/
theorem sum_eval_randomizedResponseSurvey_mul_estimator {n : ℕ} (hn : n ≠ 0) (x : Fin n → Bool) :
    ∑ answers, (ProbComp.eval (randomizedResponseSurvey x) answers).toReal *
        (2 * ((Finset.univ.filter fun i => answers i = true).card / n) - 1 / 2) =
      (Finset.univ.filter fun i => x i = true).card / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  set μ := ProbComp.eval (randomizedResponseSurvey x)
  calc ∑ answers, (μ answers).toReal *
        (2 * ((Finset.univ.filter fun i => answers i = true).card / n) - 1 / 2)
      = 2 / n * ∑ answers, (μ answers).toReal *
            (Finset.univ.filter fun i => answers i = true).card -
          1 / 2 * ∑ answers, (μ answers).toReal := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring
    _ = (Finset.univ.filter fun i => x i = true).card / n := by
        rw [sum_eval_randomizedResponseSurvey_mul_card, Probability.PMF.sum_toReal]
        field_simp
        ring

end Cslib.Privacy
