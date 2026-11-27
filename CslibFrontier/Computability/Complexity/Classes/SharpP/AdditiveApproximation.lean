/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP.Relation
public import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import Mathlib.Data.Int.Log

/-!
# Additive approximation of counts of exact-length solutions

For an `NPRelation R` with `r`-bit witnesses, sample uniform `r`-bit strings and test the verifier.
The rational output is `2 ^ r * successes / trials`. With inverse accuracy `k > 0` and confidence
`t`, `2 (t + 1) k²` trials give additive error at most `2 ^ r / k`, except with probability
strictly less than `2⁻ᵗ`.

This is [Goldreich2007Draft], Proposition 6.23 (printed p. 233, February 2007 draft), using
unary inverse accuracy and unary logarithmic confidence as in the library's FPRAS interface.
Fixing `k = p(|enc a|)` for any positive natural-coefficient polynomial gives its running time
polynomial in input length and logarithmic confidence. The output is a numerator/denominator
pair in binary, representing an exact rational, rather than a rounded integer. Sampling,
verification, repetition, the exponential scale in binary and output arithmetic all have native
strict PPT certificates. Exact witness length is essential to this estimator's scale.
-/

public section

namespace Cslib.Complexity.NPRelation

open Turing.MultiTapeTM ComputableInPolyTime Probability

variable {α : Type} {enc : α ↪ List Bool}

/-- Input instance (framed), then unary inverse accuracy (framed), then unary logarithmic
confidence. This is the same layout as the generic FPRAS parameters. -/
abbrev encAdditiveApproximationInput (enc : α ↪ List Bool) : α × ℕ × ℕ ↪ List Bool :=
  encPair enc (encPair encUnary encUnary)

/-- Sample and check one uniformly random certificate of the relation's prescribed length. -/
private noncomputable def countingTrial (R : NPRelation enc) (a : α) : ProbComp Bool :=
  R.verifier.curry a <$> BitString.sampleList (R.certLength.eval (enc a).length)

/-- Rational additive estimator: numerator and positive denominator, both encoded in binary.
The trial count is `2 (t + 1) k²`; correctness requires `k > 0`. -/
noncomputable def additiveEstimate (R : NPRelation enc) (a : α) (k t : ℕ) : ProbComp (ℕ × ℕ) :=
  (fun successes => (successes * 2 ^ R.certLength.eval (enc a).length, 2 * (t + 1) * k ^ 2)) <$>
    OracleComp.countTrue (2 * (t + 1) * k ^ 2) (R.countingTrial a)

/-- Uniform fair-bit sampling followed by the native verifier is strict PPT. -/
private theorem isPPTOn_countingTrial (R : NPRelation enc) : IsPPTOn enc encBool R.countingTrial :=
  IsPPTOn.of_seeded ((unary_eval R.certLength).comp (encoding_length enc))
    R.computableInPolyTime_verifier

/-- The rational additive estimator is strict PPT, with unary accuracy/confidence parameters.
The value `2 ^ r` is constructed in binary from unary `r`, so its cost is polynomial in `r`. -/
theorem isPPTOn_additiveEstimate (R : NPRelation enc) :
    IsPPTOn (encAdditiveApproximationInput enc) (encPair encNat encNat)
      (fun q : α × ℕ × ℕ => R.additiveEstimate q.1 q.2.1 q.2.2) := by
  have htrial := R.isPPTOn_countingTrial.preprocess
    (fst enc (encPair encUnary encUnary))
  have hcount : ComputableInPolyTime (fun q : α × ℕ × ℕ => 2 * (q.2.2 + 1) * q.2.1 ^ 2)
      (encAdditiveApproximationInput enc) encUnary := by fun_prop
  have hpost : ComputableInPolyTime
      (fun q : (α × ℕ × ℕ) × ℕ =>
        (q.2 * 2 ^ R.certLength.eval (enc q.1.1).length, 2 * (q.1.2.2 + 1) * q.1.2.1 ^ 2))
      (encPair (encAdditiveApproximationInput enc) encUnary) (encPair encNat encNat) := by
    have hr : ComputableInPolyTime
        (fun q : (α × ℕ × ℕ) × ℕ => R.certLength.eval (enc q.1.1).length)
        (encPair (encAdditiveApproximationInput enc) encUnary) encUnary :=
      (unary_eval R.certLength).comp ((encoding_length enc).comp ((fst _ _).comp (fst _ _)))
    exact (binary_mul' (unary_to_binary.comp (snd _ _)) (binary_two_pow.comp hr)).prod
      (unary_to_binary.comp (hcount.comp (fst _ _)))
  simpa only [additiveEstimate] using (htrial.countTrue hcount).map_with hpost

private theorem countingTrial_true (R : NPRelation enc) (a : α) :
    (ProbComp.eval (R.countingTrial a) true).toReal =
      searchCount R.IsWitness a / (2 : ℝ) ^ R.certLength.eval (enc a).length := by
  rw [countingTrial, ProbComp.eval_map, BitString.eval_sampleList, BitString.uniformList_map_apply,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    R.searchCount_eq]
  rfl

/-- [Goldreich2007Draft], Proposition 6.23: additive error `2 ^ r / k` with failure probability
strictly below `2⁻ᵗ`. Combined with `isPPTOn_additiveEstimate`, this includes the algorithm,
its strict time certificate and the rational-output cost, not only a concentration inequality. -/
theorem additiveEstimate_error (R : NPRelation enc) (a : α) {k : ℕ} (hk : 0 < k) (t : ℕ) :
    ((ProbComp.eval (R.additiveEstimate a k t)).toOuterMeasure {out |
      (2 : ℝ) ^ R.certLength.eval (enc a).length / k <
        |(out.1 : ℝ) / out.2 - searchCount R.IsWitness a|}).toReal < (1 / 2 : ℝ) ^ t := by
  let m := 2 * (t + 1) * k ^ 2
  let μ := (ProbComp.eval (R.countingTrial a) true).toReal
  let B : ℝ := 2 ^ R.certLength.eval (enc a).length
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : 0 < m := by dsimp [m]; positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hB : 0 < B := by dsimp [B]; positivity
  have hμ : μ * B = searchCount R.IsWitness a := by
    dsimp only [μ, B]
    rw [countingTrial_true, div_mul_cancel₀ _ (by positivity)]
  have hconc := Probability.PMF.pi_sum_abs_sub_mean_ge_card_mul
    (fun _ : Fin m => ProbComp.eval (R.countingTrial a))
    (fun _ bit => (bit.toNat : ℝ))
    (by intro i bit _; cases bit <;> norm_num) (γ := 1 / k) (by positivity)
  have hcount : ((ProbComp.eval (OracleComp.countTrue m (R.countingTrial a))).toOuterMeasure
      {s | (m : ℝ) / k ≤ |(s : ℝ) - m * μ|}).toReal ≤
      2 * Real.exp (-2 * m * (1 / (k : ℝ)) ^ 2) := by
    rw [ProbComp.eval_countTrue, PMF.toOuterMeasure_map_apply]
    simpa [μ, Set.preimage_ofPred_eq, Nat.cast_sum, Fintype.sum_bool, div_eq_mul_inv] using hconc
  have hsub : (fun s : ℕ => (s * 2 ^ R.certLength.eval (enc a).length, m)) ⁻¹'
      {out : ℕ × ℕ | B / k < |(out.1 : ℝ) / out.2 - searchCount R.IsWitness a|} ⊆
      {s | (m : ℝ) / k ≤ |(s : ℝ) - m * μ|} := by
    intro s hs
    change B / k < |((s * 2 ^ R.certLength.eval (enc a).length : ℕ) : ℝ) / m -
      searchCount R.IsWitness a| at hs
    have heq : ((s * 2 ^ R.certLength.eval (enc a).length : ℕ) : ℝ) / m -
        searchCount R.IsWitness a = ((s : ℝ) - m * μ) * B / m := by
      push_cast
      rw [← hμ]
      field_simp
      ring
    rw [heq, abs_div, abs_mul, abs_of_pos hB, abs_of_pos hmR,
      div_lt_div_iff₀ hkR hmR] at hs
    change (m : ℝ) / k ≤ |(s : ℝ) - m * μ|
    apply (div_le_iff₀ hkR).2
    nlinarith
  rw [additiveEstimate, ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
  apply (Probability.PMF.toOuterMeasure_toReal_mono _ hsub).trans_lt
  apply hcount.trans_lt
  have hexp : -2 * (m : ℝ) * (1 / (k : ℝ)) ^ 2 = -((t + 2 : ℕ) : ℝ) - (3 * t + 2) := by
    dsimp [m]
    push_cast
    field_simp
    ring
  have hbound : -2 * (m : ℝ) * (1 / (k : ℝ)) ^ 2 ≤ -((t + 2 : ℕ) : ℝ) := by
    rw [hexp]
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    linarith
  calc 2 * Real.exp (-2 * (m : ℝ) * (1 / (k : ℝ)) ^ 2)
      ≤ 2 * (1 / 2 : ℝ) ^ (t + 2) := by
        gcongr
        exact Real.exp_le_half_pow (t + 2) hbound
    _ = (1 / 2 : ℝ) ^ t / 2 := by rw [pow_add]; ring
    _ < (1 / 2 : ℝ) ^ t := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) t]

/-- The real-confidence form of Proposition 6.23: use logarithmic confidence
`⌈log₂ ⌈1 / δ⌉⌉`. The accuracy parameter remains unary; fixing it to a positive polynomial in
input length gives the source's `poly(|x|, log(1/δ))` bound by `isPPTOn_additiveEstimate`. -/
theorem additiveEstimate_error_confidence (R : NPRelation enc) (a : α) {k : ℕ} (hk : 0 < k)
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) :
    ((ProbComp.eval (R.additiveEstimate a k (Nat.clog 2 ⌈δ⁻¹⌉₊))).toOuterMeasure {out |
      (2 : ℝ) ^ R.certLength.eval (enc a).length / k <
        |(out.1 : ℝ) / out.2 - searchCount R.IsWitness a|}).toReal < δ := by
  have hpow := Int.zpow_log_le_self (b := 2) (by norm_num) hδ
  rw [Int.log_of_right_le_one 2 hδ₁.le, zpow_neg, zpow_natCast] at hpow
  exact (R.additiveEstimate_error a hk _).trans_le (by simpa [one_div, inv_pow] using hpow)

end Cslib.Complexity.NPRelation
