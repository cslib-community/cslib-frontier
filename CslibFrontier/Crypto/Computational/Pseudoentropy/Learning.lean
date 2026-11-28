/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Pseudoentropy.Masking
public import CslibFrontier.Crypto.Computational.Pseudoentropy.Boosting.Learner
import CslibFrontier.Languages.Probabilistic.Notation

/-!
# From sequence distinguishers to validation bias

Saved coordinate predictors turn a sequence distinguishing gap into the average bias of a
weighted validation trial. All target predictions receive only the public observation.

The replay law is an explicit hypothesis. `SequenceLearner` constructs saved descriptions, obtains
replay from a certified sequence test, and learns a predictor from this bias
(`SequenceLearner.learn_goodPredictor_error`). Choosing uniform asymptotic parameters remains a
separate step in the final cryptographic reduction.

## Main results

* `maskedSequence_validation_gap`: exact transfer from a sequence gap to weighted validation bias.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Games 3--5 and the following prediction reduction.
  [Holenstein2006].
  This uses the fresh-mask adaptation.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

public section

namespace Cslib.Crypto.Pseudoentropy

open Probability Probability.PMF BitString Boosting

variable {α β : Type}

/-- The complete sequence gap is the dyadic coordinate count times the average weighted
validation bias of saved descriptions. The replay law is needed only at actual observations. -/
theorem maskedSequence_validation_gap [Finite α]
    (source : ProbComp α) (observe : α → β) (truth : α → Bool)
    (mask : α → ProbComp Bool) (count : ℕ) (test : List (β × Bool) → ProbComp Bool)
    (candidates : ProbComp (List Bool)) (predict : List Bool → β → Bool)
    (hrealize : ∀ value ∈ (ProbComp.eval source).support,
      ProbComp.eval ((fun code => predict code (observe value)) <$> candidates) =
        ProbComp.eval
          (maskedSequencePredictor source observe truth mask count test (observe value))) :
    Pr[OracleComp.replicate count ((fun value => (observe value, truth value)) <$>
      source) >>= test] -
        Pr[OracleComp.replicate count (maskedSample source observe truth mask) >>= test] =
      (dyadicSize count : ℝ) * (Pr[candidates >>= fun code =>
        weightedTrial source mask
          (fun value => pure (predict code (observe value) == truth value))] - 1 / 2) := by
  let := Fintype.ofFinite α
  rw [maskedSequence_prediction_gap,
    congrArg (fun law : PMF Bool => (law true).toReal)
      (eval_weightedTrial_bind candidates source mask _),
    weightedTrial_probability, add_sub_cancel_left]
  refine congrArg (_ * ·) (Finset.sum_congr rfl fun value _ => ?_)
  by_cases hsupport : value ∈ (ProbComp.eval source).support
  · have hpoint :
        Pr[candidates >>= fun code => pure (predict code (observe value) == truth value)] =
          Pr[(fun guess => guess == truth value) <$>
            maskedSequencePredictor source observe truth mask count test (observe value)] :=
      congrArg (fun law : PMF Bool => (law true).toReal) (by
        simpa only [bind_pure_comp, ProbComp.eval_map, PMF.map_comp, Function.comp_def] using
          congrArg (PMF.map (· == truth value)) (hrealize value hsupport))
    rw [hpoint, mul_assoc]
  · simp only [PMF.mem_support_iff, not_not] at hsupport
    simp [hsupport]

end Cslib.Crypto.Pseudoentropy
