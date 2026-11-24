/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.TwoStage
public import CslibFrontier.Probability.HashFamily
import CslibFrontier.Languages.Probabilistic.Semantics
import CslibFrontier.Probability.HashFamily.UniformOffset
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.UniformPoint

/-!
# Pairwise unpredictability

[BonehShoup2023], Section 7.6.1, printed p. 275, defines pairwise unpredictability for a single
keyed hash with a private uniform key. After seeing the digest of its first message, the
adversary chooses another message and tries to predict its digest.

## Main definitions

* `Cslib.Crypto.UHF.predictionExperiment`: Attack Game 7.5 for a finite uniform key.
* `Cslib.Crypto.UHF.IsPairwiseUnpredictable`: Definition 7.7, the bound against all two-stage
  adversaries.

## Main results

* `Cslib.Crypto.UHF.IsPairwiseUnpredictable.isUniversalHash` and
  `Cslib.Crypto.UHF.IsPairwiseUnpredictable.isDeltaUniversalHash`: the bound also holds
  for collisions and for predicted hash differences.
* `Cslib.Crypto.UHF.isPairwiseUnpredictable_add_uniform`: adding an independent uniform
  digest to a difference-universal family gives pairwise unpredictability (Lemma 7.11).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Sections 7.6.1–7.6.2.
-/

public section

namespace Cslib.Crypto.UHF

open Cslib.Probability
open scoped ENNReal

variable {K M Y σ : Type}

/-- The second message and its predicted hash. -/
structure PredictionGuess (M Y : Type) where
  /-- The message whose hash the adversary predicts. -/
  message : M
  /-- The predicted hash. -/
  digest : Y

/-- The adversary chooses a message, saves private state, then receives only its hash. -/
abbrev PredictionAdversary (M Y σ : Type) := TwoStage Unit M Y (PredictionGuess M Y) σ

/-- Attack Game 7.5 ([BonehShoup2023], v0.6, printed p. 275). The challenger samples a private
uniform key and answers the first query. The experiment rejects a prediction for the first
message, which the source forbids submitting. -/
@[expose] noncomputable def predictionExperiment [Fintype K] [Nonempty K]
    [DecidableEq M] [DecidableEq Y] (H : K → M → Y) (A : PredictionAdversary M Y σ) :
    Experiment := do
  let k ← ProbComp.uniform K
  let (m, state) ← A.choose ()
  let guess ← A.guess state (H k m)
  return decide (guess.message ≠ m ∧ H k guess.message = guess.digest)

/-- Statistical pairwise unpredictability ([BonehShoup2023], Definition 7.7, v0.6, p. 275).
All probabilistic two-stage adversaries, with arbitrary saved state, succeed with probability
at most `ε`. -/
@[expose] def IsPairwiseUnpredictable [Fintype K] [Nonempty K] [DecidableEq M] [DecidableEq Y]
    (H : K → M → Y) (ε : ℝ≥0∞) : Prop :=
  ∀ (σ : Type) (A : PredictionAdversary M Y σ), ProbComp.eval (predictionExperiment H A) true ≤ ε

variable [Fintype K] [Nonempty K] [DecidableEq M] [DecidableEq Y] {H : K → M → Y} {ε : ℝ≥0∞}

private theorem prediction_le (h : IsPairwiseUnpredictable H ε) {m m' : M} (hne : m ≠ m')
    (predict : Y → Y) :
    (PMF.uniformOfFintype K).toOuterMeasure {k | H k m = predict (H k m')} ≤ ε := by
  let A : PredictionAdversary M Y Unit :=
    ⟨fun _ => pure (m', ()), fun _ t => pure ⟨m, predict t⟩⟩
  simpa only [A, predictionExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.pure_bind, ne_eq, hne, not_false_eq_true, true_and,
    Probability.PMF.bind_pure_decide_apply_true] using h Unit A

/-- An `ε`-PUF is an `ε`-UHF ([BonehShoup2023], v0.6, p. 275). Use the revealed digest as the
prediction for the other message. -/
theorem IsPairwiseUnpredictable.isUniversalHash (h : IsPairwiseUnpredictable H ε) :
    IsUniversalHash (PMF.uniformOfFintype K) H ε :=
  fun _ _ hne => prediction_le h hne id

/-- An `ε`-PUF with group-valued digests is an `ε`-DUF ([BonehShoup2023], v0.6, p. 275).
To test a proposed difference, add it on the left of the revealed digest. The proof works for
any additive group, including the source's cyclic and abelian cases. -/
theorem IsPairwiseUnpredictable.isDeltaUniversalHash [AddGroup Y]
    (h : IsPairwiseUnpredictable H ε) :
    IsDeltaUniversalHash (PMF.uniformOfFintype K) H ε := by
  intro m m' hne d
  simpa only [sub_eq_iff_eq_add] using prediction_le h hne (d + ·)

/-- **Lemma 7.11** ([BonehShoup2023], v0.6, Section 7.6.2, printed p. 276). Add an
independent uniform digest to every hash evaluation. If the original family is
`ε`-difference universal, the resulting family is `ε`-pairwise unpredictable. The challenger
uses a uniform key in the product of the original key and digest spaces. The argument works
for finite additive groups, including the source's cyclic groups. -/
theorem isPairwiseUnpredictable_add_uniform [AddGroup Y] [Fintype Y]
    (h : IsDeltaUniversalHash (PMF.uniformOfFintype K) H ε) :
    IsPairwiseUnpredictable (fun (key : K × Y) m => H key.1 m + key.2) ε := by
  intro σ A
  simp only [predictionExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rw [PMF.bind_comm]
  refine Probability.PMF.bind_apply_le_on_support _ fun ⟨m, state⟩ _ => ?_
  rw [← Probability.PMF.uniformOfFintype_prod K Y]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, Bool.decide_and]
  exact h.bind_uniform_offset_le m (fun t => ProbComp.eval (A.guess state t))
    PredictionGuess.message PredictionGuess.digest

end Cslib.Crypto.UHF
