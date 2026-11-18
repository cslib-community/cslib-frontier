/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingGame

/-!
# Consistency rounds of the Pauli braiding verifier

The same-basis round of the combined verifier samples an odd pair and a uniform independent
dummy. With the roles and basis fixed, its rejection bounds the squared distance between
the observables read from the answers at the sampled questions. Both observables refer to
the same checked string. A second bound compares the basis marginal and the special-question
observable, conditional on the matched question. These are steps toward the averaged
consistency bound of
[Natarajan and Vidick, Lemma 17][NatarajanVidick2017] (arXiv:1610.03574v1, p. 21).

## Main definitions

* `Cslib.PCP.pauliBraidingSameBasisGame`: the same-basis round with fixed roles and basis.

* `Cslib.PCP.pauliBraidingMatchedGame`: the special-question round at the matched question.

## Main results

* `Cslib.PCP.sum_norm_sub_sq_le_of_pauliBraidingSameBasisGame`: the same-basis distance bound.
* `Cslib.PCP.weighted_sum_norm_sub_sq_le_of_pauliBraidingMatchedGame`: the matched distance bound.
-/

public section

namespace Cslib.PCP

open BitString Quantum

variable {n : ℕ} [Nonempty (Fin n)] {Q A 𝒜 : Type*}

/-- The same-basis consistency subtest conditioned on a role assignment and basis. Its
seed retains the odd pair and independent dummy as separate choices. -/
@[expose] noncomputable def pauliBraidingSameBasisGame (n : ℕ) [Nonempty (Fin n)]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (swapRoles basis : Bool) :
    SeededGame (↥(oddPairs (Fin n)) × (Fin n → Bool))
      (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) :=
  letI := oddPairs_nonempty (ι := Fin n)
  (pauliBraidingGame n G special decode).pullbackSeed (Probability.PMF.uniformOfFintype _)
    fun (p, dummy) => .sameBasis swapRoles basis p dummy

/-- Condition the special-question round on the matching question of the chosen basis,
with the basis and role assignment fixed. The odd pair remains uniform. -/
@[expose] noncomputable def pauliBraidingMatchedGame (n : ℕ) [Nonempty (Fin n)]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (swapRoles basis : Bool) :
    SeededGame ↥(oddPairs (Fin n)) (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) :=
  letI := oddPairs_nonempty (ι := Fin n)
  (pauliBraidingGame n G special decode).pullbackSeed (Probability.PMF.uniformOfFintype _)
    fun p => .special swapRoles basis p (special basis)

/-- Decoders for the matched round in physical player order. Malformed answers
have a default decoded bit of `false`. -/
@[expose] def pauliBraidingMatchedDecoders (decode : Bool → A → Bool) (swapRoles basis : Bool)
    (p : ↥(oddPairs (Fin n))) :
    (((Bool × Bool) ⊕ A) → Bool) × (((Bool × Bool) ⊕ A) → Bool) :=
  let q : PauliConsistencyQuestion (Fin n) := ⟨p.val.1, p.val.2, basis⟩
  let readPair := Sum.elim q.braidingCheckedBit (fun _ : A => false)
  let readSpecial := Sum.elim (fun _ : Bool × Bool => false) (decode basis)
  cond swapRoles Prod.swap id (readPair, readSpecial)

private theorem rejection_consistencyLaw_le
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (swapRoles basis specialRound : Bool)
    (answer : PauliBraidingQuestion n Q → PauliBraidingQuestion n Q →
      PMF (((Bool × Bool) ⊕ A) × ((Bool × Bool) ⊕ A))) :
    let game := pauliBraidingGame n G special decode
    let conditional := pauliBraidingConsistencyLaw n G.questions swapRoles basis specialRound
    1 - ({ game with seed := conditional }).answersWinProb answer ≤
      8 * (1 - (pauliBraidingBranchGame n G special decode 2).answersWinProb answer) := by
  let game := pauliBraidingGame n G special decode
  let law (s : Bool × Bool × Bool) := pauliBraidingConsistencyLaw n G.questions s.1 s.2.1 s.2.2
  let index := (swapRoles, basis, specialRound)
  have h := game.weighted_rejection_le_of_bind_seed (Probability.PMF.uniformOfFintype _)
    law answer index
  have hmass : ((Probability.PMF.uniformOfFintype (Bool × Bool × Bool)) index).toReal =
      (8 : ℝ)⁻¹ := by
    rw [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv]
    norm_num [Fintype.card_prod]
  rw [hmass] at h
  let score := ({ game with seed := law index }).answersWinProb answer
  let total := (pauliBraidingBranchGame n G special decode 2).answersWinProb answer
  change (8 : ℝ)⁻¹ * (1 - score) ≤ 1 - total at h
  change 1 - score ≤ 8 * (1 - total)
  linarith

/-- The same-basis conditional rejection probability for either role assignment and
either basis costs at most eight times the consistency-branch rejection probability. -/
theorem rejection_pauliBraidingSameBasisGame_le
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (swapRoles basis : Bool)
    (answer : PauliBraidingQuestion n Q → PauliBraidingQuestion n Q →
      PMF (((Bool × Bool) ⊕ A) × ((Bool × Bool) ⊕ A))) :
    1 - (pauliBraidingSameBasisGame n G special decode swapRoles basis).answersWinProb answer ≤
      8 * (1 - (pauliBraidingBranchGame n G special decode 2).answersWinProb answer) := by
  let := oddPairs_nonempty (ι := Fin n)
  let game := pauliBraidingGame n G special decode
  have h := rejection_consistencyLaw_le G special decode swapRoles basis false answer
  have hpull := game.answersWinProb_pullbackSeed (Probability.PMF.uniformOfFintype
    (↥(oddPairs (Fin n)) × (Fin n → Bool))) (fun (p, dummy) =>
      PauliBraidingSeed.sameBasis swapRoles basis p dummy) answer
  change 1 - (game.pullbackSeed _ _).answersWinProb answer ≤ _
  rw [hpull]
  exact h

/-- The matched-question rejection probability, weighted by its probability in the
second-question marginal, costs at most eight times the consistency-branch rejection. -/
theorem weighted_rejection_pauliBraidingMatchedGame_le [Finite Q]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (swapRoles basis : Bool)
    (answer : PauliBraidingQuestion n Q → PauliBraidingQuestion n Q →
      PMF (((Bool × Bool) ⊕ A) × ((Bool × Bool) ⊕ A))) :
    ((G.questions.map Prod.snd) (special basis)).toReal *
        (1 - (pauliBraidingMatchedGame n G special decode swapRoles basis).answersWinProb answer) ≤
      8 * (1 - (pauliBraidingBranchGame n G special decode 2).answersWinProb answer) := by
  let := oddPairs_nonempty (ι := Fin n)
  let game := pauliBraidingGame n G special decode
  let odd := Probability.PMF.uniformOfFintype ↥(oddPairs (Fin n))
  let seed (y : Q) (p : ↥(oddPairs (Fin n))) := PauliBraidingSeed.special swapRoles basis p y
  have hpull := game.answersWinProb_pullbackSeed odd (seed (special basis)) answer
  change ((G.questions.map Prod.snd) (special basis)).toReal *
    (1 - (game.pullbackSeed odd (seed (special basis))).answersWinProb answer) ≤ _
  rw [hpull]
  exact (game.weighted_rejection_le_of_bind_seed (G.questions.map Prod.snd)
    (fun y => odd.map (seed y)) answer (special basis)).trans
    (rejection_consistencyLaw_le G special decode swapRoles basis true answer)

variable [Fintype A] [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [SelfAdjointDecompose 𝒜] [TopologicalSpace 𝒜]
  [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]

/-- Rejection in the consistency branch bounds the mean squared distance of the
two same-basis observables that decode the shared string. In the decoded measurements a malformed
answer is read as `false`. The verifier itself rejects such an answer. -/
theorem sum_norm_sub_sq_le_of_pauliBraidingSameBasisGame
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (swapRoles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    let test := pauliBraidingSameBasisGame n G special decode swapRoles basis
    (∑ r, (test.seed r).toReal *
      let (x, y) := pauliBraidingSameBasisQuestions swapRoles basis r.1 r.2
      S.state.norm
        (((S.alice x.toBraidingQuestion).map
            (Sum.elim x.braidingCheckedBit fun _ => false)).observable -
          ((S.bob y.toBraidingQuestion).map
            (Sum.elim y.braidingCheckedBit fun _ => false)).observable) ^ 2) ≤
      32 * (1 - (pauliBraidingBranchGame n G special decode 2).commutingWinProb S) := by
  let test := pauliBraidingSameBasisGame n G special decode swapRoles basis
  let read (q : PauliConsistencyQuestion (Fin n)) : (Bool × Bool) ⊕ A → Bool :=
    Sum.elim q.braidingCheckedBit fun _ => false
  let questions (r : ↥(oddPairs (Fin n)) × (Fin n → Bool)) :=
    pauliBraidingSameBasisQuestions swapRoles basis r.1 r.2
  have haccept (r : ↥(oddPairs (Fin n)) × (Fin n → Bool)) (a b : (Bool × Bool) ⊕ A)
      (h : test.accepts r a b) : read (questions r).1 a = read (questions r).2 b := by
    obtain ⟨_, _⟩ := r
    cases a <;> cases b <;> first | exact h | exact False.elim h
  refine (test.sum_norm_sub_sq_le_of_accepts_imp_eq
    (fun r => read (questions r).1) (fun r => read (questions r).2) haccept S).trans ?_
  have h := rejection_pauliBraidingSameBasisGame_le G special decode swapRoles basis S.answers
  change 4 * (1 - test.answersWinProb S.answers) ≤ _
  unfold SeededGame.commutingWinProb
  linarith

/-- Rejection in the consistency branch bounds the mean squared distance between the decoded
basis marginal and special observable, weighted by the probability of the matching question. -/
theorem weighted_sum_norm_sub_sq_le_of_pauliBraidingMatchedGame [Finite Q]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (swapRoles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    let test := pauliBraidingMatchedGame n G special decode swapRoles basis
    ((G.questions.map Prod.snd) (special basis)).toReal *
      (∑ p, (test.seed p).toReal *
        let q := test.query p
        let read := pauliBraidingMatchedDecoders decode swapRoles basis p
        S.state.norm (((S.alice q.1).map read.1).observable -
          ((S.bob q.2).map read.2).observable) ^ 2) ≤
      32 * (1 - (pauliBraidingBranchGame n G special decode 2).commutingWinProb S) := by
  let test := pauliBraidingMatchedGame n G special decode swapRoles basis
  let read := pauliBraidingMatchedDecoders (n := n) decode swapRoles basis
  have haccept (p : ↥(oddPairs (Fin n))) (a b : (Bool × Bool) ⊕ A) (h : test.accepts p a b) :
      (read p).1 a = (read p).2 b := by
    cases swapRoles <;> cases a <;> cases b <;>
      first | exact False.elim h | exact h rfl | exact (h rfl).symm
  refine (mul_le_mul_of_nonneg_left
    (test.sum_norm_sub_sq_le_of_accepts_imp_eq
      (fun p => (read p).1) (fun p => (read p).2) haccept S) ENNReal.toReal_nonneg).trans ?_
  have h := weighted_rejection_pauliBraidingMatchedGame_le G special decode swapRoles basis
    S.answers
  change ((G.questions.map Prod.snd) (special basis)).toReal *
    (4 * (1 - test.answersWinProb S.answers)) ≤ _
  unfold SeededGame.commutingWinProb
  linarith only [h]

end Cslib.PCP
