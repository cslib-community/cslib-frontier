/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Seeded
public import CslibFrontier.Foundations.Data.BitString.OddPairs
public import CslibFrontier.Foundations.Quantum.Algebra.Consistency
import CslibFrontier.Probability.PMF.Expect

/-!
# Agreement tests on decoded bits

A seeded agreement test compares one bit decoded from each player's answer. The seed determines
the questions and how to decode the answers. Failure bounds the average squared distance of the
two binary observables obtained from the players' measurements by those decoders. This formalizes
the round-by-round agreement estimate used in the proof of
[Natarajan and Vidick, §4.3.1, Lemma 17][NatarajanVidick2017] (arXiv:1610.03574v1, p. 21).
The generic bound takes the seed distribution and the decoders as parameters. Its first
application fixes one basis and the players' roles, samples an odd pair uniformly, and compares
the corresponding coordinate of the pair answer with the special-question answer. The passage
to the averaged observables of their equation (11) and the complete verifier are tracked in
cslib-community/cslib-frontier#6149.

## Main definitions

* `Cslib.PCP.SeededGame.bitAgreement`: a seeded game comparing decoded bits.
* `Cslib.PCP.PauliConsistencyQuestion`: the two strings and measurement basis.
* `Cslib.PCP.pauliSpecialQuestionTest`: the matched-basis special-question rounds on odd pairs.

## Main results

* `Cslib.PCP.SeededGame.sum_norm_sub_sq_le_of_bitAgreement`: a strategy's probability of
  disagreement bounds the average squared distance between its decoded observables.
* `Cslib.PCP.expect_norm_sub_sq_le_of_pauliSpecialQuestionTest`: the resulting conditional
  consistency bound on odd pairs.
-/

public section

namespace Cslib.PCP

open Finset Quantum
open scoped BigOperators

variable {R X Y A B 𝒜 : Type*}

namespace SeededGame

/-- Draw a private seed, send its two questions, and accept if the decoded bits agree. -/
@[expose] def bitAgreement (seed : PMF R) (query : R → X × Y)
    (decodeAlice : R → A → Bool) (decodeBob : R → B → Bool) : SeededGame R X Y A B where
  seed := seed
  query := query
  accepts r a b := decodeAlice r a = decodeBob r b

instance (seed : PMF R) (query : R → X × Y) (decodeAlice : R → A → Bool)
    (decodeBob : R → B → Bool) (r : R) (a : A) (b : B) :
    Decidable ((bitAgreement seed query decodeAlice decodeBob).accepts r a b) :=
  inferInstanceAs (Decidable (decodeAlice r a = decodeBob r b))

end SeededGame

variable [Fintype A] [Fintype B] [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [Algebra ℂ 𝒜]

private theorem CommutingStrategy.sum_ite_prob_eq_agreement (S : CommutingStrategy X Y A B 𝒜)
    (x : X) (y : Y) (f : A → Bool) (g : B → Bool) :
    (∑ a, ∑ b, if f a = g b then S.prob x y a b else 0) =
      Measurement.agreement S.state ((S.alice x).map f) ((S.bob y).map g) := by
  have hb (a : A) :
      (∑ b, if f a = g b then S.prob x y a b else 0) =
        (S.state ((S.alice x).effect a * ((S.bob y).map g).effect (f a))).re := by
    rw [Measurement.map_effect, mul_sum, map_sum, Complex.re_sum, sum_filter]
    refine sum_congr rfl fun b _ => ?_
    by_cases he : g b = f a
    · simp [he, CommutingStrategy.prob]
    · simp [he, Ne.symm he]
  rw [Measurement.agreement]
  simp only [hb]
  rw [← sum_fiberwise univ f]
  refine sum_congr rfl fun c _ => ?_
  simp only [Measurement.map_effect, sum_mul, map_sum, Complex.re_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [(mem_filter.mp ha).2]

namespace SeededGame

variable [Fintype R] [StarModule ℂ 𝒜] [SelfAdjointDecompose 𝒜] [TopologicalSpace 𝒜]
  [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]

/-- The seed-weighted squared distance of the decoded observables is at most four times the
probability that the verifier rejects. The estimate applies also to nonprojective measurements. -/
theorem sum_norm_sub_sq_le_of_bitAgreement (seed : PMF R) (query : R → X × Y)
    (decodeAlice : R → A → Bool) (decodeBob : R → B → Bool)
    (S : CommutingStrategy X Y A B 𝒜) :
    (∑ r, (seed r).toReal * S.state.norm
      (((S.alice (query r).1).map (decodeAlice r)).observable -
        ((S.bob (query r).2).map (decodeBob r)).observable) ^ 2) ≤
      4 * (1 - (bitAgreement seed query decodeAlice decodeBob).commutingWinProb S) := by
  have hwin : (bitAgreement seed query decodeAlice decodeBob).commutingWinProb S =
      ∑ r, (seed r).toReal * Measurement.agreement S.state
        ((S.alice (query r).1).map (decodeAlice r)) ((S.bob (query r).2).map (decodeBob r)) := by
    rw [commutingWinProb_eq_sum]
    refine sum_congr rfl fun r _ => ?_
    exact congrArg ((seed r).toReal * ·)
      (S.sum_ite_prob_eq_agreement (query r).1 (query r).2 (decodeAlice r) (decodeBob r))
  rw [hwin]
  have h r c : Commute (((S.alice (query r).1).map (decodeAlice r)).effect c)
      (((S.bob (query r).2).map (decodeBob r)).effect c) := by
    simp only [Measurement.map_effect]
    refine Commute.sum_left _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ => ?_
    exact S.commute _ _ a b
  have havg := Probability.PMF.sum_le_affine seed (a := 4) (b := -4) fun r => by
    have hdist := Measurement.norm_observable_sub_sq_le S.state
      ((S.alice (query r).1).map (decodeAlice r)) ((S.bob (query r).2).map (decodeBob r)) (h r)
    exact hdist.trans_eq (by ring)
  linarith

end SeededGame


/-- A question for the fixed-role special-question consistency test. -/
structure PauliConsistencyQuestion (ι : Type*) where
  /-- The bit string for the first coordinate, checked in the X basis. -/
  xString : ι → Bool
  /-- The bit string for the second coordinate, checked in the Z basis. -/
  zString : ι → Bool
  /-- The basis of the check: `false` for X and `true` for Z. -/
  basis : Bool

/-- The bit of the pair answer checked in the question's basis. -/
@[expose] def PauliConsistencyQuestion.checkedBit {ι : Type*}
    (q : PauliConsistencyQuestion ι) (bits : Bool × Bool) : Bool :=
  if q.basis then bits.2 else bits.1

section Pauli
open BitString

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A fixed-role special-question consistency round, with the odd pair sampled uniformly.
Both questions carry the same pair and basis. The pair player returns two bits and the
special-question player returns one. The verifier checks the first bit for the X basis
(`false`) and the second for the Z basis (`true`). -/
@[expose] noncomputable def pauliSpecialQuestionTest (basis : Bool) :
    SeededGame ↥(oddPairs ι) (PauliConsistencyQuestion ι) (PauliConsistencyQuestion ι)
      (Bool × Bool) Bool :=
  letI := oddPairs_nonempty (ι := ι)
  let question (p : ↥(oddPairs ι)) : PauliConsistencyQuestion ι :=
    ⟨p.val.fst, p.val.snd, basis⟩
  SeededGame.bitAgreement (Probability.PMF.uniformOfFintype _)
    (fun p => (question p, question p)) (fun p => (question p).checkedBit) (fun _ => id)

variable {ι} [StarModule ℂ 𝒜] [SelfAdjointDecompose 𝒜] [TopologicalSpace 𝒜]
  [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]

/-- In the matched-basis special-question rounds, the conditional average squared distance
between the checked pair marginal and the special-question observable is at most four times
the rejection probability. This is a step toward the special-question estimates in
[Natarajan and Vidick, §4.3.1, Lemma 17][NatarajanVidick2017]. It concerns the marginal at the
sampled pair; the source's observables also average over the other question coordinate. -/
theorem expect_norm_sub_sq_le_of_pauliSpecialQuestionTest
    (basis : Bool)
    (S : CommutingStrategy (PauliConsistencyQuestion ι) (PauliConsistencyQuestion ι)
      (Bool × Bool) Bool 𝒜) :
    (𝔼 p : ↥(oddPairs ι),
      let q : PauliConsistencyQuestion ι := ⟨p.val.fst, p.val.snd, basis⟩
      S.state.norm (((S.alice q).map q.checkedBit).observable - (S.bob q).observable) ^ 2) ≤
      4 * (1 - (pauliSpecialQuestionTest ι basis).commutingWinProb S) := by
  let := oddPairs_nonempty (ι := ι)
  let question (p : ↥(oddPairs ι)) : PauliConsistencyQuestion ι :=
    ⟨p.val.fst, p.val.snd, basis⟩
  have h := SeededGame.sum_norm_sub_sq_le_of_bitAgreement
    (Probability.PMF.uniformOfFintype ↥(oddPairs ι))
    (fun p => (question p, question p)) (fun p => (question p).checkedBit) (fun _ => id) S
  have hid (M : Measurement Bool 𝒜) : M.map id = M := by
    ext b
    simp only [Measurement.map_effect, sum_filter, id_eq, sum_ite_eq', mem_univ, ite_true]
  simpa only [pauliSpecialQuestionTest, question, hid, Probability.PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ← mul_sum, expect_eq_sum_div_card,
    card_univ, div_eq_inv_mul, Prod.fst, Prod.snd] using h

end Pauli

end Cslib.PCP
