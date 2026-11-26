/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingGame
public import CslibFrontier.Foundations.Quantum.Algebra.Expect
import CslibFrontier.Foundations.Quantum.Algebra.MeasurementAverage

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
* `Cslib.PCP.expect_norm_pauliBraidingBasisObservable_sub_sq_le_add_zero`: the uniform
  averaged-observable bound with an explicit zero-string term.
* `Cslib.PCP.weighted_expect_norm_pauliBraidingAverage_sub_special_sq_le`: the averaged
  basis-to-special distance on odd pairs, weighted by the matching question mass.
-/

public section

namespace Cslib.PCP

open BitString Finset Quantum
open scoped BigOperators

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
  dsimp only
  change (8 : ℝ)⁻¹ * (1 - ({ game with seed := law index }).answersWinProb answer) ≤
    1 - (pauliBraidingBranchGame n G special decode 2).answersWinProb answer at h
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
  rwa [hpull]

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

/-- The binary measurement of a checked string and dummy in the consistency verifier.
Malformed answers are decoded as `false`. -/
abbrev pauliBraidingBasisBitMeasurement
    (measure : PauliBraidingQuestion n Q → Measurement ((Bool × Bool) ⊕ A) 𝒜)
    (basis : Bool) (checked dummy : Fin n → Bool) : Measurement Bool 𝒜 :=
  let q := PauliConsistencyQuestion.ofChecked basis checked dummy
  (measure q.toBraidingQuestion).map (Sum.elim q.braidingCheckedBit fun _ => false)

/-- The consistency observable decoded from one checked string and one dummy. -/
@[expose] noncomputable def pauliBraidingBasisObservable
    (measure : PauliBraidingQuestion n Q → Measurement ((Bool × Bool) ⊕ A) 𝒜)
    (basis : Bool) (checked dummy : Fin n → Bool) : 𝒜 :=
  (pauliBraidingBasisBitMeasurement measure basis checked dummy).observable

omit [Nonempty (Fin n)] [StarModule ℂ 𝒜] [SelfAdjointDecompose 𝒜] in
/-- Averaging the binary consistency observable over the dummy gives a contraction. -/
theorem star_pauliBraidingBasisObservable_average_mul_self_le_one
    [Module ℚ≥0 𝒜] [PosSMulMono ℚ≥0 𝒜]
    (M : PauliBraidingQuestion n Q → Measurement ((Bool × Bool) ⊕ A) 𝒜)
    (b : Bool) (x : Fin n → Bool) :
    star (𝔼 d, pauliBraidingBasisObservable M b x d) *
      (𝔼 d, pauliBraidingBasisObservable M b x d) ≤ 1 := by
  simp only [pauliBraidingBasisObservable, ← Measurement.observable_average]
  exact (Measurement.average _).star_observable_mul_self_le_one

omit [Nonempty (Fin n)] in
private theorem oddExpect_expect_eq_dens_mul (f : (Fin n → Bool) → (Fin n → Bool) →
    (Fin n → Bool) → ℝ) :
    oddExpect (fun x y => 𝔼 z, f x y z) =
      ((oddPairs (Fin n)).dens : ℝ) * (𝔼 r : ↥(oddPairs (Fin n)) × (Fin n → Bool),
        f r.1.val.1 r.1.val.2 r.2) := by
  rw [oddExpect_eq_dens_mul_expect, Fintype.expect_prod_type]

omit [Nonempty (Fin n)] [Fintype A] [TopologicalSpace 𝒜]
  [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜] in
/-- On nonzero checked strings, both role assignments of the same-basis round control
the distance between the two observables averaged over unrestricted dummies. The right
side uses masked odd-pair averages. The left side is a uniform average with zero masked. -/
theorem expect_norm_averaged_sub_sq_nonzero_le [Module ℚ≥0 𝒜]
    (φ : AlgState 𝒜) (a b : (Fin n → Bool) → (Fin n → Bool) → 𝒜) :
    (𝔼 x, if x = 0 then 0 else
      φ.norm ((𝔼 y, a x y) - (𝔼 y, b x y)) ^ 2) ≤
      24 * oddExpect (fun x y => 𝔼 z, φ.norm (a x y - b x z) ^ 2) +
      4 * oddExpect (fun x y => 𝔼 z, φ.norm (a x z - b x y) ^ 2) := by
  classical
  rw [oddExpect_def, oddExpect_def, Finset.mul_expect, Finset.mul_expect,
    ← Finset.expect_add_distrib]
  refine expect_le_expect fun x _ => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  let partners := (univ : Finset (Fin n → Bool)).filter fun y => x ⬝ᵥ y = true
  have hmem (y : Fin n → Bool) : (x ⬝ᵥ y = true) ↔ y ∈ partners := by simp [partners]
  simp only [hx, ite_false, hmem]
  rw [Fintype.expect_ite_mem, Fintype.expect_ite_mem, NNRat.smul_def, NNRat.smul_def,
    dens_oddFiber hx]
  have h := φ.norm_expect_sub_expect_sq_le_of_half partners (oddFiber_nonempty hx)
    (le_of_eq (dens_oddFiber hx).symm) (a x) (b x)
  linarith

private theorem oddExpect_pauliBraidingRoundDistances_le
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    let a := pauliBraidingBasisObservable S.alice basis
    let b := pauliBraidingBasisObservable S.bob basis
    let bound := ((oddPairs (Fin n)).dens : ℝ) *
      (32 * (1 - (pauliBraidingBranchGame n G special decode 2).commutingWinProb S))
    oddExpect (fun x y => 𝔼 z, S.state.norm (a x y - b x z) ^ 2) ≤ bound ∧
      oddExpect (fun x y => 𝔼 z, S.state.norm (a x z - b x y) ^ 2) ≤ bound := by
  let a := pauliBraidingBasisObservable S.alice basis
  let b := pauliBraidingBasisObservable S.bob basis
  let δ := 1 - (pauliBraidingBranchGame n G special decode 2).commutingWinProb S
  let density := ((oddPairs (Fin n)).dens : ℝ)
  have hround (roles : Bool) :
      (𝔼 r : ↥(oddPairs (Fin n)) × (Fin n → Bool),
        let (x, y) := pauliBraidingSameBasisQuestions roles basis r.1 r.2
        S.state.norm
          (((S.alice x.toBraidingQuestion).map
              (Sum.elim x.braidingCheckedBit fun _ => false)).observable -
            ((S.bob y.toBraidingQuestion).map
              (Sum.elim y.braidingCheckedBit fun _ => false)).observable) ^ 2) ≤ 32 * δ := by
    have h := sum_norm_sub_sq_le_of_pauliBraidingSameBasisGame G special decode roles basis S
    let := oddPairs_nonempty (ι := Fin n)
    dsimp only [pauliBraidingSameBasisGame, SeededGame.pullbackSeed] at h
    simp only [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ← mul_sum] at h
    simpa only [← div_eq_inv_mul, Fintype.expect_eq_sum_div_card] using h
  dsimp only
  cases basis
  · exact ⟨(oddExpect_expect_eq_dens_mul _).trans_le
      (mul_le_mul_of_nonneg_left (hround false) (by positivity)),
      (oddExpect_expect_eq_dens_mul _).trans_le
        (mul_le_mul_of_nonneg_left (hround true) (by positivity))⟩
  · exact ⟨((oddExpect_swap _).symm.trans (oddExpect_expect_eq_dens_mul _)).trans_le
      (mul_le_mul_of_nonneg_left (hround false) (by positivity)),
      ((oddExpect_swap _).symm.trans (oddExpect_expect_eq_dens_mul _)).trans_le
        (mul_le_mul_of_nonneg_left (hround true) (by positivity))⟩

/-- The combined verifier's consistency rejection controls the uniform average of the
squared distance of the two averaged basis observables over the nonzero strings. The
omitted zero term has weight `1 / 2^n` in the full uniform average. -/
theorem expect_norm_pauliBraidingBasisObservable_sub_sq_nonzero_le [Module ℚ≥0 𝒜]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    let a := pauliBraidingBasisObservable S.alice basis
    let b := pauliBraidingBasisObservable S.bob basis
    (𝔼 x, if x = 0 then 0 else S.state.norm ((𝔼 y, a x y) - (𝔼 y, b x y)) ^ 2) ≤
      896 * ((oddPairs (Fin n)).dens : ℝ) *
        (1 - (pauliBraidingBranchGame n G special decode 2).commutingWinProb S) := by
  let a := pauliBraidingBasisObservable S.alice basis
  let b := pauliBraidingBasisObservable S.bob basis
  obtain ⟨hforward, hreverse⟩ := oddExpect_pauliBraidingRoundDistances_le G special decode basis S
  refine (expect_norm_averaged_sub_sq_nonzero_le S.state a b).trans ?_
  linarith only [hforward, hreverse]

/-- In the checked-string coordinate order, the same-basis estimates bound how much
the first logical player's decoded observable changes as its dummy varies, on odd pairs. -/
theorem oddExpect_norm_pauliBraidingBasisObservable_sub_average_sq_le [Module ℚ≥0 𝒜]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    let measure := cond roles S.bob S.alice
    let a := pauliBraidingBasisObservable measure basis
    oddExpect (fun x y => S.state.norm (a x y - (𝔼 z, a x z)) ^ 2) ≤
      960 * ((oddPairs (Fin n)).dens : ℝ) *
        (1 - (pauliBraidingBranchGame n G special decode 2).commutingWinProb S) := by
  intro measure a
  let b := pauliBraidingBasisObservable (cond roles S.alice S.bob) basis
  let δ := 1 - (pauliBraidingBranchGame n G special decode 2).commutingWinProb S
  let density := ((oddPairs (Fin n)).dens : ℝ)
  have hround : oddExpect (fun x y => 𝔼 z, S.state.norm (a x y - b x z) ^ 2) ≤
      density * (32 * δ) := by
    obtain ⟨hforward, hreverse⟩ :=
      oddExpect_pauliBraidingRoundDistances_le G special decode basis S
    cases roles
    · exact hforward
    · simp_rw [S.state.norm_sub_comm (a _ _)]
      exact hreverse
  have hcross : oddExpect (fun x _ => S.state.norm ((𝔼 z, b x z) - (𝔼 z, a x z)) ^ 2)
      ≤ 448 * density * δ := by
    rw [oddExpect_fst]
    have h := expect_norm_pauliBraidingBasisObservable_sub_sq_nonzero_le G special decode basis S
    dsimp only at h
    cases roles <;> dsimp only [a, b, measure, cond]
    · simp_rw [S.state.norm_sub_comm (𝔼 z, pauliBraidingBasisObservable S.bob basis _ z)]
      linarith only [h]
    · linarith only [h]
  have hjensen : oddExpect (fun x y => S.state.norm (a x y - (𝔼 z, b x z)) ^ 2) ≤
      density * (32 * δ) :=
    (oddExpect_mono fun x y _ =>
      S.state.norm_sub_expect_sq_le univ univ_nonempty (a x y) (b x)).trans hround
  have htri := oddExpect_mono (fun x y (_ : x ⬝ᵥ y = true) =>
    S.state.norm_sub_sq_le_through (a x y) (𝔼 z, b x z) (𝔼 z, a x z))
  rw [oddExpect_add, oddExpect_const_mul, oddExpect_const_mul] at htri
  change _ ≤ 960 * density * δ
  linarith only [htri, hjensen, hcross]

/-- The opposite player's decoded observable on the matched special question. -/
@[expose] noncomputable def pauliBraidingSpecialObservable
    (measure : PauliBraidingQuestion n Q → Measurement ((Bool × Bool) ⊕ A) 𝒜)
    (question : Q) (decode : A → Bool) (p : ↥(oddPairs (Fin n))) : 𝒜 :=
  ((measure (.anticommutation true question p)).map
    (Sum.elim (fun _ : Bool × Bool => false) decode)).observable

/-- The averaged basis observable of the first logical player is close to the other
player's matched special observable on odd pairs. The estimate carries the marginal
question mass, so it applies even when that mass is zero. -/
theorem weighted_expect_norm_pauliBraidingAverage_sub_special_sq_le [Module ℚ≥0 𝒜] [Finite Q]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    let a := pauliBraidingBasisObservable (cond roles S.bob S.alice) basis
    let b := pauliBraidingSpecialObservable (cond roles S.alice S.bob)
      (special basis) (decode basis)
    let mass := ((G.questions.map Prod.snd) (special basis)).toReal
    let density := ((oddPairs (Fin n)).dens : ℝ)
    let δ := 1 - (pauliBraidingBranchGame n G special decode 2).commutingWinProb S
    (mass * density) * (𝔼 p : ↥(oddPairs (Fin n)),
      let checked := if basis then p.val.2 else p.val.1
      S.state.norm ((𝔼 z, a checked z) - b p) ^ 2) ≤ (1920 * mass + 64) * density * δ := by
  intro a b mass density δ
  let checked (p : ↥(oddPairs (Fin n))) := if basis then p.val.2 else p.val.1
  let dummy (p : ↥(oddPairs (Fin n))) := if basis then p.val.1 else p.val.2
  let point (p : ↥(oddPairs (Fin n))) := a (checked p) (dummy p)
  let avg (p : ↥(oddPairs (Fin n))) := 𝔼 z, a (checked p) z
  have hvar : density * (𝔼 p, S.state.norm (point p - avg p) ^ 2) ≤ 960 * density * δ := by
    have h := oddExpect_norm_pauliBraidingBasisObservable_sub_average_sq_le
      G special decode roles basis S
    let f (x y : Fin n → Bool) := S.state.norm (a x y - (𝔼 z, a x z)) ^ 2
    change oddExpect f ≤ _ at h
    cases basis
    · rwa [oddExpect_eq_dens_mul_expect] at h
    · rwa [← oddExpect_swap, oddExpect_eq_dens_mul_expect] at h
  have hlocal : mass * (𝔼 p, S.state.norm (point p - b p) ^ 2) ≤ 32 * δ := by
    have h := weighted_sum_norm_sub_sq_le_of_pauliBraidingMatchedGame
      G special decode roles basis S
    let := oddPairs_nonempty (ι := Fin n)
    dsimp only [pauliBraidingMatchedGame, SeededGame.pullbackSeed] at h
    simp only [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ← mul_sum] at h
    rw [Fintype.expect_eq_sum_div_card, div_eq_inv_mul]
    refine le_trans ?_ h
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
      ENNReal.toReal_nonneg
    refine sum_le_sum fun p _ => ?_
    cases roles
    · cases basis <;> exact le_rfl
    · cases basis <;> exact (congrArg (· ^ 2) (S.state.norm_sub_comm (point p) (b p))).le
  have htri : (𝔼 p, S.state.norm (avg p - b p) ^ 2) ≤
      2 * (𝔼 p, S.state.norm (point p - avg p) ^ 2) +
      2 * (𝔼 p, S.state.norm (point p - b p) ^ 2) := by
    rw [Finset.mul_expect, Finset.mul_expect, ← expect_add_distrib]
    refine expect_le_expect fun p _ => ?_
    rw [← S.state.norm_sub_comm (avg p) (point p)]
    exact S.state.norm_sub_sq_le_through (avg p) (point p) (b p)
  have hmass : 0 ≤ mass := ENNReal.toReal_nonneg
  have hdensity : 0 ≤ density := NNRat.cast_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left htri (mul_nonneg hmass hdensity)
  change (mass * density) * (𝔼 p, S.state.norm (avg p - b p) ^ 2) ≤ _
  linarith only [hscaled, mul_le_mul_of_nonneg_left hvar hmass,
    mul_le_mul_of_nonneg_left hlocal hdensity]

/-- In the full uniform average, the distance at zero is the only additional term.
The odd-pair consistency branch controls the remaining contribution. -/
theorem expect_norm_pauliBraidingBasisObservable_sub_sq_le_add_zero [Module ℚ≥0 𝒜]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    let a := pauliBraidingBasisObservable S.alice basis
    let b := pauliBraidingBasisObservable S.bob basis
    let d (x : Fin n → Bool) := S.state.norm ((𝔼 y, a x y) - (𝔼 y, b x y)) ^ 2
    (𝔼 x, d x) ≤ 896 * ((oddPairs (Fin n)).dens : ℝ) *
      (1 - (pauliBraidingBranchGame n G special decode 2).commutingWinProb S) +
      d 0 / Fintype.card (Fin n → Bool) := by
  intro a b d
  rw [expect_eq_two_mul_oddExpect_fst_add_zero, oddExpect_fst, ← mul_assoc]
  norm_num
  exact expect_norm_pauliBraidingBasisObservable_sub_sq_nonzero_le G special decode basis S

end Cslib.PCP
