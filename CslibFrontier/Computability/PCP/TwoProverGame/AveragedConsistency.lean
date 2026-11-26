/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.ConsistencyTest
public import CslibFrontier.Foundations.Quantum.Algebra.Expect
import CslibFrontier.Probability.PMF

/-!
# Same-basis agreement and averaged observables

In the fixed-basis game, the verifier draws a checked string uniformly and gives each player an
independent uniform dummy string. It compares the bits associated with the checked string.
This sampling gives a direct bound on the squared distance between the two players' marginals
averaged over their dummy questions. It is a step toward the consistency analysis of
[Natarajan and Vidick, §4.3.1, Lemma 17][NatarajanVidick2017] (arXiv:1610.03574v1, p. 21).
Figure 2 samples an odd pair first and randomizes the roles. Here both roles are fixed, and all
checked strings and dummy strings are sampled independently, without sorting.

## Main definitions

* `Cslib.PCP.pauliSameBasisTest`: the game with a shared checked string and independent dummies.
* `Cslib.PCP.PauliConsistencyQuestion.averagedObservable`: the uniform mean of the decoded
  observable with the checked string fixed.

## Main results

* `Cslib.PCP.expect_norm_sub_sq_le_of_pauliSameBasisTest`: rejection bounds the squared distance
  between the two averaged observables.
* `Cslib.PCP.oddExpect_norm_sub_sq_le_of_pauliConsistency`: on odd pairs, the same-basis
  and special-question deficits control the distance to Alice's averaged observable.
-/

public section

namespace Cslib.PCP

open Finset Quantum
open scoped BigOperators

variable {ι 𝒜 : Type*} [Fintype ι] [DecidableEq ι]

/-- Ask both players for the bit associated with a shared uniform string, each with an independent
uniform dummy string. The verifier reads only the answer coordinate for the chosen basis. -/
@[expose] noncomputable def pauliSameBasisTest (ι : Type*) [Fintype ι] [DecidableEq ι]
    (basis : Bool) :
    SeededGame ((ι → Bool) × (ι → Bool) × (ι → Bool))
      (PauliConsistencyQuestion ι) (PauliConsistencyQuestion ι) (Bool × Bool) (Bool × Bool) :=
  let alice : (ι → Bool) × (ι → Bool) × (ι → Bool) → PauliConsistencyQuestion ι :=
    fun (a, b, _) => PauliConsistencyQuestion.ofChecked basis a b
  let bob : (ι → Bool) × (ι → Bool) × (ι → Bool) → PauliConsistencyQuestion ι :=
    fun (a, _, c) => PauliConsistencyQuestion.ofChecked basis a c
  SeededGame.bitAgreement (Probability.PMF.uniformOfFintype _)
    (fun r => (alice r, bob r)) (fun r => (alice r).checkedBit) (fun r => (bob r).checkedBit)

variable [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜]
  [StarModule ℂ 𝒜] [SelfAdjointDecompose 𝒜] [TopologicalSpace 𝒜]
  [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]
  [Module ℚ≥0 𝒜]

/-- The decoded observable averaged over the dummy string at a fixed basis and checked string. -/
@[expose] noncomputable def PauliConsistencyQuestion.averagedObservable
    (measure : PauliConsistencyQuestion ι → Measurement (Bool × Bool) 𝒜)
    (basis : Bool) (checked : ι → Bool) : 𝒜 :=
  𝔼 dummy,
    let q := ofChecked basis checked dummy
    ((measure q).map q.checkedBit).observable

variable (basis : Bool)
  (S : CommutingStrategy (PauliConsistencyQuestion ι) (PauliConsistencyQuestion ι)
    (Bool × Bool) (Bool × Bool) 𝒜)

omit [Module ℚ≥0 𝒜] in
private theorem expect_roundDistance_le :
    (𝔼 a : ι → Bool, 𝔼 b : ι → Bool, 𝔼 c : ι → Bool,
      let q := PauliConsistencyQuestion.ofChecked basis a b
      let r := PauliConsistencyQuestion.ofChecked basis a c
      S.state.norm (((S.alice q).map q.checkedBit).observable -
        ((S.bob r).map r.checkedBit).observable) ^ 2) ≤
      4 * (1 - (pauliSameBasisTest ι basis).commutingWinProb S) := by
  let alice : (ι → Bool) × (ι → Bool) × (ι → Bool) → PauliConsistencyQuestion ι :=
    fun (a, b, _) => PauliConsistencyQuestion.ofChecked basis a b
  let bob : (ι → Bool) × (ι → Bool) × (ι → Bool) → PauliConsistencyQuestion ι :=
    fun (a, _, c) => PauliConsistencyQuestion.ofChecked basis a c
  have h := SeededGame.sum_norm_sub_sq_le_of_bitAgreement (Probability.PMF.uniformOfFintype _)
    (fun r => (alice r, bob r)) (fun r => (alice r).checkedBit) (fun r => (bob r).checkedBit) S
  simp only [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ← mul_sum] at h
  simpa only [pauliSameBasisTest, ← div_eq_inv_mul, ← card_univ,
    ← expect_eq_sum_div_card, Fintype.expect_prod_type, alice, bob] using h

private theorem expect_localDistance_le :
    (𝔼 a : ι → Bool, 𝔼 b : ι → Bool,
      let q := PauliConsistencyQuestion.ofChecked basis a b
      S.state.norm (((S.alice q).map q.checkedBit).observable -
        PauliConsistencyQuestion.averagedObservable S.bob basis a) ^ 2) ≤
      4 * (1 - (pauliSameBasisTest ι basis).commutingWinProb S) := by
  refine le_trans (expect_le_expect fun a _ => expect_le_expect fun b _ => ?_)
    (expect_roundDistance_le basis S)
  exact S.state.norm_sub_expect_sq_le univ univ_nonempty _ _

/-- The mean squared distance between the two averaged observables is at most four times the
same-basis game's rejection probability. -/
theorem expect_norm_sub_sq_le_of_pauliSameBasisTest :
    (𝔼 a : ι → Bool, S.state.norm
      (PauliConsistencyQuestion.averagedObservable S.alice basis a -
        PauliConsistencyQuestion.averagedObservable S.bob basis a) ^ 2) ≤
      4 * (1 - (pauliSameBasisTest ι basis).commutingWinProb S) := by
  refine le_trans (expect_le_expect fun a _ => ?_) (expect_localDistance_le basis S)
  exact S.state.norm_expect_sub_sq_le univ univ_nonempty _ _

open BitString

/-- Averaging Alice's dummy coordinate preserves consistency with the special-question observable
on odd pairs. The left-hand side is masked by the odd-pair event, so the special-question
rejection probability on the right is weighted by the same density. The two games share Alice's
question measurement. -/
theorem oddExpect_norm_sub_sq_le_of_pauliConsistency [Nonempty ι]
    (T : CommutingStrategy (PauliConsistencyQuestion ι) (PauliConsistencyQuestion ι)
      (Bool × Bool) Bool 𝒜) (hstate : T.state = S.state) (halice : T.alice = S.alice) :
    oddExpect (fun x z =>
      let q : PauliConsistencyQuestion ι := ⟨x, z, basis⟩
      let a := if basis then z else x
      S.state.norm
        (PauliConsistencyQuestion.averagedObservable S.alice basis a - (T.bob q).observable) ^ 2) ≤
      32 * (1 - (pauliSameBasisTest ι basis).commutingWinProb S) +
        8 * ((oddPairs ι).dens : ℝ) *
          (1 - (pauliSpecialQuestionTest ι basis).commutingWinProb T) := by
  let q (x z : ι → Bool) : PauliConsistencyQuestion ι := ⟨x, z, basis⟩
  let a (x z : ι → Bool) := if basis then z else x
  let A (x z) := ((S.alice (q x z)).map (q x z).checkedBit).observable
  let Aavg (x z) := PauliConsistencyQuestion.averagedObservable S.alice basis (a x z)
  let Bavg (x z) := PauliConsistencyQuestion.averagedObservable S.bob basis (a x z)
  let B (x z) := (T.bob (q x z)).observable
  let d (x z) := S.state.norm (Aavg x z - A x z) ^ 2
  let e (x z) := S.state.norm (A x z - B x z) ^ 2
  have hspread : (𝔼 x, 𝔼 z, d x z) ≤
      16 * (1 - (pauliSameBasisTest ι basis).commutingWinProb S) := by
    have havg := expect_norm_sub_sq_le_of_pauliSameBasisTest basis S
    have hlocal := expect_localDistance_le basis S
    have hlocal' : (𝔼 x, 𝔼 z, S.state.norm (A x z - Bavg x z) ^ 2) ≤
        4 * (1 - (pauliSameBasisTest ι basis).commutingWinProb S) := by
      cases basis
      · exact hlocal
      · rwa [expect_comm]
    have havg' : (𝔼 x, 𝔼 z, S.state.norm (Aavg x z - Bavg x z) ^ 2) ≤
        4 * (1 - (pauliSameBasisTest ι basis).commutingWinProb S) := by
      cases basis
      · simpa [Aavg, Bavg, a, Fintype.expect_const] using havg
      · rw [expect_comm]
        simpa [Aavg, Bavg, a, Fintype.expect_const] using havg
    have htri : (𝔼 x, 𝔼 z, d x z) ≤ 𝔼 x, 𝔼 z,
        (2 * S.state.norm (Aavg x z - Bavg x z) ^ 2 +
          2 * S.state.norm (A x z - Bavg x z) ^ 2) := by
      refine expect_le_expect fun x _ => expect_le_expect fun z _ => ?_
      rw [S.state.norm_sub_comm (A x z) (Bavg x z)]
      exact S.state.norm_sub_sq_le_through _ _ _
    simp only [expect_add_distrib, ← mul_expect] at htri
    linarith
  have hd : oddExpect d ≤ 16 * (1 - (pauliSameBasisTest ι basis).commutingWinProb S) := by
    refine le_trans ?_ hspread
    rw [oddExpect_def]
    refine expect_le_expect fun x _ => expect_le_expect fun z _ => ?_
    split_ifs
    exacts [le_rfl, sq_nonneg _]
  have he : oddExpect e ≤ ((oddPairs ι).dens : ℝ) *
      (4 * (1 - (pauliSpecialQuestionTest ι basis).commutingWinProb T)) := by
    rw [oddExpect_eq_dens_smul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h := expect_norm_sub_sq_le_of_pauliSpecialQuestionTest basis T
    rw [hstate, halice] at h
    change (𝔼 p : ↥(oddPairs ι), e p.val.fst p.val.snd) ≤ _ at h
    rw [univ_eq_attach] at h
    simpa only [expect, card_attach, sum_attach (oddPairs ι) (fun p => e p.fst p.snd)] using h
  have htri : oddExpect (fun x z => S.state.norm (Aavg x z - B x z) ^ 2) ≤
      oddExpect (fun x z => 2 * d x z + 2 * e x z) :=
    oddExpect_mono fun x z _ => S.state.norm_sub_sq_le_through _ _ _
  rw [oddExpect_add, oddExpect_const_mul, oddExpect_const_mul] at htri
  change oddExpect (fun x z => S.state.norm (Aavg x z - B x z) ^ 2) ≤ _
  linarith

end Cslib.PCP
