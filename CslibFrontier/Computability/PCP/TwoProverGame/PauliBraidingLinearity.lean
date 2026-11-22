/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingConsistency
import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingDiagonal
public import CslibFrontier.Computability.PCP.TwoProverGame.SymmetricLinearityReduction
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# The linearity branch of the Pauli braiding game

Restrict a strategy's questions to one basis. Decoding malformed answers as two false bits
can only increase the linearity score. Each basis contributes half its conditional
rejection probability to the branch's rejection probability. The symmetric linearity
reduction then controls the averaged point observables in each basis and role assignment.

## Main definitions

* `Cslib.PCP.pauliBraidingLinearityStrategy`: the decoded strategy on one basis.
* `Cslib.PCP.pauliBraidingPointMeasurement`: the averaged binary point measurement.

## Main results

* `Cslib.PCP.rejection_pauliBraidingLinearityStrategy_le`: rejection in a fixed basis.
* `Cslib.PCP.one_sub_le_expect_re_apply_mul_mul_of_pauliBraidingLinearity`: the correlation
  estimate for either basis and either role assignment.
* `Cslib.PCP.expect_norm_asymmetricLinearity_sub_basis_sq_le`: the averaged point and
  consistency decoders agree up to an error controlled by linearity rejection.
-/

public section

namespace Cslib.PCP

open Finset Quantum
open scoped BigOperators ENNReal

variable {n : ℕ} {Q A 𝒜 : Type*} [Fintype A] [CStarAlgebra 𝒜] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜]

/-- The strategy on one basis of the Pauli braiding verifier, with malformed answers
decoded as the all-false pair. -/
@[expose] def pauliBraidingLinearityStrategy (basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    CommutingStrategy ((Fin n → Bool) × (Fin n → Bool)) ((Fin n → Bool) × (Fin n → Bool))
      (Bool × Bool) (Bool × Bool) 𝒜 :=
  S.map (.basis basis) (.basis basis)
    (fun _ => Sum.elim id (fun _ => (false, false)))
    (fun _ => Sum.elim id (fun _ => (false, false)))

variable [Nonempty (Fin n)]

private theorem winProb_fixedBasis_le
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) (basis : Bool) :
    let sym := symmetricLinearityGame n
    ((pauliBraidingGame n G special decode).pullbackSeed sym.seed
      (.linearity basis)).commutingWinProb S ≤
        sym.commutingWinProb (pauliBraidingLinearityStrategy basis S) := by
  classical
  intro sym
  let game := (pauliBraidingGame n G special decode).pullbackSeed sym.seed
    (.linearity basis)
  change game.commutingWinProb S ≤ _
  rw [SeededGame.commutingWinProb_eq_sum, SeededGame.commutingWinProb_eq_sum]
  refine sum_le_sum fun r _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  unfold pauliBraidingLinearityStrategy
  rw [S.sum_ite_prob_map]
  have hq : game.query r = (.basis basis (sym.query r).1, .basis basis (sym.query r).2) := by
    simp only [game, SeededGame.pullbackSeed, Function.comp_apply, pauliBraidingGame,
      pauliBraidingBranchGame, sym]
  rw [hq]
  refine sum_le_sum fun p _ => sum_le_sum fun q _ => ?_
  split_ifs with h₁ h₂ h₂
  · exact le_rfl
  · cases p <;> cases q <;> first | exact (h₂ h₁).elim | exact h₁.elim
  · exact S.prob_nonneg _ _ _ _
  · exact le_rfl

/-- For either basis, the rejection of the decoded symmetric strategy is at most twice
the combined verifier's linearity rejection. -/
theorem rejection_pauliBraidingLinearityStrategy_le
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) (basis : Bool) :
    1 - (symmetricLinearityGame n).commutingWinProb (pauliBraidingLinearityStrategy basis S) ≤
      2 * (1 - (pauliBraidingBranchGame n G special decode 0).commutingWinProb S) := by
  let game := pauliBraidingGame n G special decode
  let law := (symmetricLinearityGame n).seed
  have h := game.weighted_rejection_le_of_bind_seed
    (Probability.PMF.uniformOfFintype Bool)
    (fun b => law.map (PauliBraidingSeed.linearity b)) S.answers basis
  rw [← game.answersWinProb_pullbackSeed law (PauliBraidingSeed.linearity basis) S.answers,
    Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv] at h
  have hmass : (↑(Fintype.card Bool) : ℝ≥0∞).toReal = 2 := by norm_num
  rw [hmass] at h
  have hdecode := winProb_fixedBasis_le G special decode S basis
  change (2 : ℝ)⁻¹ * (1 - (game.pullbackSeed law (.linearity basis)).commutingWinProb S) ≤
    1 - (pauliBraidingBranchGame n G special decode 0).commutingWinProb S at h
  linarith

variable [Module ℚ≥0 𝒜] [PosSMulMono ℚ≥0 𝒜]

/-- Either physical player's averaged point observables in either basis have triple-product
correlation at least `1 - 24ε - 2√(48ε)` if the Pauli braiding linearity branch rejects with
probability at most `ε`. The underlying measurements on basis questions are projective. -/
theorem one_sub_le_expect_re_apply_mul_mul_of_pauliBraidingLinearity
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜)
    (hA : ∀ basis q, (S.alice (.basis basis q)).IsProjective)
    (hB : ∀ basis q, (S.bob (.basis basis q)).IsProjective)
    {ε : ℝ} (hwin : 1 - ε ≤ (pauliBraidingBranchGame n G special decode 0).commutingWinProb S)
    (basis roles : Bool) :
    let R := pauliBraidingLinearityStrategy basis S
    let T := (cond roles R R.swap).asymmetricLinearity
    1 - 24 * ε - √(48 * ε) - √(48 * ε) ≤
      𝔼 a, 𝔼 b, (T.state ((T.alice a).observable * (T.alice b).observable *
        (T.alice (a + b)).observable)).re := by
  intro R T
  have hscore : 1 - 2 * ε ≤ (symmetricLinearityGame n).commutingWinProb R := by
    have h := rejection_pauliBraidingLinearityStrategy_le G special decode S basis
    change 1 - (symmetricLinearityGame n).commutingWinProb R ≤ _ at h
    linarith
  have h := R.one_sub_le_expect_re_apply_mul_mul_of_symmetricLinearityGame
    (fun q => (hA basis q).map _) (fun q => (hB basis q).map _) hscore roles
  dsimp only at h
  rwa [show 12 * (2 * ε) = 24 * ε by ring, show 24 * (2 * ε) = 48 * ε by ring] at h

open BitString in
/-- The binary point measurement in one basis, with the checked string sent with a
uniform dummy and decoded in its original coordinate. -/
@[expose] noncomputable def pauliBraidingPointMeasurement
    (M : PauliBraidingQuestion n Q → Measurement ((Bool × Bool) ⊕ A) 𝒜)
    (basis : Bool) (c : Fin n → Bool) : Measurement Bool 𝒜 :=
  Measurement.average fun d =>
    (M (.basis basis (cond (lexSwap c d) Prod.swap id (c, d)))).map
      (Sum.elim (fun r => (cond (lexSwap c d) Prod.swap id r).1) fun _ => false)

omit [Nonempty (Fin n)] in
open BitString in
/-- The observable in the asymmetrized strategy uses that same point measurement. -/
theorem observable_asymmetricLinearity_eq_pointMeasurement
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) (basis roles : Bool) (c : Fin n → Bool) :
    let R := pauliBraidingLinearityStrategy basis S
    ((cond roles R R.swap).asymmetricLinearity.alice c).observable =
      (pauliBraidingPointMeasurement (cond roles S.alice S.bob) basis c).observable := by
  intro R
  rw [CommutingStrategy.observable_asymmetricLinearity, pauliBraidingPointMeasurement,
    Measurement.observable_average]
  refine expect_congr rfl fun d _ => ?_
  let read (r : Bool × Bool) := (cond (lexSwap c d) Prod.swap id r).1
  have hread : read ∘ Sum.elim id (fun _ : A => (false, false)) =
      Sum.elim read (fun _ => false) := by
    funext a
    cases a with
    | inl r => rfl
    | inr a =>
      change (cond (lexSwap c d) Prod.swap id (false, false)).1 = false
      cases lexSwap c d <;> rfl
  change (Measurement.map read ((cond roles R R.swap).alice _)).observable =
    (Measurement.map (Sum.elim read (fun _ => false)) _).observable
  cases roles <;>
    simp only [R, Bool.cond_false, Bool.cond_true, pauliBraidingLinearityStrategy,
      CommutingStrategy.swap, CommutingStrategy.map, Measurement.map_map, hread]

open BitString in
/-- The averaged point and consistency observables agree in X. In Z, the squared
state-norm distance is controlled by the linearity rejection probability for general
measurements. -/
theorem expect_norm_asymmetricLinearity_sub_basis_sq_le
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜)
    (basis roles : Bool) :
    let R := pauliBraidingLinearityStrategy basis S
    let T := (cond roles R R.swap).asymmetricLinearity
    let M := cond roles S.alice S.bob
    (𝔼 c, S.state.norm ((T.alice c).observable -
      (𝔼 d, pauliBraidingBasisObservable M basis c d)) ^ 2) ≤
      if basis then 48 / (Fintype.card (Fin n → Bool) : ℝ) *
        (1 - (pauliBraidingBranchGame n G special decode 0).commutingWinProb S)
      else 0 := by
  classical
  intro R T M
  let point (c d : Fin n → Bool) :=
    ((M (.basis basis (cond (lexSwap c d) Prod.swap id (c, d)))).map
      (Sum.elim (fun r => (cond (lexSwap c d) Prod.swap id r).1) fun _ => false)).observable
  let tie (c : Fin n → Bool) := M (.basis basis (c, c))
  let first : (Bool × Bool) ⊕ A → Bool := Sum.elim Prod.fst fun _ => false
  let second : (Bool × Bool) ⊕ A → Bool := Sum.elim Prod.snd fun _ => false
  let diff (c : Fin n → Bool) := ((tie c).map first).observable - ((tie c).map second).observable
  let bad (c : Fin n → Bool) := ((tie c).map (fun a => first a ^^ second a)).prob S.state true
  let size := Fintype.card (Fin n → Bool)
  have hpoint (c : Fin n → Bool) : (T.alice c).observable = 𝔼 d, point c d := by
    rw [observable_asymmetricLinearity_eq_pointMeasurement S basis roles c,
      pauliBraidingPointMeasurement, Measurement.observable_average]
  have hcompare (c d : Fin n → Bool) :
      point c d - pauliBraidingBasisObservable M basis c d =
        if basis then (if d = c then diff c else 0) else 0 := by
    cases basis
    · change point c d - point c d = 0
      exact sub_self _
    · by_cases h : d = c
      · subst d
        change point c c -
          ((M (.basis true (cond (lexSwap c c) Prod.swap id (c, c)))).map
            (Sum.elim (fun r => (cond (lexSwap c c) Prod.swap id r).2) fun _ => false)).observable =
          if c = c then diff c else 0
        have htie : lexSwap c c = false := by simp [lexSwap]
        simp only [point, diff, tie, first, second, htie, Bool.cond_false, id_eq, ite_true, eq_self]
      · obtain ⟨hq, hbit⟩ :=
          PauliConsistencyQuestion.ofChecked_braiding (Q := Q) true c d (Or.inl h)
        simp only [point, pauliBraidingBasisObservable, pauliBraidingBasisBitMeasurement,
          hq, hbit, h, ite_true, ite_false, sub_self]
  have hdiff (c : Fin n → Bool) :
      (T.alice c).observable - (𝔼 d, pauliBraidingBasisObservable M basis c d) =
        if basis then (size : ℚ≥0)⁻¹ • diff c else 0 := by
    rw [hpoint, ← expect_sub_distrib]
    simp_rw [hcompare]
    cases basis <;> simp [size]
  simp only [hdiff]
  cases basis
  · simp [AlgState.norm_zero]
  · have hweighted : (𝔼 c, bad c) / size ≤
        12 * (1 - (pauliBraidingBranchGame n G special decode 0).commutingWinProb S) := by
      have h := expect_prob_mismatch_pauliBraidingDiagonal_le G special decode (!roles) true S
      dsimp only at h
      have hdecode : (fun a => first a ^^ second a) =
          Sum.elim (fun bits : Bool × Bool => bits.1 ^^ bits.2) (fun _ => false) := by
        funext a
        cases a <;> rfl
      simp only [bad, tie, hdecode, size]
      cases roles <;> exact h
    simp only [ite_true, AlgState.norm_nnqsmul, NNRat.cast_inv, NNRat.cast_natCast, mul_pow]
    calc
      _ ≤ 𝔼 c, (4 * ((size : ℝ)⁻¹) ^ 2) * bad c := by
        refine expect_le_expect fun c _ => ?_
        have h := (tie c).norm_observable_map_sub_sq_le S.state first second
        change S.state.norm (diff c) ^ 2 ≤ 4 * bad c at h
        simpa only [mul_assoc, mul_left_comm (((size : ℝ)⁻¹) ^ 2) 4] using
          mul_le_mul_of_nonneg_left h (sq_nonneg ((size : ℝ)⁻¹))
      _ = (4 / size) * ((𝔼 c, bad c) / size) := by
        rw [← mul_expect]
        ring
      _ ≤ _ := by
        rw [show (48 : ℝ) / size = (4 / size) * 12 by ring, mul_assoc]
        exact mul_le_mul_of_nonneg_left hweighted (by positivity)

end Cslib.PCP
