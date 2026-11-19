/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingGame
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

## Main results

* `Cslib.PCP.rejection_pauliBraidingLinearityStrategy_le`: rejection in a fixed basis.
* `Cslib.PCP.one_sub_le_expect_re_apply_mul_mul_of_pauliBraidingLinearity`: the correlation
  estimate for either basis and either role assignment.
-/

public section

namespace Cslib.PCP

open Finset Quantum
open scoped BigOperators ENNReal

variable {n : ℕ} {Q A 𝒜 : Type*} [Fintype A] [CStarAlgebra 𝒜] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜]

/-- The strategy on one basis of the Pauli braiding verifier, with malformed answers
decoded as the all-false pair. -/
def pauliBraidingLinearityStrategy (basis : Bool)
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

end Cslib.PCP
