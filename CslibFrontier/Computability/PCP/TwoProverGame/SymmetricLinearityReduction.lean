/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.SymmetricLinearity
public import CslibFrontier.Foundations.Quantum.Algebra.MeasurementAverage
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Removing the dummy query from symmetric linearity

Fix the roles and average the point player's decoded binary measurements over the dummy.
The resulting strategy plays the asymmetric linearity test. Averaging its score over
the two assignments gives the symmetric game's score. Averaging can destroy projectivity
of the point measurement, so the linearity estimate uses it as a binary POVM and retains
projectivity on the pair side.

## Main definitions

* `Cslib.PCP.CommutingStrategy.asymmetricLinearity`: the strategy with a uniform dummy.

## Main results

* `Cslib.PCP.CommutingStrategy.commutingWinProb_symmetricLinearityGame`: exact score transfer.
* `Cslib.PCP.CommutingStrategy.one_sub_le_expect_re_apply_mul_mul_of_symmetricLinearityGame`:
  the triple-product bound for either point player.
-/

public section

namespace Cslib.PCP.CommutingStrategy

open Finset Quantum
open scoped BigOperators

variable {n : ℕ} {𝒜 : Type*}

section Algebra

variable [Ring 𝒜] [PartialOrder 𝒜] [Algebra ℂ 𝒜]
  [IsOrderedAddMonoid 𝒜]

private def sortPair (q : (Fin n → Bool) × (Fin n → Bool)) : (Fin n → Bool) × (Fin n → Bool) :=
  cond (BitString.lexSwap q.1 q.2) Prod.swap id q

private def unsortAnswer (q : (Fin n → Bool) × (Fin n → Bool)) (r : Bool × Bool) : Bool × Bool :=
  cond (BitString.lexSwap q.1 q.2) Prod.swap id r

private def withLinearityDummy
    (S : CommutingStrategy ((Fin n → Bool) × (Fin n → Bool)) ((Fin n → Bool) × (Fin n → Bool))
      (Bool × Bool) (Bool × Bool) 𝒜) (dummy : Fin n → Bool) :
    CommutingStrategy (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)) Bool (Bool × Bool) 𝒜 :=
  S.map (fun c => sortPair (c, dummy)) sortPair
    (fun c r => (unsortAnswer (c, dummy) r).1) unsortAnswer

variable [Module ℚ≥0 𝒜] [PosSMulMono ℚ≥0 𝒜]

/-- The asymmetric strategy obtained when Alice plays the point role. Alice's measurement
averages the decoded responses over a uniform dummy. Bob's measurement restores the original
order of the pair and is independent of the dummy. Use `S.swap` for the other role assignment. -/
noncomputable def asymmetricLinearity
    (S : CommutingStrategy ((Fin n → Bool) × (Fin n → Bool)) ((Fin n → Bool) × (Fin n → Bool))
      (Bool × Bool) (Bool × Bool) 𝒜) :
    CommutingStrategy (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)) Bool (Bool × Bool) 𝒜 where
  state := S.state
  alice c := Measurement.average fun dummy => (S.withLinearityDummy dummy).alice c
  bob q := (S.withLinearityDummy 0).bob q
  commute c q a b := by
    change Commute (𝔼 d, ((S.withLinearityDummy d).alice c).effect a)
      (((S.withLinearityDummy 0).bob q).effect b)
    rw [Finset.expect, ← NNRat.cast_smul_eq_nnqsmul ℂ]
    exact (Commute.sum_left _ _ _ fun d _ => (S.withLinearityDummy d).commute c q a b).smul_left _

/-- The observable on a point query is the uniform average of the observables for the
decoded point bit. The checked string is the first coordinate before sorting. -/
theorem observable_asymmetricLinearity
    (S : CommutingStrategy ((Fin n → Bool) × (Fin n → Bool)) ((Fin n → Bool) × (Fin n → Bool))
      (Bool × Bool) (Bool × Bool) 𝒜) (c : Fin n → Bool) :
    (S.asymmetricLinearity.alice c).observable =
      𝔼 d, ((S.alice (cond (BitString.lexSwap c d) Prod.swap id (c, d))).map
        (fun r => (cond (BitString.lexSwap c d) Prod.swap id r).1)).observable :=
  Measurement.observable_average _

private theorem prob_asymmetricLinearity
    (S : CommutingStrategy ((Fin n → Bool) × (Fin n → Bool)) ((Fin n → Bool) × (Fin n → Bool))
      (Bool × Bool) (Bool × Bool) 𝒜) (c : Fin n → Bool)
    (q : (Fin n → Bool) × (Fin n → Bool)) (a : Bool) (b : Bool × Bool) :
    S.asymmetricLinearity.prob c q a b = 𝔼 d, (S.withLinearityDummy d).prob c q a b := by
  simp only [asymmetricLinearity, prob, Measurement.average, withLinearityDummy, map, Finset.expect]
  have hcoeff (t : ℚ≥0) (z : ℂ) : ((t : ℂ) * z).re = t • z.re := by
    rw [← RCLike.ofReal_nnratCast (K := ℂ)]
    change ((↑(t : ℝ) : ℂ) * z).re = _
    rw [Complex.re_ofReal_mul, NNRat.smul_def]
  rw [← NNRat.cast_smul_eq_nnqsmul ℂ, smul_mul_assoc, map_smul, sum_mul, map_sum, smul_eq_mul,
    hcoeff, Complex.re_sum]

private theorem linearityTestProb_asymmetricLinearity
    (S : CommutingStrategy ((Fin n → Bool) × (Fin n → Bool)) ((Fin n → Bool) × (Fin n → Bool))
      (Bool × Bool) (Bool × Bool) 𝒜) :
    S.asymmetricLinearity.linearityTestProb = 𝔼 k : Fin 3, 𝔼 a, 𝔼 b, 𝔼 d, ∑ γ, ∑ r,
      if γ = linearityCheck k r then
        (S.withLinearityDummy d).prob (linearityQuery k a b) (a, b) γ r else 0 := by
  unfold linearityTestProb
  refine expect_congr rfl fun k _ => expect_congr rfl fun a _ => expect_congr rfl fun b _ => ?_
  rw [expect_sum_comm]
  simp_rw [expect_sum_comm, prob_asymmetricLinearity]
  refine sum_congr rfl fun γ _ => sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

omit [Module ℚ≥0 𝒜] [PosSMulMono ℚ≥0 𝒜] in
private theorem symmetricLinearityRound_eq
    (S : CommutingStrategy ((Fin n → Bool) × (Fin n → Bool)) ((Fin n → Bool) × (Fin n → Bool))
      (Bool × Bool) (Bool × Bool) 𝒜) (roles : Bool) (k : Fin 3)
    (a b dummy : Fin n → Bool) :
    let game := symmetricLinearityGame n
    let seed : SymmetricLinearitySeed n := ⟨roles, k, a, b, dummy⟩
    let logical := cond roles S S.swap
    (∑ p, ∑ q, if game.accepts seed p q then
      S.prob (game.query seed).1 (game.query seed).2 p q else 0) =
    ∑ γ, ∑ r, if γ = linearityCheck k r then
      (logical.withLinearityDummy dummy).prob (linearityQuery k a b) (a, b) γ r else 0 := by
  classical
  intro game seed logical
  have h := logical.sum_ite_prob_map (fun c => sortPair (c, dummy)) sortPair
    (fun c r => (unsortAnswer (c, dummy) r).1) unsortAnswer (linearityQuery k a b) (a, b)
    (fun γ r => γ = linearityCheck k r)
  change _ = ∑ γ, ∑ r, if γ = linearityCheck k r then
    (logical.map _ _ _ _).prob (linearityQuery k a b) (a, b) γ r else 0
  rw [h]
  cases roles
  · simp only [game, seed, logical, symmetricLinearityGame, sortPair, unsortAnswer,
      Bool.cond_false, id_eq, prob_swap]
    exact sum_comm
  · rfl

variable [StarRing 𝒜] [StarOrderedRing 𝒜] [TopologicalSpace 𝒜]
  [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]

/-- The symmetric verifier's score is the mean of the two asymmetric scores, one for each
assignment of the point and pair roles. -/
theorem commutingWinProb_symmetricLinearityGame
    (S : CommutingStrategy ((Fin n → Bool) × (Fin n → Bool)) ((Fin n → Bool) × (Fin n → Bool))
      (Bool × Bool) (Bool × Bool) 𝒜) :
    (symmetricLinearityGame n).commutingWinProb S =
      𝔼 roles : Bool, (cond roles S S.swap).asymmetricLinearity.linearityTestProb := by
  classical
  let game := symmetricLinearityGame n
  let f (seed : SymmetricLinearitySeed n) := ∑ p, ∑ q, if game.accepts seed p q then
    S.prob (game.query seed).1 (game.query seed).2 p q else 0
  let e := SymmetricLinearitySeed.equivProd n
  change game.commutingWinProb S = _
  calc
    _ = 𝔼 seed, f seed := game.commutingWinProb_eq_expect_of_uniform rfl S
    _ = 𝔼 t, f (e.symm t) :=
      Fintype.expect_equiv e f (fun t => f (e.symm t)) (fun s => by rw [e.symm_apply_apply])
    _ = _ := by
      simp only [Fintype.expect_prod_type, linearityTestProb_asymmetricLinearity]
      refine expect_congr rfl fun roles _ => expect_congr rfl fun k _ =>
        expect_congr rfl fun a _ => expect_congr rfl fun b _ => expect_congr rfl fun d _ => ?_
      exact symmetricLinearityRound_eq S roles k a b d

end Algebra

section CStar

variable [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [Module ℚ≥0 𝒜] [PosSMulMono ℚ≥0 𝒜]

/-- If the symmetric game rejects with probability at most `ε`, either player's observable
averaged over the dummy has triple-product correlation at least `1 - 12ε - 2√(24ε)`.
The pair measurements are projective on both sides, since either player can play that role. -/
theorem one_sub_le_expect_re_apply_mul_mul_of_symmetricLinearityGame
    (S : CommutingStrategy ((Fin n → Bool) × (Fin n → Bool)) ((Fin n → Bool) × (Fin n → Bool))
      (Bool × Bool) (Bool × Bool) 𝒜)
    (hA : ∀ q, (S.alice q).IsProjective) (hB : ∀ q, (S.bob q).IsProjective)
    {ε : ℝ} (hwin : 1 - ε ≤ (symmetricLinearityGame n).commutingWinProb S) (roles : Bool) :
    let T := (cond roles S S.swap).asymmetricLinearity
    1 - 12 * ε - √(24 * ε) - √(24 * ε) ≤
      𝔼 a, 𝔼 b, (T.state ((T.alice a).observable * (T.alice b).observable *
        (T.alice (a + b)).observable)).re := by
  intro T
  have hmax (R : CommutingStrategy ((Fin n → Bool) × (Fin n → Bool))
      ((Fin n → Bool) × (Fin n → Bool)) (Bool × Bool) (Bool × Bool) 𝒜) :
      R.asymmetricLinearity.linearityTestProb ≤ 1 := by
    rw [← commutingWinProb_linearityGame]
    exact SeededGame.answersWinProb_le_one _ _
  rw [commutingWinProb_symmetricLinearityGame, Fintype.expect_bool] at hwin
  simp only [Bool.cond_false, Bool.cond_true] at hwin
  have hscore : 1 - 2 * ε ≤ T.linearityTestProb := by
    cases roles
    · change 1 - 2 * ε ≤ S.swap.asymmetricLinearity.linearityTestProb
      linarith [hmax S]
    · change 1 - 2 * ε ≤ S.asymmetricLinearity.linearityTestProb
      linarith [hmax S.swap]
  have hpair (q : (Fin n → Bool) × (Fin n → Bool)) : (T.bob q).IsProjective := by
    cases roles
    · exact (hA (sortPair q)).map _
    · exact (hB (sortPair q)).map _
  have h := T.one_sub_le_expect_re_apply_mul_mul_of_linearityTest hpair hscore
  rwa [show 6 * (2 * ε) = 12 * ε by ring, show 12 * (2 * ε) = 24 * ε by ring] at h

end CStar

end Cslib.PCP.CommutingStrategy
