/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingGame
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Duplicated pairs in the Pauli braiding linearity branch

Fixing the basis and roles and using equal strings in the original pair selects a
fraction `1 / (4 * 2^n)` of linearity seeds. These rounds bound the probability
that a pair answer calls for opposite point answers in two checks with the same
visible questions.

## Main definitions

* `Cslib.PCP.pauliBraidingDiagonalGame`: the conditioned linearity verifier.

## Main results

* `Cslib.PCP.rejection_pauliBraidingDiagonalGame_le`: transfer of the rejection budget.
* `Cslib.PCP.expect_prob_mismatch_pauliBraidingDiagonal_le`: weighted pair-bit mismatch.
-/

public section

namespace Cslib.PCP

open scoped BigOperators

variable {n : ℕ} [Nonempty (Fin n)] {Q A : Type*}

/-- Fix the roles and keep exactly the seeds at which the original two strings coincide. -/
@[expose] def SymmetricLinearitySeed.diagonal (n : ℕ) (roles : Bool) :
    (Fin 3 × (Fin n → Bool) × (Fin n → Bool)) ↪ SymmetricLinearitySeed n where
  toFun := fun (k, a, dummy) => ⟨roles, k, a, a, dummy⟩
  inj' := by
    rintro ⟨k, a, d⟩ ⟨k', a', d'⟩ h
    cases h
    rfl

/-- The symmetric linearity round with a fixed basis and role assignment and equal original
strings. The check, common string and dummy remain independent and uniform. -/
@[expose] noncomputable def pauliBraidingDiagonalGame (n : ℕ) [Nonempty (Fin n)]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool) :
    SeededGame (Fin 3 × (Fin n → Bool) × (Fin n → Bool))
      (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) :=
  (pauliBraidingGame n G special decode).pullbackSeed (Probability.PMF.uniformOfFintype _)
    fun r => .linearity basis (SymmetricLinearitySeed.diagonal n roles r)

/-- For a fixed role and basis, the diagonal round's rejection contributes its actual
sampling mass to the rejection probability of the linearity branch. -/
theorem rejection_pauliBraidingDiagonalGame_le
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool)
    (answer : PauliBraidingQuestion n Q → PauliBraidingQuestion n Q →
      PMF (((Bool × Bool) ⊕ A) × ((Bool × Bool) ⊕ A))) :
    (1 - (pauliBraidingDiagonalGame n G special decode roles basis).answersWinProb answer) /
        (4 * Fintype.card (Fin n → Bool)) ≤
      1 - (pauliBraidingBranchGame n G special decode 0).answersWinProb answer := by
  let game := pauliBraidingGame n G special decode
  let seedLaw := Probability.PMF.uniformOfFintype (SymmetricLinearitySeed n)
  let fixedBasis := game.pullbackSeed seedLaw (PauliBraidingSeed.linearity basis)
  let diagonal := pauliBraidingDiagonalGame n G special decode roles basis
  let linearity := pauliBraidingBranchGame n G special decode 0
  have hbasis := game.weighted_rejection_le_of_bind_seed (Probability.PMF.uniformOfFintype Bool)
    (fun basis => seedLaw.map (PauliBraidingSeed.linearity basis)) answer basis
  rw [Probability.PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    ← game.answersWinProb_pullbackSeed seedLaw (PauliBraidingSeed.linearity basis) answer]
    at hbasis
  have hdiag := fixedBasis.weighted_rejection_pullback_uniform_le
    (SymmetricLinearitySeed.diagonal n roles) answer
  let size : ℝ := Fintype.card (Fin n → Bool)
  have hsize : size ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hcard :
      (Fintype.card (Fin 3 × (Fin n → Bool) × (Fin n → Bool)) : ℝ) /
        Fintype.card (SymmetricLinearitySeed n) = (2 * size)⁻¹ := by
    rw [Fintype.card_congr (SymmetricLinearitySeed.equivProd n)]
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    change 3 * (size * size) / (2 * (3 * (size * (size * size)))) = _
    field_simp
  rw [hcard] at hdiag
  have h := (mul_le_mul_of_nonneg_left hdiag (by positivity : 0 ≤ (2 : ℝ)⁻¹)).trans hbasis
  have h4 : (2 : ℝ) * 2 = 4 := by norm_num
  rwa [inv_mul_eq_div, inv_mul_eq_div, div_div, mul_right_comm (2 : ℝ) size 2, h4] at h

open Finset Quantum in
/-- Average a pointwise bound by the three check losses at the sampling weight of
a duplicated pair with fixed roles and basis. -/
theorem expect_le_of_pauliBraidingDiagonal_checks {𝒜 : Type*} [Fintype A] [Ring 𝒜] [StarRing 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜] [TopologicalSpace 𝒜]
    [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜)
    (bad : (Fin n → Bool) → (Fin n → Bool) → ℝ)
    (hlocal : ∀ a dummy,
      let game := pauliBraidingDiagonalGame n G special decode roles basis
      let loss (k : Fin 3) :=
        1 - ({ game with seed := PMF.pure (k, a, dummy) }).commutingWinProb S
      bad a dummy ≤ loss 0 + loss 1 + loss 2) :
    (𝔼 a, 𝔼 dummy, bad a dummy) / Fintype.card (Fin n → Bool) ≤
      12 * (1 - (pauliBraidingBranchGame n G special decode 0).commutingWinProb S) := by
  let game := pauliBraidingDiagonalGame n G special decode roles basis
  let lose (r : Fin 3 × (Fin n → Bool) × (Fin n → Bool)) :=
    1 - ({ game with seed := PMF.pure r }).commutingWinProb S
  have havg : (𝔼 a, 𝔼 dummy, bad a dummy) ≤ 3 * (𝔼 r, lose r) := by
    have h := expect_le_expect (s := (univ : Finset (Fin n → Bool))) fun a _ =>
      expect_le_expect (s := (univ : Finset (Fin n → Bool))) fun dummy _ => hlocal a dummy
    refine h.trans_eq ?_
    simp_rw [Fintype.expect_prod_type]
    rw [Finset.expect_comm univ univ (fun k a => 𝔼 d, lose (k, a, d)), Finset.mul_expect]
    refine expect_congr rfl fun a _ => ?_
    rw [Finset.expect_comm univ univ (fun k d => lose (k, a, d)), Finset.mul_expect]
    refine expect_congr rfl fun d _ => ?_
    rw [Fintype.expect_eq_sum_div_card, Fin.sum_univ_three, Fintype.card_fin]
    push_cast
    ring
  have hscore : (𝔼 r, lose r) = 1 - game.commutingWinProb S := by
    unfold SeededGame.commutingWinProb
    rw [SeededGame.rejection_eq_sum]
    change _ = ∑ r, ((Probability.PMF.uniformOfFintype _) r).toReal * lose r
    simp only [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ← mul_sum, Fintype.expect_eq_sum_div_card]
    ring
  have hbudget := rejection_pauliBraidingDiagonalGame_le G special decode roles basis S.answers
  change (1 - game.commutingWinProb S) / (4 * Fintype.card (Fin n → Bool)) ≤
    1 - (pauliBraidingBranchGame n G special decode 0).commutingWinProb S at hbudget
  rw [div_mul_eq_div_div_swap] at hbudget
  have hdiv := div_le_div_of_nonneg_right (hscore ▸ havg)
    (Nat.cast_nonneg (Fintype.card (Fin n → Bool)))
  rw [mul_div_assoc] at hdiv
  linarith

open BitString Finset Quantum in
/-- Two checks with the same visible questions charge the probability of any pair
answer on which their required bits differ to the sum of their rejection probabilities. -/
theorem prob_bad_le_of_pauliBraidingDiagonal_checks {𝒜 : Type*} [Fintype A] [Ring 𝒜] [StarRing 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜] [TopologicalSpace 𝒜]
    [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) (a dummy : Fin n → Bool)
    (k l : Fin 3) (read : Bool × Bool → Bool)
    (hquery : linearityQuery k a a = linearityQuery l a a)
    (hcheck : ∀ bits, read bits = true → linearityCheck k bits ≠ linearityCheck l bits) :
    let game := pauliBraidingDiagonalGame n G special decode roles basis
    let logical := cond roles S.swap S
    let question : PauliBraidingQuestion n Q := .basis basis (a, a)
    let loss (i : Fin 3) := 1 - ({ game with seed := PMF.pure (i, a, dummy) }).commutingWinProb S
    ((logical.alice question).map (Sum.elim read (fun _ => false))).prob logical.state true ≤
      loss k + loss l := by
  classical
  intro game logical question loss
  let c := linearityQuery k a a
  let pointQuestion : PauliBraidingQuestion n Q :=
    .basis basis (cond (lexSwap c dummy) Prod.swap id (c, dummy))
  let accepted (i : Fin 3) (p q : (Bool × Bool) ⊕ A) :=
    game.accepts (i, a, dummy) (cond roles q p) (cond roles p q)
  let bad := Sum.elim read (fun _ : A => false)
  have htie : lexSwap a a = false := by simp [lexSwap]
  have hquestions (i : Fin 3) (hi : linearityQuery i a a = c) :
      game.query (i, a, dummy) = cond roles Prod.swap id (question, pointQuestion) := by
    cases roles <;>
      simp only [game, pauliBraidingDiagonalGame, SeededGame.pullbackSeed, Function.comp_apply,
        pauliBraidingGame, pauliBraidingBranchGame, SymmetricLinearitySeed.diagonal,
        Function.Embedding.coeFn_mk, symmetricLinearityGame, hi, htie, Bool.cond_false,
        Bool.cond_true, id_eq, Prod.swap_prod_mk, question, pointQuestion]
  have hloss (i : Fin 3) (hi : linearityQuery i a a = c) :
      loss i = ∑ p, ∑ q, if accepted i p q then 0 else logical.prob question pointQuestion p q := by
    dsimp only [loss]
    rw [game.one_sub_commutingWinProb_pure_seed (i, a, dummy) S, hquestions i hi]
    cases roles
    · rfl
    · simp only [accepted, logical, Bool.cond_true, Prod.swap_prod_mk, S.prob_swap]
      exact sum_comm
  have hmarginal :
      ((logical.alice question).map bad).prob logical.state true =
        ∑ p, ∑ q, if bad p = true then logical.prob question pointQuestion p q else 0 := by
    rw [Measurement.prob_map, sum_filter]
    refine sum_congr rfl fun p _ => ?_
    split_ifs
    · exact (logical.sum_prob_bob question pointQuestion p).symm
    · simp
  have hchecks (p q : (Bool × Bool) ⊕ A) (hp : bad p = true) :
      ¬ (accepted k p q ∧ accepted l p q) := by
    rintro ⟨hk, hl⟩
    rcases p with bits | malformed
    · rcases q with point | malformed
      · have hdecoded (i : Fin 3) (hi : linearityQuery i a a = c) :
            accepted i (.inl bits) (.inl point) ↔
              (cond (lexSwap c dummy) Prod.swap id point).1 = linearityCheck i bits := by
          cases roles <;>
            simp only [accepted, game, pauliBraidingDiagonalGame, SeededGame.pullbackSeed,
              pauliBraidingGame, pauliBraidingBranchGame, SymmetricLinearitySeed.diagonal,
              Function.Embedding.coeFn_mk, symmetricLinearityGame, hi, htie, Bool.cond_false,
              Bool.cond_true, id_eq, Prod.swap_prod_mk]
        exact hcheck bits hp ((hdecoded k rfl |>.mp hk).symm.trans
          (hdecoded l hquery.symm |>.mp hl))
      · cases roles <;> exact hk
    · exact Bool.noConfusion hp
  change ((logical.alice question).map bad).prob logical.state true ≤ _
  rw [hmarginal, hloss k rfl, hloss l hquery.symm]
  simp only [← sum_add_distrib]
  refine sum_le_sum fun p _ => sum_le_sum fun q _ => ?_
  have hn := logical.prob_nonneg question pointQuestion p q
  split_ifs with hp hk hl <;> first | linarith | exact absurd ⟨hk, hl⟩ (hchecks p q hp)

open Quantum in
/-- If the two bits of the duplicated pair answer differ, at least one of the two
equality checks rejects. The average mismatch is weighted by the uniform mass of a tie. -/
theorem expect_prob_mismatch_pauliBraidingDiagonal_le {𝒜 : Type*} [Fintype A] [Ring 𝒜] [StarRing 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜] [TopologicalSpace 𝒜]
    [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    let logical := cond roles S.swap S
    (𝔼 a, ((logical.alice (.basis basis (a, a))).map
      (Sum.elim (fun bits => bits.1 ^^ bits.2) (fun _ => false))).prob logical.state true) /
      Fintype.card (Fin n → Bool) ≤
        12 * (1 - (pauliBraidingBranchGame n G special decode 0).commutingWinProb S) := by
  intro logical
  let bad (a : Fin n → Bool) := ((logical.alice (.basis basis (a, a))).map
    (Sum.elim (fun bits => bits.1 ^^ bits.2) (fun _ => false))).prob logical.state true
  simpa only [Fintype.expect_const] using expect_le_of_pauliBraidingDiagonal_checks G special
    decode roles basis S (fun a _ => bad a) fun a d => by
      have h01 := prob_bad_le_of_pauliBraidingDiagonal_checks G special decode roles basis S a d 0 1
        (fun bits => bits.1 ^^ bits.2) (by simp [linearityQuery]) (by decide)
      have h₂ := sub_nonneg.mpr (SeededGame.answersWinProb_le_one
        ({ pauliBraidingDiagonalGame n G special decode roles basis with
            seed := PMF.pure (2, a, d) }) S.answers)
      dsimp only at h01 h₂
      change bad a ≤ _ at h01
      simp only [SeededGame.commutingWinProb] at h01 ⊢
      linarith only [h01, h₂]

end Cslib.PCP
