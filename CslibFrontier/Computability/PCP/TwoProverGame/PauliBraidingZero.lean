/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LinearityDiagonal
public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingConsistency
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Diagonal linearity seeds in the Pauli braiding game

Conditioning the linearity branch on equal strings in the original pair, a fixed
basis and a fixed role assignment retains a fraction `1 / (4 * 2^n)` of the seeds.
The remaining choices are the common string, the other player's dummy, and the check.
This isolates the probability cost of using these rounds to analyze the zero string.

## Main definitions

* `Cslib.PCP.pauliBraidingDiagonalGame`: the conditioned linearity verifier.

## Main results

* `Cslib.PCP.rejection_pauliBraidingDiagonalGame_le`: transfer of the rejection budget.
* `Cslib.PCP.expect_norm_pauliBraidingBasisObservable_sub_sq_le`: full uniform consistency
  from the consistency and linearity branches.
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
  have hmass : ((Probability.PMF.uniformOfFintype Bool) basis).toReal = (2 : ℝ)⁻¹ := by
    rw [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv]
    norm_num
  rw [hmass, ← game.answersWinProb_pullbackSeed seedLaw (PauliBraidingSeed.linearity basis) answer]
    at hbasis
  change (2 : ℝ)⁻¹ * (1 - fixedBasis.answersWinProb answer) ≤
    1 - linearity.answersWinProb answer at hbasis
  have hdiag := fixedBasis.weighted_rejection_pullback_uniform_le
    (SymmetricLinearitySeed.diagonal n roles) answer
  let size : ℝ := Fintype.card (Fin n → Bool)
  have hsize : size ≠ 0 := by
    dsimp [size]
    exact_mod_cast Fintype.card_ne_zero
  have hcard :
      (Fintype.card (Fin 3 × (Fin n → Bool) × (Fin n → Bool)) : ℝ) /
        Fintype.card (SymmetricLinearitySeed n) = (2 * size)⁻¹ := by
    rw [Fintype.card_congr (SymmetricLinearitySeed.equivProd n)]
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    change 3 * (size * size) / (2 * (3 * (size * (size * size)))) = _
    field_simp
  rw [hcard] at hdiag
  change (2 * size)⁻¹ * (1 - diagonal.answersWinProb answer) ≤
    1 - fixedBasis.answersWinProb answer at hdiag
  have h := (mul_le_mul_of_nonneg_left hdiag (by norm_num : 0 ≤ (2 : ℝ)⁻¹)).trans hbasis
  change (1 - diagonal.answersWinProb answer) / (4 * size) ≤ 1 - linearity.answersWinProb answer
  convert h using 1
  rw [div_eq_mul_inv, ← mul_assoc, ← mul_inv]
  ring

/-- The visible question for zero with a dummy in one of the two bases. -/
@[expose] def pauliBraidingZeroQuestion (basis : Bool) (dummy : Fin n → Bool) :
    PauliBraidingQuestion n Q :=
  .basis basis (0, dummy)

/-- Decode the bit checked at zero by the diagonal linearity test. The all-false string
is first after sorting, including when the dummy is also zero. -/
@[expose] def pauliBraidingZeroBit : (Bool × Bool) ⊕ A → Bool :=
  Sum.elim Prod.fst (fun _ => false)

omit [Nonempty (Fin n)] in
open BitString in
/-- The linearity and consistency decoders at zero agree away from the duplicated
zero query. They also agree at the tie in the X basis. -/
theorem pauliBraidingZero_decoding (basis : Bool) (dummy : Fin n → Bool)
    (h : dummy ≠ 0 ∨ basis = false) :
    let q := PauliConsistencyQuestion.ofChecked basis 0 dummy
    q.toBraidingQuestion = (pauliBraidingZeroQuestion basis dummy : PauliBraidingQuestion n Q) ∧
      (Sum.elim q.braidingCheckedBit (fun _ : A => false)) = pauliBraidingZeroBit := by
  intro q
  cases basis
  · change (.basis false (cond (lexSwap (0 : Fin n → Bool) dummy) Prod.swap id (0, dummy)) :
      PauliBraidingQuestion n Q) = .basis false (0, dummy) ∧ _
    refine ⟨by rw [lexSwap_zero_left]; rfl, ?_⟩
    funext answer
    cases answer with
    | inr malformed => rfl
    | inl bits =>
      change (cond (lexSwap (0 : Fin n → Bool) dummy) Prod.swap id bits).1 = bits.1
      rw [lexSwap_zero_left]
      rfl
  have hn : dummy ≠ 0 := h.resolve_right Bool.noConfusion
  have hswap : lexSwap dummy 0 = true := by
    rw [lexSwap_reverse (Ne.symm hn), lexSwap_zero_left]
    rfl
  change PauliConsistencyQuestion.toBraidingQuestion ⟨dummy, 0, true⟩ =
      (pauliBraidingZeroQuestion true dummy : PauliBraidingQuestion n Q) ∧
    Sum.elim (PauliConsistencyQuestion.braidingCheckedBit ⟨dummy, 0, true⟩)
      (fun _ : A => false) = pauliBraidingZeroBit
  constructor
  · rw [PauliConsistencyQuestion.toBraidingQuestion, hswap]
    rfl
  · funext answer
    cases answer with
    | inr malformed => rfl
    | inl bits =>
      change (cond (lexSwap dummy (0 : Fin n → Bool)) Prod.swap id bits).2 = bits.1
      rw [hswap]
      rfl

open BitString Finset Quantum in
/-- For either role assignment, the three checks of a diagonal round bound the point
player’s probability of a true decoded answer at zero.
Malformed answers are decoded as false and still rejected by the verifier. -/
theorem prob_true_le_pauliBraidingDiagonal {𝒜 : Type*} [Fintype A] [Ring 𝒜] [StarRing 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜] [TopologicalSpace 𝒜]
    [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜)
    (a dummy : Fin n → Bool) :
    let game := pauliBraidingDiagonalGame n G special decode roles basis
    let logical := cond roles S.swap S
    let loss (k : Fin 3) :=
      1 - ({ game with seed := PMF.pure (k, a, dummy) }).commutingWinProb S
    ((logical.bob (pauliBraidingZeroQuestion basis dummy)).map
      pauliBraidingZeroBit).prob logical.state true ≤ loss 0 + loss 1 + loss 2 := by
  classical
  intro game logical loss
  let x : PauliBraidingQuestion n Q := .basis basis (a, a)
  let point (c : Fin n → Bool) : PauliBraidingQuestion n Q :=
    .basis basis (cond (lexSwap c dummy) Prod.swap id (c, dummy))
  let pair : (Bool × Bool) ⊕ A → Bool × Bool := Sum.elim id (fun _ => (false, false))
  let pointRead (c : Fin n → Bool) (ans : (Bool × Bool) ⊕ A) : Bool :=
    (cond (lexSwap c dummy) Prod.swap id (pair ans)).1
  have hread : pointRead 0 = pauliBraidingZeroBit := by
    funext ans
    cases ans <;> simp [pointRead, pair, pauliBraidingZeroBit]
  have htie : lexSwap a a = false := by simp [lexSwap]
  have hquery (k : Fin 3) : game.query (k, a, dummy) =
      cond roles Prod.swap id (x, point (linearityQuery k a a)) := by
    cases roles <;>
      simp only [game, pauliBraidingDiagonalGame, SeededGame.pullbackSeed, Function.comp_apply,
      pauliBraidingGame, pauliBraidingBranchGame, SymmetricLinearitySeed.diagonal,
        Function.Embedding.coeFn_mk, symmetricLinearityGame, htie, Bool.cond_false,
        Bool.cond_true, id_eq, Prod.swap_prod_mk, x, point]
  have hcheck (k : Fin 3) (p q : (Bool × Bool) ⊕ A)
      (h : game.accepts (k, a, dummy) (cond roles q p) (cond roles p q)) :
      pointRead (linearityQuery k a a) q = linearityCheck k (pair p) := by
    cases roles <;> cases p <;> cases q
    all_goals
      first
      | exact False.elim h
      | simpa only [game, pauliBraidingDiagonalGame, SeededGame.pullbackSeed, pauliBraidingGame,
          pauliBraidingBranchGame, SymmetricLinearitySeed.diagonal, Function.Embedding.coeFn_mk,
          symmetricLinearityGame, htie, Bool.cond_false, Bool.cond_true, id_eq, Prod.swap_prod_mk,
          pointRead, pair, Sum.elim_inl] using h
  have hcompare (k : Fin 3) :
      (∑ p, ∑ q, if pointRead (linearityQuery k a a) q = linearityCheck k (pair p) then 0
        else logical.prob x (point (linearityQuery k a a)) p q) ≤ loss k := by
    rw [show loss k = _ from game.one_sub_commutingWinProb_pure_seed (k, a, dummy) S, hquery]
    have hloss :
        (∑ p, ∑ q, if game.accepts (k, a, dummy) (cond roles q p) (cond roles p q) then 0
          else logical.prob x (point (linearityQuery k a a)) p q) =
        ∑ p, ∑ q, if game.accepts (k, a, dummy) p q then 0 else
          S.prob (cond roles Prod.swap id (x, point (linearityQuery k a a))).1
            (cond roles Prod.swap id (x, point (linearityQuery k a a))).2 p q := by
      cases roles
      · rfl
      · simp only [logical, Bool.cond_true, Prod.swap_prod_mk, S.prob_swap]
        exact sum_comm
    rw [← hloss]
    refine sum_le_sum fun p _ => sum_le_sum fun q _ => ?_
    by_cases h : game.accepts (k, a, dummy) (cond roles q p) (cond roles p q)
    · simp only [h, hcheck k p q h, ite_true, le_refl]
    · simp only [h, ite_false]
      split_ifs
      · exact logical.prob_nonneg _ _ _ _
      · exact le_rfl
  have hzero : linearityQuery 2 a a = 0 := by simp [linearityQuery]
  have hzeroQuestion : point 0 = pauliBraidingZeroQuestion basis dummy := by
    simp [point, pauliBraidingZeroQuestion]
  rw [← hzeroQuestion, ← hread]
  have h := logical.prob_true_le_diagonal_linearity x (point a) (point 0) pair
    (pointRead a) (pointRead 0)
  have h0 := hcompare 0
  have h1 := hcompare 1
  have h2 := hcompare 2
  rw [hzero] at h2
  simp only [linearityQuery, linearityCheck, Fin.reduceEq, ite_true, ite_false] at h0 h1
  simp only [linearityCheck, Fin.reduceEq, ite_false] at h2
  dsimp only at h
  linarith only [h, h0, h1, h2]

open Finset Quantum in
private theorem expect_diagonal_le {𝒜 : Type*} [Fintype A] [Ring 𝒜] [StarRing 𝒜]
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
    rw [Fintype.expect_prod_type]
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
  rw [hscore] at havg
  have hbudget := rejection_pauliBraidingDiagonalGame_le G special decode roles basis S.answers
  change (1 - game.commutingWinProb S) / (4 * Fintype.card (Fin n → Bool)) ≤ _ at hbudget
  change (𝔼 a, 𝔼 dummy, bad a dummy) / Fintype.card (Fin n → Bool) ≤ _
  refine (div_le_div_of_nonneg_right havg (by positivity)).trans ?_
  rw [show 3 * (1 - game.commutingWinProb S) / (Fintype.card (Fin n → Bool) : ℝ) =
      12 * ((1 - game.commutingWinProb S) / (4 * Fintype.card (Fin n → Bool))) by ring]
  exact mul_le_mul_of_nonneg_left hbudget (by norm_num)

open Finset Quantum in
/-- The probability of a true decoded zero answer, averaged over the dummy and weighted by
the uniform mass of zero, is at most twelve times the linearity-branch rejection probability. -/
theorem expect_prob_true_pauliBraidingZero_le {𝒜 : Type*} [Fintype A] [Ring 𝒜] [StarRing 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜] [TopologicalSpace 𝒜]
    [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    let logical := cond roles S.swap S
    (𝔼 dummy, ((logical.bob (pauliBraidingZeroQuestion basis dummy)).map
      pauliBraidingZeroBit).prob logical.state true) / Fintype.card (Fin n → Bool) ≤
      12 * (1 - (pauliBraidingBranchGame n G special decode 0).commutingWinProb S) := by
  intro logical
  let bad (dummy : Fin n → Bool) :=
    ((logical.bob (pauliBraidingZeroQuestion basis dummy)).map
      pauliBraidingZeroBit).prob logical.state true
  have h := expect_diagonal_le G special decode roles basis S (fun _ => bad)
    (prob_true_le_pauliBraidingDiagonal G special decode roles basis S)
  simpa only [Fintype.expect_const] using h

open BitString Finset Quantum in
/-- When the pair player receives the duplicated zero string, their second bit can be
true only if at least one of the first-coordinate and parity checks rejects. Both checks
query zero with the same dummy. -/
theorem prob_true_second_le_pauliBraidingZero_tie {𝒜 : Type*} [Fintype A] [Ring 𝒜] [StarRing 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜] [TopologicalSpace 𝒜]
    [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) (dummy : Fin n → Bool) :
    let game := pauliBraidingDiagonalGame n G special decode roles basis
    let logical := cond roles S.swap S
    let question : PauliBraidingQuestion n Q := .basis basis (0, 0)
    let loss (k : Fin 3) := 1 - ({ game with seed := PMF.pure (k, 0, dummy) }).commutingWinProb S
    ((logical.alice question).map (Sum.elim Prod.snd (fun _ => false))).prob logical.state true ≤
      loss 0 + loss 2 := by
  classical
  intro game logical question loss
  let pointQuestion : PauliBraidingQuestion n Q := pauliBraidingZeroQuestion basis dummy
  let accepted (k : Fin 3) (p q : (Bool × Bool) ⊕ A) :=
    game.accepts (k, 0, dummy) (cond roles q p) (cond roles p q)
  let read (p : (Bool × Bool) ⊕ A) := Sum.elim Prod.snd (fun _ => false) p
  have htie : lexSwap (0 : Fin n → Bool) 0 = false := by simp [lexSwap]
  have hpoint (k : Fin 3) : linearityQuery k (0 : Fin n → Bool) 0 = 0 := by
    simp [linearityQuery]
  have hquery (k : Fin 3) : game.query (k, 0, dummy) =
      cond roles Prod.swap id (question, pointQuestion) := by
    cases roles <;>
      simp only [game, pauliBraidingDiagonalGame, SeededGame.pullbackSeed, Function.comp_apply,
        pauliBraidingGame, pauliBraidingBranchGame, SymmetricLinearitySeed.diagonal,
        Function.Embedding.coeFn_mk, symmetricLinearityGame, hpoint, htie, Bool.cond_false,
        Bool.cond_true, id_eq, Prod.swap_prod_mk, question, pointQuestion,
        pauliBraidingZeroQuestion, lexSwap_zero_left]
  have hloss (k : Fin 3) :
      loss k = ∑ p, ∑ q, if accepted k p q then 0 else logical.prob question pointQuestion p q := by
    rw [show loss k = _ from game.one_sub_commutingWinProb_pure_seed (k, 0, dummy) S, hquery]
    cases roles
    · rfl
    · simp only [accepted, logical, Bool.cond_true, Prod.swap_prod_mk, S.prob_swap]
      exact sum_comm
  have hmarginal :
      ((logical.alice question).map read).prob logical.state true =
        ∑ p, ∑ q, if read p = true then logical.prob question pointQuestion p q else 0 := by
    rw [Measurement.prob_map, sum_filter]
    refine sum_congr rfl fun p _ => ?_
    split_ifs
    · exact (logical.sum_prob_bob question pointQuestion p).symm
    · simp
  have hchecks (p q : (Bool × Bool) ⊕ A) (hp : read p = true) :
      ¬ (accepted 0 p q ∧ accepted 2 p q) := by
    intro h
    rcases p with bits | malformed
    · rcases q with point | malformed
      · let bit := pauliBraidingZeroBit (A := A) (.inl point)
        have hdecoded (k : Fin 3) :
            accepted k (.inl bits) (.inl point) ↔ bit = linearityCheck k bits := by
          cases roles <;>
            simp only [accepted, game, pauliBraidingDiagonalGame, SeededGame.pullbackSeed,
              pauliBraidingGame, pauliBraidingBranchGame, SymmetricLinearitySeed.diagonal,
              Function.Embedding.coeFn_mk, symmetricLinearityGame, hpoint, htie, Bool.cond_false,
              Bool.cond_true, id_eq, Prod.swap_prod_mk, bit, lexSwap_zero_left,
              pauliBraidingZeroBit, Sum.elim_inl]
        have hone : bits.2 = true := hp
        have hp₀ := (hdecoded 0).mp h.1
        have hp₂ := (hdecoded 2).mp h.2
        simp only [linearityCheck, Fin.reduceEq, ite_true, ite_false, hone,
          Bool.xor_true] at hp₀ hp₂
        exact Bool.not_ne_self bits.1 (hp₂.symm.trans hp₀)
      · cases roles <;> exact h.1
    · exact Bool.noConfusion hp
  change ((logical.alice question).map read).prob logical.state true ≤ _
  rw [hmarginal, hloss 0, hloss 2]
  simp only [← sum_add_distrib]
  refine sum_le_sum fun p _ => sum_le_sum fun q _ => ?_
  have hn := logical.prob_nonneg question pointQuestion p q
  by_cases hp : read p = true
  · have h := hchecks p q hp
    by_cases h₀ : accepted 0 p q <;> by_cases h₂ : accepted 2 p q <;>
      simp only [hp, h₀, h₂, ite_true, ite_false] at *
    all_goals first | contradiction | linarith
  · simp only [hp]
    positivity

open Quantum in
/-- The second-bit error at the duplicated zero query has the joint uniform weight of
zero and its zero dummy. It is controlled by using the same player in the pair role. -/
theorem weighted_prob_true_second_pauliBraidingZero_tie_le {𝒜 : Type*} [Fintype A] [Ring 𝒜]
    [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜] [TopologicalSpace 𝒜]
    [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    let logical := cond roles S.swap S
    let probability := ((logical.alice (.basis basis (0, 0))).map
      (Sum.elim Prod.snd (fun _ => false))).prob logical.state true
    probability / (Fintype.card (Fin n → Bool) : ℝ) ^ 2 ≤
      12 * (1 - (pauliBraidingBranchGame n G special decode 0).commutingWinProb S) := by
  classical
  intro logical probability
  have h := expect_diagonal_le G special decode roles basis S
    (fun a _ => if a = 0 then probability else 0) (fun a dummy => by
      by_cases ha : a = 0
      · subst a
        simp only [ite_true]
        have h := prob_true_second_le_pauliBraidingZero_tie G special decode roles basis S dummy
        have h₁ := sub_nonneg.mpr (SeededGame.answersWinProb_le_one
          ({ pauliBraidingDiagonalGame n G special decode roles basis with
              seed := PMF.pure (1, 0, dummy) }) S.answers)
        dsimp only at h h₁
        change probability ≤ _ at h
        simp only [SeededGame.commutingWinProb] at h ⊢
        linarith only [h, h₁]
      · simp only [ha, ite_false]
        exact add_nonneg (add_nonneg (sub_nonneg.mpr (SeededGame.answersWinProb_le_one _ _))
          (sub_nonneg.mpr (SeededGame.answersWinProb_le_one _ _)))
          (sub_nonneg.mpr (SeededGame.answersWinProb_le_one _ _)))
  simp only [Fintype.expect_const, Fintype.expect_ite_eq', NNRat.smul_def, NNRat.cast_inv,
    NNRat.cast_natCast] at h
  convert h using 1
  ring

open BitString Finset Quantum in
/-- Both bases of the consistency decoder at zero are controlled by linearity rejection,
including the second coordinate used by the Z-basis decoder on a duplicated query. -/
theorem expect_prob_true_pauliBraidingConsistencyZero_le {𝒜 : Type*} [Fintype A] [Ring 𝒜]
    [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜] [TopologicalSpace 𝒜]
    [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    let logical := cond roles S.swap S
    (𝔼 dummy, let q := PauliConsistencyQuestion.ofChecked basis 0 dummy
      let measure := (logical.bob q.toBraidingQuestion).map
        (Sum.elim q.braidingCheckedBit fun _ => false)
      measure.prob logical.state true) / Fintype.card (Fin n → Bool) ≤
      24 * (1 - (pauliBraidingBranchGame n G special decode 0).commutingWinProb S) := by
  classical
  intro logical
  let consistency (dummy : Fin n → Bool) :=
    let q := PauliConsistencyQuestion.ofChecked basis 0 dummy
    ((logical.bob q.toBraidingQuestion).map
      (Sum.elim q.braidingCheckedBit fun _ => false)).prob logical.state true
  let linearity (dummy : Fin n → Bool) :=
    ((logical.bob (pauliBraidingZeroQuestion basis dummy)).map
      pauliBraidingZeroBit).prob logical.state true
  let secondBit : ℝ := ((logical.bob (.basis basis (0, 0))).map
    (Sum.elim Prod.snd (fun _ => false))).prob logical.state true
  have hnonneg : 0 ≤ secondBit := Measurement.prob_nonneg _ _ _
  have hcompare (dummy : Fin n → Bool) :
      consistency dummy ≤ linearity dummy + if dummy = 0 then secondBit else 0 := by
    by_cases h : dummy ≠ 0 ∨ basis = false
    · obtain ⟨hq, hread⟩ := pauliBraidingZero_decoding (Q := Q) (A := A) basis dummy h
      unfold consistency linearity
      dsimp only
      rw [hq, hread]
      exact le_add_of_nonneg_right (by split_ifs <;> positivity)
    · push Not at h
      obtain ⟨rfl, hb⟩ := h
      have hb' : basis = true := by cases basis <;> simp_all
      have htie : lexSwap (0 : Fin n → Bool) 0 = false := by simp [lexSwap]
      have heq : consistency 0 = secondBit := by
        subst basis
        dsimp [consistency, secondBit, PauliConsistencyQuestion.ofChecked,
          PauliConsistencyQuestion.toBraidingQuestion]
        rw [htie]
        congr 2
        funext answer
        cases answer <;> simp [PauliConsistencyQuestion.braidingCheckedBit,
          PauliConsistencyQuestion.checkedBit, htie]
      rw [heq]
      simpa only [ite_true, eq_self] using
        (le_add_of_nonneg_left (Measurement.prob_nonneg logical.state
          ((logical.bob (pauliBraidingZeroQuestion basis 0)).map pauliBraidingZeroBit)
          true) : secondBit ≤ linearity 0 + secondBit)
  have haverage := expect_le_expect (s := (univ : Finset (Fin n → Bool))) fun d _ => hcompare d
  rw [expect_add_distrib] at haverage
  have hsingle : (𝔼 d : Fin n → Bool, if d = 0 then secondBit else 0) =
      secondBit / Fintype.card (Fin n → Bool) := by
    rw [Fintype.expect_ite_eq']
    simp only [NNRat.smul_def, NNRat.cast_inv, NNRat.cast_natCast]
    ring
  rw [hsingle] at haverage
  have hlinear := expect_prob_true_pauliBraidingZero_le G special decode roles basis S
  have htie := weighted_prob_true_second_pauliBraidingZero_tie_le G special decode (!roles) basis S
  have hsecond : secondBit / (Fintype.card (Fin n → Bool) : ℝ) ^ 2 ≤
      12 * (1 - (pauliBraidingBranchGame n G special decode 0).commutingWinProb S) := by
    cases roles <;> exact htie
  change (𝔼 d, linearity d) / (Fintype.card (Fin n → Bool) : ℝ) ≤ _ at hlinear
  change (𝔼 d, consistency d) / (Fintype.card (Fin n → Bool) : ℝ) ≤ _
  have hscaled := div_le_div_of_nonneg_right haverage
    (Nat.cast_nonneg (α := ℝ) (Fintype.card (Fin n → Bool)))
  rw [add_div, div_div, ← pow_two] at hscaled
  linarith only [hscaled, hlinear, hsecond]

section UniformConsistency

open BitString Finset Quantum

variable {𝒜 : Type*} [Fintype A] [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [SelfAdjointDecompose 𝒜] [TopologicalSpace 𝒜]
  [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜] [Module ℚ≥0 𝒜]

private theorem weighted_norm_zero_sub_one_le
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    let logical := cond roles S.swap S
    let observable := 𝔼 d, pauliBraidingBasisObservable logical.bob basis 0 d
    logical.state.norm (observable - 1) ^ 2 / Fintype.card (Fin n → Bool) ≤
      96 * (1 - (pauliBraidingBranchGame n G special decode 0).commutingWinProb S) := by
  intro logical observable
  let M (d : Fin n → Bool) :=
    let q := PauliConsistencyQuestion.ofChecked basis 0 d
    (logical.bob q.toBraidingQuestion).map (Sum.elim q.braidingCheckedBit fun _ => false)
  have hnorm : logical.state.norm (observable - 1) ^ 2 ≤
      4 * (𝔼 d, (M d).prob logical.state true) := by
    change logical.state.norm ((𝔼 d, (M d).observable) - 1) ^ 2 ≤ _
    rw [Finset.mul_expect]
    exact (logical.state.norm_expect_sub_sq_le univ univ_nonempty _ _).trans
      (expect_le_expect fun d _ => (M d).norm_observable_sub_one_sq_le logical.state)
  have h := expect_prob_true_pauliBraidingConsistencyZero_le G special decode roles basis S
  change (𝔼 d, (M d).prob logical.state true) / (Fintype.card (Fin n → Bool) : ℝ) ≤ _ at h
  have hscaled := div_le_div_of_nonneg_right hnorm
    (Nat.cast_nonneg (α := ℝ) (Fintype.card (Fin n → Bool)))
  rw [mul_div_assoc] at hscaled
  exact hscaled.trans (by linarith only [h])

/-- The full uniform average of squared consistency distances of the basis observables
is controlled by consistency rejection on the nonzero strings and linearity rejection at
zero. Both branch scores use the very same commuting strategy. -/
theorem expect_norm_pauliBraidingBasisObservable_sub_sq_le
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    let a := pauliBraidingBasisObservable S.alice basis
    let b := pauliBraidingBasisObservable S.bob basis
    (𝔼 x, S.state.norm ((𝔼 y, a x y) - (𝔼 y, b x y)) ^ 2) ≤
      896 * ((oddPairs (Fin n)).dens : ℝ) *
        (1 - (pauliBraidingBranchGame n G special decode 2).commutingWinProb S) +
      384 * (1 - (pauliBraidingBranchGame n G special decode 0).commutingWinProb S) := by
  intro a b
  let aZero := 𝔼 y, a 0 y
  let bZero := 𝔼 y, b 0 y
  let size : ℝ := Fintype.card (Fin n → Bool)
  have ha := weighted_norm_zero_sub_one_le G special decode true basis S
  have hb := weighted_norm_zero_sub_one_le G special decode false basis S
  change S.state.norm (aZero - 1) ^ 2 / size ≤ _ at ha
  change S.state.norm (bZero - 1) ^ 2 / size ≤ _ at hb
  have htri := S.state.norm_sub_sq_le_through aZero 1 bZero
  rw [← neg_sub bZero 1, S.state.norm_neg] at htri
  have hscaled := div_le_div_of_nonneg_right htri (show 0 ≤ size by positivity)
  rw [add_div, mul_div_assoc, mul_div_assoc] at hscaled
  have havg := expect_norm_pauliBraidingBasisObservable_sub_sq_le_add_zero G special decode basis S
  dsimp only at havg
  change _ ≤ _ + S.state.norm (aZero - bZero) ^ 2 / size at havg
  linarith only [ha, hb, hscaled, havg]

end UniformConsistency

end Cslib.PCP
