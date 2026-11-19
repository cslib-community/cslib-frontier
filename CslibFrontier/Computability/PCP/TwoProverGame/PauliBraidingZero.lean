/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LinearityDiagonal
public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingDiagonal
public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingConsistency
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# The zero-string term in Pauli braiding consistency

The parity check sends the point player zero on duplicated pairs. The two equality
checks on those same pairs control the parity of the pair answer. This supplies the
zero-string contribution missing from the odd-pair consistency checks.

## Main results

* `Cslib.PCP.expect_norm_pauliBraidingBasisObservable_sub_sq_le`: full uniform consistency
  from the consistency and linearity branches.
-/

public section

namespace Cslib.PCP

open scoped BigOperators

variable {n : ℕ} [Nonempty (Fin n)] {Q A : Type*}

/-- The visible question for zero with a dummy in one of the two bases. -/
@[expose] def pauliBraidingZeroQuestion (basis : Bool) (dummy : Fin n → Bool) :
    PauliBraidingQuestion n Q :=
  .basis basis (0, dummy)

/-- Decode the bit checked at zero by the diagonal linearity test. The all-false string
is first after sorting, including when the dummy is also zero. -/
@[expose] def pauliBraidingZeroBit : (Bool × Bool) ⊕ A → Bool :=
  Sum.elim Prod.fst (fun _ => false)

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
  have h := expect_le_of_pauliBraidingDiagonal_checks G special decode roles basis S (fun _ => bad)
    (prob_true_le_pauliBraidingDiagonal G special decode roles basis S)
  simpa only [Fintype.expect_const] using h

open Quantum in
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
  apply prob_bad_le_of_pauliBraidingDiagonal_checks
    G special decode roles basis S 0 dummy 0 2 Prod.snd
  · simp [linearityQuery]
  · intro bits h
    simpa only [linearityCheck, Fin.reduceEq, ite_true, ite_false, h, Bool.xor_true] using
      Ne.symm (Bool.not_ne_self bits.1)

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
  have h := expect_le_of_pauliBraidingDiagonal_checks G special decode roles basis S
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
    · obtain ⟨hq, hread⟩ :=
        PauliConsistencyQuestion.ofChecked_braiding (Q := Q) basis 0 dummy h
      unfold consistency linearity
      dsimp only at hq hread ⊢
      rw [hq, hread, lexSwap_zero_left]
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
