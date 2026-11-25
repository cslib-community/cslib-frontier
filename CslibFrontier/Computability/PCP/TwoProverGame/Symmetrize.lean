/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
public import CslibFrontier.Foundations.Quantum.POVM.Restriction
import CslibFrontier.Foundations.LinearAlgebra.Matrix.BlockDiagonalOrder

/-!
# Symmetrizing a tensor strategy

Give both players the sum of the two local spaces. The shared state puts equal weight on
the original strategy and its swap, on disjoint pairs of summands. A question is answered
by the block diagonal measurement formed from the original players' measurements.

The construction also describes expectations against a measurement on one side that need
not preserve the two summands. This is how a measurement obtained on the symmetric space
can be restricted to the original players, as in [JNVWY2020LowIndividualDegree, §6].
-/

public section

namespace Cslib.PCP.QuantumStrategy

open Cslib.Quantum Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

variable {Q A B ι κ : Type*} [Fintype A] [Fintype B]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

private def roleMeasurement (M : POVM A ι) (N : POVM A κ) : POVM A (ι ⊕ κ) where
  effect a := fromBlocks (M.effect a) 0 0 (N.effect a)
  posSemidef a := fromBlocks_posSemidef_diagonal _ _ (M.posSemidef a) (N.posSemidef a)
  sum_effect := by
    rw [← fromBlocks_one]
    ext (i | i) (j | j)
    · simpa only [Matrix.sum_apply, fromBlocks_apply₁₁] using congr_fun (congr_fun M.sum_effect i) j
    · simp
    · simp
    · simpa only [Matrix.sum_apply, fromBlocks_apply₂₂] using congr_fun (congr_fun N.sum_effect i) j

private theorem roleMeasurement_projective (M : POVM A ι) (N : POVM A κ)
    (hM : M.toMeasurement.IsProjective) (hN : N.toMeasurement.IsProjective) :
    (roleMeasurement M N).toMeasurement.IsProjective := by
  intro a
  change fromBlocks (M.effect a) 0 0 (N.effect a) * fromBlocks (M.effect a) 0 0 (N.effect a) =
    fromBlocks (M.effect a) 0 0 (N.effect a)
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    show M.effect a * M.effect a = M.effect a from hM a,
    show N.effect a * N.effect a = N.effect a from hN a]

private def roleVec (v : ι × κ → ℂ) : (ι ⊕ κ) × (ι ⊕ κ) → ℂ
  | (.inl i, .inr j) => v (i, j)
  | (.inr j, .inl i) => v (i, j)
  | _ => 0

private noncomputable def roleState (ψ : EuclideanSpace ℂ (ι × κ)) :
    EuclideanSpace ℂ ((ι ⊕ κ) × (ι ⊕ κ)) :=
  ((Real.sqrt 2 : ℂ)⁻¹) • WithLp.toLp 2 (roleVec ψ.ofLp)

omit [DecidableEq ι] [DecidableEq κ] in
private theorem norm_roleState (ψ : EuclideanSpace ℂ (ι × κ)) (hψ : ‖ψ‖ = 1) :
    ‖roleState ψ‖ = 1 := by
  have hsum : (∑ i, ∑ j, ‖ψ.ofLp (i, j)‖ ^ 2) = 1 := by
    rw [EuclideanSpace.norm_eq] at hψ
    have h1 : (∑ p, ‖ψ.ofLp p‖ ^ 2) = 1 := by
      rw [← Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), hψ, one_pow]
    rwa [Fintype.sum_prod_type] at h1
  rw [roleState, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), EuclideanSpace.norm_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, roleVec, norm_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0), sum_const_zero, zero_add, add_zero]
  rw [Finset.sum_comm (γ := κ) (α := ι), hsum, show (1 + 1 : ℝ) = 2 by norm_num,
    inv_mul_cancel₀ (by positivity)]

/-- Add the two possible assignments of player roles on disjoint local summands. -/
noncomputable def symmetrize (S : QuantumStrategy Q Q A A ι κ) :
    QuantumStrategy Q Q A A (ι ⊕ κ) (ι ⊕ κ) where
  state := roleState S.state
  norm_state := norm_roleState S.state S.norm_state
  alice q := roleMeasurement (S.alice q) (S.bob q)
  bob q := roleMeasurement (S.alice q) (S.bob q)

theorem symmetrize_bob_eq_alice (S : QuantumStrategy Q Q A A ι κ) :
    S.symmetrize.bob = S.symmetrize.alice := by
  unfold symmetrize
  rfl

theorem symmetrize_state_swap (S : QuantumStrategy Q Q A A ι κ) (i j : ι ⊕ κ) :
    S.symmetrize.state.ofLp (i, j) = S.symmetrize.state.ofLp (j, i) := by
  cases i <;> cases j <;> rfl

theorem symmetrize_isProjective (S : QuantumStrategy Q Q A A ι κ)
    (hA : ∀ q, (S.alice q).toMeasurement.IsProjective)
    (hB : ∀ q, (S.bob q).toMeasurement.IsProjective) (q : Q) :
    (S.symmetrize.alice q).toMeasurement.IsProjective :=
  roleMeasurement_projective _ _ (hA q) (hB q)

omit [DecidableEq ι] [DecidableEq κ] in
private theorem roleVec_mulVec_inl_inr (v : ι × κ → ℂ)
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) (R : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ)
    (i : ι) (j : κ) :
    ((fromBlocks X 0 0 Y ⊗ₖ R) *ᵥ roleVec v) (.inl i, .inr j) =
      ((X ⊗ₖ R.toBlocks₂₂) *ᵥ v) (i, j) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type, roleVec,
    Matrix.toBlocks₂₂]

omit [DecidableEq ι] [DecidableEq κ] in
private theorem roleVec_mulVec_inr_inl (v : ι × κ → ℂ)
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) (R : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ)
    (i : ι) (j : κ) :
    ((fromBlocks X 0 0 Y ⊗ₖ R) *ᵥ roleVec v) (.inr j, .inl i) =
      ((R.toBlocks₁₁ ⊗ₖ Y) *ᵥ v) (i, j) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type, roleVec,
    Matrix.kronecker_apply, Matrix.toBlocks₁₁, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.of_apply, Matrix.zero_apply, zero_mul, mul_zero, sum_const_zero, zero_add, add_zero]
  rw [Finset.sum_comm]
  simp only [mul_comm (Y j _)]

omit [DecidableEq ι] [DecidableEq κ] in
private theorem roleVec_coeff (v : ι × κ → ℂ)
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) (R : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) :
    star (roleVec v) ⬝ᵥ ((fromBlocks X 0 0 Y ⊗ₖ R) *ᵥ roleVec v) =
      star v ⬝ᵥ ((X ⊗ₖ R.toBlocks₂₂) *ᵥ v) +
      star v ⬝ᵥ ((R.toBlocks₁₁ ⊗ₖ Y) *ᵥ v) := by
  simp only [dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type, Pi.star_apply, roleVec,
    star_zero, zero_mul, sum_const_zero, zero_add, add_zero, roleVec_mulVec_inl_inr,
    roleVec_mulVec_inr_inl]
  rw [Finset.sum_comm (γ := κ) (α := ι)]

/-- An observable on the other side of one symmetrized measurement is read through
its two diagonal blocks. Each block contributes half of the corresponding
expectation in the original strategy. -/
theorem symmetrize_expectation (S : QuantumStrategy Q Q A A ι κ) (q : Q) (a : A)
    (R : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) :
    S.symmetrize.toCommuting.state ((S.symmetrize.alice q).effect a ⊗ₖ R) =
      (S.toCommuting.state ((S.alice q).effect a ⊗ₖ R.toBlocks₂₂) +
        S.toCommuting.state (R.toBlocks₁₁ ⊗ₖ (S.bob q).effect a)) / 2 := by
  let t : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have ht : star t * t = 2⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← pow_two,
      ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  change star (t • roleVec S.state.ofLp) ⬝ᵥ
      ((fromBlocks (S.alice q |>.effect a) 0 0 (S.bob q |>.effect a) ⊗ₖ R) *ᵥ
        (t • roleVec S.state.ofLp)) = _
  rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, ht, roleVec_coeff, ← div_eq_inv_mul]
  rfl

/-- The correlation of the symmetrized strategy is the mean of the original
correlation and the correlation obtained by exchanging both players' roles. -/
theorem symmetrize_prob (S : QuantumStrategy Q Q A A ι κ) (x y : Q) (a b : A) :
    S.symmetrize.prob x y a b = (S.prob x y a b + S.prob y x b a) / 2 := by
  have h := congrArg Complex.re (symmetrize_expectation S x a ((S.symmetrize.bob y).effect b))
  simpa only [symmetrize, roleMeasurement, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂,
    toCommuting, AlgState.vector_apply, prob_eq, Complex.div_ofNat_re, Complex.add_re] using h

/-- The agreement between decoded outcomes of the symmetric strategy's question
measurement and a new measurement is the mean of the two original-role
agreements. The new measurement is compressed to each player's original space. -/
theorem symmetrize_agreement {V : Type*} [Fintype V] [DecidableEq V]
    (S : QuantumStrategy Q Q A A ι κ) (q : Q) (G : POVM B (ι ⊕ κ))
    (f : A → V) (g : B → V) :
    Measurement.agreement S.symmetrize.toCommuting.state
        ((S.symmetrize.toCommuting.alice q).map f)
        ((rightMeasurement (ι := ι ⊕ κ) G).map g) =
      (Measurement.agreement S.toCommuting.state ((S.toCommuting.alice q).map f)
          ((rightMeasurement (ι := ι) (G.restrictBasis Function.Embedding.inr)).map g) +
        Measurement.agreement S.toCommuting.state
          ((leftMeasurement (κ := κ) (G.restrictBasis Function.Embedding.inl)).map g)
          ((S.toCommuting.bob q).map f)) / 2 := by
  classical
  let C := S.toCommuting
  let T := S.symmetrize.toCommuting
  let R := rightMeasurement (ι := ι ⊕ κ) G
  let L₀ := leftMeasurement (κ := κ) (G.restrictBasis Function.Embedding.inl)
  let R₀ := rightMeasurement (ι := ι) (G.restrictBasis Function.Embedding.inr)
  have h (a : A) (b : B) :
      (T.state ((T.alice q).effect a * R.effect b)).re =
        ((C.state ((C.alice q).effect a * R₀.effect b)).re +
          (C.state (L₀.effect b * (C.bob q).effect a)).re) / 2 := by
    change (T.state (((S.symmetrize.alice q).effect a ⊗ₖ 1) * (1 ⊗ₖ G.effect b))).re =
      ((C.state (((S.alice q).effect a ⊗ₖ 1) *
          (1 ⊗ₖ (G.restrictBasis Function.Embedding.inr).effect b))).re +
        (C.state ((((G.restrictBasis Function.Embedding.inl).effect b) ⊗ₖ 1) *
          (1 ⊗ₖ (S.bob q).effect a))).re) / 2
    dsimp only [T]
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, symmetrize_expectation]
    simp only [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      POVM.restrictBasis_effect, Complex.div_ofNat_re, Complex.add_re]
    rfl
  change Measurement.agreement T.state ((T.alice q).map f) (R.map g) =
    (Measurement.agreement C.state ((C.alice q).map f) (R₀.map g) +
      Measurement.agreement C.state (L₀.map g) ((C.bob q).map f)) / 2
  simp only [Measurement.agreement_map_map]
  rw [Finset.sum_comm (γ := B) (α := A), ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_add_distrib, sum_div]
  refine sum_congr rfl fun b _ => ?_
  by_cases he : f a = g b
  · simp [he, h]
  · simp [he, Ne.symm he]

end Cslib.PCP.QuantumStrategy

namespace Cslib.PCP.TwoProverGame

open Finset

variable {Q A ι κ : Type*} [Finite Q] [Fintype A]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Exchanging the players' roles does not alter the score in a game with symmetric
questions and a symmetric acceptance predicate. -/
theorem quantumWinProb_symmetrize (G : TwoProverGame Q Q A A)
    (hquestions : ∀ x y, G.questions (y, x) = G.questions (x, y))
    (haccepts : ∀ x y a b, G.accepts y x b a ↔ G.accepts x y a b)
    (S : QuantumStrategy Q Q A A ι κ) :
    G.quantumWinProb S.symmetrize = G.quantumWinProb S := by
  classical
  let _ := Fintype.ofFinite Q
  let score (p : Q → Q → A → A → ℝ) := ∑ x, ∑ y, (G.questions (x, y)).toReal *
    ∑ a, ∑ b, if G.accepts x y a b then p x y a b else 0
  let rev x y a b := S.prob y x b a
  have hrev : score rev = score S.prob := by
    dsimp only [score, rev]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    rw [hquestions, Finset.sum_comm]
    exact congrArg _ (sum_congr rfl fun a _ => sum_congr rfl fun b _ => by rw [haccepts])
  have hmean (x y a b) : (if G.accepts x y a b then S.symmetrize.prob x y a b else 0) =
      (if G.accepts x y a b then S.prob x y a b else 0) / 2 +
        (if G.accepts x y a b then rev x y a b else 0) / 2 := by
    rw [QuantumStrategy.symmetrize_prob]
    split_ifs <;> (try dsimp only [rev]) <;> ring
  rw [quantumWinProb_eq_sum, quantumWinProb_eq_sum]
  simp only [← QuantumStrategy.prob_eq, hmean, sum_add_distrib, mul_add, ← sum_div, ← mul_div_assoc]
  change score S.prob / 2 + score rev / 2 = score S.prob
  rw [hrev]
  ring

end Cslib.PCP.TwoProverGame
