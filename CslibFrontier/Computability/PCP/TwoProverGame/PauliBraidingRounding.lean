/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingLinearity
public import CslibFrontier.Foundations.Quantum.LinearityRounding
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Order
import CslibFrontier.Foundations.Quantum.Algebra.Expect

/-!
# Exactly linear local observables from the Pauli linearity branch

For a tensor-product strategy with projective basis measurements, fix a basis. High
linearity-branch acceptance yields a projective measurement on each player's original
matrix space. Its character observables are close to the averaged consistency
observables in the joint state. The proof rounds the averaged point measurement, then
uses the decoder comparison to pass to the consistency measurement.

## Main results

* `Cslib.PCP.exists_local_charObs_of_pauliBraidingLinearity`: same-space rounding in either basis.
-/

public section

namespace Cslib.PCP

open Quantum BitString Finset
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder Real

/-- The width-independent squared distance budget for the rounded local characters
and the averaged basis observables. -/
noncomputable def pauliBraidingRoundingError (ε : ℝ) : ℝ :=
  96 * (24 * ε + 2 * √(48 * ε)) + 48 * ε

@[simp]
theorem pauliBraidingRoundingError_zero : pauliBraidingRoundingError 0 = 0 := by
  simp [pauliBraidingRoundingError]

variable {n : ℕ} [Nonempty (Fin n)] {ι κ η Q A : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]

omit [Nonempty (Fin n)] in
private theorem observable_pointMeasurement_eq_map [Fintype η] [DecidableEq η]
    (f : Matrix η η ℂ →⋆ₐ[ℂ] Matrix (ι × κ) (ι × κ) ℂ)
    (M : PauliBraidingQuestion n Q → Measurement ((Bool × Bool) ⊕ A) (Matrix η η ℂ))
    (N : PauliBraidingQuestion n Q → Measurement ((Bool × Bool) ⊕ A)
      (Matrix (ι × κ) (ι × κ) ℂ))
    (h : ∀ q a, (N q).effect a = f ((M q).effect a)) (basis : Bool) (c : Fin n → Bool) :
    (pauliBraidingPointMeasurement N basis c).observable =
      f (pauliBraidingPointMeasurement M basis c).observable := by
  simp only [pauliBraidingPointMeasurement, Measurement.observable_average, Finset.expect]
  rw [← NNRat.cast_smul_eq_nnqsmul ℂ, ← NNRat.cast_smul_eq_nnqsmul ℂ, map_smul, map_sum]
  congr 1
  refine sum_congr rfl fun d _ => ?_
  simp only [Measurement.observable, Measurement.map_effect, map_sub, map_sum, h]

private theorem roundPauliSide [Fintype η] [DecidableEq η]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) (Matrix (ι × κ) (ι × κ) ℂ))
    (hA : ∀ basis q, (S.alice (.basis basis q)).IsProjective)
    (hB : ∀ basis q, (S.bob (.basis basis q)).IsProjective)
    (f : Matrix η η ℂ →⋆ₐ[ℂ] Matrix (ι × κ) (ι × κ) ℂ) (hf : Monotone f) (basis roles : Bool)
    (M : PauliBraidingQuestion n Q → Measurement ((Bool × Bool) ⊕ A) (Matrix η η ℂ))
    (hplace : ∀ q a, ((cond roles S.alice S.bob) q).effect a = f ((M q).effect a))
    {ε : ℝ} (hwin : 1 - ε ≤ (pauliBraidingBranchGame n G special decode 0).commutingWinProb S) :
    ∃ P : Measurement (Fin n → Bool) (Matrix η η ℂ), P.IsProjective ∧
      (𝔼 c, S.state.norm ((𝔼 d, pauliBraidingBasisObservable
        (cond roles S.alice S.bob) basis c d) - f (P.charObs c)) ^ 2) ≤
          pauliBraidingRoundingError ε := by
  let R := pauliBraidingLinearityStrategy basis S
  let T := (cond roles R R.swap).asymmetricLinearity
  let L (c : Fin n → Bool) := (pauliBraidingPointMeasurement M basis c).observable
  let B (c : Fin n → Bool) := 𝔼 d, pauliBraidingBasisObservable
    (cond roles S.alice S.bob) basis c d
  have hTstate : T.state = S.state := by
    simp only [T, CommutingStrategy.asymmetricLinearity_state]
    cases roles <;> rfl
  have hL (c : Fin n → Bool) : (T.alice c).observable = f (L c) :=
    (observable_asymmetricLinearity_eq_pointMeasurement S basis roles c).trans
      (observable_pointMeasurement_eq_map f M _ hplace basis c)
  have hTrip := one_sub_le_expect_re_apply_mul_mul_of_pauliBraidingLinearity
    G special decode S hA hB hwin basis roles
  change _ ≤ 𝔼 a, 𝔼 b, (T.state ((T.alice a).observable * (T.alice b).observable *
    (T.alice (a + b)).observable)).re at hTrip
  simp only [hTstate, hL, ← map_mul, ← AlgState.comap_apply S.state f hf] at hTrip
  have hδ : 1 - (24 * ε + 2 * √(48 * ε)) ≤
      𝔼 a, 𝔼 b, ((S.state.comap f hf) (L a * L b * L (a + b))).re := by
    linarith only [hTrip]
  have hself (c : Fin n → Bool) : IsSelfAdjoint (L c) :=
    (pauliBraidingPointMeasurement M basis c).isSelfAdjoint_observable
  have hcon (c : Fin n → Bool) : L c * L c ≤ 1 := by
    have h := (pauliBraidingPointMeasurement M basis c).star_observable_mul_self_le_one
    change star (L c) * L c ≤ 1 at h
    rwa [(hself c).star_eq] at h
  obtain ⟨P, hP, _, _, hround⟩ :=
    exists_isProjective_charObs_of_linear_contractions (S.state.comap f hf) L hself hcon hδ
  simp only [AlgState.norm_comap, map_sub, ← hL] at hround
  have hdec := expect_norm_asymmetricLinearity_sub_basis_sq_le G special decode S basis roles
  change (𝔼 c, S.state.norm ((T.alice c).observable - B c) ^ 2) ≤ _ at hdec
  have hε : 0 ≤ ε := by
    have h := SeededGame.answersWinProb_le_one (pauliBraidingBranchGame n G special decode 0)
      S.answers
    change (pauliBraidingBranchGame n G special decode 0).commutingWinProb S ≤ 1 at h
    linarith only [h, hwin]
  have hdec' : (𝔼 c, S.state.norm ((T.alice c).observable - B c) ^ 2) ≤ 24 * ε := by
    refine hdec.trans ?_
    cases basis
    · simp only [Bool.false_eq_true, ite_false]
      positivity
    · simp only [ite_true]
      have hsize : (2 : ℝ) ≤ Fintype.card (Fin n → Bool) := by
        exact_mod_cast Nat.succ_le_of_lt (Fintype.one_lt_card (α := Fin n → Bool))
      have hreject : 0 ≤ 1 - (pauliBraidingBranchGame n G special decode 0).commutingWinProb S :=
        sub_nonneg.mpr (SeededGame.answersWinProb_le_one _ S.answers)
      have hweight : (48 : ℝ) / Fintype.card (Fin n → Bool) ≤ 24 := by
        apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hsize)).mpr
        linarith only [hsize]
      exact (mul_le_mul_of_nonneg_right hweight hreject).trans
        (mul_le_mul_of_nonneg_left (by linarith only [hwin]) (by norm_num))
  refine ⟨P, hP, ?_⟩
  change (𝔼 c, S.state.norm (B c - f (P.charObs c)) ^ 2) ≤ _
  have h := S.state.expect_norm_sub_sq_le_through univ B
    (fun c => (T.alice c).observable) (fun c => f (P.charObs c))
  simp only [S.state.norm_sub_comm (B _) (T.alice _).observable] at h
  unfold pauliBraidingRoundingError
  linarith only [h, hdec', hround]

/-- The linearity branch rounds each player's averaged consistency observables in a fixed basis
to exactly linear unitary characters on their respective original matrix spaces. -/
theorem exists_local_charObs_of_pauliBraidingLinearity
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (S : QuantumStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) ι κ)
    (hA : ∀ basis q, ((S.alice (.basis basis q)).toMeasurement).IsProjective)
    (hB : ∀ basis q, ((S.bob (.basis basis q)).toMeasurement).IsProjective)
    (basis : Bool) {ε : ℝ}
    (hwin : 1 - ε ≤ (pauliBraidingBranchGame n G special decode 0).quantumWinProb S) :
    let T := S.toCommuting
    ∃ (P : Measurement (Fin n → Bool) (Matrix ι ι ℂ))
      (R : Measurement (Fin n → Bool) (Matrix κ κ ℂ)), P.IsProjective ∧ R.IsProjective ∧
      (𝔼 c, T.state.norm ((𝔼 d, pauliBraidingBasisObservable T.alice basis c d) -
        kroneckerOne (P.charObs c)) ^ 2) ≤ pauliBraidingRoundingError ε ∧
      (𝔼 c, T.state.norm ((𝔼 d, pauliBraidingBasisObservable T.bob basis c d) -
        oneKronecker (R.charObs c)) ^ 2) ≤ pauliBraidingRoundingError ε := by
  intro T
  have hplaceA (q : PauliBraidingQuestion n Q) (a : (Bool × Bool) ⊕ A) :
      (T.alice q).effect a = kroneckerOne ((S.alice q).toMeasurement.effect a) := rfl
  have hplaceB (q : PauliBraidingQuestion n Q) (a : (Bool × Bool) ⊕ A) :
      (T.bob q).effect a = oneKronecker ((S.bob q).toMeasurement.effect a) := rfl
  have hAlift (basis : Bool) (q : (Fin n → Bool) × (Fin n → Bool)) :
      (T.alice (.basis basis q)).IsProjective := fun a => by
    rw [hplaceA, ← map_mul, hA basis q a]
  have hBlift (basis : Bool) (q : (Fin n → Bool) × (Fin n → Bool)) :
      (T.bob (.basis basis q)).IsProjective := fun a => by
    rw [hplaceB, ← map_mul, hB basis q a]
  have hscore : 1 - ε ≤ (pauliBraidingBranchGame n G special decode 0).commutingWinProb T := by
    simpa only [T, SeededGame.commutingWinProb_toCommuting] using hwin
  obtain ⟨P, hP, hPc⟩ := roundPauliSide G special decode T hAlift hBlift kroneckerOne
    (OrderHomClass.mono _) basis true (fun q => (S.alice q).toMeasurement) hplaceA hscore
  obtain ⟨R, hR, hRc⟩ := roundPauliSide G special decode T hAlift hBlift oneKronecker
    (OrderHomClass.mono _) basis false (fun q => (S.bob q).toMeasurement) hplaceB hscore
  exact ⟨P, R, hP, hR, hPc, hRc⟩

end Cslib.PCP
