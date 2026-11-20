/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Quantum.Algebra.CompletedMeasurement
import CslibFrontierTests.QubitMeasurementFixture

/-! # An interior coordinate of a sequential projective measurement -/

set_option linter.privateModule false

open Cslib.Quantum Cslib.Quantum.Measurement
open scoped ComplexOrder BigOperators

private def instructions (j : Fin 3) : Cslib.Quantum.Measurement Bool ℂ :=
  const (j == 1)

private theorem projective (j : Fin 3) : (instructions j).IsProjective :=
  isProjective_const _

/-- In the sequence false, true, false, keeping just the middle outcome
gives the full effect for true. -/
example :
    (∑ g : Fin 3 → Bool, if g 1 = true then
      (sequentialProjective instructions projective).effect g else 0) = 1 := by
  rw [sequentialProjective_marginal]
  have h : (instructions 1).effect true = 1 := by simp [instructions, const]
  simp only [h, mul_one]
  exact sum_transcriptProduct_mul_star _ (fun _ => projective _)

/-- The complementary outcome at the same position has zero effect. -/
example :
    (∑ g : Fin 3 → Bool, if g 1 = false then
      (sequentialProjective instructions projective).effect g else 0) = 0 := by
  rw [sequentialProjective_marginal]
  have h : (instructions 1).effect false = 0 := by simp [instructions, const]
  simp [h]


private noncomputable def scalarState : AlgState ℂ where
  toFun z := z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  monotone' _ _ h := h
  map_one' := rfl

/-- A two-measurement prefix has zero average commutator defect in the scalar strategy.
The measured outcomes depend on the sampled questions. -/
example :
    (𝔼 x : Fin 3 → Fin 3,
      prefixCommutatorDefect scalarState (instructions ∘ x) (2 : Fin 3)) = 0 := by
  apply le_antisymm
  · have hp (x y : Fin 3) :
        pairCommutatorDefect scalarState (instructions x) (instructions y) = 0 :=
      pairCommutatorDefect_eq_zero _ _ _ fun _ _ => Commute.all _ _
    have h := average_prefixCommutatorDefect_le scalarState instructions instructions
      projective projective (fun _ _ _ _ => Commute.all _ _) (2 : Fin 3)
      (χ := 0) (ζ := 0) (by simp [hp]) (by simp)
    simpa using h
  · exact Finset.expect_nonneg fun _ _ => prefixCommutatorDefect_nonneg _ _ _


private def certainSuccess : Measurement (Option Bool) ℂ := const (some true)
private def certainFailure : Measurement (Option Bool) ℂ := const none

/-- The successful part contributes one unit of discrepancy, and the failure effect
contributes a second unit. The factor two in the completion bound is attained. -/
example : successfulCopyDefect scalarState certainSuccess certainFailure = 1 ∧
    copyDefect scalarState certainSuccess certainFailure = 2 := by
  unfold successfulCopyDefect copyDefect
  norm_num [certainSuccess, certainFailure, const, Fintype.sum_option, AlgState.norm_one,
    AlgState.norm_neg]

open Cslib.Quantum Finset Matrix CslibFrontierTests.QubitMeasurementFixture
open scoped MatrixOrder Matrix.Norms.L2Operator Real

section Qubit

private noncomputable def D :=
  binary diagonalProjection diagonalProjection_star diagonalProjection_sq
private noncomputable def U := binary uniformProjection uniformProjection_star uniformProjection_sq
private noncomputable def qubitSequence : Fin 2 → Measurement Bool Mat := ![U, D]

private theorem qubitSequence_projective : ∀ j, (qubitSequence j).IsProjective :=
  pair_projective U D (binary_projective _ _ _) (binary_projective _ _ _)

private def W (a : Bool) : Mat := if a then 1 else 0

private def boolWord : (Fin 1 → Bool) ≃ Bool where
  toFun f := f 0
  invFun b _ := b
  left_inv f := funext fun i => congrArg f (Subsingleton.elim 0 i)
  right_inv _ := rfl

private theorem weighted_score :
    (∑ g : Fin 2 → Bool, (φ ((Measurement.sequentialProjective qubitSequence
      qubitSequence_projective).effect g * W (g 1))).re) = 1 / 2 := by
  have hterm (g : Fin 2 → Bool) : (Measurement.sequentialProjective qubitSequence
      qubitSequence_projective).effect g =
      U.effect (g 0) * D.effect (g 1) * U.effect (g 0) := by
    rw [Measurement.sequentialProjective_effect_succ, Measurement.sequentialProjective_effect_one]
    rfl
  simp only [hterm]
  rw [← (Fin.consEquiv (fun _ : Fin 2 => Bool)).sum_comp, Fintype.sum_prod_type]
  have ht (a : Bool) (g : Fin 1 → Bool) :
      (Fin.consEquiv (fun _ : Fin 2 => Bool) (a, g)) 1 = g 0 := rfl
  simp only [ht]
  simp only [Fin.consEquiv_apply, Fin.cons_zero]
  simp_rw [← boolWord.symm.sum_comp]
  simp only [boolWord, Equiv.symm_mk, Equiv.coe_fn_mk, Fintype.sum_bool]
  norm_num [U, D, W, binary, φ, AlgState.vector_apply, basisVector, EuclideanSpace.single,
    Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    uniformProjection, diagonalProjection, Matrix.one_apply]

private theorem isolated_score :
    (∑ a : Bool, (φ ((qubitSequence 1).effect a * W a)).re) = 0 := by
  norm_num [qubitSequence, D, W, binary, φ, AlgState.vector_apply, basisVector,
    EuclideanSpace.single, Matrix.mulVec, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, Fintype.sum_bool, diagonalProjection]

private theorem prefix_defect_eq_pair :
    Measurement.prefixCommutatorDefect φ qubitSequence 1 =
      Measurement.pairCommutatorDefect φ D U := by
  have h (p : Fin 1 → Bool) :
      Measurement.transcriptProduct (Measurement.before qubitSequence 1) p =
        U.effect (p 0) := by
    rw [Measurement.transcriptProduct_succ, Measurement.transcriptProduct_zero, mul_one]
    rfl
  unfold Measurement.prefixCommutatorDefect Measurement.transcriptCommutatorDefect
    Measurement.pairCommutatorDefect
  change (∑ a : Bool, ∑ p : Fin 1 → Bool, _) = _
  simp only [h, (U.nonneg _).isSelfAdjoint.star_eq]
  simp_rw [← boolWord.symm.sum_comp]
  rfl

private theorem pair_defect : Measurement.pairCommutatorDefect φ D U = 1 := by
  norm_num [Measurement.pairCommutatorDefect, U, D, binary, AlgState.norm_sq, φ,
    AlgState.vector_apply, basisVector, EuclideanSpace.single, Matrix.star_apply, Matrix.mul_apply,
    Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Fintype.sum_bool, uniformProjection,
    diagonalProjection, Matrix.one_apply]

/-- The exposed formulas compute a nonzero algebraic commutator and a nonzero copy error. -/
example : Measurement.pairCommutatorDefect φ D U = 1 ∧
    Measurement.copyDefect φ D (Measurement.const true) = 2 := by
  refine ⟨pair_defect, ?_⟩
  norm_num [Measurement.copyDefect, D, Measurement.const, binary, AlgState.norm_sq, φ,
    AlgState.vector_apply, basisVector, EuclideanSpace.single, Matrix.star_apply, Matrix.mul_apply,
    Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Fintype.sum_bool,
    diagonalProjection,
    Matrix.one_apply]

/-- In the second measurement the selected score increases from zero to one half.
The theorem applies with a nonzero prefix commutator defect. -/
example : (1 / 2 : ℝ) ≤ 0 + 2 * √1 := by
  have h := Measurement.sequentialProjective_weighted_le φ qubitSequence qubitSequence_projective
    1 W (fun a => by cases a <;> simp [W])
    (fun _ _ a => by
      cases a
      · exact Commute.zero_right _
      · exact Commute.one_right _)
  rw [weighted_score, isolated_score, prefix_defect_eq_pair, pair_defect] at h
  exact h

end Qubit
