/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.Computability.Circuit.Arithmetic.Permanent.Formula
import CslibFrontier.Computability.Circuit.Arithmetic.Permanent.Projection
import CslibFrontier.Foundations.Data.Matrix.Permanent
import CslibFrontier.Foundations.Data.Matrix.Permanent.Blocks
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Permanent projections of concrete arithmetic formulas and specialization matrices

Ordinary `module` clients of `Formula.isProjection_permanent` and the specialization-matrix
characterization (`IsSubstEntry`, `IsSubstMatrix`,
`isProjection_permanent_iff_exists_isSubstMatrix`):

* `(X₀ + 1) * (X₁ + 2)` has five operation nodes, giving a `6 × 6` permanent projection via
  `Formula.isProjection_permanent`, and also arises directly from an explicit `3 × 3`
  specialization matrix via `isProjection_permanent_iff_exists_isSubstMatrix`.
* `X₀ * X₁` is not a substitution entry and hence not a projection of the `1 × 1` generic
  permanent, exercising the forward direction of `isProjection_permanent_iff_exists_isSubstMatrix`.
* `(X₀ + 2) * (X₀ + X₁)` evaluates to `50` on `(3, 7)` and gives a `5 × 5` projection, padded and
  multiplied to `8 × 8`. Squaring in characteristic two and zero-dimensional boundary cases are
  checked alongside.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PermanentFormulas

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial

private def factored : Formula (arithSignature ℕ) 2 :=
  .gate₂ .mul rfl
    (.gate₂ .add rfl (.input 0) (.gate (.const 1) Fin.elim0))
    (.gate₂ .add rfl (.input 1) (.gate (.const 2) Fin.elim0))

private theorem factored_size : factored.size = 5 := by
  simp [factored]

example : factored.eval (arithInterpretation ℕ) ![3, 4] = 24 := by
  norm_num [factored, Formula.eval, Formula.gate₂, arithInterpretation, arithInterpretationWith]

-- Formula simulation represents `(X₀ + 1) * (X₁ + 2)` as a projection of the `6 × 6` permanent.
example : IsProjection
    ((X 0 + 1) * (X 1 + 2) : MvPolynomial (Fin 2) ℕ)
    (genericMatrix ℕ 6).permanent := by
  have h := factored.isProjection_permanent
  rw [factored_size] at h
  simpa [factored, Formula.eval, Formula.gate₂, arithInterpretationWith, map_ofNat] using h

-- The public specialization-matrix characterization gives a sharper `3 × 3` projection directly.
private noncomputable def factoredMatrix : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 2) ℕ) :=
  !![X 0, 0, 1; 2, X 1, 2; 1, 1, 1]

private theorem isSubstMatrix_factoredMatrix : IsSubstMatrix factoredMatrix := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [factoredMatrix]

example : IsProjection
    ((X 0 + 1) * (X 1 + 2) : MvPolynomial (Fin 2) ℕ)
    (genericMatrix ℕ 3).permanent := by
  refine isProjection_permanent_iff_exists_isSubstMatrix.mpr ⟨factoredMatrix,
    isSubstMatrix_factoredMatrix, ?_⟩
  simp [factoredMatrix, Matrix.permanent_succ_row_zero, Fin.sum_univ_three, Fin.sum_univ_two,
    Fin.succAbove]
  ring

-- Block-diagonal combination on `Fin 2 ⊕ Fin 2` exercises `IsSubstMatrix.fromBlocks` and
-- `IsSubstMatrix.isProjection_permanent` without manual index equivalences.
example : IsProjection
    ((X 0 + 1) * (X 1 + 2) : MvPolynomial (Fin 2) ℕ)
    (genericMatrix ℕ 4).permanent := by
  let M₁ : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 2) ℕ) := !![X 0, 1; 1, 1]
  let M₂ : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 2) ℕ) := !![X 1, 2; 1, 1]
  have hM₁ : IsSubstMatrix M₁ := fun i j => by fin_cases i <;> fin_cases j <;> simp [M₁]
  have hM₂ : IsSubstMatrix M₂ := fun i j => by fin_cases i <;> fin_cases j <;> simp [M₂]
  have hperm : (Matrix.fromBlocks M₁ 0 0 M₂).permanent = (X 0 + 1) * (X 1 + 2) := by
    rw [Matrix.permanent_fromBlocks_zero]
    simp [M₁, M₂, Matrix.permanent_succ_row_zero, Fin.sum_univ_two]
  have h := (hM₁.fromBlocks .zero .zero hM₂).isProjection_permanent
  rwa [hperm] at h

-- Nonvacuity / forward characterization: `X 0 * X 1` is not a single substitution entry, hence
-- not a projection of the `1 × 1` generic permanent.
private theorem not_isSubstEntry_mul : ¬ IsSubstEntry (X 0 * X 1 : MvPolynomial (Fin 2) ℕ) := by
  rintro ⟨s, hs⟩
  rcases s with i | c
  · fin_cases i
    · have h := congrArg (MvPolynomial.eval ![1, 0]) hs
      norm_num at h
    · have h := congrArg (MvPolynomial.eval ![0, 1]) hs
      norm_num at h
  · have h0 := congrArg (MvPolynomial.eval ![0, 0]) hs
    have h1 := congrArg (MvPolynomial.eval ![1, 1]) hs
    norm_num at h0 h1
    omega

example : ¬ IsProjection (X 0 * X 1 : MvPolynomial (Fin 2) ℕ) (genericMatrix ℕ 1).permanent := by
  intro h
  obtain ⟨M, hM, hperm⟩ := isProjection_permanent_iff_exists_isSubstMatrix.mp h
  rw [Matrix.permanent_unique] at hperm
  exact not_isSubstEntry_mul (hperm ▸ hM 0 0)

private def mixed : Formula (arithSignature ℕ) 2 :=
  .gate₂ .mul rfl
    (.gate₂ .add rfl (.input 0) (.gate (.const 2) Fin.elim0))
    (.gate₂ .add rfl (.input 0) (.input 1))

private theorem mixed_size : mixed.size = 4 := by
  simp [mixed]

example : mixed.eval (arithInterpretation ℕ) ![3, 7] = 50 := by
  norm_num [mixed, Formula.eval, Formula.gate₂, arithInterpretation, arithInterpretationWith]

private theorem mixed_projection : IsProjection
    ((X 0 + 2) * (X 0 + X 1) : MvPolynomial (Fin 2) ℕ)
    (genericMatrix ℕ 5).permanent := by
  have h := mixed.isProjection_permanent
  rw [mixed_size] at h
  simpa [mixed, Formula.eval, Formula.gate₂, arithInterpretationWith] using h

-- Multiplicative closure and padding use the same projection API.
example : IsProjection
    (((X 0 + 2) * (X 0 + X 1)) * X 0 : MvPolynomial (Fin 2) ℕ)
    (genericMatrix ℕ 8).permanent := by
  have hx : IsProjection (X (0 : Fin 2) : MvPolynomial (Fin 2) ℕ)
      (genericMatrix ℕ 1).permanent :=
    (Formula.input (σ := arithSignature ℕ) (n := 2) 0).isProjection_permanent
  exact isProjection_permanent_mono (by decide : 5 + 1 ≤ 8) (mixed_projection.permanent_mul hx)

example : IsProjection (mixed.toCircuit.polynomial 0) (genericMatrix ℕ 5).permanent := by
  have h := mixed.isProjection_permanent_toCircuit
  rw [mixed_size] at h
  exact h

private def square : Formula (arithSignature (ZMod 2)) 1 :=
  .gate₂ .mul rfl (.input 0) (.input 0)

example : IsProjection (X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 2))
    (genericMatrix (ZMod 2) 2).permanent := by
  have h := square.isProjection_permanent
  rw [show square.size = 1 by decide] at h
  simpa [square, Formula.eval, Formula.gate₂, arithInterpretationWith, sq] using h

private def constantOnly : Formula (arithSignature ℕ) 0 := .gate (.const 7) Fin.elim0

example : IsProjection (C 7 : MvPolynomial (Fin 0) ℕ) (genericMatrix ℕ 2).permanent := by
  have h := constantOnly.isProjection_permanent
  rw [show constantOnly.size = 1 by decide] at h
  simpa [constantOnly, Formula.eval, arithInterpretationWith] using h

-- The upper-right block can be nonzero: square diagonal blocks still factor.
example : (Matrix.fromBlocks (!![2] : Matrix (Fin 1) (Fin 1) ℕ)
    (!![3, 11] : Matrix (Fin 1) (Fin 2) ℕ) 0 !![2, 3; 5, 7]).permanent = 58 := by
  rw [Matrix.permanent_fromBlocks_zero₂₁, Matrix.permanent_unique,
    Matrix.permanent_succ_row_zero, Fin.sum_univ_two]
  decide

example (A : Matrix (Fin 2) (Fin 2) ℕ) :
    (Matrix.fromBlocks A (0 : Matrix (Fin 2) (Fin 0) ℕ) 0 1).permanent = A.permanent := by
  rw [Matrix.permanent_fromBlocks_zero, Matrix.permanent_one, mul_one]

example : ((!![2, 3; 5, 7] : Matrix (Fin 2) (Fin 2) ℕ).submatrix
    (Equiv.swap 0 1) (Equiv.refl _)).permanent = 29 := by
  rw [Matrix.permanent_submatrix_equiv_equiv, Matrix.permanent_succ_row_zero, Fin.sum_univ_two]
  decide

end CslibFrontierTests.PermanentFormulas
