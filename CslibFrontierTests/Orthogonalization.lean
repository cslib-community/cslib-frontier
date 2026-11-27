/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Quantum.Algebra.Orthogonalization
import CslibFrontier.Foundations.Quantum.Orthogonalization
import CslibFrontier.Foundations.Algebra.BigOperators.Selection
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Polar

/-! # Orthogonalization of measurements

Checked clients of de la Salle's orthogonalization theorem: the `d` largest weights beat every
fractional selection, square matrices have polar decompositions, every measurement on `ℂ^ι` is
`9ε`-close to a projective one in every state, and a projective measurement is recovered exactly
in the state.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Orthogonalization

open Matrix Cslib Cslib.Quantum
open scoped MatrixOrder ComplexOrder

/-- Choosing the two largest of three weights beats the fractional selection `(1, ½, ½)`. -/
example : ∃ S : Finset (Fin 3), S.card = 2 ∧
    ∑ i, ![3, 2, 1] i * ![1, 1 / 2, 1 / 2] i ≤ ∑ i ∈ S, (![3, 2, 1] i : ℝ) :=
  Finset.exists_card_eq_sum_mul_le _ _ (fun i => by fin_cases i <;> norm_num)
    (fun i => by fin_cases i <;> norm_num) (by simp [Fin.sum_univ_three]; norm_num)

/-- Every square matrix is a unitary times a positive semidefinite matrix. -/
example {n : Type} [Fintype n] [DecidableEq n] (y : Matrix n n ℂ) :
    ∃ R ∈ unitaryGroup n ℂ, ∃ h : Matrix n n ℂ, h.PosSemidef ∧ y = R * h := by
  obtain ⟨R, h, hR1, hR2, hh, -, hy, -⟩ := Matrix.exists_polar y rfl
  refine ⟨R, ?_, h, hh, hy⟩
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
  exact hR2

/-- **Orthogonalization**: a measurement with `φ(∑_a M_a²) ≥ 1 - ε` is `9ε`-close to a projective
measurement on the same space, in any state, for instance the vector state of a unit vector. -/
example {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq ι] (M : Measurement α (Matrix ι ι ℂ))
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) {ε : ℝ}
    (hε : 1 - ε ≤ ∑ a, ((AlgState.vector ψ hψ) (M.effect a * M.effect a)).re) :
    ∃ P : Measurement α (Matrix ι ι ℂ), P.IsProjective ∧
      ∑ a, (AlgState.vector ψ hψ).norm (M.effect a - P.effect a) ^ 2 ≤ 9 * ε :=
  Measurement.exists_isProjective_sum_norm_sub_sq_le_of_le _ M hε

/-- A projective measurement has defect `0`, so it is recovered exactly in the state. -/
example {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq ι] (φ : AlgState (Matrix ι ι ℂ))
    (M : Measurement α (Matrix ι ι ℂ)) (hM : M.IsProjective) :
    ∃ P : Measurement α (Matrix ι ι ℂ), P.IsProjective ∧
      ∀ a, φ.norm (M.effect a - P.effect a) = 0 := by
  have hε : 1 - 0 ≤ ∑ a, (φ (M.effect a * M.effect a)).re := by
    have := M.sum_prob φ
    simp only [Measurement.prob] at this
    have hM' : ∀ a, M.effect a * M.effect a = M.effect a := hM
    simp only [hM', sub_zero, this, le_refl]
  obtain ⟨P, hP, h⟩ := Measurement.exists_isProjective_sum_norm_sub_sq_le_of_le φ M hε
  refine ⟨P, hP, fun a => ?_⟩
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => sq_nonneg (φ.norm _)).mp
    (le_antisymm (by simpa using h) (Finset.sum_nonneg fun a _ => sq_nonneg _)) a
    (Finset.mem_univ a)
  exact pow_eq_zero_iff two_ne_zero |>.mp h0

end CslibFrontierTests.Orthogonalization
