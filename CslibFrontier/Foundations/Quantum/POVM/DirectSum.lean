/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.POVM
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block

/-!
# Direct sums of measurements

Two POVMs with the same outcomes can act block diagonally on a direct sum of systems.
If their effects are projections, so are the effects of the direct sum.
-/

public section

open Matrix Finset
open scoped MatrixOrder ComplexOrder

namespace Cslib.Quantum.POVM

variable {A ι κ : Type*} [Fintype A] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A measurement that acts as `M` and `N` on the two summands. -/
noncomputable def directSum (M : POVM A ι) (N : POVM A κ) : POVM A (ι ⊕ κ) where
  effect a := fromBlocks (M.effect a) 0 0 (N.effect a)
  posSemidef a := by
    obtain ⟨U, hU⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (M.posSemidef a).nonneg
    obtain ⟨V, hV⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (N.posSemidef a).nonneg
    have h := posSemidef_conjTranspose_mul_self (fromBlocks U 0 0 V)
    rw [fromBlocks_conjTranspose, conjTranspose_zero, conjTranspose_zero, fromBlocks_multiply]
      at h
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero] at h
    rw [star_eq_conjTranspose] at hU hV
    rwa [← hU, ← hV] at h
  sum_effect := by
    have h : ∑ a, fromBlocks (M.effect a) 0 0 (N.effect a) =
        fromBlocks (∑ a, M.effect a) 0 0 (∑ a, N.effect a) := by
      ext (i | i) (j | j) <;> simp [Matrix.sum_apply]
    rw [h, M.sum_effect, N.sum_effect, fromBlocks_one]

@[simp] theorem directSum_effect (M : POVM A ι) (N : POVM A κ) (a : A) :
    (M.directSum N).effect a = fromBlocks (M.effect a) 0 0 (N.effect a) := by
  unfold directSum
  rfl

theorem directSum_effect_mul_self (M : POVM A ι) (N : POVM A κ) (a : A)
    (hM : M.effect a * M.effect a = M.effect a) (hN : N.effect a * N.effect a = N.effect a) :
    (M.directSum N).effect a * (M.directSum N).effect a = (M.directSum N).effect a := by
  simp only [directSum_effect, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, hM, hN]

end Cslib.Quantum.POVM
