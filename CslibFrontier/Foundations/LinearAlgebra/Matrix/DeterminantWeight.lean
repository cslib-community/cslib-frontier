/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, determinant bounds)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Determinant bounds from weights on the entries -/

public section

namespace Matrix

/-- A subadditive, submultiplicative weight that is invariant under negation bounds the
determinant by the number of permutations times the uniform bound on each product. -/
theorem det_weight_le {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    {w : R → ℕ} (hzero : w 0 = 0) (hone : w 1 ≤ 1)
    (hadd : ∀ a b, w (a + b) ≤ w a + w b) (hmul : ∀ a b, w (a * b) ≤ w a * w b)
    (hneg : ∀ a, w (-a) = w a) (M : Matrix ι ι R) {A : ℕ} (hM : ∀ i j, w (M i j) ≤ A) :
    w M.det ≤ (Fintype.card ι).factorial * A ^ Fintype.card ι := by
  rw [det_apply]
  refine (Finset.le_sum_of_subadditive w hzero.le hadd _ _).trans ?_
  calc
    _ ≤ ∑ _σ : Equiv.Perm ι, A ^ Fintype.card ι := by
      apply Finset.sum_le_sum
      intro σ _
      have hsign (a : R) : w (Equiv.Perm.sign σ • a) = w a := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · rw [h, one_smul]
        · rw [h, Units.neg_smul, one_smul, hneg]
      rw [hsign]
      refine (Finset.le_prod_of_submultiplicative w hone hmul _ _).trans ?_
      simpa only [Finset.prod_const, Finset.card_univ] using
        (Finset.prod_le_prod fun i _ => hM (σ i) i :
          (∏ i, w (M (σ i) i)) ≤ ∏ _i : ι, A)
    _ = _ := by simp [Fintype.card_perm]

end Matrix
