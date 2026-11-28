/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, beside `Mathlib/LinearAlgebra/Matrix/Farkas.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Abel

/-!
# Nonnegative equality form of a linear inequality system

`Matrix.nonnegForm A = [A, -A, I]` replaces unrestricted variables by positive and negative
parts and inequalities by equalities with nonnegative slack variables. The transformation
works over ordered rings, including the integers, without division.
-/

public section

namespace Matrix

variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [Ring R]

/-- The matrix `[A, -A, I]`, with columns for positive parts, negative parts, and slacks. -/
@[expose] def nonnegForm (A : Matrix m n R) : Matrix m (n ⊕ n ⊕ m) R :=
  fromCols A (fromCols (-A) 1)

/-- Multiplication by `[A, -A, I]` subtracts the two variable blocks and adds the slack block. -/
theorem nonnegForm_mulVec (A : Matrix m n R) (z : n ⊕ n ⊕ m → R) :
    nonnegForm A *ᵥ z = A *ᵥ (fun j => z (.inl j) - z (.inr (.inl j))) +
      (fun i => z (.inr (.inr i))) := by
  ext i
  simp only [nonnegForm, mulVec, dotProduct, Fintype.sum_sum_type, fromCols_apply_inl,
    fromCols_apply_inr, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib,
    Matrix.one_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_sub,
    Finset.sum_sub_distrib, Pi.add_apply]
  abel

omit [Fintype m] [Fintype n] in
/-- Changing coefficients by a ring homomorphism commutes with the nonnegative-form matrix. -/
theorem nonnegForm_map {S : Type*} [Ring S] (A : Matrix m n R) (f : R →+* S) :
    (nonnegForm A).map f = nonnegForm (A.map f) := by
  ext i j
  rcases j with j | j | i'
  · rfl
  · simp [nonnegForm]
  · simp only [nonnegForm, fromCols_apply_inr, Matrix.one_apply, map_apply]
    split_ifs <;> simp

omit [Fintype m] [Fintype n] in
/-- The split-variable and slack transformation increases an integer entry bound by at most one. -/
theorem abs_nonnegForm_le {A : Matrix m n ℤ} {B : ℕ} (hA : ∀ i j, |A i j| ≤ B) :
    ∀ i j, |nonnegForm A i j| ≤ (B + 1 : ℕ) := by
  intro i j
  rcases j with j | j | i'
  · exact (hA i j).trans (by simp)
  · simpa only [nonnegForm, fromCols_apply_inr, fromCols_apply_inl, Matrix.neg_apply, abs_neg]
      using (hA i j).trans (by simp : (B : ℤ) ≤ (B + 1 : ℕ))
  · simp only [nonnegForm, fromCols_apply_inr, Matrix.one_apply]
    split_ifs <;> simp
    omega

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- An inequality solution yields a nonnegative equality solution by splitting variables
into positive and negative parts and introducing the residual as slack. -/
theorem nonnegForm_solution {A : Matrix m n R} {b : m → R} {x : n → R}
    (hx : A *ᵥ x ≤ b) :
    ∃ z : n ⊕ n ⊕ m → R, 0 ≤ z ∧ nonnegForm A *ᵥ z = b := by
  let z : n ⊕ n ⊕ m → R := Sum.elim (fun j => max (x j) 0)
    (Sum.elim (fun j => max (-x j) 0) (fun i => b i - (A *ᵥ x) i))
  refine ⟨z, ?_, ?_⟩
  · intro j
    rcases j with j | j | i
    · exact le_max_right _ _
    · exact le_max_right _ _
    · exact sub_nonneg.mpr (hx i)
  · rw [nonnegForm_mulVec]
    have hsplit : (fun j => z (.inl j) - z (.inr (.inl j))) = x :=
      funext fun j => max_zero_sub_max_neg_zero_eq_self (x j)
    rw [hsplit]
    ext i
    change (A *ᵥ x) i + (b i - (A *ᵥ x) i) = b i
    abel

end Matrix
