/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, matrix characteristic polynomial)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Polynomial.BivariateCoeffNorm1
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Charpoly.TraceExponential

/-!
# Characteristic coefficient norms from power traces

Over the integer polynomial ring, a geometric bound on the norms of the positive power
traces gives the same geometric bound on the reversed characteristic coefficients. In
Newton's identity the scalar on the left cancels the number of terms on the right.
Summing over the ordinary characteristic polynomial bounds its bivariate coefficient norm.

Adapted from `LeanCanny.CountingHierarchy.NewtonMassBounds` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Matrix

open Polynomial
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem coeffNorm1_charpolyRev_coeff_le (M : Matrix ι ι (Polynomial ℤ)) (A : ℕ)
    (ht : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → coeffNorm1 ((M ^ j).trace) ≤ A ^ j)
    (k : ℕ) (hk : k ≤ Fintype.card ι) : coeffNorm1 (M.charpolyRev.coeff k) ≤ A ^ k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    cases k with
    | zero =>
      rw [coeff_zero_eq_eval_zero, eval_charpolyRev, coeffNorm1_one, pow_zero]
    | succ k =>
      have hrec : (k + 1) • M.charpolyRev.coeff (k + 1) =
          -(∑ j ∈ Finset.range (k + 1), M.charpolyRev.coeff (k - j) * (M ^ (j + 1)).trace) := by
        simpa only [nsmul_eq_mul] using charpolyRev_newton M k
      have h : (k + 1) * coeffNorm1 (M.charpolyRev.coeff (k + 1)) ≤ (k + 1) * A ^ (k + 1) := by
        rw [← coeffNorm1_nsmul, hrec, coeffNorm1_neg]
        refine (coeffNorm1_sum_le _ _).trans ?_
        calc
          _ ≤ ∑ _j ∈ Finset.range (k + 1), A ^ (k + 1) := by
            apply Finset.sum_le_sum
            intro j hj
            have hjk := Finset.mem_range.mp hj
            exact (coeffNorm1_mul_le _ _).trans
              ((Nat.mul_le_mul (ih (k - j) (by omega) (by omega))
                (ht (j + 1) (by omega) (by omega))).trans_eq (by rw [← pow_add]; congr 1; omega))
          _ = _ := by simp
      exact Nat.le_of_mul_le_mul_left h (by omega)

/-- The norm of the `k`th characteristic coefficient is at most `A ^ (D - k)` for
`D = card ι` if each positive power trace through `D` has norm at most `A ^ j`. -/
theorem coeffNorm1_charpoly_coeff_le_of_trace_pow (M : Matrix ι ι (Polynomial ℤ)) (A : ℕ)
    (ht : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → coeffNorm1 ((M ^ j).trace) ≤ A ^ j)
    (k : ℕ) : coeffNorm1 (M.charpoly.coeff k) ≤ A ^ (Fintype.card ι - k) := by
  by_cases hk : k ≤ Fintype.card ι
  · have h := coeffNorm1_charpolyRev_coeff_le M A ht _ (Nat.sub_le _ k)
    rw [← reverse_charpoly, coeff_reverse, charpoly_natDegree_eq_dim,
      revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hk] at h
    exact h
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim]; omega), coeffNorm1_zero]
    exact Nat.zero_le _

/-- Bound the full bivariate characteristic polynomial from its positive power traces. -/
theorem bivariateCoeffNorm1_charpoly_le_of_trace_pow (M : Matrix ι ι (Polynomial ℤ))
    {A : ℕ} (hA : 1 ≤ A)
    (ht : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → coeffNorm1 ((M ^ j).trace) ≤ A ^ j) :
    M.charpoly.bivariateCoeffNorm1 ≤ (Fintype.card ι + 1) * A ^ Fintype.card ι := by
  rw [bivariateCoeffNorm1_eq_sum_of_support_subset (S := Finset.range (Fintype.card ι + 1))
    (fun k hk => Finset.mem_range.mpr (Nat.lt_succ_of_le
      (charpoly_natDegree_eq_dim M ▸ le_natDegree_of_mem_supp k hk)))]
  calc
    _ ≤ ∑ _k ∈ Finset.range (Fintype.card ι + 1), A ^ Fintype.card ι :=
      Finset.sum_le_sum fun k _ => (coeffNorm1_charpoly_coeff_le_of_trace_pow M A ht k).trans
        (Nat.pow_le_pow_right hA (Nat.sub_le _ _))
    _ = _ := by simp

end Matrix
