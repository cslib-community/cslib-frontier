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

A geometric bound on the weights of the positive power traces gives the same
geometric bound on the reversed characteristic coefficients. In Newton's identity the
natural scalar on the left cancels the number of terms on the right. The proof applies
to subadditive, submultiplicative weights that respect negation and natural scaling,
including the coefficient norm over univariate and multivariate integer polynomial rings.

Adapted from `LeanCanny.CountingHierarchy.NewtonMassBounds` and
`LeanCanny.CountingHierarchy.MultivariateNewtonMass` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Matrix

open Polynomial
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem charpoly_natDegree_le_card {S : Type*} [CommRing S] (M : Matrix ι ι S) :
    M.charpoly.natDegree ≤ Fintype.card ι := by
  nontriviality S
  exact (charpoly_natDegree_eq_dim M).le

private theorem weight_charpolyRev_coeff_le {S : Type*} [CommRing S] {w : S → ℕ}
    (hzero : w 0 = 0) (hone : w 1 ≤ 1)
    (hadd : ∀ a b, w (a + b) ≤ w a + w b) (hmul : ∀ a b, w (a * b) ≤ w a * w b)
    (hneg : ∀ a, w (-a) = w a) (hnsmul : ∀ (j : ℕ) a, w (j • a) = j * w a)
    (M : Matrix ι ι S) (A : ℕ)
    (ht : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → w ((M ^ j).trace) ≤ A ^ j)
    (k : ℕ) (hk : k ≤ Fintype.card ι) : w (M.charpolyRev.coeff k) ≤ A ^ k := by
  cases k with
  | zero =>
    rwa [coeff_zero_eq_eval_zero, eval_charpolyRev, pow_zero]
  | succ k =>
    have hrec : (k + 1) • M.charpolyRev.coeff (k + 1) =
        -(∑ j ∈ Finset.range (k + 1), M.charpolyRev.coeff (k - j) * (M ^ (j + 1)).trace) := by
      simpa only [nsmul_eq_mul] using charpolyRev_newton M k
    have h : (k + 1) * w (M.charpolyRev.coeff (k + 1)) ≤ (k + 1) * A ^ (k + 1) := by
      rw [← hnsmul, hrec, hneg]
      refine (Finset.le_sum_of_subadditive w hzero.le hadd _ _).trans ?_
      calc
        _ ≤ ∑ _j ∈ Finset.range (k + 1), A ^ (k + 1) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjk := Finset.mem_range.mp hj
          have hprev := weight_charpolyRev_coeff_le hzero hone hadd hmul hneg hnsmul
            M A ht (k - j) (by omega)
          exact (hmul _ _).trans
            ((Nat.mul_le_mul hprev
              (ht (j + 1) (by omega) (by omega))).trans_eq (by rw [← pow_add]; congr 1; omega))
        _ = _ := by simp
    exact Nat.le_of_mul_le_mul_left h (by omega)
termination_by k

/-- When each positive power trace through the matrix dimension `D` has weight at most
`A ^ j`, the `k`th characteristic coefficient has weight at most `A ^ (D - k)`. -/
theorem weight_charpoly_coeff_le_of_trace_pow {S : Type*} [CommRing S] {w : S → ℕ}
    (hzero : w 0 = 0) (hone : w 1 ≤ 1)
    (hadd : ∀ a b, w (a + b) ≤ w a + w b) (hmul : ∀ a b, w (a * b) ≤ w a * w b)
    (hneg : ∀ a, w (-a) = w a) (hnsmul : ∀ (j : ℕ) a, w (j • a) = j * w a)
    (M : Matrix ι ι S) (A : ℕ)
    (ht : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → w ((M ^ j).trace) ≤ A ^ j)
    (k : ℕ) : w (M.charpoly.coeff k) ≤ A ^ (Fintype.card ι - k) := by
  by_cases hk : k ≤ Fintype.card ι
  · rw [← coeff_charpolyRev_card_sub M k hk]
    exact weight_charpolyRev_coeff_le hzero hone hadd hmul hneg hnsmul M A ht _ (Nat.sub_le _ k)
  · rw [coeff_eq_zero_of_natDegree_lt ((charpoly_natDegree_le_card M).trans_lt (by omega)),
      hzero]
    exact Nat.zero_le _

/-- Sum the characteristic coefficient weights using a geometric bound on the power traces. -/
theorem sum_charpoly_coeff_le_of_trace_pow {S : Type*} [CommRing S] {w : S → ℕ}
    (hzero : w 0 = 0) (hone : w 1 ≤ 1)
    (hadd : ∀ a b, w (a + b) ≤ w a + w b) (hmul : ∀ a b, w (a * b) ≤ w a * w b)
    (hneg : ∀ a, w (-a) = w a) (hnsmul : ∀ (j : ℕ) a, w (j • a) = j * w a)
    (M : Matrix ι ι S) {A : ℕ} (hA : 1 ≤ A)
    (ht : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → w ((M ^ j).trace) ≤ A ^ j) :
    M.charpoly.sum (fun _ a => w a) ≤ (Fintype.card ι + 1) * A ^ Fintype.card ι := by
  rw [Polynomial.sum_eq_of_subset _ (fun _ => hzero)
    (s := Finset.range (Fintype.card ι + 1)) (fun k hk => Finset.mem_range.mpr (Nat.lt_succ_of_le
      ((le_natDegree_of_mem_supp k hk).trans (charpoly_natDegree_le_card M))))]
  calc
    _ ≤ ∑ _k ∈ Finset.range (Fintype.card ι + 1), A ^ Fintype.card ι :=
      Finset.sum_le_sum fun k _ =>
        (weight_charpoly_coeff_le_of_trace_pow hzero hone hadd hmul hneg hnsmul M A ht k).trans
          (Nat.pow_le_pow_right hA (Nat.sub_le _ _))
    _ = _ := by simp

/-- The norm of the `k`th characteristic coefficient is at most `A ^ (D - k)` for
`D = card ι` if each positive power trace through `D` has norm at most `A ^ j`. -/
theorem coeffNorm1_charpoly_coeff_le_of_trace_pow (M : Matrix ι ι (Polynomial ℤ)) (A : ℕ)
    (ht : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → coeffNorm1 ((M ^ j).trace) ≤ A ^ j)
    (k : ℕ) : coeffNorm1 (M.charpoly.coeff k) ≤ A ^ (Fintype.card ι - k) :=
  weight_charpoly_coeff_le_of_trace_pow coeffNorm1_zero coeffNorm1_one.le coeffNorm1_add_le
    coeffNorm1_mul_le coeffNorm1_neg coeffNorm1_nsmul M A ht k

/-- Bound the full bivariate characteristic polynomial from its positive power traces. -/
theorem bivariateCoeffNorm1_charpoly_le_of_trace_pow (M : Matrix ι ι (Polynomial ℤ))
    {A : ℕ} (hA : 1 ≤ A)
    (ht : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → coeffNorm1 ((M ^ j).trace) ≤ A ^ j) :
    M.charpoly.bivariateCoeffNorm1 ≤ (Fintype.card ι + 1) * A ^ Fintype.card ι :=
  sum_charpoly_coeff_le_of_trace_pow coeffNorm1_zero coeffNorm1_one.le coeffNorm1_add_le
    coeffNorm1_mul_le coeffNorm1_neg coeffNorm1_nsmul M hA ht

end Matrix
