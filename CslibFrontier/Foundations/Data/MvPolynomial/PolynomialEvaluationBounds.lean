/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial evaluation)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.CoeffNorm1
public import CslibFrontier.Foundations.Data.Polynomial.CoeffNorm1
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Bounds for evaluating a polynomial at a multivariate polynomial

The degree of the outer polynomial controls the degree and coefficient norm after
evaluation. Adapted from `PolynomialMultivariateCompositionBounds` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

open scoped BigOperators

/-- The degree of a univariate polynomial times the total degree of its argument bounds the
total degree after evaluation. -/
theorem totalDegree_aeval_mvPolynomial_le {ι R : Type*} [CommRing R]
    (p : Polynomial R) (v : MvPolynomial ι R) :
    (aeval v p).totalDegree ≤ p.natDegree * v.totalDegree := by
  rw [aeval_def, MvPolynomial.algebraMap_eq, eval₂_eq_sum, sum_def]
  refine MvPolynomial.totalDegree_finsetSum_le fun i hi => ?_
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_pow _ _).trans
    (Nat.mul_le_mul_right _ (le_natDegree_of_mem_supp i hi))

/-- Evaluating an integer polynomial at a multivariate polynomial of coefficient norm at most
`M` costs a factor of at most `M ^ p.natDegree` in coefficient norm, for `M ≥ 1`. -/
theorem coeffNorm1_aeval_mvPolynomial_le {ι : Type*}
    (p : Polynomial ℤ) (v : MvPolynomial ι ℤ) {M : ℕ} (hM : 1 ≤ M)
    (hv : v.coeffNorm1 ≤ M) :
    (aeval v p).coeffNorm1 ≤ p.coeffNorm1 * M ^ p.natDegree := by
  rw [aeval_def, MvPolynomial.algebraMap_eq, eval₂_eq_sum, sum_def]
  refine (MvPolynomial.coeffNorm1_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ p.support, (p.coeff i).natAbs * M ^ p.natDegree := by
      refine Finset.sum_le_sum fun i hi => (MvPolynomial.coeffNorm1_mul_le _ _).trans ?_
      rw [MvPolynomial.coeffNorm1_C]
      exact Nat.mul_le_mul_left _ ((MvPolynomial.coeffNorm1_pow_le v i).trans
        ((Nat.pow_le_pow_left hv i).trans
          (Nat.pow_le_pow_right hM (le_natDegree_of_mem_supp i hi))))
    _ = _ := by rw [coeffNorm1, Finset.sum_mul]

end Polynomial
