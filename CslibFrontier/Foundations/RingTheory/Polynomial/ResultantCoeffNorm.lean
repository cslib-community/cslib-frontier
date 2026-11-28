/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial resultant)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Polynomial.BivariateCoeffNorm1
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import CslibFrontier.Foundations.LinearAlgebra.Matrix.DeterminantWeight

/-!
# Coefficient norm of a resultant over the integer polynomial ring

The Sylvester determinant bounds the norm of a resultant from coefficient norms. The
derivative-resultant bound uses the bivariate norm and the outer degree of the source
polynomial. Together with `Polynomial.coeffNorm1_eval_C_le`, it bounds the two polynomials
used for parameter exclusion in the real-counting argument.

Adapted from `derivative_resultant_mass_le` in
`LeanCanny.CountingHierarchy.BivariateSpecializationMass` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

/-- A uniform bound on the coefficient norms of both polynomials bounds their resultant. -/
theorem coeffNorm1_resultant_le (P Q : Polynomial (Polynomial ℤ)) {A : ℕ}
    (hP : ∀ k, (P.coeff k).coeffNorm1 ≤ A) (hQ : ∀ k, (Q.coeff k).coeffNorm1 ≤ A) :
    (P.resultant Q).coeffNorm1 ≤
      (P.natDegree + Q.natDegree).factorial * A ^ (P.natDegree + Q.natDegree) := by
  unfold resultant
  have h := Matrix.det_weight_le coeffNorm1_zero coeffNorm1_one.le coeffNorm1_add_le
    coeffNorm1_mul_le coeffNorm1_neg (sylvester P Q P.natDegree Q.natDegree) (A := A) (by
      intro i j
      induction j using Fin.addCases <;>
        simp only [sylvester, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
      · split_ifs
        · exact hQ _
        · exact coeffNorm1_zero ▸ Nat.zero_le _
      · split_ifs
        · exact hP _
        · exact coeffNorm1_zero ▸ Nat.zero_le _)
  rwa [Fintype.card_fin] at h

/-- Bound the derivative resultant in terms of the outer degree and the bivariate coefficient
norm bound. The bound also applies to constant and zero polynomials. -/
theorem coeffNorm1_resultant_derivative_le (P : Polynomial (Polynomial ℤ)) {D H : ℕ}
    (hD : P.natDegree ≤ D) (hH : P.bivariateCoeffNorm1 ≤ H) :
    (P.resultant P.derivative).coeffNorm1 ≤
      (2 * D).factorial * (max 1 (max 1 D * H)) ^ (2 * D) := by
  let A := max 1 (max 1 D * H)
  have hcoeff (k : ℕ) : (P.coeff k).coeffNorm1 ≤ H :=
    (coeffNorm1_coeff_le_bivariateCoeffNorm1 P k).trans hH
  have hP (k : ℕ) : (P.coeff k).coeffNorm1 ≤ A := by
    have hHd : H ≤ max 1 D * H := by
      simpa only [one_mul] using Nat.mul_le_mul_right H (le_max_left 1 D)
    exact (hcoeff k).trans (hHd.trans (le_max_right 1 _))
  have hQ (k : ℕ) : (P.derivative.coeff k).coeffNorm1 ≤ A := by
    have hderiv : P.derivative.coeff k = (k + 1) • P.coeff (k + 1) := by
      rw [coeff_derivative, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm]
    rw [hderiv, coeffNorm1_nsmul]
    by_cases hk : k + 1 ≤ P.natDegree
    · exact (Nat.mul_le_mul ((hk.trans hD).trans (le_max_right 1 D)) (hcoeff _)).trans
        (le_max_right 1 _)
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeffNorm1_zero, mul_zero]
      exact Nat.zero_le _
  have hN : P.natDegree + P.derivative.natDegree ≤ 2 * D := by
    have := natDegree_derivative_le P
    omega
  exact (coeffNorm1_resultant_le P P.derivative hP hQ).trans
    (Nat.mul_le_mul (Nat.factorial_le hN) (Nat.pow_le_pow_right (le_max_left 1 _) hN))

end Polynomial
