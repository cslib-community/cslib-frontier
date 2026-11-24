/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/MvPolynomial/CoeffNorm1.lean`)

public import CslibFrontier.Init

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finsupp.Order
import CslibFrontier.Foundations.Data.MvPolynomial.CoeffSumBounds

/-!
# The coefficient ℓ₁ norm of an integer multivariate polynomial

The sum of absolute coefficients bounds every coefficient, is subadditive and
submultiplicative, and does not increase under variable renaming. A partial derivative
increases it by at most the total degree. These bounds support implicit polynomial
families without storing expanded coefficient lists.

Adapted from [lean-canny’s coefficient-mass development](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/Algebra/MvCoefficientMass.lean).
The name matches the univariate
`Polynomial.coeffNorm1` API; no machine model is involved.

## Main definitions

* `MvPolynomial.coeffNorm1`: sum of the absolute values of all coefficients.

## Main results

* `MvPolynomial.coeffNorm1_add_le`, `MvPolynomial.coeffNorm1_mul_le`:
  triangle inequality and submultiplicativity.
* `MvPolynomial.coeffNorm1_rename_le`, `MvPolynomial.coeffNorm1_pderiv_le`:
  coefficient bounds for renaming and partial differentiation.
-/

public section

namespace MvPolynomial
open scoped BigOperators

variable {ι κ : Type*}

/-- The sum of the absolute values of the integer coefficients. -/
@[expose] noncomputable def coeffNorm1 (p : MvPolynomial ι ℤ) : ℕ :=
  ∑ m ∈ p.support, (p.coeff m).natAbs

/-- The zero polynomial has zero coefficient norm. -/
@[simp] theorem coeffNorm1_zero : coeffNorm1 (0 : MvPolynomial ι ℤ) = 0 := by simp [coeffNorm1]

/-- A monomial has the norm of its coefficient. -/
@[simp] theorem coeffNorm1_monomial (m : ι →₀ ℕ) (a : ℤ) :
    coeffNorm1 (MvPolynomial.monomial m a) = a.natAbs := by
  rw [coeffNorm1, ← MvPolynomial.sum_def]
  exact MvPolynomial.sum_monomial_eq (by simp)

/-- A constant polynomial has the norm of its coefficient. -/
theorem coeffNorm1_C (a : ℤ) :
    coeffNorm1 (MvPolynomial.C a : MvPolynomial ι ℤ) = a.natAbs :=
  coeffNorm1_monomial 0 a

/-- The constant polynomial one has coefficient norm one. -/
@[simp] theorem coeffNorm1_one : coeffNorm1 (1 : MvPolynomial ι ℤ) = 1 := coeffNorm1_C 1

/-- A variable has coefficient norm one. -/
@[simp] theorem coeffNorm1_X (i : ι) :
    coeffNorm1 (MvPolynomial.X i : MvPolynomial ι ℤ) = 1 := coeffNorm1_monomial _ 1

/-- Every coefficient is bounded in absolute value by the coefficient norm. -/
theorem natAbs_coeff_le_coeffNorm1 (p : MvPolynomial ι ℤ) (m : ι →₀ ℕ) :
    (p.coeff m).natAbs ≤ coeffNorm1 p := by
  simpa only [coeffNorm1, MvPolynomial.sum_def] using
    Finsupp.single_eval_le_sum p.coeff (g := Int.natAbs) rfl (fun _ => Nat.zero_le _) m

/-- The coefficient norm may be summed over any finite superset of the support. -/
theorem coeffNorm1_eq_sum_of_support_subset (p : MvPolynomial ι ℤ)
    (s : Finset (ι →₀ ℕ)) (hs : p.support ⊆ s) :
    coeffNorm1 p = ∑ m ∈ s, (p.coeff m).natAbs := by
  simpa only [coeffNorm1, MvPolynomial.sum_def] using
    Finsupp.sum_of_support_subset p.coeff hs (fun _ c => c.natAbs) (by simp)

/-- Multiplication by a natural scalar scales the coefficient norm exactly. -/
theorem coeffNorm1_nsmul (k : ℕ) (p : MvPolynomial ι ℤ) :
    (k • p).coeffNorm1 = k * p.coeffNorm1 := by
  rw [coeffNorm1_eq_sum_of_support_subset (k • p) p.support support_smul,
    coeffNorm1, Finset.mul_sum]
  simp only [nsmul_eq_mul, ← C_eq_natCast, coeff_C_mul, Int.natAbs_mul, Int.natAbs_natCast]

/-- Triangle inequality for the coefficient norm. -/
theorem coeffNorm1_add_le (p q : MvPolynomial ι ℤ) :
    coeffNorm1 (p + q) ≤ coeffNorm1 p + coeffNorm1 q :=
  sum_add_le_of_subadditive Int.natAbs_zero Int.natAbs_add_le p q

/-- Negation preserves the coefficient norm. -/
@[simp] theorem coeffNorm1_neg (p : MvPolynomial ι ℤ) : coeffNorm1 (-p) = coeffNorm1 p := by
  simp [coeffNorm1]

/-- Triangle inequality for a difference. -/
theorem coeffNorm1_sub_le (p q : MvPolynomial ι ℤ) :
    coeffNorm1 (p - q) ≤ coeffNorm1 p + coeffNorm1 q := by
  simpa only [sub_eq_add_neg, coeffNorm1_neg] using coeffNorm1_add_le p (-q)

/-- The coefficient norm of a finite sum is bounded by the sum of the norms. -/
theorem coeffNorm1_sum_le {J : Type*} (s : Finset J) (p : J → MvPolynomial ι ℤ) :
    coeffNorm1 (∑ j ∈ s, p j) ≤ ∑ j ∈ s, coeffNorm1 (p j) :=
  Finset.le_sum_of_subadditive coeffNorm1 coeffNorm1_zero.le coeffNorm1_add_le s p

/-- Submultiplicativity of the coefficient norm. -/
theorem coeffNorm1_mul_le (p q : MvPolynomial ι ℤ) :
    coeffNorm1 (p * q) ≤ coeffNorm1 p * coeffNorm1 q :=
  sum_mul_le_of_submultiplicative Int.natAbs_zero Int.natAbs_add_le
    (fun a b => (Int.natAbs_mul a b).le) p q

/-- Powers satisfy the corresponding coefficient-norm bound. -/
theorem coeffNorm1_pow_le (p : MvPolynomial ι ℤ) (n : ℕ) :
    coeffNorm1 (p ^ n) ≤ coeffNorm1 p ^ n :=
  sum_pow_le_of_submultiplicative Int.natAbs_zero (by decide) Int.natAbs_add_le
    (fun a b => (Int.natAbs_mul a b).le) p n

/-- Finite products satisfy the corresponding coefficient-norm bound. -/
theorem coeffNorm1_prod_le {J : Type*} (s : Finset J) (p : J → MvPolynomial ι ℤ) :
    coeffNorm1 (∏ j ∈ s, p j) ≤ ∏ j ∈ s, coeffNorm1 (p j) :=
  Finset.le_prod_of_submultiplicative coeffNorm1 coeffNorm1_one.le coeffNorm1_mul_le s p

/-- Renaming cannot increase the norm, even when variables merge. -/
theorem coeffNorm1_rename_le (f : ι → κ) (p : MvPolynomial ι ℤ) :
    coeffNorm1 (rename f p) ≤ coeffNorm1 p := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  apply (coeffNorm1_sum_le _ _).trans
  simp only [rename_monomial, coeffNorm1_monomial]
  exact le_rfl

/-- A partial derivative increases the norm by at most the total degree. -/
theorem coeffNorm1_pderiv_le (p : MvPolynomial ι ℤ) (i : ι) :
    coeffNorm1 (pderiv i p) ≤ p.totalDegree * coeffNorm1 p :=
  sum_pderiv_le_of_subadditive Int.natAbs_zero Int.natAbs_add_le p i

end MvPolynomial
