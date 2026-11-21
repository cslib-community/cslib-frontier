/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial coefficient norms)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.CoeffNorm1
public import CslibFrontier.Foundations.Data.Polynomial.CoeffNorm1
import CslibFrontier.Foundations.Data.MvPolynomial.CoeffSumBounds

/-!
# Coefficient norm with one integer polynomial parameter

Sum the ordinary integer polynomial coefficient norms over the outer monomials. This gives
arithmetic bounds used in the pure-power residue estimate. Constant promotion preserves the
integer multivariate coefficient norm.

Adapted from `LeanCanny.CountingHierarchy.ParameterMass` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial.ParameterCoeffNorm

open MvPolynomial
open scoped BigOperators

variable {ι : Type*}

/-- Sum the integer coefficient norms of the outer polynomial's coefficients. -/
@[expose] noncomputable def norm (p : MvPolynomial ι (Polynomial ℤ)) : ℕ :=
  ∑ m ∈ p.support, Polynomial.coeffNorm1 (p.coeff m)

/-- The zero polynomial has norm zero. -/
@[simp] theorem zero : norm (0 : MvPolynomial ι (Polynomial ℤ)) = 0 := by simp [norm]

/-- A monomial has the norm of its coefficient. -/
@[simp] theorem monomial (m : ι →₀ ℕ) (a : Polynomial ℤ) :
    norm (MvPolynomial.monomial m a) = Polynomial.coeffNorm1 a := by
  rw [norm, ← MvPolynomial.sum_def]
  exact MvPolynomial.sum_monomial_eq (by simp)

/-- A constant has the norm of its coefficient. -/
@[simp] theorem C (a : Polynomial ℤ) :
    norm (MvPolynomial.C a : MvPolynomial ι (Polynomial ℤ)) = Polynomial.coeffNorm1 a :=
  monomial 0 a
/-- The constant one has norm one. -/
@[simp] theorem one : norm (1 : MvPolynomial ι (Polynomial ℤ)) = 1 := by
  rw [← MvPolynomial.C_1, C, ← Polynomial.C_1, Polynomial.coeffNorm1_C]
  rfl
/-- An outer variable has norm one. -/
@[simp] theorem X (i : ι) : norm (MvPolynomial.X i : MvPolynomial ι (Polynomial ℤ)) = 1 := by
  change norm (MvPolynomial.monomial (Finsupp.single i 1) 1) = 1
  rw [monomial, ← Polynomial.C_1, Polynomial.coeffNorm1_C]
  rfl

/-- Promoting integer coefficients to constant parameter polynomials preserves norm. -/
@[simp] theorem map_C (p : MvPolynomial ι ℤ) :
    norm (p.map Polynomial.C) = MvPolynomial.coeffNorm1 p := by
  simp only [norm, MvPolynomial.support_map_of_injective p Polynomial.C_injective,
    MvPolynomial.coeff_map, Polynomial.coeffNorm1_C, MvPolynomial.coeffNorm1]

/-- Each parameter coefficient is bounded by the full norm. -/
theorem coeff_le (p : MvPolynomial ι (Polynomial ℤ)) (m : ι →₀ ℕ) :
    Polynomial.coeffNorm1 (p.coeff m) ≤ norm p := by
  simpa only [norm, MvPolynomial.sum_def] using
    Finsupp.single_eval_le_sum p.coeff (g := Polynomial.coeffNorm1)
      Polynomial.coeffNorm1_zero (fun _ => Nat.zero_le _) m

/-- The parameter coefficient norm satisfies the triangle inequality. -/
theorem add_le (p q : MvPolynomial ι (Polynomial ℤ)) : norm (p + q) ≤ norm p + norm q :=
  sum_add_le_of_subadditive Polynomial.coeffNorm1_zero Polynomial.coeffNorm1_add_le p q

/-- Negation preserves the parameter coefficient norm. -/
@[simp] theorem neg (p : MvPolynomial ι (Polynomial ℤ)) : norm (-p) = norm p := by
  simp [norm]

/-- The norm of a difference is bounded by the sum of the norms. -/
theorem sub_le (p q : MvPolynomial ι (Polynomial ℤ)) : norm (p - q) ≤ norm p + norm q := by
  simpa only [sub_eq_add_neg, neg] using add_le p (-q)

/-- A finite sum has norm at most the sum of the norms. -/
theorem sum_le {J : Type*} (s : Finset J) (p : J → MvPolynomial ι (Polynomial ℤ)) :
    norm (∑ j ∈ s, p j) ≤ ∑ j ∈ s, norm (p j) :=
  Finset.le_sum_of_subadditive norm zero.le add_le s p

/-- The parameter coefficient norm is submultiplicative. -/
theorem mul_le (p q : MvPolynomial ι (Polynomial ℤ)) : norm (p * q) ≤ norm p * norm q :=
  sum_mul_le_of_submultiplicative Polynomial.coeffNorm1_zero Polynomial.coeffNorm1_add_le
    Polynomial.coeffNorm1_mul_le p q

/-- Powers satisfy the corresponding coefficient norm bound. -/
theorem pow_le (p : MvPolynomial ι (Polynomial ℤ)) (n : ℕ) : norm (p ^ n) ≤ norm p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

/-- A finite product has norm at most the product of the norms. -/
theorem prod_le {J : Type*} (s : Finset J) (p : J → MvPolynomial ι (Polynomial ℤ)) :
    norm (∏ j ∈ s, p j) ≤ ∏ j ∈ s, norm (p j) :=
  Finset.le_prod_of_submultiplicative norm one.le mul_le s p

end MvPolynomial.ParameterCoeffNorm
