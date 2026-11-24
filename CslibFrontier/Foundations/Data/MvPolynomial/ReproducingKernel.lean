/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/MvPolynomial/ReproducingKernel`)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial reproducing kernels

A normalized kernel annihilating all coordinate differences under a linear functional
reproduces evaluation on every polynomial. Its normalization and annihilation are polynomial
identities, with no assumption about a root's multiplicity or the coefficient characteristic.

Ported from
[lean-canny](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/PolynomialKernel.lean).
-/

public section

namespace MvPolynomial

variable {A σ : Type*} [CommRing A]

/-- A normalized kernel annihilating coordinate differences reproduces polynomial evaluation. -/
theorem polynomial_kernel_reproduces (L : MvPolynomial σ A →ₗ[A] A)
    (K : MvPolynomial σ A) (x : σ → A) (hone : L K = 1)
    (hcoord : ∀ i q, L (K * q * (X i - C (x i))) = 0)
    (q : MvPolynomial σ A) : L (K * q) = eval x q := by
  have hscalar (a : A) (v : MvPolynomial σ A) : L (v * C a) = a * L v := by
    rw [mul_comm v, ← smul_eq_C_mul, map_smul, smul_eq_mul]
  induction q using MvPolynomial.induction_on with
  | C a => simp only [hscalar, hone, mul_one, eval_C]
  | add q r hq hr => simp only [mul_add, map_add, hq, hr]
  | mul_X q i hq =>
    have hz := hcoord i q
    rw [mul_sub, map_sub, sub_eq_zero] at hz
    rw [← mul_assoc, hz, hscalar, hq, map_mul, eval_X, mul_comm]

end MvPolynomial
