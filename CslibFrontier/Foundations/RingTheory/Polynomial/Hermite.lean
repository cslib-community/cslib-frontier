/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, `Mathlib/RingTheory/Polynomial/Hermite/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# Derivatives of the Hermite polynomials

The probabilists' Hermite polynomials `Polynomial.hermite` form an *Appell sequence*:
`(hermite (n + 1))' = (n + 1) hermite n` (`Polynomial.derivative_hermite_succ`). With Mathlib's
recursion `Polynomial.hermite_succ` this gives the three-term recurrence
`hermite (n + 2) = X hermite (n + 1) - (n + 1) hermite n` (`Polynomial.hermite_succ_succ`) and
the Hermite differential equation `X hermite n' - hermite n'' = n hermite n`
(`Polynomial.X_mul_derivative_hermite_sub`, [O'Donnell, Exercise 11.10(c)][ODonnell2014]).

## Main results

* `Polynomial.derivative_hermite_succ`: the Appell property.
* `Polynomial.hermite_succ_succ`: the three-term recurrence.
* `Polynomial.X_mul_derivative_hermite_sub`: the Hermite differential equation.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Polynomial

/-- The Hermite polynomials form an **Appell sequence**:
`(hermite (n + 1))' = (n + 1) hermite n`. -/
theorem derivative_hermite_succ (n : ℕ) :
    derivative (hermite (n + 1)) = (n + 1 : ℤ[X]) * hermite n := by
  induction n with
  | zero => simp [hermite_zero]
  | succ n ih =>
    rw [hermite_succ (n + 1), derivative_sub, derivative_mul, derivative_X, ih, derivative_mul,
      hermite_succ n]
    simp only [derivative_add, derivative_natCast, derivative_one, add_zero, zero_mul, zero_add]
    push_cast
    ring

/-- The **three-term recurrence** `hermite (n + 2) = X hermite (n + 1) - (n + 1) hermite n`. -/
theorem hermite_succ_succ (n : ℕ) :
    hermite (n + 2) = X * hermite (n + 1) - (n + 1 : ℤ[X]) * hermite n := by
  rw [hermite_succ (n + 1), derivative_hermite_succ]

/-- The **Hermite differential equation** `X hermite n' - hermite n'' = n hermite n`
[O'Donnell, Exercise 11.10(c)][ODonnell2014]: `hermite n` is an eigenvector, with eigenvalue `n`,
of `p ↦ X p' - p''`, the one-dimensional Ornstein–Uhlenbeck operator of
[O'Donnell, Proposition 11.26][ODonnell2014]. -/
theorem X_mul_derivative_hermite_sub (n : ℕ) :
    X * derivative (hermite n) - derivative (derivative (hermite n)) = (n : ℤ[X]) * hermite n := by
  have h := congrArg derivative (hermite_succ n)
  rw [derivative_hermite_succ, add_comm (n : ℤ[X]) 1, add_mul, derivative_sub, derivative_mul,
    derivative_X, one_mul, add_sub_assoc] at h
  exact add_left_cancel h.symm

end Polynomial
