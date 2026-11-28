/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, derivatives of multivariate polynomial evaluation)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivative of a multivariate polynomial along one coordinate

Varying one coordinate gives the corresponding formal partial derivative.
This coordinate argument is adapted from the multivariate evaluation calculus in
`LeanCanny.Geometry.PolynomialCalculus` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial

/-- The derivative when only coordinate `i` varies is given by `pderiv i`. -/
theorem hasDerivAt_eval_update {ι K : Type*} [DecidableEq ι] [NontriviallyNormedField K]
    (p : MvPolynomial ι K) (x : ι → K) (i : ι) :
    HasDerivAt (fun t => eval (Function.update x i t) p)
      (eval x (pderiv i p)) (x i) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa only [eval_C, pderiv_C, map_zero] using (hasDerivAt_const (x i) a)
  | add p q hp hq =>
    simpa only [map_add] using HasDerivAt.fun_add hp hq
  | mul_X p j hp =>
    by_cases h : j = i
    · subst j
      simpa only [map_mul, eval_X, Function.update_self, pderiv_mul, pderiv_X_self,
        map_add, map_one, Function.update_eq_self, mul_one] using
        hp.fun_mul (hasDerivAt_id' (x i))
    · simpa only [map_mul, eval_X, Function.update_of_ne h, pderiv_mul, pderiv_X_of_ne h,
        map_add, map_zero, mul_zero, add_zero] using hp.fun_mul (hasDerivAt_const (x i) (x j))

end MvPolynomial
