/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module

import CslibFrontier.Foundations.Algebra.Polynomial.BivariateKronecker

open Polynomial

-- The two indices contribute differently when both are nonzero.
example :
    ((monomial 2 (monomial 1 (-3 : ℤ))).eval (X ^ 2)).coeff 5 = -3 := by
  let p := monomial 2 (monomial 1 (-3 : ℤ))
  have hdegree : (Bivariate.swap p).natDegree < 2 := by
    dsimp only [p]
    rw [Bivariate.swap_monomial_monomial]
    exact (natDegree_monomial_le (monomial 2 (-3 : ℤ)) (m := 1)).trans_lt (by decide)
  change (p.eval (X ^ 2)).coeff (1 + 2 * 2) = _
  rw [Bivariate.coeff_eval_X_pow p hdegree 1 2 (by decide)]
  simp [p]
