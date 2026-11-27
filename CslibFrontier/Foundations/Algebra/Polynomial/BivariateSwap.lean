/-
Copyright (c) 2026 Mayank Rathee, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, bivariate polynomial swap)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Bivariate

/-! # Coefficients and specialization under bivariate variable swap

Swapping the two variables transposes the coefficient array and turns outer-variable
evaluation at a constant into coefficient-wise evaluation.
-/

public section

namespace Polynomial.Bivariate

open scoped Polynomial.Bivariate

variable {R : Type*} [CommSemiring R]

/-- The coefficient indices exchange places when swapping the two variables. -/
theorem coeff_coeff_swap (p : R[X][Y]) (a b : ℕ) :
    ((swap p).coeff a).coeff b = (p.coeff b).coeff a := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
  | monomial k c =>
    rw [swap_monomial, coeff_mul_C, coeff_map, C_mul_X_pow_eq_monomial]
    by_cases h : b = k
    · subst b
      simp
    · simp [coeff_monomial, h]

/-- Substitution for the outer variable is coefficient-wise evaluation after swapping. -/
theorem eval_C_eq_map_swap (p : R[X][Y]) (x : R) :
    p.eval (C x) = (swap p).map (evalRingHom x) := by
  simpa only [coe_mapAlgHom, coe_aeval_eq_evalRingHom, aeval_def, algebraMap_def,
    Algebra.algebraMap_self, mapRingHom_id, eval₂_id] using aeval_eq_map_swap x p

end Polynomial.Bivariate
