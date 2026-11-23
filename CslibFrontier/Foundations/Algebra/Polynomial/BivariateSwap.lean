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

/-- Each outer coefficient has degree at most the degree in the inner variable. -/
theorem natDegree_coeff_le_natDegree_swap (p : R[X][Y]) (t : ℕ) :
    (p.coeff t).natDegree ≤ (swap p).natDegree :=
  natDegree_le_iff_coeff_eq_zero.2 fun d hd => by
    rw [← coeff_coeff_swap, coeff_eq_zero_of_natDegree_lt hd, coeff_zero]

/-- A bound on the inner degree is equivalent to a bound on every outer coefficient. -/
theorem natDegree_swap_le_iff (p : R[X][Y]) (m : ℕ) :
    (swap p).natDegree ≤ m ↔ ∀ t, (p.coeff t).natDegree ≤ m := by
  refine ⟨fun h t => (natDegree_coeff_le_natDegree_swap p t).trans h, fun h => ?_⟩
  refine natDegree_le_iff_coeff_eq_zero.2 fun d hd => ?_
  ext t
  rw [coeff_coeff_swap, coeff_zero]
  exact coeff_eq_zero_of_natDegree_lt ((h t).trans_lt hd)

/-- Substitution for the outer variable is coefficient-wise evaluation after swapping. -/
theorem eval_C_eq_map_swap (p : R[X][Y]) (x : R) :
    p.eval (C x) = (swap p).map (evalRingHom x) := by
  simpa only [coe_mapAlgHom, coe_aeval_eq_evalRingHom, aeval_def, algebraMap_def,
    Algebra.algebraMap_self, mapRingHom_id, eval₂_id] using aeval_eq_map_swap x p

/-- After a coefficient map, swapping the polynomial exchanges the two evaluation points. -/
theorem eval₂_eval₂RingHom_swap {S : Type*} [CommSemiring S] (f : R →+* S)
    (x y : S) (p : R[X][Y]) :
    (swap p).eval₂ (eval₂RingHom f x) y = p.eval₂ (eval₂RingHom f y) x := by
  have h : (eval₂RingHom (eval₂RingHom f x) y).comp swap.toRingHom =
      eval₂RingHom (eval₂RingHom f y) x := by
    ext <;> simp [swap_C_C, swap_X, swap_Y]
  exact DFunLike.congr_fun h p

end Polynomial.Bivariate
