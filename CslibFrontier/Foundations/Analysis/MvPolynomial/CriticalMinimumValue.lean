/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, real multivariate polynomial minima)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.MvPolynomial.CriticalCoercive
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValuePolynomial
import CslibFrontier.Foundations.Analysis.MvPolynomial.CoordinateDerivative
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The minimum is a root of the critical-value characteristic polynomial

A global minimizer of the real deformation satisfies the normalized critical equations.
Cayley–Hamilton in the pure-power quotient then gives a characteristic root at its value.
Compact sublevels ensure that the minimum is attained for nonnegative parameters.

Adapted from `CriticalMinimum` and `CriticalMinimumValue` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial.CriticalSystem

open Set PurePower

variable {n : ℕ}

/-- The infimum of the values of the real deformation. Under the coercivity and sign
hypotheses, it is attained by a global minimizer. -/
noncomputable def criticalMinimumValue (ell : ℕ) (a : Fin n → ℝ)
    (F : MvPolynomial (Fin n) ℝ) (u : ℝ) : ℝ :=
  sInf (range (fun x => eval x (deformedPolynomial ell a u F)))

/-- Any global minimizer realizes the infimum defining `criticalMinimumValue`. -/
theorem criticalMinimumValue_eq_of_isMinOn (ell : ℕ) (a : Fin n → ℝ)
    (F : MvPolynomial (Fin n) ℝ) (u : ℝ) {x : Fin n → ℝ}
    (hx : IsMinOn (fun y => eval y (deformedPolynomial ell a u F)) univ x) :
    criticalMinimumValue ell a F u = eval x (deformedPolynomial ell a u F) := by
  apply IsLeast.csInf_eq
  refine ⟨mem_range_self x, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact hx (mem_univ y)

/-- The attained minimum for the nonnegative parameter is a root of the actual
critical-value characteristic polynomial. -/
theorem isRoot_valuePolynomial_criticalMinimumValue {ell : ℕ} (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (F : MvPolynomial (Fin n) ℝ) (hF : F.totalDegree ≤ ell)
    (hFn : ∀ x, 0 ≤ eval x F) (u : ℝ) (hu : 0 ≤ u) :
    (valuePolynomial hell a u F hF).IsRoot (criticalMinimumValue ell a F u) := by
  obtain ⟨x, hx⟩ := exists_isMinOn_eval_deformedPolynomial ell hell he a ha F hFn u hu
  let p := deformedPolynomial ell a u F
  have hzero (i : Fin n) : eval x (pderiv i p) = 0 := by
    have hmin : IsMinOn (fun t => eval (Function.update x i t) p) univ (x i) := by
      intro t _
      change eval (Function.update x i (x i)) p ≤ eval (Function.update x i t) p
      rw [Function.update_eq_self]
      exact hx (mem_univ _)
    exact (hmin.isLocalMin Filter.univ_mem).hasDerivAt_eq_zero (hasDerivAt_eval_update p x i)
  have hrel (i : Fin n) : aeval x (criticalLower ell a u F i) = x i ^ ell := by
    have hi := hzero i
    dsimp only [p] at hi
    rw [pderiv_deformedPolynomial, map_mul, eval_C, map_sub, map_pow, eval_X] at hi
    have hc : ((ell + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    simpa only [aeval_eq_eval] using (sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left hc)).symm
  rw [criticalMinimumValue_eq_of_isMinOn ell a F u hx]
  simpa only [valuePolynomial, aeval_eq_eval] using
    isRoot_charpoly_multiplicationMatrix_of_aeval_eq hell (criticalLower ell a u F)
      (criticalLower_degree ell hell a u F hF) p x hrel

end MvPolynomial.CriticalSystem
