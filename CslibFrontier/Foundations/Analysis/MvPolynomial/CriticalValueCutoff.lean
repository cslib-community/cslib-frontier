/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, real multivariate polynomial minima)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.ParameterExclusion
public import CslibFrontier.Foundations.Analysis.MvPolynomial.CriticalMinimumValue
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.BranchCutoff
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees

/-!
# Detecting a real zero at the chosen deformation parameter

The actual minimum of the critical deformation follows the characteristic roots. The finite
branch cutoff detects a real zero at the same power-of-two parameter used for separability.
The bivariate coefficient norm bounds both the leading coefficient in the parameter and the
value section at the cutoff.

Adapted from `CriticalFeasibility` and `LargeSpecializationBounds` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial.CriticalSystem

open Polynomial

private theorem eval₂_swap (P : Polynomial (Polynomial ℤ)) (x y : ℝ) :
    (Bivariate.swap P).eval₂ (eval₂RingHom (Int.castRingHom ℝ) x) y =
      P.eval₂ (eval₂RingHom (Int.castRingHom ℝ) y) x := by
  have heval (a b : ℝ) :
      (aevalAeval (R := ℤ) a b).toRingHom =
        eval₂RingHom (eval₂RingHom (Int.castRingHom ℝ) a) b := by
    ext <;> simp [Polynomial.aeval_def, algebraMap_int_eq]
  have happ (a b : ℝ) (Q : Polynomial (Polynomial ℤ)) :
      Q.eval₂ (eval₂RingHom (Int.castRingHom ℝ) a) b = aevalAeval a b Q := by
    rw [← coe_eval₂RingHom, ← heval]
    rfl
  rw [happ, happ, Bivariate.aevalAeval_swap]

/-- A nonnegative integer input has a real zero exactly when the actual critical minimum
is below the value cutoff at the chosen deformation parameter. -/
theorem exists_zero_iff_criticalMinimumValue_lt_at_parameterExclusion {n ell H : ℕ}
    (hell : 1 ≤ ell) (he : Even (ell + 1)) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ ell)
    (hFn : ∀ x, 0 ≤ MvPolynomial.eval x (F.map (Int.castRingHom ℝ)))
    (hH : (parametricValuePolynomial hell F hF).bivariateCoeffNorm1 ≤ 2 ^ H) :
    (∃ x, MvPolynomial.eval x (F.map (Int.castRingHom ℝ)) = 0) ↔
      criticalMinimumValue ell (fun i => (separatedCenters ell i : ℝ))
        (F.map (Int.castRingHom ℝ)) (2 ^ parameterExclusionExponent (ell ^ n) H) < 2 ^ (H + 1) := by
  let a : Fin n → ℝ := fun i => separatedCenters ell i
  let G := F.map (Int.castRingHom ℝ)
  let q := parametricValuePolynomial hell F hF
  let P := Bivariate.swap q
  let R : ℤ := (2 : ℤ) ^ (H + 1)
  let U : ℝ := (2 : ℝ) ^ parameterExclusionExponent (ell ^ n) H
  have hP : P ≠ 0 := by
    intro hz
    exact (parametricValuePolynomial_monic hell F hF).ne_zero
      (Bivariate.swap.injective (hz.trans (map_zero Bivariate.swap).symm))
  have ha (i : Fin n) : 0 ≤ a i := Nat.cast_nonneg _
  have hR : (P.leadingCoeff.coeffNorm1 : ℝ) + 1 ≤ (R : ℝ) := by
    have hnorm := (coeffNorm1_coeff_swap_le q P.natDegree).trans hH
    have htwo : (2 : ℕ) ^ H + 1 ≤ 2 ^ (H + 1) := by
      rw [pow_succ]
      have := Nat.one_le_two_pow (n := H)
      omega
    have hbound : P.leadingCoeff.coeffNorm1 + 1 ≤ 2 ^ (H + 1) :=
      (Nat.add_le_add_right hnorm 1).trans htwo
    dsimp only [R]
    exact_mod_cast hbound
  have hU : ((P.map (evalRingHom R)).coeffNorm1 : ℝ) + 1 ≤ U := by
    rw [show P = Bivariate.swap q from rfl, ← Bivariate.eval_C_eq_map_swap]
    have hD : q.natDegree ≤ ell ^ n := (parametricValuePolynomial_natDegree hell F hF).le
    dsimp only [R, U]
    exact_mod_cast coeffNorm1_eval_C_add_one_le_parameterExclusion hD hH
  have hroot (u : ℝ) (hu : 0 < u) :
      P.eval₂ (eval₂RingHom (Int.castRingHom ℝ) (criticalMinimumValue ell a G u)) u = 0 := by
    rw [show P = Bivariate.swap q from rfl, eval₂_swap, ← Polynomial.eval_map,
      show q = parametricValuePolynomial hell F hF from rfl, parametricValuePolynomial_map_eval₂]
    exact isRoot_valuePolynomial_criticalMinimumValue hell he a ha G
      ((totalDegree_map_le (Int.castRingHom ℝ) F).trans hF) hFn u hu.le
  rw [exists_zero_iff_bounded_criticalMinimumValue hell he a ha G hFn]
  simpa only [R, Int.cast_pow, Int.cast_ofNat] using bounded_root_branch_iff_lt hP
    (monotoneOn_criticalMinimumValue hell he a ha G hFn)
    (continuousOn_criticalMinimumValue hell he a ha G hFn) hroot hR hU

end MvPolynomial.CriticalSystem
