/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, critical equations in pure-power quotients)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.ParameterExclusion
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValuePolynomial
public import Mathlib.FieldTheory.Separable
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.InitialCriticalSeparability
import CslibFrontier.Foundations.RingTheory.Polynomial.ResultantSpecialization

/-!
# A parameter avoiding exceptional critical values

Initial separability shows that the derivative resultant of the symbolic critical-value
polynomial is nonzero. Given a logarithmic norm bound, the explicit parameter and value cutoff
therefore give a separable specialized polynomial that does not vanish at the cutoff.

Adapted from `ParametricCriticalDiscriminant` and `LargeSpecializationBounds` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial.CriticalSystem

/-- The symbolic derivative resultant is nonzero because the specialization at zero is
separable over the complex numbers. -/
theorem parametricValuePolynomial_resultant_derivative_ne_zero {n ell : ℕ} (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) :
    let q := parametricValuePolynomial hell F hF
    q.resultant q.derivative ≠ 0 := by
  intro q
  let φ := Polynomial.eval₂RingHom (Int.castRingHom ℂ) 0
  have hm : q.Monic := parametricValuePolynomial_monic hell F hF
  have hn := (hm.separable_map_iff_resultant_derivative_ne_zero φ).mp
    (parametricValuePolynomial_at_zero_separable hell F hF)
  intro h
  exact hn (by rw [h, map_zero])

/-- From a logarithmic norm bound, choose a parameter at which the actual critical-value
polynomial specializes to a separable polynomial with no root at the chosen value cutoff. -/
theorem parametricValuePolynomial_at_parameterExclusion {n ell H : ℕ} (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell)
    (hH : (parametricValuePolynomial hell F hF).bivariateCoeffNorm1 ≤ 2 ^ H) :
    let q := parametricValuePolynomial hell F hF
    let a : ℤ := 2 ^ (H + 1)
    let u : ℝ := 2 ^ Polynomial.parameterExclusionExponent (ell ^ n) H
    let q' := q.map (Polynomial.eval₂RingHom (Int.castRingHom ℝ) u)
    q'.Separable ∧ q'.eval (a : ℝ) ≠ 0 := by
  intro q a u q'
  let φ := Polynomial.eval₂RingHom (Int.castRingHom ℝ) u
  have hm : q.Monic := parametricValuePolynomial_monic hell F hF
  have hd : q.natDegree ≤ ell ^ n := (parametricValuePolynomial_natDegree hell F hF).le
  have ⟨hvalue, hres⟩ := Polynomial.eval₂_ne_zero_at_parameterExclusion hm.ne_zero
    (parametricValuePolynomial_resultant_derivative_ne_zero hell F hF) hd hH
  refine ⟨(hm.separable_map_iff_resultant_derivative_ne_zero φ).mpr hres, ?_⟩
  have ha : φ (Polynomial.C a) = (a : ℝ) := Polynomial.eval₂_C _ _
  change (q.map φ).eval (a : ℝ) ≠ 0
  rw [← ha, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  exact hvalue

end MvPolynomial.CriticalSystem
