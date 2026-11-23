/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, limits of polynomial critical points)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CoordinateCharacteristicPolynomial
public import Mathlib.Topology.Instances.Real.Lemmas
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.BranchCutoff

/-!
# Coordinate roots of limits of critical points

At a convergent family of solutions to the zero-centered pure-power equations, the leading
deformation coefficients of the coordinate characteristic polynomials give equations for the
limiting coordinates. The parameter tends to positive infinity along a nontrivial filter.
This supplies the limit step of `candidateCoordinates_meet_clopen` in lean-canny
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial.CriticalSystem

open Polynomial Filter PurePower
open scoped Topology

/-- A limit of solutions to the normalized pure-power relations at divergent parameters
is a root of the leading deformation coefficient in each coordinate. -/
theorem eval₂_coordinateLeadingCoeff_eq_zero_of_tendsto {ι : Type*} {l : Filter ι} [NeBot l]
    {n ell : ℕ} (hell : 1 ≤ ell) (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell)
    {u : ι → ℝ} {x : ι → Fin n → ℝ} {y : Fin n → ℝ}
    (hu : Tendsto u l atTop) (hx : Tendsto x l (𝓝 y))
    (hcritical : ∀ᶠ k in l, ∀ j, aeval (x k)
      (criticalLower ell (fun _ => 0) (u k) (F.map (Int.castRingHom ℝ)) j) = x k j ^ ell)
    (i : Fin n) :
    (Bivariate.swap (parametricCoordinatePolynomial hell F hF i)).leadingCoeff.eval₂
      (Int.castRingHom ℝ) (y i) = 0 := by
  apply eval₂_leadingCoeff_eq_zero_of_tendsto_atTop _ hu
    ((continuous_apply i).continuousAt.tendsto.comp hx)
  filter_upwards [hcritical] with k hk
  rw [Bivariate.eval₂_eval₂RingHom_swap, ← Polynomial.eval_map,
    parametricCoordinatePolynomial_map_eval₂]
  simpa only [Polynomial.IsRoot, aeval_X, Function.comp_apply] using
    isRoot_charpoly_multiplicationMatrix_of_aeval_eq hell _
      (criticalLower_degree ell hell _ _ _ ((totalDegree_map_le _ F).trans hF)) (X i) (x k) hk

end MvPolynomial.CriticalSystem
