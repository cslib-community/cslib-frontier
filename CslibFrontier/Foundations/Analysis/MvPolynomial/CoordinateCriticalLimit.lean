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
import CslibFrontier.Foundations.Analysis.MvPolynomial.CriticalCoercive
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Coordinate roots of limits of critical points

At a convergent family of solutions to the zero-centered pure-power equations, the leading
deformation coefficients of the coordinate characteristic polynomials give equations for the
limiting coordinates. The parameter tends to positive infinity along a nontrivial filter.
The product of these real coordinate root sets is finite and meets each nonempty
relatively clopen piece of the zero set of a nonnegative input.
This adapts `candidateCoordinates_meet_clopen` in lean-canny
`970f28a5ecefc1327402ade16c068aa4b1b2c183` to the normalized deformation.
-/

public section

namespace MvPolynomial.CriticalSystem

open Polynomial Filter PurePower Set
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

/-- The product of the real root sets of the leading deformation coefficients of the
coordinate characteristic polynomials. -/
noncomputable def coordinateRootGrid {n ell : ℕ} (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) : Set (Fin n → ℝ) :=
  {x | ∀ i, ((Bivariate.swap (parametricCoordinatePolynomial hell F hF i)).leadingCoeff.map
    (Int.castRingHom ℝ)).IsRoot (x i)}

/-- Grid membership is equivalent to each coordinate being a root of its leading
deformation coefficient. -/
@[simp] theorem mem_coordinateRootGrid {n ell : ℕ} {hell : 1 ≤ ell}
    {F : MvPolynomial (Fin n) ℤ} {hF : F.totalDegree ≤ ell} {x : Fin n → ℝ} :
    x ∈ coordinateRootGrid hell F hF ↔
      ∀ i, ((Bivariate.swap (parametricCoordinatePolynomial hell F hF i)).leadingCoeff.map
        (Int.castRingHom ℝ)).IsRoot (x i) := Iff.rfl

/-- The leading deformation coefficient is nonzero for every coordinate, so the
product of its real root sets is finite. -/
theorem coordinateRootGrid_finite {n ell : ℕ} (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) :
    (coordinateRootGrid hell F hF).Finite :=
  Set.Finite.pi' fun i => Polynomial.finite_setOfPred_isRoot
    ((Polynomial.map_ne_zero_iff Int.cast_injective).2
      (leadingCoeff_swap_parametricCoordinatePolynomial_ne_zero hell F hF i))

/-- Each nonempty relatively clopen piece of the real zero set of a nonnegative
integer polynomial meets its coordinate root grid. -/
theorem exists_mem_coordinateRootGrid_of_isClopen {n ell : ℕ} (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell)
    (hFn : ∀ x, 0 ≤ eval x (F.map (Int.castRingHom ℝ)))
    (C : Set {x : Fin n → ℝ // eval x (F.map (Int.castRingHom ℝ)) = 0})
    (hC : IsClopen C) (hCne : C.Nonempty) :
    ∃ z ∈ C, z.val ∈ coordinateRootGrid hell F hF := by
  obtain ⟨y, z, φ, hz, hφ, hlim, hcritical⟩ :=
    exists_deformedPolynomial_critical_subseq_in_clopen ell hell he (fun _ => 0) (fun _ => le_rfl)
      (F.map (Int.castRingHom ℝ)) hFn C hC hCne
      (u := fun k => (k : ℝ)) (fun _ => Nat.cast_nonneg _) tendsto_natCast_atTop_atTop
  refine ⟨z, hz, mem_coordinateRootGrid.mpr fun i => ?_⟩
  rw [Polynomial.IsRoot, Polynomial.eval_map]
  exact eval₂_coordinateLeadingCoeff_eq_zero_of_tendsto hell F hF
    (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop) hlim hcritical i

end MvPolynomial.CriticalSystem
