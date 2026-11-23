/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, critical equations in pure-power quotients)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.CriticalSystem
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.MultiplicationMatrix
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Coordinate characteristic polynomials in the zero-centered deformation

The polynomial for a coordinate is the characteristic polynomial of multiplication
by that coordinate in the normalized pure-power quotient. The inner variable is
the deformation parameter, and the outer variable is the coordinate value.
Specialization commutes with this construction over every commutative ring.

This adapts `LeanCanny.CountingHierarchy.parametricCoordinatePolynomial` at
lean-canny `970f28a5ecefc1327402ade16c068aa4b1b2c183` and formalizes the polynomial
in [OpenAI2026CountingHierarchy], Proposition 6.3, equation (6.11).
-/

public section

namespace MvPolynomial.CriticalSystem

open PurePower

variable {n ell : ℕ}

/-- The characteristic polynomial of coordinate multiplication in the quotient by
`X j ^ ell + C u * pderiv j F = 0`, with the parameter `u` left symbolic. -/
noncomputable def parametricCoordinatePolynomial (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (i : Fin n) :
    Polynomial (Polynomial ℤ) :=
  (multiplicationMatrix hell (criticalLower ell (fun _ => 0) Polynomial.X (F.map Polynomial.C))
    (criticalLower_degree ell hell _ _ _ ((totalDegree_map_le Polynomial.C F).trans hF))
    (X i)).charpoly

/-- The degree in the coordinate value is the number of normal monomials. -/
theorem parametricCoordinatePolynomial_natDegree (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (i : Fin n) :
    (parametricCoordinatePolynomial hell F hF i).natDegree = ell ^ n := by
  rw [parametricCoordinatePolynomial, Matrix.charpoly_natDegree_eq_dim]
  simp [NormalIndex]

/-- Evaluating the parameter commutes with coordinate multiplication and its characteristic
polynomial, including for noninjective specializations. -/
theorem parametricCoordinatePolynomial_map_eval₂ {R : Type*} [CommRing R] (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (i : Fin n) (u : R) :
    (parametricCoordinatePolynomial hell F hF i).map
        (Polynomial.eval₂RingHom (Int.castRingHom R) u) =
      (multiplicationMatrix hell (criticalLower ell (fun _ => 0) u (F.map (Int.castRingHom R)))
        (criticalLower_degree ell hell _ _ _ ((totalDegree_map_le _ F).trans hF))
        (X i)).charpoly := by
  rw [parametricCoordinatePolynomial, ← Matrix.charpoly_map, multiplicationMatrix_map]
  simp only [criticalLower_map, map_zero, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    MvPolynomial.map_map, Polynomial.eval₂RingHom_comp_C, MvPolynomial.map_X]

end MvPolynomial.CriticalSystem
