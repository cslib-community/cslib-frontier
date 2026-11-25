/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, critical equations in pure-power quotients)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.CriticalSystem
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CharpolyCoeffNorm
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.MultiplicationMatrix
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Eval.Defs
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValueParameterDegree

/-!
# Coordinate characteristic polynomials in the zero-centered deformation

The polynomial for a coordinate is the characteristic polynomial of multiplication
by that coordinate in the normalized pure-power quotient. The inner variable is
the deformation parameter, and the outer variable is the coordinate value.
Specialization commutes with this construction over every commutative ring. The
parameter degree is bounded from the spatial arity and deformation exponent. The
coefficient-norm bound uses the norm of the zero-centered lower relations and the
generic quotient characteristic estimate for multiplication by a variable.

This adapts `LeanCanny.CountingHierarchy.parametricCoordinatePolynomial` at
lean-canny `970f28a5ecefc1327402ade16c068aa4b1b2c183` and formalizes the polynomial
in [OpenAI2026CountingHierarchy], Proposition 6.3, equation (6.11). The norm estimate
adapts `parametricCoordinatePolynomial_mass_le` at the same source revision.
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

/-- The leading coefficient in the deformation parameter is a nonzero polynomial in the
coordinate value. -/
theorem leadingCoeff_swap_parametricCoordinatePolynomial_ne_zero (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (i : Fin n) :
    (Polynomial.Bivariate.swap (parametricCoordinatePolynomial hell F hF i)).leadingCoeff ≠ 0 := by
  apply Polynomial.leadingCoeff_ne_zero.mpr
  intro hswap
  have hz := congrArg Polynomial.Bivariate.swap hswap
  rw [Polynomial.Bivariate.swap_swap_apply, map_zero] at hz
  exact (Matrix.charpoly_monic _).ne_zero hz

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

/-- A bound on the deformation-parameter degree for pure powers of exponent `d + 1`. -/
@[expose] def coordinateParameterDegreeBound (n d : ℕ) : ℕ :=
  (d + 1) ^ n * (1 + n * (d + 1))

/-- The deformation degree is bounded uniformly across all coordinates of the critical system. -/
theorem parametricCoordinatePolynomial_natDegree_swap_le (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (i : Fin n) :
    (Polynomial.Bivariate.swap
      (parametricCoordinatePolynomial (by omega : 1 ≤ d + 1) F hF i)).natDegree ≤
      coordinateParameterDegreeBound n d := by
  let r := criticalLower (d + 1) (fun _ => 0) Polynomial.X (F.map Polynomial.C)
  have hr (j : Fin n) : (r j).totalDegree ≤ d := Nat.le_of_lt_succ
    (criticalLower_degree _ (by omega) _ _ _ ((totalDegree_map_le Polynomial.C F).trans hF) j)
  have hparam (j : Fin n) : HasParameterDegree (r j) 1 := by
    simpa only [r, map_zero] using criticalLower_hasParameterDegree (d + 1) (fun _ => 0) F j
  have hcoeff (k : ℕ) :
      ((parametricCoordinatePolynomial (by omega : 1 ≤ d + 1) F hF i).coeff k).natDegree ≤
        coordinateParameterDegreeBound n d := by
    have hk := natDegree_multiplicationMatrix_charpoly_coeff_le hd r hr hparam (X i)
      (totalDegree_X_le i) (HasParameterDegree.X i) k
    have h := hk.trans (Nat.mul_le_mul_right _ (Nat.sub_le ((d + 1) ^ n) k))
    simpa only [parametricCoordinatePolynomial, r, coordinateParameterDegreeBound,
      Nat.mul_one, Nat.zero_add] using h
  exact (Polynomial.Bivariate.natDegree_swap_le_iff _ _).mpr hcoeff

/-- Binary coefficient-norm exponent for coordinate multiplication with pure-power
exponent `ell` and input coefficient norm at most `2 ^ b`. -/
@[expose] def parametricCoordinateCoeffNormExponent (n ell b : ℕ) : ℕ :=
  multiplicationMatrixCharpolyCoeffNormExponent n ell 1 0 (ell.size + b)

/-- The norm sums absolute coefficients in both the deformation and coordinate variables. -/
theorem parametricCoordinatePolynomial_bivariateCoeffNorm1_le {n ell b : ℕ} (hell : 2 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (hb : F.coeffNorm1 ≤ 2 ^ b)
    (i : Fin n) :
    (parametricCoordinatePolynomial (by omega : 1 ≤ ell) F hF i).bivariateCoeffNorm1 ≤
      2 ^ parametricCoordinateCoeffNormExponent n ell b := by
  let G := F.map Polynomial.C
  let r := criticalLower ell (fun _ => 0) Polynomial.X G
  have hG : G.totalDegree ≤ ell := (totalDegree_map_le Polynomial.C F).trans hF
  have hr (j : Fin n) : (r j).totalDegree < ell :=
    criticalLower_degree ell (by omega) _ _ _ hG j
  have hrnorm (j : Fin n) : ParameterCoeffNorm.norm (r j) ≤ 2 ^ (ell.size + b) := by
    simp only [r, criticalLower, zero_pow (by omega : ell ≠ 0), map_zero, zero_sub,
      ParameterCoeffNorm.neg]
    refine (ParameterCoeffNorm.mul_le _ _).trans ?_
    rw [ParameterCoeffNorm.C, Polynomial.coeffNorm1_X, one_mul, pow_add]
    exact (ParameterCoeffNorm.pderiv_le G j).trans
      (Nat.mul_le_mul (hG.trans (Nat.lt_size_self _).le)
        (by simpa only [G, ParameterCoeffNorm.map_C] using hb))
  unfold parametricCoordinatePolynomial parametricCoordinateCoeffNormExponent
  change (multiplicationMatrix (by omega : 1 ≤ ell) r hr (X i)).charpoly.bivariateCoeffNorm1 ≤ _
  exact bivariateCoeffNorm1_multiplicationMatrix_charpoly_le_pow_two (Ω := 1) (bv := 0)
    (br := ell.size + b) hell r hr hrnorm (X i) (totalDegree_X_le i)
    (by simp only [ParameterCoeffNorm.X, pow_zero, le_refl])

end MvPolynomial.CriticalSystem
