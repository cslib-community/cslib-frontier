/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, critical equations in pure-power quotients)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.CriticalSystem
public import CslibFrontier.Foundations.Data.MvPolynomial.Substitution
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.MultiplicationMatrix
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Characteristic polynomial of the critical-value quotient

The deformed potential acts by multiplication in the quotient by the normalized critical
equations `X i ^ ell - criticalLower ell a u F i`. The partial derivatives are `ell + 1`
times these equations. The normalized ideal agrees with the gradient ideal when `ell + 1`
is a unit, and the two ideals can differ when that scalar vanishes. The monic characteristic
polynomial has degree equal to the quotient dimension over a nontrivial coefficient ring.
With a symbolic integer parameter, evaluating the coefficients gives the characteristic
polynomial of the corresponding normalized quotient over the target ring.
The relative construction retains a whole parameter block in the coefficients, so
specialization gives the critical-value polynomial for an individual witness fiber.

Adapted from `ParametricCriticalPolynomial` and `ParametricCriticalSpecialization` in
lean-canny at `970f28a5ecefc1327402ade16c068aa4b1b2c183`. Specialization uses the coefficient-map
identity for the multiplication matrix and works over arbitrary commutative rings.
-/

public section

namespace MvPolynomial.CriticalSystem

open PurePower

variable {S T : Type*} [CommRing S] [CommRing T] {n ell : ℕ}

/-- The characteristic polynomial of multiplication by the deformed potential in the
quotient by the normalized equations `X i ^ ell - criticalLower ell a u F i`.
The gradient generates this ideal when the scalar `ell + 1` is a unit. -/
@[expose] noncomputable def valuePolynomial (hell : 1 ≤ ell) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) (hF : F.totalDegree ≤ ell) : Polynomial S :=
  (multiplicationMatrix hell (criticalLower ell a u F) (criticalLower_degree ell hell a u F hF)
    (deformedPolynomial ell a u F)).charpoly

/-- The critical-value characteristic polynomial is monic. -/
theorem valuePolynomial_monic (hell : 1 ≤ ell) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) (hF : F.totalDegree ≤ ell) :
    (valuePolynomial hell a u F hF).Monic := Matrix.charpoly_monic _

/-- The degree is the number of normal monomials in the critical quotient. -/
theorem valuePolynomial_natDegree [Nontrivial S] (hell : 1 ≤ ell) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) (hF : F.totalDegree ≤ ell) :
    (valuePolynomial hell a u F hF).natDegree = ell ^ n := by
  rw [valuePolynomial, Matrix.charpoly_natDegree_eq_dim]
  simp [NormalIndex]

/-- The characteristic polynomial commutes with coefficient maps on the entire system. -/
theorem valuePolynomial_map (φ : S →+* T) (hell : 1 ≤ ell) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) (hF : F.totalDegree ≤ ell) :
    (valuePolynomial hell a u F hF).map φ =
      valuePolynomial hell (fun i => φ (a i)) (φ u) (F.map φ)
        ((totalDegree_map_le φ F).trans hF) := by
  simp only [valuePolynomial, ← Matrix.charpoly_map, multiplicationMatrix_map,
    deformedPolynomial_map, criticalLower_map]

/-- The separated critical-value polynomial with a symbolic deformation parameter.
The outer indeterminate is the critical value, and the inner indeterminate is the parameter. -/
@[expose] noncomputable def parametricValuePolynomial (hell : 1 ≤ ell) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ ell) : Polynomial (Polynomial ℤ) :=
  valuePolynomial hell (fun i => Polynomial.C (separatedCenters ell i : ℤ)) Polynomial.X
    (F.map Polynomial.C) ((totalDegree_map_le Polynomial.C F).trans hF)

/-- The symbolic critical-value polynomial is monic. -/
theorem parametricValuePolynomial_monic (hell : 1 ≤ ell) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ ell) : (parametricValuePolynomial hell F hF).Monic :=
  valuePolynomial_monic hell _ _ _ _

/-- The outer degree of the symbolic critical-value polynomial is the quotient dimension. -/
theorem parametricValuePolynomial_natDegree (hell : 1 ≤ ell) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ ell) : (parametricValuePolynomial hell F hF).natDegree = ell ^ n :=
  valuePolynomial_natDegree hell _ _ _ _

/-- Substitution of the deformation parameter gives the characteristic polynomial in the
normalized critical quotient over the target ring, with the same separated centers. -/
theorem parametricValuePolynomial_map_eval₂ (hell : 1 ≤ ell) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ ell) (u : T) :
    (parametricValuePolynomial hell F hF).map (Polynomial.eval₂RingHom (Int.castRingHom T) u) =
      valuePolynomial hell (fun i => (separatedCenters ell i : T)) u
        (F.map (Int.castRingHom T)) ((totalDegree_map_le (Int.castRingHom T) F).trans hF) := by
  simp only [parametricValuePolynomial, valuePolynomial_map, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Int.coe_castRingHom, Int.cast_natCast,
    MvPolynomial.map_map, Polynomial.eval₂RingHom_comp_C]

/-- Evaluating the parameter at an integer gives the actual integer quotient polynomial. -/
theorem parametricValuePolynomial_map_evalRingHom (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (u : ℤ) :
    (parametricValuePolynomial hell F hF).map (Polynomial.evalRingHom u) =
      valuePolynomial hell (fun i => (separatedCenters ell i : ℤ)) u F hF := by
  have heval : Polynomial.eval₂RingHom (RingHom.id ℤ) u = Polynomial.evalRingHom u :=
    RingHom.ext fun _ => Polynomial.eval₂_id
  simpa only [Int.castRingHom_int, heval, MvPolynomial.map_id, Int.cast_id] using
    parametricValuePolynomial_map_eval₂ hell F hF u

section Relative

variable {κ : Type*}

/-- Regard the parameters as coefficients and reserve `none` for the penalty variable. -/
@[expose] noncomputable def relativeSource (F : MvPolynomial (Fin n ⊕ κ) ℤ) :
    MvPolynomial (Fin n) (MvPolynomial (Option κ) ℤ) :=
  (sumRingEquiv ℤ (Fin n) κ F).map (rename some).toRingHom

/-- Passing the parameters to the coefficients does not raise the witness-variable degree. -/
theorem totalDegree_relativeSource_le (F : MvPolynomial (Fin n ⊕ κ) ℤ) :
    (relativeSource F).totalDegree ≤ F.totalDegree := by
  unfold relativeSource
  exact (totalDegree_map_le _ _).trans (totalDegree_sumRingEquiv_le F)

/-- The relative critical-value polynomial with zero centers. Its coefficients retain
the penalty variable at `none` and the original parameters at `some i`. -/
@[expose] noncomputable def relativeValuePolynomial (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin n ⊕ κ) ℤ) (hF : F.totalDegree ≤ ell) :
    Polynomial (MvPolynomial (Option κ) ℤ) :=
  valuePolynomial hell (fun _ => 0) (X none) (relativeSource F)
    ((totalDegree_relativeSource_le F).trans hF)

private theorem relativeSource_map (F : MvPolynomial (Fin n ⊕ κ) ℤ) (u : T) (x : κ → T) :
    (relativeSource F).map (eval₂Hom (Int.castRingHom T) (fun i => i.elim u x)) =
      (sumRingEquiv ℤ (Fin n) κ F).map (eval₂Hom (Int.castRingHom T) x) := by
  have hcomp : (eval₂Hom (Int.castRingHom T) (fun i : Option κ => i.elim u x)).comp
      (rename some).toRingHom = eval₂Hom (Int.castRingHom T) x := by
    apply RingHom.ext
    intro p
    change eval₂Hom (Int.castRingHom T) (fun i : Option κ => i.elim u x) (rename some p) = _
    have hcoords : (fun i : Option κ => i.elim u x) ∘ some = x := funext fun _ => rfl
    rw [eval₂Hom_rename, hcoords]
  rw [relativeSource, map_map, hcomp]

/-- Specializing the penalty and parameter coordinates gives the critical-value polynomial
of the fiber with those fixed parameters. Adapted from lean-canny's
`RelativeCriticalPolynomial` and `RelativeCriticalSpecialization` at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. -/
theorem relativeValuePolynomial_map (hell : 1 ≤ ell) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hF : F.totalDegree ≤ ell) (u : T) (x : κ → T) :
    (relativeValuePolynomial hell F hF).map (eval₂Hom (Int.castRingHom T) (fun i => i.elim u x)) =
      valuePolynomial hell (fun _ => 0) u
        ((sumRingEquiv ℤ (Fin n) κ F).map (eval₂Hom (Int.castRingHom T) x))
        ((totalDegree_map_le _ _).trans ((totalDegree_sumRingEquiv_le F).trans hF)) := by
  let φ := eval₂Hom (Int.castRingHom T) (fun i : Option κ => i.elim u x)
  have hu : φ (X none) = u := by simp [φ]
  change (valuePolynomial hell (fun _ => 0) (X none) (relativeSource F) _).map φ = _
  simpa only [map_zero, hu, φ, relativeSource_map] using
    valuePolynomial_map φ hell (fun _ => 0) (X none) (relativeSource F)
      ((totalDegree_relativeSource_le F).trans hF)

end Relative

end MvPolynomial.CriticalSystem
