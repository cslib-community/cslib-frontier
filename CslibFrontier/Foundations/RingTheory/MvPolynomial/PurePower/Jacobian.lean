/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, pure-power polynomial residues and traces)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The Jacobian polynomial of a pure-power system

`jacobian ell r` is the determinant of the derivatives of the actual relations
`X i ^ ell - r i`. It commutes with coefficient specialization (`jacobian_map`), without
requiring a degree bound or simple roots. Keeping this polynomial below the trace construction
also lets modular Jacobian evaluators use it without importing quotient bases or traces.

Ported from `LeanCanny.CountingHierarchy.PurePowerTrace` and `QuotientTraceSpecialization` at
lean-canny commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`, as an algebraic step toward the
counting bounds.
-/

public section

namespace MvPolynomial.PurePower

variable {S T : Type*} [CommRing S] [CommRing T] {n : ℕ}

/-- The Jacobian determinant of the relations `X i ^ ell - r i`. -/
@[expose] noncomputable def jacobian (ell : ℕ)
    (r : Fin n → MvPolynomial (Fin n) S) : MvPolynomial (Fin n) S :=
  Matrix.det (Matrix.of (fun i j => pderiv j (X i ^ ell - r i)))

/-- Differentiating and taking the Jacobian determinant commute with coefficient maps. -/
theorem jacobian_map (φ : S →+* T) (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S) :
    (jacobian ell r).map φ = jacobian ell (fun i => (r i).map φ) := by
  unfold jacobian
  rw [(MvPolynomial.map φ).map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change (pderiv j (X i ^ ell - r i)).map φ = _
  rw [← pderiv_map]
  simp only [map_sub, map_pow, map_X, Matrix.of_apply]

end MvPolynomial.PurePower
