/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, pure-power polynomial residues and traces)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.PDerivDegree
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees
import CslibFrontier.Foundations.Data.MvPolynomial.Determinant
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

/-- Lower relations of degree at most `d` give a Jacobian of degree at most `n * d`. -/
theorem totalDegree_jacobian_le (d : ℕ) (r : Fin n → MvPolynomial (Fin n) S)
    (hr : ∀ i, (r i).totalDegree ≤ d) :
    (jacobian (d + 1) r).totalDegree ≤ n * d := by
  classical
  unfold jacobian
  refine (totalDegree_det_le _ d ?_).trans_eq (by rw [Fintype.card_fin])
  intro i j
  have hX : (X i ^ (d + 1) : MvPolynomial (Fin n) S).totalDegree ≤ d + 1 := by
    exact (totalDegree_pow _ _).trans (by
      simpa only [mul_one] using Nat.mul_le_mul_left (d + 1) (totalDegree_X_le (R := S) i))
  have hf := (totalDegree_sub _ _).trans (max_le hX ((hr i).trans (Nat.le_succ d)))
  exact (totalDegree_pderiv_le _ j).trans (by omega)

end MvPolynomial.PurePower
