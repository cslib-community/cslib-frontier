/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, beside `Mathlib/LinearAlgebra/Matrix/Adjugate.lean`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Cramer's rule for an integer system over a ring extension

`Matrix.intCast_cramer_eq_det_smul` clears the denominator of a solution after casting the
integer coefficients into any commutative ring.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n]

/-- **Cramer's rule over an extension.** If the integer system `G *ᵥ y = c` holds after casting
into a commutative ring `R`, then the cast of Cramer's integer vector `cramer G c` is
`det G • y`. -/
theorem intCast_cramer_eq_det_smul {R : Type*} [CommRing R] [DecidableEq n]
    {G : Matrix n n ℤ} {c : n → ℤ} {y : n → R}
    (hGy : G.map (Int.cast : ℤ → R) *ᵥ y = fun j => (c j : R)) :
    (fun j => (cramer G c j : R)) = (G.det : R) • y := by
  have h := (Int.castRingHom R).map_mulVec (adjugate G) c
  simp only [eq_intCast, Int.coe_castRingHom] at h
  have hadj : (adjugate G).map (Int.cast : ℤ → R) = adjugate (G.map Int.cast) :=
    (Int.castRingHom R).map_adjugate G
  have hdet : ((G.det : ℤ) : R) = (G.map (Int.cast : ℤ → R)).det := (Int.castRingHom R).map_det G
  calc (fun j => (cramer G c j : R))
      = (adjugate G).map (Int.cast : ℤ → R) *ᵥ fun j => (c j : R) := by
        rw [cramer_eq_adjugate_mulVec]
        exact funext h
    _ = (G.det : R) • y := by
        rw [← hGy, mulVec_mulVec, hadj, adjugate_mul, smul_mulVec, one_mulVec, hdet]

end Matrix
