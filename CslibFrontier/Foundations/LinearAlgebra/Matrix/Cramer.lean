/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, beside `Mathlib/LinearAlgebra/Matrix/Adjugate.lean`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Cramer's rule after a ring homomorphism

`Matrix.map_cramer_eq_det_smul` recovers the determinant-scaled solution of a linear system after
mapping its coefficients into another commutative ring. For integer coefficients,
`Matrix.abs_cramer_le` bounds each Cramer coordinate by the Leibniz determinant bound.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Applying a ring homomorphism to the Cramer vector of a system gives its mapped determinant
times any solution of the mapped system. -/
theorem map_cramer_eq_det_smul {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {A : Matrix n n R} {b : n → R} {y : n → S}
    (h : A.map φ *ᵥ y = fun i => φ (b i)) :
    (fun i => φ (cramer A b i)) = φ A.det • y := by
  calc (fun i => φ (cramer A b i)) = A.adjugate.map φ *ᵥ (fun i => φ (b i)) := by
        rw [cramer_eq_adjugate_mulVec]
        exact funext (φ.map_mulVec _ _)
    _ = φ A.det • y := by
        have hadj : A.adjugate.map φ = (A.map φ).adjugate := φ.map_adjugate A
        have hdet : φ A.det = (A.map φ).det := φ.map_det A
        rw [← h, mulVec_mulVec, hadj, adjugate_mul, smul_mulVec, one_mulVec, hdet]

/-- Each coordinate of the integer Cramer vector is the determinant of a matrix whose entries
are bounded by the same `H` as the coefficients and right-hand side. -/
theorem abs_cramer_le {A : Matrix n n ℤ} {b : n → ℤ} {H : ℕ}
    (hA : ∀ i j, |A i j| ≤ H) (hb : ∀ i, |b i| ≤ H) (j : n) :
    |cramer A b j| ≤ (Nat.factorial (Fintype.card n) * H ^ Fintype.card n : ℕ) := by
  rw [cramer_apply]
  have hcol (i k : n) : |(A.updateCol j b) i k| ≤ H := by
    rw [updateCol_apply]
    split_ifs
    · exact hb i
    · exact hA i k
  simpa [nsmul_eq_mul] using det_le (abv := AbsoluteValue.abs) hcol

end Matrix
