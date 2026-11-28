/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial resultants)

public import CslibFrontier.Init
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Coefficient maps and the derivative resultant

For a monic polynomial over a characteristic-zero domain, mapping coefficients to a
characteristic-zero field preserves both Sylvester dimensions. The mapped derivative
resultant then detects separability of the specialized polynomial.

Adapted from `DiscriminantSpecialization` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

variable {R K : Type*} [CommRing R] [IsDomain R] [CharZero R] [Field K] [CharZero K]

/-- Coefficient maps preserve the derivative resultant of a monic polynomial. -/
theorem Monic.resultant_derivative_map {p : Polynomial R} (hp : p.Monic) (φ : R →+* K) :
    φ (p.resultant p.derivative) = (p.map φ).resultant (p.map φ).derivative := by
  symm
  simp only [Polynomial.natDegree_derivative, hp.natDegree_map φ]
  rw [Polynomial.derivative_map]
  exact Polynomial.resultant_map_map p p.derivative p.natDegree (p.natDegree - 1) φ

/-- A monic specialization is separable exactly when the original derivative resultant
has nonzero image under the coefficient map. -/
theorem Monic.separable_map_iff_resultant_derivative_ne_zero {p : Polynomial R} (hp : p.Monic)
    (φ : R →+* K) : (p.map φ).Separable ↔ φ (p.resultant p.derivative) ≠ 0 := by
  rw [hp.resultant_derivative_map φ]
  refine ⟨resultant_ne_zero _ _, fun h => ?_⟩
  by_contra hsep
  exact h (resultant_eq_zero_iff.mpr ⟨Or.inl (hp.map φ).ne_zero, hsep⟩)

end Polynomial
