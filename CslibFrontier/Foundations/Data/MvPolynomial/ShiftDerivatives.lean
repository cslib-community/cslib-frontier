/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, derivatives and total degree of multivariate shifts)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.Shift
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees
import CslibFrontier.Foundations.Data.MvPolynomial.Substitution

/-!
# Derivative values as coefficients of a shift

First and mixed second derivative values are coefficients of the existing `MvPolynomial.shift`.
The second-derivative formula includes factor two when the two coordinates coincide.
Shifting cannot increase total degree, including when the point has coordinates in an algebra
and coefficient specialization makes some coefficients vanish.

The coefficient identities are adapted from
[lean-canny](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/PolynomialTranslation.lean),
using the existing shift evaluation and derivative API.
-/

public section

namespace MvPolynomial

variable {ι R A : Type*} [CommSemiring R]

/-- A first derivative value is one coefficient of the shifted polynomial. -/
theorem first_derivative_translation_coeff (z : ι → R) (F : MvPolynomial ι R) (i : ι) :
    eval z (pderiv i F) = (shift z F).coeff (Finsupp.single i 1) := by
  classical
  simpa [← pderiv_shift, coeff_pderiv] using (coeff_zero_shift z (pderiv i F)).symm

/-- A second derivative is one shifted coefficient, including factor two for a repeated index. -/
theorem second_derivative_translation_coeff (z : ι → R) (F : MvPolynomial ι R) (i j : ι) :
    eval z (pderiv j (pderiv i F)) =
      (shift z F).coeff (Finsupp.single j 1 + Finsupp.single i 1) *
        ((Finsupp.single j 1 : ι →₀ ℕ) i + 1 : ℕ) := by
  rw [first_derivative_translation_coeff z (pderiv i F) j,
    ← pderiv_shift, coeff_pderiv, Nat.cast_add, Nat.cast_one]

/-- Shifting by a point in an algebra cannot increase total degree. -/
theorem totalDegree_shift_le [CommSemiring A] [Algebra R A]
    (z : ι → A) (F : MvPolynomial ι R) : (shift z F).totalDegree ≤ F.totalDegree := by
  have hshift : shift z F = aeval (R := A) (fun i => X i + C (z i)) (F.map (algebraMap R A)) := by
    simp only [shift, aeval_def, eval₂_map]
    rfl
  exact hshift ▸ (totalDegree_aeval_le (fun i => (totalDegree_add _ _).trans
    (max_le (totalDegree_X_le i) (by simp))) _).trans (totalDegree_map_le _ _)

end MvPolynomial
