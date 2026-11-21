/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
module
-- upstream: local-only (tests)

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Charpoly.CoeffNorm
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CharpolyCoeffNorm

/-! # Nonconstant parameters in characteristic coefficient norm bounds -/

public section
namespace CslibFrontierTests.RealAlgebraicCharpolyNorm

open Polynomial Matrix

private theorem coeffNorm1_parameter : coeffNorm1 (X : ℤ[X]) = 1 := by
  simpa only [mul_one, coeffNorm1_one] using coeffNorm1_X_mul (1 : ℤ[X])

/-- The one-entry matrix `[U]` has characteristic polynomial of bivariate norm at most two. -/
theorem parameterMatrix :
    (Matrix.of (fun _ _ : Fin 1 => (X : ℤ[X]))).charpoly.bivariateCoeffNorm1 ≤ 2 := by
  refine (bivariateCoeffNorm1_charpoly_le_of_trace_pow _ (A := 1) (by decide) ?_).trans ?_
  · intro j hj hjD
    have hj1 : j = 1 := by rw [Fintype.card_fin] at hjD; omega
    subst j
    simp [trace, coeffNorm1_parameter]
  · decide

/-- The bound applies to multiplication by `x` in the quotient with relation `x² = U`. -/
theorem quadraticQuotient :
    let r : Fin 1 → MvPolynomial (Fin 1) ℤ[X] := fun _ => MvPolynomial.C X
    let hr : ∀ i, (r i).totalDegree < 2 := fun _ => by simp [r]
    (MvPolynomial.PurePower.multiplicationMatrix (by decide : 1 ≤ 2) r hr
      (MvPolynomial.X 0)).charpoly.bivariateCoeffNorm1 ≤ 768 := by
  dsimp only
  exact MvPolynomial.PurePower.bivariateCoeffNorm1_multiplicationMatrix_charpoly_le
    (d := 1) (Ω := 1) (V := 1) (R := 1) (by decide) _ (by simp) (by simp [coeffNorm1_parameter])
    (by decide) _ (by simp) (by simp) (by decide)

end CslibFrontierTests.RealAlgebraicCharpolyNorm
