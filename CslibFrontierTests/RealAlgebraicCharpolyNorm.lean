/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
module
-- upstream: local-only (tests)

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Charpoly.CoeffNorm

/-! # A nonconstant parameter in the characteristic coefficient norm bound -/

public section
namespace CslibFrontierTests.RealAlgebraicCharpolyNorm

open Polynomial Matrix

/-- The one-entry matrix `[U]` has characteristic polynomial of bivariate norm at most two. -/
theorem parameterMatrix :
    (Matrix.of (fun _ _ : Fin 1 => (X : ℤ[X]))).charpoly.bivariateCoeffNorm1 ≤ 2 := by
  have hX : coeffNorm1 (X : ℤ[X]) = 1 := by
    simpa only [mul_one, coeffNorm1_one] using coeffNorm1_X_mul (1 : ℤ[X])
  refine (bivariateCoeffNorm1_charpoly_le_of_trace_pow _ (A := 1) (by decide) ?_).trans ?_
  · intro j hj hjD
    have hj1 : j = 1 := by rw [Fintype.card_fin] at hjD; omega
    subst j
    simp [trace, hX]
  · decide

end CslibFrontierTests.RealAlgebraicCharpolyNorm
