/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
module
-- upstream: local-only (tests)

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Charpoly.CoeffNorm
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CharpolyCoeffNorm
public import CslibFrontier.Foundations.RingTheory.Polynomial.ResultantCoeffNorm

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

private noncomputable def quadratic : Polynomial (Polynomial ℤ) := X ^ 2 + C X

private theorem quadratic_degree : quadratic.natDegree ≤ 2 := by
  exact (natDegree_add_le _ _).trans (by simp)

private theorem quadratic_norm : quadratic.bivariateCoeffNorm1 ≤ 2 := by
  have hX : (X ^ 2 : Polynomial (Polynomial ℤ)).bivariateCoeffNorm1 ≤ 1 := by
    simpa only [one_mul, bivariateCoeffNorm1_one] using
      bivariateCoeffNorm1_mul_X_pow_le (1 : Polynomial (Polynomial ℤ)) 2
  have hC : (C (X : ℤ[X])).bivariateCoeffNorm1 = 1 :=
    (bivariateCoeffNorm1_C _).trans coeffNorm1_parameter
  exact (bivariateCoeffNorm1_add_le _ _).trans (Nat.add_le_add hX hC.le)

/-- Substituting `-2` for the outer variable of `Y² + U` retains a polynomial in `U`. -/
private theorem quadraticValueSection : (quadratic.eval (C (-2))).coeffNorm1 ≤ 8 :=
  (coeffNorm1_eval_C_le quadratic (-2) (by decide)).trans
    (Nat.mul_le_mul quadratic_norm (Nat.pow_le_pow_right (by decide) quadratic_degree))

/-- The derivative-resultant estimate applies to the same nonconstant parameter family. -/
private theorem quadraticDerivativeResultant :
    (quadratic.resultant quadratic.derivative).coeffNorm1 ≤ 6144 :=
  coeffNorm1_resultant_derivative_le quadratic quadratic_degree quadratic_norm

end CslibFrontierTests.RealAlgebraicCharpolyNorm
