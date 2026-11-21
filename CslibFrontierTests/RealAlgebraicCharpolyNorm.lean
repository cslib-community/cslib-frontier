/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
module
-- upstream: local-only (tests)

public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.ParameterExclusion
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

private noncomputable def quadratic : Polynomial (Polynomial ℤ) := X ^ 2 + C (X - 1)

private theorem quadratic_degree : quadratic.natDegree = 2 := natDegree_X_pow_add_C

private theorem quadratic_norm : quadratic.bivariateCoeffNorm1 ≤ 3 := by
  have hX : (X ^ 2 : Polynomial (Polynomial ℤ)).bivariateCoeffNorm1 ≤ 1 := by
    simpa only [one_mul, bivariateCoeffNorm1_one] using
      bivariateCoeffNorm1_mul_X_pow_le (1 : Polynomial (Polynomial ℤ)) 2
  have hC : (C (X - 1 : ℤ[X])).bivariateCoeffNorm1 ≤ 2 := by
    rw [bivariateCoeffNorm1_C]
    simpa only [coeffNorm1_parameter, coeffNorm1_one] using coeffNorm1_sub_le (X : ℤ[X]) 1
  exact (bivariateCoeffNorm1_add_le _ _).trans (Nat.add_le_add hX hC)

/-- Substituting `-2` for the outer variable of `Y² + U - 1` retains a polynomial in `U`. -/
private theorem quadraticValueSection : (quadratic.eval (C (-2))).coeffNorm1 ≤ 12 :=
  (coeffNorm1_eval_C_le quadratic (-2) (by decide)).trans
    (Nat.mul_le_mul quadratic_norm (Nat.pow_le_pow_right (by decide) quadratic_degree.le))

/-- The derivative-resultant estimate applies to the same nonconstant parameter family. -/
private theorem quadraticDerivativeResultant :
    (quadratic.resultant quadratic.derivative).coeffNorm1 ≤ 31104 :=
  coeffNorm1_resultant_derivative_le quadratic quadratic_degree.le quadratic_norm

private theorem quadraticResultant : quadratic.resultant quadratic.derivative = 4 * (X - 1) := by
  have hd : quadratic.derivative = C 2 * X := by
    simp only [quadratic, derivative_add, derivative_X_sq, derivative_C, add_zero]
  have hX : quadratic.resultant X 2 1 = quadratic.coeff 0 := by
    have h := resultant_X_pow_right quadratic 2 1 quadratic_degree.le
    rw [show (X : Polynomial (Polynomial ℤ)) ^ (1 : ℕ) = X from pow_one _,
      Nat.mul_one, neg_one_sq, one_mul, pow_one] at h
    exact h
  rw [hd, quadratic_degree, natDegree_C_mul_X 2 (by norm_num), resultant_C_mul_right, hX]
  norm_num [quadratic]

/-- The derivative resultant has a positive real root at `U = 1`. -/
private theorem quadraticResultantRoot :
    (quadratic.resultant quadratic.derivative).eval₂ (Int.castRingHom ℝ) 1 = 0 := by
  rw [quadraticResultant]
  simp

/-- The computed cutoff and parameter avoid both polynomials for `Y² + U - 1`. -/
private theorem quadraticParameterExclusion :
    let u : ℝ := 2 ^ parameterExclusionExponent 2 2
    (quadratic.eval (C 8)).eval₂ (Int.castRingHom ℝ) u ≠ 0 ∧
      (quadratic.resultant quadratic.derivative).eval₂ (Int.castRingHom ℝ) u ≠ 0 := by
  have hp : quadratic ≠ 0 := by
    intro h
    have hdeg := quadratic_degree
    rw [h, natDegree_zero] at hdeg
    omega
  have hres : quadratic.resultant quadratic.derivative ≠ 0 := by
    rw [quadraticResultant]
    exact mul_ne_zero (by norm_num) (by simpa only [C_1] using X_sub_C_ne_zero (1 : ℤ))
  exact eval₂_ne_zero_at_parameterExclusion hp hres quadratic_degree.le
    (quadratic_norm.trans (by decide))

end CslibFrontierTests.RealAlgebraicCharpolyNorm
