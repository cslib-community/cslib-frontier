/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Polynomial.BivariateCoeffNorm1
public import CslibFrontier.Logics.RealArithmetic.FormulaWordValidation
public import Mathlib.Algebra.Polynomial.Bivariate
import CslibFrontier.Foundations.Data.MvPolynomial.Substitution

/-!
# Substituting bivariate coordinates into indexed formula gates

This adapts the per-gate polynomial in `LeanCanny.ETR.FormulaAtomPolynomials.family`
at lean-canny revision `970f28a5ecefc1327402ade16c068aa4b1b2c183` to the frontier term
source. Evaluating both variables recovers the original term evaluated at the specialized
coordinates. The term budget bounds both degrees of the substituted polynomial and the growth
of its coefficient norm.
-/

public section

namespace Cslib.Logic.RealArithmetic

/-- Substitute integer bivariate coordinate polynomials for the variables of an indexed
gate term. The coefficient variable is the first variable and the outer variable is the
second. -/
noncomputable def formulaWordGatePolynomial (word : List Bool) (index : ℕ)
    (coordinates : Fin word.length → Polynomial (Polynomial ℤ)) : Polynomial (Polynomial ℤ) :=
  MvPolynomial.aeval coordinates (formulaWordGateTerm word index).toPolynomial

/-- Evaluating the substituted polynomial at a real pair gives the gate term evaluated at
the corresponding real coordinates. -/
theorem aevalAeval_formulaWordGatePolynomial (word : List Bool) (index : ℕ)
    (coordinates : Fin word.length → Polynomial (Polynomial ℤ)) (x y : ℝ) :
    Polynomial.aevalAeval x y (formulaWordGatePolynomial word index coordinates) =
      (formulaWordGateTerm word index).eval
        (fun i => Polynomial.aevalAeval x y (coordinates i)) := by
  rw [formulaWordGatePolynomial, MvPolynomial.comp_aeval_apply (φ := Polynomial.aevalAeval x y),
    ← Term.eval_toPolynomial, MvPolynomial.aeval_def, algebraMap_int_eq]

/-- Substitution bounds the degree in each variable by the corresponding coordinate degree
times the formula's gate-term budget. Swapping the variables exposes the coefficient variable
as the outer variable. -/
theorem formulaWordGatePolynomial_degree_bounds (word : List Bool) (index : ℕ)
    (coordinates : Fin word.length → Polynomial (Polynomial ℤ)) {outer inner : ℕ}
    (houter : ∀ i, (coordinates i).natDegree ≤ outer)
    (hinner : ∀ i, (Polynomial.Bivariate.swap (coordinates i)).natDegree ≤ inner) :
    let budget := max word.length (encTerm 0 (.const 0)).length
    let p := formulaWordGatePolynomial word index coordinates
    p.natDegree ≤ budget * outer ∧ (Polynomial.Bivariate.swap p).natDegree ≤ budget * inner := by
  have hterm := (formulaWordGateTerm_toPolynomial_bounds word index).1
  constructor
  · exact (MvPolynomial.natDegree_aeval_le_mul houter _).trans (Nat.mul_le_mul_right _ hterm)
  · change ((Polynomial.Bivariate.swap (R := ℤ)).toAlgHom
      (MvPolynomial.aeval coordinates (formulaWordGateTerm word index).toPolynomial)).natDegree ≤ _
    rw [MvPolynomial.comp_aeval_apply]
    exact (MvPolynomial.natDegree_aeval_le_mul hinner _).trans (Nat.mul_le_mul_right _ hterm)

/-- The formula's gate-term budget bounds the coefficient norm after substitution, uniformly
over gate indices. Each coordinate must have bivariate coefficient norm at most `M ≥ 1`. -/
theorem formulaWordGatePolynomial_bivariateCoeffNorm1_le (word : List Bool) (index : ℕ)
    (coordinates : Fin word.length → Polynomial (Polynomial ℤ)) {M : ℕ} (hM : 1 ≤ M)
    (hcoordinates : ∀ i, (coordinates i).bivariateCoeffNorm1 ≤ M) :
    let budget := max word.length (encTerm 0 (.const 0)).length
    (formulaWordGatePolynomial word index coordinates).bivariateCoeffNorm1 ≤ (2 * M) ^ budget := by
  intro budget
  obtain ⟨hdegree, hnorm⟩ := formulaWordGateTerm_toPolynomial_bounds word index
  rw [formulaWordGatePolynomial, mul_pow]
  exact (Polynomial.bivariateCoeffNorm1_aeval_le _ coordinates hM hcoordinates).trans
    (Nat.mul_le_mul hnorm (Nat.pow_le_pow_right hM hdegree))

end Cslib.Logic.RealArithmetic
