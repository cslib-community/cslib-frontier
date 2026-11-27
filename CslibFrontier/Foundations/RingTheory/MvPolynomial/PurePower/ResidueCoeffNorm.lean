/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, pure-power polynomial residues)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.ParameterCoeffNorm
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.Residue
import Mathlib.Data.Fintype.BigOperators

/-!
# Coefficient norm of a pure-power residue with a polynomial parameter

For a numerator of total degree at most `B`, only terms with index sum at most `B`
contribute. If all lower relations have coefficient norm at most `R ≥ 1`, a term has
norm at most the numerator norm times `R ^ B`. The rectangular index count bounds the
number of contributions.

Adapted from `LeanCanny.CountingHierarchy.ResidueMassBounds` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, using the total-degree vanishing bound to
replace the source exponent `n * B` by `B`.
-/

public section

namespace MvPolynomial.PurePower

open scoped BigOperators

/-- Bound the coefficient norm of the actual residue by the numerator norm, the rectangular
index count, and at most `B` factors from the lower relations in each contributing term. -/
theorem coeffNorm1_residue_le {n ell B R : ℕ} (hell : 1 ≤ ell) (hR : 1 ≤ R)
    (r : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (hr : ∀ i, (r i).totalDegree < ell) (hM : ∀ i, ParameterCoeffNorm.norm (r i) ≤ R)
    (v : MvPolynomial (Fin n) (Polynomial ℤ)) (hB : v.totalDegree ≤ B) :
    Polynomial.coeffNorm1 (residue ell r v) ≤
      (B + 1) ^ n * (ParameterCoeffNorm.norm v * R ^ B) := by
  classical
  rw [residue_eq_truncated hell r hr v hB]
  change Polynomial.coeffNorm1 (∑ j ∈ indices n B, term ell r v j) ≤ _
  refine (Polynomial.coeffNorm1_sum_le _ _).trans ?_
  have hterm (j : Fin n → ℕ) : Polynomial.coeffNorm1 (term ell r v j) ≤
      ParameterCoeffNorm.norm v * R ^ B := by
    by_cases hj : (∑ i, j i) ≤ B
    · refine (ParameterCoeffNorm.coeff_le _ _).trans ((ParameterCoeffNorm.mul_le _ _).trans ?_)
      apply Nat.mul_le_mul_left
      refine (ParameterCoeffNorm.prod_le _ _).trans ?_
      calc
        _ ≤ ∏ i : Fin n, R ^ j i := Finset.prod_le_prod fun i _ =>
          (ParameterCoeffNorm.pow_le _ _).trans (Nat.pow_le_pow_left (hM i) _)
        _ = R ^ (∑ i, j i) := by rw [Finset.prod_pow_eq_pow_sum]
        _ ≤ R ^ B := Nat.pow_le_pow_right hR hj
    · rw [term_eq_zero_of_degree_lt hell r hr v j (by omega), Polynomial.coeffNorm1_zero]
      exact Nat.zero_le _
  calc
    _ ≤ ∑ _j ∈ indices n B, ParameterCoeffNorm.norm v * R ^ B :=
      Finset.sum_le_sum fun j _ => hterm j
    _ = _ := by
      simp [indices, Fintype.card_piFinset]

end MvPolynomial.PurePower
