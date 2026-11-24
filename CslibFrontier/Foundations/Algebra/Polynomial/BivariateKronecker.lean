/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, bivariate polynomial coefficient recovery)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Bivariate
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Recovering bivariate coefficients after Kronecker substitution

Substituting `X ^ radix` for the outer variable packs the two indices into one exponent.
If the inner degree is strictly below `radix`, the coefficient at `i + radix * j`
recovers the coefficient at inner degree `i` and outer degree `j`.
This adapts `LeanCanny.Algebra.PolynomialKronecker.coefficient` from lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183` using the ordinary polynomial evaluation API.
-/

public section

namespace Polynomial.Bivariate

open scoped Polynomial.Bivariate

/-- Kronecker substitution recovers the original coefficient at inner index `i`
and outer index `j` when both `i` and the inner degree are strictly below the radix. -/
theorem coeff_eval_X_pow {R : Type*} [CommSemiring R] (p : R[X][Y]) {radix : ℕ}
    (hdegree : (swap p).natDegree < radix) (i j : ℕ) (hi : i < radix) :
    (p.eval (X ^ radix)).coeff (i + radix * j) = (p.coeff j).coeff i := by
  rw [eval_eq_sum_range]
  simp only [← pow_mul, finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · exact coeff_mul_X_pow (p.coeff j) (radix * j) i
  · intro k _ hkj
    rcases Nat.lt_or_gt_of_ne hkj with hk | hk
    · have hgap : radix * k + radix ≤ radix * j := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left radix (Nat.succ_le_of_lt hk)
      rw [coeff_mul_X_pow', ite_eq_left (by omega), ← coeff_coeff_swap,
        coeff_eq_zero_of_natDegree_lt (hdegree.trans_le (by omega)), coeff_zero]
    · have hgap : radix * j + radix ≤ radix * k := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left radix (Nat.succ_le_of_lt hk)
      rw [coeff_mul_X_pow', ite_eq_right (by omega)]
  · intro hj
    have h : p.natDegree < j := by
      simp only [Finset.mem_range] at hj
      omega
    rw [coeff_eq_zero_of_natDegree_lt h, zero_mul, coeff_zero]

/-- The packed degree is at most the inner degree plus the radix times the outer degree. -/
theorem natDegree_eval_X_pow_le {R : Type*} [CommSemiring R] (p : R[X][Y]) (radix : ℕ) :
    (p.eval (X ^ radix)).natDegree ≤ (swap p).natDegree + radix * p.natDegree := by
  rw [eval_eq_sum_range]
  simp only [← pow_mul]
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => natDegree_mul_le.trans ?_
  exact Nat.add_le_add (natDegree_coeff_le_natDegree_swap p k) ((natDegree_X_pow_le _).trans
    (Nat.mul_le_mul_left radix (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))

/-- Evaluating the packed polynomial at `z` evaluates the bivariate polynomial
at `z` and `z ^ radix`. -/
theorem aeval_eval_X_pow {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (p : R[X][Y]) (radix : ℕ) (z : A) :
    aeval z (p.eval (X ^ radix)) = aevalAeval z (z ^ radix) p := by
  let specialize : R[X][Y] →ₐ[R] R[X] :=
    (aeval (R := R[X]) (X ^ radix)).restrictScalars R
  change ((aeval z).comp specialize) p = _
  congr 1
  apply algHom_ext'
  · ext
    simp [specialize]
  · simp [specialize]

end Polynomial.Bivariate
