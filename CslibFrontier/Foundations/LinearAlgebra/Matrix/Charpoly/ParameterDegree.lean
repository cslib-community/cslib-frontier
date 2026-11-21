/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, matrix characteristic polynomial)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Charpoly.TraceExponential
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Parameter degrees of characteristic coefficients from trace degrees

Newton's identity gives a bound on the degree in the coefficient parameter. If each
positive power trace has degree at most its exponent times `H`, then the `k`th reversed
characteristic coefficient has degree at most `k * H`.

Adapted from `NewtonDegreeBounds` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, retaining the coefficient-dependent bounds.
-/

public section

namespace Matrix

open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem natDegree_charpolyRev_coeff_le (M : Matrix ι ι (Polynomial ℤ)) (H : ℕ)
    (ht : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → ((M ^ j).trace).natDegree ≤ j * H)
    (k : ℕ) (hk : k ≤ Fintype.card ι) : (M.charpolyRev.coeff k).natDegree ≤ k * H := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    cases k with
    | zero => rw [coeff_zero_eq_eval_zero, eval_charpolyRev, natDegree_one, Nat.zero_mul]
    | succ k =>
      have hn : ((k + 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      rw [← natDegree_C_mul (p := M.charpolyRev.coeff (k + 1)) hn,
        C_eq_natCast, charpolyRev_newton, natDegree_neg]
      apply natDegree_sum_le_of_forall_le
      intro j hj
      have hjk := Finset.mem_range.mp hj
      exact natDegree_mul_le.trans
        ((Nat.add_le_add (ih (k - j) (by omega) (by omega))
          (ht (j + 1) (by omega) (by omega))).trans_eq
            (by rw [← Nat.add_mul]; congr 1; omega))

/-- The degree in the parameter of characteristic coefficient `k` is at most
`(D - k) * H` if each positive power trace through the dimension `D` has degree at
most its exponent times `H`. -/
theorem natDegree_charpoly_coeff_le_of_trace_pow (M : Matrix ι ι (Polynomial ℤ)) (H : ℕ)
    (ht : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → ((M ^ j).trace).natDegree ≤ j * H)
    (k : ℕ) : (M.charpoly.coeff k).natDegree ≤ (Fintype.card ι - k) * H := by
  by_cases hk : k ≤ Fintype.card ι
  · rw [← coeff_charpolyRev_card_sub M k hk]
    exact natDegree_charpolyRev_coeff_le M H ht _ (Nat.sub_le _ k)
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim]; omega), natDegree_zero]
    exact Nat.zero_le _

end Matrix
