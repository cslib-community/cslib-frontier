/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial approximation)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.DyadicSignProduct
public import CslibFrontier.Foundations.Data.Polynomial.CoeffNorm1
import Mathlib.Tactic.Ring

/-!
# Size bounds for dyadic sign products

The number of linear factors, counted with repetition, bounds the degree.
The coefficient norm is bounded by multiplying the shared dyadic bound for
the individual factors. Composition with an integer test polynomial
multiplies the degree bounds and adds the contribution of its coefficient norm.

Adapted from `RationalSignProductBounds` and `ClearedSignTestBounds` in
lean-canny at commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

open Finset

/-- The integer sign product has degree and logarithmic coefficient norm
bounded by the number of linear factors and the largest factor exponent. -/
theorem dyadicSignProduct_bounds (B s : ℕ) :
    let n := 2 * s * (2 * B + 1)
    (dyadicSignProduct B s).natDegree ≤ n ∧
      (dyadicSignProduct B s).coeffNorm1 ≤ 2 ^ (n * (2 * B + 1)) := by
  let k := 2 * B + 1
  let f (j : ℕ) : ℤ[X] := C ((2 : ℤ) ^ j) + C ((2 : ℤ) ^ B) * X
  let q := ∏ j ∈ range k, f j
  change (q ^ (2 * s)).natDegree ≤ 2 * s * k ∧
    (q ^ (2 * s)).coeffNorm1 ≤ 2 ^ (2 * s * k * k)
  have hdeg : q.natDegree ≤ k := by
    refine (natDegree_prod_le _ _).trans ?_
    calc
      _ ≤ ∑ _j ∈ range k, (1 : ℕ) := sum_le_sum fun _ _ =>
        (natDegree_add_le _ _).trans (max_le (by simp)
          ((natDegree_C_mul_le _ _).trans natDegree_X_le))
      _ = _ := by simp
  have hnorm (j : ℕ) (hj : j ∈ range k) : (f j).coeffNorm1 ≤ 2 ^ k := by
    have hj' : j ≤ 2 * B := Nat.le_of_lt_succ (mem_range.mp hj)
    have hB : B ≤ 2 * B := by omega
    unfold f
    refine (coeffNorm1_add_le _ _).trans ?_
    rw [mul_comm (C _), coeffNorm1_X_mul, coeffNorm1_C, coeffNorm1_C,
      Int.natAbs_pow, Int.natAbs_pow]
    calc
      _ ≤ 2 ^ (2 * B) + 2 ^ (2 * B) :=
        Nat.add_le_add (Nat.pow_le_pow_right (by decide) hj')
          (Nat.pow_le_pow_right (by decide) hB)
      _ = _ := by rw [show k = 2 * B + 1 from rfl, pow_succ, Nat.mul_two]
  have hq : q.coeffNorm1 ≤ 2 ^ (k * k) := by
    exact (coeffNorm1_prod_le _ _).trans ((prod_le_prod hnorm).trans_eq (by
      rw [prod_const, card_range, ← pow_mul]))
  refine ⟨natDegree_pow_le.trans (Nat.mul_le_mul_left _ hdeg), ?_⟩
  exact (coeffNorm1_pow_le _ _).trans ((Nat.pow_le_pow_left hq _).trans_eq (by
    rw [← pow_mul]
    congr 1
    ring))

/-- Composing the sign product with a bounded integer test polynomial
multiplies the degree budget and adds the test's log norm per factor. -/
theorem dyadicSignProduct_comp_bounds (B s : ℕ) (g : ℤ[X]) {D b : ℕ}
    (hD : g.natDegree ≤ D) (hb : g.coeffNorm1 ≤ 2 ^ b) :
    let n := 2 * s * (2 * B + 1)
    ((dyadicSignProduct B s).comp g).natDegree ≤ n * D ∧
      ((dyadicSignProduct B s).comp g).coeffNorm1 ≤ 2 ^ (n * (2 * B + 1 + b)) := by
  let p := dyadicSignProduct B s
  let n := 2 * s * (2 * B + 1)
  obtain ⟨hdeg, hnorm⟩ := dyadicSignProduct_bounds B s
  refine ⟨natDegree_comp_le.trans (Nat.mul_le_mul hdeg hD), ?_⟩
  calc
    _ ≤ p.coeffNorm1 * (max 1 g.coeffNorm1) ^ p.natDegree := coeffNorm1_comp_le p g
    _ ≤ 2 ^ (n * (2 * B + 1)) * (2 ^ b) ^ n := Nat.mul_le_mul hnorm
      ((Nat.pow_le_pow_left (max_le Nat.one_le_two_pow hb) _).trans
        (Nat.pow_le_pow_right Nat.one_le_two_pow hdeg))
    _ = _ := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring

end Polynomial
