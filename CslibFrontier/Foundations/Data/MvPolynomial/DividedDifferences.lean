/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/MvPolynomial/DividedDifferences`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# Polynomial divided differences

Every polynomial of total degree at most `d + 1` has polynomial divided differences of
total degree at most `d`: they express `p(x) - p(X)` as a sum of coordinate differences,
and evaluate to the partial derivatives on the diagonal. This holds over an arbitrary
commutative coefficient ring. `purePowerDifference` supplies the explicit geometric sum
for a pure power, including its leading term and diagonal evaluation.

Ported and simplified from the
[polynomial divided differences](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/PolynomialDifference.lean)
and
[pure-power differences](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/PurePowerDifference.lean)
in lean-canny. Finsupp subtraction supplies the monomial step and Mathlib's geometric-sum
identity supplies the pure-power quotient.
-/

public section

namespace MvPolynomial

open scoped BigOperators

variable {A : Type*} [CommRing A] {n : ℕ}

/-- Monomials admit polynomial divided differences, with their expected
 degree and derivative on the diagonal, over every commutative ring. -/
private theorem monomial_divided_differences (x : Fin n → A) (e : Fin n →₀ ℕ) (a : A) :
    ∃ d : Fin n → MvPolynomial (Fin n) A,
      C (eval x (monomial e a)) - monomial e a =
        ∑ i, d i * (C (x i) - X i) ∧
      (∀ i, (d i).totalDegree ≤ e.degree - 1) ∧
      (e.degree = 0 → ∀ i, d i = 0) ∧
      (∀ i, eval x (d i) = eval x (pderiv i (monomial e a))) := by
  classical
  by_cases he0 : e = 0
  · subst e
    exact ⟨fun _ => 0, by simp, by simp, by simp, by simp⟩
  · obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he0
    have hi : e i ≠ 0 := by simpa only [Finsupp.zero_apply] using hi
    let e' := e - Finsupp.single i 1
    have hres : e' + Finsupp.single i 1 = e := Finsupp.sub_add_single_one_cancel hi
    have hdeg : e'.degree + 1 = e.degree := by
      simpa only [map_add, Finsupp.degree_single] using congrArg Finsupp.degree hres
    have hlt : e'.degree < e.degree := by omega
    obtain ⟨d, hd, hbound, hzero, hdiag⟩ := monomial_divided_differences x e' a
    let q : MvPolynomial (Fin n) A := monomial e' a
    have hq : q * X i = monomial e a := by rw [← pow_one (X i), ← monomial_add_single, hres]
    let D : Fin n → MvPolynomial (Fin n) A := fun j =>
      d j * X i + if j = i then C (eval x q) else 0
    refine ⟨D, ?_, fun j => ?_, fun hz => by omega, fun j => ?_⟩
    · have hsum : (∑ j, D j * (C (x j) - X j)) =
          (∑ j, d j * (C (x j) - X j)) * X i + C (eval x q) * (C (x i) - X i) := by
        simp only [D, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte, Finset.sum_mul]
        exact congrArg (· + _) (Finset.sum_congr rfl fun _ _ => by ring)
      rw [hsum, ← hd, ← hq, map_mul, eval_X, map_mul]
      change C (eval x q) * C (x i) - q * X i = _; ring
    · have hX : (X i : MvPolynomial (Fin n) A).totalDegree ≤ 1 := totalDegree_X_le i
      have hC :
          (if j = i then C (eval x q) else (0 : MvPolynomial (Fin n) A)).totalDegree = 0 := by
        split_ifs <;> simp
      have hb : (d j * X i).totalDegree ≤ e'.degree := by
        by_cases hz : e'.degree = 0
        · simp [hzero hz j]
        · have := totalDegree_mul (d j) (X i)
          have := hbound j; omega
      exact (totalDegree_add _ _).trans (by rw [hC]; omega)
    · rw [← hq, pderiv_mul]
      simp only [D, map_add, map_mul, eval_X, hdiag]
      by_cases hj : j = i
      · subst j; simp [q]
      · simp [q, hj, Ne.symm hj]
termination_by e.degree
decreasing_by exact hlt

/-- Every polynomial of degree at most `d + 1` has divided differences of
 degree at most `d`, including over rings with zero divisors. -/
theorem polynomial_divided_differences (x : Fin n → A)
    (p : MvPolynomial (Fin n) A) (d : ℕ) (hp : p.totalDegree ≤ d + 1) :
    ∃ D : Fin n → MvPolynomial (Fin n) A,
      C (eval x p) - p = ∑ i, D i * (C (x i) - X i) ∧
      (∀ i, (D i).totalDegree ≤ d) ∧
      (∀ i, eval x (D i) = eval x (pderiv i p)) := by
  classical
  choose D hdiff hdeg _ hdiag using
    (fun e : Fin n →₀ ℕ => monomial_divided_differences x e (p.coeff e))
  refine ⟨fun i => ∑ e ∈ p.support, D e i, ?_,
    fun i => totalDegree_finsetSum_le fun e he => (hdeg e i).trans
      (by have : e.degree ≤ p.totalDegree := le_totalDegree he; omega), fun i => ?_⟩
  · calc
      C (eval x p) - p =
          ∑ e ∈ p.support, (C (eval x (monomial e (p.coeff e))) -
            monomial e (p.coeff e)) := by
        conv_lhs => rw [p.as_sum]
        simp only [map_sum, Finset.sum_sub_distrib]
      _ = ∑ i, (∑ e ∈ p.support, D e i) * (C (x i) - X i) := by
        simp_rw [hdiff]
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
  · rw [map_sum]; simp_rw [hdiag]
    conv_rhs => rw [p.as_sum]
    simp only [map_sum]

/-- The polynomial quotient of `x^ell - Y^ell` by `x - Y`, with
 `ell = d + 1`. -/
noncomputable def purePowerDifference (x : A) (i : Fin n) (d : ℕ) :
    MvPolynomial (Fin n) A :=
  ∑ k ∈ Finset.range (d + 1), C (x ^ (d - k)) * X i ^ k

theorem purePowerDifference_mul (x : A) (i : Fin n) (d : ℕ) :
    purePowerDifference x i d * (C x - X i) = C (x ^ (d + 1)) - X i ^ (d + 1) := by
  classical
  have h := (Commute.all (X i : MvPolynomial (Fin n) A) (C x)).mul_neg_geom_sum₂ (d + 1)
  have heq : (∑ k ∈ Finset.range (d + 1), X i ^ k * C x ^ (d + 1 - 1 - k)) =
      purePowerDifference x i d := by
    simp only [purePowerDifference, Nat.add_sub_cancel, ← map_pow, mul_comm]
  rw [heq, ← map_pow] at h
  simpa only [mul_comm] using h

theorem purePowerDifference_degree (x : A) (i : Fin n) (d : ℕ) :
    (purePowerDifference x i d).totalDegree ≤ d := by
  classical
  refine totalDegree_finsetSum_le fun k hk => ?_
  rw [C_mul_X_pow_eq_monomial]
  have := Finset.mem_range.mp hk
  exact (totalDegree_monomial_le _ _).trans (by simp; omega)

theorem purePowerDifference_lower_degree (x : A) (i : Fin n) {d : ℕ} (hd : 1 ≤ d) :
    (purePowerDifference x i d - X i ^ d).totalDegree < d := by
  classical
  rw [show purePowerDifference x i d - X i ^ d =
      ∑ k ∈ Finset.range d, C (x ^ (d - k)) * X i ^ k by
    simp only [purePowerDifference, Finset.sum_range_succ, Nat.sub_self, pow_zero,
      C_1, one_mul, add_sub_cancel_right]]
  refine lt_of_le_of_lt (totalDegree_finsetSum_le (d := d - 1) fun k hk => ?_) (by omega)
  rw [C_mul_X_pow_eq_monomial]
  have := Finset.mem_range.mp hk
  exact (totalDegree_monomial_le _ _).trans (by simp; omega)

theorem purePowerDifference_diagonal (x : Fin n → A) (i : Fin n) (d : ℕ) :
    eval x (purePowerDifference (x i) i d) = (d + 1 : ℕ) * x i ^ d := by
  classical
  rw [purePowerDifference, map_sum, Finset.sum_congr rfl fun k hk => (?_ : _ = x i ^ d),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [map_mul, eval_C, map_pow, eval_X, ← pow_add]
  have := Finset.mem_range.mp hk
  exact congrArg _ (by omega)

end MvPolynomial
