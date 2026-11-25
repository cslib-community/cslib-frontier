/-
Copyright (c) 2026 Samuel Schlesinger, Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Anton Kovsharov
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Foundations.Data.Polynomial.CoeffSumBounds
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The `ℓ₁` coefficient norm of an integer polynomial

This module defines the `ℓ₁` coefficient norm `Polynomial.coeffNorm1` of a univariate integer
polynomial `p : ℤ[X]`:
$$\|p\|_1 = \sum_{i \in \mathrm{supp}(p)} |p_i|,$$
together with its basic triangle, scaling, shift, linear-factor, submultiplicative, and
integer-cast inequalities used in Lemma 4.6, Lemma 5.1, and Appendix B of `[OpenAI2026ETH]`.

## Main definitions

* `Polynomial.coeffNorm1`: the `ℓ₁` coefficient norm `∑ i ∈ p.support, (p.coeff i).natAbs`.

## Main results

* `Polynomial.natAbs_coeff_le_coeffNorm1`, `Polynomial.sum_natAbs_coeff_le_coeffNorm1`:
  individual and finite-subset coefficient bounds by `coeffNorm1`.
* `Polynomial.coeffNorm1_add_le`, `Polynomial.coeffNorm1_sub_le`, `Polynomial.coeffNorm1_sum_le`:
  triangle inequalities for binary sums, differences, and finite sums.
* `Polynomial.coeffNorm1_C_mul_le`, `Polynomial.coeffNorm1_X_mul`,
  `Polynomial.coeffNorm1_mul_X_pow_le`, `Polynomial.coeffNorm1_C_sub_X_mul_le`,
  `Polynomial.coeffNorm1_one_sub_X_mul_le`, `Polynomial.coeffNorm1_one_sub_X_pow_mul_le`:
  norm bounds under scalar multiplication, monomial shifts, and linear factors.
* `Polynomial.coeffNorm1_mul_le`, `Polynomial.coeffNorm1_pow_le`, `Polynomial.coeffNorm1_prod_le`:
  submultiplicativity for binary products, powers, and finite products.
* `Polynomial.natCast_coeffNorm1`: integer cast identity
  `(p.coeffNorm1 : ℤ) = ∑ i ∈ p.support, |p.coeff i|`.
* `Polynomial.coeffNorm1_ofCoeffList`: `coeffNorm1 (ofCoeffList l) = (l.map Int.natAbs).sum`.
* `Polynomial.coeffNorm1_derivative_le`, `Polynomial.coeffNorm1_iterate_derivative_le_two_pow`:
  norm bounds for derivatives, including one dyadic bound for every order.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
  (Lemma 4.6, Appendix B.1, and Appendix B.2)

The derivative bounds are adapted from `DerivativeProductBounds` and `DerivativeTestBounds`
in lean-canny at commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

@[expose] public noncomputable section

namespace Polynomial

open Finset

/-- The `ℓ₁` coefficient norm `∑ i ∈ p.support, (p.coeff i).natAbs` of an integer polynomial. -/
def coeffNorm1 (p : ℤ[X]) : ℕ :=
  ∑ i ∈ p.support, (p.coeff i).natAbs

/-- The `ℓ₁` norm of `0` is `0`. -/
@[simp]
theorem coeffNorm1_zero : coeffNorm1 0 = 0 := by
  simp only [coeffNorm1, support_zero, sum_empty]

/-- Sum expression for `coeffNorm1` over any superset `S ⊇ p.support`. -/
theorem coeffNorm1_eq_sum_of_support_subset {p : ℤ[X]} {S : Finset ℕ} (hS : p.support ⊆ S) :
    coeffNorm1 p = ∑ i ∈ S, (p.coeff i).natAbs :=
  sum_eq_of_subset _ (fun _ => Int.natAbs_zero) hS

/-- Reversing the coefficients preserves the coefficient norm. -/
theorem coeffNorm1_reverse (p : ℤ[X]) : p.reverse.coeffNorm1 = p.coeffNorm1 := by
  rw [coeffNorm1, reverse, reflect_support, sum_image (revAt _).injective.injOn]
  simp only [coeff_reflect, revAt_invol, coeffNorm1]

/-- Multiplication by a natural scalar scales the coefficient norm exactly. -/
theorem coeffNorm1_nsmul (k : ℕ) (p : ℤ[X]) : coeffNorm1 (k • p) = k * coeffNorm1 p := by
  rw [coeffNorm1_eq_sum_of_support_subset (support_smul k p), coeffNorm1, Finset.mul_sum]
  simp only [nsmul_eq_mul, ← C_eq_natCast, coeff_C_mul, Int.natAbs_mul, Int.natAbs_natCast]

/-- Every individual coefficient of `p` has absolute value at most `coeffNorm1 p`. -/
theorem natAbs_coeff_le_coeffNorm1 (p : ℤ[X]) (k : ℕ) :
    (p.coeff k).natAbs ≤ coeffNorm1 p := by
  by_cases hk : k ∈ p.support
  · exact single_le_sum (f := fun i => (p.coeff i).natAbs) (fun _ _ => Nat.zero_le _) hk
  · rw [notMem_support_iff.mp hk, Int.natAbs_zero]
    exact Nat.zero_le _

/-- The sum of `(p.coeff i).natAbs` over any finite set of indices is at most `coeffNorm1 p`. -/
theorem sum_natAbs_coeff_le_coeffNorm1 (p : ℤ[X]) (s : Finset ℕ) :
    ∑ i ∈ s, (p.coeff i).natAbs ≤ coeffNorm1 p := by
  have hsub : ∑ i ∈ s, (p.coeff i).natAbs = ∑ i ∈ s ∩ p.support, (p.coeff i).natAbs := by
    refine (sum_subset inter_subset_left ?_).symm
    intro i hi his
    rw [mem_inter, not_and_or, notMem_support_iff] at his
    rcases his with hns | hp0
    · exact absurd hi hns
    · simp only [hp0, Int.natAbs_zero]
  rw [hsub, coeffNorm1]
  exact sum_le_sum_of_subset inter_subset_right

/-- Differentiation increases the coefficient norm by at most a factor of the degree. -/
theorem coeffNorm1_derivative_le (p : ℤ[X]) :
    p.derivative.coeffNorm1 ≤ p.natDegree * p.coeffNorm1 := by
  let shift : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩
  calc
    p.derivative.coeffNorm1 ≤ ∑ i ∈ p.derivative.support,
        (p.coeff (i + 1)).natAbs * p.natDegree := by
      refine sum_le_sum fun i hi => ?_
      simp only [coeff_derivative, Int.natAbs_mul, ← Nat.cast_succ, Int.natAbs_natCast]
      exact Nat.mul_le_mul_left _ (le_natDegree_of_mem_supp _ (of_mem_support_derivative hi))
    _ = (∑ i ∈ p.derivative.support.map shift, (p.coeff i).natAbs) * p.natDegree := by
      rw [sum_mul, sum_map]
      rfl
    _ ≤ p.natDegree * p.coeffNorm1 := by
      rw [mul_comm p.natDegree]
      exact Nat.mul_le_mul_right _ (sum_natAbs_coeff_le_coeffNorm1 p _)

/-- A common base-two coefficient norm exponent for all derivatives of a polynomial
with degree at most `D` and coefficient norm at most `2 ^ b`. -/
def iterateDerivativeNormExponent (D b : ℕ) : ℕ := b + D.size * D

/-- The same dyadic norm bound holds at every derivative order, including order zero
and orders above the degree. -/
theorem coeffNorm1_iterate_derivative_le_two_pow (p : ℤ[X]) {D b : ℕ}
    (hD : p.natDegree ≤ D) (hb : p.coeffNorm1 ≤ 2 ^ b) (k : ℕ) :
    (derivative^[k] p).coeffNorm1 ≤ 2 ^ iterateDerivativeNormExponent D b := by
  have hiter (j : ℕ) : (derivative^[j] p).coeffNorm1 ≤ D ^ j * p.coeffNorm1 := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', pow_succ']
      have hdeg := (natDegree_iterate_derivative p j).trans ((Nat.sub_le _ _).trans hD)
      exact (coeffNorm1_derivative_le _).trans
        ((Nat.mul_le_mul hdeg ih).trans_eq (Nat.mul_assoc _ _ _).symm)
  by_cases hk : k ≤ D
  · refine (hiter k).trans ((Nat.mul_le_mul (Nat.pow_le_pow_left D.lt_size_self.le k) hb).trans ?_)
    rw [← pow_mul, ← pow_add, iterateDerivativeNormExponent, add_comm b]
    exact Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right (Nat.mul_le_mul_left _ hk) _)
  · rw [iterate_derivative_eq_zero (hD.trans_lt (Nat.lt_of_not_ge hk)), coeffNorm1_zero]
    exact Nat.zero_le _

/-- The `ℓ₁` norm of a constant polynomial `C a` is `a.natAbs`. -/
theorem coeffNorm1_C (a : ℤ) : coeffNorm1 (C a) = a.natAbs := by
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero, coeffNorm1_zero, Int.natAbs_zero]
  · rw [coeffNorm1, support_C ha, sum_singleton, coeff_C_zero]

/-- The `ℓ₁` norm of `1` is `1`. -/
@[simp]
theorem coeffNorm1_one : coeffNorm1 1 = 1 := by
  rw [← C_1, coeffNorm1_C, Int.natAbs_one]

/-- Negating a polynomial preserves `coeffNorm1`. -/
@[simp]
theorem coeffNorm1_neg (p : ℤ[X]) : coeffNorm1 (-p) = coeffNorm1 p := by
  rw [coeffNorm1_eq_sum_of_support_subset (S := p.support) (by simp), coeffNorm1]
  refine sum_congr rfl fun i _ => ?_
  rw [coeff_neg, Int.natAbs_neg]

/-- Triangle inequality for `coeffNorm1`. -/
theorem coeffNorm1_add_le (p q : ℤ[X]) :
    coeffNorm1 (p + q) ≤ coeffNorm1 p + coeffNorm1 q :=
  sum_add_le_of_subadditive Int.natAbs_zero Int.natAbs_add_le p q

/-- Difference triangle inequality for `coeffNorm1`. -/
theorem coeffNorm1_sub_le (p q : ℤ[X]) :
    coeffNorm1 (p - q) ≤ coeffNorm1 p + coeffNorm1 q := by
  rw [sub_eq_add_neg, ← coeffNorm1_neg q]
  exact coeffNorm1_add_le p (-q)

/-- Finite-sum triangle inequality for `coeffNorm1`. -/
theorem coeffNorm1_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) :
    coeffNorm1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coeffNorm1 (f i) :=
  le_sum_of_subadditive coeffNorm1 coeffNorm1_zero.le coeffNorm1_add_le s f

/-- `coeffNorm1` is submultiplicative on `ℤ[X]`. -/
theorem coeffNorm1_mul_le (p q : ℤ[X]) :
    coeffNorm1 (p * q) ≤ coeffNorm1 p * coeffNorm1 q :=
  sum_mul_le_of_submultiplicative Int.natAbs_zero Int.natAbs_add_le
    (fun a b => (Int.natAbs_mul a b).le) p q

/-- Scaling by `C a` scales `coeffNorm1` by at most `a.natAbs`. -/
theorem coeffNorm1_C_mul_le (a : ℤ) (p : ℤ[X]) :
    coeffNorm1 (C a * p) ≤ a.natAbs * coeffNorm1 p :=
  coeffNorm1_C a ▸ coeffNorm1_mul_le (C a) p

/-- Multiplying by `X` preserves `coeffNorm1`. -/
theorem coeffNorm1_X_mul (p : ℤ[X]) : coeffNorm1 (X * p) = coeffNorm1 p := by
  let S := p.support.map ⟨Nat.succ, Nat.succ_injective⟩
  have hsub : (X * p).support ⊆ S := by
    intro i hi
    rw [mem_support_iff] at hi
    rcases i with _ | i
    · rw [mul_comm, coeff_mul_X_zero] at hi
      exact (hi rfl).elim
    · rw [mul_comm, coeff_mul_X] at hi
      exact mem_map.mpr ⟨i, mem_support_iff.mpr hi, rfl⟩
  rw [coeffNorm1_eq_sum_of_support_subset hsub, sum_map, coeffNorm1]
  refine sum_congr rfl fun i _ => ?_
  change ((X * p).coeff (i + 1)).natAbs = (p.coeff i).natAbs
  rw [mul_comm, coeff_mul_X]

/-- The variable has coefficient norm one. -/
@[simp] theorem coeffNorm1_X : coeffNorm1 (X : ℤ[X]) = 1 := by
  simpa only [mul_one, coeffNorm1_one] using coeffNorm1_X_mul (1 : ℤ[X])

/-- Multiplying by `X ^ k` does not increase `coeffNorm1`. -/
theorem coeffNorm1_mul_X_pow_le (p : ℤ[X]) (k : ℕ) :
    coeffNorm1 (p * X ^ k) ≤ coeffNorm1 p := by
  have hX : coeffNorm1 (X ^ k) = 1 := by
    rw [X_pow_eq_monomial, coeffNorm1, support_monomial k one_ne_zero, sum_singleton,
      coeff_monomial_same, Int.natAbs_one]
  simpa only [hX, mul_one] using coeffNorm1_mul_le p (X ^ k)

/-- Multiplying by `C a - X` scales `coeffNorm1` by at most `a.natAbs + 1`. -/
theorem coeffNorm1_C_sub_X_mul_le (a : ℤ) (p : ℤ[X]) :
    coeffNorm1 ((C a - X) * p) ≤ (a.natAbs + 1) * coeffNorm1 p := by
  rw [sub_mul, add_one_mul]
  have h1 := coeffNorm1_sub_le (C a * p) (X * p)
  rw [coeffNorm1_X_mul] at h1
  exact h1.trans (Nat.add_le_add_right (coeffNorm1_C_mul_le a p) _)

/-- Multiplying by `1 - X` increases `coeffNorm1` by at most a factor of `2`. -/
theorem coeffNorm1_one_sub_X_mul_le (p : ℤ[X]) :
    coeffNorm1 ((1 - X) * p) ≤ 2 * coeffNorm1 p := by
  simpa only [C_1, Int.natAbs_one, Nat.reduceAdd] using coeffNorm1_C_sub_X_mul_le 1 p

/-- Multiplying by `(1 - X) ^ ℓ` increases `coeffNorm1` by at most a factor of `2 ^ ℓ`. -/
theorem coeffNorm1_one_sub_X_pow_mul_le (ℓ : ℕ) (p : ℤ[X]) :
    coeffNorm1 ((1 - X) ^ ℓ * p) ≤ 2 ^ ℓ * coeffNorm1 p := by
  induction ℓ with
  | zero => simp only [pow_zero, one_mul, le_refl]
  | succ ℓ ih =>
    have hEq : (1 - X) ^ (ℓ + 1) * p = (1 - X) * ((1 - X) ^ ℓ * p) := by ring
    rw [hEq, pow_succ', mul_assoc]
    exact (coeffNorm1_one_sub_X_mul_le _).trans (Nat.mul_le_mul_left 2 ih)

/-- `coeffNorm1 (p ^ k) ≤ coeffNorm1 p ^ k`. -/
theorem coeffNorm1_pow_le (p : ℤ[X]) (k : ℕ) :
    coeffNorm1 (p ^ k) ≤ coeffNorm1 p ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, coeffNorm1_one, le_refl]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (coeffNorm1_mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

/-- `coeffNorm1` of a finite product is at most the product of the `coeffNorm1`s. -/
theorem coeffNorm1_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) :
    coeffNorm1 (∏ a ∈ s, f a) ≤ ∏ a ∈ s, coeffNorm1 (f a) :=
  le_prod_of_submultiplicative coeffNorm1 coeffNorm1_one.le coeffNorm1_mul_le s f

/-- Composition grows the coefficient norm by at most the inner norm to the
outer degree, with the inner norm rounded up to one to include zero. -/
theorem coeffNorm1_comp_le (p q : ℤ[X]) :
    (p.comp q).coeffNorm1 ≤ p.coeffNorm1 * (max 1 q.coeffNorm1) ^ p.natDegree := by
  rw [comp_eq_sum_left, Polynomial.sum]
  refine (coeffNorm1_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ p.support, (p.coeff i).natAbs * (max 1 q.coeffNorm1) ^ p.natDegree := by
      refine sum_le_sum fun i hi => (coeffNorm1_C_mul_le _ _).trans (Nat.mul_le_mul_left _ ?_)
      exact (coeffNorm1_pow_le q i).trans
        ((Nat.pow_le_pow_left (le_max_right 1 q.coeffNorm1) i).trans
          (Nat.pow_le_pow_right (le_max_left 1 q.coeffNorm1) (le_natDegree_of_mem_supp i hi)))
    _ = _ := by simp only [coeffNorm1, sum_mul]

/-- Evaluation at a nonzero integer is bounded by the coefficient norm times the
absolute value of the integer raised to the degree. -/
theorem natAbs_eval_le_coeffNorm1 (p : ℤ[X]) (a : ℤ) (ha : 1 ≤ a.natAbs) :
    (p.eval a).natAbs ≤ p.coeffNorm1 * a.natAbs ^ p.natDegree := by
  simpa only [comp_C, coeffNorm1_C, max_eq_right ha] using coeffNorm1_comp_le p (C a)

/-- Casting `coeffNorm1 p` to `ℤ` gives the sum of integer absolute values `|p.coeff i|`. -/
theorem natCast_coeffNorm1 (p : ℤ[X]) :
    (coeffNorm1 p : ℤ) = ∑ i ∈ p.support, |p.coeff i| := by
  unfold coeffNorm1
  rw [Nat.cast_sum]
  refine sum_congr rfl fun i _ => Int.natCast_natAbs (p.coeff i)

/-- Integer-cast constant norm `(coeffNorm1 (C a) : ℤ) = |a|`. -/
theorem natCast_coeffNorm1_C (a : ℤ) : (coeffNorm1 (C a) : ℤ) = |a| := by
  rw [coeffNorm1_C, Int.natCast_natAbs]

/-- Integer-cast triangle inequality for `coeffNorm1`. -/
theorem natCast_coeffNorm1_add_le (p q : ℤ[X]) :
    (coeffNorm1 (p + q) : ℤ) ≤ (coeffNorm1 p : ℤ) + (coeffNorm1 q : ℤ) := by
  exact_mod_cast coeffNorm1_add_le p q

/-- Integer-cast finite-sum triangle inequality for `coeffNorm1`. -/
theorem natCast_coeffNorm1_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) :
    (coeffNorm1 (∑ i ∈ s, f i) : ℤ) ≤ ∑ i ∈ s, (coeffNorm1 (f i) : ℤ) := by
  rw [← Nat.cast_sum]
  exact_mod_cast coeffNorm1_sum_le s f

/-- Integer-cast scalar multiplication bound for `coeffNorm1`. -/
theorem natCast_coeffNorm1_C_mul_le (a : ℤ) (p : ℤ[X]) :
    (coeffNorm1 (C a * p) : ℤ) ≤ |a| * (coeffNorm1 p : ℤ) := by
  rw [← Int.natCast_natAbs, ← Nat.cast_mul]
  exact_mod_cast coeffNorm1_C_mul_le a p

/-- The `ℓ₁` coefficient norm of `ofCoeffList l` equals the sum of `Int.natAbs` of `l`. -/
@[simp]
theorem coeffNorm1_ofCoeffList (l : List ℤ) :
    coeffNorm1 (ofCoeffList l) = (l.map Int.natAbs).sum := by
  have hsub : (ofCoeffList l).support ⊆ range l.length := fun i hi =>
    mem_range.2 <| by
      by_contra hge
      exact (mem_support_iff.1 hi)
        (by rw [coeff_ofCoeffList, List.getD_eq_default l 0 (by omega)])
  rw [coeffNorm1_eq_sum_of_support_subset hsub,
    ← Fin.sum_univ_eq_sum_range (fun i => ((ofCoeffList l).coeff i).natAbs),
    ← List.sum_map_range l.length (fun i => ((ofCoeffList l).coeff i).natAbs)]
  congr 1; apply List.ext_getElem (by simp only [List.length_map, List.length_range])
  intro i hi₁ _
  have hi : i < l.length := by simpa only [List.length_map, List.length_range] using hi₁
  simp only [List.getElem_map, List.getElem_range, coeff_ofCoeffList, List.getD_eq_getElem l 0 hi]

end Polynomial
