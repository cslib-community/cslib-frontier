/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Local multiplication for the contraction trinomial

The ordinary product of two operands of degree below `2q` has degree below `4q`. Reducing
modulo `X^(2q) + X^q + 1` recovers any desired low coefficient from at most three coefficients
of this product. The formula works over `ZMod (2^p)` at any positive precision.
-/

public section
namespace Cslib.SparseTrinomial

open Polynomial

/-- Combine the two or three coefficients of an ordinary convolution that contribute to the
specified coordinate after trinomial reduction. -/
@[expose] def reducedCoeff {R : Type*} [Ring R] (q : ℕ) (c : ℕ → R) (i : ℕ) : R :=
  if i < q then c i - c (i + 2 * q) + c (i + 3 * q) else c i - c (i + q)

/-- A degree-bounded product has a sparse coefficient formula modulo the contraction trinomial.
The low and high halves use different indices because `X^(3q) = 1` in the quotient. -/
theorem coeff_mod_sparse {R : Type*} [CommRing R] [Nontrivial R] (q : ℕ) (hq : 0 < q)
    (P : R[X]) (hP : P.natDegree < 4 * q) (i : ℕ) (hi : i < 2 * q) :
    (P %ₘ (X ^ (2 * q) + X ^ q + 1)).coeff i = reducedCoeff q P.coeff i := by
  let f : R[X] := X ^ (2 * q) + X ^ q + 1
  let r := P %ₘ f
  let d := P /ₘ f
  have hl : (X ^ q + 1 : R[X]).degree < (2 * q : ℕ) := by
    have ha : (X ^ q + 1 : R[X]).degree = q := by
      simpa only [map_one] using degree_X_pow_add_C (R := R) (a := (1 : R)) hq
    rw [ha]
    exact_mod_cast (show q < 2 * q by omega)
  have hm : f.Monic := by
    dsimp [f]
    rw [add_assoc]
    exact monic_X_pow_add hl
  have hdeg : f.degree = (2 * q : ℕ) := by
    dsimp [f]
    rw [add_assoc, degree_add_eq_left_of_degree_lt, degree_X_pow]
    simpa only [degree_X_pow] using hl
  have hnat : f.natDegree = 2 * q := natDegree_eq_of_degree_eq_some hdeg
  have hr (j : ℕ) (hj : 2 * q ≤ j) : r.coeff j = 0 :=
    coeff_eq_zero_of_degree_lt ((degree_modByMonic_lt P hm).trans_le (hdeg ▸ by exact_mod_cast hj))
  have hd (j : ℕ) (hj : 2 * q ≤ j) : d.coeff j = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    dsimp [d]
    rw [natDegree_divByMonic _ hm, hnat]
    omega
  have hc (j : ℕ) : r.coeff j + (((if 2 * q ≤ j then d.coeff (j - 2 * q) else 0) +
      (if q ≤ j then d.coeff (j - q) else 0)) + d.coeff j) = P.coeff j := by
    have h := congrArg (fun t : R[X] => t.coeff j) (modByMonic_add_div P f)
    change (r + f * d).coeff j = P.coeff j at h
    rwa [show f * d = d * X ^ (2 * q) + d * X ^ q + d by dsimp [f]; ring,
      coeff_add, coeff_add, coeff_add, coeff_mul_X_pow', coeff_mul_X_pow'] at h
  change r.coeff i = _
  by_cases hilo : i < q
  · have h0 := hc i
    have h2 := hc (i + 2 * q)
    have h3 := hc (i + 3 * q)
    simp only [ite_eq_right (show ¬2 * q ≤ i by omega), ite_eq_right (by omega : ¬q ≤ i),
      zero_add] at h0
    simp only [ite_eq_left (show 2 * q ≤ i + 2 * q by omega),
      ite_eq_left (show q ≤ i + 2 * q by omega),
      hr (i + 2 * q) (by omega), hd (i + 2 * q) (by omega), Nat.add_sub_cancel,
      show i + 2 * q - q = i + q by omega,
      zero_add, add_zero] at h2
    simp only [ite_eq_left (show 2 * q ≤ i + 3 * q by omega),
      ite_eq_left (show q ≤ i + 3 * q by omega),
      hr (i + 3 * q) (by omega), hd (i + 3 * q) (by omega), hd (i + 2 * q) (by omega),
      show i + 3 * q - 2 * q = i + q by omega,
      show i + 3 * q - q = i + 2 * q by omega, zero_add, add_zero] at h3
    rw [reducedCoeff, ite_eq_left hilo, ← h0, ← h2, ← h3]
    abel
  · have h0 := hc i
    have h1 := hc (i + q)
    simp only [ite_eq_right (show ¬2 * q ≤ i by omega), ite_eq_left (show q ≤ i by omega),
      zero_add] at h0
    simp only [ite_eq_left (show 2 * q ≤ i + q by omega), ite_eq_left (show q ≤ i + q by omega),
      hr (i + q) (by omega), hd (i + q) (by omega), Nat.add_sub_cancel,
      show i + q - 2 * q = i - q by omega,
      zero_add, add_zero] at h1
    rw [reducedCoeff, ite_eq_right hilo, ← h0, ← h1]
    abel

/-- One ordinary convolution coefficient as an inner product with a zero-padded second operand.
The summation has the operand width, independently of the requested convolution index. -/
theorem coeff_mul_eq_inner {R : Type*} [CommRing R] {width : ℕ} (u v : R[X])
    (hu : u.natDegree < width) (k : ℕ) :
    (u * v).coeff k = ∑ j : Fin width, u.coeff j.val *
      (if j.val ≤ k then v.coeff (k - j.val) else 0) := by
  classical
  let f (j : ℕ) := u.coeff j * (if j ≤ k then v.coeff (k - j) else 0)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Fin.sum_univ_eq_sum_range f]
  change _ = ∑ j ∈ Finset.range width, f j
  trans ∑ j ∈ Finset.range (k + 1), f j
  · apply Finset.sum_congr rfl
    intro j hj
    simp [f, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)]
  · rcases le_total width (k + 1) with h | h
    · symm
      apply Finset.sum_subset (Finset.range_mono h)
      intro j _ hj
      simp only [Finset.mem_range, not_lt] at hj
      simp [f, coeff_eq_zero_of_natDegree_lt (hu.trans_le hj)]
    · apply Finset.sum_subset (Finset.range_mono h)
      intro j _ hj
      simp only [Finset.mem_range, not_lt] at hj
      simp [f, show ¬j ≤ k by omega]

end Cslib.SparseTrinomial
