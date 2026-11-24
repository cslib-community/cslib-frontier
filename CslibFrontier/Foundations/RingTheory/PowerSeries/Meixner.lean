/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate (Mathlib, beside Mathlib/RingTheory/PowerSeries/Basic.lean)

public import CslibFrontier.Init
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Coefficients of `(1 + X)^r / (1 + y X)^(r + 1)`, and their orthogonality

Over a commutative ring `R` with an element `y`, `PowerSeries.meixnerB y r n` and
`PowerSeries.meixnerC y r n` are defined by recursion in `r` and `n`. They are the coefficients of
`Xⁿ` in `(1 + X)^r / (1 + y X)^(r + 1)` and in `(1 + y X)^r / (1 + X)^(r + 1)`
(`PowerSeries.mk_meixnerB_mul_pow`, `PowerSeries.mk_meixnerC_mul_pow`); for `y = q⁻¹` they are
Meixner polynomials up to normalization. If `y` is a unit, the two families are related by
reciprocity (`PowerSeries.pow_mul_meixnerB_of_mul_eq_one`), and the first family is orthogonal
modulo `y^N` for the weights `(1 - y) y^r`, `r < N` (`PowerSeries.pow_dvd_meixnerB_orthogonality`).

## Main definitions

* `PowerSeries.meixnerB`, `PowerSeries.meixnerC`.

## Main results

* `PowerSeries.mk_meixnerB_mul_pow`, `PowerSeries.mk_meixnerC_mul_pow`: the generating functions.
* `PowerSeries.pow_mul_meixnerB_of_mul_eq_one`, `PowerSeries.pow_mul_meixnerC_of_mul_eq_one`:
  reciprocity.
* `PowerSeries.pow_dvd_meixnerB_orthogonality`: orthogonality modulo `y^N`.
* `PowerSeries.map_meixnerB`, `PowerSeries.map_meixnerC`: ring homomorphisms commute with both.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  the proof of Proposition B.2 of the paper; modules `Nc.Cross.Meix` and `Paper.Identity`
  (`meixner_B`, `meixner_C`, `meixner_reciprocal`, `eq_orth`)
-/

public section

namespace PowerSeries

open Finset

variable {R : Type*} [CommRing R]

/-- `[tⁿ] (1+t)^r/(1+yt)^(r+1)`. -/
def meixnerB (y : R) : ℕ → ℕ → R
  | 0, n => (-y) ^ n
  | _ + 1, 0 => 1
  | r + 1, n + 1 => meixnerB y r (n + 1) + meixnerB y r n - y * meixnerB y (r + 1) n
termination_by r n => (r, n)

/-- `[tⁿ] (1+yt)^r/(1+t)^(r+1)`. -/
def meixnerC (y : R) : ℕ → ℕ → R
  | 0, n => (-1) ^ n
  | _ + 1, 0 => 1
  | r + 1, n + 1 => meixnerC y r (n + 1) + y * meixnerC y r n - meixnerC y (r + 1) n
termination_by r n => (r, n)

@[simp] theorem meixnerB_zero (y : R) (n : ℕ) : meixnerB y 0 n = (-y) ^ n := by rw [meixnerB]

@[simp] theorem meixnerB_zero_right (y : R) (r : ℕ) : meixnerB y r 0 = 1 := by
  cases r with
  | zero => rw [meixnerB, pow_zero]
  | succ r => rw [meixnerB]

theorem meixnerB_succ (y : R) (r n : ℕ) :
    meixnerB y (r + 1) (n + 1) = meixnerB y r (n + 1) + meixnerB y r n - y *
        meixnerB y (r + 1) n := by rw [meixnerB]

@[simp] theorem meixnerC_zero (y : R) (n : ℕ) : meixnerC y 0 n = (-1) ^ n := by rw [meixnerC]

@[simp] theorem meixnerC_zero_right (y : R) (r : ℕ) : meixnerC y r 0 = 1 := by
  cases r with
  | zero => rw [meixnerC, pow_zero]
  | succ r => rw [meixnerC]

theorem meixnerC_succ (y : R) (r n : ℕ) :
    meixnerC y (r + 1) (n + 1) = meixnerC y r (n + 1) + y * meixnerC y r n -
        meixnerC y (r + 1) n := by rw [meixnerC]

theorem map_meixnerB {S : Type*} [CommRing S] (f : R →+* S) (y : R) (r n : ℕ) :
    f (meixnerB y r n) = meixnerB (f y) r n := by
  induction r generalizing n with
  | zero => simp [meixnerB_zero]
  | succ r ih =>
    induction n with
    | zero => simp [meixnerB_zero_right]
    | succ n ih' => simp [meixnerB_succ, ih, ih']

theorem map_meixnerC {S : Type*} [CommRing S] (f : R →+* S) (y : R) (r n : ℕ) :
    f (meixnerC y r n) = meixnerC (f y) r n := by
  induction r generalizing n with
  | zero => simp [meixnerC_zero]
  | succ r ih =>
    induction n with
    | zero => simp [meixnerC_zero_right]
    | succ n ih' => simp [meixnerC_succ, ih, ih']

/-- The coefficients of a power series times 1 + at. -/
private theorem coeff_mk_mul_one_add_zero (f : ℕ → R) (a : R) :
    coeff 0 (mk f * (1 + C a * X)) = f 0 := by
  simp [mul_add, ← mul_assoc]

private theorem coeff_mk_mul_one_add_succ (f : ℕ → R) (a : R) (n : ℕ) :
    coeff (n + 1) (mk f * (1 + C a * X)) = f (n + 1) + f n * a := by
  simp [mul_add, ← mul_assoc, coeff_succ_mul_X]

/-- `meixnerB y r` is the sequence of coefficients of `(1 + X)^r / (1 + y X)^(r + 1)`. -/
theorem mk_meixnerB_mul_pow (y : R) (r : ℕ) :
    mk (meixnerB y r) * (1 + C y * X) ^ (r + 1) = (1 + X) ^ r := by
  induction r with
  | zero =>
    rw [zero_add, pow_one, pow_zero]
    ext n
    cases n with
    | zero => rw [coeff_mk_mul_one_add_zero, meixnerB_zero]; simp
    | succ n =>
        rw [coeff_mk_mul_one_add_succ, meixnerB_zero, meixnerB_zero, coeff_one,
            ite_eq_right (Nat.succ_ne_zero n)]; ring
  | succ r ih =>
    have step : mk (meixnerB y (r + 1)) * (1 + C y * X) =
        mk (meixnerB y r) * (1 + C 1 * X) := by
      ext n
      cases n with
      | zero =>
          rw [coeff_mk_mul_one_add_zero, coeff_mk_mul_one_add_zero, meixnerB_zero_right,
              meixnerB_zero_right]
      | succ n => rw [coeff_mk_mul_one_add_succ, coeff_mk_mul_one_add_succ, meixnerB_succ]; ring
    rw [map_one, one_mul] at step
    rw [pow_succ' _ (r + 1), ← mul_assoc, step, mul_right_comm, ih, pow_succ]

/-- `meixnerC y r` is the sequence of coefficients of `(1 + y X)^r / (1 + X)^(r + 1)`. -/
theorem mk_meixnerC_mul_pow (y : R) (r : ℕ) :
    mk (meixnerC y r) * (1 + X) ^ (r + 1) = (1 + C y * X) ^ r := by
  have one : (1 + X : PowerSeries R) = 1 + C 1 * X := by rw [map_one, one_mul]
  induction r with
  | zero =>
    rw [zero_add, pow_one, pow_zero, one]
    ext n
    cases n with
    | zero => rw [coeff_mk_mul_one_add_zero, meixnerC_zero]; simp
    | succ n =>
        rw [coeff_mk_mul_one_add_succ, meixnerC_zero, meixnerC_zero, coeff_one,
            ite_eq_right (Nat.succ_ne_zero n)]; ring
  | succ r ih =>
    have step : mk (meixnerC y (r + 1)) * (1 + X) =
        mk (meixnerC y r) * (1 + C y * X) := by
      rw [one]
      ext n
      cases n with
      | zero =>
          rw [coeff_mk_mul_one_add_zero, coeff_mk_mul_one_add_zero, meixnerC_zero_right,
              meixnerC_zero_right]
      | succ n => rw [coeff_mk_mul_one_add_succ, coeff_mk_mul_one_add_succ, meixnerC_succ]; ring
    rw [pow_succ' _ (r + 1), ← mul_assoc, step, mul_right_comm, ih, pow_succ]

/-- Reciprocity: `yⁿ · meixnerB (1/y) r n = meixnerC y r n`, for an inverse `z` of `y`. -/
theorem pow_mul_meixnerB_of_mul_eq_one {y z : R} (h : y * z = 1) (r n : ℕ) : y ^ n *
    meixnerB z r n = meixnerC y r n := by
  induction r generalizing n with
  | zero =>
    rw [meixnerB_zero, meixnerC_zero, ← mul_pow, mul_neg, h]
  | succ r ih =>
    induction n with
    | zero => simp [meixnerB_zero_right, meixnerC_zero_right]
    | succ n ih' =>
      rw [meixnerB_succ, meixnerC_succ, ← ih, ← ih, ← ih']
      linear_combination (-(y ^ n * meixnerB z (r + 1) n)) * h

/-- Reciprocity read backwards: `yⁿ · meixnerC (1/y) r n = meixnerB y r n`. -/
theorem pow_mul_meixnerC_of_mul_eq_one {y z : R} (h : y * z = 1) (r n : ℕ) : y ^ n *
    meixnerC z r n = meixnerB y r n := by
  have h' : z * y = 1 := by rw [mul_comm, h]
  rw [← pow_mul_meixnerB_of_mul_eq_one h', ← mul_assoc, ← mul_pow, h, one_pow, one_mul]

/-- A telescoping sum. -/
private theorem sum_range_pow_mul_sub (y : R) (u v : ℕ → R) (N : ℕ) (h : ∀ r, v (r + 1) = u r) :
    ∑ r ∈ Finset.range N, y ^ r * (v r - y * u r) = v 0 - y ^ N * v N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, h]
    ring

/-- The first family against `1`: `(1 - y) ∑_{r<N} y^r B(r, k + 1) ≡ 0` modulo `y^N`. -/
private theorem pow_dvd_sum_meixnerB_succ (y : R) (N k : ℕ) :
    y ^ N ∣ (1 - y) * ∑ r ∈ Finset.range N, y ^ r * meixnerB y r (k + 1) := by
  have := sum_range_pow_mul_sub y (fun r => meixnerB y r (k + 1) + meixnerB y r k)
      (fun r => meixnerB y r (k + 1) + y * meixnerB y r k) N
    (fun r => by rw [meixnerB_succ]; ring)
  refine ⟨-(meixnerB y N (k + 1) + y * meixnerB y N k), ?_⟩
  simp only [meixnerB_zero] at this
  rw [Finset.mul_sum]
  have e : ∑ r ∈ Finset.range N, (1 - y) * (y ^ r * meixnerB y r (k + 1)) =
      ∑ r ∈ Finset.range N, y ^ r * (meixnerB y r (k + 1) + y * meixnerB y r k
        - y * (meixnerB y r (k + 1) + meixnerB y r k)) :=
    Finset.sum_congr rfl fun r _ => by ring
  rw [e, this]
  ring

/-- Orthogonality modulo `y^N`: `(1 - y) ∑_{r<N} y^r B(r, i) B(r, j) ≡ [i = j] y^i`, where
`B = meixnerB y`, for any element `y` of any commutative ring (the display (B.1) (eq:orth) in the
proof of Proposition B.2 of [AnthropicVPVNP2026], where `y` is the variable of `ℤ[y]`). -/
theorem pow_dvd_meixnerB_orthogonality (y : R) (N i j : ℕ) :
    y ^ N ∣ (1 - y) * ∑ r ∈ Finset.range N, y ^ r * (meixnerB y r i * meixnerB y r j)
      - (if i = j then y ^ i else 0) := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero =>
      have := sum_range_pow_mul_sub y (fun _ => (1 : R)) (fun _ => 1) N (fun _ => rfl)
      refine ⟨-1, ?_⟩
      simp only [meixnerB_zero_right, mul_one, ite_true, pow_zero]
      simp only [mul_one] at this
      rw [← Finset.sum_mul] at this
      linear_combination this
    | succ j =>
      simpa [(Nat.succ_ne_zero j).symm] using pow_dvd_sum_meixnerB_succ y N j
  | succ i ih =>
    cases j with
    | zero =>
      simpa [Nat.succ_ne_zero i] using pow_dvd_sum_meixnerB_succ y N i
    | succ j =>
      have := sum_range_pow_mul_sub y
        (fun r => (meixnerB y r (i + 1) + meixnerB y r i) * (meixnerB y r (j + 1) + meixnerB y r j))
        (fun r => (meixnerB y r (i + 1) + y * meixnerB y r i) *
            (meixnerB y r (j + 1) + y * meixnerB y r j)) N
        (fun r => by rw [meixnerB_succ, meixnerB_succ]; ring)
      obtain ⟨w, hw⟩ := ih j
      refine ⟨y * w - (meixnerB y N (i + 1) + y * meixnerB y N i) *
          (meixnerB y N (j + 1) + y * meixnerB y N j), ?_⟩
      have e : ∑ r ∈ Finset.range N, y ^ r * ((meixnerB y r (i + 1) + y * meixnerB y r i) *
            (meixnerB y r (j + 1) + y * meixnerB y r j)
            - y * ((meixnerB y r (i + 1) + meixnerB y r i) *
                (meixnerB y r (j + 1) + meixnerB y r j))) =
          (1 - y) * ∑ r ∈ Finset.range N, y ^ r * (meixnerB y r (i + 1) * meixnerB y r (j + 1))
          - y * ((1 - y) * ∑ r ∈ Finset.range N, y ^ r * (meixnerB y r i * meixnerB y r j)) := by
        simp only [Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun r _ => by ring
      rw [e] at this
      have z0 : (meixnerB y 0 (i + 1) + y * meixnerB y 0 i) = 0 :=
          by simp only [meixnerB_zero]; ring
      have z1 : (if i + 1 = j + 1 then y ^ (i + 1) else 0) = y * (if i = j then y ^ i else 0) := by
        by_cases hmn : i = j
        · simp [hmn, pow_succ, mul_comm]
        · simp [hmn]
      rw [z0, zero_mul, zero_sub] at this
      rw [z1]
      linear_combination this + y * hw

end PowerSeries
