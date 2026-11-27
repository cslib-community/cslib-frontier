/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Polynomial.CoeffNorm1
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Integer parity-amplifying polynomials and shared-total-order truncation

For `ℓ ≥ 1`, the complement of the Beigel–Tarui modulus-amplifying polynomial [Toda][Toda1991],
[Arora and Barak, Section 17.4][AroraBarak09],
$$p_\ell(Y) = (1 - Y)^\ell \sum_{j=0}^{\ell-1} \binom{\ell - 1 + j}{j} Y^j \in \mathbb{Z}[Y],$$
satisfies $p_\ell(Y) \equiv 1 \pmod{Y^\ell}$ and $p_\ell(Y) \equiv 0 \pmod{(1 - Y)^\ell}$, so
for every integer modulus $m$ and $y \in \mathbb{Z}$, $m \mid y$ implies
$p_\ell(y) \equiv 1 \pmod{m^\ell}$ (`Polynomial.parityAmplifier_eval_modEq_one_of_dvd`) and
$m \mid y - 1$ implies $p_\ell(y) \equiv 0 \pmod{m^\ell}$
(`Polynomial.parityAmplifier_eval_modEq_zero_of_dvd_sub_one`). The case $m = 2$ gives
$p_\ell(y) \equiv \mathbf{1}_{\{2 \mid y\}} \pmod{2^\ell}$
(`Polynomial.parityAmplifier_eval_modEq_two_pow`).

Following Lemma 5.1 and Lemma B.1 of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], writing $p_\ell$ in powers of
the monic quadratic $h(Y) = Y^2 - Y = Y(Y - 1)$ (`Polynomial.hPoly`) by successive monic division
produces remainders $e_0, \dots, e_{\ell-1} \in \mathbb{Z}[Y]$ (`Polynomial.parityBaseDigit`) of
degree at most $1$ with $p_\ell(Y) = \sum_{j=0}^{\ell-1} e_j(Y) h(Y)^j$
(`Polynomial.parityAmplifier_eq_sum_baseDigit`) and explicit coefficient bounds
(`Polynomial.natAbs_coeff_parityBaseDigit_le`, `Polynomial.coeffNorm1_parityBaseDigit_le`).

Since $h(y) = y(y - 1)$ is even for every $y \in \mathbb{Z}$, introducing a shared formal variable
$V$ (`Polynomial.parityFactor`) across a family of equations and discarding powers $V^s$ with
$s \ge \ell$ via `Polynomial.sumCoeffsBelow` (Lemma 5.2 of [OpenAI2026ETH]) preserves the product
of evenness indicators modulo $2^\ell$ (`Polynomial.sumCoeffsBelow_prod_parityFactor_modEq`), while
bounding the multivariate total degree of every retained coefficient and of their sum by
$d_* (\#I + 2(\ell - 1))$ when each input polynomial has total degree at most $d_*$
(`Polynomial.totalDegree_sumCoeffsBelow_prod_parityFactor_le`).

## Main definitions

* `Polynomial.hPoly`: the monic quadratic `X ^ 2 - X` in `ℤ[X]`.
* `Polynomial.parityKernel`: the partial binomial series `∑ j < ℓ, choose (ℓ - 1 + j) j * X ^ j`.
* `Polynomial.parityAmplifier`: the even-parity amplifying polynomial `p_ℓ(X) ∈ ℤ[X]`.
* `Polynomial.iterDivByH`, `Polynomial.baseDigitByH`, `Polynomial.parityBaseDigit`: successive
  monic quotients and linear remainders `e_j(X)` on division by `X ^ 2 - X`.
* `Polynomial.coeffNorm1`: the `ℓ₁` coefficient norm `∑ i ∈ p.support, (p.coeff i).natAbs`.
* `Polynomial.parityFactor`: the `V`-series factor `B(y; V) = ∑ j < ℓ, e_j(y) h(y)^j V^j`.
* `Polynomial.sumCoeffsBelow`: the truncated coefficient sum `S_ℓ(P) = ∑ s < ℓ, P.coeff s`.

## Main results

* `Polynomial.parityAmplifier_add_X_pow_mul_eq_one`: Bezout identity
  `p_ℓ(X) + X ^ ℓ * ∑ m < ℓ, choose (m + ℓ - 1) (ℓ - 1) * (1 - X) ^ m = 1` for `ℓ ≥ 1`.
* `Polynomial.parityAmplifier_eval_modEq_one_of_dvd`,
  `Polynomial.parityAmplifier_eval_modEq_zero_of_dvd_sub_one`: amplification from modulus `m` to
  `m ^ ℓ`.
* `Polynomial.parityAmplifier_eval_modEq_two_pow`:
  `p_ℓ(y) ≡ (if Even y then 1 else 0) [ZMOD 2 ^ ℓ]`.
* `Polynomial.parityAmplifier_eq_sum_baseDigit`: `p_ℓ = ∑ j < ℓ, e_j * (X ^ 2 - X) ^ j`.
* `Polynomial.coeffNorm1_parityAmplifier_le`: `‖p_ℓ‖₁ ≤ 2 ^ (3 * ℓ)`.
* `Polynomial.natAbs_coeff_parityBaseDigit_le`: `|coeff k (e_j)| ≤ (2 * ℓ) ^ j * 2 ^ (3 * ℓ)`.
* `Polynomial.coeffNorm1_parityBaseDigit_le`: `‖e_j‖₁ ≤ 2 * ((2 * ℓ) ^ j * 2 ^ (3 * ℓ))`.
* `Polynomial.sumCoeffsBelow_prod_parityFactor_modEq`: shared-`V` truncation modulo `2 ^ ℓ`.
* `Polynomial.totalDegree_sumCoeffsBelow_prod_parityFactor_le`: linear total-degree bound
  `totalDegree ≤ d_* * (#I + 2 * (ℓ - 1))`.

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (Lemmas 5.1, 5.2, and B.1)
-/

@[expose] public noncomputable section

namespace Polynomial

open Finset

/-! ### 1. The univariate even-parity amplifier `p_ℓ(X)` -/

/-- The partial binomial series `g(m, K) = ∑ j ∈ range K, choose (m + j) j * X ^ j` in `ℤ[X]`. -/
def paritySeriesAux (m K : ℕ) : ℤ[X] :=
  ∑ j ∈ range K, (Nat.choose (m + j) j : ℤ[X]) * X ^ j

/-- The kernel `∑ j ∈ range ℓ, choose (ℓ - 1 + j) j * X ^ j` of the even-parity amplifier. -/
def parityKernel (ℓ : ℕ) : ℤ[X] :=
  paritySeriesAux (ℓ - 1) ℓ

/-- The even-parity amplifying polynomial
`p_ℓ(X) = (1 - X) ^ ℓ * ∑ j ∈ range ℓ, choose (ℓ - 1 + j) j * X ^ j` in `ℤ[X]`. -/
def parityAmplifier (ℓ : ℕ) : ℤ[X] :=
  (1 - X) ^ ℓ * parityKernel ℓ

/-- At precision `0`, `parityAmplifier 0` is `0`. -/
@[simp]
theorem parityAmplifier_zero : parityAmplifier 0 = 0 := by
  simp only [parityAmplifier, parityKernel, paritySeriesAux, range_zero, sum_empty, mul_zero]

/-- At precision `1`, `parityAmplifier 1 = 1 - X`. -/
theorem parityAmplifier_one : parityAmplifier 1 = 1 - X := by
  simp only [parityAmplifier, parityKernel, paritySeriesAux, tsub_self, range_one, sum_singleton,
    add_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, pow_one]

/-- At precision `2`, `parityAmplifier 2 = 1 - 3 * X ^ 2 + 2 * X ^ 3`. -/
theorem parityAmplifier_two : parityAmplifier 2 = 1 - 3 * X ^ 2 + 2 * X ^ 3 := by
  simp only [parityAmplifier, parityKernel, paritySeriesAux, sum_range_succ, range_zero, sum_empty,
    Nat.reduceSub, zero_add, add_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one,
    Nat.reduceAdd, Nat.choose_one_right, Nat.cast_ofNat, pow_one]
  ring

/-- `(1 - X) ^ ℓ` divides `parityAmplifier ℓ` in `ℤ[X]`. -/
theorem one_sub_X_pow_dvd_parityAmplifier (ℓ : ℕ) :
    (1 - X : ℤ[X]) ^ ℓ ∣ parityAmplifier ℓ :=
  dvd_mul_right _ _

private theorem paritySeriesAux_succ (m K : ℕ) :
    paritySeriesAux m (K + 1) = paritySeriesAux m K + (Nat.choose (m + K) K : ℤ[X]) * X ^ K :=
  sum_range_succ _ K

private theorem one_sub_X_mul_paritySeriesAux_zero (K : ℕ) :
    (1 - X) * paritySeriesAux 0 K = 1 - X ^ K := by
  induction K with
  | zero =>
    simp only [paritySeriesAux, range_zero, sum_empty, mul_zero, pow_zero, sub_self]
  | succ K ih =>
    rw [paritySeriesAux_succ, zero_add, Nat.choose_self, Nat.cast_one, one_mul, mul_add, ih]
    ring

private theorem one_sub_X_mul_paritySeriesAux_succ (m k : ℕ) :
    (1 - X) * paritySeriesAux (m + 1) (k + 1) =
      paritySeriesAux m (k + 1) - (Nat.choose (m + k + 1) k : ℤ[X]) * X ^ (k + 1) := by
  induction k with
  | zero =>
    simp only [paritySeriesAux, zero_add, range_one, sum_singleton, add_zero,
      Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, pow_one]
    ring
  | succ k ih =>
    rw [paritySeriesAux_succ (m + 1) (k + 1), mul_add, ih, paritySeriesAux_succ m (k + 1),
      ← add_assoc (m + 1) k 1, Nat.add_right_comm m 1 k, ← add_assoc m k 1,
      Nat.choose_succ_succ (m + k + 1) k, Nat.cast_add]
    ring

private theorem one_sub_X_pow_mul_paritySeriesAux_add_sum (m k : ℕ) :
    (1 - X) ^ (m + 1) * paritySeriesAux m (k + 1) +
      X ^ (k + 1) * ∑ i ∈ range (m + 1), (Nat.choose (i + k) k : ℤ[X]) * (1 - X) ^ i = 1 := by
  induction m with
  | zero =>
    simp only [zero_add, pow_one, one_sub_X_mul_paritySeriesAux_zero, range_one, sum_singleton,
      Nat.choose_self, Nat.cast_one, pow_zero, mul_one, sub_add_cancel]
  | succ m ih =>
    rw [sum_range_succ, Nat.add_right_comm m 1 k]
    linear_combination ih + (1 - X) ^ (m + 1) * one_sub_X_mul_paritySeriesAux_succ m k

/-- Exact Bezout identity for `parityAmplifier ℓ` (`ℓ ≥ 1`):
`p_ℓ(X) + X ^ ℓ * ∑ i ∈ range ℓ, choose (i + ℓ - 1) (ℓ - 1) * (1 - X) ^ i = 1`. -/
theorem parityAmplifier_add_X_pow_mul_eq_one {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    parityAmplifier ℓ +
      X ^ ℓ * ∑ i ∈ range ℓ, (Nat.choose (i + (ℓ - 1)) (ℓ - 1) : ℤ[X]) * (1 - X) ^ i = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  simpa only [parityAmplifier, parityKernel, add_tsub_cancel_right] using
    one_sub_X_pow_mul_paritySeriesAux_add_sum k k

/-- For `ℓ ≥ 1`, `X ^ ℓ` divides `1 - parityAmplifier ℓ` in `ℤ[X]`. -/
theorem X_pow_dvd_one_sub_parityAmplifier {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    X ^ ℓ ∣ 1 - parityAmplifier ℓ := by
  refine ⟨∑ i ∈ range ℓ, (Nat.choose (i + (ℓ - 1)) (ℓ - 1) : ℤ[X]) * (1 - X) ^ i, ?_⟩
  exact (eq_sub_of_add_eq' (parityAmplifier_add_X_pow_mul_eq_one hℓ)).symm

/-- For `ℓ ≥ 1` and `m ∣ y`, `p_ℓ(y) ≡ 1 (mod m ^ ℓ)`: `y ^ ℓ` divides `1 - p_ℓ(y)`. -/
private theorem parityAmplifier_eval_modEq_one_of_dvd_of_pos {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {m y : ℤ}
    (hy : m ∣ y) : (parityAmplifier ℓ).eval y ≡ 1 [ZMOD m ^ ℓ] := by
  rw [Int.modEq_iff_dvd]
  refine (pow_dvd_pow_of_dvd hy ℓ).trans ?_
  simpa only [coe_evalRingHom, eval_sub, eval_one, eval_pow, eval_X] using
    _root_.map_dvd (evalRingHom y) (X_pow_dvd_one_sub_parityAmplifier hℓ)

/-- If `m ∣ y`, then `p_ℓ(y) ≡ 1 (mod m ^ ℓ)`. -/
theorem parityAmplifier_eval_modEq_one_of_dvd (ℓ : ℕ) {m y : ℤ} (hy : m ∣ y) :
    (parityAmplifier ℓ).eval y ≡ 1 [ZMOD m ^ ℓ] := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp only [pow_zero, Int.modEq_one]
  exact parityAmplifier_eval_modEq_one_of_dvd_of_pos hℓ hy

/-- If `m ∣ y - 1`, then `p_ℓ(y) ≡ 0 (mod m ^ ℓ)`. -/
theorem parityAmplifier_eval_modEq_zero_of_dvd_sub_one (ℓ : ℕ) {m y : ℤ} (hy : m ∣ y - 1) :
    (parityAmplifier ℓ).eval y ≡ 0 [ZMOD m ^ ℓ] := by
  rw [Int.modEq_iff_dvd, zero_sub, dvd_neg]
  refine (pow_dvd_pow_of_dvd (neg_sub y 1 ▸ dvd_neg.2 hy) ℓ).trans ?_
  simpa only [coe_evalRingHom, eval_pow, eval_sub, eval_one, eval_X] using
    _root_.map_dvd (evalRingHom y) (one_sub_X_pow_dvd_parityAmplifier ℓ)

/-- At any even integer `y`, `parityAmplifier ℓ` (`ℓ ≥ 1`) evaluates to `1` modulo `2 ^ ℓ`. -/
theorem parityAmplifier_eval_modEq_one_of_even {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {y : ℤ} (hy : Even y) :
    (parityAmplifier ℓ).eval y ≡ 1 [ZMOD (2 : ℤ) ^ ℓ] :=
  parityAmplifier_eval_modEq_one_of_dvd_of_pos hℓ (even_iff_two_dvd.1 hy)

/-- At any odd integer `y`, `parityAmplifier ℓ` evaluates to `0` modulo `2 ^ ℓ`. -/
theorem parityAmplifier_eval_modEq_zero_of_odd (ℓ : ℕ) {y : ℤ} (hy : Odd y) :
    (parityAmplifier ℓ).eval y ≡ 0 [ZMOD (2 : ℤ) ^ ℓ] :=
  parityAmplifier_eval_modEq_zero_of_dvd_sub_one ℓ (even_iff_two_dvd.1 (hy.sub_odd odd_one))

/-- **Lemma 5.1 (parity congruence)**: for `ℓ ≥ 1` and `y ∈ ℤ`,
`p_ℓ(y) ≡ (if Even y then 1 else 0) (mod 2 ^ ℓ)`. -/
theorem parityAmplifier_eval_modEq_two_pow {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (y : ℤ) [Decidable (Even y)] :
    (parityAmplifier ℓ).eval y ≡ (if Even y then 1 else 0) [ZMOD (2 : ℤ) ^ ℓ] := by
  split_ifs with hy
  · exact parityAmplifier_eval_modEq_one_of_even hℓ hy
  · exact parityAmplifier_eval_modEq_zero_of_odd ℓ (Int.not_even_iff_odd.mp hy)

/-! ### 2. Base-`h(X)` expansion (`h(X) = X ^ 2 - X`) and degree bounds -/

/-- The monic quadratic `h(X) = X ^ 2 - X = X * (X - 1)` in `ℤ[X]`. -/
def hPoly : ℤ[X] :=
  X ^ 2 - X

/-- `hPoly = X ^ 2 - X` is monic. -/
theorem monic_hPoly : hPoly.Monic := by
  exact (monic_X_pow 2).sub_of_left (by simp [degree_X])

/-- `hPoly` has degree `2`. -/
@[simp]
theorem natDegree_hPoly : hPoly.natDegree = 2 := by
  rw [hPoly, natDegree_sub_eq_left_of_natDegree_lt (by simp), natDegree_X_pow]

/-- `hPoly` is not equal to `1`. -/
theorem hPoly_ne_one : hPoly ≠ 1 := by
  intro h
  simpa using congr_arg natDegree h

/-- Evaluation of an integer polynomial `P : ℤ[X]` at `y : A` via the canonical cast `ℤ →+* A`. -/
def evalInt {A : Type*} [CommRing A] (y : A) (P : ℤ[X]) : A :=
  P.eval₂ (Int.castRingHom A) y

/-- On `ℤ`, `evalInt` coincides with `Polynomial.eval`. -/
@[simp]
theorem evalInt_int (y : ℤ) (P : ℤ[X]) : evalInt y P = P.eval y := by
  simp only [evalInt, Int.castRingHom_int, eval₂_id]

/-- Evaluating `hPoly` at `y : A` gives `y ^ 2 - y`. -/
@[simp]
theorem evalInt_hPoly {A : Type*} [CommRing A] (y : A) :
    evalInt y hPoly = y ^ 2 - y := by
  simp only [evalInt, hPoly, eval₂_sub, eval₂_X_pow, eval₂_X]

/-- Evaluating `hPoly` at `y : ℤ` gives `y ^ 2 - y`. -/
@[simp]
theorem eval_hPoly (y : ℤ) : hPoly.eval y = y ^ 2 - y := by
  simp only [hPoly, eval_sub, eval_pow, eval_X]

/-- For every integer `y`, `h(y) = y ^ 2 - y` is even. -/
theorem two_dvd_eval_hPoly (y : ℤ) : (2 : ℤ) ∣ hPoly.eval y := by
  rw [eval_hPoly]
  rcases Int.even_or_odd y with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · refine ⟨(k + k) * k - k, by ring⟩
  · refine ⟨(2 * k + 1) * k, by ring⟩

/-- Iterated monic quotient of `P : ℤ[X]` on division by `hPoly = X ^ 2 - X`. -/
def iterDivByH (P : ℤ[X]) : ℕ → ℤ[X]
  | 0 => P
  | j + 1 => iterDivByH P j /ₘ hPoly

/-- The `j`-th remainder `(iterDivByH P j) %ₘ hPoly` in the base-`hPoly` expansion of `P`. -/
def baseDigitByH (P : ℤ[X]) (j : ℕ) : ℤ[X] :=
  iterDivByH P j %ₘ hPoly

/-- The `j`-th linear remainder `e_j(X)` in the base-`(X ^ 2 - X)` expansion of `p_ℓ(X)`. -/
def parityBaseDigit (ℓ j : ℕ) : ℤ[X] :=
  baseDigitByH (parityAmplifier ℓ) j

/-- Remainder modulo `hPoly` has degree at most `1`. -/
theorem natDegree_modByMonic_hPoly_le (P : ℤ[X]) : (P %ₘ hPoly).natDegree ≤ 1 := by
  exact Nat.le_of_lt_succ
    ((natDegree_modByMonic_lt P monic_hPoly hPoly_ne_one).trans_eq natDegree_hPoly)

/-- Each `baseDigitByH P j` has degree at most `1`. -/
theorem natDegree_baseDigitByH_le (P : ℤ[X]) (j : ℕ) :
    (baseDigitByH P j).natDegree ≤ 1 :=
  natDegree_modByMonic_hPoly_le (iterDivByH P j)

/-- Each `parityBaseDigit ℓ j` (`e_j`) has degree at most `1`. -/
theorem natDegree_parityBaseDigit_le (ℓ j : ℕ) :
    (parityBaseDigit ℓ j).natDegree ≤ 1 :=
  natDegree_baseDigitByH_le (parityAmplifier ℓ) j

/-- Explicit affine decomposition `e_j(X) = a_j + b_j X` of `parityBaseDigit ℓ j`. -/
theorem parityBaseDigit_eq_C_add_C_mul_X (ℓ j : ℕ) :
    parityBaseDigit ℓ j =
      C ((parityBaseDigit ℓ j).coeff 0) + C ((parityBaseDigit ℓ j).coeff 1) * X :=
  (eq_X_add_C_of_natDegree_le_one (natDegree_parityBaseDigit_le ℓ j)).trans (add_comm _ _)

/-- Division expansion after `m` steps of monic division by `hPoly`:
`P = (∑ j ∈ range m, baseDigitByH P j * hPoly ^ j) + iterDivByH P m * hPoly ^ m`. -/
theorem eq_sum_baseDigitByH_add_iterDivByH (P : ℤ[X]) (m : ℕ) :
    P = (∑ j ∈ range m, baseDigitByH P j * hPoly ^ j) + iterDivByH P m * hPoly ^ m := by
  induction m with
  | zero =>
    simp only [range_zero, sum_empty, iterDivByH, pow_zero, mul_one, zero_add]
  | succ m ih =>
    rw [sum_range_succ, baseDigitByH, iterDivByH, pow_succ]
    linear_combination ih + hPoly ^ m * (modByMonic_add_div (iterDivByH P m) hPoly).symm

/-- `iterDivByH P j` has degree `P.natDegree - 2 * j`. -/
theorem natDegree_iterDivByH (P : ℤ[X]) (j : ℕ) :
    (iterDivByH P j).natDegree = P.natDegree - 2 * j := by
  induction j with
  | zero => simp only [iterDivByH, mul_zero, Nat.sub_zero]
  | succ j ih =>
    rw [iterDivByH, natDegree_divByMonic _ monic_hPoly, ih, natDegree_hPoly]
    omega

/-- `iterDivByH P j` vanishes once `P.natDegree < 2 * j` (or `P = 0`). -/
theorem iterDivByH_eq_zero_of_natDegree_lt {P : ℤ[X]} {j : ℕ}
    (h : P = 0 ∨ P.natDegree < 2 * j) :
    iterDivByH P j = 0 := by
  rcases h with rfl | hlt
  · induction j with
    | zero => rfl
    | succ j ih => rw [iterDivByH, ih, zero_divByMonic]
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  rw [iterDivByH, divByMonic_eq_zero_iff monic_hPoly]
  exact degree_lt_degree (by rw [natDegree_iterDivByH, natDegree_hPoly]; omega)

private theorem natDegree_paritySeriesAux_le (m K : ℕ) :
    (paritySeriesAux m K).natDegree ≤ K - 1 := by
  refine natDegree_sum_le_of_forall_le (range K) _ fun j hj => natDegree_mul_le.trans ?_
  rw [natDegree_natCast, zero_add, natDegree_X_pow]
  exact Nat.le_sub_one_of_lt (mem_range.1 hj)

/-- `parityKernel ℓ` has degree at most `ℓ - 1`. -/
theorem natDegree_parityKernel_le (ℓ : ℕ) :
    (parityKernel ℓ).natDegree ≤ ℓ - 1 :=
  natDegree_paritySeriesAux_le (ℓ - 1) ℓ

/-- `parityAmplifier ℓ` has degree at most `2 * ℓ - 1`. -/
theorem natDegree_parityAmplifier_le (ℓ : ℕ) :
    (parityAmplifier ℓ).natDegree ≤ 2 * ℓ - 1 := by
  refine (natDegree_mul_le (p := (1 - X) ^ ℓ) (q := parityKernel ℓ)).trans ?_
  have h1 : ((1 - X : ℤ[X]) ^ ℓ).natDegree ≤ ℓ :=
    natDegree_pow_le.trans ((Nat.mul_le_mul_left ℓ
      (by simpa using natDegree_sub_le (1 : ℤ[X]) X)).trans_eq (mul_one ℓ))
  have h2 := natDegree_parityKernel_le ℓ
  omega

/-- After `ℓ` divisions by `hPoly`, the quotient of `parityAmplifier ℓ` is `0`. -/
theorem iterDivByH_parityAmplifier_self (ℓ : ℕ) :
    iterDivByH (parityAmplifier ℓ) ℓ = 0 := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · exact iterDivByH_eq_zero_of_natDegree_lt (Or.inl parityAmplifier_zero)
  · exact iterDivByH_eq_zero_of_natDegree_lt
      (Or.inr ((natDegree_parityAmplifier_le ℓ).trans_lt (by omega)))

/-- **Lemma 5.1 (base-`h` decomposition)**: for every `ℓ : ℕ`,
`parityAmplifier ℓ = ∑ j ∈ range ℓ, parityBaseDigit ℓ j * hPoly ^ j`. -/
theorem parityAmplifier_eq_sum_baseDigit (ℓ : ℕ) :
    parityAmplifier ℓ = ∑ j ∈ range ℓ, parityBaseDigit ℓ j * hPoly ^ j := by
  simpa [iterDivByH_parityAmplifier_self, parityBaseDigit] using
    eq_sum_baseDigitByH_add_iterDivByH (parityAmplifier ℓ) ℓ

/-- Evaluation of `parityAmplifier ℓ` in any commutative ring `A` via `parityBaseDigit`. -/
theorem evalInt_parityAmplifier_eq_sum {A : Type*} [CommRing A] (ℓ : ℕ) (y : A) :
    evalInt y (parityAmplifier ℓ) =
      ∑ j ∈ range ℓ, evalInt y (parityBaseDigit ℓ j) * (y ^ 2 - y) ^ j := by
  simpa only [evalInt, map_sum, map_mul, map_pow, coe_eval₂RingHom, hPoly, eval₂_sub,
    eval₂_X_pow, eval₂_X] using
    congr_arg (eval₂RingHom (Int.castRingHom A) y) (parityAmplifier_eq_sum_baseDigit ℓ)

/-! ### 3. Coefficient and `ℓ₁`-norm bounds (Lemma B.1) -/

private theorem sum_range_choose_add (m k : ℕ) :
    ∑ j ∈ range (k + 1), Nat.choose (m + j) j = Nat.choose (m + k + 1) k := by
  induction k with
  | zero => simp only [zero_add, range_one, sum_singleton, add_zero, Nat.choose_zero_right]
  | succ k ih =>
    rw [sum_range_succ, ih, ← add_assoc m k 1, Nat.choose_succ_succ (m + k + 1) k]

/-- The `ℓ₁` norm of `parityKernel ℓ` is at most `2 ^ (2 * ℓ)`. -/
theorem coeffNorm1_parityKernel_le (ℓ : ℕ) :
    coeffNorm1 (parityKernel ℓ) ≤ 2 ^ (2 * ℓ) := by
  have hsum : ∀ K, coeffNorm1 (paritySeriesAux (ℓ - 1) K) ≤
      ∑ j ∈ range K, Nat.choose (ℓ - 1 + j) j := fun K =>
    (coeffNorm1_sum_le _ _).trans <| sum_le_sum fun j _ => (coeffNorm1_mul_X_pow_le _ j).trans <| by
      rw [← C_eq_natCast, coeffNorm1_C, Int.natAbs_natCast]
  rcases ℓ with _ | k
  · exact (hsum 0).trans (by simp only [range_zero, sum_empty, zero_le])
  · refine (hsum (k + 1)).trans ?_
    rw [add_tsub_cancel_right, sum_range_choose_add k k]
    exact (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by omega) (by omega))

/-- **Lemma B.1 (`ℓ₁`-norm of `p_ℓ`)**: `‖p_ℓ‖₁ ≤ 2 ^ (3 * ℓ)`. -/
theorem coeffNorm1_parityAmplifier_le (ℓ : ℕ) :
    coeffNorm1 (parityAmplifier ℓ) ≤ 2 ^ (3 * ℓ) := by
  rw [parityAmplifier]
  calc
    coeffNorm1 ((1 - X) ^ ℓ * parityKernel ℓ)
      ≤ 2 ^ ℓ * coeffNorm1 (parityKernel ℓ) := coeffNorm1_one_sub_X_pow_mul_le ℓ _
    _ ≤ 2 ^ ℓ * 2 ^ (2 * ℓ) := Nat.mul_le_mul_left (2 ^ ℓ) (coeffNorm1_parityKernel_le ℓ)
    _ = 2 ^ (3 * ℓ) := by rw [← pow_add, ← one_add_mul]

private theorem coeff_modByMonic_hPoly_add (p : ℤ[X]) (n : ℕ) :
    (p %ₘ hPoly).coeff n + ((p /ₘ hPoly * X ^ 2).coeff n - (p /ₘ hPoly * X).coeff n) =
      p.coeff n := by
  rw [← coeff_sub, ← coeff_add, ← mul_sub, mul_comm, ← hPoly, modByMonic_add_div]

/-- Recurrence for the coefficients of the quotient `p /ₘ hPoly`. -/
theorem coeff_divByMonic_hPoly_rec (p : ℤ[X]) (n : ℕ) :
    (p /ₘ hPoly).coeff n = p.coeff (n + 2) + (p /ₘ hPoly).coeff (n + 1) := by
  have h := coeff_modByMonic_hPoly_add p (n + 2)
  rw [coeff_eq_zero_of_natDegree_lt (by have := natDegree_modByMonic_hPoly_le p; omega),
    coeff_mul_X_pow, coeff_mul_X] at h
  linarith

/-- Telescoping sum formula for the coefficients of `p /ₘ hPoly`. -/
theorem coeff_divByMonic_hPoly_sum (p : ℤ[X]) (n m : ℕ) :
    (p /ₘ hPoly).coeff n =
      (∑ t ∈ range m, p.coeff (n + 2 + t)) + (p /ₘ hPoly).coeff (n + m) := by
  induction m with
  | zero => simp only [range_zero, sum_empty, add_zero, zero_add]
  | succ m ih =>
    rw [sum_range_succ, ih, coeff_divByMonic_hPoly_rec p (n + m),
      Nat.add_right_comm n m 2, ← add_assoc n m 1]
    ring

/-- The constant coefficient of `p %ₘ hPoly` equals `p.coeff 0`. -/
theorem coeff_modByMonic_hPoly_zero (p : ℤ[X]) :
    (p %ₘ hPoly).coeff 0 = p.coeff 0 := by
  have h := coeff_modByMonic_hPoly_add p 0
  rwa [coeff_mul_X_zero, coeff_mul_X_pow', ite_eq_right (by decide), sub_zero, add_zero] at h

/-- The linear coefficient of `p %ₘ hPoly` equals `p.coeff 1 + (p /ₘ hPoly).coeff 0`. -/
theorem coeff_modByMonic_hPoly_one (p : ℤ[X]) :
    (p %ₘ hPoly).coeff 1 = p.coeff 1 + (p /ₘ hPoly).coeff 0 := by
  have h := coeff_modByMonic_hPoly_add p 1
  rw [coeff_mul_X_pow', ite_eq_right (by decide), coeff_mul_X] at h
  linarith

private theorem coeff_divByMonic_hPoly_eq_sum (p : ℤ[X]) (n : ℕ) :
    (p /ₘ hPoly).coeff n = ∑ t ∈ range (p.natDegree + 1), p.coeff (n + 2 + t) := by
  rw [coeff_divByMonic_hPoly_sum p n (p.natDegree + 1), coeff_eq_zero_of_natDegree_lt, add_zero]
  rw [natDegree_divByMonic p monic_hPoly, natDegree_hPoly]
  omega

private theorem natAbs_sum_coeff_add_le (p : ℤ[X]) (a N : ℕ) :
    (∑ t ∈ range N, p.coeff (a + t)).natAbs ≤ coeffNorm1 p :=
  (Int.natAbs_sum_le _ _).trans <| (sum_map (range N) (addLeftEmbedding a)
    fun i => (p.coeff i).natAbs).symm.trans_le (sum_natAbs_coeff_le_coeffNorm1 p _)

/-- Every coefficient of `p /ₘ hPoly` has absolute value at most `coeffNorm1 p`. -/
theorem natAbs_coeff_divByMonic_hPoly_le (p : ℤ[X]) (n : ℕ) :
    ((p /ₘ hPoly).coeff n).natAbs ≤ coeffNorm1 p := by
  rw [coeff_divByMonic_hPoly_eq_sum]
  exact natAbs_sum_coeff_add_le p (n + 2) _

/-- Every coefficient of `p %ₘ hPoly` has absolute value at most `coeffNorm1 p`. -/
theorem natAbs_coeff_modByMonic_hPoly_le (p : ℤ[X]) (k : ℕ) :
    ((p %ₘ hPoly).coeff k).natAbs ≤ coeffNorm1 p := by
  rcases k with _ | _ | k
  · simpa only [coeff_modByMonic_hPoly_zero] using natAbs_coeff_le_coeffNorm1 p 0
  · rw [coeff_modByMonic_hPoly_one, coeff_divByMonic_hPoly_eq_sum]
    have hsum : p.coeff 1 + ∑ t ∈ range (p.natDegree + 1), p.coeff (0 + 2 + t) =
        ∑ t ∈ range (p.natDegree + 2), p.coeff (1 + t) := by
      rw [sum_range_succ' (fun t => p.coeff (1 + t)) (p.natDegree + 1), add_zero, add_comm]
      exact congrArg₂ _ (sum_congr rfl fun t _ => congrArg _ (by omega)) rfl
    exact hsum ▸ natAbs_sum_coeff_add_le p 1 _
  · rw [coeff_eq_zero_of_natDegree_lt ((natDegree_modByMonic_hPoly_le p).trans_lt (by omega))]
    simp

private theorem coeffNorm1_le_mul_of_natDegree_lt {q : ℤ[X]} {N c : ℕ} (hq : q.natDegree < N)
    (hc : ∀ i, (q.coeff i).natAbs ≤ c) : coeffNorm1 q ≤ N * c := by
  rw [coeffNorm1_eq_sum_of_support_subset (supp_subset_range hq)]
  simpa only [card_range, smul_eq_mul] using sum_le_card_nsmul (range N) _ _ fun i _ => hc i

/-- The `ℓ₁` norm of `p %ₘ hPoly` is at most `2 * coeffNorm1 p`. -/
theorem coeffNorm1_modByMonic_hPoly_le (p : ℤ[X]) :
    coeffNorm1 (p %ₘ hPoly) ≤ 2 * coeffNorm1 p :=
  coeffNorm1_le_mul_of_natDegree_lt (by have := natDegree_modByMonic_hPoly_le p; omega)
    (natAbs_coeff_modByMonic_hPoly_le p)

/-- The `ℓ₁` norm of `p /ₘ hPoly` is at most `p.natDegree * coeffNorm1 p`. -/
theorem coeffNorm1_divByMonic_hPoly_le (p : ℤ[X]) :
    coeffNorm1 (p /ₘ hPoly) ≤ p.natDegree * coeffNorm1 p := by
  by_cases hdiv : p /ₘ hPoly = 0
  · rw [hdiv, coeffNorm1_zero]
    exact Nat.zero_le _
  refine coeffNorm1_le_mul_of_natDegree_lt (natDegree_lt_natDegree hdiv
    (degree_divByMonic_lt p hPoly ?_ (monic_hPoly.degree_pos.2 hPoly_ne_one)))
    (natAbs_coeff_divByMonic_hPoly_le p)
  rintro rfl
  exact hdiv (zero_divByMonic _)

/-- After `j` monic divisions by `hPoly`, `coeffNorm1 (iterDivByH p j)` is at most
`p.natDegree ^ j * coeffNorm1 p`. -/
theorem coeffNorm1_iterDivByH_le (p : ℤ[X]) (j : ℕ) :
    coeffNorm1 (iterDivByH p j) ≤ p.natDegree ^ j * coeffNorm1 p := by
  induction j with
  | zero => simp only [iterDivByH, pow_zero, one_mul, le_refl]
  | succ j ih =>
    rw [iterDivByH, pow_succ', mul_assoc]
    exact (coeffNorm1_divByMonic_hPoly_le _).trans
      (Nat.mul_le_mul ((natDegree_iterDivByH p j).trans_le (Nat.sub_le _ _)) ih)

private theorem coeffNorm1_iterDivByH_parityAmplifier_le (ℓ j : ℕ) :
    coeffNorm1 (iterDivByH (parityAmplifier ℓ) j) ≤ (2 * ℓ) ^ j * 2 ^ (3 * ℓ) :=
  (coeffNorm1_iterDivByH_le _ j).trans <| Nat.mul_le_mul
    (Nat.pow_le_pow_left ((natDegree_parityAmplifier_le ℓ).trans (Nat.sub_le _ _)) j)
    (coeffNorm1_parityAmplifier_le ℓ)

/-- **Lemma B.1 (coefficient bound for `e_j`)**: every coefficient of `parityBaseDigit ℓ j` has
absolute value at most `(2 * ℓ) ^ j * 2 ^ (3 * ℓ)`. -/
theorem natAbs_coeff_parityBaseDigit_le (ℓ j k : ℕ) :
    ((parityBaseDigit ℓ j).coeff k).natAbs ≤ (2 * ℓ) ^ j * 2 ^ (3 * ℓ) :=
  (natAbs_coeff_modByMonic_hPoly_le _ k).trans (coeffNorm1_iterDivByH_parityAmplifier_le ℓ j)

/-- **Lemma B.1 (`ℓ₁`-norm bound for `e_j`)**: `‖parityBaseDigit ℓ j‖₁` is at most
`2 * ((2 * ℓ) ^ j * 2 ^ (3 * ℓ))`. -/
theorem coeffNorm1_parityBaseDigit_le (ℓ j : ℕ) :
    coeffNorm1 (parityBaseDigit ℓ j) ≤ 2 * ((2 * ℓ) ^ j * 2 ^ (3 * ℓ)) :=
  (coeffNorm1_modByMonic_hPoly_le _).trans
    (Nat.mul_le_mul_left 2 (coeffNorm1_iterDivByH_parityAmplifier_le ℓ j))

/-! ### 4. Shared-total-order truncation and multivariate total-degree bound (Lemma 5.2) -/

/-- The `V`-series factor `B(y; V) = ∑ j ∈ range ℓ, e_j(y) h(y)^j V^j` in `A[X]`, where the
polynomial indeterminate `X` represents the shared formal truncation marker `V`. -/
def parityFactor {A : Type*} [CommRing A] (ℓ : ℕ) (y : A) : A[X] :=
  ∑ j ∈ range ℓ, C (evalInt y (parityBaseDigit ℓ j) * evalInt y hPoly ^ j) * X ^ j

/-- The linear map `S_ℓ(∑_s b_s V^s) = ∑ s ∈ range ℓ, b_s` summing the coefficients of
`V ^ 0, …, V ^ (ℓ - 1)`. -/
def sumCoeffsBelow {A : Type*} [Semiring A] (ℓ : ℕ) (P : A[X]) : A :=
  ∑ s ∈ range ℓ, P.coeff s

/-- The `s`-th coefficient of `parityFactor ℓ y` is `e_s(y) h(y)^s` for `s < ℓ` and `0`
otherwise. -/
theorem coeff_parityFactor {A : Type*} [CommRing A] (ℓ : ℕ) (y : A) (s : ℕ) :
    (parityFactor ℓ y).coeff s =
      if s < ℓ then evalInt y (parityBaseDigit ℓ s) * evalInt y hPoly ^ s else 0 := by
  rw [parityFactor, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_range]

/-- Evaluating `parityFactor ℓ y` at `V = 1` recovers `p_ℓ(y)`. -/
theorem eval_one_parityFactor {A : Type*} [CommRing A] (ℓ : ℕ) (y : A) :
    (parityFactor ℓ y).eval 1 = evalInt y (parityAmplifier ℓ) := by
  rw [parityFactor, ← coe_evalRingHom, map_sum, evalInt_parityAmplifier_eq_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [coe_evalRingHom, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one, evalInt_hPoly]

/-- At an integer `y`, the `s`-th coefficient of `parityFactor ℓ y` is divisible by `2 ^ s`. -/
theorem two_pow_dvd_coeff_parityFactor (ℓ : ℕ) (y : ℤ) (s : ℕ) :
    (2 : ℤ) ^ s ∣ (parityFactor ℓ y).coeff s := by
  rw [coeff_parityFactor]
  split_ifs with hs
  · rw [evalInt_int y hPoly]
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (two_dvd_eval_hPoly y) s) _
  · exact dvd_zero _

/-- Graded divisibility `2 ^ s ∣ coeff s` is preserved under polynomial multiplication. -/
theorem two_pow_dvd_coeff_mul {P Q : ℤ[X]}
    (hP : ∀ s, (2 : ℤ) ^ s ∣ P.coeff s) (hQ : ∀ s, (2 : ℤ) ^ s ∣ Q.coeff s) (s : ℕ) :
    (2 : ℤ) ^ s ∣ (P * Q).coeff s := by
  rw [coeff_mul]
  exact dvd_sum fun ij hij =>
    mem_antidiagonal.1 hij ▸ pow_add (2 : ℤ) ij.1 ij.2 ▸ mul_dvd_mul (hP ij.1) (hQ ij.2)

/-- Every `V ^ s`-coefficient of `∏ i ∈ I, parityFactor ℓ (y i)` at integer arguments `y i` is
divisible by `2 ^ s`. -/
theorem two_pow_dvd_coeff_prod_parityFactor {ι : Type*} (I : Finset ι) (ℓ : ℕ) (y : ι → ℤ)
    (s : ℕ) :
    (2 : ℤ) ^ s ∣ (∏ i ∈ I, parityFactor ℓ (y i)).coeff s := by
  classical
  induction I using Finset.induction_on generalizing s with
  | empty =>
    rw [prod_empty, coeff_one]
    split_ifs with hs <;> simp [hs]
  | insert a I ha ih =>
    rw [prod_insert ha]
    exact two_pow_dvd_coeff_mul (two_pow_dvd_coeff_parityFactor ℓ (y a)) ih s

/-- If `2 ^ s ∣ P.coeff s` for all `s`, then `sumCoeffsBelow ℓ P ≡ P.eval 1 (mod 2 ^ ℓ)`. -/
theorem sumCoeffsBelow_modEq_eval_one {P : ℤ[X]} {ℓ : ℕ}
    (hP : ∀ s, (2 : ℤ) ^ s ∣ P.coeff s) :
    sumCoeffsBelow ℓ P ≡ P.eval 1 [ZMOD (2 : ℤ) ^ ℓ] := by
  rw [eval_eq_sum_range' (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right ℓ _))]
  simp only [one_pow, mul_one]
  rw [← sum_range_add_sum_Ico _ (le_max_left ℓ _), sumCoeffsBelow, Int.modEq_iff_dvd,
    add_sub_cancel_left]
  exact dvd_sum fun s hs => (pow_dvd_pow 2 (mem_Ico.1 hs).1).trans (hP s)

/-- **Lemma 5.2 (shared-`V` truncation congruence)**: for integers `y i`,
`S_ℓ(∏ i ∈ I, B_i(V)) ≡ ∏ i ∈ I, (if Even (y i) then 1 else 0) (mod 2 ^ ℓ)`. At `ℓ = 0` the
modulus is `1`. -/
theorem sumCoeffsBelow_prod_parityFactor_modEq {ι : Type*} (I : Finset ι) (ℓ : ℕ)
    (y : ι → ℤ) [∀ i, Decidable (Even (y i))] :
    sumCoeffsBelow ℓ (∏ i ∈ I, parityFactor ℓ (y i)) ≡
      (∏ i ∈ I, if Even (y i) then (1 : ℤ) else 0) [ZMOD (2 : ℤ) ^ ℓ] := by
  obtain rfl | hℓ := Nat.eq_zero_or_pos ℓ
  · simp only [pow_zero, Int.modEq_one]
  refine (sumCoeffsBelow_modEq_eval_one (two_pow_dvd_coeff_prod_parityFactor I ℓ y)).trans ?_
  rw [eval_prod, prod_congr rfl fun i _ =>
    (eval_one_parityFactor ℓ (y i)).trans (evalInt_int (y i) _)]
  exact Int.ModEq.prod fun i _ => parityAmplifier_eval_modEq_two_pow hℓ (y i)

/-- Evaluating an affine integer polynomial (`natDegree ≤ 1`) at `y : MvPolynomial σ R` preserves
any upper bound `d` on `y.totalDegree`. -/
theorem totalDegree_evalInt_of_natDegree_le_one {σ R : Type*} [CommRing R] {q : ℤ[X]}
    (hq : q.natDegree ≤ 1) {y : MvPolynomial σ R} {d : ℕ} (hy : y.totalDegree ≤ d) :
    (evalInt y q).totalDegree ≤ d := by
  rw [evalInt, eq_X_add_C_of_natDegree_le_one hq, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, eval₂_C]
  simp only [eq_intCast, ← zsmul_one, smul_mul_assoc, one_mul]
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le
    ((MvPolynomial.totalDegree_smul_le _ _).trans hy)
    ((MvPolynomial.totalDegree_smul_le _ _).trans (by simp)))

/-- Evaluating `hPoly = X ^ 2 - X` at `y : MvPolynomial σ R` of total degree at most `d` gives
a polynomial of total degree at most `2 * d`. -/
theorem totalDegree_evalInt_hPoly_le {σ R : Type*} [CommRing R] {y : MvPolynomial σ R} {d : ℕ}
    (hy : y.totalDegree ≤ d) :
    (evalInt y hPoly).totalDegree ≤ 2 * d := by
  rw [evalInt_hPoly]
  refine (MvPolynomial.totalDegree_sub (y ^ 2) y).trans (max_le ?_ (hy.trans (by omega)))
  exact (MvPolynomial.totalDegree_pow y 2).trans (Nat.mul_le_mul_left 2 hy)

/-- For `y : MvPolynomial σ R` of total degree at most `d`, the `V ^ s`-coefficient of
`parityFactor ℓ y` has total degree at most `d + 2 * d * s`. -/
theorem totalDegree_coeff_parityFactor_le {σ R : Type*} [CommRing R] (ℓ : ℕ)
    {y : MvPolynomial σ R} {d : ℕ} (hy : y.totalDegree ≤ d) (s : ℕ) :
    ((parityFactor ℓ y).coeff s).totalDegree ≤ d + 2 * d * s := by
  rw [coeff_parityFactor]
  split_ifs with hs
  · exact (MvPolynomial.totalDegree_mul _ _).trans (add_le_add
      (totalDegree_evalInt_of_natDegree_le_one (natDegree_parityBaseDigit_le ℓ s) hy)
      ((MvPolynomial.totalDegree_pow _ s).trans
        ((Nat.mul_le_mul_left s (totalDegree_evalInt_hPoly_le hy)).trans_eq (by ring))))
  · simp only [MvPolynomial.totalDegree_zero, zero_le]

/-- Graded total-degree bounds `totalDegree (coeff s) ≤ M + 2 * d * s` add in the offset `M`
under multiplication in `(MvPolynomial σ R)[X]`. -/
theorem totalDegree_coeff_mul_le {σ R : Type*} [CommRing R] {P Q : (MvPolynomial σ R)[X]}
    {M₁ M₂ d : ℕ}
    (hP : ∀ s, (P.coeff s).totalDegree ≤ M₁ + 2 * d * s)
    (hQ : ∀ s, (Q.coeff s).totalDegree ≤ M₂ + 2 * d * s) (s : ℕ) :
    ((P * Q).coeff s).totalDegree ≤ (M₁ + M₂) + 2 * d * s := by
  rw [coeff_mul]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun ij hij =>
    (MvPolynomial.totalDegree_mul _ _).trans ?_)
  linarith [hP ij.1, hQ ij.2, congr_arg (2 * d * ·) (mem_antidiagonal.1 hij)]

/-- **Lemma 5.2 (graded total-degree bound)**: if every `y i` (`i ∈ I`) has multivariate total
degree at most `d`, then the `V ^ s`-coefficient of `∏ i ∈ I, parityFactor ℓ (y i)` has total
degree at most `d * (#I + 2 * s)`. -/
theorem totalDegree_coeff_prod_parityFactor_le {ι σ R : Type*} [CommRing R] (I : Finset ι)
    (ℓ : ℕ) {y : ι → MvPolynomial σ R} {d : ℕ} (hy : ∀ i ∈ I, (y i).totalDegree ≤ d) (s : ℕ) :
    ((∏ i ∈ I, parityFactor ℓ (y i)).coeff s).totalDegree ≤ d * (#I + 2 * s) := by
  classical
  induction I using Finset.induction_on generalizing s with
  | empty =>
    rw [prod_empty, coeff_one]
    split_ifs <;> simp
  | insert a I ha ih =>
    rw [prod_insert ha, card_insert_of_notMem ha]
    refine (totalDegree_coeff_mul_le (M₁ := d) (M₂ := d * #I) (d := d)
      (totalDegree_coeff_parityFactor_le ℓ (hy a (mem_insert_self a I)))
      (fun k => (ih (fun i hi => hy i (mem_insert_of_mem hi)) k).trans_eq (by ring))
      s).trans_eq (by ring)

/-- **Lemma 5.2 (retained coefficient total-degree bound)**: for `s < ℓ`, the `V ^ s`-coefficient
of `∏ i ∈ I, parityFactor ℓ (y i)` has total degree at most `d * (#I + 2 * (ℓ - 1))`. -/
theorem totalDegree_coeff_prod_parityFactor_le_of_lt {ι σ R : Type*} [CommRing R] (I : Finset ι)
    {ℓ s : ℕ} (hs : s < ℓ) {y : ι → MvPolynomial σ R} {d : ℕ}
    (hy : ∀ i ∈ I, (y i).totalDegree ≤ d) :
    ((∏ i ∈ I, parityFactor ℓ (y i)).coeff s).totalDegree ≤ d * (#I + 2 * (ℓ - 1)) := by
  exact (totalDegree_coeff_prod_parityFactor_le I ℓ hy s).trans (Nat.mul_le_mul_left d (by omega))

/-- **Lemma 5.2 (truncated sum total-degree bound)**: the truncated coefficient sum
`sumCoeffsBelow ℓ (∏ i ∈ I, parityFactor ℓ (y i))` has total degree at most
`d * (#I + 2 * (ℓ - 1))`. -/
theorem totalDegree_sumCoeffsBelow_prod_parityFactor_le {ι σ R : Type*} [CommRing R]
    (I : Finset ι) (ℓ : ℕ) {y : ι → MvPolynomial σ R} {d : ℕ}
    (hy : ∀ i ∈ I, (y i).totalDegree ≤ d) :
    (sumCoeffsBelow ℓ (∏ i ∈ I, parityFactor ℓ (y i))).totalDegree ≤
      d * (#I + 2 * (ℓ - 1)) := by
  rw [sumCoeffsBelow]
  exact (MvPolynomial.totalDegree_finsetSum _ _).trans
    (Finset.sup_le fun s hs => totalDegree_coeff_prod_parityFactor_le_of_lt I (mem_range.1 hs) hy)

end Polynomial
