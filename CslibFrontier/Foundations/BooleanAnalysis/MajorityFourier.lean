/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Influence
public import CslibFrontier.Foundations.BooleanAnalysis.LongCode
public import CslibFrontier.Foundations.Data.BitString.Threshold
import CslibFrontier.Foundations.BooleanAnalysis.TransitiveSymmetric
import CslibFrontier.Foundations.Data.BitString.AgreeExpect
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The Fourier coefficients of majority

The majority of an odd number `n = 2 m + 1` of bits, read as signs, has Fourier coefficient `0` on
every set of even size, and on a set of odd size `k = 2 j + 1` the coefficient
`(-1) ^ j C(m, j) / C(2 m, 2 j) · C(2 m, m) / 4 ^ m`
(`BitString.fourierCoeff_signVal_majority_of_even`,
`BitString.fourierCoeff_signVal_majority_of_card_eq`) [O'Donnell, Theorem 5.19][ODonnell2014]. In
the book's notation this is `(-1) ^ ((k - 1) / 2) C((n - 1) / 2, (k - 1) / 2) / C(n - 1, k - 1) ·
2 / 2 ^ n · C(n - 1, (n - 1) / 2)`.

The even coefficients vanish because majority is odd (`BitString.isOdd_majority`): it has no ties
(`majority_eq_strictMajority` in `Data.BitString.Threshold`). For the odd ones, the derivative of
majority in a coordinate `i` is the indicator that the other `2 m` bits tie
(`BitString.derivative_signVal_majority`), so the coefficient on `S ∋ i` is the coefficient of that
indicator on `S \ {i}`. A function of the weight has the same coefficient on all sets of a given
size (`BitString.fourierCoeff_eq_of_card_eq`), so it suffices to sum the coefficients over all
`2 j`-subsets `T` of the other coordinates. At a string with `m` true and `m` false bits among the
other `2 m` coordinates, the characters of these sets sum to the coefficient of `X ^ (2 m - 2 j)` in
`(X - 1) ^ m (X + 1) ^ m = (X ^ 2 - 1) ^ m`, which is `(-1) ^ j C(m, j)`
(`BitString.sum_powersetCard_chi`); such strings have density `C(2 m, m) / 4 ^ m`
(`BitString.expect_ite_card_filter_eq` in `Data.BitString.AgreeExpect`). The book instead compares
two expansions of the noise operator applied to the tie indicator.

## Main results

* `Cslib.BitString.sum_powersetCard_chi`: the sum of the characters of the `2 j`-subsets at a
  balanced string.
* `Cslib.BitString.isOdd_majority`, `Cslib.BitString.derivative_signVal_majority`: majority of an
  odd number of bits is odd, and its derivative is the tie indicator.
* `Cslib.BitString.fourierCoeff_signVal_majority_of_even`,
  `Cslib.BitString.fourierCoeff_signVal_majority_of_card_eq`: the Fourier coefficients of majority.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Function Polynomial
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- At a string with `m` true and `m` false bits on `s`, the characters of the `2 j`-subsets of
`s` sum to `(-1) ^ j C(m, j)`: by Vieta's formula the sum is a coefficient of
`∏_{l ∈ s} (X + χ(x_l)) = (X - 1) ^ m (X + 1) ^ m = (X ^ 2 - 1) ^ m`. -/
theorem sum_powersetCard_chi (s : Finset ι) (x : ι → Bool) (m j : ℕ)
    (htrue : #{l ∈ s | x l = true} = m) (hfalse : #{l ∈ s | x l = false} = m) :
    ∑ T ∈ s.powersetCard (2 * j), chi ℝ T x = (-1) ^ j * m.choose j := by
  have hs : #s = 2 * m := by
    rw [← card_filter_add_card_filter_not (s := s) (fun l => x l = true)]
    simp only [Bool.not_eq_true, htrue, hfalse]
    omega
  rcases lt_or_ge m j with hjm | hjm
  · rw [powersetCard_eq_empty.2 (by omega), sum_empty, Nat.choose_eq_zero_of_lt hjm]
    simp
  have hV := Finset.prod_X_add_C_coeff s (fun l => ((-1 : ℝ) ^ (x l).toNat)) (k := #s - 2 * j)
    (by omega)
  rw [show #s - (#s - 2 * j) = 2 * j by omega] at hV
  simp only [chi]
  rw [← hV]
  have hprod : ∏ l ∈ s, (X + C ((-1 : ℝ) ^ (x l).toNat)) =
      expand ℝ 2 ((X + C (-1)) ^ m) := by
    have h (b : Bool) : ∏ l ∈ s with x l = b, (X + C ((-1 : ℝ) ^ (x l).toNat)) =
        (X + C ((-1) ^ b.toNat)) ^ #{l ∈ s | x l = b} :=
      prod_eq_pow_card fun l hl => by rw [(mem_filter.1 hl).2]
    rw [← prod_filter_mul_prod_filter_not s (fun l => x l = true)]
    simp only [Bool.not_eq_true]
    rw [h, h, htrue, hfalse, ← mul_pow, map_pow (expand ℝ 2)]
    congr 1
    simp only [Bool.toNat_true, Bool.toNat_false, pow_one, pow_zero, map_add, expand_X, map_neg,
      map_one]
    ring
  rw [hprod, coeff_expand two_pos, ite_eq_left ⟨m - j, by omega⟩,
    show (#s - 2 * j) / 2 = m - j by omega, coeff_X_add_C_pow,
    show m - (m - j) = j by omega, Nat.choose_symm hjm]

/-- **Majority of an odd number of bits is odd**: complementing the input complements the output.
-/
theorem isOdd_majority (m : ℕ) : IsOdd (majority (2 * m + 1)) := fun x => by
  rw [show (x + fun _ => true) = fun i => !x i from funext fun i => Bool.xor_true (x i),
    majority_eq_strictMajority, strictMajority_not, majority_eq_strictMajority]

/-- **The derivative of majority** in `i`, read as signs, is the indicator that exactly half of
the other `2 m` bits are true, that is, that `i` is pivotal
[O'Donnell, proof of Theorem 5.19][ODonnell2014]. -/
theorem derivative_signVal_majority (m : ℕ) (i : Fin (2 * m + 1)) (x : Fin (2 * m + 1) → Bool) :
    derivative i (fun x => signVal (majority (2 * m + 1) x)) x =
      if #{l ∈ univ.erase i | x l = true} = m then 1 else 0 := by
  have ht : weight (update x i true) = weight (update x i false) + 1 := by
    rw [← weight_update_true (x := update x i false) (i := i) (by simp), update_idem]
  rw [derivative, card_filter_erase_eq_weight_update_false, majority, threshold_apply,
    threshold_apply, ht, show (2 * m + 1 + 1) / 2 = m + 1 by omega]
  generalize weight (update x i false) = w
  by_cases h : w = m
  · simp [h]
  · simp [h, show m + 1 ≤ w + 1 ↔ m + 1 ≤ w by omega]

/-- **The even Fourier coefficients of majority vanish** [O'Donnell, Theorem 5.19][ODonnell2014]:
majority of an odd number of bits, read as signs, is odd. -/
theorem fourierCoeff_signVal_majority_of_even (m : ℕ) {S : Finset (Fin (2 * m + 1))}
    (hS : Even #S) : fourierCoeff (fun x => signVal (majority (2 * m + 1) x)) S = 0 :=
  (isOdd_majority m).fourierCoeff_of_even hS

/-- **The odd Fourier coefficients of majority** [O'Donnell, Theorem 5.19][ODonnell2014]: for
majority of `2 m + 1` bits read as signs, the coefficient on a set of size `2 j + 1` is
`(-1) ^ j C(m, j) / C(2 m, 2 j) · C(2 m, m) / 4 ^ m`. -/
theorem fourierCoeff_signVal_majority_of_card_eq (m j : ℕ) {S : Finset (Fin (2 * m + 1))}
    (hS : #S = 2 * j + 1) :
    fourierCoeff (fun x => signVal (majority (2 * m + 1) x)) S =
      (-1) ^ j * m.choose j / (2 * m).choose (2 * j) * ((2 * m).choose m / 4 ^ m) := by
  set f : (Fin (2 * m + 1) → Bool) → ℝ := fun x => signVal (majority (2 * m + 1) x)
  have hsym : ∀ x y, weight x = weight y → f x = f y := fun x y h =>
    congrArg signVal (isSymmetric_majority x y h)
  obtain ⟨i, hi⟩ : S.Nonempty := card_pos.1 (by omega)
  have hjm : 2 * j ≤ 2 * m := by
    have := S.card_le_univ.trans_eq (Fintype.card_fin _)
    omega
  -- every coefficient of the derivative on a `2 j`-set avoiding `i` is the coefficient on `S`
  have hT : ∀ T ∈ (univ.erase i).powersetCard (2 * j),
      fourierCoeff (derivative i f) T = fourierCoeff f S := fun T hT => by
    obtain ⟨hTs, hTc⟩ := mem_powersetCard.1 hT
    have hiT : i ∉ T := fun h => by simpa using hTs h
    rw [fourierCoeff_derivative, ite_eq_right hiT]
    exact fourierCoeff_eq_of_card_eq hsym (by rw [card_insert_of_notMem hiT, hTc, hS])
  have hsum : ∑ T ∈ (univ.erase i).powersetCard (2 * j), fourierCoeff (derivative i f) T =
      (-1) ^ j * m.choose j * ((2 * m).choose m / 4 ^ m) := by
    simp only [fourierCoeff, ← expect_sum_comm, ← mul_sum]
    have hpt (x : Fin (2 * m + 1) → Bool) :
        derivative i f x * ∑ T ∈ (univ.erase i).powersetCard (2 * j), chi ℝ T x =
          (-1) ^ j * m.choose j * if #{l ∈ univ.erase i | x l = true} = m then 1 else 0 := by
      rw [derivative_signVal_majority]
      split_ifs with hx
      · rw [one_mul, mul_one, sum_powersetCard_chi _ x m j hx]
        have := card_filter_add_card_filter_not (s := univ.erase i) (fun l => x l = true)
        simp only [Bool.not_eq_true, card_erase_of_mem (mem_univ i), card_univ,
          Fintype.card_fin] at this
        omega
      · simp
    simp only [hpt, ← mul_expect]
    rw [expect_ite_card_filter_eq, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin,
      show 2 * m + 1 - 1 = 2 * m by omega, pow_mul]
    norm_num
  rw [sum_congr rfl hT, sum_const, card_powersetCard, card_erase_of_mem (mem_univ i), card_univ,
    Fintype.card_fin, show 2 * m + 1 - 1 = 2 * m by omega, nsmul_eq_mul] at hsum
  rw [div_mul_eq_mul_div, eq_div_iff (Nat.cast_ne_zero.2 (Nat.choose_pos hjm).ne'), mul_comm]
  exact hsum

end Cslib.BitString
