/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.LevelWeight
public import CslibFrontier.Foundations.BooleanAnalysis.LongCode
public import CslibFrontier.Foundations.Data.BitString.Threshold
import CslibFrontier.Foundations.BooleanAnalysis.TransitiveSymmetric
import CslibFrontier.Foundations.Data.BitString.AgreeExpect
import CslibFrontier.Foundations.Data.Nat.Choose.Vandermonde
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
`(X - 1) ^ m (X + 1) ^ m = (X ^ 2 - 1) ^ m` by Vieta's formula, which is `(-1) ^ j C(m, j)`; such
strings have density `C(2 m, m) / 4 ^ m`
(`BitString.expect_ite_card_filter_eq` in `Data.BitString.AgreeExpect`). The book instead compares
two expansions of the noise operator applied to the tie indicator.

For an even number `2 m` of bits, ties are accepted by `majority`. Pairing each string with its
complement shows that the constant Fourier coefficient is `-C(2 m, m) / 4 ^ m`
(`BitString.fourierCoeff_signVal_majority_two_mul_empty`).

From the explicit formula, no coefficient exceeds the one on a singleton, `C(2 m, m) / 4 ^ m`,
since `C(m, j) ≤ C(2 m, 2 j)`, and up to size `m` the coefficients decrease in size, by the ratio
`|S| / (2 m - |S|)` from `|S|` to `|S| + 2`
(`BitString.fourierCoeff_signVal_majority_singleton`,
`BitString.abs_fourierCoeff_signVal_majority_le_singleton`,
`BitString.abs_fourierCoeff_signVal_majority_le_of_card_le`)
[O'Donnell, Exercise 5.21][ODonnell2014]. The exercise's asymptotic
`C(2 m, m) / 4 ^ m ∼ √(2 / (n π))` is, squared, the degree-one case `W^1[Maj_n] → 2 / π` of
`BitString.tendsto_levelWeight_signVal_majority`. The coefficients on sets `S`, `T` with
`|S| + |T| = n + 1` agree up to the sign `(-1) ^ ((n - 1) / 2)`, so `(n - k + 1) W^{n-k+1} = k W^k`
(`BitString.fourierCoeff_signVal_majority_of_card_add_card`,
`BitString.card_mul_levelWeight_signVal_majority`)
[O'Donnell, Corollary 5.20][ODonnell2014]. The weight `W^k` on each odd level `k` strictly
decreases as `n` grows (`BitString.levelWeight_signVal_majority_succ_lt`)
[O'Donnell, Corollary 5.21][ODonnell2014]. Hence the noise stability
`Stab_ρ[Maj_n] = ∑_k ρ ^ k W^k` strictly decreases from `n` to `n + 2` for `0 < ρ < 1`
(`BitString.noiseStability_signVal_majority_succ_lt`): the weight lost on the levels up to `n`
moves to the new top level `n + 2`, where `ρ ^ k` is smaller
[O'Donnell, Theorem 5.18][ODonnell2014]. The limits of the level weights and of the noise
stability (Theorems 5.22 and 2.45) and the lower bound of Theorem 5.18 are in
`CslibFrontier.Foundations.BooleanAnalysis.MajorityStability`.

## Usage

Majority of `n = 2 m + 1` bits read as signs is `fun x => signVal (majority (2 * m + 1) x)` on
`Fin (2 * m + 1) → Bool`, the book's `Maj_n` with `true` read as `−1`; the statements write odd set
sizes as `2 * j + 1`. On a concrete set, discharge the size hypothesis of
`BitString.fourierCoeff_signVal_majority_of_card_eq` by `decide` or `simp` and evaluate the right
side with `norm_num [Nat.choose]`. Level weights are `levelWeight k f` from
`BooleanAnalysis.LevelWeight`, and `BitString.noiseStability_eq_sum_levelWeight` there turns noise
stability into a sum over levels. Import `BooleanAnalysis.TransitiveSymmetric` as well to use
`BitString.fourierCoeff_eq_of_card_eq`, which this module imports privately. The checked clients
in
[CslibFrontierTests/BooleanAnalysisMajorityFourier.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisMajorityFourier.lean)
compute the coefficients of majority of three and five bits, check two of them by brute force,
check each step of the proof on small cases, compare the level weights and noise stability of
majority of three and five bits, and follow the size of the coefficients of majority of seven bits
across the levels.

## Main results

* `Cslib.BitString.isOdd_majority`, `Cslib.BitString.derivative_signVal_majority`: majority of an
  odd number of bits is odd, and its derivative is the tie indicator.
* `Cslib.BitString.fourierCoeff_signVal_majority_of_even`,
  `Cslib.BitString.fourierCoeff_signVal_majority_of_card_eq`: the Fourier coefficients of majority.
* `Cslib.BitString.fourierCoeff_signVal_majority_two_mul_empty`: the constant coefficient for an
  even number of inputs, with ties accepted.
* `Cslib.BitString.fourierCoeff_signVal_majority_singleton`,
  `Cslib.BitString.abs_fourierCoeff_signVal_majority_le_singleton`,
  `Cslib.BitString.abs_fourierCoeff_signVal_majority_le_of_card_le`: the largest coefficients of
  majority are on singletons, and the odd coefficients decrease in size up to level `m + 2`.
* `Cslib.BitString.levelWeight_signVal_majority_of_odd`,
  `Cslib.BitString.levelWeight_signVal_majority_of_even`: the level weights of majority.
* `Cslib.BitString.fourierCoeff_signVal_majority_of_card_add_card`,
  `Cslib.BitString.card_mul_levelWeight_signVal_majority`: Corollary 5.20.
* `Cslib.BitString.levelWeight_signVal_majority_succ_lt`: Corollary 5.21.
* `Cslib.BitString.noiseStability_signVal_majority_succ_lt`: the noise stability of majority
  decreases in `n`, the monotonicity claim of Theorem 5.18.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Function Polynomial
open scoped BigOperators Nat

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- At a string with `m` true and `m` false bits on `s`, the characters of the `2 j`-subsets of
`s` sum to `(-1) ^ j C(m, j)`: by Vieta's formula the sum is a coefficient of
`∏_{l ∈ s} (X + χ(x_l)) = (X - 1) ^ m (X + 1) ^ m = (X ^ 2 - 1) ^ m`. -/
private theorem sum_powersetCard_chi (s : Finset ι) (x : ι → Bool) (m j : ℕ)
    (htrue : #{l ∈ s | x l = true} = m) (hfalse : #{l ∈ s | x l = false} = m) :
    ∑ T ∈ s.powersetCard (2 * j), chi ℝ T x = (-1) ^ j * m.choose j := by
  have hs : #s = 2 * m := by
    have hcard := card_filter_add_card_filter_not (s := s) (fun l => x l = true)
    simp only [Bool.not_eq_true, htrue, hfalse] at hcard; omega
  rcases lt_or_ge m j with hjm | hjm
  · simp [powersetCard_eq_empty.2 (hs ▸ Nat.mul_lt_mul_of_pos_left hjm two_pos),
      Nat.choose_eq_zero_of_lt hjm]
  have hV := Finset.prod_X_add_C_coeff s (fun l => ((-1 : ℝ) ^ (x l).toNat)) (k := #s - 2 * j)
    (by omega)
  rw [show #s - (#s - 2 * j) = 2 * j by omega] at hV
  simp only [chi, ← hV]
  have hprod : ∏ l ∈ s, (X + C ((-1 : ℝ) ^ (x l).toNat)) =
      expand ℝ 2 ((X + C (-1)) ^ m) := by
    have h (b : Bool) : ∏ l ∈ s with x l = b, (X + C ((-1 : ℝ) ^ (x l).toNat)) =
        (X + C ((-1) ^ b.toNat)) ^ #{l ∈ s | x l = b} :=
      prod_eq_pow_card fun l hl => by rw [(mem_filter.1 hl).2]
    rw [← prod_filter_mul_prod_filter_not s (fun l => x l = true)]
    simp only [Bool.not_eq_true, h, htrue, hfalse, ← mul_pow, map_pow (expand ℝ 2)]
    congr 1
    simp [Bool.toNat_true, Bool.toNat_false, expand_X]; ring
  rw [hprod, coeff_expand two_pos, ite_eq_left ⟨m - j, by omega⟩,
    show (#s - 2 * j) / 2 = m - j by omega, coeff_X_add_C_pow,
    show m - (m - j) = j by omega, Nat.choose_symm hjm]

/-- **Majority of an odd number of bits is odd**: complementing the input complements the output.
-/
theorem isOdd_majority (m : ℕ) : IsOdd (majority (2 * m + 1)) := fun x => by
  rw [show (x + fun _ => true) = fun i => !x i from funext fun i => Bool.xor_true (x i),
    majority_eq_strictMajority, strictMajority_not, majority_eq_strictMajority]

/-- The constant Fourier coefficient of majority on `2 m` bits is the negative probability of
a tie: complementary inputs cancel except when both have weight `m`, where both are accepted. -/
theorem fourierCoeff_signVal_majority_two_mul_empty (m : ℕ) :
    fourierCoeff (fun x => signVal (majority (2 * m) x)) ∅ =
      -((2 * m).choose m / (4 : ℝ) ^ m) := by
  let f : (Fin (2 * m) → Bool) → ℝ := fun x => signVal (majority (2 * m) x)
  have hcomp : (𝔼 x, f (x + fun _ => true)) = 𝔼 x, f x :=
    Fintype.expect_equiv (Equiv.addRight (fun _ : Fin (2 * m) => true)) _ _ fun _ => rfl
  have hpair (x : Fin (2 * m) → Bool) :
      f x + f (x + fun _ => true) = (-2 : ℝ) * (if weight x = m then 1 else 0) := by
    have hnot : weight (fun i => !x i) + weight x = 2 * m := by simpa using weight_not_add x
    have hhalf : (2 * m + 1) / 2 = m := by omega
    have hcomp_eq : (x + fun _ => true) = fun i => !x i := funext fun i => Bool.xor_true (x i)
    simp only [f, hcomp_eq, majority, threshold_apply, hhalf, signVal, decide_eq_true_eq]
    split_ifs <;> first | omega | norm_num
  have htie : (𝔼 x : Fin (2 * m) → Bool, if weight x = m then (1 : ℝ) else 0) =
      (2 * m).choose m / (4 : ℝ) ^ m := by
    change (𝔼 x : Fin (2 * m) → Bool, if #{i ∈ univ | x i = true} = m then (1 : ℝ) else 0) = _
    rw [expect_ite_card_filter_eq, card_univ, Fintype.card_fin, pow_mul]; norm_num
  have hmean : (𝔼 x, f x) + (𝔼 x, f x) =
      (-2 : ℝ) * ((2 * m).choose m / (4 : ℝ) ^ m) := by
    calc
      _ = 𝔼 x, (f x + f (x + fun _ => true)) := by rw [expect_add_distrib, hcomp]
      _ = (-2 : ℝ) * ((2 * m).choose m / (4 : ℝ) ^ m) := by
        simp only [hpair, ← mul_expect, htie]
  simp only [fourierCoeff_empty, f] at hmean ⊢
  linarith

/-- **The derivative of majority** in `i`, read as signs, is the indicator that exactly half of
the other `2 m` bits are true, that is, that `i` is pivotal
[O'Donnell, proof of Theorem 5.19][ODonnell2014]. -/
theorem derivative_signVal_majority (m : ℕ) (i : Fin (2 * m + 1)) (x : Fin (2 * m + 1) → Bool) :
    derivative i (fun x => signVal (majority (2 * m + 1) x)) x =
      if #{l ∈ univ.erase i | x l = true} = m then 1 else 0 := by
  have ht : weight (update x i true) = weight (update x i false) + 1 := by
    rw [← weight_update_true (x := update x i false) (i := i) (by simp), update_idem]
  have hhalf : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [derivative, card_filter_erase_eq_weight_update_false, majority, threshold_apply,
    threshold_apply, ht, hhalf]
  simp only [signVal, decide_eq_true_eq]
  split_ifs <;> first | omega | norm_num

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
  rwa [div_mul_eq_mul_div, eq_div_iff (Nat.cast_ne_zero.2 (Nat.choose_pos hjm).ne'), mul_comm]

/-! ### Levels of majority -/

/-- The size of the odd coefficients of majority, in factorials. -/
private theorem choose_div_choose_mul_choose_div {m j : ℕ} (hj : j ≤ m) :
    (m.choose j : ℝ) / (2 * m).choose (2 * j) * ((2 * m).choose m / 4 ^ m) =
      (2 * j)! * (2 * (m - j))! / (j ! * (m - j)! * m ! * 4 ^ m) := by
  rw [Nat.cast_choose ℝ hj, Nat.cast_choose ℝ (by omega : 2 * j ≤ 2 * m),
    Nat.cast_choose ℝ (by omega : m ≤ 2 * m), show 2 * m - 2 * j = 2 * (m - j) by omega,
    show 2 * m - m = m by omega]
  field_simp

/-- **The level weights of majority**: the Fourier weight `W^{2 j + 1}` of majority of `2 m + 1`
bits, read as signs, is `C(2 m + 1, 2 j + 1)` times the square of the coefficient on a set of size
`2 j + 1`. -/
theorem levelWeight_signVal_majority_of_odd (m j : ℕ) :
    levelWeight (2 * j + 1) (fun x => signVal (majority (2 * m + 1) x)) =
      (2 * m + 1).choose (2 * j + 1) *
        ((m.choose j : ℝ) / (2 * m).choose (2 * j) * ((2 * m).choose m / 4 ^ m)) ^ 2 := by
  rw [levelWeight, sum_congr rfl fun S hS =>
    congrArg (· ^ 2) (fourierCoeff_signVal_majority_of_card_eq m j (mem_filter.1 hS).2),
    sum_const, nsmul_eq_mul]
  congr 1
  · simp
  · rw [mul_div_assoc, mul_assoc, mul_pow, ← pow_mul, mul_comm j 2, pow_mul]; norm_num

/-- Majority has no Fourier weight on the levels of even size. -/
theorem levelWeight_signVal_majority_of_even (m : ℕ) {k : ℕ} (hk : Even k) :
    levelWeight k (fun x => signVal (majority (2 * m + 1) x)) = 0 :=
  sum_eq_zero fun S hS => by
    simp [fourierCoeff_signVal_majority_of_even m ((mem_filter.1 hS).2 ▸ hk)]

/-- The Fourier coefficient of majority of `2 m + 1` bits, read as signs, on a singleton is
`C(2 m, m) / 4 ^ m`. -/
theorem fourierCoeff_signVal_majority_singleton (m : ℕ) (i : Fin (2 * m + 1)) :
    fourierCoeff (fun x => signVal (majority (2 * m + 1) x)) {i} = (2 * m).choose m / 4 ^ m := by
  simpa using fourierCoeff_signVal_majority_of_card_eq m 0 (card_singleton i)

/-- **The largest Fourier coefficients of majority are on singletons**
[O'Donnell, Exercise 5.21][ODonnell2014]: `‖Maĵ‖_∞ = Maĵ({i})`. Every coefficient of majority of
`2 m + 1` bits, read as signs, is at most the coefficient `C(2 m, m) / 4 ^ m` on a singleton in
absolute value, since `C(m, j) ≤ C(2 m, 2 j)`. The exercise's asymptotic `√(2 / (n π))` is not
formalized. -/
theorem abs_fourierCoeff_signVal_majority_le_singleton (m : ℕ) (S : Finset (Fin (2 * m + 1)))
    (i : Fin (2 * m + 1)) :
    |fourierCoeff (fun x => signVal (majority (2 * m + 1) x)) S| ≤
      fourierCoeff (fun x => signVal (majority (2 * m + 1) x)) {i} := by
  rw [fourierCoeff_signVal_majority_singleton]
  rcases Nat.even_or_odd #S with he | ⟨j, hj⟩
  · rw [fourierCoeff_signVal_majority_of_even m he, abs_zero]; positivity
  rw [fourierCoeff_signVal_majority_of_card_eq m j hj, mul_div_assoc, abs_mul, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  refine mul_le_of_le_one_left (by positivity) (div_le_one_of_le₀ ?_ (by positivity))
  rcases le_or_gt j m with hjm | hjm
  · exact_mod_cast two_mul j ▸
      (Nat.choose_le_choose_add_add m j j).trans (Nat.choose_le_choose _ (by omega))
  · simp [Nat.choose_eq_zero_of_lt hjm]

/-- One step of the decrease: from level `2 j + 1 ≤ m` to level `2 j + 3`, the coefficients of
majority shrink by the factor `(2 j + 1) / (2 m - 2 j - 1) ≤ 1`. -/
private theorem choose_div_choose_succ_le {m j : ℕ} (hjm : 2 * j + 1 ≤ m) :
    (m.choose (j + 1) : ℝ) / (2 * m).choose (2 * (j + 1)) ≤
      (m.choose j : ℝ) / (2 * m).choose (2 * j) := by
  have hc : (0 : ℝ) < (2 * m).choose m / 4 ^ m := by
    have := Nat.choose_pos (by omega : m ≤ 2 * m); positivity
  rw [← mul_le_mul_iff_of_pos_right hc]
  obtain ⟨r, rfl⟩ : ∃ r, m = j + 1 + r := ⟨m - j - 1, by omega⟩
  rw [choose_div_choose_mul_choose_div (by omega), choose_div_choose_mul_choose_div (by omega),
    show j + 1 + r - (j + 1) = r by omega, show j + 1 + r - j = r + 1 by omega]
  simp only [mul_add, mul_one, Nat.factorial_succ]
  push_cast
  have hq : (2 * (j : ℝ) + 1) / (2 * r + 1) ≤ 1 :=
    (div_le_one (by positivity)).2 (by gcongr; omega)
  refine le_of_eq_of_le ?_ (mul_le_of_le_one_right (by positivity) hq)
  field_simp
  ring

/-- **The Fourier coefficients of majority decrease in size**
[O'Donnell, Exercise 5.21][ODonnell2014]: for majority of `2 m + 1` bits and sets `S`, `T` of odd
sizes `|S| ≤ |T| ≤ m + 2`, the coefficient on `T` is at most the one on `S` in absolute value. Each
step from `|S|` to `|S| + 2` multiplies the size by `|S| / (2 m - |S|)`, so the book's range
`|T| ≤ m` extends to `m + 2`, with equality at the last step from `m`. -/
theorem abs_fourierCoeff_signVal_majority_le_of_card_le (m : ℕ)
    {S T : Finset (Fin (2 * m + 1))} (hS : Odd #S) (hT : Odd #T) (hST : #S ≤ #T)
    (hTm : #T ≤ m + 2) :
    |fourierCoeff (fun x => signVal (majority (2 * m + 1) x)) T| ≤
      |fourierCoeff (fun x => signVal (majority (2 * m + 1) x)) S| := by
  obtain ⟨j, hj⟩ := hS
  obtain ⟨k, hk⟩ := hT
  rw [fourierCoeff_signVal_majority_of_card_eq m k hk,
    fourierCoeff_signVal_majority_of_card_eq m j hj]
  simp only [mul_div_assoc, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hjk : j ≤ k := by omega
  have hkm : 2 * k ≤ m + 1 := by omega
  clear hk hST hTm
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hjk ih => exact (choose_div_choose_succ_le (by omega)).trans (ih (by omega))

/-- **Complementary levels of majority** [O'Donnell, Corollary 5.20][ODonnell2014]: for majority of
`n = 2 m + 1` bits read as signs, the coefficients on sets `S`, `T` with `|S| + |T| = n + 1` agree
up to the sign `(-1) ^ m = (-1) ^ ((n - 1) / 2)`. -/
theorem fourierCoeff_signVal_majority_of_card_add_card (m : ℕ) {S T : Finset (Fin (2 * m + 1))}
    (h : #S + #T = 2 * m + 2) :
    fourierCoeff (fun x => signVal (majority (2 * m + 1) x)) T =
      (-1) ^ m * fourierCoeff (fun x => signVal (majority (2 * m + 1) x)) S := by
  rcases Nat.even_or_odd #S with ⟨a, ha⟩ | ⟨j, hS⟩
  · rw [fourierCoeff_signVal_majority_of_even m ⟨a, ha⟩,
      fourierCoeff_signVal_majority_of_even m ⟨m + 1 - a, by omega⟩, mul_zero]
  obtain ⟨r, rfl⟩ : ∃ r, m = j + r := ⟨m - j, by omega⟩
  have hT : #T = 2 * r + 1 := by omega
  have hpow : ((-1 : ℝ)) ^ r = (-1) ^ (j + r) * (-1) ^ j := by
    rw [pow_add, mul_right_comm, ← pow_add, Even.neg_one_pow ⟨j, rfl⟩, one_mul]
  rw [fourierCoeff_signVal_majority_of_card_eq _ j hS,
    fourierCoeff_signVal_majority_of_card_eq _ r hT, ← Nat.choose_symm_add (a := j) (b := r),
    mul_add, ← Nat.choose_symm_add (a := 2 * j), ← mul_add, hpow]
  ring

/-- **Complementary level weights of majority** [O'Donnell, Corollary 5.20][ODonnell2014]: for
majority of `n = 2 m + 1` bits and `k = 2 j + 1`, `(n - k + 1) W^{n-k+1} = k W^k`. The book's
`W^{n-k+1} = k / (n - k + 1) W^k` is stated multiplied out, and only for odd `k`: for even `k` both
levels are even and both sides vanish by `BitString.levelWeight_signVal_majority_of_even`. -/
theorem card_mul_levelWeight_signVal_majority (m j : ℕ) (hj : j ≤ m) :
    ((2 * (m - j) + 1 : ℕ) : ℝ) *
        levelWeight (2 * (m - j) + 1) (fun x => signVal (majority (2 * m + 1) x)) =
      ((2 * j + 1 : ℕ) : ℝ) *
        levelWeight (2 * j + 1) (fun x => signVal (majority (2 * m + 1) x)) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = j + r := ⟨m - j, by omega⟩
  rw [show j + r - j = r by omega, levelWeight_signVal_majority_of_odd,
    levelWeight_signVal_majority_of_odd, ← Nat.choose_symm_add (a := j) (b := r),
    mul_add, ← Nat.choose_symm_add (a := 2 * j), ← mul_add, ← mul_assoc, ← mul_assoc]
  congr 1
  -- `C(n, n - k + 1) (n - k + 1) = C(n, k - 1) (n - k + 1) = C(n, k) k`
  have := Nat.choose_succ_right_eq (2 * (j + r) + 1) (2 * j)
  rw [show 2 * (j + r) + 1 - 2 * j = 2 * r + 1 by omega,
    show 2 * (j + r) + 1 = 2 * j + (2 * r + 1) by ring, Nat.choose_symm_add] at this
  rw [show 2 * (j + r) + 1 = 2 * j + (2 * r + 1) by ring]
  exact_mod_cast by rw [mul_comm, ← this, mul_comm]

/-- **The level weights of majority decrease** [O'Donnell, Corollary 5.21][ODonnell2014]: for odd
`k = 2 j + 1 ≤ n = 2 m + 1`, the weight of majority on level `k` is strictly smaller on `n + 2` bits
than on `n` bits. Their ratio is `(2 m + 3) (2 m + 1 - 2 j) / ((2 m + 2 - 2 j) (2 m + 2)) < 1`. -/
theorem levelWeight_signVal_majority_succ_lt (m j : ℕ) (hj : j ≤ m) :
    levelWeight (2 * j + 1) (fun x => signVal (majority (2 * (m + 1) + 1) x)) <
      levelWeight (2 * j + 1) (fun x => signVal (majority (2 * m + 1) x)) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = j + r := ⟨m - j, by omega⟩
  rw [levelWeight_signVal_majority_of_odd, levelWeight_signVal_majority_of_odd,
    choose_div_choose_mul_choose_div (by omega), choose_div_choose_mul_choose_div hj,
    show j + r + 1 - j = r + 1 by omega, show j + r - j = r by omega,
    Nat.cast_choose ℝ (by omega : 2 * j + 1 ≤ 2 * (j + r + 1) + 1),
    Nat.cast_choose ℝ (by omega : 2 * j + 1 ≤ 2 * (j + r) + 1),
    show 2 * (j + r + 1) + 1 - (2 * j + 1) = 2 * r + 1 + 1 by omega,
    show 2 * (j + r) + 1 - (2 * j + 1) = 2 * r by omega,
    show 2 * (j + r + 1) + 1 = 2 * (j + r) + 1 + 1 + 1 by omega,
    show 2 * (r + 1) = 2 * r + 1 + 1 by omega]
  simp only [Nat.factorial_succ, pow_succ]
  push_cast
  have hq : (2 * ((j : ℝ) + r) + 3) * (2 * r + 1) / (4 * ((r : ℝ) + 1) * (j + r + 1)) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith [(j.cast_nonneg : (0 : ℝ) ≤ j), (r.cast_nonneg : (0 : ℝ) ≤ r)]
  refine lt_of_eq_of_lt ?_ (mul_lt_of_lt_one_right (by positivity) hq)
  field_simp
  ring

/-- **The noise stability of majority decreases in `n`** [O'Donnell, Theorem 5.18][ODonnell2014]:
for `0 < ρ < 1`, `Stab_ρ[Maj_n]` is strictly smaller on `n + 2 = 2 m + 3` bits than on
`n = 2 m + 1` bits. At the endpoints the two agree: both are `0` at `ρ = 0` (majority is
unbiased) and `1` at `ρ = 1`. The lower bound of Theorem 5.18 by `(2 / π) arcsin ρ` is
`BitString.le_noiseStability_signVal_majority`. The levels up to `n` lose weight, which the new
top level `n + 2` gains, and `ρ ^ k ≥ ρ ^ n > ρ ^ (n + 2)` there. -/
theorem noiseStability_signVal_majority_succ_lt (m : ℕ) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    noiseStability ρ (fun x => signVal (majority (2 * (m + 1) + 1) x)) <
      noiseStability ρ (fun x => signVal (majority (2 * m + 1) x)) := by
  set W : ℕ → ℕ → ℝ := fun n k => levelWeight k fun x : Fin n → Bool => signVal (majority n x)
    with hW
  -- Sums over the levels `k ≤ n` extend to `k < 2 m + 4`, where the weights vanish.
  have hext {n : ℕ} (hn : n < 2 * m + 4) (c : ℕ → ℝ) :
      ∑ k ∈ range (n + 1), c k * W n k = ∑ k ∈ range (2 * m + 4), c k * W n k :=
    sum_subset (range_subset_range.2 (by omega)) fun k _ hk => by
      rw [show W n k = 0 from levelWeight_eq_zero_of_card_lt (by simpa using hk) _, mul_zero]
  have hstab {n : ℕ} (hn : n < 2 * m + 4) :
      noiseStability ρ (fun x => signVal (majority n x)) =
        ∑ k ∈ range (2 * m + 4), ρ ^ k * W n k := by
    rw [noiseStability_eq_sum_levelWeight, Fintype.card_fin]
    exact hext hn _
  have hone {n : ℕ} (hn : n < 2 * m + 4) : ∑ k ∈ range (2 * m + 4), W n k = 1 := by
    simpa using (hext hn fun _ => 1).symm.trans
      (by simpa [Fintype.card_fin] using sum_levelWeight_signVal (majority n))
  rw [hstab (by omega), hstab (by omega), ← sub_pos, ← sum_sub_distrib]
  -- `∑ ρ ^ n (a k - b k) = 0`, and `(ρ ^ k - ρ ^ n) (a k - b k) ≥ 0` on every level, with strict
  -- inequality on the new top level
  have hsum : ∑ k ∈ range (2 * m + 4),
      ρ ^ (2 * m + 1) * (W (2 * m + 1) k - W (2 * (m + 1) + 1) k) = 0 := by
    rw [← mul_sum, sum_sub_distrib, hone (by omega), hone (by omega), sub_self, mul_zero]
  have hpow := pow_lt_pow_right_of_lt_one₀ h0 h1 (by omega : 2 * m + 1 < 2 * (m + 1) + 1)
  rw [← hsum]
  refine sum_lt_sum (fun k _ => ?_) ⟨2 * (m + 1) + 1, by simp; omega, ?_⟩
  · rcases le_or_gt k (2 * m + 1) with hk | hk
    · rw [← mul_sub]
      refine mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one h0.le h1.le hk) (sub_nonneg.2 ?_)
      rcases Nat.even_or_odd k with he | ⟨j, rfl⟩
      · simp only [hW, levelWeight_signVal_majority_of_even _ he, le_refl]
      · exact (levelWeight_signVal_majority_succ_lt m j (by omega)).le
    · rw [show W (2 * m + 1) k = 0 from levelWeight_eq_zero_of_card_lt (by simpa using hk) _]
      nlinarith [pow_le_pow_of_le_one h0.le h1.le hk.le, levelWeight_nonneg k
        fun x : Fin (2 * (m + 1) + 1) → Bool => signVal (majority (2 * (m + 1) + 1) x)]
  · rw [show W (2 * m + 1) (2 * (m + 1) + 1) = 0 from
      levelWeight_eq_zero_of_card_lt (by simp) _]
    have hb : 0 < W (2 * (m + 1) + 1) (2 * (m + 1) + 1) := by
      simp only [hW, levelWeight_signVal_majority_of_odd, Nat.choose_self, Nat.cast_one, div_one,
        one_mul]
      have := Nat.choose_pos (by omega : m + 1 ≤ 2 * (m + 1))
      positivity
    nlinarith

end Cslib.BitString
