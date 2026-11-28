/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Resilience
import CslibFrontier.Foundations.Data.BitString.AgreeExpect
import CslibFrontier.Foundations.Data.Finset.ExpectPi

/-!
# The Tribes function

The *Tribes* function `Tribes_{w,s}` (`Cslib.BitString.tribes`) on `s * w` bits is the `OR` of `s`
`AND`s of `w` bits each, on disjoint *tribes* of bits [O'Donnell, Definition 2.7][ODonnell2014],
introduced by Ben-Or and Linial. It is monotone (`Cslib.BitString.monotone_tribes`) and true with
probability `1 - (1 - 2 ^ (-w)) ^ s` (`Cslib.BitString.expect_bitVal_tribes`)
[O'Donnell, Fact 4.10][ODonnell2014].

O'Donnell takes `s` largest with this probability at most `1 / 2`
[O'Donnell, Definition 4.11][ODonnell2014]. This `s` exists for every `w`
(`Cslib.BitString.tribesSize`) and lies in `[2 ^ (w - 1), 2 ^ w)` for `w ≥ 1`
(`Cslib.BitString.two_pow_sub_one_le_tribesSize`, `Cslib.BitString.tribesSize_lt_two_pow`); these
bounds are ours. For such `s` we show that the probability is within `2 ^ (-w)` of `1 / 2`
(`Cslib.BitString.abs_expect_bitVal_tribes_sub_half_le`); this explicit bound is ours. O'Donnell's
asymptotic statements, that then `2 ^ w = (n / ln n) (1 + o(1))` for `n = s w` with bias
`1 / 2 - O(log n / n)` [O'Donnell, Proposition 4.12][ODonnell2014], are not formalized. The
influences of Tribes [O'Donnell, Proposition 4.13][ODonnell2014] are computed exactly, and bounded
by explicit multiples of `log n / n`, in
`CslibFrontier.Foundations.BooleanAnalysis.TribesInfluence`,
from the independence of the tribes (`Cslib.BitString.expect_prod_tribe`); the asymptotic form
`(ln n / n) (1 ± o(1))` of that proposition is not formalized.

The same independence gives the Fourier coefficients of Tribes, read as signs. A character splits
over the tribes, by the parts `Tⱼ` of `T` in the tribes (`Cslib.BitString.tribePart`), and each
tribe is `1 - AND_w`, where `AND_w` is the indicator of the all-`true` point, with coefficients
`Cslib.BitString.fourierCoeff_ite_eq`. So the coefficient on `T` is `2 ∏ⱼ cⱼ - [T = ∅]`, with
`cⱼ = 1 - 2 ^ (-w)` if `T` misses the `j`-th tribe and `cⱼ = -2 ^ (-w) (-1) ^ |Tⱼ|` otherwise;
this product form is ours. It is
`2 (1 - 2 ^ (-w)) ^ s - 1` on `∅`, and `2 (-1) ^ (k + |T|) 2 ^ (-k w) (1 - 2 ^ (-w)) ^ (s - k)`
on a nonempty `T` meeting `k` tribes (`Cslib.BitString.fourierCoeff_signVal_tribes_empty`,
`Cslib.BitString.fourierCoeff_signVal_tribes_of_ne_empty`)
[O'Donnell, Proposition 4.14][ODonnell2014].

A coalition `Q` leaves Tribes undetermined only if some tribe meets `Q` and is all `true` outside
`Q`. A union bound over these tribes bounds the influence of `Q` by `2 ^ (|Q| - w)`
(`Cslib.BitString.coalitionInfluence_tribes_le`), so Tribes is `(q, 2 ^ (q - w))`-resilient
(`Cslib.BitString.isResilient_tribes`); the bound and its proof are ours. It is useful only for
`q < w`, about `log n`. Bribing one tribe, about `log n` voters, forces Tribes to `True`
[O'Donnell, Section 9.6][ODonnell2014], and the largest coalitional influence toward `True` of at
most `log n` bits is `1 / 2 + Θ(log n / n)` [O'Donnell, Exercise 9.25(g)][ODonnell2014]. In our
terms, one whole tribe of `w` bits has influence `(1 - 2 ^ (-w)) ^ (s - 1)`, about `1 / 2` for the
`s` above. For `s = tribesSize w`, this whole-tribe coalition rules out an
`O(q log n / n)` influence bound at `q = w` as `w` tends to infinity, where `n = s * w`.
This computation and conclusion are ours and are not formalized.

## Main definitions

* `Cslib.BitString.tribes`: the Tribes function `Tribes_{w,s}`.
* `Cslib.BitString.tribesSize`: the number of tribes of width `w` making Tribes nearly balanced.
* `Cslib.BitString.tribePart`: the part of a set of coordinates in one tribe.

## Main results

* `Cslib.BitString.monotone_tribes`: Tribes is monotone.
* `Cslib.BitString.expect_bitVal_tribes`: the probability that Tribes is true.
* `Cslib.BitString.expect_prod_tribe`: the tribes are independent.
* `Cslib.BitString.card_eq_sum_card_tribePart`: `#T` equals the sum of `#(tribePart T j)`.
* `Cslib.BitString.one_div_two_le_pow_tribesSize`,
  `Cslib.BitString.pow_tribesSize_add_one_lt_one_div_two`,
  `Cslib.BitString.two_pow_sub_one_le_tribesSize`, `Cslib.BitString.tribesSize_lt_two_pow`: the
  number of tribes for which Tribes is nearly balanced.
* `Cslib.BitString.abs_expect_bitVal_tribes_sub_half_le`: Tribes is nearly balanced.
* `Cslib.BitString.coalitionInfluence_tribes_le`, `Cslib.BitString.isResilient_tribes`: the
  influence of coalitions on Tribes.
* `Cslib.BitString.fourierCoeff_signVal_tribes_empty`,
  `Cslib.BitString.fourierCoeff_signVal_tribes_of_ne_empty`: the Fourier coefficients of Tribes.

## Usage

Open `Cslib.BitString`. Bit `i` of tribe `j` of `tribes w s` is coordinate
`finProdFinEquiv (j, i)` of `Fin (s * w)`, and Tribes is read as signs through
`fun x => signVal (tribes w s x)`, whose `true` is O'Donnell's True, `-1`. For a set `T` of
coordinates, `tribePart T j` is its part in tribe `j`; compute it with
`Cslib.BitString.mem_tribePart`, since its body is not exposed. On `∅`, rewrite with
`Cslib.BitString.fourierCoeff_signVal_tribes_empty w s`. On a nonempty `T`, rewrite with
`Cslib.BitString.fourierCoeff_signVal_tribes_of_ne_empty`, then supply the number of tribes
`T` meets, `#{j | tribePart T j ≠ ∅}`, and `#T`. The checked clients in
[CslibFrontierTests/TribesFourier.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/TribesFourier.lean)
compute the coefficients of `Tribes_{2,2}` on the empty set (`1 / 8`), on one coordinate
(`3 / 8`) and on a whole tribe (`-3 / 8`), each both from these theorems and by brute force.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Function
open scoped BigOperators

/-! ### The function -/

variable {w s : ℕ}

/-- **Tribes** `Tribes_{w,s}` [O'Donnell, Definition 2.7][ODonnell2014]: on `s * w` bits, the `OR`
of `s` `AND`s of `w` bits each, the `i`-th bit of the `j`-th tribe being bit
`finProdFinEquiv (j, i)`. The value `true` is O'Donnell's `True`, which he writes `-1`. -/
@[expose] def tribes (w s : ℕ) (x : BitString (s * w)) : Bool :=
  decide (∃ j : Fin s, ∀ i : Fin w, x (finProdFinEquiv (j, i)) = true)

/-- Tribes is true exactly when some tribe is all `true`. -/
theorem tribes_eq_true_iff {x : BitString (s * w)} :
    tribes w s x = true ↔ ∃ j : Fin s, ∀ i : Fin w, x (finProdFinEquiv (j, i)) = true :=
  decide_eq_true_iff

/-- **Tribes is monotone.** -/
theorem monotone_tribes (w s : ℕ) : Monotone (tribes w s) := fun x y hxy => by
  cases hx : tribes w s x
  · exact Bool.false_le _
  · obtain ⟨j, hj⟩ := tribes_eq_true_iff.1 hx
    exact (tribes_eq_true_iff.2 ⟨j, fun i =>
      le_antisymm (Bool.le_true _) (hj i ▸ hxy (finProdFinEquiv (j, i)))⟩).ge

/-! ### The probability of `true` -/

/-- Strings of `s * w` bits as `s` blocks of `w` bits. -/
private def blocks (w s : ℕ) : (Fin s → Fin w → Bool) ≃ BitString (s * w) :=
  (Equiv.curry (Fin s) (Fin w) Bool).symm.trans (finProdFinEquiv.arrowCongr (Equiv.refl Bool))

private theorem blocks_apply (y : Fin s → Fin w → Bool) (j : Fin s) (i : Fin w) :
    blocks w s y (finProdFinEquiv (j, i)) = y j i := by
  simp [blocks]

/-- `AND_w`, read as `0` or `1`, is the product of the bits. -/
private theorem prod_bitVal_eq_ite (z : Fin w → Bool) :
    ∏ i, bitVal ℝ (z i) = if ∀ i, z i = true then 1 else 0 := by
  simp [bitVal, Fintype.prod_boole]

/-- Tribes on blocks, as `1 - ∏ⱼ (1 - ∏ᵢ yⱼᵢ)`. -/
private theorem bitVal_tribes_blocks (y : Fin s → Fin w → Bool) :
    bitVal ℝ (tribes w s (blocks w s y)) = 1 - ∏ j, (1 - ∏ i, bitVal ℝ (y j i)) := by
  simp only [tribes, blocks_apply, prod_bitVal_eq_ite]
  by_cases h : ∃ j, ∀ i, y j i = true
  · obtain ⟨j, hj⟩ := h
    rw [decide_eq_true ⟨j, hj⟩, bitVal_true,
      prod_eq_zero (mem_univ j) (by rw [ite_eq_left hj, sub_self]), sub_zero]
  · rw [decide_eq_false h, bitVal_false,
      prod_eq_one fun j _ => by rw [ite_eq_right fun hj => h ⟨j, hj⟩, sub_zero], sub_self]

/-- Over all block strings, `∏ⱼ (1 - ∏ᵢ yⱼᵢ)` sums to `(2 ^ w - 1) ^ s`. -/
private theorem sum_prod_one_sub_prod (w s : ℕ) :
    ∑ y : Fin s → Fin w → Bool, ∏ j, (1 - ∏ i, bitVal ℝ (y j i)) = (2 ^ w - 1) ^ s := by
  have hs := Fintype.prod_sum fun (_ : Fin s) (z : Fin w → Bool) => 1 - ∏ i, bitVal ℝ (z i)
  have hw := Fintype.prod_sum fun (_ : Fin w) (b : Bool) => bitVal ℝ b
  beta_reduce at hs hw
  rw [← hs, sum_sub_distrib, ← hw]
  simp only [Fintype.sum_bool, bitVal_true, bitVal_false, add_zero, prod_const_one, sum_const,
    card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Nat.cast_pow, Nat.cast_ofNat, prod_const]

/-- **The probability that Tribes is true** [O'Donnell, Fact 4.10][ODonnell2014]:
`Pr[Tribes_{w,s} = True] = 1 - (1 - 2 ^ (-w)) ^ s`. -/
theorem expect_bitVal_tribes (w s : ℕ) :
    𝔼 x, bitVal ℝ (tribes w s x) = 1 - (1 - 2⁻¹ ^ w) ^ s := by
  rw [Fintype.expect_equiv (blocks w s).symm _ (fun y => bitVal ℝ (tribes w s (blocks w s y)))
    fun x => by rw [Equiv.apply_symm_apply]]
  simp only [bitVal_tribes_blocks]
  rw [expect_sub_distrib, Fintype.expect_const, expect_eq_sum_div_card, sum_prod_one_sub_prod,
    card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, ← div_pow, sub_div,
    div_self (by positivity), inv_pow, one_div]

/-- **The tribes are independent**: the average of a product of functions of the separate tribes
is the product of their averages. -/
theorem expect_prod_tribe (g : Fin s → (Fin w → Bool) → ℝ) :
    𝔼 x : BitString (s * w), ∏ j, g j (fun i => x (finProdFinEquiv (j, i))) =
      ∏ j, 𝔼 z, g j z := by
  rw [Fintype.prod_expect]
  exact Fintype.expect_equiv (blocks w s).symm _ _ fun x => rfl

/-! ### The number of tribes -/

/-- By `1 - x ≤ exp (-x)`, `(1 - 2 ^ (-w)) ^ (2 ^ w) ≤ exp (-1) < 1 / 2`. -/
private theorem pow_two_pow_lt_one_div_two (w : ℕ) : (1 - (2⁻¹ : ℝ) ^ w) ^ 2 ^ w < 1 / 2 := by
  have h0 : 0 ≤ 1 - (2⁻¹ : ℝ) ^ w := sub_nonneg.2 (pow_le_one₀ (by norm_num) (by norm_num))
  calc (1 - (2⁻¹ : ℝ) ^ w) ^ 2 ^ w
      ≤ Real.exp (-(2⁻¹ : ℝ) ^ w) ^ 2 ^ w := by
        gcongr
        exact Real.one_sub_le_exp_neg _
    _ = Real.exp (-1) := by
        rw [← Real.exp_natCast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_neg, ← mul_pow,
          mul_inv_cancel₀ two_ne_zero, one_pow]
    _ < 1 / 2 := by
        rw [Real.exp_neg, one_div]
        exact inv_strictAnti₀ two_pos
          (by linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)])

/-- By Bernoulli's inequality, `(1 - 2 ^ (-w)) ^ (2 ^ (w - 1)) ≥ 1 / 2` for `w ≥ 1`. -/
private theorem one_div_two_le_pow_two_pow_sub_one {w : ℕ} (hw : 1 ≤ w) :
    1 / 2 ≤ (1 - (2⁻¹ : ℝ) ^ w) ^ 2 ^ (w - 1) := by
  have h := one_add_mul_le_pow (a := -(2⁻¹ : ℝ) ^ w)
    (by linarith [pow_le_one₀ (n := w) (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)]) (2 ^ (w - 1))
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hw
  rw [Nat.add_sub_cancel, ← sub_eq_add_neg] at h
  refine le_trans (le_of_eq ?_) h
  rw [Nat.cast_pow, Nat.cast_ofNat, mul_neg, pow_succ, ← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ two_ne_zero, one_pow, one_mul]
  norm_num

/-- The **number of tribes** of width `w` in O'Donnell's `Tribes_n`
[O'Donnell, Definition 4.11][ODonnell2014]: the largest `s` with `(1 - 2 ^ (-w)) ^ s ≥ 1 / 2`, that
is, with `Tribes_{w,s}` true with probability at most `1 / 2` (`expect_bitVal_tribes`). It is the
least `s` with `(1 - 2 ^ (-w)) ^ (s + 1) < 1 / 2`, which exists since the base is less than `1`.
O'Donnell defines it for `w ≥ 1`; for `w = 0` it is `0`. -/
noncomputable def tribesSize (w : ℕ) : ℕ :=
  Nat.find (p := fun s => (1 - (2⁻¹ : ℝ) ^ w) ^ (s + 1) < 1 / 2)
    ⟨2 ^ w - 1, by rw [Nat.sub_add_cancel Nat.one_le_two_pow]; exact pow_two_pow_lt_one_div_two w⟩

/-- `Tribes_{w, tribesSize w}` is true with probability at most `1 / 2`
(`1 - (1 - 2 ^ (-w)) ^ s ≤ 1 / 2`). -/
theorem one_div_two_le_pow_tribesSize (w : ℕ) :
    1 / 2 ≤ (1 - (2⁻¹ : ℝ) ^ w) ^ tribesSize w := by
  rcases Nat.eq_zero_or_pos (tribesSize w) with h | h
  · norm_num [h]
  · rw [← Nat.sub_add_cancel h]
    exact not_lt.1 (Nat.find_min _ (Nat.sub_lt h one_pos))

/-- `tribesSize w` is largest: one more tribe makes Tribes true with probability more than
`1 / 2`. -/
theorem pow_tribesSize_add_one_lt_one_div_two (w : ℕ) :
    (1 - (2⁻¹ : ℝ) ^ w) ^ (tribesSize w + 1) < 1 / 2 :=
  Nat.find_spec (p := fun s => (1 - (2⁻¹ : ℝ) ^ w) ^ (s + 1) < 1 / 2) _

/-- `tribesSize w < 2 ^ w`, our bound. -/
theorem tribesSize_lt_two_pow (w : ℕ) : tribesSize w < 2 ^ w := by
  refine (Nat.find_min' _ ?_).trans_lt (Nat.sub_lt Nat.one_le_two_pow one_pos)
  simpa [Nat.sub_add_cancel Nat.one_le_two_pow] using pow_two_pow_lt_one_div_two w

/-- `2 ^ (w - 1) ≤ tribesSize w` for `w ≥ 1`, our bound. -/
theorem two_pow_sub_one_le_tribesSize {w : ℕ} (hw : 1 ≤ w) : 2 ^ (w - 1) ≤ tribesSize w := by
  by_contra h
  have h0 : 0 ≤ 1 - (2⁻¹ : ℝ) ^ w := sub_nonneg.2 (pow_le_one₀ (by norm_num) (by norm_num))
  have h1 : 1 - (2⁻¹ : ℝ) ^ w ≤ 1 := sub_le_self _ (by positivity)
  exact (pow_tribesSize_add_one_lt_one_div_two w).not_ge
    ((one_div_two_le_pow_two_pow_sub_one hw).trans (pow_le_pow_of_le_one h0 h1 (by omega)))

/-- **Tribes is nearly balanced**, our explicit form of
[O'Donnell, Proposition 4.12, last statement][ODonnell2014]: if `s` is largest with
`(1 - 2 ^ (-w)) ^ s ≥ 1 / 2`, that is, `Tribes_{w,s}` is true with probability at most `1 / 2`
[O'Donnell, Definition 4.11][ODonnell2014], then the probability is within `2 ^ (-w)` of `1 / 2`.
The bound is ours; O'Donnell states `1 / 2 - O(log n / n)` for `n = s w`. -/
theorem abs_expect_bitVal_tribes_sub_half_le
    (h₁ : 1 / 2 ≤ (1 - (2⁻¹ : ℝ) ^ w) ^ s) (h₂ : (1 - (2⁻¹ : ℝ) ^ w) ^ (s + 1) < 1 / 2) :
    |𝔼 x, bitVal ℝ (tribes w s x) - 1 / 2| ≤ 2⁻¹ ^ w := by
  rw [expect_bitVal_tribes, abs_le]
  have hb : 0 ≤ (2⁻¹ : ℝ) ^ w := by positivity
  have hb1 : (2⁻¹ : ℝ) ^ w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ha : (1 - (2⁻¹ : ℝ) ^ w) ^ s ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  rw [pow_succ] at h₂
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right ha hb]

/-! ### Coalitions -/

/-- The `j`-th tribe. -/
private def tribe (w : ℕ) (j : Fin s) : Finset (Fin (s * w)) :=
  univ.map ⟨fun i => finProdFinEquiv (j, i), fun _ _ h => by simpa using h⟩

private theorem mem_tribe {j : Fin s} {k : Fin (s * w)} :
    k ∈ tribe w j ↔ (finProdFinEquiv.symm k).1 = j := by
  rw [tribe, mem_map]
  refine ⟨?_, ?_⟩
  · rintro ⟨i, -, rfl⟩
    exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)
  · rintro rfl
    exact ⟨_, mem_univ _, finProdFinEquiv.apply_symm_apply k⟩

private theorem card_tribe (j : Fin s) : #(tribe w j) = w := by
  rw [tribe, card_map, card_univ, Fintype.card_fin]

/-- Tribes is true exactly when some tribe is all `true`, with tribes as sets. -/
private theorem tribes_eq_true_iff_tribe {x : BitString (s * w)} :
    tribes w s x = true ↔ ∃ j : Fin s, ∀ k ∈ tribe w j, x k = true := by
  rw [tribes_eq_true_iff]
  refine exists_congr fun j => ⟨fun h k hk => ?_, fun h i => h _ (mem_map_of_mem _ (mem_univ i))⟩
  obtain ⟨i, -, rfl⟩ := mem_map.1 hk
  exact h i

/-- The tribes partition the bits, so their intersections with `Q` have total size `|Q|`. -/
private theorem sum_card_tribe_inter (Q : Finset (Fin (s * w))) :
    ∑ j, #(tribe w j ∩ Q) = #Q := by
  rw [card_eq_sum_card_fiberwise (f := fun k => (finProdFinEquiv.symm k).1) (t := univ)
    fun _ _ => mem_coe.2 (mem_univ _)]
  refine sum_congr rfl fun j _ => congrArg card (Finset.ext fun k => ?_)
  rw [mem_inter, mem_filter, mem_tribe, and_comm]

/-- If Tribes is undetermined at `x` by the bits outside `Q`, some tribe meets `Q` and is all
`true` outside `Q`. -/
private theorem exists_tribe_of_isUndetermined {Q : Finset (Fin (s * w))} {x : BitString (s * w)}
    (h : IsUndetermined Q (tribes w s) x) :
    ∃ j, (tribe w j ∩ Q).Nonempty ∧ ∀ k ∈ tribe w j \ Q, x k = true := by
  rw [isUndetermined_iff_of_monotone (monotone_tribes w s), tribes_eq_true_iff_tribe,
    ← Bool.not_eq_true, tribes_eq_true_iff_tribe] at h
  obtain ⟨⟨j, hj⟩, h0⟩ := h
  have hx : ∀ k ∈ tribe w j \ Q, x k = true := fun k hk =>
    piecewise_eq_of_notMem Q (fun _ => true) x (mem_sdiff.1 hk).2 ▸ hj k (mem_sdiff.1 hk).1
  refine ⟨j, ?_, hx⟩
  by_contra hne
  refine h0 ⟨j, fun k hk => ?_⟩
  have hkQ : k ∉ Q := fun hkQ => hne ⟨k, mem_inter.2 ⟨hk, hkQ⟩⟩
  exact (piecewise_eq_of_notMem _ _ _ hkQ).trans (hx k (mem_sdiff.2 ⟨hk, hkQ⟩))

/-- For numbers `a j ≥ 1`, `∑ 2 ^ a j ≤ 2 ^ ∑ a j`. -/
private theorem sum_two_pow_le_two_pow_sum {α : Type*} (J : Finset α) (a : α → ℕ)
    (ha : ∀ j ∈ J, 1 ≤ a j) : ∑ j ∈ J, 2 ^ a j ≤ 2 ^ ∑ j ∈ J, a j := by
  classical
  induction J using Finset.induction with
  | empty => simp
  | insert j J hj ih =>
    rw [sum_insert hj, sum_insert hj, pow_add]
    have ih := ih fun i hi => ha i (mem_insert_of_mem hi)
    have h1 : 2 ^ 1 ≤ 2 ^ a j := Nat.pow_le_pow_right two_pos (ha j (mem_insert_self j J))
    rcases J.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
    · simp
    · have h2 : 2 ^ 1 ≤ 2 ^ ∑ i ∈ J, a i := Nat.pow_le_pow_right two_pos
        ((ha i (mem_insert_of_mem hi)).trans (single_le_sum (fun _ _ => Nat.zero_le _) hi))
      rw [pow_one] at h1 h2
      nlinarith

/-- **The influence of a coalition on Tribes**, our union bound: a coalition `Q` has influence at
most `2 ^ (|Q| - w)` on `Tribes_{w,s}`. -/
theorem coalitionInfluence_tribes_le (Q : Finset (Fin (s * w))) :
    coalitionInfluence (Probability.PMF.uniformOfFintype _) Q (tribes w s) ≤ 2 ^ #Q / 2 ^ w := by
  set J := ({j | (tribe w j ∩ Q).Nonempty} : Finset (Fin s))
  have key (m a : ℕ) (h : m + a = w) : (2⁻¹ : ℝ) ^ m = 2 ^ a / 2 ^ w := by
    rw [← h, pow_add, inv_pow, mul_comm, ← div_div, div_self (by positivity), one_div]
  rw [coalitionInfluence_uniformOfFintype]
  calc 𝔼 x, (if IsUndetermined Q (tribes w s) x then (1 : ℝ) else 0)
      ≤ 𝔼 x : BitString (s * w), ∑ j ∈ J, if ∀ k ∈ tribe w j \ Q, x k = true then (1 : ℝ) else 0 :=
        expect_le_expect fun x _ => by
          by_cases h : IsUndetermined Q (tribes w s) x
          · obtain ⟨j, hj, hx⟩ := exists_tribe_of_isUndetermined h
            rw [ite_eq_left h]
            refine (single_le_sum (f := fun j => if ∀ k ∈ tribe w j \ Q, x k = true then (1 : ℝ)
              else 0) (fun j _ => by split_ifs <;> norm_num) (mem_filter.2 ⟨mem_univ j, hj⟩)).trans'
              ?_
            rw [ite_eq_left hx]
          · rw [ite_eq_right h]
            exact sum_nonneg fun j _ => by split_ifs <;> norm_num
    _ = ∑ j ∈ J, 𝔼 x : BitString (s * w),
          if ∀ k ∈ tribe w j \ Q, x k = true then (1 : ℝ) else 0 := expect_sum_comm _ _ _
    _ = ∑ j ∈ J, (2 : ℝ) ^ #(tribe w j ∩ Q) / 2 ^ w := sum_congr rfl fun j _ => by
        exact (expect_ite_forall_mem_eq (tribe w j \ Q) fun _ => true).trans
          (key _ _ ((card_sdiff_add_card_inter _ _).trans (card_tribe j)))
    _ ≤ 2 ^ #Q / 2 ^ w := by
        rw [← sum_div]
        gcongr
        have hN : ∑ j ∈ J, 2 ^ #(tribe w j ∩ Q) ≤ 2 ^ #Q :=
          (sum_two_pow_le_two_pow_sum J _ fun j hj => (mem_filter.1 hj).2.card_pos).trans
            (Nat.pow_le_pow_right two_pos ((sum_le_sum_of_subset (subset_univ J)).trans_eq
              (sum_card_tribe_inter Q)))
        exact_mod_cast hN

/-- **Tribes is resilient against small coalitions**, our bound: `Tribes_{w,s}` is
`(q, 2 ^ (q - w))`-resilient [Chattopadhyay–Zuckerman, Definition 1.7][ChattopadhyayZuckerman2019].
This is useful only for `q < w`. For `s = tribesSize w`, a whole-tribe coalition rules out an
`O(q log n / n)` influence bound at `q = w` as `w` tends to infinity, where `n = s * w`.
This asymptotic conclusion is not formalized here
(compare [O'Donnell, Section 9.6][ODonnell2014]). -/
theorem isResilient_tribes (w s q : ℕ) : IsResilient q (2 ^ q / 2 ^ w) (tribes w s) :=
  fun Q hQ => hQ ▸ coalitionInfluence_tribes_le Q

/-! ### Fourier coefficients -/

/-- The part of a set `T` of coordinates of `Tribes_{w,s}` lying in the `j`-th tribe, as the
positions `i` with `finProdFinEquiv (j, i) ∈ T`. -/
def tribePart (T : Finset (Fin (s * w))) (j : Fin s) : Finset (Fin w) :=
  {i | finProdFinEquiv (j, i) ∈ T}

/-- A position is in the part of `T` in a tribe when its coordinate is in `T`. -/
@[simp] theorem mem_tribePart {T : Finset (Fin (s * w))} {j : Fin s} {i : Fin w} :
    i ∈ tribePart T j ↔ finProdFinEquiv (j, i) ∈ T := by
  simp [tribePart]

private theorem card_tribePart (T : Finset (Fin (s * w))) (j : Fin s) :
    #(tribePart T j) = #(tribe w j ∩ T) := by
  rw [tribe, ← filter_mem_eq_inter, filter_map, card_map]
  rfl

/-- The size of a set of coordinates is the sum of the sizes of its parts in the tribes. -/
theorem card_eq_sum_card_tribePart (T : Finset (Fin (s * w))) :
    #T = ∑ j, #(tribePart T j) := by
  simp only [card_tribePart, sum_card_tribe_inter]

/-- A character splits over the tribes. -/
private theorem chi_blocks (T : Finset (Fin (s * w))) (y : Fin s → Fin w → Bool) :
    chi ℝ T (blocks w s y) = ∏ j, chi ℝ (tribePart T j) (y j) := by
  rw [chi_eq_prod_univ, ← Fintype.prod_equiv finProdFinEquiv _ _ fun _ => rfl,
    Fintype.prod_prod_type]
  refine prod_congr rfl fun j _ => ?_
  rw [chi_eq_prod_univ]
  simp [blocks_apply]

/-- The Fourier coefficients of one tribe, `1 - AND_w`, read as `0` or `1`. `AND_w` is the
indicator of the all-`true` point. -/
private theorem expect_one_sub_prod_mul_chi (U : Finset (Fin w)) :
    𝔼 z : Fin w → Bool, (1 - ∏ i, bitVal ℝ (z i)) * chi ℝ U z =
      (if U = ∅ then 1 else 0) - 2⁻¹ ^ w * (-1) ^ #U := by
  have h := fourierCoeff_ite_eq (fun _ => true) U
  simp only [fourierCoeff, funext_iff, Fintype.card_fin] at h
  have hchi : chi ℝ U (fun _ => true) = (-1) ^ #U := by
    rw [chi_eq_prod_signVal, prod_const, signVal_true]
  simp only [prod_bitVal_eq_ite, sub_mul, one_mul, expect_sub_distrib, expect_chi, h, hchi,
    div_eq_mul_inv, inv_pow]
  ring

/-- **The Fourier coefficients of Tribes**, in product form: `Tribes_{w,s}`, read as signs, has
coefficient `2 ∏ⱼ cⱼ - [T = ∅]` on `T`, where `cⱼ = 1 - 2 ^ (-w)` if `T` misses the `j`-th tribe and
`cⱼ = -2 ^ (-w) (-1) ^ |Tⱼ|` otherwise. This product form is ours; the two-case formula of
[O'Donnell, Proposition 4.14][ODonnell2014], whose proof the book leaves as its Exercise 4.6,
follows from it. -/
private theorem fourierCoeff_signVal_tribes (T : Finset (Fin (s * w))) :
    fourierCoeff (fun x => signVal (tribes w s x)) T =
      2 * ∏ j, ((if tribePart T j = ∅ then 1 else 0) - 2⁻¹ ^ w * (-1) ^ #(tribePart T j)) -
        if T = ∅ then 1 else 0 := by
  have hpt (x : BitString (s * w)) : signVal (tribes w s x) * chi ℝ T x =
      2 * ∏ j, (1 - ∏ i, bitVal ℝ (x (finProdFinEquiv (j, i)))) *
          chi ℝ (tribePart T j) (fun i => x (finProdFinEquiv (j, i))) -
        ∏ j, chi ℝ (tribePart T j) (fun i => x (finProdFinEquiv (j, i))) := by
    obtain ⟨y, rfl⟩ := (blocks w s).surjective x
    simp only [blocks_apply]
    rw [signVal_eq_one_sub_two_mul_bitVal, bitVal_tribes_blocks, chi_blocks, prod_mul_distrib]
    ring
  rw [fourierCoeff, expect_congr rfl fun x _ => hpt x, expect_sub_distrib, ← mul_expect,
    expect_prod_tribe fun j z => (1 - ∏ i, bitVal ℝ (z i)) * chi ℝ (tribePart T j) z,
    expect_prod_tribe fun j z => chi ℝ (tribePart T j) z]
  simp_rw [expect_one_sub_prod_mul_chi, expect_chi]
  congr 1
  rw [prod_boole]
  simp_rw [← card_eq_zero, card_eq_sum_card_tribePart T, sum_eq_zero_iff]

/-- **The Fourier coefficient of Tribes on `∅`** [O'Donnell, Proposition 4.14][ODonnell2014]:
`2 (1 - 2 ^ (-w)) ^ s - 1`. -/
theorem fourierCoeff_signVal_tribes_empty (w s : ℕ) :
    fourierCoeff (fun x => signVal (tribes w s x)) ∅ = 2 * (1 - 2⁻¹ ^ w) ^ s - 1 := by
  rw [fourierCoeff_signVal_tribes]
  simp [tribePart]

/-- **The Fourier coefficients of Tribes on nonempty sets**
[O'Donnell, Proposition 4.14][ODonnell2014]: for `T ≠ ∅` meeting `k` tribes, `Tribes_{w,s}`,
read as signs, has coefficient `2 (-1) ^ (k + |T|) 2 ^ (-k w) (1 - 2 ^ (-w)) ^ (s - k)` on `T`. -/
theorem fourierCoeff_signVal_tribes_of_ne_empty {T : Finset (Fin (s * w))} (hT : T ≠ ∅) :
    fourierCoeff (fun x => signVal (tribes w s x)) T =
      2 * (-1) ^ (#{j | tribePart T j ≠ ∅} + #T) * 2⁻¹ ^ (#{j | tribePart T j ≠ ∅} * w) *
        (1 - 2⁻¹ ^ w) ^ (s - #{j | tribePart T j ≠ ∅}) := by
  set k := #{j | tribePart T j ≠ ∅}
  rw [fourierCoeff_signVal_tribes, ite_eq_right hT, sub_zero]
  set b : ℝ := 2⁻¹ ^ w with hb
  have hfac (j : Fin s) : ((if tribePart T j = ∅ then 1 else 0) - b * (-1) ^ #(tribePart T j)) =
      if tribePart T j = ∅ then 1 - b else -b * (-1) ^ #(tribePart T j) := by
    split_ifs with h
    · simp [h]
    · ring
  simp_rw [hfac]
  rw [prod_ite, prod_const, prod_mul_distrib, prod_const, prod_pow_eq_pow_sum]
  have hk' : #({j | ¬tribePart T j = ∅} : Finset (Fin s)) = k := rfl
  have hk : #({j | tribePart T j = ∅} : Finset (Fin s)) = s - k := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin s)))
      (fun j => tribePart T j = ∅)
    rw [card_univ, Fintype.card_fin, hk'] at this; omega
  have hsum : ∑ j ∈ ({j | ¬tribePart T j = ∅} : Finset (Fin s)), #(tribePart T j) = #T := by
    rw [sum_filter_of_ne fun _ _ h => by rwa [Ne, card_eq_zero] at h, ← card_eq_sum_card_tribePart]
  rw [hk, hsum, hk', neg_pow, pow_add, mul_comm k w, pow_mul, hb]; ring

end Cslib.BitString
