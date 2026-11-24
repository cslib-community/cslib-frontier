/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Carry chains and products of short numbers

The elementary Chinese remainder step computes the bits of a large number `N` without ever writing
`N` down. `N` is given as a sum of *columns*, `N = ∑_{i<J} c i · 2^i`, where each column `c i` is a
small number computable on its own. A bit of `N` is then a carry chain:

* `chain c j` is the carry into position `j`, `chain c (j+1) = (c j + chain c j) / 2`;
* `bitOf c j = (c j + chain c j) % 2` is bit `j` of `N` (`div_two_pow_mod_two_eq_bitOf`).

The columns of a product of `g` numbers below `2^W` count the tuples of bit positions
`(i_0, …, i_{g-1}) ∈ [W]^g` with `∑ i_m = i` at which all factors have a `1` bit; such a tuple is
packed into one number `u < W^g` with digits `dig W u m = u / W^m % W`
(`prod_eq_sum_pbits`, `sum_mul_two_pow_regroup`).

## Main results

* `Cslib.Complexity.NtimeDspace.Cross.Exact.div_two_pow_mod_two_eq_bitOf`: the carry chain computes
the bits.
* `Cslib.Complexity.NtimeDspace.Cross.Exact.prod_eq_sum_pbits`: the expansion of a product over
packed tuples.
* `Cslib.Complexity.NtimeDspace.Cross.Exact.sum_mul_two_pow_regroup`: regrouping a sum of powers of
two by exponent.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.Exact

open Finset

/-! ### Binary expansions -/

/-- `Bool.toNat` of a bit, as a division. -/
theorem toNat_testBit (x i : ℕ) : (x.testBit i).toNat = x / 2 ^ i % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]

/-- The low `W` bits of `f`. -/
theorem sum_bits_eq_mod (f : ℕ) : ∀ W : ℕ, ∑ i ∈ range W, f / 2 ^ i % 2 * 2 ^ i = f % 2 ^ W
  | 0 => by simp [Nat.mod_one]
  | W + 1 => by
    rw [sum_range_succ, sum_bits_eq_mod f W, Nat.mod_pow_succ, Nat.mul_comm (f / 2 ^ W % 2)]

/-- **Binary expansion** of a number below `2^W`. -/
theorem sum_bits_eq {f W : ℕ} (h : f < 2 ^ W) : ∑ i ∈ range W, f / 2 ^ i % 2 * 2 ^ i = f := by
  rw [sum_bits_eq_mod, Nat.mod_eq_of_lt h]

/-- A bit, as a division, is at most `1`. -/
theorem div_mod_two_le_one (x : ℕ) : x % 2 ≤ 1 := by omega

/-! ### Carry chains -/

/-- The carry into position `j` of `∑ c i · 2^i`. -/
def chain (c : ℕ → ℕ) (j : ℕ) : ℕ :=
  (List.range j).foldl (fun acc i => (c i + acc) / 2) 0

/-- Bit `j` of `∑ c i · 2^i`, by the carry chain. -/
def bitOf (c : ℕ → ℕ) (j : ℕ) : ℕ := (c j + chain c j) % 2

theorem chain_zero (c : ℕ → ℕ) : chain c 0 = 0 := rfl

theorem chain_succ (c : ℕ → ℕ) (j : ℕ) : chain c (j + 1) = (c j + chain c j) / 2 := by
  simp [chain, List.range_succ, List.foldl_append]

theorem bitOf_le_one (c : ℕ → ℕ) (j : ℕ) : bitOf c j ≤ 1 := by unfold bitOf; omega

/-- The carry stays below the largest column. -/
theorem chain_le {c : ℕ → ℕ} {C : ℕ} (hc : ∀ i, c i ≤ C) : ∀ j, chain c j ≤ C
  | 0 => Nat.zero_le _
  | j + 1 => by
    rw [chain_succ]
    have := chain_le hc j
    have := hc j
    omega

/-- The carry stays below the largest column of the positions before it. -/
theorem chain_le_of_lt {c : ℕ → ℕ} {C J : ℕ} (hc : ∀ i < J, c i ≤ C) :
    ∀ j ≤ J, chain c j ≤ C
  | 0, _ => Nat.zero_le _
  | j + 1, hj => by
    rw [chain_succ]
    have := chain_le_of_lt hc j (by omega)
    have := hc j (by omega)
    omega

/-- The low bits produced by the chain are below `2^j`. -/
theorem sum_bitOf_lt (c : ℕ → ℕ) : ∀ j, ∑ i ∈ range j, bitOf c i * 2 ^ i < 2 ^ j
  | 0 => by simp
  | j + 1 => by
    rw [sum_range_succ, pow_succ]
    have := sum_bitOf_lt c j
    have := bitOf_le_one c j
    have : bitOf c j * 2 ^ j ≤ 2 ^ j := by
      calc bitOf c j * 2 ^ j ≤ 1 * 2 ^ j := Nat.mul_le_mul_right _ this
        _ = 2 ^ j := one_mul _
    omega

/-- **The carry-chain invariant**: the first `j` columns are the first `j` bits plus the carry. -/
theorem sum_cols_eq (c : ℕ → ℕ) : ∀ j,
    ∑ i ∈ range j, c i * 2 ^ i = ∑ i ∈ range j, bitOf c i * 2 ^ i + chain c j * 2 ^ j
  | 0 => by simp [chain_zero]
  | j + 1 => by
    rw [sum_range_succ, sum_range_succ, sum_cols_eq c j, chain_succ, pow_succ]
    have h := Nat.mod_add_div (c j + chain c j) 2
    rw [show bitOf c j = (c j + chain c j) % 2 from rfl]
    set s := c j + chain c j
    calc ∑ i ∈ range j, bitOf c i * 2 ^ i + chain c j * 2 ^ j + c j * 2 ^ j
        = ∑ i ∈ range j, bitOf c i * 2 ^ i + s * 2 ^
            j := by rw [show s = c j + chain c j from rfl]; ring
      _ = ∑ i ∈ range j, bitOf c i * 2 ^ i + (s % 2 + 2 * (s / 2)) * 2 ^ j := by rw [h]
      _ = _ := by ring

/-- **The carry chain computes the bits.** If `N = ∑_{i<J} c i · 2^i`, then bit `j < J` of `N` is
`bitOf c j`. -/
theorem div_two_pow_mod_two_eq_bitOf {c : ℕ → ℕ} {J N : ℕ}
    (hN : N = ∑ i ∈ range J, c i * 2 ^ i) {j : ℕ} (hj : j < J) : N / 2 ^ j % 2 = bitOf c j := by
  obtain ⟨d, rfl⟩ : ∃ d, J = j + (d + 1) := ⟨J - j - 1, by omega⟩
  rw [sum_range_add, sum_cols_eq c j, sum_range_succ'] at hN
  set T := ∑ i ∈ range d, c (j + (i + 1)) * 2 ^ (j + (i + 1))
  have hT : T = 2 ^ j * (2 * ∑ i ∈ range d, c (j + (i + 1)) * 2 ^ i) := by
    simp only [T, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [pow_add, pow_succ]
    ring
  have hlow := sum_bitOf_lt c j
  set low := ∑ i ∈ range j, bitOf c i * 2 ^ i
  set R := ∑ i ∈ range d, c (j + (i + 1)) * 2 ^ i
  have hN' : N = low + 2 ^ j * (chain c j + c j + 2 * R) := by
    simp only [add_zero] at hN
    rw [hN, hT]; ring
  have hdiv : N / 2 ^ j = chain c j + c j + 2 * R := by
    rw [hN', Nat.add_mul_div_left _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt hlow, zero_add]
  rw [hdiv]
  unfold bitOf
  omega

/-! ### Packed tuples of bit positions -/

/-- Digit `m` of `u` in base `W`. -/
def dig (W u m : ℕ) : ℕ := u / W ^ m % W

/-- The sum of the first `g` digits of `u` in base `W`. -/
def sdig (W g u : ℕ) : ℕ := ∑ m ∈ range g, dig W u m

/-- The product of the bits of the factors `f m` at the positions given by the digits of `u`. -/
def pbits (W g : ℕ) (f : ℕ → ℕ) (u : ℕ) : ℕ := ∏ m ∈ range g, f m / 2 ^ dig W u m % 2

/-- A sum over `u < A · B` as a double sum over `u = u' + A · a`. -/
theorem sum_range_mul_split (F : ℕ → ℕ) (A : ℕ) : ∀ B,
    ∑ u ∈ range (A * B), F u = ∑ a ∈ range B, ∑ u ∈ range A, F (u + A * a)
  | 0 => by simp
  | B + 1 => by
    rw [Nat.mul_succ, sum_range_add, sum_range_mul_split F A B, sum_range_succ]
    congr 1
    refine sum_congr rfl fun u _ => ?_
    rw [Nat.add_comm]

theorem dig_add_of_lt {W u a m g : ℕ} (hW : 1 ≤ W) (hm : m < g) :
    dig W (u + W ^ g * a) m = dig W u m := by
  unfold dig
  obtain ⟨e, rfl⟩ : ∃ e, g = m + (e + 1) := ⟨g - m - 1, by omega⟩
  have hpos : 0 < W ^ m := Nat.pow_pos (by omega : 0 < W)
  rw [show W ^ (m + (e + 1)) * a = W ^ m * (W * (W ^ e * a)) by rw [pow_add, pow_succ]; ring,
    Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]

theorem dig_add_self {W u a g : ℕ} (hu : u < W ^ g) (ha : a < W) :
    dig W (u + W ^ g * a) g = a := by
  unfold dig
  rw [Nat.add_mul_div_left _ _ (Nat.pow_pos (by omega : 0 < W)),
    Nat.div_eq_of_lt hu, zero_add, Nat.mod_eq_of_lt ha]

/-- **Expansion of a product over packed tuples.** For factors below `2^W`,
`∏_{m<g} f m = ∑_{u < W^g} pbits W g f u · 2^(sdig W g u)`. -/
theorem prod_eq_sum_pbits {W : ℕ} (hW : 1 ≤ W) : ∀ (g : ℕ) (f : ℕ → ℕ),
    (∀ m < g, f m < 2 ^ W) →
      ∏ m ∈ range g, f m = ∑ u ∈ range (W ^ g), pbits W g f u * 2 ^ sdig W g u
  | 0, f, _ => by simp [pbits, sdig]
  | g + 1, f, hf => by
    rw [prod_range_succ, prod_eq_sum_pbits hW g f (fun m hm => hf m (by omega)),
      ← sum_bits_eq (hf g (by omega)), sum_mul_sum, pow_succ, sum_range_mul_split, sum_comm]
    refine sum_congr rfl fun a ha => sum_congr rfl fun u hu => ?_
    rw [mem_range] at ha hu
    have hd : ∀ m ∈ range g, dig W (u + W ^ g * a) m = dig W u m :=
      fun m hm => dig_add_of_lt hW (mem_range.mp hm)
    have hp : pbits W (g + 1) f (u + W ^ g * a) = pbits W g f u * (f g / 2 ^ a % 2) := by
      unfold pbits
      rw [prod_range_succ, dig_add_self hu ha]
      congr 1
      exact prod_congr rfl fun m hm => by rw [hd m hm]
    have hs : sdig W (g + 1) (u + W ^ g * a) = sdig W g u + a := by
      unfold sdig
      rw [sum_range_succ, dig_add_self hu ha]
      congr 1
      exact sum_congr rfl hd
    rw [hp, hs, pow_add]
    ring

/-- The digit sum of `u` is below `g · W`, for `g ≥ 1` and `W ≥ 1`. -/
theorem sdig_lt {W g : ℕ} (hW : 1 ≤ W) (hg : 1 ≤ g) (u : ℕ) : sdig W g u < g * W := by
  unfold sdig
  have h : ∀ m ∈ range g, dig W u m ≤ W - 1 := fun m _ => by
    unfold dig; have := Nat.mod_lt (u / W ^ m) (show 0 < W by omega); omega
  have := sum_le_sum h
  rw [sum_const_nat (fun _ _ => rfl), card_range] at this
  have : g * (W - 1) < g * W := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  omega

/-- `pbits` is a product of bits, so at most `1`. -/
theorem pbits_le_one (W g : ℕ) (f : ℕ → ℕ) (u : ℕ) : pbits W g f u ≤ 1 := by
  unfold pbits
  exact prod_le_one fun m _ => by omega

/-- **Regrouping by exponent.** If every exponent `s u` is below `I`, then
`∑_u T u · 2^(s u) = ∑_{i<I} (∑_u [s u = i] T u) · 2^i`. -/
theorem sum_mul_two_pow_regroup (T s : ℕ → ℕ) (U I : ℕ) (hs : ∀ u < U, s u < I) :
    ∑ u ∈ range U, T u * 2 ^ s u =
      ∑ i ∈ range I, (∑ u ∈ range U, if s u = i then T u else 0) * 2 ^ i := by
  simp only [sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun u hu => ?_
  rw [sum_ite_eq (range I) (s u) (fun i => T u * 2 ^ i)]
  simp [hs u (mem_range.mp hu)]

end Cslib.Complexity.NtimeDspace.Cross.Exact
