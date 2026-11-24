/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.KWiseIndependent.Reduced
import Mathlib.Data.Nat.Bitwise

/-!
# Limb-Aligned Arithmetic and Bit-Packed Table Bounds for Reduced `k`-Wise Hashing

This module develops the pure arithmetic and polynomial-limb identities underlying the Word-RAM
implementation of the two-stage universe-reduced `k`-wise independent hash family
(`Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise`):

1. **Overflow-free full-word multiply-shift (`halfMulMod`, `oddMulModWord`)**: computes
   `(2 * α + 1) * x % 2 ^ w₀ / 2 ^ (w₀ - R)` for any `0 < w₀ ≤ w`. When `α < 2 ^ (w₀ - 1)` and
   `x < 2 ^ w₀`, every intermediate product and sum is `< 2 ^ w₀`, avoiding any `2 * w₀ ≤ w`
   restriction.
2. **Exact limb factorization of `2 * 3 ^ t` (`reducedChunkBits`, `reducedHalfLimbs`,
   `reducedLimbCount`)**: decomposes any `2 * 3 ^ t`-bit element of `TrinomialField t` into
   `reducedLimbCount t = 2 * 3 ^ min t 3 ≤ 54` limbs of `reducedChunkBits t = 3 ^ (t - 3)` bits
   each, with `2 * reducedChunkBits t ≤ w` unconditionally whenever `w₀ ≤ w`, `b' ≤ w`, and
   `2 ≤ w`, and bit-packed Four-Russians table size
   `reducedTableBits t ≤ max 8 (2 ^ (b / 2)) = o(2 ^ b)` bits
   (`reducedTableWords t w ≤ 2 * reducedTableBits t / w + 1` words) whenever `b' ≤ 3 * b`.
3. **Bit-packed word slices (`getLimb`) and limb-level polynomial multiplication / 4-block
   trinomial reduction (`packLimbs`, `truncLimbs`)**: proves that limb-by-limb carryless
   multiplication followed by limb-aligned 4-block XOR reduction computes exact multiplication and
   addition in `TrinomialField t`.

## Main definitions

* `Cslib.Probability.halfMulMod`, `Cslib.Probability.oddMulModWord`: overflow-free full-word
  odd-multiplier modular product `(2 * α + 1) * x % 2 ^ w₀`.
* `Cslib.Probability.reducedChunkBits`, `Cslib.Probability.reducedHalfLimbs`,
  `Cslib.Probability.reducedLimbCount`: limb bit-width `3 ^ (t - 3)` and limb counts
  `3 ^ min t 3 ≤ 27`, `2 * 3 ^ min t 3 ≤ 54`.
* `Cslib.Probability.reducedTableBits`, `Cslib.Probability.reducedPackShift`,
  `Cslib.Probability.reducedTableWords`: bit-packed Four-Russians table size in bits and words.
* `Cslib.Probability.getLimb`, `Cslib.Probability.packLimbs`,
  `Cslib.Probability.truncLimbs`: conversion between natural numbers `< 2 ^ (L * c)` and `L` limbs
  of `c` bits.

## Main results

* `Cslib.Probability.oddMulModWord_parts_lt`: every intermediate product, shift, and sum in
  `halfMulMod (w₀ - 1)` and `oddMulModWord w₀` is strictly `< 2 ^ w₀` when `0 < w₀`,
  `α < 2 ^ (w₀ - 1)`, and `x < 2 ^ w₀`.
* `Cslib.Probability.oddMulModWord_shiftRight_eq_multiplyShiftReduced`: `oddMulModWord` shifted
  right by `w₀ - R` equals `multiplyShiftReduced`.
* `Cslib.Probability.two_mul_reducedChunkBits_le`: `2 * reducedChunkBits t ≤ w` whenever `w₀ ≤ w`,
  `b' ≤ w`, and `2 ≤ w`.
* `Cslib.Probability.reducedTableBits_le`: `reducedTableBits t ≤ max 8 (2 ^ (b / 2))` whenever
  `b' ≤ 3 * b`.
* `Cslib.Probability.reducedTableWords_le`:
  `reducedTableWords t w ≤ 2 * reducedTableBits t / w + 1`.
-/

public section

namespace Cslib.Probability

open Finset Polynomial

/-! ## Section 1: Overflow-free full-word `multiplyShiftReduced` arithmetic -/

/-- Computes `(α * (x' % 2 ^ m)) % 2 ^ m` by splitting `m` at `h = m / 2`. Whenever `α < 2 ^ m` and
`x' < 2 ^ m`, every intermediate product and sum is `< 2 ^ (m + 1)`. -/
@[expose] def halfMulMod (m α x' : ℕ) : ℕ :=
  let h := m / 2
  let α₀ := α &&& (2 ^ h - 1)
  let α₁ := α >>> h
  let x₀ := x' &&& (2 ^ h - 1)
  let x₁ := x' >>> h
  let p₀ := (α₀ * x₀) &&& (2 ^ m - 1)
  let p₁ := ((α₀ * x₁) &&& (2 ^ (m - h) - 1)) <<< h
  let p₂ := ((α₁ * x₀) &&& (2 ^ (m - h) - 1)) <<< h
  let p₃ := ((α₁ &&& (2 ^ (m - 2 * h) - 1)) * (x₁ &&& (2 ^ (m - 2 * h) - 1))) <<< (2 * h)
  (((((p₀ + p₁) &&& (2 ^ m - 1)) + p₂) &&& (2 ^ m - 1)) + p₃) &&& (2 ^ m - 1)

/-- Computes `(2 * α + 1) * x % 2 ^ w₀` using `halfMulMod (w₀ - 1)` so that every intermediate
quantity is strictly less than `2 ^ w₀` whenever `α < 2 ^ (w₀ - 1)` and `x < 2 ^ w₀`. -/
@[expose] def oddMulModWord (w₀ α x : ℕ) : ℕ :=
  let m := w₀ - 1
  let x' := x &&& (2 ^ m - 1)
  let p := halfMulMod m α x'
  (x &&& 1) + ((((x >>> 1) + p) &&& (2 ^ m - 1)) <<< 1)

private theorem mul_and_lt_of_le_one {a b d : ℕ} (hd : d ≤ 1) :
    (a &&& (2 ^ d - 1)) * (b &&& (2 ^ d - 1)) < 2 ^ d := by
  rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
  · simp
  · simp only [pow_one]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h, Nat.mod_lt b two_pos]

theorem halfMulMod_lt (m α x' : ℕ) : halfMulMod m α x' < 2 ^ m :=
  Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos m) one_pos)

theorem oddMulModWord_lt {w₀ : ℕ} (hw₀ : 0 < w₀) (α x : ℕ) :
    oddMulModWord w₀ α x < 2 ^ w₀ := by
  have hhigh := Nat.and_lt_two_pow
    ((x >>> 1) + halfMulMod (w₀ - 1) α (x &&& (2 ^ (w₀ - 1) - 1)))
    (Nat.sub_lt (Nat.two_pow_pos (w₀ - 1)) one_pos)
  have hpow : 2 ^ w₀ = 2 * 2 ^ (w₀ - 1) := by rw [← pow_succ', Nat.sub_add_cancel hw₀]
  dsimp only [oddMulModWord]
  rw [Nat.and_one_is_mod, Nat.shiftLeft_eq, pow_one]
  omega

/-- Every intermediate product, shift, and sum in `halfMulMod (w₀ - 1) α_val (u_val &&& ...)` and
`oddMulModWord w₀ α_val u_val` is strictly `< 2 ^ w₀` whenever `0 < w₀`, `α_val < 2 ^ (w₀ - 1)`,
and `u_val < 2 ^ w₀`. -/
theorem oddMulModWord_parts_lt {w₀ α_val u_val : ℕ} (hw₀ : 0 < w₀)
    (hα : α_val < 2 ^ (w₀ - 1)) (hu : u_val < 2 ^ w₀) :
    let m := w₀ - 1
    let h := m / 2
    let x' := u_val &&& (2 ^ m - 1)
    let α₀ := α_val &&& (2 ^ h - 1)
    let α₁ := α_val >>> h
    let x₀ := x' &&& (2 ^ h - 1)
    let x₁ := x' >>> h
    let p₀ := (α₀ * x₀) &&& (2 ^ m - 1)
    let p₁ := ((α₀ * x₁) &&& (2 ^ (m - h) - 1)) <<< h
    let p₂ := ((α₁ * x₀) &&& (2 ^ (m - h) - 1)) <<< h
    let p₃ := ((α₁ &&& (2 ^ (m - 2 * h) - 1)) * (x₁ &&& (2 ^ (m - 2 * h) - 1))) <<< (2 * h)
    let s₁ := (p₀ + p₁) &&& (2 ^ m - 1)
    let s₂ := (s₁ + p₂) &&& (2 ^ m - 1)
    let hm := (s₂ + p₃) &&& (2 ^ m - 1)
    α₀ * x₀ < 2 ^ w₀ ∧
    α₀ * x₁ < 2 ^ w₀ ∧
    (((α₀ * x₁) &&& (2 ^ (m - h) - 1)) <<< h) < 2 ^ w₀ ∧
    α₁ * x₀ < 2 ^ w₀ ∧
    (((α₁ * x₀) &&& (2 ^ (m - h) - 1)) <<< h) < 2 ^ w₀ ∧
    (α₁ &&& (2 ^ (m - 2 * h) - 1)) * (x₁ &&& (2 ^ (m - 2 * h) - 1)) < 2 ^ w₀ ∧
    (((α₁ &&& (2 ^ (m - 2 * h) - 1)) * (x₁ &&& (2 ^ (m - 2 * h) - 1))) <<< (2 * h)) < 2 ^ w₀ ∧
    p₀ + p₁ < 2 ^ w₀ ∧
    s₁ + p₂ < 2 ^ w₀ ∧
    s₂ + p₃ < 2 ^ w₀ ∧
    (u_val >>> 1) + hm < 2 ^ w₀ ∧
    ((((u_val >>> 1) + hm) &&& (2 ^ m - 1)) <<< 1) < 2 ^ w₀ ∧
    (u_val &&& 1) + ((((u_val >>> 1) + hm) &&& (2 ^ m - 1)) <<< 1) < 2 ^ w₀ := by
  intro m h x' α₀ α₁ x₀ x₁ p₀ p₁ p₂ p₃ s₁ s₂ hm
  have mask_lt (a n : ℕ) : a &&& (2 ^ n - 1) < 2 ^ n :=
    Nat.and_lt_two_pow a (Nat.sub_lt (Nat.two_pow_pos n) one_pos)
  have shr_lt {a n k : ℕ} (hk : k ≤ n) (ha : a < 2 ^ n) : a >>> k < 2 ^ (n - k) := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rwa [← pow_add, Nat.add_sub_of_le hk])
  have shl_lt {a k : ℕ} (hk : k ≤ m) (ha : a < 2 ^ (m - k)) : a <<< k < 2 ^ m :=
    (Nat.shiftLeft_lt ha).trans_eq (congrArg (2 ^ ·) (Nat.sub_add_cancel hk))
  have h2m : 2 * 2 ^ m = 2 ^ w₀ := by rw [← pow_succ', Nat.sub_add_cancel hw₀]
  have hm_lt : 2 ^ m < 2 ^ w₀ := by have := Nat.two_pow_pos m; omega
  have h_le : h ≤ m := Nat.div_le_self m 2
  have h2_le : 2 * h ≤ m := Nat.mul_div_le m 2
  have hp₀_raw : α₀ * x₀ < 2 ^ m := (Nat.mul_lt_mul'' (mask_lt _ h) (mask_lt _ h)).trans_le
    (by rw [← pow_add, ← two_mul]; exact Nat.pow_le_pow_right two_pos h2_le)
  have hp₁_raw : α₀ * x₁ < 2 ^ m := (Nat.mul_lt_mul'' (mask_lt _ h)
    (shr_lt h_le (mask_lt _ m))).trans_eq (by rw [← pow_add, Nat.add_sub_of_le h_le])
  have hp₂_raw : α₁ * x₀ < 2 ^ m := (Nat.mul_lt_mul'' (shr_lt h_le hα)
    (mask_lt _ h)).trans_eq (by rw [← pow_add, Nat.sub_add_cancel h_le])
  have hp₃_mul := mul_and_lt_of_le_one (a := α₁) (b := x₁) (d := m - 2 * h) (by omega)
  have hp₁_lt : p₁ < 2 ^ m := shl_lt h_le (mask_lt _ _)
  have hp₂_lt : p₂ < 2 ^ m := shl_lt h_le (mask_lt _ _)
  have hp₃_lt : p₃ < 2 ^ m := shl_lt h2_le hp₃_mul
  have hp₀_lt : p₀ < 2 ^ m := mask_lt _ m
  have hs₁_lt : s₁ < 2 ^ m := mask_lt _ m
  have hs₂_lt : s₂ < 2 ^ m := mask_lt _ m
  have hhm_lt : hm < 2 ^ m := mask_lt _ m
  have hu_shr : u_val >>> 1 < 2 ^ m := shr_lt hw₀ hu
  have hodd : (u_val &&& 1) + ((((u_val >>> 1) + hm) &&& (2 ^ m - 1)) <<< 1) < 2 ^ w₀ :=
    oddMulModWord_lt hw₀ α_val u_val
  exact ⟨hp₀_raw.trans hm_lt, hp₁_raw.trans hm_lt, hp₁_lt.trans hm_lt,
    hp₂_raw.trans hm_lt, hp₂_lt.trans hm_lt,
    hp₃_mul.trans_le (Nat.pow_le_pow_right two_pos (by omega)), hp₃_lt.trans hm_lt,
    by omega, by omega, by omega, by omega, by omega, hodd⟩

/-- Exact modular correctness of `halfMulMod`: for all `m α x' : ℕ`, `halfMulMod m α x'` equals
`(α * x') % 2 ^ m`. -/
theorem halfMulMod_eq (m α x' : ℕ) :
    halfMulMod m α x' = (α * x') % 2 ^ m := by
  dsimp only [halfMulMod]
  set h := m / 2
  have h_le : h ≤ m := Nat.div_le_self m 2
  have h2_le : 2 * h ≤ m := Nat.mul_div_le m 2
  have hp₃_lt := mul_and_lt_of_le_one (a := α >>> h) (b := x' >>> h) (d := m - 2 * h) (by omega)
  simp only [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    at hp₃_lt ⊢
  have hsh (y k : ℕ) (hk : k ≤ m) : (y % 2 ^ (m - k)) * 2 ^ k = (y * 2 ^ k) % 2 ^ m := by
    rw [← Nat.mul_mod_mul_right, ← pow_add, Nat.sub_add_cancel hk]
  have hp₃_mod : (α / 2 ^ h % 2 ^ (m - 2 * h)) * (x' / 2 ^ h % 2 ^ (m - 2 * h)) =
      (α / 2 ^ h * (x' / 2 ^ h)) % 2 ^ (m - 2 * h) := by
    rw [← Nat.mod_eq_of_lt hp₃_lt, ← Nat.mul_mod]
  rw [hsh _ h h_le, hsh _ h h_le, hp₃_mod, hsh _ (2 * h) h2_le]
  simp only [Nat.add_mod_mod, Nat.mod_add_mod]
  congr 1
  conv_rhs => rw [← Nat.div_add_mod α (2 ^ h), ← Nat.div_add_mod x' (2 ^ h)]
  rw [two_mul, pow_add]
  ring

/-- Exact modular correctness of `oddMulModWord`: for all `0 < w₀`,
`oddMulModWord w₀ α x = (2 * α + 1) * x % 2 ^ w₀`. -/
theorem oddMulModWord_eq {w₀ : ℕ} (hw₀ : 0 < w₀) (α x : ℕ) :
    oddMulModWord w₀ α x = (2 * α + 1) * x % 2 ^ w₀ := by
  dsimp only [oddMulModWord]
  rw [halfMulMod_eq, Nat.and_one_is_mod]
  simp only [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    pow_one, Nat.mul_mod_mod, Nat.add_mod_mod]
  set m := w₀ - 1
  have hpow : 2 ^ w₀ = 2 * 2 ^ m := by rw [← pow_succ', Nat.sub_add_cancel hw₀]
  have h1 := Nat.div_add_mod x 2
  have h2 := Nat.div_add_mod (x / 2 + α * x) (2 ^ m)
  have hlt : x % 2 + (x / 2 + α * x) % 2 ^ m * 2 < 2 * 2 ^ m := by
    have := Nat.mod_lt x two_pos
    have := Nat.mod_lt (x / 2 + α * x) (Nat.two_pow_pos m)
    omega
  rw [hpow, show (2 * α + 1) * x =
      (x % 2 + (x / 2 + α * x) % 2 ^ m * 2) + (2 * 2 ^ m) * ((x / 2 + α * x) / 2 ^ m) by linarith,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- Shifting `oddMulModWord w₀ α.val u.val` right by `w₀ - R` computes
`(multiplyShiftReduced U w₀ R α u).val`. -/
theorem oddMulModWord_shiftRight_eq_multiplyShiftReduced {U w₀ R : ℕ} (hw₀ : 0 < w₀)
    (α : Fin (2 ^ (w₀ - 1))) (u : Fin U) :
    oddMulModWord w₀ α.val u.val >>> (w₀ - R) = (multiplyShiftReduced U w₀ R α u).val := by
  rw [oddMulModWord_eq hw₀, Nat.shiftRight_eq_div_pow, val_multiplyShiftReduced]

/-! ## Section 2: Limb parameters and bit-packed Four-Russians table bounds -/

/-- Limb bit-width `c = 3 ^ (t - 3)` for trinomial parameter `t`. -/
@[expose] def reducedChunkBits (t : ℕ) : ℕ :=
  3 ^ (t - 3)

/-- Half-field limb count `L₀ = 3 ^ min t 3 ≤ 27`, so `L₀ * c = 3 ^ t`. -/
@[expose] def reducedHalfLimbs (t : ℕ) : ℕ :=
  3 ^ min t 3

/-- Full-field limb count `L = 2 * L₀ = 2 * 3 ^ min t 3 ≤ 54`, so `L * c = 2 * 3 ^ t`. -/
@[expose] def reducedLimbCount (t : ℕ) : ℕ :=
  2 * reducedHalfLimbs t

theorem reducedChunkBits_pos (t : ℕ) : 0 < reducedChunkBits t := by
  dsimp only [reducedChunkBits]; positivity

theorem reducedHalfLimbs_pos (t : ℕ) : 0 < reducedHalfLimbs t := by
  dsimp only [reducedHalfLimbs]; positivity

theorem reducedLimbCount_pos (t : ℕ) : 0 < reducedLimbCount t := by
  dsimp only [reducedLimbCount, reducedHalfLimbs]; positivity

theorem reducedHalfLimbs_mul_chunkBits (t : ℕ) :
    reducedHalfLimbs t * reducedChunkBits t = 3 ^ t := by
  rw [reducedHalfLimbs, reducedChunkBits, ← pow_add, show min t 3 + (t - 3) = t by omega]

theorem reducedLimbCount_mul_chunkBits (t : ℕ) :
    reducedLimbCount t * reducedChunkBits t = 2 * 3 ^ t := by
  rw [reducedLimbCount, Nat.mul_assoc, reducedHalfLimbs_mul_chunkBits]

theorem reducedHalfLimbs_le (t : ℕ) : reducedHalfLimbs t ≤ 27 :=
  Nat.pow_le_pow_right (by decide) (Nat.min_le_right t 3)

theorem reducedLimbCount_le (t : ℕ) : reducedLimbCount t ≤ 54 := by
  have := reducedHalfLimbs_le t; unfold reducedLimbCount; omega

/-- A trinomial step above `3` comes from more than two target bits, so
`2 * 3 ^ (t - 1) < B` (`two_mul_three_pow_pred_lt_of_two_lt`). -/
private theorem two_mul_three_pow_pred_lt_reducedTargetBits {w₀ b b' : ℕ}
    (ht : ¬reducedTrinomialStep w₀ b b' ≤ 3) :
    2 * 3 ^ (reducedTrinomialStep w₀ b b' - 1) < reducedTargetBits w₀ b b' :=
  (two_mul_three_pow_pred_lt_of_two_lt <| not_le.mp fun hle =>
    ht (by rw [reducedTrinomialStep, trinomialStepAux, ite_eq_left hle]; decide)).2

/-- Whenever `w₀ ≤ w`, `b' ≤ w`, and `2 ≤ w`, `2 * reducedChunkBits (reducedTrinomialStep w₀ b b')`
fits in a single `w`-bit word (`≤ w`) unconditionally for all `b : ℕ`. -/
theorem two_mul_reducedChunkBits_le {w₀ b b' w : ℕ} (hw₀ : w₀ ≤ w) (hb' : b' ≤ w) (hw : 2 ≤ w) :
    2 * reducedChunkBits (reducedTrinomialStep w₀ b b') ≤ w := by
  by_cases ht : reducedTrinomialStep w₀ b b' ≤ 3
  · rw [reducedChunkBits, Nat.sub_eq_zero_of_le ht]; omega
  · have hlt := two_mul_three_pow_pred_lt_reducedTargetBits ht
    have : reducedChunkBits (reducedTrinomialStep w₀ b b') ≤
        3 ^ (reducedTrinomialStep w₀ b b' - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    unfold reducedTargetBits at hlt
    omega

/-- Total number of bits `(2 * c) * 2 ^ (2 * c)` in the Four-Russians carryless multiplication
table for trinomial step `t`. -/
@[expose] def reducedTableBits (t : ℕ) : ℕ :=
  (2 * reducedChunkBits t) * 2 ^ (2 * reducedChunkBits t)

/-- Whenever `b' ≤ 3 * b`, the Four-Russians table bit count satisfies
`reducedTableBits (reducedTrinomialStep w₀ b b') ≤ max 8 (2 ^ (b / 2)) = o(2 ^ b)`. -/
theorem reducedTableBits_le {w₀ b b' : ℕ} (hb' : b' ≤ 3 * b) :
    reducedTableBits (reducedTrinomialStep w₀ b b') ≤ max 8 (2 ^ (b / 2)) := by
  set t := reducedTrinomialStep w₀ b b'
  by_cases ht : t ≤ 3
  · rw [reducedTableBits, reducedChunkBits, Nat.sub_eq_zero_of_le ht]
    exact le_max_left 8 _
  · have hlt := two_mul_three_pow_pred_lt_reducedTargetBits ht
    change 2 * 3 ^ (t - 1) < reducedTargetBits w₀ b b' at hlt
    have h9 : 3 ^ (t - 1) = 9 * reducedChunkBits t := by
      rw [reducedChunkBits, show t - 1 = 2 + (t - 3) by omega, pow_add]; rfl
    have hc_pos := reducedChunkBits_pos t
    have h3c : 3 * reducedChunkBits t ≤ b / 2 := by unfold reducedTargetBits at hlt; omega
    have h2c : 2 * reducedChunkBits t ≤ 2 ^ reducedChunkBits t := by
      rcases reducedChunkBits t with _ | c
      · decide
      · have := @Nat.lt_two_pow_self c; rw [pow_succ']; omega
    refine (le_trans ?_ (Nat.pow_le_pow_right two_pos h3c)).trans (le_max_right 8 _)
    calc reducedTableBits t
        ≤ 2 ^ reducedChunkBits t * 2 ^ (2 * reducedChunkBits t) :=
          Nat.mul_le_mul_right _ h2c
      _ = 2 ^ (3 * reducedChunkBits t) := by
          rw [← pow_add, show reducedChunkBits t + 2 * reducedChunkBits t =
            3 * reducedChunkBits t by ring]

/-- Log₂ of the number of `2 * c`-bit entries packed into each `w`-bit word:
`p = min (2 * c) ⌊log₂ (w / (2 * c))⌋`. -/
@[expose] def reducedPackShift (t w : ℕ) : ℕ :=
  min (2 * reducedChunkBits t) (Nat.log 2 (w / (2 * reducedChunkBits t)))

/-- Number of `w`-bit words `2 ^ (2 * c - p)` occupied by the bit-packed Four-Russians table. -/
@[expose] def reducedTableWords (t w : ℕ) : ℕ :=
  2 ^ (2 * reducedChunkBits t - reducedPackShift t w)

theorem reducedPackShift_le (t w : ℕ) :
    reducedPackShift t w ≤ 2 * reducedChunkBits t :=
  Nat.min_le_left _ _

theorem two_pow_reducedPackShift_mul_le {t w : ℕ} (hc : 2 * reducedChunkBits t ≤ w) :
    2 ^ reducedPackShift t w * (2 * reducedChunkBits t) ≤ w := by
  have hdiv_pos : 0 < w / (2 * reducedChunkBits t) :=
    Nat.div_pos hc (by have := reducedChunkBits_pos t; omega)
  calc 2 ^ reducedPackShift t w * (2 * reducedChunkBits t)
      ≤ 2 ^ Nat.log 2 (w / (2 * reducedChunkBits t)) * (2 * reducedChunkBits t) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos (Nat.min_le_right _ _))
    _ ≤ (w / (2 * reducedChunkBits t)) * (2 * reducedChunkBits t) :=
        Nat.mul_le_mul_right _ (Nat.pow_log_le_self 2 hdiv_pos.ne')
    _ ≤ w := Nat.div_mul_le_self w _

/-- The bit-packed Four-Russians table uses at most `2 * reducedTableBits t / w + 1` words. -/
theorem reducedTableWords_le {t w : ℕ} (hc : 2 * reducedChunkBits t ≤ w) :
    reducedTableWords t w ≤ 2 * reducedTableBits t / w + 1 := by
  set c2 := 2 * reducedChunkBits t
  have hc2_pos : 0 < c2 := by have := reducedChunkBits_pos t; omega
  by_cases hle : c2 ≤ Nat.log 2 (w / c2)
  · rw [reducedTableWords, reducedPackShift, Nat.min_eq_left hle, Nat.sub_self, pow_zero]
    exact Nat.le_add_left 1 _
  · have hp : reducedPackShift t w = Nat.log 2 (w / c2) := Nat.min_eq_right (not_le.mp hle).le
    have hlt_pow : w / c2 < 2 * 2 ^ reducedPackShift t w := by
      simpa only [hp, pow_succ'] using Nat.lt_pow_succ_log_self one_lt_two (w / c2)
    have hw_le : w ≤ 2 * c2 * 2 ^ reducedPackShift t w := by
      have := Nat.div_add_mod w c2
      have := Nat.mod_lt w hc2_pos
      nlinarith
    have hmul : w * reducedTableWords t w ≤ 2 * reducedTableBits t := by
      calc w * 2 ^ (c2 - reducedPackShift t w)
          ≤ (2 * c2 * 2 ^ reducedPackShift t w) * 2 ^ (c2 - reducedPackShift t w) := by gcongr
        _ = 2 * (c2 * (2 ^ reducedPackShift t w * 2 ^ (c2 - reducedPackShift t w))) := by ring
        _ = 2 * reducedTableBits t := by
            rw [← pow_add, Nat.add_sub_of_le (reducedPackShift_le t w)]; rfl
    exact ((Nat.le_div_iff_mul_le (lt_of_lt_of_le hc2_pos hc)).mpr (by linarith)).trans
      (Nat.le_succ _)


/-! ## Section 3: Limb extraction, packing, and 4-block trinomial reduction on limbs -/

/-- Extract the `m`-th `c`-bit limb `(a >>> (m * c)) &&& (2 ^ c - 1)` of a natural number `a`. -/
@[expose] def getLimb (c a m : ℕ) : ℕ :=
  (a >>> (m * c)) &&& (2 ^ c - 1)

/-- Above bit `m * c`, the `m`-th `c`-bit limb of `a < 2 ^ (m * c)` is `0`. -/
theorem getLimb_eq_zero_of_lt {c a m : ℕ} (ha : a < 2 ^ (m * c)) :
    getLimb c a m = 0 := by
  rw [getLimb, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt ha, Nat.zero_and]

theorem getLimb_lt (c a m : ℕ) : getLimb c a m < 2 ^ c :=
  Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos c) one_pos)

theorem getLimb_zero (c m : ℕ) : getLimb c 0 m = 0 := by
  simp [getLimb]

theorem testBit_getLimb (c a m k : ℕ) :
    (getLimb c a m).testBit k = (decide (k < c) && a.testBit (m * c + k)) := by
  rw [getLimb, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight, Bool.and_comm]

theorem getLimb_xor (c a b m : ℕ) :
    getLimb c (a ^^^ b) m = getLimb c a m ^^^ getLimb c b m := by
  simp only [getLimb, Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right]

theorem getLimb_and_low {c a m s : ℕ} (hm : m < s) :
    getLimb c (a &&& (2 ^ (s * c) - 1)) m = getLimb c a m := by
  apply Nat.eq_of_testBit_eq; intro k
  have : k < c → m * c + k < s * c := fun _ => by nlinarith
  simp [testBit_getLimb]; grind

theorem getLimb_and_high (c a : ℕ) {s m : ℕ} (hm : s ≤ m) :
    getLimb c (a &&& (2 ^ (s * c) - 1)) m = 0 :=
  getLimb_eq_zero_of_lt <| (Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) one_pos)).trans_le
    (Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_right c hm))

theorem getLimb_and_self (c a s : ℕ) :
    getLimb c (a &&& (2 ^ (s * c) - 1)) s = 0 :=
  getLimb_and_high c a le_rfl

theorem getLimb_shiftRight_mul (c a s m : ℕ) :
    getLimb c (a >>> (s * c)) m = getLimb c a (s + m) := by
  rw [getLimb, getLimb, ← Nat.shiftRight_add, ← Nat.add_mul]

theorem getLimb_shiftLeft_mul_low (c a : ℕ) {s m : ℕ} (hm : m < s) :
    getLimb c (a <<< (s * c)) m = 0 := by
  apply Nat.eq_of_testBit_eq; intro k
  have : k < c → m * c + k < s * c := fun _ => by nlinarith
  simp [testBit_getLimb, Nat.testBit_shiftLeft]; grind

theorem getLimb_shiftLeft_mul_add (c a s m : ℕ) :
    getLimb c (a <<< (s * c)) (s + m) = getLimb c a m := by
  simp only [getLimb, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.add_mul, pow_add,
    mul_comm (2 ^ (s * c)), Nat.mul_div_mul_right _ _ (Nat.two_pow_pos (s * c))]

theorem getLimb_xor_shiftLeft_self {c a val s : ℕ}
    (ha : a < 2 ^ (s * c)) (hval : val < 2 ^ c) :
    getLimb c (a ^^^ (val <<< (s * c))) s = val := by
  have hsh := getLimb_shiftLeft_mul_add c val s 0
  rw [Nat.add_zero] at hsh
  rw [getLimb_xor, getLimb_eq_zero_of_lt ha, Nat.zero_xor, hsh, getLimb,
    Nat.zero_mul, Nat.shiftRight_zero, Nat.and_two_pow_sub_one_of_lt_two_pow hval]

theorem getLimb_xor_shiftLeft_of_ne {c a val s m : ℕ}
    (hval : val < 2 ^ c) (hne : m ≠ s) :
    getLimb c (a ^^^ (val <<< (s * c))) m = getLimb c a m := by
  rw [getLimb_xor, show getLimb c (val <<< (s * c)) m = 0 from ?_, Nat.xor_zero]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact getLimb_shiftLeft_mul_low c val hlt
  · rw [show m = s + (m - s) by omega, getLimb_shiftLeft_mul_add]
    exact getLimb_eq_zero_of_lt
      (hval.trans_le (Nat.pow_le_pow_right two_pos (Nat.le_mul_of_pos_left c (by omega))))

/-- Pack `n` limbs `f 0, …, f (n - 1)` of `c` bits each into a single natural number
`< 2 ^ (n * c)`. -/
@[expose] def packLimbs (c : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => packLimbs c n f ^^^ ((f n &&& (2 ^ c - 1)) <<< (n * c))

theorem packLimbs_congr {c n : ℕ} {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) :
    packLimbs c n f = packLimbs c n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [packLimbs, packLimbs, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem packLimbs_lt (c n : ℕ) (f : ℕ → ℕ) :
    packLimbs c n f < 2 ^ (n * c) := by
  induction n with
  | zero => simp [packLimbs]
  | succ n ih =>
    refine Nat.xor_lt_two_pow (ih.trans_le (Nat.pow_le_pow_right two_pos
      (Nat.mul_le_mul_right c (Nat.le_succ n)))) ?_
    exact (Nat.shiftLeft_lt (Nat.and_lt_two_pow _
      (Nat.sub_lt (Nat.two_pow_pos c) one_pos))).trans_eq (by rw [Nat.add_comm c, ← Nat.succ_mul])

theorem getLimb_packLimbs (c : ℕ) {n m : ℕ} (f : ℕ → ℕ) (hm : m < n) :
    getLimb c (packLimbs c n f) m = f m &&& (2 ^ c - 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hand_lt := Nat.and_lt_two_pow (f n) (Nat.sub_lt (Nat.two_pow_pos c) one_pos)
    rcases eq_or_ne m n with rfl | hne
    · exact getLimb_xor_shiftLeft_self (packLimbs_lt c m f) hand_lt
    · rw [packLimbs, getLimb_xor_shiftLeft_of_ne hand_lt hne]
      exact ih (by omega)

theorem getLimb_packLimbs_of_lt (c : ℕ) {n m : ℕ} {f : ℕ → ℕ}
    (hm : m < n) (hf : f m < 2 ^ c) :
    getLimb c (packLimbs c n f) m = f m := by
  rw [getLimb_packLimbs c f hm, Nat.and_two_pow_sub_one_of_lt_two_pow hf]

theorem getLimb_packLimbs_of_ge (c : ℕ) {n m : ℕ} (f : ℕ → ℕ) (hm : n ≤ m) :
    getLimb c (packLimbs c n f) m = 0 :=
  getLimb_eq_zero_of_lt <| (packLimbs_lt c n f).trans_le
    (Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_right c hm))

theorem eq_of_getLimb_eq {c : ℕ} (hc : 0 < c) {a b : ℕ}
    (h : ∀ m, getLimb c a m = getLimb c b m) : a = b := by
  apply Nat.eq_of_testBit_eq; intro idx
  simpa only [testBit_getLimb, Nat.mod_lt idx hc, decide_true, Bool.true_and,
    Nat.mul_comm (idx / c) c, Nat.div_add_mod] using
    congrArg (·.testBit (idx % c)) (h (idx / c))

theorem packLimbs_getLimb {c : ℕ} (hc : 0 < c) (n : ℕ) {a : ℕ} (ha : a < 2 ^ (n * c)) :
    packLimbs c n (getLimb c a) = a := by
  refine eq_of_getLimb_eq hc fun m => ?_
  by_cases hm : m < n
  · exact getLimb_packLimbs_of_lt c hm (getLimb_lt c a m)
  · rw [getLimb_packLimbs_of_ge c _ (not_lt.mp hm), getLimb_eq_zero_of_lt
      (ha.trans_le (Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_right c (not_lt.mp hm))))]

theorem packLimbs_xor {c : ℕ} (n : ℕ) (f g : ℕ → ℕ) :
    packLimbs c n (fun i => f i ^^^ g i) = packLimbs c n f ^^^ packLimbs c n g := by
  induction n with
  | zero => simp [packLimbs]
  | succ n ih =>
    simp only [packLimbs, ih, Nat.and_xor_distrib_right, Nat.shiftLeft_xor_distrib]
    ac_rfl

theorem getLimb_zero_of_lt {c val : ℕ} (hval : val < 2 ^ c) :
    getLimb c val 0 = val := by
  rw [getLimb, Nat.zero_mul, Nat.shiftRight_zero, Nat.and_two_pow_sub_one_of_lt_two_pow hval]

theorem packLimbs_update_xor {c n i v : ℕ} (f : ℕ → ℕ)
    (hi : i < n) (hv : v < 2 ^ c) :
    packLimbs c n (Function.update f i (f i ^^^ v)) =
      packLimbs c n f ^^^ (v <<< (i * c)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    dsimp only [packLimbs]
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with rfl | hlt
    · rw [packLimbs_congr fun j hj => Function.update_of_ne hj.ne _ f, Function.update_self,
        Nat.and_xor_distrib_right, Nat.and_two_pow_sub_one_of_lt_two_pow hv,
        Nat.shiftLeft_xor_distrib, Nat.xor_assoc]
    · rw [Function.update_of_ne hlt.ne', ih hlt]
      ac_rfl

/-- Updating two consecutive limbs `i` and `i + 1` of `f` by XORing `v &&& (2 ^ c - 1)` and
`v >>> c` (where `v < 2 ^ (2 * c)`) XORs `packLimbs c n f` with `v <<< (i * c)`. -/
theorem packLimbs_update_pair {c n i v : ℕ} (f : ℕ → ℕ)
    (hi : i + 1 < n) (hv : v < 2 ^ (2 * c)) :
    packLimbs c n
      (Function.update (Function.update f i (f i ^^^ (v &&& (2 ^ c - 1))))
        (i + 1) (f (i + 1) ^^^ (v >>> c))) =
      packLimbs c n f ^^^ (v <<< (i * c)) := by
  have hv_lo := Nat.and_lt_two_pow v (Nat.sub_lt (Nat.two_pow_pos c) one_pos)
  have hv_hi : v >>> c < 2 ^ c := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_lt_of_lt_mul (by rwa [← pow_add, ← two_mul])
  let g := Function.update f i (f i ^^^ (v &&& (2 ^ c - 1)))
  have hupd := packLimbs_update_xor g hi hv_hi
  rw [show g (i + 1) = f (i + 1) from Function.update_of_ne (Nat.succ_ne_self i) _ f] at hupd
  rw [hupd, packLimbs_update_xor f (Nat.lt_of_succ_lt hi) hv_lo, Nat.xor_assoc]
  congr 1
  rw [Nat.succ_mul, Nat.add_comm (i * c) c, Nat.shiftLeft_add, ← Nat.shiftLeft_xor_distrib,
    and_xor_shiftRight_shiftLeft]

/-- Low-half limb formula (`m < L₀`) for `reduceTrinomialCode t P`. -/
theorem getLimb_reduceTrinomialCode_low (t P : ℕ) {m : ℕ} (hm : m < reducedHalfLimbs t) :
    let c := reducedChunkBits t
    let L₀ := reducedHalfLimbs t
    getLimb c (reduceTrinomialCode t P) m =
      (getLimb c P m ^^^ getLimb c P (3 * L₀ + m)) ^^^ getLimb c P (2 * L₀ + m) := by
  intro c L₀
  simp only [reduceTrinomialCode, ← reducedHalfLimbs_mul_chunkBits, ← Nat.mul_assoc,
    show reducedChunkBits t = c from rfl, show reducedHalfLimbs t = L₀ from rfl,
    getLimb_xor, getLimb_shiftRight_mul]
  rw [getLimb_and_low (by omega : m < 2 * L₀), getLimb_and_low hm, getLimb_shiftRight_mul,
    getLimb_shiftLeft_mul_low c _ hm, Nat.xor_zero]

/-- High-half limb formula (`m < L₀`, limb index `L₀ + m`) for `reduceTrinomialCode t P`. -/
theorem getLimb_reduceTrinomialCode_high (t P : ℕ) {m : ℕ} (hm : m < reducedHalfLimbs t) :
    let c := reducedChunkBits t
    let L₀ := reducedHalfLimbs t
    getLimb c (reduceTrinomialCode t P) (L₀ + m) =
      (getLimb c P (L₀ + m) ^^^ getLimb c P (4 * L₀ + m)) ^^^ getLimb c P (2 * L₀ + m) := by
  intro c L₀
  simp only [reduceTrinomialCode, ← reducedHalfLimbs_mul_chunkBits, ← Nat.mul_assoc,
    show reducedChunkBits t = c from rfl, show reducedHalfLimbs t = L₀ from rfl,
    getLimb_xor, getLimb_shiftRight_mul]
  rw [getLimb_and_low (by omega : L₀ + m < 2 * L₀),
    getLimb_and_high c _ (Nat.le_add_right L₀ m), Nat.xor_zero, getLimb_shiftLeft_mul_add,
    getLimb_and_low hm, getLimb_shiftRight_mul, show 3 * L₀ + (L₀ + m) = 4 * L₀ + m by ring]

/-- Equivalence between `L`-tuples of `c`-bit limbs `Fin L → Fin (2 ^ c)` and
`Fin (2 ^ (L * c))`. -/
@[expose] def limbsEquivFin (c L : ℕ) (hc : 0 < c) :
    (Fin L → Fin (2 ^ c)) ≃ Fin (2 ^ (L * c)) where
  toFun f :=
    ⟨packLimbs c L (fun i => if h : i < L then (f ⟨i, h⟩).val else 0), packLimbs_lt c L _⟩
  invFun a i :=
    ⟨getLimb c a.val i.val, getLimb_lt c a.val i.val⟩
  left_inv f := by
    funext i
    ext
    dsimp only
    rw [getLimb_packLimbs_of_lt c i.isLt (by simp [i.isLt, (f i).isLt])]
    simp [i.isLt]
  right_inv a := by
    ext
    dsimp only
    have hcongr : packLimbs c L (fun i => if h : i < L then getLimb c a.val i else 0) =
        packLimbs c L (getLimb c a.val) :=
      packLimbs_congr fun i hi => dite_eq_left hi
    rw [hcongr, packLimbs_getLimb hc L a.isLt]

/-- Low `n` limbs `a &&& (2 ^ (n * c) - 1)` of a natural number `a`. -/
@[expose] def truncLimbs (c n a : ℕ) : ℕ :=
  a &&& (2 ^ (n * c) - 1)

@[simp]
theorem truncLimbs_zero (c a : ℕ) : truncLimbs c 0 a = 0 := by
  simp [truncLimbs]

theorem truncLimbs_of_lt {c n a : ℕ} (ha : a < 2 ^ (n * c)) :
    truncLimbs c n a = a :=
  Nat.and_two_pow_sub_one_of_lt_two_pow ha

theorem truncLimbs_succ (c n a : ℕ) :
    truncLimbs c (n + 1) a = truncLimbs c n a ^^^ (getLimb c a n <<< (n * c)) := by
  apply Nat.eq_of_testBit_eq; intro idx
  simp [truncLimbs, testBit_getLimb, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.succ_mul]
  grind

theorem clmul_truncLimbs_right_succ (c i m xc x : ℕ) :
    clmul xc (truncLimbs c (m + 1) x) <<< (i * c) =
      (clmul xc (truncLimbs c m x) <<< (i * c)) ^^^
        (clmul xc (getLimb c x m) <<< ((i + m) * c)) := by
  rw [truncLimbs_succ, clmul_xor_right, clmul_shiftLeft_right, Nat.shiftLeft_xor_distrib,
    Nat.add_mul, Nat.add_comm (i * c) (m * c), Nat.shiftLeft_add]

theorem clmul_truncLimbs_left_succ (c i a x : ℕ) :
    clmul (truncLimbs c (i + 1) a) x =
      clmul (truncLimbs c i a) x ^^^ (clmul (getLimb c a i) x <<< (i * c)) := by
  rw [truncLimbs_succ, clmul_xor_left, clmul_shiftLeft_left]

/-- Mask `2 ^ min c (b' - m * c) - 1` for extracting the `< b'` bits of limb `m`. -/
@[expose] def reducedOutMask (c b' m : ℕ) : ℕ :=
  2 ^ min c (b' - m * c) - 1

/-- Shift `if m * c < b' then m * c else 0` for placing limb `m` into the `< b'` output word. -/
@[expose] def reducedOutShift (c b' m : ℕ) : ℕ :=
  if m * c < b' then m * c else 0

theorem reducedOutMask_lt (c b' m : ℕ) : reducedOutMask c b' m < 2 ^ c :=
  (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans_le
    (Nat.pow_le_pow_right two_pos (Nat.min_le_left _ _))

theorem reducedOutShift_le (c b' m : ℕ) : reducedOutShift c b' m ≤ b' := by
  unfold reducedOutShift; split_ifs with h <;> [exact h.le; exact Nat.zero_le b']

theorem and_reducedOutMask_shiftLeft_lt (c b' m v : ℕ) :
    (v &&& reducedOutMask c b' m) <<< reducedOutShift c b' m < 2 ^ max b' 1 := by
  dsimp only [reducedOutMask, reducedOutShift]
  split_ifs with h
  · exact (Nat.shiftLeft_lt (Nat.and_lt_two_pow v
      (Nat.sub_lt (Nat.two_pow_pos _) one_pos))).trans_le
      (Nat.pow_le_pow_right two_pos (by omega))
  · rw [Nat.sub_eq_zero_of_le (not_lt.mp h)]; simp

theorem packLimbs_and_mask_succ (c b' n : ℕ) (f : ℕ → ℕ) :
    (packLimbs c (n + 1) f) &&& (2 ^ b' - 1) =
      ((packLimbs c n f) &&& (2 ^ b' - 1)) ^^^
        ((f n &&& reducedOutMask c b' n) <<< reducedOutShift c b' n) := by
  rw [packLimbs, Nat.and_xor_distrib_right]
  congr 1
  apply Nat.eq_of_testBit_eq; intro idx
  simp [reducedOutMask, reducedOutShift, Nat.testBit_shiftLeft]
  grind

theorem shiftRight_lt_reducedTableWords {t w idx : ℕ}
    (hidx : idx < 2 ^ (2 * reducedChunkBits t)) :
    idx >>> reducedPackShift t w < reducedTableWords t w := by
  rw [reducedTableWords, Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (by rwa [← pow_add, Nat.add_sub_of_le (reducedPackShift_le t w)])

theorem shiftRight_add_one_le (idx p : ℕ) :
    (idx + 1) >>> p ≤ (idx >>> p) + 1 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    ← Nat.add_div_right idx (Nat.two_pow_pos p)]
  exact Nat.div_le_div_right (Nat.add_le_add_left Nat.one_le_two_pow idx)

theorem and_lt_of_lt_of_shiftRight_eq {i idx p : ℕ}
    (hlt : i < idx) (heq : i >>> p = idx >>> p) :
    i &&& (2 ^ p - 1) < idx &&& (2 ^ p - 1) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at heq
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  have hi := Nat.div_add_mod i (2 ^ p)
  have hidx := Nat.div_add_mod idx (2 ^ p)
  rw [heq] at hi
  omega

theorem two_pow_two_mul_chunkBits_shiftRight (t w : ℕ) :
    2 ^ (2 * reducedChunkBits t) >>> reducedPackShift t w = reducedTableWords t w := by
  rw [reducedTableWords, Nat.shiftRight_eq_div_pow]
  exact Nat.pow_div (reducedPackShift_le t w) two_pos

theorem xor_shiftLeft_lt_two_pow {c s a v : ℕ}
    (ha : a < 2 ^ (s * c)) (hv : v < 2 ^ c) :
    a ^^^ (v <<< (s * c)) < 2 ^ ((s + 1) * c) :=
  Nat.xor_lt_two_pow
    (ha.trans_le (Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_right c (Nat.le_succ s))))
    (by rw [Nat.shiftLeft_eq, Nat.succ_mul, Nat.add_comm (s * c) c, Nat.pow_add]
        exact Nat.mul_lt_mul_of_pos_right hv (Nat.two_pow_pos _))

/-- Ascending Horner prefix over `TrinomialField t`, processing coefficients from `k - 1` down to
`k - n` as `n` goes from `0` to `k`. -/
@[expose] noncomputable def hornerPrefix (t k : ℕ)
    (c_field : Fin k → TrinomialField t) (x_field : TrinomialField t) : ℕ → TrinomialField t
  | 0 => 0
  | n + 1 =>
    if h : n < k then
      hornerPrefix t k c_field x_field n * x_field + c_field ⟨k - 1 - n, by omega⟩
    else
      hornerPrefix t k c_field x_field n

theorem hornerPrefix_succ_of_lt {t k n : ℕ} (hn : n < k)
    (c_field : Fin k → TrinomialField t) (x_field : TrinomialField t) :
    hornerPrefix t k c_field x_field (n + 1) =
      hornerPrefix t k c_field x_field n * x_field + c_field ⟨k - 1 - n, by omega⟩ := by
  simp [hornerPrefix, hn]

theorem hornerPrefix_eq_sum {t k : ℕ}
    (c_field : Fin k → TrinomialField t) (x_field : TrinomialField t) :
    ∀ (n : ℕ) (hn : n ≤ k),
      hornerPrefix t k c_field x_field n =
        ∑ i : Fin n,
          c_field ⟨k - 1 - i.val, by have := i.isLt; omega⟩ * x_field ^ (n - 1 - i.val)
  | 0, _ => by simp [hornerPrefix]
  | n + 1, hn => by
    rw [hornerPrefix_succ_of_lt (Nat.lt_of_succ_le hn), hornerPrefix_eq_sum c_field x_field n
      (Nat.le_of_succ_le hn), Fin.sum_univ_castSucc, Finset.sum_mul]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    refine congrArg (· + _) (Finset.sum_congr rfl fun i _ => ?_)
    rw [show n - i.val = (n - 1 - i.val) + 1 by omega, pow_succ, mul_assoc]

theorem hornerPrefix_self_eq_polynomialHash {t k : ℕ}
    (c_field : Fin k → TrinomialField t) (x_field : TrinomialField t) :
    hornerPrefix t k c_field x_field k = polynomialHash c_field x_field := by
  rw [hornerPrefix_eq_sum c_field x_field k le_rfl]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  have hrev : k - 1 - i.val = (Fin.revPerm i).val := by
    rw [Fin.revPerm_apply, Fin.val_rev]; omega
  rw [show (⟨k - 1 - i.val, _⟩ : Fin k) = Fin.revPerm i from Fin.ext hrev, hrev]

end Cslib.Probability
