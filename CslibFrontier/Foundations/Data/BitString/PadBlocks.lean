/-
Copyright (c) 2026 Karn Seth, Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Aviv Bar Natan
-/
module
-- upstream: candidate
public import CslibFrontier.Foundations.Data.BitString.List
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
/-!
# Fixed-width blocks of a padded bit list

`BitString.padBlocks n L x` reads the bit list `x` as `L / n` consecutive blocks of `n` bits, block
`i` being `BitString.listBlock n x i` padded with `false` past the end of `x`. Only the first
`(L / n) * n` positions take part: the block count is the floor `L / n`, so when `n ∤ L` the last
`L % n` positions below `L` are dropped, and bits of `x` at positions `≥ (L / n) * n` are ignored.
The reading is exact (`padBlocks_getElem_apply` reads every bit of `x`) when `n ∣ L` and
`x.length ≤ L`.

`BitString.toBlocks n x` is the case `L = x.length`: the consecutive blocks of `n` bits of `x`,
without an incomplete last block. A list made of whole blocks is the concatenation of its blocks
(`flatMap_ofFn_toBlocks`), so cutting is injective on such lists (`toBlocks_injOn`).

## Main definitions

* `Cslib.BitString.padBlocks`: the first `L / n` padded width-`n` blocks of a bit list.
* `Cslib.BitString.toBlocks`: the blocks of `n` bits of a bit list.

## Main results

* `Cslib.BitString.length_padBlocks`: there are exactly `L / n` blocks.
* `Cslib.BitString.padBlocks_getElem_apply`: bit `j` of block `i` is bit `i * n + j` of the list,
  or `false` past its end.
* `Cslib.BitString.listRows_eq_map_ofFn_padBlocks`: `listRows (L / n) n x` is the word view of
  `padBlocks n L x`.
* `Cslib.BitString.flatMap_ofFn_toBlocks`: a list of whole blocks is the concatenation of its
  blocks.
* `Cslib.BitString.toBlocks_injOn`, `Cslib.BitString.toBlocks_append`,
  `Cslib.BitString.toBlocks_ofFn`: cutting is injective on lists of whole blocks and commutes
  with appending after whole blocks.
-/
@[expose] public section
namespace Cslib.BitString
/-- The first `L / n` blocks of `n` bits of the bit list `x`: block `i` is `listBlock n x i`,
  padded with `false` past the end of `x`. The block count is the floor `L / n`, so positions
  `≥ (L / n) * n` are dropped; the reading is exact when `n ∣ L` and `x.length ≤ L`. -/
def padBlocks (n L : ℕ) (x : List Bool) : List (BitString n) :=
  List.ofFn fun i : Fin (L / n) => fun j : Fin n => (listBlock n x i).getD j false
/-- `padBlocks n L x` has `L / n` blocks, whatever the length of `x`. -/
@[simp] theorem length_padBlocks (n L : ℕ) (x : List Bool) : (padBlocks n L x).length = L / n := by
  simp [padBlocks]
/-- Bit `j` of block `i` of `padBlocks n L x` is bit `i * n + j` of `x`, or `false` past its end. -/
theorem padBlocks_getElem_apply (n L : ℕ) (x : List Bool) (i : ℕ) (hi : i < L / n) (j : Fin n) :
    ((padBlocks n L x)[i]'(by simpa using hi)) j = x.getD (i * n + j) false := by
  have h : ∀ (l : List (BitString n)) (_ : l = padBlocks n L x) (h' : i < l.length),
      l[i] j = x.getD (i * n + j) false := by
    rintro _ rfl h'
    unfold padBlocks at h' ⊢
    rw [List.getElem_ofFn]
    simp only [listBlock, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt j.isLt,
      List.getElem?_drop]
  exact h _ rfl _
/-- The consecutive blocks of `n` bits of a bit list, without an incomplete last block:
`padBlocks` with the length of the list itself as the bound. -/
def toBlocks (n : ℕ) (x : List Bool) : List (BitString n) := padBlocks n x.length x
@[simp] theorem length_toBlocks (n : ℕ) (x : List Bool) : (toBlocks n x).length = x.length / n :=
  length_padBlocks n x.length x
theorem getElem?_toBlocks (n : ℕ) (x : List Bool) (i : ℕ) :
    (toBlocks n x)[i]? =
      if i < x.length / n then some (fun j : Fin n => x.getD (i * n + j) false) else none := by
  split_ifs with hi
  · rw [List.getElem?_eq_getElem (by simpa using hi)]
    exact congrArg some (funext fun j => padBlocks_getElem_apply n x.length x i hi j)
  · exact List.getElem?_eq_none (by simpa using hi)
/-- The blocks of a list, read position by position. -/
theorem toBlocks_eq_map_range (n : ℕ) (x : List Bool) :
    toBlocks n x =
      (List.range (x.length / n)).map fun i => (fun j : Fin n => x.getD (i * n + j) false) :=
  List.ext_getElem? fun i => by
    rw [getElem?_toBlocks]
    by_cases hi : i < x.length / n <;> simp [hi]
/-- A list made of whole `n`-bit blocks is the concatenation of its blocks. -/
theorem flatMap_ofFn_toBlocks {n : ℕ} {x : List Bool} (hx : n ∣ x.length) :
    (toBlocks n x).flatMap List.ofFn = x := by
  have hblocks : toBlocks n x =
      List.ofFn (block (fun p : Fin (x.length / n * n) => x.getD p false)) := by
    unfold toBlocks
    refine List.ext_getElem (by simp) fun i h₁ _ => funext fun j => ?_
    rw [padBlocks_getElem_apply n x.length x i (by simpa using h₁), List.getElem_ofFn, block_apply]
    simp only [finProdFinEquiv_apply_val, Nat.add_comm, Nat.mul_comm]
  rw [hblocks, List.flatMap_def, List.map_ofFn, Function.comp_def, ← ofFn_blocksEquiv_symm,
    blocksEquiv_symm_block]
  refine List.ext_getElem (by simp [Nat.div_mul_cancel hx]) fun p _ h₂ => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
/-- `listRows (L / n) n x` is the word view of `padBlocks n L x`. -/
theorem listRows_eq_map_ofFn_padBlocks (n L : ℕ) (x : List Bool) :
    listRows (L / n) n x = (padBlocks n L x).map List.ofFn := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  refine List.ext_getElem (by simp [listRows]) fun j hj₁ hj₂ => ?_
  simp only [listRows, List.getElem_map, List.getElem_range]
  rw [getElem_listRow (by simpa using hj₂), List.getElem_ofFn,
    padBlocks_getElem_apply n L x i (by simpa using h₁) ⟨j, by simpa using hj₂⟩]
/-- The rows of a list are the word view of its blocks. -/
theorem listRows_eq_map_ofFn_toBlocks (n : ℕ) (x : List Bool) :
    listRows (x.length / n) n x = (toBlocks n x).map List.ofFn :=
  listRows_eq_map_ofFn_padBlocks n x.length x
/-- Cutting is injective on lists whose lengths are multiples of `n`. -/
theorem toBlocks_injOn {n : ℕ} {x y : List Bool} (hx : n ∣ x.length) (hy : n ∣ y.length)
    (h : toBlocks n x = toBlocks n y) : x = y := by
  rw [← flatMap_ofFn_toBlocks hx, ← flatMap_ofFn_toBlocks hy, h]
theorem toBlocks_append {n : ℕ} {a : List Bool} (ha : n ∣ a.length) (b : List Bool) :
    toBlocks n (a ++ b) = toBlocks n a ++ toBlocks n b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 (x : List Bool) : toBlocks 0 x = [] := List.eq_nil_of_length_eq_zero (by simp)
    rw [h0, h0, h0, List.append_nil]
  obtain ⟨k, hk⟩ := ha
  have hka : (toBlocks n a).length = k := by simp [hk, Nat.mul_div_cancel_left _ hn]
  refine List.ext_getElem? fun j => ?_
  rcases Nat.lt_or_ge j k with hj | hj
  · rw [List.getElem?_append_left (hka ▸ hj), getElem?_toBlocks, getElem?_toBlocks,
      List.length_append, hk, Nat.mul_add_div hn, Nat.mul_div_cancel_left _ hn]
    simp only [Nat.lt_add_right _ hj, hj, ↓reduceIte, Option.some.injEq]
    exact funext fun i => List.getD_append _ _ _ _
      (by rw [hk]; nlinarith [i.isLt, Nat.mul_le_mul_right n (show j + 1 ≤ k from hj)])
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [List.getElem?_append_right (hka ▸ hj), hka, Nat.add_sub_cancel_left,
      getElem?_toBlocks, getElem?_toBlocks, List.length_append, hk, Nat.mul_add_div hn]
    simp only [Nat.add_lt_add_iff_left]
    split_ifs
    · congr 1 with i : 1
      rw [List.getD_append_right a b false ((k + d) * n + i) (by rw [hk]; nlinarith), hk,
        show (k + d) * n + i - n * k = d * n + i by
          rw [add_mul, mul_comm k n, Nat.add_assoc, Nat.add_sub_cancel_left]]
    · rfl
@[simp]
theorem toBlocks_ofFn {n : ℕ} (hn : 0 < n) (m : BitString n) :
    toBlocks n (List.ofFn m) = [m] := by
  refine List.ext_getElem? fun j => ?_
  rw [getElem?_toBlocks, List.length_ofFn, Nat.div_self hn]
  rcases j with _ | j
  · simp only [Nat.zero_lt_one, ↓reduceIte, zero_mul, zero_add, List.getElem?_cons_zero,
      Option.some.injEq]
    funext i
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  · simp
end Cslib.BitString
