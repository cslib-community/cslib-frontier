/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Perm.Basic
import CslibFrontier.Foundations.Data.List.Blocks

/-!
# Bin packing

An instance of bin packing is a list `l : List ℕ` of item sizes and a bin capacity `C : ℕ`. A
packing (`Cslib.Algorithms.Lean.BinPacking.IsPacking`) is a list of bins, each a list of items,
that together hold exactly the items of `l`, counted with multiplicity, and each hold at most `C`.
The number of bins is the length of the packing, and an optimal packing minimizes it. This is the
problem of [Williamson and Shmoys, Section 3.3][WilliamsonShmoys2011] with the sizes `aᵢ ∈ (0, 1]`
scaled to integers `aᵢ ≤ C`.

Every packing uses at least `l.sum / C` bins (`IsPacking.sum_le_mul_length`). Next Fit and First
Fit both return packings in which every two consecutive bins are *jointly overfull*: their
contents do not fit together into one bin. Pairing consecutive bins, such a packing with `m` bins
holds more than `C * ⌊m / 2⌋` (`add_one_mul_div_two_le_of_isChain`), so it uses fewer than twice as
many bins as any packing of the same items (`length_lt_two_mul_of_isChain`).

## Main definitions

* `Cslib.Algorithms.Lean.BinPacking.IsPacking`: packings of a list of items into bins of a given
  capacity.

## Main results

* `Cslib.Algorithms.Lean.BinPacking.IsPacking.sum_le_mul_length`: the volume bound.
* `Cslib.Algorithms.Lean.BinPacking.IsPacking.sum_map_le_mul_length`: the volume bound for a
  weight bounded on every bin.
* `Cslib.Algorithms.Lean.BinPacking.IsPacking.count_le_mul_length`: the counting bound for an item
  of which every bin holds a bounded number of copies.
* `Cslib.Algorithms.Lean.BinPacking.exists_isPacking_iff`: a packing exists exactly when every
  item fits into a bin.
* `Cslib.Algorithms.Lean.BinPacking.length_lt_two_mul_of_isChain`: a packing whose consecutive
  bins are jointly overfull uses fewer than twice as many bins as any packing.

## References

* [D. P. Williamson, D. B. Shmoys, *The Design of Approximation Algorithms*][WilliamsonShmoys2011]
-/

public section

namespace Cslib.Algorithms.Lean.BinPacking

open scoped List

/-- `bins` packs the items `l` into bins of capacity `C`: together the bins hold exactly the items
of `l`, counted with multiplicity, and each bin holds at most `C`. -/
structure IsPacking (C : ℕ) (l : List ℕ) (bins : List (List ℕ)) : Prop where
  /-- The bins hold exactly the items. -/
  perm : bins.flatten ~ l
  /-- Every bin holds at most `C`. -/
  sum_le : ∀ b ∈ bins, b.sum ≤ C

namespace IsPacking

variable {C : ℕ} {l : List ℕ} {bins : List (List ℕ)}

/-- The items' total size is the sum of the bins' loads. -/
theorem sum_eq (h : IsPacking C l bins) : l.sum = (bins.map List.sum).sum := by
  rw [← h.perm.sum_eq, List.sum_flatten]

/-- The total weight of the items is the sum of the weights of the bins. -/
theorem sum_map_eq {M : Type*} [AddCommMonoid M] (h : IsPacking C l bins) (f : ℕ → M) :
    (l.map f).sum = (bins.map fun b => (b.map f).sum).sum := by
  rw [← (h.perm.map f).sum_eq, ← List.flatMap_id', List.sum_map_flatMap]

/-- **Volume bound**: the items' total size is at most `C` times the number of bins. -/
theorem sum_le_mul_length (h : IsPacking C l bins) : l.sum ≤ C * bins.length := by
  rw [h.sum_eq, Nat.mul_comm]
  simpa using List.sum_le_length_nsmul (bins.map List.sum) C (by simpa using h.sum_le)

/-- **Weighted volume bound**: if every list of items of total size at most `C` has total weight
at most `K` under a weight `f`, then the items of a packing have total weight at most `K` times
the number of bins. -/
theorem sum_map_le_mul_length (h : IsPacking C l bins) (f : ℕ → ℕ) {K : ℕ}
    (hK : ∀ b : List ℕ, b.sum ≤ C → (b.map f).sum ≤ K) :
    (l.map f).sum ≤ K * bins.length := by
  rw [h.sum_map_eq f, Nat.mul_comm]
  simpa using
    List.sum_le_length_nsmul (bins.map fun b => (b.map f).sum) K
      (List.forall_mem_map.mpr fun b hb => hK b (h.sum_le b hb))

/-- **Counting bound**: if every list of items of total size at most `C` holds at most `k` copies
of an item `x`, then a packing holds at most `k` copies of `x` per bin. -/
theorem count_le_mul_length (h : IsPacking C l bins) (x : ℕ) {k : ℕ}
    (hk : ∀ b : List ℕ, b.sum ≤ C → b.count x ≤ k) :
    l.count x ≤ k * bins.length := by
  rw [← h.perm.count_eq, List.count_flatten, Nat.mul_comm]
  simpa using List.sum_le_length_nsmul (bins.map (List.count x)) k fun y hy => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
    exact hk b (h.sum_le b hb)

/-- Every packed item fits into a bin. -/
theorem le_of_mem (h : IsPacking C l bins) {a : ℕ} (ha : a ∈ l) : a ≤ C := by
  obtain ⟨b, hb, hab⟩ := List.mem_flatten.1 (h.perm.mem_iff.2 ha)
  exact (List.le_sum_of_mem hab).trans (h.sum_le b hb)

/-- A packing of a nonempty list has a bin. -/
theorem ne_nil (h : IsPacking C l bins) (hl : l ≠ []) : bins ≠ [] := by
  rintro rfl
  exact hl (List.Perm.nil_eq h.perm).symm

end IsPacking

/-- One bin for each item packs a list of items exactly when every item fits into a bin. -/
theorem isPacking_map_singleton {C : ℕ} {l : List ℕ} (hl : ∀ a ∈ l, a ≤ C) :
    IsPacking C l (l.map fun a => [a]) :=
  ⟨by rw [← List.flatMap_def, List.flatMap_singleton'], by simpa using hl⟩

/-- A packing exists exactly when every item fits into a bin. -/
theorem exists_isPacking_iff {C : ℕ} {l : List ℕ} :
    (∃ bins, IsPacking C l bins) ↔ ∀ a ∈ l, a ≤ C :=
  ⟨fun ⟨_, h⟩ _ ha => h.le_of_mem ha, fun hl => ⟨_, isPacking_map_singleton hl⟩⟩

/-- Pairing consecutive bins: if every two consecutive bins are jointly overfull, then the bins
hold more than `C` for each pair, so `(C + 1) * ⌊m / 2⌋` is at most their total load. -/
theorem add_one_mul_div_two_le_of_isChain {C : ℕ} :
    ∀ {bins : List (List ℕ)}, bins.IsChain (fun b b' => C < b.sum + b'.sum) →
      (C + 1) * (bins.length / 2) ≤ (bins.map List.sum).sum
  | [], _ => by simp
  | [_], _ => by simp
  | b :: b' :: rest, h => by
    rw [List.isChain_cons_cons] at h
    have ih := add_one_mul_div_two_le_of_isChain (bins := rest) h.2.tail
    have h1 : C + 1 ≤ b.sum + b'.sum := h.1
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have hdiv : (rest.length + 1 + 1) / 2 = rest.length / 2 + 1 := by omega
    rw [hdiv, Nat.mul_succ]
    omega

/-- A packing of a nonempty list whose consecutive bins are jointly overfull uses fewer than twice
as many bins as any packing of the same items, that is at most `2 * OPT - 1` bins. -/
theorem length_lt_two_mul_of_isChain {C : ℕ} {l : List ℕ} {bins Q : List (List ℕ)}
    (hperm : bins.flatten ~ l) (hchain : bins.IsChain (fun b b' => C < b.sum + b'.sum))
    (hQ : IsPacking C l Q) (hl : l ≠ []) : bins.length < 2 * Q.length := by
  have h1 := add_one_mul_div_two_le_of_isChain hchain
  have h2 := hQ.sum_le_mul_length
  rw [← hperm.sum_eq, List.sum_flatten] at h2
  have hQ0 := List.length_pos_iff.2 (hQ.ne_nil hl)
  have : bins.length / 2 < Q.length := by
    by_contra hcon
    have h5 := Nat.mul_le_mul_left (C + 1) (Nat.le_of_not_lt hcon)
    rw [Nat.succ_mul] at h5; omega
  omega

end Cslib.Algorithms.Lean.BinPacking
