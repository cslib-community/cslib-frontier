/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BPlusTree.Basic
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring

/-!
# Height bounds for B+-trees

The height of a well-formed B+-tree is logarithmic in its size. Every entry is in a leaf, so the
count is of leaves: a balanced subtree of height `h` all of whose nodes are occupied has at
least `t ^ (h - 1)` leaves, each holding at least `t - 1` entries. The root of a well-formed tree
of height at least `2` has at least two children, which gives `2 * (t - 1) * t ^ (h - 2)`
entries, and that is at least `t ^ (h - 1)` because `2 ≤ t`.

`height` counts the nodes on a root-to-leaf path, so a leaf has height `1` and the bound is
`height ≤ Nat.log t size + 1`. The empty tree is the empty leaf, of height `1` and size `0`, and
satisfies it. The lower bound on the size needs height at least `2`: a root leaf may hold any
number of entries up to `2 * t - 1`, including none.

## Main results

* `BPlusTree.Occupied.mul_pow_le_size`: a balanced occupied subtree of height `h` holds at least
  `(t - 1) * t ^ (h - 1)` entries.
* `BPlusTree.Balanced.pow_le_size`, `BPlusTree.Balanced.height_le_log`: the two bounds below from
  the shape alone, with no hypothesis on the keys.
* `BPlusTree.IsWF.pow_le_size`: a well-formed tree of height `h ≥ 2` holds at least `t ^ (h - 1)`
  entries.
* `BPlusTree.IsWF.height_le_log`: the height of a well-formed tree is at most
  `Nat.log t size + 1`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]. Theorem 18.1 there is the corresponding bound for classic B-trees; the
  statements here are its counterparts for B+-trees and are not taken from a source.
-/

public section

namespace Cslib.DataStructure.BPlusTree

variable {α : Type*} {β : Type*} {t : ℕ} {tr : BPlusTree α β}

/-- A node whose children each hold at least `n` entries holds at least `n` for each child. -/
theorem le_size_node {first : BPlusTree α β} {rest : List (Branch α β)} {n : ℕ}
    (h₁ : n ≤ first.size) (h₂ : ∀ e ∈ rest, n ≤ e.child.size) :
    (rest.length + 1) * n ≤ (node first rest).size := by
  have hs :=
    (rest.map fun e => e.child.size).length_nsmul_le_sum n (List.forall_mem_map.2 h₂)
  rw [List.length_map, Nat.nsmul_eq_mul] at hs
  rw [size_node, Nat.add_mul, Nat.one_mul]
  omega

/-- A balanced occupied subtree of height `h` holds at least `(t - 1) * t ^ (h - 1)` entries: it
has at least `t ^ (h - 1)` leaves, each with at least `t - 1` entries. -/
theorem Occupied.mul_pow_le_size (ho : Occupied t tr) (hb : Balanced tr) :
    (t - 1) * t ^ (tr.height - 1) ≤ tr.size := by
  induction tr with
  | leaf entries => simpa using ho.le_width
  | node first rest ih₁ ih₂ =>
    have hc : ∀ e : Branch α β, e ∈ rest → (t - 1) * t ^ (first.height - 1) ≤ e.child.size :=
      fun e he => hb.height_of_mem_rest he ▸ ih₂ e he (ho.of_mem_rest he) (hb.of_mem_rest he)
    refine le_trans ?_ (le_size_node (ih₁ ho.first hb.first) hc)
    obtain ⟨m, hm⟩ : ∃ m, first.height = m + 1 :=
      ⟨first.height - 1, by have := height_pos (tr := first); omega⟩
    have hl : t ≤ rest.length + 1 := by
      have := ho.le_width
      rw [width_node] at this
      omega
    rw [hb.height_node, hm, Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.pow_succ]
    calc (t - 1) * (t ^ m * t) = t * ((t - 1) * t ^ m) := by ring
      _ ≤ (rest.length + 1) * ((t - 1) * t ^ m) := Nat.mul_le_mul_right _ hl

/-- At a minimum degree of at least `2`, a balanced tree of height `h ≥ 2` whose root has a
separator and whose children are occupied holds at least `t ^ (h - 1)` entries: the bound depends
on the shape only, not on the keys. -/
theorem Balanced.pow_le_size (hb : Balanced tr) (ht : 2 ≤ t)
    (hw : (∀ entries, tr ≠ .leaf entries) → 1 ≤ tr.width)
    (ho : ∀ c ∈ tr.children, Occupied t c) (h2 : 2 ≤ tr.height) :
    t ^ (tr.height - 1) ≤ tr.size := by
  cases tr with
  | leaf entries => simp at h2
  | node first rest =>
    have hw : 1 ≤ rest.length := hw nofun
    have hf := (ho first List.mem_cons_self).mul_pow_le_size hb.first
    have hc : ∀ e : Branch α β, e ∈ rest → (t - 1) * t ^ (first.height - 1) ≤ e.child.size :=
      fun e he => hb.height_of_mem_rest he ▸
        (ho _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he))).mul_pow_le_size
          (hb.of_mem_rest he)
    refine le_trans ?_ (le_size_node hf hc)
    obtain ⟨m, hm⟩ : ∃ m, first.height = m + 1 :=
      ⟨first.height - 1, by have := height_pos (tr := first); omega⟩
    rw [hb.height_node, hm, Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.pow_succ]
    calc t ^ m * t = t * t ^ m := Nat.mul_comm _ _
      _ ≤ 2 * (t - 1) * t ^ m := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * ((t - 1) * t ^ m) := Nat.mul_assoc _ _ _
      _ ≤ (rest.length + 1) * ((t - 1) * t ^ m) := Nat.mul_le_mul_right _ (by omega)

/-- At a minimum degree of at least `2`, the height of a balanced tree whose root has a separator
and whose children are occupied is logarithmic in its size: the bound depends on the shape only,
not on the keys. -/
theorem Balanced.height_le_log (hb : Balanced tr) (ht : 2 ≤ t)
    (hw : (∀ entries, tr ≠ .leaf entries) → 1 ≤ tr.width)
    (ho : ∀ c ∈ tr.children, Occupied t c) : tr.height ≤ Nat.log t tr.size + 1 := by
  rcases Nat.lt_or_ge tr.height 2 with h1 | h2
  · omega
  · have := Nat.le_log_of_pow_le (by omega) (hb.pow_le_size ht hw ho h2)
    omega

variable [LinearOrder α]

/-- A well-formed tree of height `h ≥ 2` holds at least `t ^ (h - 1)` entries. -/
theorem IsWF.pow_le_size (h : IsWF t tr) (h2 : 2 ≤ tr.height) :
    t ^ (tr.height - 1) ≤ tr.size :=
  h.balanced.pow_le_size h.two_le h.width_pos h.occupied_of_mem_children h2

/-- The height of a well-formed tree is logarithmic in its size. -/
theorem IsWF.height_le_log (h : IsWF t tr) : tr.height ≤ Nat.log t tr.size + 1 :=
  h.balanced.height_le_log h.two_le h.width_pos h.occupied_of_mem_children

end Cslib.DataStructure.BPlusTree
