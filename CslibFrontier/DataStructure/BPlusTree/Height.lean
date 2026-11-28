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
* `BPlusTree.le_mul_height_add_of_scan`: a count on trees that spends at most one unit per
  separator at each interior node of a descent, and at most one per entry and `c` more in the
  leaf, is at most `(2 * t - 1) * height + c`.

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
    refine le_trans ?_ (le_size_node (ih₁ ho.first hb.first) fun e he =>
      hb.height_of_mem_rest he ▸ ih₂ e he (ho.of_mem_rest he) (hb.of_mem_rest he))
    obtain ⟨m, hm⟩ : ∃ m, first.height = m + 1 :=
      ⟨first.height - 1, by have := height_pos (tr := first); omega⟩
    rw [hb.height_node, hm, Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.pow_succ]
    calc (t - 1) * (t ^ m * t) = t * ((t - 1) * t ^ m) := by ring
      _ ≤ (rest.length + 1) * ((t - 1) * t ^ m) :=
        Nat.mul_le_mul_right _ (by simpa only [width_node, Nat.sub_le_iff_le_add] using ho.le_width)

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
    refine le_trans ?_ (le_size_node ((ho first List.mem_cons_self).mul_pow_le_size hb.first)
      fun e he => hb.height_of_mem_rest he ▸
        (ho _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he))).mul_pow_le_size
          (hb.of_mem_rest he))
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

/-- A count that spends at most one unit per entry and `c` more in a leaf, and at most one unit
per separator at a node beyond what it spends in one of the node's children, is at most
`(2 * t - 1) * height + c` on a tree whose root has width at most `2 * t - 1` and whose children
are occupied. -/
theorem le_mul_height_add_of_scan {c : ℕ} {f : BPlusTree α β → ℕ}
    (hleaf : ∀ entries, f (.leaf entries) ≤ entries.length + c)
    (hnode : ∀ (first : BPlusTree α β) (rest : List (Branch α β)) (B : ℕ),
      (∀ ch ∈ (node first rest).children, f ch ≤ B) → f (node first rest) ≤ rest.length + B)
    {tr : BPlusTree α β} (hw : tr.width ≤ 2 * t - 1) (hc : ∀ ch ∈ tr.children, Occupied t ch) :
    f tr ≤ (2 * t - 1) * tr.height + c := by
  induction tr with
  | leaf entries => simpa using (hleaf entries).trans (Nat.add_le_add_right hw c)
  | node first rest ihf ihr =>
    have ih : ∀ ch ∈ (node first rest).children, ch.width ≤ 2 * t - 1 →
        (∀ d ∈ ch.children, Occupied t d) → f ch ≤ (2 * t - 1) * ch.height + c := by
      simpa only [children_node, List.forall_mem_cons, List.forall_mem_map] using ⟨ihf, ihr⟩
    have hB : ∀ ch ∈ (node first rest).children,
        f ch ≤ (2 * t - 1) * ((node first rest).height - 1) + c := fun ch hch => by
      have ho := hc ch hch
      exact (ih ch hch ho.width_le fun _ hd => ho.of_mem_children hd).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left _
          (Nat.le_sub_of_add_le (height_succ_le_of_mem_children hch))) c)
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (height_pos (tr := node first rest)).ne'
    have := hnode first rest _ hB
    rw [width_node] at hw
    rw [hn, Nat.succ_sub_one] at this
    rw [hn, Nat.mul_succ]
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
