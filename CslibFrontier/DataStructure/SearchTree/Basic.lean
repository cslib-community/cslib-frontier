/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Tree.Basic
public import CslibFrontier.DataStructure.OrderedSet.Basic

/-!
# Unbalanced binary search trees

An ordinary binary search tree reuses Mathlib's `BinaryTree`. Keys strictly smaller than the
root occur on the left, larger keys on the right. Inserting a duplicate leaves the tree unchanged.
These are the textbook search and insertion algorithms of [Cormen et al., Chapter 12][CLRS2009].

## Main definitions

* `elements`: the finite set represented by a tree.
* `Ordered`: the strict binary-search-tree invariant.
* `contains`, `insert`, `minimum`, `successor`: executable search-tree operations.

## Main results

* `contains_eq_true`: membership is exactly finite-set membership.
* `elements_insert`, `ordered_insert`: insertion has set semantics and preserves the invariant.
* `minimum_spec`, `successor_spec`: queries return the least eligible key, or `none`.

Trees are not balanced. Cost bounds in the companion module depend on their actual height.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*, Chapter 12][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.SearchTree

open Cslib.DataStructure.OrderedSet

variable {α : Type*} [LinearOrder α]

/-- The finite set of keys stored at internal nodes. -/
def elements : BinaryTree α → Finset α
  | .nil => ∅
  | .node a l r => insert a (elements l ∪ elements r)

/-- Strict subtree separation rules out duplicate keys. -/
def Ordered : BinaryTree α → Prop
  | .nil => True
  | .node a l r => Ordered l ∧ Ordered r ∧
      (∀ x ∈ elements l, x < a) ∧ (∀ x ∈ elements r, a < x)

/-- Follow a single search path; no subtree is scanned. -/
def contains (x : α) : BinaryTree α → Bool
  | .nil => false
  | .node a l r => if x < a then contains x l else if a < x then contains x r else true

/-- Insert at the first empty child on the search path; equality preserves the existing node. -/
def insert (x : α) : BinaryTree α → BinaryTree α
  | .nil => .node x .nil .nil
  | .node a l r =>
      if x < a then .node a (insert x l) r
      else if a < x then .node a l (insert x r) else .node a l r

/-- Follow left children to find the least key. -/
def minimum : BinaryTree α → Option α
  | .nil => none
  | .node a l _ => (minimum l).or (some a)

/-- The least stored key strictly greater than `x`, including when `x` is absent. -/
def successor (x : α) : BinaryTree α → Option α
  | .nil => none
  | .node a l r => if x < a then (successor x l).or (some a) else successor x r

/-- Membership in a node's element set splits across the root key and the two subtrees. -/
@[simp] theorem mem_elements_node {x a : α} {l r : BinaryTree α} :
    x ∈ elements (.node a l r) ↔ x = a ∨ x ∈ elements l ∨ x ∈ elements r := by
  simp [elements]

/-- The two subtrees of an ordered node store disjoint key sets. -/
theorem Ordered.disjoint_elements {a : α} {l r : BinaryTree α} (h : Ordered (.node a l r)) :
    Disjoint (elements l) (elements r) :=
  Finset.disjoint_left.mpr fun x hxl hxr => lt_asymm (h.2.2.1 x hxl) (h.2.2.2 x hxr)

/-- The root key of an ordered node is stored in neither subtree. -/
theorem Ordered.notMem_elements_union {a : α} {l r : BinaryTree α} (h : Ordered (.node a l r)) :
    a ∉ elements l ∪ elements r := fun ha =>
  (Finset.mem_union.mp ha).elim (fun hl => lt_irrefl a (h.2.2.1 a hl))
    fun hr => lt_irrefl a (h.2.2.2 a hr)

private theorem mem_node_iff_left {a x : α} {l r : BinaryTree α} (ht : Ordered (.node a l r))
    (hx : x < a) : x ∈ elements (.node a l r) ↔ x ∈ elements l := by
  rw [mem_elements_node]
  exact ⟨fun h => h.elim (fun h => (ne_of_lt hx h).elim)
    (·.resolve_right fun h => lt_asymm hx (ht.2.2.2 x h)), fun h => Or.inr (Or.inl h)⟩

private theorem mem_node_iff_right {a x : α} {l r : BinaryTree α} (ht : Ordered (.node a l r))
    (hx : a < x) : x ∈ elements (.node a l r) ↔ x ∈ elements r := by
  rw [mem_elements_node]
  exact ⟨fun h => h.elim (fun h => (ne_of_gt hx h).elim)
    (·.resolve_left fun h => lt_asymm hx (ht.2.2.1 x h)), fun h => Or.inr (Or.inr h)⟩

/-- Search is correct for any shape satisfying the invariant. -/
theorem contains_eq_true {t : BinaryTree α} (ht : Ordered t) (x : α) :
    contains x t = true ↔ x ∈ elements t := by
  fun_induction contains x t with
  | case1 => simp [elements] -- nil
  | case2 a l r hx il => rw [il ht.1, mem_node_iff_left ht hx] -- x < a: search l
  | case3 a l r _ ha ir => rw [ir ht.2.1, mem_node_iff_right ht ha] -- a < x: search r
  | case4 a l r hx ha => simp [le_antisymm (le_of_not_gt ha) (le_of_not_gt hx)] -- x = a

/-- Insertion adds exactly the requested key, even when it was already present. -/
theorem elements_insert (x : α) (t : BinaryTree α) :
    elements (insert x t) = Insert.insert x (elements t) := by
  fun_induction insert x t with
  | case1 => simp [elements] -- nil
  | case2 _ _ _ _ ih | case3 _ _ _ _ _ ih => -- x < a: insert into l; a < x: into r
    ext y
    simp [elements, ih, or_left_comm]
  -- x = a
  | case4 a l r hx ha => simp [elements, le_antisymm (le_of_not_gt ha) (le_of_not_gt hx)]

/-- The binary-search-tree invariant survives insertion. -/
theorem ordered_insert {t : BinaryTree α} (ht : Ordered t) (x : α) :
    Ordered (insert x t) := by
  induction t with
  | nil => simp [insert, Ordered, elements]
  | node a l r il ir =>
    obtain ⟨hl, hr, hla, har⟩ := ht
    simp only [insert]
    split <;> rename_i hx
    · refine ⟨il hl, hr, fun y hy => ?_, har⟩
      rw [elements_insert, Finset.mem_insert] at hy
      exact hy.elim (· ▸ hx) (hla y)
    · split <;> rename_i ha
      · refine ⟨hl, ir hr, hla, fun y hy => ?_⟩
        rw [elements_insert, Finset.mem_insert] at hy
        exact hy.elim (· ▸ ha) (har y)
      · exact ⟨hl, hr, hla, har⟩

/-- Re-inserting a present key preserves the entire tree, not just its represented set. -/
theorem insert_eq_self {t : BinaryTree α} (ht : Ordered t) {x : α}
    (hx : x ∈ elements t) : insert x t = t := by
  fun_induction insert x t with
  | case1 => simp [elements] at hx -- nil
  | case2 a l r hxa il => rw [il ht.1 ((mem_node_iff_left ht hxa).mp hx)] -- x < a: insert into l
  | case3 a l r _ hax ir => rw [ir ht.2.1 ((mem_node_iff_right ht hax).mp hx)] -- a < x: into r
  | case4 => rfl -- x = a

/-- A strict search tree stores each represented key in exactly one node. -/
theorem card_elements {t : BinaryTree α} (ht : Ordered t) :
    (elements t).card = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r il ir =>
    simp only [elements, Finset.card_insert_of_notMem ht.notMem_elements_union,
      Finset.card_union_of_disjoint ht.disjoint_elements, il ht.1, ir ht.2.1, BinaryTree.numNodes]

/-- Left descent returns the least element, with the empty case accounted for. -/
theorem minimum_spec {t : BinaryTree α} (ht : Ordered t) :
    LeastResult (elements t) (minimum t) := by
  induction t with
  | nil => rfl
  | node a l r il _ =>
    obtain ⟨hl, _, hla, har⟩ := ht
    have ih := il hl
    cases he : minimum l with
    | none =>
      simp only [he, LeastResult] at ih
      simp only [minimum, he, Option.or, LeastResult]
      refine ⟨by simp, ?_⟩
      intro b hb
      rcases mem_elements_node.mp hb with rfl | hb | hb
      · exact le_rfl
      · simp [ih] at hb
      · exact (har b hb).le
    | some b =>
      simp only [he, LeastResult] at ih
      simp only [minimum, he, Option.or, LeastResult]
      refine ⟨by simp [ih.1], ?_⟩
      intro c hc
      rcases mem_elements_node.mp hc with rfl | hc | hc
      · exact (hla b ih.1).le
      · exact ih.2 c hc
      · exact (lt_trans (hla b ih.1) (har c hc)).le

/-- Successor is strict and does not require the query itself to belong to the tree. -/
theorem successor_spec {t : BinaryTree α} (ht : Ordered t) (x : α) :
    LeastResult ((elements t).filter (x < ·)) (successor x t) := by
  induction t with
  | nil => rfl
  | node a l r il ir =>
    obtain ⟨hl, hr, hla, har⟩ := ht
    simp only [successor]
    split <;> rename_i hx
    · have ih := il hl
      cases he : successor x l with
      | none =>
        simp only [he, LeastResult] at ih
        simp only [Option.or, LeastResult]
        refine ⟨by simp [hx], ?_⟩
        intro b hb
        obtain ⟨hb, hxb⟩ := Finset.mem_filter.mp hb
        rcases mem_elements_node.mp hb with rfl | hb | hb
        · exact le_rfl
        · have : b ∈ (elements l).filter (x < ·) := Finset.mem_filter.mpr ⟨hb, hxb⟩
          simp [ih] at this
        · exact (har b hb).le
      | some b =>
        simp only [he, LeastResult] at ih
        simp only [Option.or, LeastResult]
        obtain ⟨hbl, hxb⟩ := Finset.mem_filter.mp ih.1
        refine ⟨by simp [hbl, hxb], ?_⟩
        intro c hc
        obtain ⟨hc, hxc⟩ := Finset.mem_filter.mp hc
        rcases mem_elements_node.mp hc with rfl | hc | hc
        · exact (hla b hbl).le
        · exact ih.2 c (Finset.mem_filter.mpr ⟨hc, hxc⟩)
        · exact (lt_trans (hla b hbl) (har c hc)).le
    · have he : (elements (.node a l r)).filter (x < ·) = (elements r).filter (x < ·) :=
        Finset.ext fun b => by
          simp only [Finset.mem_filter]
          exact and_congr_left fun hxb =>
            mem_node_iff_right ⟨hl, hr, hla, har⟩ ((not_lt.mp hx).trans_lt hxb)
      rw [he]
      exact ir hr

end Cslib.DataStructure.SearchTree
