/-
Copyright (c) 2026 Paulo Matos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Matos
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.List.BalancedFold
public import CslibFrontier.Foundations.Data.List.ToChunks

/-!
# Ropes: structure, list model and basic API

A rope is a persistent sequence stored as a binary tree whose leaves hold non-empty chunks of at
most `B` elements and whose internal nodes cache their length and height. This file defines the
raw tree, its three independent well-formedness predicates and the basic API, and proves that
every operation agrees with the `List` model given by `toList`. Balance of bulk construction,
join and split are open objectives of cslib-community/cslib-frontier#3670.

`Rope α` is a plain inductive type with no proof fields, so malformed trees can be written down.
Well-formedness `IsWF B t` is a hypothesis of theorems, never part of the type, and splits into
`CacheCorrect` (cached fields are correct), `Chunked B` (leaves have between `1` and `B`
elements, and internal nodes have non-empty children) and `Balanced` (sibling structural heights
differ by at most one). Lemmas assume only the parts they use. Both `empty` and a leaf have height
`0`, so height counts internal nodes on the longest root-to-leaf path. Different trees can
represent the same list, so there is no structural extensionality.

The operations and predicates are `@[expose]`d so that `decide` and `rfl` evaluate them from
other modules.

## Main definitions

* `Cslib.DataStructure.Rope`: the raw rope tree.
* `Rope.length`, `Rope.height`, `Rope.structuralHeight`, `Rope.leaves`: cached and structural
  size measures.
* `Rope.CacheCorrect`, `Rope.Chunked`, `Rope.Balanced`, `Rope.IsWF`: the well-formedness
  predicates, each decidable.
* `Rope.mkNode`: a node with recomputed caches, eliminating empty children.
* `Rope.toList`, `Rope.get?`, `Rope.map`, `Rope.foldl`, `Rope.foldr`, `Rope.singleton`: the
  list model and the basic operations.
* `Rope.ofList`: bulk construction from the chunks `xs.toChunks (max 1 B)`, combined by
  `List.balancedFold`.

## Main results

* `Rope.length_eq_length_toList`, `Rope.height_eq_structuralHeight`: cached fields agree with
  the model and the structure.
* `Rope.get?_eq_getElem?`, `Rope.toList_map`, `Rope.foldl_eq`, `Rope.foldr_eq`: the operations
  agree with the `List` model. Membership is membership in `toList` (`Rope.mem_toList`).
* `Rope.toList_ofList`, `Rope.cacheCorrect_ofList`, `Rope.chunked_ofList`: bulk construction
  represents its input with correct caches and, for `1 ≤ B`, chunks of between `1` and `B`
  elements.
* `Rope.isWF_map`: mapping preserves well-formedness.
* `Rope.IsWF.left`, `Rope.IsWF.right`: the children of a well-formed node are well-formed.

## References

* [H.-J. Boehm, R. Atkinson and M. Plass, *Ropes: an Alternative to
  Strings*][BoehmAtkinsonPlass1995]
-/

public section

universe u v

namespace Cslib.DataStructure

/-- A raw rope over `α`: the empty rope, a leaf holding a chunk, or an internal node caching its
length and height. Well-formedness is the separate predicate `Rope.IsWF`. -/
inductive Rope (α : Type u) where
  /-- The empty rope. -/
  | empty
  /-- A leaf holding a chunk of elements. -/
  | leaf (xs : List α)
  /-- An internal node with cached length and height. -/
  | node (cachedLength cachedHeight : ℕ) (left right : Rope α)

namespace Rope

/-! ### Structure and well-formedness -/

section Structure

variable {α : Type u}

/-- The number of elements, read from the cache at an internal node. -/
@[expose] def length : Rope α → ℕ
  | .empty => 0
  | .leaf xs => xs.length
  | .node n _ _ _ => n

/-- The height, read from the cache at an internal node; `empty` and leaves have height `0`. -/
@[expose] def height : Rope α → ℕ
  | .empty | .leaf _ => 0
  | .node _ h _ _ => h

/-- The height computed from the structure, ignoring the caches. -/
@[expose] def structuralHeight : Rope α → ℕ
  | .empty | .leaf _ => 0
  | .node _ _ l r => max l.structuralHeight r.structuralHeight + 1

/-- The number of leaves. -/
@[expose] def leaves : Rope α → ℕ
  | .empty => 0
  | .leaf _ => 1
  | .node _ _ l r => l.leaves + r.leaves

/-- Whether the rope is the `empty` constructor. -/
@[expose] def isEmpty : Rope α → Bool
  | .empty => true
  | _ => false

/-- The cached length and height of every internal node are correct. -/
@[expose] def CacheCorrect : Rope α → Prop
  | .empty | .leaf _ => True
  | .node n h l r =>
    CacheCorrect l ∧ CacheCorrect r ∧ n = l.length + r.length ∧ h = max l.height r.height + 1

/-- Every leaf holds between `1` and `B` elements and every internal node has non-empty
children, so the empty rope is only ever the `empty` constructor. -/
@[expose] def Chunked (B : ℕ) : Rope α → Prop
  | .empty => True
  | .leaf xs => 0 < xs.length ∧ xs.length ≤ B
  | .node _ _ l r => Chunked B l ∧ Chunked B r ∧ l.isEmpty = false ∧ r.isEmpty = false

/-- At every internal node the structural heights of the children differ by at most one. -/
@[expose] def Balanced : Rope α → Prop
  | .empty | .leaf _ => True
  | .node _ _ l r =>
    Balanced l ∧ Balanced r ∧
      l.structuralHeight ≤ r.structuralHeight + 1 ∧ r.structuralHeight ≤ l.structuralHeight + 1

/-- Well-formedness at chunk bound `B`: correct caches, bounded non-empty chunks and balance. -/
structure IsWF (B : ℕ) (t : Rope α) : Prop where
  /-- The cached fields are correct. -/
  cacheCorrect : CacheCorrect t
  /-- Leaves hold between `1` and `B` elements and internal nodes have non-empty children. -/
  chunked : Chunked B t
  /-- Sibling structural heights differ by at most one. -/
  balanced : Balanced t

@[simp] theorem length_empty : (empty : Rope α).length = 0 := rfl
@[simp] theorem length_leaf (xs : List α) : (leaf xs).length = xs.length := rfl
@[simp] theorem length_node (n h : ℕ) (l r : Rope α) : (node n h l r).length = n := rfl
@[simp] theorem height_empty : (empty : Rope α).height = 0 := rfl
@[simp] theorem height_leaf (xs : List α) : (leaf xs).height = 0 := rfl
@[simp] theorem height_node (n h : ℕ) (l r : Rope α) : (node n h l r).height = h := rfl
@[simp] theorem isEmpty_empty : (empty : Rope α).isEmpty = true := rfl
@[simp] theorem isEmpty_leaf (xs : List α) : (leaf xs).isEmpty = false := rfl
@[simp] theorem isEmpty_node (n h : ℕ) (l r : Rope α) : (node n h l r).isEmpty = false := rfl

@[simp] theorem isWF_empty (B : ℕ) : IsWF B (empty : Rope α) := ⟨trivial, trivial, trivial⟩

theorem isWF_leaf_iff {B : ℕ} {xs : List α} :
    IsWF B (leaf xs) ↔ 0 < xs.length ∧ xs.length ≤ B :=
  ⟨fun h => h.chunked, fun h => ⟨trivial, h, trivial⟩⟩

/-- The left child of a well-formed node is well-formed. -/
theorem IsWF.left {B n h : ℕ} {l r : Rope α} (hw : IsWF B (node n h l r)) : IsWF B l :=
  ⟨hw.cacheCorrect.1, hw.chunked.1, hw.balanced.1⟩

/-- The right child of a well-formed node is well-formed. -/
theorem IsWF.right {B n h : ℕ} {l r : Rope α} (hw : IsWF B (node n h l r)) : IsWF B r :=
  ⟨hw.cacheCorrect.2.1, hw.chunked.2.1, hw.balanced.2.1⟩

instance instDecidableCacheCorrect : (t : Rope α) → Decidable (CacheCorrect t)
  | .empty | .leaf _ => inferInstanceAs (Decidable True)
  | .node n h l r =>
    haveI := instDecidableCacheCorrect l
    haveI := instDecidableCacheCorrect r
    inferInstanceAs (Decidable (CacheCorrect l ∧ CacheCorrect r ∧
      n = l.length + r.length ∧ h = max l.height r.height + 1))

instance instDecidableChunked (B : ℕ) : (t : Rope α) → Decidable (Chunked B t)
  | .empty => inferInstanceAs (Decidable True)
  | .leaf xs => inferInstanceAs (Decidable (0 < xs.length ∧ xs.length ≤ B))
  | .node _ _ l r =>
    haveI := instDecidableChunked B l
    haveI := instDecidableChunked B r
    inferInstanceAs (Decidable (Chunked B l ∧ Chunked B r ∧
      l.isEmpty = false ∧ r.isEmpty = false))

instance instDecidableBalanced : (t : Rope α) → Decidable (Balanced t)
  | .empty | .leaf _ => inferInstanceAs (Decidable True)
  | .node _ _ l r =>
    haveI := instDecidableBalanced l
    haveI := instDecidableBalanced r
    inferInstanceAs (Decidable (Balanced l ∧ Balanced r ∧
      l.structuralHeight ≤ r.structuralHeight + 1 ∧
      r.structuralHeight ≤ l.structuralHeight + 1))

instance (B : ℕ) (t : Rope α) : Decidable (IsWF B t) :=
  decidable_of_iff (CacheCorrect t ∧ Chunked B t ∧ Balanced t)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- Cached height equals structural height when the caches are correct. -/
theorem height_eq_structuralHeight {t : Rope α} (hc : CacheCorrect t) :
    t.height = t.structuralHeight := by
  induction t <;> simp_all [CacheCorrect, structuralHeight]

/-- A node over `l` and `r` with recomputed caches; an empty child is dropped instead. -/
@[expose] def mkNode : Rope α → Rope α → Rope α
  | .empty, r => r
  | l, .empty => l
  | l, r => .node (l.length + r.length) (max l.height r.height + 1) l r

@[simp] theorem mkNode_empty_left (r : Rope α) : mkNode .empty r = r := rfl

@[simp] theorem mkNode_empty_right (l : Rope α) : mkNode l .empty = l := by
  cases l <;> rfl

theorem cacheCorrect_mkNode {l r : Rope α} (hl : CacheCorrect l) (hr : CacheCorrect r) :
    CacheCorrect (mkNode l r) := by
  cases l <;> cases r <;> first | assumption | exact ⟨hl, hr, rfl, rfl⟩

theorem chunked_mkNode {B : ℕ} {l r : Rope α} (hl : Chunked B l) (hr : Chunked B r) :
    Chunked B (mkNode l r) := by
  cases l <;> cases r <;> first | assumption | exact ⟨hl, hr, rfl, rfl⟩

end Structure

/-! ### The list model and basic operations -/

section Model

variable {α : Type u} {β : Type v}

/-- The element at index `i`, if any. -/
@[expose] def get? : Rope α → ℕ → Option α
  | .empty, _ => none
  | .leaf xs, i => xs[i]?
  | .node _ _ l r, i => if i < l.length then get? l i else get? r (i - l.length)

/-- Apply `f` to every element, keeping the shape and the caches. -/
@[expose] def map (f : α → β) : Rope α → Rope β
  | .empty => .empty
  | .leaf xs => .leaf (xs.map f)
  | .node n h l r => .node n h (map f l) (map f r)

/-- Left fold over the elements. -/
@[expose] def foldl (f : β → α → β) : β → Rope α → β
  | z, .empty => z
  | z, .leaf xs => xs.foldl f z
  | z, .node _ _ l r => foldl f (foldl f z l) r

/-- Right fold over the elements. -/
@[expose] def foldr (f : α → β → β) : β → Rope α → β
  | z, .empty => z
  | z, .leaf xs => xs.foldr f z
  | z, .node _ _ l r => foldr f (foldr f z r) l

/-- The elements of `t` in order: the list model of the rope. It is one right-to-left traversal
that conses each element once. -/
@[expose] def toList (t : Rope α) : List α := t.foldr List.cons []

/-- The one-element rope. -/
@[expose] def singleton (x : α) : Rope α := .leaf [x]

/-- Bulk construction: one leaf per chunk of `xs.toChunks (max 1 B)`, combined by
`List.balancedFold`. At every node the two sides receive `⌊n / 2⌋` and `⌈n / 2⌉` of the `n`
chunks. Every chunk is non-empty, so `mkNode` never drops a leaf, and the shape depends only on
the number of chunks. -/
@[expose] def ofList (B : ℕ) (xs : List α) : Rope α :=
  (xs.toChunks (max 1 B)).balancedFold mkNode .empty leaf

instance : Membership α (Rope α) := ⟨fun t x => x ∈ t.toList⟩

instance [DecidableEq α] (x : α) (t : Rope α) : Decidable (x ∈ t) :=
  inferInstanceAs (Decidable (x ∈ t.toList))

/-- Membership in the model is membership in the rope. -/
@[simp] theorem mem_toList {x : α} {t : Rope α} : x ∈ t.toList ↔ x ∈ t := Iff.rfl

private theorem foldr_cons_eq (t : Rope α) (tail : List α) :
    t.foldr List.cons tail = t.toList ++ tail := by
  induction t generalizing tail with
  | empty => rfl
  | leaf xs =>
    change xs.foldr List.cons tail = xs.foldr List.cons [] ++ tail
    simp
  | node n h l r ihl ihr =>
    change l.foldr List.cons (r.foldr List.cons tail) =
      l.foldr List.cons (r.foldr List.cons []) ++ tail
    rw [ihl, ihl (r.foldr List.cons []), ihr, ihr [], List.append_nil, List.append_assoc]

@[simp] theorem toList_empty : (empty : Rope α).toList = [] := rfl
@[simp] theorem toList_leaf (xs : List α) : (leaf xs).toList = xs := List.foldr_cons_nil
@[simp] theorem toList_node (n h : ℕ) (l r : Rope α) :
    (node n h l r).toList = l.toList ++ r.toList := by
  rw [toList, foldr, foldr_cons_eq, foldr_cons_eq, List.append_nil]

@[simp] theorem toList_mkNode (l r : Rope α) : (mkNode l r).toList = l.toList ++ r.toList := by
  cases l <;> cases r <;> simp [mkNode]

/-- The cached length is the length of the model when the caches are correct. -/
theorem length_eq_length_toList {t : Rope α} (hc : CacheCorrect t) :
    t.length = t.toList.length := by
  induction t <;> simp_all [CacheCorrect]

@[simp] theorem get?_empty (i : ℕ) : (empty : Rope α).get? i = none := rfl
@[simp] theorem get?_leaf (xs : List α) (i : ℕ) : (leaf xs).get? i = xs[i]? := rfl

/-- Indexing agrees with indexing the model; out-of-range indices give `none`. -/
theorem get?_eq_getElem? {t : Rope α} (hc : CacheCorrect t) (i : ℕ) :
    t.get? i = t.toList[i]? := by
  induction t generalizing i <;>
    simp_all [CacheCorrect, get?, List.getElem?_append, length_eq_length_toList]

@[simp] theorem map_empty (f : α → β) : (empty : Rope α).map f = .empty := rfl
@[simp] theorem map_leaf (f : α → β) (xs : List α) : (leaf xs).map f = .leaf (xs.map f) := rfl
@[simp] theorem map_node (f : α → β) (n h : ℕ) (l r : Rope α) :
    (node n h l r).map f = .node n h (l.map f) (r.map f) := rfl

@[simp] theorem toList_map (f : α → β) (t : Rope α) : (t.map f).toList = t.toList.map f := by
  induction t <;> simp_all

@[simp] theorem length_map (f : α → β) (t : Rope α) : (t.map f).length = t.length := by
  cases t <;> simp

@[simp] theorem height_map (f : α → β) (t : Rope α) : (t.map f).height = t.height := by
  cases t <;> simp

@[simp] theorem structuralHeight_map (f : α → β) (t : Rope α) :
    (t.map f).structuralHeight = t.structuralHeight := by
  induction t <;> simp_all [structuralHeight]

@[simp] theorem isEmpty_map (f : α → β) (t : Rope α) : (t.map f).isEmpty = t.isEmpty := by
  cases t <;> simp

theorem cacheCorrect_map (f : α → β) {t : Rope α} (hc : CacheCorrect t) :
    CacheCorrect (t.map f) := by
  induction t <;> simp_all [CacheCorrect]

theorem chunked_map (f : α → β) {B : ℕ} {t : Rope α} (hc : Chunked B t) :
    Chunked B (t.map f) := by
  induction t <;> simp_all [Chunked]

theorem balanced_map (f : α → β) {t : Rope α} (hb : Balanced t) : Balanced (t.map f) := by
  induction t <;> simp_all [Balanced]

theorem isWF_map (f : α → β) {B : ℕ} {t : Rope α} (hw : IsWF B t) : IsWF B (t.map f) :=
  ⟨cacheCorrect_map f hw.cacheCorrect, chunked_map f hw.chunked, balanced_map f hw.balanced⟩

/-- The left fold agrees with the left fold of the model. -/
theorem foldl_eq (f : β → α → β) (z : β) (t : Rope α) : t.foldl f z = t.toList.foldl f z := by
  induction t generalizing z <;> simp_all [foldl]

/-- The right fold agrees with the right fold of the model. -/
theorem foldr_eq (f : α → β → β) (z : β) (t : Rope α) : t.foldr f z = t.toList.foldr f z := by
  induction t generalizing z <;> simp_all [foldr]

@[simp] theorem toList_singleton (x : α) : (singleton x).toList = [x] := rfl

theorem isWF_singleton {B : ℕ} (hB : 1 ≤ B) (x : α) : IsWF B (singleton x) :=
  isWF_leaf_iff.2 ⟨Nat.one_pos, hB⟩

/-- Bulk construction represents its input. -/
@[simp] theorem toList_ofList (B : ℕ) (xs : List α) : (ofList B xs).toList = xs := by
  unfold ofList
  refine (List.balancedFold_induction (op := mkNode) (e := .empty) (f := leaf)
    (p := fun cs (t : Rope α) => t.toList = cs.flatten) rfl (by simp)
    (fun _ _ _ _ _ _ hx hy => ?_) (xs.toChunks (max 1 B))).trans (xs.flatten_toChunks _)
  simp [hx, hy]

theorem cacheCorrect_ofList (B : ℕ) (xs : List α) : CacheCorrect (ofList B xs) :=
  List.balancedFold_induction (op := mkNode) (e := .empty) (f := leaf)
    (p := fun _ (t : Rope α) => CacheCorrect t) trivial (fun _ => trivial)
    (fun _ _ _ _ _ _ hx hy => cacheCorrect_mkNode hx hy) _

/-- Bulk construction produces chunks of between `1` and `B` elements. Its balance is an open
objective of cslib-community/cslib-frontier#3670. -/
theorem chunked_ofList {B : ℕ} (hB : 1 ≤ B) (xs : List α) : Chunked B (ofList B xs) := by
  refine List.balancedFold_induction (op := mkNode) (e := .empty) (f := leaf)
    (p := fun cs (t : Rope α) => (∀ c ∈ cs, 0 < c.length ∧ c.length ≤ B) → Chunked B t)
    (fun _ => trivial) (fun c h => h c (List.mem_singleton_self c))
    (fun _ _ _ _ _ _ hx hy h => chunked_mkNode (hx fun c hc => h c (List.mem_append_left _ hc))
      (hy fun c hc => h c (List.mem_append_right _ hc))) (xs.toChunks (max 1 B)) fun c hc => ?_
  have := List.length_pos_and_le_of_mem_toChunks (by omega) hc
  omega

end Model

end Rope

end Cslib.DataStructure
