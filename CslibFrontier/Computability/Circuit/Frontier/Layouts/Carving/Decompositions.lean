/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Basic
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.TreeSide
public import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Carving decompositions, branch decompositions, and binary partition trees

A *carving decomposition* of a multigraph `G : Multigraph V E`
([Seymour and Thomas][SeymourThomas1994]) is an
unrooted tree `T` of maximum degree at most `3` whose leaves (`deg ≤ 1`) are in bijection with `V`.
Deleting an oriented edge `(u, v)` of `T` splits `T` into two subtrees
(`SimpleGraph.IsTree.treeSide`) and induces a vertex cut of `G`; the width of the decomposition is
the largest size of an induced edge cut `G.edgeCut S`, and `G.carvingWidth` is the minimum width
over finite index trees.

A *branch decomposition* of `G` ([Robertson and Seymour][RobertsonSeymour1991]) is an unrooted
subcubic tree `T` whose leaves are in bijection with the edge set `E`. Deleting an edge of `T`
splits `E` into `(A, Aᶜ)` and induces the *middle set* `G.middleSet A` of vertices incident to both
`A` and `Aᶜ`; the minimum width is `G.branchwidth`.

Recursive separator constructions build rooted binary partition trees (`BinTree α`). We prove the
exact equivalence between unrooted `SubcubicLeafTree α` decompositions and rooted `BinTree α`
partitions for any symmetric cut cost (`cost Sᶜ = cost S` with `cost ∅ = 0`), and deduce the
classical inequality `G.branchwidth ≤ G.carvingWidth` on every finite loopless cubic multigraph.

## Main definitions

* `Cslib.Circuits.Frontier.Carving.SubcubicLeafTree`: an unrooted subcubic tree whose degree-`≤ 1`
  nodes are in bijection with `α`.
* `Cslib.Circuits.Frontier.Multigraph.CarvingDecomposition`,
  `Cslib.Circuits.Frontier.Multigraph.ecarvingWidth`,
  `Cslib.Circuits.Frontier.Multigraph.carvingWidth`: carving decompositions and carving-width.
* `Cslib.Circuits.Frontier.Multigraph.middleSet`,
  `Cslib.Circuits.Frontier.Multigraph.BranchDecomposition`,
  `Cslib.Circuits.Frontier.Multigraph.ebranchwidth`,
  `Cslib.Circuits.Frontier.Multigraph.branchwidth`: middle sets, branch decompositions, and
  branchwidth.
* `Cslib.Circuits.Frontier.Carving.BinTree`: rooted binary partition trees over `α`.

## Main results

* `Cslib.Circuits.Frontier.Multigraph.carvingWidth_le_of_binTree`,
  `Cslib.Circuits.Frontier.Multigraph.exists_binTree_carvingWidth`: equivalence between carving
  decompositions and binary partition trees of `V`.
* `Cslib.Circuits.Frontier.Multigraph.branchwidth_le_of_binTree`: constructing a branch
  decomposition from a binary partition tree of `E`.
* `Cslib.Circuits.Frontier.Multigraph.branchwidth_le_carvingWidth`: on a finite loopless cubic
  multigraph, `G.branchwidth ≤ G.carvingWidth`.

## References

* [N. Robertson and P. D. Seymour, *Graph Minors. X. Obstructions to
  Tree-Decomposition*][RobertsonSeymour1991]
* [P. D. Seymour and R. Thomas, *Call routing and the ratcatcher*][SeymourThomas1994]
-/

public section

open Set

namespace Cslib.Circuits.Frontier

/-! ### Unrooted subcubic leaf-labeled trees -/

namespace Carving

/-- An unrooted subcubic tree on `ι` whose leaves (vertices of degree at most `1`) are in bijection
with `α`. When `|ι| = 1` the unique vertex has degree `0 ≤ 1`, accommodating singleton `α`. -/
structure SubcubicLeafTree (α : Type*) (ι : Type*) where
  /-- The underlying simple graph. -/
  tree : SimpleGraph ι
  /-- The graph is a tree. -/
  isTree : tree.IsTree
  /-- Every node has degree at most `3`. -/
  degree_le_three : ∀ t : ι, (tree.neighborSet t).ncard ≤ 3
  /-- Bijection between `α` and the nodes of degree at most `1`. -/
  leaf : α ≃ {t : ι // (tree.neighborSet t).ncard ≤ 1}

namespace SubcubicLeafTree

variable {α ι κ : Type*} (D : SubcubicLeafTree α ι)

/-- The subset of `α` on the `u`-side of `(u, v)`. -/
def cutSet (u v : ι) : Set α :=
  {a : α | (D.leaf a).val ∈ D.isTree.treeSide u v}

/-- Reversing an edge of `D.tree` complements the induced subset of `α`. -/
theorem cutSet_compl_of_adj {u v : ι} (huv : D.tree.Adj u v) :
    D.cutSet v u = (D.cutSet u v)ᶜ := by
  ext a
  simp [cutSet, D.isTree.treeSide_compl_of_adj huv]

/-- A finite index tree implies `Finite α`. -/
theorem finite [Finite ι] (D : SubcubicLeafTree α ι) : Finite α :=
  Finite.of_equiv {t : ι // (D.tree.neighborSet t).ncard ≤ 1} D.leaf.symm

private theorem ncard_neighborSet_comap_symm (e : ι ≃ κ) (k : κ) :
    ((D.tree.comap e.symm).neighborSet k).ncard = (D.tree.neighborSet (e.symm k)).ncard := by
  have h : (D.tree.comap e.symm).neighborSet k = e '' D.tree.neighborSet (e.symm k) := by
    ext x
    simp only [SimpleGraph.mem_neighborSet, SimpleGraph.comap_adj]
    exact ⟨fun hx => ⟨e.symm x, hx, e.apply_symm_apply x⟩, by rintro ⟨y, hy, rfl⟩; simpa using hy⟩
  rw [h, ncard_image_of_injective _ e.injective]

/-- Transport a `SubcubicLeafTree` along an equivalence of index types. -/
def reindex (e : ι ≃ κ) : SubcubicLeafTree α κ where
  tree := D.tree.comap e.symm
  isTree := (SimpleGraph.Iso.comap e.symm D.tree).symm.isTree_iff.1 D.isTree
  degree_le_three k := (D.ncard_neighborSet_comap_symm e k).trans_le (D.degree_le_three _)
  leaf := D.leaf.trans
    { toFun := fun t => ⟨e t.val, by
        rw [D.ncard_neighborSet_comap_symm, e.symm_apply_apply]; exact t.property⟩
      invFun := fun k => ⟨e.symm k.val, by
        rw [← D.ncard_neighborSet_comap_symm]; exact k.property⟩
      left_inv := fun t => Subtype.ext (e.symm_apply_apply t.val)
      right_inv := fun k => Subtype.ext (e.apply_symm_apply k.val) }

private theorem pathTo_reindex_length (e : ι ≃ κ) (w u : ι) :
    ((D.reindex e).isTree.pathTo (e w) (e u)).length = (D.isTree.pathTo w u).length := by
  let iso : D.tree ≃g (D.reindex e).tree := (SimpleGraph.Iso.comap e.symm D.tree).symm
  let q : (D.reindex e).tree.Walk (iso.toHom u) (iso.toHom w) :=
    (D.isTree.pathTo w u).map iso.toHom
  have hnd : q.support.Nodup := by
    change ((D.isTree.pathTo w u).map iso.toHom).support.Nodup
    rw [SimpleGraph.Walk.support_map]
    exact (D.isTree.isPath_pathTo w u).support_nodup.map iso.injective
  have hq : q.IsPath := SimpleGraph.Walk.IsPath.mk' hnd
  have heq : q = (D.reindex e).isTree.pathTo (iso.toHom w) (iso.toHom u) :=
    (D.reindex e).isTree.eq_pathTo (iso.toHom w) hq
  change ((D.reindex e).isTree.pathTo (iso.toHom w) (iso.toHom u)).length = _
  rw [← heq, SimpleGraph.Walk.length_map]

@[simp] theorem cutSet_reindex (e : ι ≃ κ) (u v : κ) :
    (D.reindex e).cutSet u v = D.cutSet (e.symm u) (e.symm v) := by
  ext a
  have hleaf : ((D.reindex e).leaf a).val = e (D.leaf a).val := rfl
  simp only [cutSet, SimpleGraph.IsTree.treeSide, mem_ofPred_eq]
  rw [hleaf]
  conv_lhs =>
    rw [← e.apply_symm_apply u, ← e.apply_symm_apply v]
  rw [D.pathTo_reindex_length e (D.leaf a).val (e.symm u),
    D.pathTo_reindex_length e (D.leaf a).val (e.symm v)]

/-- Width of a `SubcubicLeafTree` with respect to any cut cost `cost : Set α → ℕ`. -/
noncomputable def costWidth [Fintype ι] (cost : Set α → ℕ) : ℕ :=
  open Classical in
  (Finset.univ.filter fun p : ι × ι => D.tree.Adj p.1 p.2).sup fun p => cost (D.cutSet p.1 p.2)

theorem costWidth_le_iff [Fintype ι] {cost : Set α → ℕ} {k : ℕ} :
    D.costWidth cost ≤ k ↔ ∀ u v, D.tree.Adj u v → cost (D.cutSet u v) ≤ k := by
  classical
  rw [costWidth, Finset.sup_le_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.forall]

theorem cost_cutSet_le [Fintype ι] (cost : Set α → ℕ) {u v : ι} (huv : D.tree.Adj u v) :
    cost (D.cutSet u v) ≤ D.costWidth cost :=
  (D.costWidth_le_iff.mp le_rfl) u v huv

@[simp] theorem costWidth_reindex [Fintype ι] [Fintype κ] (e : ι ≃ κ) (cost : Set α → ℕ) :
    (D.reindex e).costWidth cost = D.costWidth cost := by
  refine le_antisymm ?_ ?_
  · refine (D.reindex e).costWidth_le_iff.mpr fun u v huv => ?_
    rw [D.cutSet_reindex]
    exact D.cost_cutSet_le cost huv
  · refine D.costWidth_le_iff.mpr fun u v huv => ?_
    have huv' : (D.reindex e).tree.Adj (e u) (e v) := by
      change D.tree.Adj (e.symm (e u)) (e.symm (e v))
      simpa using huv
    have h := (D.reindex e).cost_cutSet_le cost huv'
    simpa [D.cutSet_reindex] using h

end SubcubicLeafTree

/-! ### Binary partition trees and equivalence with `SubcubicLeafTree` -/

/-- A rooted binary tree with leaves labeled in `α`. -/
inductive BinTree (α : Type*) where
  | leaf (a : α) : BinTree α
  | node (left right : BinTree α) : BinTree α

namespace BinTree

variable {α : Type*}

/-- The ordered list of leaf labels of a `BinTree`. -/
def leaves : BinTree α → List α
  | .leaf a => [a]
  | .node l r => l.leaves ++ r.leaves

/-- The set of leaf labels of a `BinTree`. -/
def leafSet (t : BinTree α) : Set α :=
  {a | a ∈ t.leaves}

@[simp] theorem leafSet_leaf (a : α) : (BinTree.leaf a).leafSet = {a} := by
  ext x; simp [leafSet, leaves]

@[simp] theorem leafSet_node (l r : BinTree α) :
    (BinTree.node l r).leafSet = l.leafSet ∪ r.leafSet := by
  ext x; simp [leafSet, leaves]

/-- `t` partitions `X` cleanly: each element of `X` appears at a unique leaf of `t`. -/
@[expose] def IsPartition (t : BinTree α) (X : Set α) : Prop :=
  t.leaves.Nodup ∧ t.leafSet = X

theorem isPartition_leaf (a : α) : (BinTree.leaf a).IsPartition {a} :=
  ⟨List.nodup_singleton a, leafSet_leaf a⟩

theorem isPartition_node {l r : BinTree α} {X Y : Set α} (hl : l.IsPartition X)
    (hr : r.IsPartition Y) (hd : Disjoint X Y) : (BinTree.node l r).IsPartition (X ∪ Y) := by
  refine ⟨List.nodup_append.mpr ⟨hl.1, hr.1, ?_⟩, ?_⟩
  · rintro x hx _ hy rfl
    have hxX : x ∈ X := by rw [← hl.2]; exact hx
    have hyY : x ∈ Y := by rw [← hr.2]; exact hy
    exact Set.disjoint_left.mp hd hxX hyY
  · rw [leafSet_node, hl.2, hr.2]

/-- Sets of leaf labels realized by subtrees of `t`. -/
inductive IsSubtreeSet : BinTree α → Set α → Prop where
  | here (t : BinTree α) : IsSubtreeSet t t.leafSet
  | left {l r : BinTree α} {S : Set α} : IsSubtreeSet l S → IsSubtreeSet (.node l r) S
  | right {l r : BinTree α} {S : Set α} : IsSubtreeSet r S → IsSubtreeSet (.node l r) S

theorem IsSubtreeSet.subset_leafSet {t : BinTree α} {S : Set α} (h : t.IsSubtreeSet S) :
    S ⊆ t.leafSet := by
  induction h with
  | here _ => exact Subset.rfl
  | @left l r _ _ ih => exact ih.trans (by rw [leafSet_node]; exact subset_union_left)
  | @right l r _ _ ih => exact ih.trans (by rw [leafSet_node]; exact subset_union_right)

theorem IsSubtreeSet.singleton_of_mem {t : BinTree α} {a : α} (ha : a ∈ t.leaves) :
    t.IsSubtreeSet {a} := by
  induction t with
  | leaf b =>
    simp only [leaves, List.mem_singleton] at ha
    subst ha
    simpa using IsSubtreeSet.here (.leaf a)
  | node l r ihl ihr =>
    simp only [leaves, List.mem_append] at ha
    rcases ha with ha | ha
    · exact .left (ihl ha)
    · exact .right (ihr ha)

/-- Combine two optional binary trees, skipping `none` branches. -/
def joinOpt : Option (BinTree α) → Option (BinTree α) → Option (BinTree α)
  | none, o₂ => o₂
  | some t₁, none => some t₁
  | some t₁, some t₂ => some (.node t₁ t₂)

theorem joinOpt_spec {o₁ o₂ : Option (BinTree α)} {X₁ X₂ : Set α} (hd : Disjoint X₁ X₂)
    (h₁ : match o₁ with | none => X₁ = ∅ | some t₁ => t₁.IsPartition X₁)
    (h₂ : match o₂ with | none => X₂ = ∅ | some t₂ => t₂.IsPartition X₂) :
    match joinOpt o₁ o₂ with
    | none => X₁ ∪ X₂ = ∅
    | some t => t.IsPartition (X₁ ∪ X₂) ∧ ∀ S, t.IsSubtreeSet S →
        S = X₁ ∪ X₂ ∨ (∃ t₁, o₁ = some t₁ ∧ t₁.IsSubtreeSet S) ∨
          (∃ t₂, o₂ = some t₂ ∧ t₂.IsSubtreeSet S) := by
  cases o₁ with
  | none =>
    cases o₂ with
    | none =>
      simp [joinOpt, h₁, h₂]
    | some t₂ =>
      simp only [joinOpt, h₁, empty_union]
      exact ⟨h₂, fun S hS => Or.inr (Or.inr ⟨t₂, rfl, hS⟩)⟩
  | some t₁ =>
    cases o₂ with
    | none =>
      simp only [joinOpt, h₂, union_empty]
      exact ⟨h₁, fun S hS => Or.inr (Or.inl ⟨t₁, rfl, hS⟩)⟩
    | some t₂ =>
      simp only [joinOpt]
      refine ⟨isPartition_node h₁ h₂ hd, fun S hS => ?_⟩
      cases hS with
      | here _ =>
        left
        rw [leafSet_node, h₁.2, h₂.2]
      | left hs => exact Or.inr (Or.inl ⟨t₁, rfl, hs⟩)
      | right hs => exact Or.inr (Or.inr ⟨t₂, rfl, hs⟩)

/-- Build a caterpillar `BinTree` from a nonempty duplicate-free list. -/
def ofNonemptyList : (l : List α) → l ≠ [] → BinTree α
  | [a], _ => .leaf a
  | a :: b :: rest, _ => .node (.leaf a) (ofNonemptyList (b :: rest) (List.cons_ne_nil b rest))

theorem isPartition_ofNonemptyList (l : List α) (hne : l ≠ []) (hnodup : l.Nodup) :
    (ofNonemptyList l hne).IsPartition {x | x ∈ l} := by
  induction l with
  | nil => contradiction
  | cons a tail ih =>
    cases tail with
    | nil =>
      simpa [ofNonemptyList] using isPartition_leaf a
    | cons b rest =>
      simp only [ofNonemptyList]
      have hnd := List.nodup_cons.mp hnodup
      have hsub := ih (List.cons_ne_nil b rest) hnd.2
      have hdisj : Disjoint ({a} : Set α) {x | x ∈ b :: rest} := by
        rw [Set.disjoint_singleton_left]
        exact hnd.1
      have heq : ({a} : Set α) ∪ {x | x ∈ b :: rest} = {x | x ∈ a :: b :: rest} := by
        ext x; simp
      rw [← heq]
      exact isPartition_node (isPartition_leaf a) hsub hdisj

/-- Build an optional caterpillar `BinTree` on any finite set `X : Set α`. -/
noncomputable def ofSet (X : Set α) (hX : X.Finite := by toFinite_tac) : Option (BinTree α) :=
  let l := hX.toFinset.toList
  if h : l = [] then none else some (ofNonemptyList l h)

theorem ofSet_spec (X : Set α) (hX : X.Finite := by toFinite_tac) :
    match ofSet X hX with
    | none => X = ∅
    | some t => t.IsPartition X := by
  dsimp only [ofSet]
  split_ifs with h
  · ext x
    have hx : x ∉ hX.toFinset.toList := by rw [h]; simp
    simpa using hx
  · have hp := isPartition_ofNonemptyList hX.toFinset.toList h (Finset.nodup_toList _)
    have hset : {x | x ∈ hX.toFinset.toList} = X := by
      ext x; simp
    rwa [hset] at hp

/-! #### From `BinTree` to `SubcubicLeafTree` -/

/-- Vertices of the rooted subtree corresponding to `s : BinTree α`. -/
@[reducible] private def Node : BinTree α → Type
  | .leaf _ => Unit
  | .node l r => Unit ⊕ l.Node ⊕ r.Node

private instance instFintypeNode : (s : BinTree α) → Fintype s.Node
  | .leaf _ => inferInstanceAs (Fintype Unit)
  | .node l r =>
    letI := instFintypeNode l
    letI := instFintypeNode r
    inferInstanceAs (Fintype (Unit ⊕ l.Node ⊕ r.Node))

private instance instDecidableEqNode : (s : BinTree α) → DecidableEq s.Node
  | .leaf _ => inferInstanceAs (DecidableEq Unit)
  | .node l r =>
    letI := instDecidableEqNode l
    letI := instDecidableEqNode r
    inferInstanceAs (DecidableEq (Unit ⊕ l.Node ⊕ r.Node))

private def nodeRoot : (s : BinTree α) → s.Node
  | .leaf _ => ()
  | .node _ _ => Sum.inl ()

@[simp] private def nodeDepth : (s : BinTree α) → s.Node → ℕ
  | .leaf _, () => 0
  | .node _ _, Sum.inl () => 0
  | .node l _, Sum.inr (Sum.inl x) => l.nodeDepth x + 1
  | .node _ r, Sum.inr (Sum.inr y) => r.nodeDepth y + 1

@[simp] private theorem nodeDepth_nodeRoot (s : BinTree α) : s.nodeDepth s.nodeRoot = 0 := by
  cases s <;> rfl

private theorem nodeDepth_eq_zero_iff (s : BinTree α) (x : s.Node) :
    s.nodeDepth x = 0 ↔ x = s.nodeRoot := by
  cases s with
  | leaf _ => rcases x with ⟨⟩; simp [nodeRoot]
  | node l r =>
    rcases x with ⟨⟩ | x | y <;> simp [nodeRoot]

@[simp] private noncomputable def nodeParent : (s : BinTree α) → s.Node → s.Node
  | .leaf _, () => ()
  | .node _ _, Sum.inl () => Sum.inl ()
  | .node l _, Sum.inr (Sum.inl x) =>
    open Classical in
    if x = l.nodeRoot then Sum.inl () else Sum.inr (Sum.inl (l.nodeParent x))
  | .node _ r, Sum.inr (Sum.inr y) =>
    open Classical in
    if y = r.nodeRoot then Sum.inl () else Sum.inr (Sum.inr (r.nodeParent y))

private theorem nodeDepth_nodeParent_add_one (s : BinTree α) {x : s.Node} (hx : x ≠ s.nodeRoot) :
    s.nodeDepth (s.nodeParent x) + 1 = s.nodeDepth x := by
  fun_induction s.nodeParent x with
  | case1 | case2 => exact absurd rfl hx -- the root
  | case3 | case5 => simp -- child is the root of its subtree
  | case4 l r x hxr ih => simp [ih hxr] -- left subtree, x ≠ its root
  | case6 l r y hyr ih => simp [ih hyr] -- right subtree, y ≠ its root

@[reducible] private def LeafIdx : BinTree α → Type
  | .leaf _ => Unit
  | .node l r => l.LeafIdx ⊕ r.LeafIdx

@[simp] private def leafLabel : (s : BinTree α) → s.LeafIdx → α
  | .leaf a, () => a
  | .node l _, Sum.inl i => l.leafLabel i
  | .node _ r, Sum.inr j => r.leafLabel j

@[simp] private def leafToNode : (s : BinTree α) → s.LeafIdx → s.Node
  | .leaf _, () => ()
  | .node l _, Sum.inl i => Sum.inr (Sum.inl (l.leafToNode i))
  | .node _ r, Sum.inr j => Sum.inr (Sum.inr (r.leafToNode j))

private theorem leafToNode_injective (s : BinTree α) : Function.Injective s.leafToNode := by
  induction s with
  | leaf _ => rintro ⟨⟩ ⟨⟩ _; rfl
  | node l r ihl ihr =>
    rintro (i₁ | j₁) (i₂ | j₂) h
    · exact congrArg Sum.inl (ihl (Sum.inl.inj (Sum.inr.inj h)))
    · exact nomatch h
    · exact nomatch h
    · exact congrArg Sum.inr (ihr (Sum.inr.inj (Sum.inr.inj h)))

private theorem range_leafLabel (s : BinTree α) : range s.leafLabel = s.leafSet := by
  induction s with
  | leaf a =>
    ext x
    simp only [mem_range, leafSet_leaf, mem_singleton_iff]
    exact ⟨by rintro ⟨⟨⟩, rfl⟩; rfl, by rintro rfl; exact ⟨(), rfl⟩⟩
  | node l r ihl ihr =>
    ext x
    simp only [mem_range, leafSet_node, mem_union, ← ihl, ← ihr]
    exact ⟨by rintro ⟨i | j, rfl⟩; exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨j, rfl⟩],
      by rintro (⟨i, rfl⟩ | ⟨j, rfl⟩); exacts [⟨Sum.inl i, rfl⟩, ⟨Sum.inr j, rfl⟩]⟩

private theorem leafLabel_injective (s : BinTree α) (hnd : s.leaves.Nodup) :
    Function.Injective s.leafLabel := by
  have hmem {t : BinTree α} (i : t.LeafIdx) : t.leafLabel i ∈ t.leafSet :=
    t.range_leafLabel ▸ mem_range_self i
  induction s with
  | leaf _ => rintro ⟨⟩ ⟨⟩ _; rfl
  | node l r ihl ihr =>
    rw [leaves, List.nodup_append] at hnd
    rintro (i₁ | j₁) (i₂ | j₂) h
    · exact congrArg Sum.inl (ihl hnd.1 h)
    · exact absurd h (hnd.2.2 _ (hmem i₁) _ (hmem j₂))
    · exact absurd h.symm (hnd.2.2 _ (hmem i₂) _ (hmem j₁))
    · exact congrArg Sum.inr (ihr hnd.2.1 h)

@[simp] private def subtreeLeafSet : (s : BinTree α) → s.Node → Set α
  | .leaf a, () => {a}
  | .node l r, Sum.inl () => l.leafSet ∪ r.leafSet
  | .node l _, Sum.inr (Sum.inl x) => l.subtreeLeafSet x
  | .node _ r, Sum.inr (Sum.inr y) => r.subtreeLeafSet y

private theorem isSubtreeSet_subtreeLeafSet (s : BinTree α) (x : s.Node) :
    s.IsSubtreeSet (s.subtreeLeafSet x) := by
  induction s with
  | leaf a =>
    rcases x with ⟨⟩
    simpa using IsSubtreeSet.here (.leaf a)
  | node l r ihl ihr =>
    rcases x with ⟨⟩ | x | y
    · simpa using IsSubtreeSet.here (.node l r)
    · exact .left (ihl x)
    · exact .right (ihr y)

@[simp] private def isLeafNode : (s : BinTree α) → s.Node → Bool
  | .leaf _, () => true
  | .node _ _, Sum.inl () => false
  | .node l _, Sum.inr (Sum.inl x) => l.isLeafNode x
  | .node _ r, Sum.inr (Sum.inr y) => r.isLeafNode y

private theorem isLeafNode_iff_mem_range (s : BinTree α) (x : s.Node) :
    s.isLeafNode x = true ↔ x ∈ range s.leafToNode := by
  induction s with
  | leaf _ =>
    rcases x with ⟨⟩
    exact ⟨fun _ => ⟨(), rfl⟩, fun _ => rfl⟩
  | node l r ihl ihr =>
    rcases x with ⟨⟩ | x | y <;>
      simp [isLeafNode, ihl, ihr, mem_range, Sum.exists, leafToNode]

@[simp] private noncomputable def nodeChildren : (s : BinTree α) → s.Node → Finset s.Node
  | .leaf _, () => ∅
  | .node l r, Sum.inl () =>
    open Classical in
    {Sum.inr (Sum.inl l.nodeRoot), Sum.inr (Sum.inr r.nodeRoot)}
  | .node l _, Sum.inr (Sum.inl x) =>
    (l.nodeChildren x).map ⟨Sum.inr ∘ Sum.inl, Sum.inr_injective.comp Sum.inl_injective⟩
  | .node _ r, Sum.inr (Sum.inr y) =>
    (r.nodeChildren y).map ⟨Sum.inr ∘ Sum.inr, Sum.inr_injective.comp Sum.inr_injective⟩

private theorem mem_nodeChildren_iff (s : BinTree α) {x c : s.Node} :
    c ∈ s.nodeChildren x ↔ c ≠ s.nodeRoot ∧ s.nodeParent c = x := by
  classical
  induction s with
  | leaf _ => rcases x with ⟨⟩; rcases c with ⟨⟩; dsimp only [nodeRoot]; simp
  | node l r ihl ihr =>
    have hr : (BinTree.node l r).nodeRoot = Sum.inl () := rfl
    rcases x with ⟨⟩ | x | y <;> rcases c with ⟨⟩ | cx | cy <;>
      simp only [nodeChildren, Finset.mem_insert, Finset.mem_singleton, Finset.mem_map,
        Function.Embedding.coeFn_mk, Function.comp_apply, ne_eq, hr, nodeParent, ihl, ihr] <;>
      (try split_ifs) <;> simp_all

private theorem card_nodeChildren (s : BinTree α) (x : s.Node) :
    (s.nodeChildren x).card = if s.isLeafNode x then 0 else 2 := by
  classical
  induction s with
  | leaf _ => rcases x with ⟨⟩; rfl
  | node l r ihl ihr =>
    rcases x with ⟨⟩ | x | y
    · simp only [nodeChildren, isLeafNode, Bool.false_eq_true, ↓reduceIte]
      exact Finset.card_pair (by simp)
    · rw [nodeChildren, Finset.card_map, ihl x]; rfl
    · rw [nodeChildren, Finset.card_map, ihr y]; rfl

private theorem subtreeLeafSet_eq_children (s : BinTree α) (x : s.Node) :
    s.subtreeLeafSet x =
      (s.leafLabel '' {i : s.LeafIdx | s.leafToNode i = x}) ∪
        ⋃ c ∈ s.nodeChildren x, s.subtreeLeafSet c := by
  classical
  induction s with
  | leaf a =>
    rcases x with ⟨⟩
    ext b; simp [eq_comm]
  | node l r ihl ihr =>
    rcases x with ⟨⟩ | x | y
    · have hl : l.subtreeLeafSet l.nodeRoot = l.leafSet := by
        cases l <;> dsimp only [nodeRoot] <;> simp
      have hr : r.subtreeLeafSet r.nodeRoot = r.leafSet := by
        cases r <;> dsimp only [nodeRoot] <;> simp
      ext b; simp [Sum.exists, hl, hr]
    · ext b; simp [ihl x, Sum.exists]
    · ext b; simp [ihr y, Sum.exists]

private abbrev TopNode (l r : BinTree α) : Type := l.Node ⊕ r.Node

/-- **Every `BinTree α` partitioning `Set.univ` realizes an unrooted `SubcubicLeafTree α`.** -/
theorem exists_subcubicLeafTree_of_binTree (t : BinTree α) (hp : t.IsPartition Set.univ) :
    ∃ (ι : Type) (_ : Fintype ι) (D : SubcubicLeafTree α ι),
      ∀ u v, D.tree.Adj u v →
        t.IsSubtreeSet (D.cutSet u v) ∨ t.IsSubtreeSet (D.cutSet u v)ᶜ := by
  classical
  cases t with
  | leaf a₀ =>
    have huniv : ({a₀} : Set α) = Set.univ := by simpa using hp.2
    let D : SubcubicLeafTree α Unit :=
      { tree := ⊥
        isTree := SimpleGraph.IsTree.of_subsingleton
        degree_le_three := fun _ => by simp
        leaf :=
          { toFun := fun _ => ⟨(), by simp⟩
            invFun := fun _ => a₀
            left_inv := fun a => by
              have : a ∈ ({a₀} : Set α) := by rw [huniv]; trivial
              exact (mem_singleton_iff.mp this).symm
            right_inv := fun ⟨(), _⟩ => rfl } }
    exact ⟨Unit, inferInstance, D, fun _ _ h => False.elim h⟩
  | node l r =>
    let root : TopNode l r := Sum.inl l.nodeRoot
    let depth : TopNode l r → ℕ
      | Sum.inl x => l.nodeDepth x
      | Sum.inr y => r.nodeDepth y + 1
    let par : TopNode l r → TopNode l r
      | Sum.inl x => if x = l.nodeRoot then root else Sum.inl (l.nodeParent x)
      | Sum.inr y => if y = r.nodeRoot then root else Sum.inr (r.nodeParent y)
    have hpar_root : par root = root := by simp [par, root]
    have hdepth_zero (z : TopNode l r) : depth z = 0 ↔ z = root := by
      rcases z with x | y
      · simp only [depth, root, l.nodeDepth_eq_zero_iff]
        exact ⟨congrArg Sum.inl, Sum.inl.inj⟩
      · simp [depth, root]
    have hdepth_step {z : TopNode l r} (hz : z ≠ root) : depth (par z) + 1 = depth z := by
      rcases z with x | y
      · have hxr : x ≠ l.nodeRoot := fun h => hz (congrArg Sum.inl h)
        simp only [par, hxr, ↓reduceIte, depth]
        exact l.nodeDepth_nodeParent_add_one hxr
      · simp only [par, depth]
        split_ifs with hyr
        · subst hyr; simp [root]
        · rw [← r.nodeDepth_nodeParent_add_one hyr]
    have hdepth_lt {z : TopNode l r} (hz : z ≠ root) : depth (par z) < depth z := by
      have := hdepth_step hz; omega
    let T := SimpleGraph.parentGraph par
    have hadj {x y : TopNode l r} :
        T.Adj x y ↔ (x ≠ root ∧ par x = y) ∨ (y ≠ root ∧ par y = x) := by
      rw [SimpleGraph.parentGraph_adj]
      constructor
      · rintro ⟨hxy, h | h⟩
        · refine Or.inl ⟨fun hxr => hxy ?_, h⟩
          rw [← h, hxr, hpar_root]
        · refine Or.inr ⟨fun hyr => hxy ?_, h⟩
          rw [← h, hyr, hpar_root]
      · rintro (⟨hx, rfl⟩ | ⟨hy, rfl⟩)
        · exact ⟨fun h => (hdepth_lt hx).ne' (congrArg depth h), Or.inl rfl⟩
        · exact ⟨fun h => (hdepth_lt hy).ne (congrArg depth h), Or.inr rfl⟩
    have hT : T.IsTree := by
      have hreach (z : TopNode l r) : T.Reachable z root := by
        induction z using (measure depth).wf.induction with | h z ih =>
          by_cases hzr : z = root
          · rw [hzr]
          · exact (hadj.mpr (Or.inl ⟨hzr, rfl⟩)).reachable.trans (ih _ (hdepth_lt hzr))
      rw [SimpleGraph.isTree_iff_connected_and_card]
      refine ⟨{ preconnected := fun x y => (hreach x).trans (hreach y).symm
                nonempty := ⟨root⟩ }, ?_⟩
      let f : {z : TopNode l r // z ≠ root} → T.edgeSet :=
        fun z => ⟨s(z.val, par z.val), hadj.mpr (Or.inl ⟨z.property, rfl⟩)⟩
      have hf : Function.Bijective f := by
        refine ⟨?_, ?_⟩
        · rintro ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩ heq
          rcases Sym2.eq_iff.mp (congrArg Subtype.val heq) with ⟨h, -⟩ | ⟨h1, h2⟩
          · exact Subtype.ext h
          · exfalso
            have h3 := hdepth_lt hz₁
            have h4 := hdepth_lt hz₂
            rw [h2] at h3
            rw [← h1] at h4
            exact lt_asymm h3 h4
        · rintro ⟨e, he⟩
          induction e using Sym2.ind with
          | h x y =>
            rcases hadj.mp ((SimpleGraph.mem_edgeSet _).mp he) with ⟨hx, rfl⟩ | ⟨hy, rfl⟩
            · exact ⟨⟨x, hx⟩, rfl⟩
            · exact ⟨⟨y, hy⟩, Subtype.ext Sym2.eq_swap⟩
      rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        Fintype.card_subtype_eq, Nat.card_eq_fintype_card]
      have hpos : 0 < Fintype.card (TopNode l r) := Fintype.card_pos_iff.mpr ⟨root⟩
      omega
    -- Degree characterization: leaves have degree 1, internal nodes have degree 3.
    have hch_inl {x : l.Node} (hxr : x ≠ l.nodeRoot) (w : TopNode l r) :
        (w ≠ root ∧ par w = Sum.inl x) ↔
          w ∈ (l.nodeChildren x).map ⟨Sum.inl, Sum.inl_injective⟩ := by
      rcases w with wx | wy
      · simp only [root, par, ne_eq, Sum.inl.injEq, Finset.mem_map, Function.Embedding.coeFn_mk,
          exists_eq_right, l.mem_nodeChildren_iff]
        split_ifs with hwx <;> simp [hwx]
      · simp only [root, par, ne_eq, reduceCtorEq, not_false_eq_true, true_and, Finset.mem_map,
          Function.Embedding.coeFn_mk]
        split_ifs <;> simp [hxr.symm]
    have hch_inr (y : r.Node) (w : TopNode l r) :
        (w ≠ root ∧ par w = Sum.inr y) ↔
          w ∈ (r.nodeChildren y).map ⟨Sum.inr, Sum.inr_injective⟩ := by
      rcases w with wx | wy
      · simp only [root, par, ne_eq, Sum.inl.injEq, Finset.mem_map, Function.Embedding.coeFn_mk,
          reduceCtorEq]
        split_ifs <;> simp
      · simp only [root, par, ne_eq, reduceCtorEq, not_false_eq_true, true_and, Finset.mem_map,
          Function.Embedding.coeFn_mk, Sum.inr.injEq, exists_eq_right, r.mem_nodeChildren_iff]
        split_ifs with hwy <;> simp [hwy]
    let isLeaf : TopNode l r → Bool := Sum.elim l.isLeafNode r.isLeafNode
    have hdeg_nonroot {s : BinTree α} (emb : s.Node ↪ TopNode l r) {u : s.Node}
        (hu : emb u ≠ root)
        (hch : ∀ w, (w ≠ root ∧ par w = emb u) ↔ w ∈ (s.nodeChildren u).map emb) :
        (T.neighborFinset (emb u)).card = if s.isLeafNode u then 1 else 3 := by
      have hfin : T.neighborFinset (emb u) =
          insert (par (emb u)) ((s.nodeChildren u).map emb) := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset, hadj, hch, Finset.mem_insert]
        exact ⟨by rintro (⟨-, rfl⟩ | hw); exacts [Or.inl rfl, Or.inr hw],
          by rintro (rfl | hw); exacts [Or.inl ⟨hu, rfl⟩, Or.inr hw]⟩
      have hnotmem : par (emb u) ∉ (s.nodeChildren u).map emb := fun hmem => by
        obtain ⟨hpr, hpp⟩ := (hch _).mpr hmem
        have h1 := hdepth_lt hu
        have h2 := hdepth_lt hpr
        rw [hpp] at h2
        exact lt_asymm h1 h2
      rw [hfin, Finset.card_insert_of_notMem hnotmem, Finset.card_map, s.card_nodeChildren]
      split_ifs <;> rfl
    have hdeg (z : TopNode l r) : (T.neighborSet z).ncard = if isLeaf z then 1 else 3 := by
      rw [← SimpleGraph.coe_neighborFinset, ncard_coe_finset]
      rcases z with x | y
      · by_cases hxr : x = l.nodeRoot
        · subst hxr
          have hfin : T.neighborFinset root =
              insert (Sum.inr r.nodeRoot)
                ((l.nodeChildren l.nodeRoot).map ⟨Sum.inl, Sum.inl_injective⟩) := by
            ext w
            simp only [SimpleGraph.mem_neighborFinset, hadj, ne_eq, not_true_eq_false, false_and,
              false_or, Finset.mem_insert, Finset.mem_map, Function.Embedding.coeFn_mk]
            rcases w with wx | wy <;>
              simp only [par, root, Sum.inl.injEq, reduceCtorEq, exists_eq_right,
                false_or, not_false_eq_true, true_and, l.mem_nodeChildren_iff] <;>
              split_ifs with hw <;> simp [hw]
          rw [hfin, Finset.card_insert_of_notMem (by simp), Finset.card_map, l.card_nodeChildren]
          dsimp only [isLeaf, root, Sum.elim_inl]
          split_ifs with h <;> simp [h]
        · exact hdeg_nonroot ⟨Sum.inl, Sum.inl_injective⟩
            (fun h => hxr (Sum.inl.inj h)) (hch_inl hxr)
      · exact hdeg_nonroot ⟨Sum.inr, Sum.inr_injective⟩ (by simp [root]) (hch_inr y)
    have hdeg_le_one_iff (z : TopNode l r) : (T.neighborSet z).ncard ≤ 1 ↔ isLeaf z = true := by
      rw [hdeg z]
      split_ifs with h <;> simp [h]
    -- Bijection between `α` and `{z : TopNode l r // deg ≤ 1}` via `(BinTree.node l r).LeafIdx`.
    let idxToNode : (BinTree.node l r).LeafIdx → {z : TopNode l r // (T.neighborSet z).ncard ≤ 1}
      | Sum.inl i => ⟨Sum.inl (l.leafToNode i),
          (hdeg_le_one_iff _).mpr ((l.isLeafNode_iff_mem_range _).mpr ⟨i, rfl⟩)⟩
      | Sum.inr j => ⟨Sum.inr (r.leafToNode j),
          (hdeg_le_one_iff _).mpr ((r.isLeafNode_iff_mem_range _).mpr ⟨j, rfl⟩)⟩
    have hidx_bij : Function.Bijective idxToNode := by
      refine ⟨?_, ?_⟩
      · rintro (i₁ | j₁) (i₂ | j₂) h
        · exact congrArg Sum.inl (l.leafToNode_injective (Sum.inl.inj (Subtype.ext_iff.mp h)))
        · exact nomatch Subtype.ext_iff.mp h
        · exact nomatch Subtype.ext_iff.mp h
        · exact congrArg Sum.inr (r.leafToNode_injective (Sum.inr.inj (Subtype.ext_iff.mp h)))
      · rintro ⟨x | y, hz⟩
        · obtain ⟨i, rfl⟩ := (l.isLeafNode_iff_mem_range x).mp ((hdeg_le_one_iff _).mp hz)
          exact ⟨Sum.inl i, rfl⟩
        · obtain ⟨j, rfl⟩ := (r.isLeafNode_iff_mem_range y).mp ((hdeg_le_one_iff _).mp hz)
          exact ⟨Sum.inr j, rfl⟩
    have hlbl_bij : Function.Bijective (BinTree.node l r).leafLabel :=
      ⟨(BinTree.node l r).leafLabel_injective hp.1,
        range_eq_univ.mp ((BinTree.node l r).range_leafLabel.trans hp.2)⟩
    let leafEquiv : α ≃ {z : TopNode l r // (T.neighborSet z).ncard ≤ 1} :=
      (Equiv.ofBijective _ hlbl_bij).symm.trans (Equiv.ofBijective _ hidx_bij)
    let D : SubcubicLeafTree α (TopNode l r) :=
      { tree := T
        isTree := hT
        degree_le_three := fun z => by rw [hdeg z]; split_ifs <;> omega
        leaf := leafEquiv }
    -- Relate `hT.parent root z` to `par z` by induction on `depth z` using `adj_iff_parent`.
    have hparent_eq : ∀ {z : TopNode l r}, z ≠ root → hT.parent root z = par z := by
      intro z hne
      induction z using (measure depth).wf.induction with | h z ih =>
        rcases (hT.adj_iff_parent root).mp (hadj.mpr (Or.inl ⟨hne, rfl⟩)) with ⟨-, hpz⟩ | ⟨hpr, hpp⟩
        · exact hpz
        · have hlt := hdepth_lt hne
          rw [ih _ hlt hpr] at hpp
          have hlt2 := hdepth_lt hpr
          rw [hpp] at hlt2
          exact absurd hlt (lt_asymm hlt2)
    have hdepth_eq_len (w : TopNode l r) : depth w = (hT.pathTo root w).length := by
      induction w using (measure depth).wf.induction with | h w ih =>
        by_cases hwr : w = root
        · rw [hwr, (hdepth_zero root).mpr rfl, SimpleGraph.IsTree.pathTo_self]; rfl
        · have hlen_p := hT.length_pathTo_parent root hwr
          rw [hparent_eq hwr] at hlen_p
          have hp := ih _ (hdepth_lt hwr)
          have hst := hdepth_step hwr
          omega
    have hdepth_lt_card (w : TopNode l r) : depth w < Fintype.card (TopNode l r) := by
      rw [hdepth_eq_len w]
      have hle := (hT.isPath_pathTo root w).support_nodup.length_le_card
      rw [SimpleGraph.Walk.length_support] at hle
      omega
    let subSet : TopNode l r → Set α := Sum.elim l.subtreeLeafSet r.subtreeLeafSet
    have hcut_eq : ∀ z : TopNode l r, z ≠ root → D.cutSet z (par z) = subSet z := by
      suffices ∀ k (z : TopNode l r), Fintype.card (TopNode l r) - depth z ≤ k → z ≠ root →
          D.cutSet z (par z) = subSet z from fun z hz => this _ z le_rfl hz
      intro k
      induction k with
      | zero =>
        intro z hk _
        have := hdepth_lt_card z
        omega
      | succ k ih =>
        intro z hk hz
        have hleaf_apply (j : (BinTree.node l r).LeafIdx) :
            (D.leaf ((BinTree.node l r).leafLabel j)).val = (idxToNode j).val := by
          change (leafEquiv ((Equiv.ofBijective _ hlbl_bij) j)).val = _
          simp [leafEquiv]
        have hset_eq (S : Set (TopNode l r)) : {a : α | (D.leaf a).val ∈ S} =
            (BinTree.node l r).leafLabel '' {j | (idxToNode j).val ∈ S} := by
          ext a
          constructor
          · intro ha
            obtain ⟨j, rfl⟩ := hlbl_bij.2 a
            exact ⟨j, by simpa [hleaf_apply] using ha, rfl⟩
          · rintro ⟨j, hj, rfl⟩
            simpa [hleaf_apply] using hj
        have hcut_step {s : BinTree α} (emb : s.Node ↪ TopNode l r) {u : s.Node}
            (hu : emb u ≠ root) (hk_u : Fintype.card (TopNode l r) - depth (emb u) ≤ k + 1)
            (hch : ∀ w, (w ≠ root ∧ par w = emb u) ↔ w ∈ (s.nodeChildren u).map emb)
            (hidx : (BinTree.node l r).leafLabel '' {j | (idxToNode j).val = emb u} =
              s.leafLabel '' {i : s.LeafIdx | s.leafToNode i = u})
            (hsub_emb : ∀ c, subSet (emb c) = s.subtreeLeafSet c) :
            D.cutSet (emb u) (par (emb u)) = s.subtreeLeafSet u := by
          have hadju : T.Adj (emb u) (par (emb u)) := hadj.mpr (Or.inl ⟨hu, rfl⟩)
          have hch_set : {c : TopNode l r | T.Adj (emb u) c ∧ c ≠ par (emb u)} =
              emb '' (s.nodeChildren u : Set s.Node) := by
            ext w
            simp only [mem_ofPred_eq, hadj, hch, Finset.mem_map, mem_image, Finset.mem_coe]
            refine ⟨?_, ?_⟩
            · rintro ⟨⟨-, rfl⟩ | hw, hne⟩
              · exact absurd rfl hne
              · exact hw
            · rintro ⟨c, hc, rfl⟩
              obtain ⟨hcr, hcp⟩ := (hch _).mpr (Finset.mem_map.mpr ⟨c, hc, rfl⟩)
              refine ⟨Or.inr ⟨c, hc, rfl⟩, fun heq => ?_⟩
              have h1 := hdepth_lt hu
              have h2 := hdepth_lt hcr
              rw [hcp, heq] at h2
              exact lt_asymm h1 h2
          have hself : {a : α | (D.leaf a).val = emb u} =
              s.leafLabel '' {i : s.LeafIdx | s.leafToNode i = u} := by
            rw [show {a : α | (D.leaf a).val = emb u} =
                {a : α | (D.leaf a).val ∈ ({emb u} : Set (TopNode l r))} from rfl, hset_eq]
            exact hidx
          change {a : α | (D.leaf a).val ∈ hT.treeSide (emb u) (par (emb u))} = s.subtreeLeafSet u
          rw [hT.treeSide_eq_insert_biUnion hadju, hch_set]
          calc {a : α | (D.leaf a).val ∈ insert (emb u)
                  (⋃ c ∈ emb '' (s.nodeChildren u : Set s.Node), hT.treeSide c (emb u))}
              = {a : α | (D.leaf a).val = emb u} ∪
                  ⋃ c ∈ s.nodeChildren u, D.cutSet (emb c) (emb u) := by
                ext a; simp [SubcubicLeafTree.cutSet]
            _ = (s.leafLabel '' {i : s.LeafIdx | s.leafToNode i = u}) ∪
                  ⋃ c ∈ s.nodeChildren u, s.subtreeLeafSet c := by
                rw [hself]
                congr 1
                refine iUnion₂_congr fun c hc => ?_
                obtain ⟨hcr, hcp⟩ := (hch (emb c)).mpr (Finset.mem_map.mpr ⟨c, hc, rfl⟩)
                have hlt : depth (emb u) < depth (emb c) := hcp ▸ hdepth_lt hcr
                have hd_bound := hdepth_lt_card (emb c)
                rw [← hcp, ih (emb c) (by omega) hcr, hsub_emb]
            _ = s.subtreeLeafSet u := (s.subtreeLeafSet_eq_children u).symm
        rcases z with x | y
        · have hxr : x ≠ l.nodeRoot := fun h => hz (congrArg Sum.inl h)
          exact hcut_step ⟨Sum.inl, Sum.inl_injective⟩ hz hk (hch_inl hxr)
            (by ext b; simp [idxToNode, Sum.exists]) (fun _ => rfl)
        · exact hcut_step ⟨Sum.inr, Sum.inr_injective⟩ hz hk (hch_inr y)
            (by ext b; simp [idxToNode, Sum.exists]) (fun _ => rfl)
    refine ⟨TopNode l r, inferInstance, D, fun u v huv => ?_⟩
    have hsub (z : TopNode l r) : (BinTree.node l r).IsSubtreeSet (subSet z) := by
      rcases z with x | y
      · exact .left (l.isSubtreeSet_subtreeLeafSet x)
      · exact .right (r.isSubtreeSet_subtreeLeafSet y)
    rcases hadj.mp huv with ⟨hu, rfl⟩ | ⟨hv, rfl⟩
    · left
      rw [hcut_eq u hu]
      exact hsub u
    · right
      rw [← D.cutSet_compl_of_adj huv, hcut_eq v hv]
      exact hsub v

/-! #### From `SubcubicLeafTree` to `BinTree` -/

/-- **Every finite `SubcubicLeafTree α` with `Nonempty α` yields a `BinTree α` partitioning
`Set.univ` whose subtree sets are either `Set.univ` or edge cuts of `D`.** -/
theorem exists_binTree_of_subcubicLeafTree {ι : Type*} [Finite ι] [Nonempty α]
    (D : SubcubicLeafTree α ι) :
    ∃ t : BinTree α, t.IsPartition Set.univ ∧
      ∀ S, t.IsSubtreeSet S → S = Set.univ ∨ ∃ u v, D.tree.Adj u v ∧ D.cutSet u v = S := by
  classical
  have := Fintype.ofFinite ι
  let a₀ : α := Classical.arbitrary α
  by_cases hcard : Fintype.card ι ≤ 1
  · have : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hcard
    have : Subsingleton {x : ι // (D.tree.neighborSet x).ncard ≤ 1} := inferInstance
    have hsub : Subsingleton α := D.leaf.injective.subsingleton
    refine ⟨.leaf a₀, ⟨List.nodup_singleton a₀, ?_⟩, fun S hS => ?_⟩
    · ext a
      simp [Subsingleton.elim a a₀]
    · cases hS
      left
      ext a
      simp [Subsingleton.elim a a₀]
  · have hcard' : 1 < Fintype.card ι := not_le.mp hcard
    let r₀ : ι := (D.leaf a₀).val
    have hr₀_le : (D.tree.neighborSet r₀).ncard ≤ 1 := (D.leaf a₀).property
    -- Since `|ι| ≥ 2` and `D.tree` is connected, `r₀` has a unique neighbour `c₀`.
    obtain ⟨w₀, hw₀⟩ : ∃ w : ι, w ≠ r₀ := Fintype.exists_ne_of_one_lt_card hcard' r₀
    have hwalk := SimpleGraph.Walk.not_nil_of_ne (p := D.isTree.pathTo w₀ r₀) hw₀.symm
    let c₀ : ι := (D.isTree.pathTo w₀ r₀).snd
    have hc₀_adj : D.tree.Adj r₀ c₀ := SimpleGraph.Walk.adj_snd hwalk
    have hc₀_uniq : ∀ c, D.tree.Adj r₀ c → c = c₀ := by
      intro c hc
      have hsub : ({c, c₀} : Set ι) ⊆ D.tree.neighborSet r₀ := by
        rintro x (rfl | rfl) <;> exact (SimpleGraph.mem_neighborSet _ _ _).mpr ‹_›
      have hnc := (ncard_le_ncard hsub).trans hr₀_le
      by_contra hne
      rw [ncard_pair hne] at hnc
      omega
    -- Build a `BinTree` on `D.cutSet t (parent r₀ t)` for any `t ≠ r₀` by recursion on fuel.
    have hrec (t : ι) : t ≠ r₀ →
        ∃ bt : BinTree α, bt.IsPartition (D.cutSet t (D.isTree.parent r₀ t)) ∧
          ∀ S, bt.IsSubtreeSet S → ∃ u v, D.tree.Adj u v ∧ D.cutSet u v = S := by
      intro ht
      induction t using
        (measure fun t => Fintype.card ι - (D.isTree.pathTo r₀ t).length).wf.induction with
      | h t ih =>
        let p := D.isTree.parent r₀ t
        have htp : D.tree.Adj t p := D.isTree.adj_parent r₀ ht
        let ch : Finset ι := (D.tree.neighborFinset t).erase p
        have hp_mem : p ∈ D.tree.neighborFinset t :=
          (SimpleGraph.mem_neighborFinset _ _ _).mpr htp
        have hch_card_add : ch.card + 1 = (D.tree.neighborSet t).ncard := by
          rw [← SimpleGraph.coe_neighborFinset, ncard_coe_finset]
          exact Finset.card_erase_add_one hp_mem
        have hch_le : ch.card ≤ 2 := by
          have := D.degree_le_three t
          omega
        have hch_mem {c : ι} : c ∈ ch ↔ D.tree.Adj t c ∧ c ≠ p := by
          simp [ch, SimpleGraph.mem_neighborFinset, and_comm]
        have hch_parent {c : ι} (hc : c ∈ ch) : c ≠ r₀ ∧ D.isTree.parent r₀ c = t := by
          obtain ⟨htc, hcp⟩ := hch_mem.mp hc
          rcases (D.isTree.adj_iff_parent r₀).mp htc with ⟨_, hpt⟩ | hcr
          · exact absurd hpt.symm hcp
          · exact hcr
        have hch_fuel {c : ι} (hc : c ∈ ch) :
            Fintype.card ι - (D.isTree.pathTo r₀ c).length <
              Fintype.card ι - (D.isTree.pathTo r₀ t).length := by
          obtain ⟨hcr, hpct⟩ := hch_parent hc
          have hlen := D.isTree.length_pathTo_parent r₀ hcr
          rw [hpct] at hlen
          have hnd := (D.isTree.isPath_pathTo r₀ c).support_nodup
          have hle := hnd.length_le_card
          rw [SimpleGraph.Walk.length_support] at hle
          omega
        have hdecomp := D.isTree.treeSide_eq_insert_biUnion htp
        have hcut_decomp : D.cutSet t p =
            {a : α | (D.leaf a).val = t} ∪
              ⋃ c ∈ ch, D.cutSet c t := by
          ext a
          simp only [SubcubicLeafTree.cutSet, mem_ofPred_eq, hdecomp, mem_insert_iff, mem_iUnion,
            mem_union, hch_mem]
        have hnotleaf (hpos : 1 ≤ ch.card) : {a : α | (D.leaf a).val = t} = ∅ := by
          ext a
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
          intro hat
          have hle1 := (D.leaf a).property
          rw [hat] at hle1
          omega
        interval_cases hcard_ch : ch.card
        · -- `ch.card = 0`: `t` has degree `1`, so `t` is a leaf.
          have hdeg1 : (D.tree.neighborSet t).ncard ≤ 1 := by omega
          let a := D.leaf.symm ⟨t, hdeg1⟩
          have hch_empty : ch = ∅ := Finset.card_eq_zero.mp hcard_ch
          have hcut_eq : D.cutSet t p = {a} := by
            rw [hcut_decomp, hch_empty]
            ext b
            simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, union_empty,
              mem_ofPred_eq, mem_singleton_iff]
            exact ⟨fun hb => D.leaf.injective (Subtype.ext (hb.trans
                (congrArg Subtype.val (D.leaf.apply_symm_apply ⟨t, hdeg1⟩)).symm)),
              by rintro rfl; exact congrArg Subtype.val (D.leaf.apply_symm_apply ⟨t, hdeg1⟩)⟩
          refine ⟨.leaf a, hcut_eq ▸ isPartition_leaf a, fun S hS => ?_⟩
          cases hS
          exact ⟨t, p, htp, by rw [hcut_eq, leafSet_leaf]⟩
        · -- `ch.card = 1`: pass-through degree-2 node.
          obtain ⟨c₁, hc₁_eq⟩ := Finset.card_eq_one.mp hcard_ch
          have hc₁ : c₁ ∈ ch := hc₁_eq ▸ Finset.mem_singleton_self c₁
          obtain ⟨hc₁r, hpc₁⟩ := hch_parent hc₁
          obtain ⟨bt, hbt_part, hbt_sub⟩ := ih c₁ (hch_fuel hc₁) hc₁r
          rw [hpc₁] at hbt_part
          have hcut_eq : D.cutSet t p = D.cutSet c₁ t := by
            rw [hcut_decomp, hnotleaf (by omega), empty_union, hc₁_eq]
            simp
          exact ⟨bt, hcut_eq ▸ hbt_part, hbt_sub⟩
        · -- `ch.card = 2`: binary split into two disjoint child subtrees.
          obtain ⟨c₁, c₂, hc₁₂, hc_eq⟩ := Finset.card_eq_two.mp hcard_ch
          have hc₁ : c₁ ∈ ch := by rw [hc_eq]; simp
          have hc₂ : c₂ ∈ ch := by rw [hc_eq]; simp
          obtain ⟨hc₁r, hpc₁⟩ := hch_parent hc₁
          obtain ⟨hc₂r, hpc₂⟩ := hch_parent hc₂
          obtain ⟨bt₁, hbt₁_part, hbt₁_sub⟩ := ih c₁ (hch_fuel hc₁) hc₁r
          obtain ⟨bt₂, hbt₂_part, hbt₂_sub⟩ := ih c₂ (hch_fuel hc₂) hc₂r
          rw [hpc₁] at hbt₁_part
          rw [hpc₂] at hbt₂_part
          have hdisj_side := D.isTree.disjoint_treeSide_of_adj (hch_mem.mp hc₁).1
            (hch_mem.mp hc₂).1 hc₁₂
          have hdisj : Disjoint (D.cutSet c₁ t) (D.cutSet c₂ t) :=
            Set.disjoint_left.mpr fun a ha₁ ha₂ => Set.disjoint_left.mp hdisj_side ha₁ ha₂
          have hcut_eq : D.cutSet t p = D.cutSet c₁ t ∪ D.cutSet c₂ t := by
            rw [hcut_decomp, hnotleaf (by omega), empty_union, hc_eq]
            simp
          refine ⟨.node bt₁ bt₂, hcut_eq ▸ isPartition_node hbt₁_part hbt₂_part hdisj,
            fun S hS => ?_⟩
          cases hS with
          | here _ =>
            rw [leafSet_node, hbt₁_part.2, hbt₂_part.2, ← hcut_eq]
            exact ⟨t, p, htp, rfl⟩
          | left hs => exact hbt₁_sub S hs
          | right hs => exact hbt₂_sub S hs
    -- Combine `{a₀}` at `r₀` with `c₀`.
    have hc₀_ne : c₀ ≠ r₀ := hc₀_adj.ne'
    have hpc₀ : D.isTree.parent r₀ c₀ = r₀ :=
      (((D.isTree.adj_iff_parent r₀).mp hc₀_adj).resolve_left fun h => h.1 rfl).2
    obtain ⟨bt₀, hbt₀_part, hbt₀_sub⟩ := hrec c₀ hc₀_ne
    rw [hpc₀] at hbt₀_part
    have hr₀_side : D.isTree.treeSide r₀ c₀ = {r₀} := by
      rw [D.isTree.treeSide_eq_insert_biUnion hc₀_adj]
      have hemp : {c : ι | D.tree.Adj r₀ c ∧ c ≠ c₀} = ∅ := by
        ext c
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun hrc hne => hne (hc₀_uniq c hrc)
      simp [hemp]
    have hcut_r₀ : D.cutSet r₀ c₀ = {a₀} := by
      ext a
      simp only [SubcubicLeafTree.cutSet, hr₀_side, mem_ofPred_eq, mem_singleton_iff]
      exact ⟨fun h => D.leaf.injective (Subtype.ext h),
        fun h => congrArg (fun x => (D.leaf x).val) h⟩
    have hcut_c₀ : D.cutSet c₀ r₀ = ({a₀} : Set α)ᶜ := by
      rw [D.cutSet_compl_of_adj hc₀_adj, hcut_r₀]
    rw [hcut_c₀] at hbt₀_part
    have hdisj : Disjoint ({a₀} : Set α) ({a₀} : Set α)ᶜ := disjoint_compl_right
    have hunion : ({a₀} : Set α) ∪ ({a₀} : Set α)ᶜ = Set.univ := union_compl_self _
    refine ⟨.node (.leaf a₀) bt₀, hunion ▸ isPartition_node (isPartition_leaf a₀) hbt₀_part hdisj,
      fun S hS => ?_⟩
    cases hS with
    | here _ =>
      left
      rw [leafSet_node, leafSet_leaf, hbt₀_part.2, hunion]
    | left hs =>
      cases hs
      exact Or.inr ⟨r₀, c₀, hc₀_adj, by rw [hcut_r₀, leafSet_leaf]⟩
    | right hs =>
      exact Or.inr (hbt₀_sub S hs)

end BinTree

end Carving

/-! ### Carving decompositions and branch decompositions of multigraphs -/

namespace Multigraph

open Carving

variable {V E ι κ : Type*}

/-- Edge cuts are invariant under vertex complement. -/
@[simp] theorem edgeCut_compl (G : Multigraph V E) (S : Set V) : G.edgeCut Sᶜ = G.edgeCut S := by
  ext e
  simp only [mem_edgeCut, mem_compl_iff]
  tauto

/-- A *carving decomposition* of `G` indexed by `ι`: an unrooted subcubic tree whose leaves are in
bijection with `V`. -/
@[nolint unusedArguments]
structure CarvingDecomposition (_G : Multigraph V E) (ι : Type*) extends SubcubicLeafTree V ι

/-- Width of a carving decomposition on finitely many tree nodes. -/
noncomputable def CarvingDecomposition.width {G : Multigraph V E} [Fintype ι]
    (D : G.CarvingDecomposition ι) : ℕ :=
  D.toSubcubicLeafTree.costWidth fun S => (G.edgeCut S).ncard

/-- Reindex a carving decomposition along an equivalence of tree vertices. -/
def CarvingDecomposition.reindex {G : Multigraph V E} (D : G.CarvingDecomposition ι) (e : ι ≃ κ) :
    G.CarvingDecomposition κ :=
  ⟨D.toSubcubicLeafTree.reindex e⟩

@[simp] theorem CarvingDecomposition.width_reindex {G : Multigraph V E} [Fintype ι] [Fintype κ]
    (D : G.CarvingDecomposition ι) (e : ι ≃ κ) :
    (D.reindex e).width = D.width :=
  D.toSubcubicLeafTree.costWidth_reindex e _

/-- Extended carving-width of `G`: minimum width over `Fin n`-indexed carving decompositions, or
`⊤` when none exists (i.e. when `V` is empty or infinite). -/
noncomputable def ecarvingWidth (G : Multigraph V E) : ℕ∞ :=
  ⨅ D : (Σ n : ℕ, G.CarvingDecomposition (Fin n)), (D.2.width : ℕ∞)

/-- Carving-width of `G`: minimum width of a finite carving decomposition (`0` when `|V| ≤ 1`). -/
noncomputable def carvingWidth (G : Multigraph V E) : ℕ :=
  G.ecarvingWidth.toNat

theorem ecarvingWidth_le_width (G : Multigraph V E) [Fintype ι]
    (D : G.CarvingDecomposition ι) : G.ecarvingWidth ≤ D.width := by
  refine (iInf_le _ ⟨_, D.reindex (Fintype.equivFin ι)⟩).trans_eq ?_
  simp

/-- Bound `G.carvingWidth` from a `BinTree V` partitioning `Set.univ`. -/
theorem carvingWidth_le_of_binTree (G : Multigraph V E) {t : BinTree V}
    (hp : t.IsPartition Set.univ) {k : ℕ} (hk : ∀ S, t.IsSubtreeSet S → (G.edgeCut S).ncard ≤ k) :
    G.carvingWidth ≤ k := by
  obtain ⟨ι, hfin, D, hD⟩ := t.exists_subcubicLeafTree_of_binTree hp
  let := hfin
  let Dc : G.CarvingDecomposition ι := ⟨D⟩
  have hw : Dc.width ≤ k := by
    refine D.costWidth_le_iff.mpr fun u v huv => ?_
    rcases hD u v huv with hS | hSc
    · exact hk _ hS
    · rw [← G.edgeCut_compl]
      exact hk _ hSc
  have he : G.ecarvingWidth ≤ (k : ℕ∞) :=
    (G.ecarvingWidth_le_width Dc).trans (ENat.natCast_le_natCast.mpr hw)
  exact ENat.toNat_le_of_le_natCast he

theorem ecarvingWidth_ne_top (G : Multigraph V E) [Finite V] [Nonempty V] :
    G.ecarvingWidth ≠ ⊤ := by
  have hv : (Set.univ : Set V).Finite := Set.finite_univ
  cases h : BinTree.ofSet (Set.univ : Set V) hv with
  | none =>
    have hemp := BinTree.ofSet_spec (Set.univ : Set V) hv
    rw [h] at hemp
    exact absurd hemp Set.univ_nonempty.ne_empty
  | some t =>
    have hp := BinTree.ofSet_spec (Set.univ : Set V) hv
    rw [h] at hp
    obtain ⟨ι, hfin, D, -⟩ := t.exists_subcubicLeafTree_of_binTree hp
    let := hfin
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) (G.ecarvingWidth_le_width ⟨D⟩)

/-- Every nonempty finite multigraph admits a `BinTree V` partitioning `Set.univ` of maximum cut
at most `G.carvingWidth`. -/
theorem exists_binTree_carvingWidth (G : Multigraph V E) [Finite V] [Nonempty V] :
    ∃ t : BinTree V, t.IsPartition Set.univ ∧
      ∀ S, t.IsSubtreeSet S → (G.edgeCut S).ncard ≤ G.carvingWidth := by
  have hne := G.ecarvingWidth_ne_top
  have : Nonempty (Σ n : ℕ, G.CarvingDecomposition (Fin n)) := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    exact hne (iInf_of_empty _)
  obtain ⟨⟨n, D⟩, hD⟩ := ciInf_mem (fun D : (Σ n : ℕ, G.CarvingDecomposition (Fin n)) =>
    (D.2.width : ℕ∞))
  have hD' : (D.width : ℕ∞) = G.ecarvingWidth := hD
  have hwidth : D.width = G.carvingWidth := by
    rw [carvingWidth, ← hD', ENat.toNat_natCast]
  obtain ⟨t, hp, ht⟩ := BinTree.exists_binTree_of_subcubicLeafTree D.toSubcubicLeafTree
  refine ⟨t, hp, fun S hS => ?_⟩
  rcases ht S hS with rfl | ⟨u, v, huv, rfl⟩
  · simp
  · rw [← hwidth]
    exact D.toSubcubicLeafTree.cost_cutSet_le (fun X => (G.edgeCut X).ncard) huv

/-! #### Middle sets and branchwidth -/

/-- The *middle set* of an edge set `A ⊆ E`: the vertices incident to both `A` and `Aᶜ`. -/
def middleSet (G : Multigraph V E) (A : Set E) : Set V :=
  {v : V | (G.incidenceSet v ∩ A).Nonempty ∧ (G.incidenceSet v ∩ Aᶜ).Nonempty}

@[simp] theorem middleSet_empty (G : Multigraph V E) : G.middleSet ∅ = ∅ := by
  ext v; simp [middleSet]

@[simp] theorem middleSet_univ (G : Multigraph V E) : G.middleSet Set.univ = ∅ := by
  ext v; simp [middleSet]

@[simp] theorem middleSet_compl (G : Multigraph V E) (A : Set E) :
    G.middleSet Aᶜ = G.middleSet A := by
  ext v
  simp [middleSet, and_comm]

/-- A *branch decomposition* of `G` indexed by `ι`: an unrooted subcubic tree whose leaves are in
bijection with `E`. -/
@[nolint unusedArguments]
structure BranchDecomposition (_G : Multigraph V E) (ι : Type*) extends SubcubicLeafTree E ι

/-- Width of a branch decomposition on finitely many tree nodes. -/
noncomputable def BranchDecomposition.width {G : Multigraph V E} [Fintype ι]
    (D : G.BranchDecomposition ι) : ℕ :=
  D.toSubcubicLeafTree.costWidth fun A => (G.middleSet A).ncard

/-- Reindex a branch decomposition along an equivalence of tree vertices. -/
def BranchDecomposition.reindex {G : Multigraph V E} (D : G.BranchDecomposition ι) (e : ι ≃ κ) :
    G.BranchDecomposition κ :=
  ⟨D.toSubcubicLeafTree.reindex e⟩

@[simp] theorem BranchDecomposition.width_reindex {G : Multigraph V E} [Fintype ι]
    [Fintype κ] (D : G.BranchDecomposition ι) (e : ι ≃ κ) :
    (D.reindex e).width = D.width :=
  D.toSubcubicLeafTree.costWidth_reindex e _

/-- Extended branchwidth of `G`: minimum width over `Fin n`-indexed branch decompositions, or `⊤`
when `E` is empty or infinite. -/
noncomputable def ebranchwidth (G : Multigraph V E) : ℕ∞ :=
  ⨅ D : (Σ n : ℕ, G.BranchDecomposition (Fin n)), (D.2.width : ℕ∞)

/-- Branchwidth of `G`: minimum width of a finite branch decomposition (`0` when `|E| ≤ 1`). -/
noncomputable def branchwidth (G : Multigraph V E) : ℕ :=
  G.ebranchwidth.toNat

theorem ebranchwidth_le_width (G : Multigraph V E) [Fintype ι]
    (D : G.BranchDecomposition ι) : G.ebranchwidth ≤ D.width := by
  refine (iInf_le _ ⟨_, D.reindex (Fintype.equivFin ι)⟩).trans_eq ?_
  simp

/-- Bound `G.branchwidth` from a `BinTree E` partitioning `Set.univ`. -/
theorem branchwidth_le_of_binTree (G : Multigraph V E) {t : BinTree E}
    (hp : t.IsPartition Set.univ) {k : ℕ} (hk : ∀ A, t.IsSubtreeSet A → (G.middleSet A).ncard ≤ k) :
    G.branchwidth ≤ k := by
  obtain ⟨ι, hfin, D, hD⟩ := t.exists_subcubicLeafTree_of_binTree hp
  let := hfin
  let Db : G.BranchDecomposition ι := ⟨D⟩
  have hw : Db.width ≤ k := by
    refine D.costWidth_le_iff.mpr fun u v huv => ?_
    rcases hD u v huv with hA | hAc
    · exact hk _ hA
    · rw [← G.middleSet_compl]
      exact hk _ hAc
  have he : G.ebranchwidth ≤ (k : ℕ∞) :=
    (G.ebranchwidth_le_width Db).trans (ENat.natCast_le_natCast.mpr hw)
  exact ENat.toNat_le_of_le_natCast he

/-- Grouping edges by their source vertex: every vertex in the middle set of `{e | G.src e ∈ X}` is
the target of an edge in `G.edgeCut X`. -/
private theorem middleSet_src_preimage_subset (G : Multigraph V E) (X : Set V) :
    G.middleSet {e : E | G.src e ∈ X} ⊆ G.tgt '' G.edgeCut X := by
  rintro w ⟨⟨e₁, he₁w, he₁X⟩, ⟨e₂, he₂w, he₂X⟩⟩
  simp only [mem_ofPred_eq, mem_compl_iff] at he₁X he₂X
  by_cases hw : w ∈ X
  · have hsrc_ne : G.src e₂ ≠ w := fun h => he₂X (h ▸ hw)
    have htgt : G.tgt e₂ = w := he₂w.resolve_left hsrc_ne
    refine ⟨e₂, ?_, htgt⟩
    rw [mem_edgeCut, htgt]
    exact fun h => he₂X (h.mpr hw)
  · have hsrc_ne : G.src e₁ ≠ w := fun h => hw (h ▸ he₁X)
    have htgt : G.tgt e₁ = w := he₁w.resolve_left hsrc_ne
    refine ⟨e₁, ?_, htgt⟩
    rw [mem_edgeCut, htgt]
    exact fun h => hw (h.mp he₁X)

/-- Expand a vertex `BinTree V` into an optional edge `BinTree E` by replacing each leaf `v` with a
caterpillar over `{e : E | G.src e = v}`. -/
private noncomputable def expandSrcEdges (G : Multigraph V E) [Finite E] :
    BinTree V → Option (BinTree E)
  | .leaf v => BinTree.ofSet {e : E | G.src e = v}
  | .node l r => BinTree.joinOpt (G.expandSrcEdges l) (G.expandSrcEdges r)

private theorem expandSrcEdges_spec (G : Multigraph V E) [Finite E] (t : BinTree V) {X : Set V}
    (hp : t.IsPartition X) :
    match G.expandSrcEdges t with
    | none => {e : E | G.src e ∈ X} = ∅
    | some te => te.IsPartition {e : E | G.src e ∈ X} ∧
        ∀ A, te.IsSubtreeSet A →
          (∃ Y, t.IsSubtreeSet Y ∧ A = {e : E | G.src e ∈ Y}) ∨
          ∃ v : V, A ⊆ {e : E | G.src e = v} := by
  induction t generalizing X with
  | leaf v =>
    have hX : X = {v} := by simpa using hp.2.symm
    subst hX
    dsimp only [expandSrcEdges]
    have hspec := BinTree.ofSet_spec {e : E | G.src e = v}
    cases h : BinTree.ofSet {e : E | G.src e = v} with
    | none =>
      rw [h] at hspec
      simpa using hspec
    | some te =>
      rw [h] at hspec
      refine ⟨by simpa using hspec, fun A hA => Or.inr ⟨v, ?_⟩⟩
      exact hA.subset_leafSet.trans hspec.2.le
  | node l r ihl ihr =>
    have hl : l.IsPartition l.leafSet := ⟨(List.nodup_append.mp hp.1).1, rfl⟩
    have hr : r.IsPartition r.leafSet := ⟨(List.nodup_append.mp hp.1).2.1, rfl⟩
    have hdisjV : Disjoint l.leafSet r.leafSet :=
      Set.disjoint_left.mpr fun x hx hy => (List.nodup_append.mp hp.1).2.2 x hx x hy rfl
    have hdisjE : Disjoint {e : E | G.src e ∈ l.leafSet} {e : E | G.src e ∈ r.leafSet} :=
      Set.disjoint_left.mpr fun e hx hy => Set.disjoint_left.mp hdisjV hx hy
    have hX : X = l.leafSet ∪ r.leafSet := by
      rw [← hp.2, BinTree.leafSet_node]
    subst hX
    have ihl' := ihl hl
    have ihr' := ihr hr
    have hjoin := BinTree.joinOpt_spec hdisjE
      (o₁ := G.expandSrcEdges l) (o₂ := G.expandSrcEdges r)
      (by cases h1 : G.expandSrcEdges l <;> rw [h1] at ihl'; exacts [ihl', ihl'.1])
      (by cases h2 : G.expandSrcEdges r <;> rw [h2] at ihr'; exacts [ihr', ihr'.1])
    have hunion : {e : E | G.src e ∈ l.leafSet} ∪ {e : E | G.src e ∈ r.leafSet} =
        {e : E | G.src e ∈ l.leafSet ∪ r.leafSet} := by
      ext e; simp [mem_union]
    change match BinTree.joinOpt (G.expandSrcEdges l) (G.expandSrcEdges r) with
      | none => _ | some te => _
    cases hj : BinTree.joinOpt (G.expandSrcEdges l) (G.expandSrcEdges r) with
    | none =>
      rw [hj] at hjoin
      rwa [← hunion]
    | some te =>
      rw [hj, hunion] at hjoin
      refine ⟨hjoin.1, fun A hA => ?_⟩
      rcases hjoin.2 A hA with rfl | ⟨t₁, ht₁, hs₁⟩ | ⟨t₂, ht₂, hs₂⟩
      · exact Or.inl ⟨l.leafSet ∪ r.leafSet, by simpa using BinTree.IsSubtreeSet.here (.node l r),
          rfl⟩
      · rw [ht₁] at ihl'
        exact (ihl'.2 A hs₁).imp (fun ⟨Y, hY, h⟩ => ⟨Y, .left hY, h⟩) id
      · rw [ht₂] at ihr'
        exact (ihr'.2 A hs₂).imp (fun ⟨Y, hY, h⟩ => ⟨Y, .right hY, h⟩) id

/-- **Branchwidth is at most carving-width on finite loopless cubic multigraphs.** -/
theorem branchwidth_le_carvingWidth (G : Multigraph V E) [Finite V] [Finite E] (hloop : G.Loopless)
    (h3 : ∀ v : V, (G.incidenceSet v).ncard = 3) :
    G.branchwidth ≤ G.carvingWidth := by
  classical
  by_cases hV : Nonempty V
  · have := hV
    obtain ⟨v₀⟩ := hV
    obtain ⟨t, hp, hcw⟩ := G.exists_binTree_carvingWidth
    have hsing (v : V) : t.IsSubtreeSet {v} :=
      BinTree.IsSubtreeSet.singleton_of_mem (show v ∈ t.leafSet from hp.2 ▸ trivial)
    have hmid (Y : Set V) (hY : t.IsSubtreeSet Y) :
        (G.middleSet {e : E | G.src e ∈ Y}).ncard ≤ G.carvingWidth :=
      ((ncard_le_ncard (G.middleSet_src_preimage_subset Y)).trans
        (ncard_image_le (toFinite _))).trans (hcw Y hY)
    have hcw_ge_three : 3 ≤ G.carvingWidth := by
      have hsub := hcw {v₀} (hsing v₀)
      rwa [G.edgeCut_singleton hloop v₀, h3 v₀] at hsub
    have hspec := G.expandSrcEdges_spec t hp
    obtain ⟨e₀, _⟩ : (G.incidenceSet v₀).Nonempty :=
      (ncard_pos (toFinite _)).mp (by rw [h3 v₀]; omega)
    cases hexp : G.expandSrcEdges t with
    | none =>
      rw [hexp] at hspec
      exact (eq_empty_iff_forall_notMem.mp hspec e₀ trivial).elim
    | some te =>
      rw [hexp] at hspec
      have huniv : {e : E | G.src e ∈ (Set.univ : Set V)} = Set.univ := by ext; simp
      rw [huniv] at hspec
      refine G.branchwidth_le_of_binTree hspec.1 fun A hA => ?_
      rcases hspec.2 A hA with ⟨Y, hY, rfl⟩ | ⟨v, hv⟩
      · exact hmid Y hY
      · by_cases hfull : A = {e : E | G.src e = v}
        · subst hfull
          exact hmid {v} (hsing v)
        · have hssub : A ⊂ {e : E | G.src e = v} := ssubset_of_subset_of_ne hv hfull
          have hle_inc : {e : E | G.src e = v} ⊆ G.incidenceSet v := fun e he => Or.inl he
          have hcard_lt : A.ncard < 3 :=
            (ncard_lt_ncard hssub).trans_le ((ncard_le_ncard hle_inc).trans_eq (h3 v))
          have hmid_sub : G.middleSet A ⊆ insert v (G.tgt '' A) := by
            rintro w ⟨⟨e, hew, heA⟩, -⟩
            rcases hew with rfl | rfl
            · exact Or.inl (hv heA)
            · exact Or.inr ⟨e, heA, rfl⟩
          have hcard_ins : (insert v (G.tgt '' A)).ncard ≤ 3 := by
            have h1 := ncard_insert_le v (G.tgt '' A)
            have h2 := ncard_image_le (f := G.tgt) (toFinite A)
            omega
          exact ((ncard_le_ncard hmid_sub).trans hcard_ins).trans hcw_ge_three
  · have : IsEmpty V := not_nonempty_iff.mp hV
    have : IsEmpty E := ⟨fun e => isEmptyElim (G.src e)⟩
    have : IsEmpty (Σ n : ℕ, G.BranchDecomposition (Fin n)) := by
      refine ⟨fun ⟨n, D⟩ => ?_⟩
      obtain ⟨w₀⟩ := D.isTree.connected.nonempty
      have hsum : ∑ v : Fin n, (D.tree.neighborFinset v).card =
          2 * (D.tree.edgeFinset).card := SimpleGraph.sum_degrees_eq_twice_card_edges D.tree
      have hcard_edges : (D.tree.edgeFinset).card + 1 = n := by
        have := D.isTree.card_edgeFinset
        simp only [Fintype.card_fin] at this
        omega
      have hall_gt_one : ∀ v : Fin n, 2 ≤ (D.tree.neighborFinset v).card := by
        intro v
        by_contra hle
        have hnc : (D.tree.neighborSet v).ncard ≤ 1 := by
          rw [← SimpleGraph.coe_neighborFinset, ncard_coe_finset]
          omega
        exact isEmptyElim (D.leaf.symm ⟨v, hnc⟩)
      have hge : 2 * n ≤ ∑ v : Fin n, (D.tree.neighborFinset v).card := by
        calc 2 * n = ∑ _ : Fin n, 2 := by simp [mul_comm]
          _ ≤ ∑ v : Fin n, (D.tree.neighborFinset v).card :=
            Finset.sum_le_sum fun v _ => hall_gt_one v
      omega
    have htop : G.ebranchwidth = ⊤ := by
      rw [ebranchwidth]
      exact iInf_of_empty _
    simp [branchwidth, htop]

end Multigraph

end Cslib.Circuits.Frontier
