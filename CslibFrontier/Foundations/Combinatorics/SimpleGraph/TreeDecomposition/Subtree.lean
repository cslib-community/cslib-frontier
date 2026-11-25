/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/TreeDecomposition/Subtree.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.TreeDecomposition.Rooted
import CslibFrontier.Tactic.FinIndex

/-!
# Subtrees of rooted tree decompositions

For a rooted tree decomposition `R : G.RootedTreeDecomposition n`, this file describes the
subtree below a node: its descendants, its children and the vertices in its bags. These are the
separation facts used by dynamic programming over tree decompositions. A bag separates the
vertices first introduced below each child from the rest of the graph, and different children
introduce disjoint sets of vertices.

## Main definitions

* `SimpleGraph.RootedTreeDecomposition.IsDescendant R j i`: climbing from `j` reaches `i`.
* `SimpleGraph.RootedTreeDecomposition.children R i`: the children of node `i`.
* `SimpleGraph.RootedTreeDecomposition.subtreeVerts R i`: the vertices in the bags of the subtree
  rooted at `i`.

## Main results

* `SimpleGraph.RootedTreeDecomposition.mem_bag_of_mem_subtreeVerts_of_mem_bag_parent`: a vertex
  below a child `c` that also lies in the parent's bag lies in the bag of `c`.
* `SimpleGraph.RootedTreeDecomposition.mem_subtreeVerts_of_adj`: a neighbour of a vertex below `c`
  that is not in the parent's bag also lies below `c`.
* `SimpleGraph.RootedTreeDecomposition.eq_of_mem_subtreeVerts_of_mem_children` and
  `SimpleGraph.RootedTreeDecomposition.exists_mem_children_of_mem_subtreeVerts`: the vertices
  below `i` that are not in its bag are partitioned among the children of `i`.

## References

* [M. Cygan et al., *Parameterized Algorithms*, Section 7.2][CyganEtAl2015]
-/

public section

namespace SimpleGraph.RootedTreeDecomposition

universe uV

variable {V : Type uV} {G : SimpleGraph V} {n : ℕ} (R : G.RootedTreeDecomposition n)

/-! ### Descendants -/

/-- `j` lies in the subtree rooted at `i`: climbing from `j` reaches `i`. -/
def IsDescendant (j i : Fin (n + 1)) : Prop :=
  ∃ a, R.parent^[a] j = i

theorem isDescendant_refl (i : Fin (n + 1)) : R.IsDescendant i i :=
  ⟨0, rfl⟩

theorem isDescendant_parent (i : Fin (n + 1)) : R.IsDescendant i (R.parent i) :=
  ⟨1, rfl⟩

variable {R}

theorem IsDescendant.trans {i j k : Fin (n + 1)} (hkj : R.IsDescendant k j)
    (hji : R.IsDescendant j i) : R.IsDescendant k i :=
  let ⟨a, ha⟩ := hkj; let ⟨b, hb⟩ := hji
  ⟨b + a, by rw [Function.iterate_add_apply, ha, hb]⟩

theorem IsDescendant.le {i j : Fin (n + 1)} (h : R.IsDescendant j i) : i ≤ j :=
  let ⟨a, ha⟩ := h; ha ▸ R.parent_iterate_le a j

theorem IsDescendant.antisymm {i j : Fin (n + 1)} (hji : R.IsDescendant j i)
    (hij : R.IsDescendant i j) : i = j :=
  le_antisymm hji.le hij.le

/-- Two ancestors of a common node are comparable. -/
theorem IsDescendant.total {i j k : Fin (n + 1)} (hi : R.IsDescendant k i)
    (hj : R.IsDescendant k j) : R.IsDescendant i j ∨ R.IsDescendant j i := by
  obtain ⟨a, rfl⟩ := hi
  obtain ⟨b, rfl⟩ := hj
  exact (le_total a b).imp
    (fun hab => let ⟨c, hc⟩ := Nat.exists_eq_add_of_le' hab
      ⟨c, by rw [hc, Function.iterate_add_apply]⟩)
    (fun hab => let ⟨c, hc⟩ := Nat.exists_eq_add_of_le' hab
      ⟨c, by rw [hc, Function.iterate_add_apply]⟩)

variable (R)

private theorem parent_iterate_val (j : Fin (n + 1)) (a : ℕ) :
    (R.parent^[a] j).val + a ≤ j.val ∨ R.parent^[a] j = 0 := by
  induction a with
  | zero => exact .inl le_rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    by_cases hx : R.parent^[a] j = 0
    · exact .inr (by rw [hx, R.parent_zero])
    · have hlt := Fin.lt_def.1 (R.parent_lt _ hx)
      exact .inl (ih.elim (by omega) fun h => absurd h hx)

/-- Every node lies in the subtree of the root. -/
theorem isDescendant_zero (j : Fin (n + 1)) : R.IsDescendant j 0 :=
  ⟨j.val, (R.parent_iterate_val j j.val).elim (fun _ => by fin_index) id⟩

/-! ### Children -/

/-- The children of node `i`: the nonroot nodes whose parent is `i`. -/
def children (i : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun c => c ≠ 0 ∧ R.parent c = i

variable {R}

theorem mem_children {i c : Fin (n + 1)} : c ∈ R.children i ↔ c ≠ 0 ∧ R.parent c = i := by
  simp [children]

theorem lt_of_mem_children {i c : Fin (n + 1)} (h : c ∈ R.children i) : i < c :=
  let ⟨hc, h⟩ := mem_children.1 h; h ▸ R.parent_lt c hc

theorem isDescendant_of_mem_children {i c : Fin (n + 1)} (h : c ∈ R.children i) :
    R.IsDescendant c i :=
  ⟨1, (mem_children.1 h).2⟩

/-- A strict descendant of `i` lies below some child of `i`. -/
theorem exists_mem_children_of_isDescendant {i j : Fin (n + 1)} (h : R.IsDescendant j i)
    (hne : j ≠ i) : ∃ c ∈ R.children i, R.IsDescendant j c := by
  obtain ⟨a, ha⟩ := h
  induction a with
  | zero => exact absurd ha hne
  | succ a ih =>
    rw [Function.iterate_succ_apply'] at ha
    exact if hx : R.parent^[a] j = i then ih hx
      else ⟨R.parent^[a] j, mem_children.2 ⟨fun h0 => hx (by rw [← ha, h0, R.parent_zero]), ha⟩,
        a, rfl⟩

private theorem eq_of_mem_children_of_isDescendant {i c c' : Fin (n + 1)}
    (hc : c ∈ R.children i) (hc' : c' ∈ R.children i) (h : R.IsDescendant c c') : c = c' := by
  by_contra hne
  rcases h with ⟨_ | a, ha⟩
  · exact hne ha
  · rw [Function.iterate_succ_apply, (mem_children.1 hc).2] at ha
    exact (lt_of_mem_children hc').not_ge (ha ▸ R.parent_iterate_le a i)

/-- A node lies below at most one child of a given node. -/
theorem eq_of_mem_children {i c c' j : Fin (n + 1)} (hc : c ∈ R.children i)
    (hc' : c' ∈ R.children i) (hj : R.IsDescendant j c) (hj' : R.IsDescendant j c') : c = c' :=
  (hj.total hj').elim (eq_of_mem_children_of_isDescendant hc hc') fun h =>
    (eq_of_mem_children_of_isDescendant hc' hc h).symm

/-! ### Vertices of a subtree -/

variable (R)

open scoped Classical in
/-- The vertices in the bags of the subtree rooted at `i`. -/
noncomputable def subtreeVerts (i : Fin (n + 1)) : Finset V :=
  (Finset.univ.filter (R.IsDescendant · i)).biUnion R.bag

variable {R}

theorem mem_subtreeVerts {i : Fin (n + 1)} {v : V} :
    v ∈ R.subtreeVerts i ↔ ∃ j, R.IsDescendant j i ∧ v ∈ R.bag j := by
  classical simp [subtreeVerts]

variable (R)

theorem bag_subset_subtreeVerts (i : Fin (n + 1)) : R.bag i ⊆ R.subtreeVerts i :=
  fun _ hv => mem_subtreeVerts.2 ⟨i, R.isDescendant_refl i, hv⟩

/-- Every vertex lies in the subtree of the root. -/
theorem mem_subtreeVerts_zero (v : V) : v ∈ R.subtreeVerts 0 :=
  let ⟨i, hi⟩ := R.exists_mem_bag v; mem_subtreeVerts.2 ⟨i, R.isDescendant_zero i, hi⟩

variable {R}

theorem subtreeVerts_mono {i j : Fin (n + 1)} (h : R.IsDescendant j i) :
    R.subtreeVerts j ⊆ R.subtreeVerts i :=
  fun _ hv => let ⟨d, hd, hv⟩ := mem_subtreeVerts.1 hv; mem_subtreeVerts.2 ⟨d, hd.trans h, hv⟩

theorem isDescendant_top {v : V} {d : Fin (n + 1)} (hd : v ∈ R.bag d) :
    R.IsDescendant d (R.top v) :=
  R.exists_iterate_eq_top hd

/-- Every bag between a node containing `v` and the topmost node for `v` contains `v`. -/
theorem mem_bag_of_isDescendant {v : V} {c d : Fin (n + 1)} (hd : v ∈ R.bag d)
    (hdc : R.IsDescendant d c) (hc : R.IsDescendant c (R.top v)) : v ∈ R.bag c := by
  obtain ⟨a, rfl⟩ := hdc
  obtain ⟨b, hb⟩ := hc
  exact R.mem_bag_parent_iterate hd (by rwa [← Function.iterate_add_apply] at hb)
    (Nat.le_add_left a b)

/-- The parent's bag meets the subtree of `c` only inside the bag of `c`. -/
theorem mem_bag_of_mem_subtreeVerts_of_mem_bag_parent {v : V} {c : Fin (n + 1)}
    (hv : v ∈ R.subtreeVerts c) (hp : v ∈ R.bag (R.parent c)) : v ∈ R.bag c := by
  by_cases hc : c = 0
  · subst hc; rwa [R.parent_zero] at hp
  obtain ⟨d, hdc, hd⟩ := mem_subtreeVerts.1 hv
  exact (hdc.total (isDescendant_top hd)).elim (mem_bag_of_isDescendant hd hdc) fun h =>
    absurd (R.parent_lt c hc) (not_lt.2 (h.le.trans (isDescendant_top hp).le))

/-- A vertex below `c` that is not in the parent's bag has its topmost node below `c`. -/
theorem isDescendant_top_of_notMem_bag_parent {v : V} {c : Fin (n + 1)}
    (hv : v ∈ R.subtreeVerts c) (hp : v ∉ R.bag (R.parent c)) : R.IsDescendant (R.top v) c := by
  obtain ⟨d, hdc, hd⟩ := mem_subtreeVerts.1 hv
  rcases hdc.total (isDescendant_top hd) with ⟨_ | a, ha⟩ | h
  · exact ⟨0, ha.symm⟩
  · exact absurd (mem_bag_of_isDescendant hd (hdc.trans (R.isDescendant_parent c))
      ⟨a, by rwa [Function.iterate_succ_apply] at ha⟩) hp
  · exact h

/-- A vertex below `c` that is not in the parent's bag occurs only in bags below `c`. -/
theorem isDescendant_of_mem_bag_of_notMem_bag_parent {v : V} {c d : Fin (n + 1)}
    (hv : v ∈ R.subtreeVerts c) (hp : v ∉ R.bag (R.parent c)) (hd : v ∈ R.bag d) :
    R.IsDescendant d c :=
  (isDescendant_top hd).trans (isDescendant_top_of_notMem_bag_parent hv hp)

/-- The parent's bag separates the vertices introduced below `c` from the rest of the graph:
every neighbour of such a vertex also lies below `c`. -/
theorem mem_subtreeVerts_of_adj {u x : V} {c : Fin (n + 1)} (hu : u ∈ R.subtreeVerts c)
    (hp : u ∉ R.bag (R.parent c)) (hux : G.Adj u x) : x ∈ R.subtreeVerts c :=
  let ⟨d, hud, hxd⟩ := R.exists_adj_mem_bag hux
  mem_subtreeVerts.2 ⟨d, isDescendant_of_mem_bag_of_notMem_bag_parent hu hp hud, hxd⟩

theorem subtreeVerts_subset_of_mem_children {i c : Fin (n + 1)} (hc : c ∈ R.children i) :
    R.subtreeVerts c ⊆ R.subtreeVerts i :=
  subtreeVerts_mono (isDescendant_of_mem_children hc)

/-- Different children of `i` introduce disjoint sets of vertices outside the bag of `i`. -/
theorem eq_of_mem_subtreeVerts_of_mem_children {v : V} {i c c' : Fin (n + 1)}
    (hc : c ∈ R.children i) (hc' : c' ∈ R.children i) (hv : v ∈ R.subtreeVerts c)
    (hv' : v ∈ R.subtreeVerts c') (hvi : v ∉ R.bag i) : c = c' := by
  obtain ⟨d, -, hd⟩ := mem_subtreeVerts.1 hv
  exact eq_of_mem_children hc hc'
    (isDescendant_of_mem_bag_of_notMem_bag_parent hv (by rwa [(mem_children.1 hc).2]) hd)
    (isDescendant_of_mem_bag_of_notMem_bag_parent hv' (by rwa [(mem_children.1 hc').2]) hd)

/-- Every vertex below `i` that is not in the bag of `i` lies below some child of `i`. -/
theorem exists_mem_children_of_mem_subtreeVerts {v : V} {i : Fin (n + 1)}
    (hv : v ∈ R.subtreeVerts i) (hvi : v ∉ R.bag i) : ∃ c ∈ R.children i, v ∈ R.subtreeVerts c := by
  obtain ⟨d, hdi, hd⟩ := mem_subtreeVerts.1 hv
  obtain ⟨c, hc, hdc⟩ := exists_mem_children_of_isDescendant hdi (fun h => hvi (h ▸ hd))
  exact ⟨c, hc, mem_subtreeVerts.2 ⟨d, hdc, hd⟩⟩

end SimpleGraph.RootedTreeDecomposition
