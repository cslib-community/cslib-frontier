/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/TreeDecomposition/Nice.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Acyclic
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.TreeDecomposition.Subtree
public import Mathlib.Data.Finset.Sort

/-!
# Nice tree decompositions

A *nice tree decomposition* (`SimpleGraph.NiceTreeDecomposition G`) is a rooted binary tree
decomposition whose root and leaves have empty bags and whose every internal node is of three types
([CyganEtAl2015]):

* **Leaf**: no children, empty bag `∅`.
* **Introduce `v`**: one child `child` with `v` outside `child.subtreeVerts` and
  `bag = insert v child.bag`.
* **Forget `v`**: one child `child` with `v ∈ child.bag` and `bag = child.bag.erase v`.
* **Join**: two children `left`, `right` with `left.bag = right.bag = bag` and
  `Disjoint (left.subtreeVerts \ left.bag) right.subtreeVerts`.

We model the syntax algebraically as `SimpleGraph.NiceTree V`, define its validity
(`NiceTree.LocalValid`, `NiceTree.CoversFinset`) and conversion to
`SimpleGraph.RootedTreeDecomposition` (`NiceTree.toRootedTreeDecomposition`), and prove that every
finite clique lies in some bag (`NiceTree.exists_coversFinset_of_isClique`). Conversely,
`RootedTreeDecomposition.prune` contracts redundant subset bags so that a finite vertex type
leaves at most `card V + 1` nodes without increasing width, and `RootedTreeDecomposition.toNiceTree`
(computable when `[LinearOrder V]`, with noncomputable `[DecidableEq V]` counterpart
`RootedTreeDecomposition.toNice`) converts any finite rooted or unrooted tree decomposition into a
`NiceTreeDecomposition G` with width at most the original width and at most
`(3 * width + 5) * (card V + 1)` nodes.

## Main definitions

* `SimpleGraph.NiceTree`: algebraic syntax of leaf/introduce/forget/join tree decompositions.
* `SimpleGraph.NiceTreeDecomposition`: bundled nice tree decomposition of `G` with empty root bag.
* `SimpleGraph.NiceTree.toRootedTreeDecomposition`: parent-array rooted decomposition of a valid
  `NiceTree`.
* `SimpleGraph.RootedTreeDecomposition.prune`: contraction eliminating redundant subset children,
  leaving at most `Fintype.card V + 1` nodes.
* `SimpleGraph.RootedTreeDecomposition.toNiceTree`, `SimpleGraph.RootedTreeDecomposition.toNice`,
  `SimpleGraph.TreeDecomposition.exists_niceTreeDecomposition`: conversion to a nice tree
  decomposition without increasing width.

## Main results

* `SimpleGraph.NiceTree.exists_coversFinset_of_isClique`: every finite clique lies in some bag.
* `SimpleGraph.RootedTreeDecomposition.prune_width_le`,
  `SimpleGraph.RootedTreeDecomposition.prune_nodes_le`: width and `O(|V|)` node bounds for pruning.
* `SimpleGraph.RootedTreeDecomposition.toNiceTree_width_le`,
  `SimpleGraph.RootedTreeDecomposition.toNiceTree_size_le`: width does not increase and node count
  is at most `(3 * R.width + 5) * (n + 1)` (hence `≤ (3 * R.width + 5) * (card V + 1)` after
  pruning).

## References

* [M. Cygan et al., *Parameterized Algorithms*][CyganEtAl2015]
-/

public section

namespace SimpleGraph

universe uV uι

/-! ### Nice tree decomposition syntax and invariants -/

/-- Algebraic tree structure for a nice tree decomposition over vertex type `V`. -/
inductive NiceTree (V : Type uV)
  | leaf : NiceTree V
  | introduce (v : V) (child : NiceTree V) : NiceTree V
  | forget (v : V) (child : NiceTree V) : NiceTree V
  | join (left right : NiceTree V) : NiceTree V
  deriving DecidableEq, Repr

namespace NiceTree

variable {V : Type uV} {G : SimpleGraph V}

/-- Total number of nodes minus one in a `NiceTree`. -/
@[expose] def sizePred : NiceTree V → ℕ
  | .leaf => 0
  | .introduce _ child => child.sizePred + 1
  | .forget _ child => child.sizePred + 1
  | .join left right => left.sizePred + right.sizePred + 2

/-- Total number of nodes in a `NiceTree`. -/
@[expose] def size (T : NiceTree V) : ℕ :=
  T.sizePred + 1

@[simp] theorem size_leaf : (.leaf : NiceTree V).size = 1 := rfl
@[simp] theorem size_introduce (v : V) (child : NiceTree V) :
    (NiceTree.introduce v child).size = child.size + 1 := rfl
@[simp] theorem size_forget (v : V) (child : NiceTree V) :
    (NiceTree.forget v child).size = child.size + 1 := rfl
@[simp] theorem size_join (left right : NiceTree V) :
    (NiceTree.join left right).size = left.size + right.size + 1 := by
  simp only [size, sizePred]; omega

theorem size_pos (T : NiceTree V) : 0 < T.size := by
  unfold size; omega

section Decidable

variable [DecidableEq V]

/-- The bag of vertices associated with the root node of `T`. -/
@[expose] def bag : NiceTree V → Finset V
  | .leaf => ∅
  | .introduce v child => insert v child.bag
  | .forget v child => child.bag.erase v
  | .join left _ => left.bag

/-- Maximum bag cardinality over all nodes in `T`. -/
@[expose] def maxBagCard : NiceTree V → ℕ
  | .leaf => 0
  | .introduce v child => max (insert v child.bag).card child.maxBagCard
  | .forget v child => max (child.bag.erase v).card child.maxBagCard
  | .join left right => max left.bag.card (max left.maxBagCard right.maxBagCard)

/-- Width of a `NiceTree`: largest bag size minus one. -/
@[expose] def width (T : NiceTree V) : ℕ :=
  T.maxBagCard - 1

theorem card_bag_le_maxBagCard (T : NiceTree V) : T.bag.card ≤ T.maxBagCard := by
  cases T <;> simp [bag, maxBagCard]

theorem width_le_iff {T : NiceTree V} {k : ℕ} : T.width ≤ k ↔ T.maxBagCard ≤ k + 1 := by
  unfold width
  omega

/-- Union of all bags occurring in the subtree `T`. -/
@[expose] def subtreeVerts : NiceTree V → Finset V
  | .leaf => ∅
  | .introduce v child => insert v child.subtreeVerts
  | .forget _ child => child.subtreeVerts
  | .join left right => left.subtreeVerts ∪ right.subtreeVerts

theorem bag_subset_subtreeVerts (T : NiceTree V) : T.bag ⊆ T.subtreeVerts := by
  induction T with
  | leaf => exact Finset.Subset.rfl
  | introduce v child ih => exact Finset.insert_subset_insert v ih
  | forget v child ih => exact (Finset.erase_subset v _).trans ih
  | join left _ ihL _ => exact ihL.trans Finset.subset_union_left

/-- Local nice-tree invariant at every node: `introduce` introduces a vertex not appearing anywhere
in the child's subtree, `forget` removes a vertex present in the child bag, and `join` combines two
children with identical bags whose forgotten subtrees are disjoint. -/
@[expose] def LocalValid : NiceTree V → Prop
  | .leaf => True
  | .introduce v child => v ∉ child.subtreeVerts ∧ child.LocalValid
  | .forget v child => v ∈ child.bag ∧ child.LocalValid
  | .join left right =>
    left.bag = right.bag ∧
      Disjoint (left.subtreeVerts \ left.bag) right.subtreeVerts ∧
      left.LocalValid ∧ right.LocalValid

instance decidableLocalValid : (T : NiceTree V) → Decidable T.LocalValid
  | .leaf => isTrue trivial
  | .introduce _ child =>
    letI := decidableLocalValid child
    instDecidableAnd
  | .forget _ child =>
    letI := decidableLocalValid child
    instDecidableAnd
  | .join left right =>
    letI := decidableLocalValid left
    letI := decidableLocalValid right
    instDecidableAnd

/-- Symmetry of the join subtree-separation condition. -/
theorem disjoint_join_right {left right : NiceTree V} (hbag : left.bag = right.bag)
    (hdisj : Disjoint (left.subtreeVerts \ left.bag) right.subtreeVerts) :
    Disjoint (right.subtreeVerts \ right.bag) left.subtreeVerts := by
  rw [Finset.disjoint_left] at hdisj ⊢
  intro x hxR hxL
  rw [Finset.mem_sdiff, ← hbag] at hxR
  exact hdisj (Finset.mem_sdiff.2 ⟨hxL, hxR.2⟩) hxR.1

/-- `K` is contained in at least one node's bag in `T`. -/
@[expose] def CoversFinset (K : Finset V) : NiceTree V → Prop
  | .leaf => K ⊆ ∅
  | .introduce v child => K ⊆ insert v child.bag ∨ child.CoversFinset K
  | .forget v child => K ⊆ child.bag.erase v ∨ child.CoversFinset K
  | .join left right => K ⊆ left.bag ∨ left.CoversFinset K ∨ right.CoversFinset K

theorem coversFinset_of_subset_bag {T : NiceTree V} {K : Finset V} (h : K ⊆ T.bag) :
    T.CoversFinset K := by
  cases T with
  | leaf => exact h
  | _ => exact Or.inl h

theorem coversFinset_mono {T : NiceTree V} {K₁ K₂ : Finset V} (hsub : K₁ ⊆ K₂)
    (h : T.CoversFinset K₂) : T.CoversFinset K₁ := by
  induction T with
  | leaf => exact hsub.trans h
  | introduce _ _ ih | forget _ _ ih => exact h.imp (hsub.trans ·) ih
  | join _ _ ihL ihR => exact h.imp (hsub.trans ·) (Or.imp ihL ihR)

theorem coversFinset_subset_subtreeVerts {T : NiceTree V} {K : Finset V}
    (h : T.CoversFinset K) : K ⊆ T.subtreeVerts := by
  induction T with
  | leaf => exact h
  | introduce v child ih =>
    exact h.elim (·.trans (Finset.insert_subset_insert v child.bag_subset_subtreeVerts))
      (fun h => (ih h).trans (Finset.subset_insert v _))
  | forget v child ih =>
    exact h.elim (·.trans ((Finset.erase_subset v _).trans child.bag_subset_subtreeVerts)) ih
  | join left _ ihL ihR =>
    rcases h with h | h | h
    · exact h.trans (left.bag_subset_subtreeVerts.trans Finset.subset_union_left)
    · exact (ihL h).trans Finset.subset_union_left
    · exact (ihR h).trans Finset.subset_union_right

theorem coversFinset_singleton_of_mem_subtreeVerts {T : NiceTree V} {v : V}
    (hv : v ∈ T.subtreeVerts) : T.CoversFinset {v} := by
  induction T with
  | leaf => simp [subtreeVerts] at hv
  | introduce _ _ ih =>
    rcases Finset.mem_insert.1 hv with rfl | hvc
    · exact coversFinset_of_subset_bag (Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _))
    · exact Or.inr (ih hvc)
  | forget _ _ ih => exact Or.inr (ih hv)
  | join _ _ ihL ihR =>
    exact (Finset.mem_union.1 hv).elim (Or.inr ∘ Or.inl ∘ ihL) (Or.inr ∘ Or.inr ∘ ihR)

private theorem coversFinset_of_join_branch {A B : NiceTree V} {K : Finset V}
    (hdisj : Disjoint (A.subtreeVerts \ A.bag) B.subtreeVerts) (hA : K ⊆ A.subtreeVerts)
    (hcov : K ⊆ A.bag ∨ A.CoversFinset K ∨ B.CoversFinset K) : A.CoversFinset K := by
  rcases hcov with hp | hcovA | hcovB
  · exact coversFinset_of_subset_bag hp
  · exact hcovA
  · exact coversFinset_of_subset_bag fun x hx => by_contra fun hxB =>
      Finset.disjoint_left.1 hdisj (Finset.mem_sdiff.2 ⟨hA hx, hxB⟩)
        (coversFinset_subset_subtreeVerts hcovB hx)

private theorem pair_subset_of_mem {S : Finset V} {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    {x, y} ⊆ S :=
  Finset.insert_subset hx (Finset.singleton_subset_iff.2 hy)

/-- Every finite clique contained in `T.subtreeVerts` lies in some bag of `T` whenever every
edge of `G` inside `T.subtreeVerts` is covered. -/
theorem exists_coversFinset_of_isClique {T : NiceTree V} (hvalid : T.LocalValid)
    (hedge : ∀ ⦃u v : V⦄, G.Adj u v → u ∈ T.subtreeVerts → v ∈ T.subtreeVerts →
      T.CoversFinset {u, v})
    {K : Finset V} (hK : G.IsClique (K : Set V)) (hsub : K ⊆ T.subtreeVerts) :
    T.CoversFinset K := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨k₀, hk₀⟩
  · exact coversFinset_of_subset_bag (Finset.empty_subset _)
  induction T with
  | leaf => exact absurd (hsub hk₀) (Finset.notMem_empty k₀)
  | introduce v child ih =>
    obtain ⟨hv_sub, hc⟩ := hvalid
    by_cases hvK : v ∈ K
    · refine Or.inl fun w hw => if hwv : w = v then hwv ▸ Finset.mem_insert_self _ _ else ?_
      rcases hedge (hK hvK hw (Ne.symm hwv)) (Finset.mem_insert_self _ _) (hsub hw) with hp | hcov
      · exact hp (by simp)
      · exact absurd (coversFinset_subset_subtreeVerts hcov (by simp)) hv_sub
    · refine Or.inr (ih hc (fun x y hxy hx hy =>
        (hedge hxy (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy)).elim
          (fun hp => coversFinset_of_subset_bag fun z hz =>
            (Finset.mem_insert.1 (hp hz)).resolve_left fun hzv =>
              hv_sub (hzv ▸ pair_subset_of_mem hx hy hz)) id) fun w hw =>
        (Finset.mem_insert.1 (hsub hw)).resolve_left fun h => hvK (h ▸ hw))
  | forget v child ih =>
    exact Or.inr (ih hvalid.2 (fun x y hxy hx hy => (hedge hxy hx hy).elim
      (fun hp => coversFinset_of_subset_bag (hp.trans (Finset.erase_subset v _))) id) hsub)
  | join left right ihL ihR =>
    obtain ⟨hbag, hdisj, hcL, hcR⟩ := hvalid
    by_cases hL : K ⊆ left.subtreeVerts
    · exact Or.inr (Or.inl (ihL hcL (fun x y hxy hx hy => coversFinset_of_join_branch hdisj
        (pair_subset_of_mem hx hy)
        (hedge hxy (Finset.mem_union_left _ hx) (Finset.mem_union_left _ hy))) hL))
    · by_cases hR : K ⊆ right.subtreeVerts
      · exact Or.inr (Or.inr (ihR hcR (fun x y hxy hx hy => coversFinset_of_join_branch
          (disjoint_join_right hbag hdisj) (pair_subset_of_mem hx hy)
          ((hedge hxy (Finset.mem_union_right _ hx) (Finset.mem_union_right _ hy)).imp
            (hbag ▸ ·) Or.symm)) hR))
      · obtain ⟨u, huK, huL⟩ := Finset.not_subset.1 hL
        obtain ⟨w, hwK, hwR⟩ := Finset.not_subset.1 hR
        have hwL := (Finset.mem_union.1 (hsub hwK)).resolve_right hwR
        rcases hedge (hK huK hwK fun h => huL (h ▸ hwL)) (hsub huK) (hsub hwK) with
          hp | hcovL | hcovR
        · exact absurd (left.bag_subset_subtreeVerts (hp (by simp))) huL
        · exact absurd (coversFinset_subset_subtreeVerts hcovL (by simp)) huL
        · exact absurd (coversFinset_subset_subtreeVerts hcovR (by simp)) hwR

end Decidable

section Map

variable {α : Type*} {β : Type*}

/-- Relabel the vertices of a `NiceTree` along `f`. -/
@[expose] def map (f : α → β) : NiceTree α → NiceTree β
  | .leaf => .leaf
  | .introduce v child => .introduce (f v) (map f child)
  | .forget v child => .forget (f v) (map f child)
  | .join left right => .join (map f left) (map f right)

@[simp] theorem sizePred_map (f : α → β) (T : NiceTree α) : (T.map f).sizePred = T.sizePred := by
  induction T <;> simp_all [map, sizePred]

@[simp] theorem size_map (f : α → β) (T : NiceTree α) : (T.map f).size = T.size := by
  simp [size]

theorem bag_map {f : α → β} (hf : Function.Injective f) (T : NiceTree α)
    [DecidableEq α] [DecidableEq β] : (T.map f).bag = T.bag.image f := by
  induction T <;> simp_all [map, bag, Finset.image_erase hf]

theorem subtreeVerts_map (f : α → β) (T : NiceTree α) [DecidableEq α] [DecidableEq β] :
    (T.map f).subtreeVerts = T.subtreeVerts.image f := by
  induction T <;> simp_all [map, subtreeVerts, Finset.image_union]

theorem localValid_map {f : α → β} (hf : Function.Injective f) {T : NiceTree α}
    [DecidableEq α] [DecidableEq β] (h : T.LocalValid) : (T.map f).LocalValid := by
  induction T with
  | leaf => trivial
  | introduce _ _ ih =>
    refine ⟨?_, ih h.2⟩
    simpa [subtreeVerts_map, hf.eq_iff] using h.1
  | forget _ _ ih =>
    exact ⟨by rw [bag_map hf]; exact Finset.mem_image_of_mem f h.1, ih h.2⟩
  | join left right ihL ihR =>
    refine ⟨by simp only [bag_map hf, h.1], ?_, ihL h.2.2.1, ihR h.2.2.2⟩
    rw [subtreeVerts_map, bag_map hf, subtreeVerts_map, ← Finset.image_sdiff _ _ hf,
      Finset.disjoint_left]
    rintro _ h1 h2
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.1 h2
    exact Finset.disjoint_left.1 h.2.1 hx (hf hxy ▸ hy)

theorem maxBagCard_map {f : α → β} (hf : Function.Injective f) (T : NiceTree α)
    [DecidableEq α] [DecidableEq β] : (T.map f).maxBagCard = T.maxBagCard := by
  induction T with
  | leaf => rfl
  | introduce _ _ ih =>
    simp only [map, maxBagCard, bag_map hf, ← Finset.image_insert,
      Finset.card_image_of_injective _ hf, ih]
  | forget _ _ ih =>
    simp only [map, maxBagCard, bag_map hf, ← Finset.image_erase hf,
      Finset.card_image_of_injective _ hf, ih]
  | join _ _ ihL ihR =>
    simp only [map, maxBagCard, bag_map hf, Finset.card_image_of_injective _ hf, ihL, ihR]

theorem width_map {f : α → β} (hf : Function.Injective f) (T : NiceTree α)
    [DecidableEq α] [DecidableEq β] : (T.map f).width = T.width := by
  simp [width, maxBagCard_map hf]

theorem coversFinset_map {f : α → β} (hf : Function.Injective f) {T : NiceTree α}
    {K : Finset α} [DecidableEq α] [DecidableEq β] (h : T.CoversFinset K) :
    (T.map f).CoversFinset (K.image f) := by
  induction T with
  | leaf => simpa [map, CoversFinset] using h
  | introduce _ _ ih =>
    exact h.imp (fun h => by
      rw [bag_map hf, ← Finset.image_insert]; exact Finset.image_subset_image h) ih
  | forget _ _ ih =>
    exact h.imp (fun h => by
      rw [bag_map hf, ← Finset.image_erase hf]; exact Finset.image_subset_image h) ih
  | join _ _ ihL ihR =>
    exact h.imp (fun h => by rw [bag_map hf]; exact Finset.image_subset_image h) (Or.imp ihL ihR)

end Map

end NiceTree

/-! ### Bundled nice tree decomposition -/

section Bundled

variable {V : Type uV}

/-- A nice tree decomposition of `G`: a valid `NiceTree V` with empty root bag that covers all
vertices and edges of `G`. -/
structure NiceTreeDecomposition (G : SimpleGraph V) [DecidableEq V] where
  /-- The underlying leaf/introduce/forget/join tree. -/
  tree : NiceTree V
  /-- Local validity of introduce, forget, and join operations. -/
  localValid : tree.LocalValid
  /-- The root bag is empty. -/
  bag_root : tree.bag = ∅
  /-- Every vertex appears in the tree. -/
  exists_mem_bag (v : V) : v ∈ tree.subtreeVerts
  /-- Every edge of `G` appears in some bag of the tree. -/
  exists_adj_mem_bag ⦃u v : V⦄ : G.Adj u v → tree.CoversFinset {u, v}

namespace NiceTreeDecomposition

variable [DecidableEq V] {G : SimpleGraph V}

/-- Width of a nice tree decomposition: largest bag size minus one. -/
@[expose] def width (N : G.NiceTreeDecomposition) : ℕ :=
  N.tree.width

/-- Number of nodes in a nice tree decomposition. -/
@[expose] def size (N : G.NiceTreeDecomposition) : ℕ :=
  N.tree.size

/-- Every finite clique of `G` lies in some bag of `N`. -/
theorem exists_coversFinset_of_isClique (N : G.NiceTreeDecomposition) {K : Finset V}
    (hK : G.IsClique (K : Set V)) : N.tree.CoversFinset K :=
  N.tree.exists_coversFinset_of_isClique N.localValid
    (fun _ _ huv _ _ => N.exists_adj_mem_bag huv) hK fun v _ => N.exists_mem_bag v

theorem width_le_iff (N : G.NiceTreeDecomposition) {k : ℕ} :
    N.width ≤ k ↔ N.tree.maxBagCard ≤ k + 1 :=
  NiceTree.width_le_iff

end NiceTreeDecomposition

end Bundled

/-! ### Converting `NiceTree` to `RootedTreeDecomposition` -/

namespace NiceTree

variable {V : Type uV} [DecidableEq V]

private def shiftEntry {m n : ℕ} (off : ℕ) (hlen : off + m ≤ n + 1)
    (dChild : Fin m → Fin m × Finset V) (j : Fin m) : Fin (n + 1) × Finset V :=
  let d := dChild j
  (if j.val = 0 then 0 else ⟨off + d.1.val, by have := d.1.isLt; omega⟩, d.2)

omit [DecidableEq V] in
private theorem shiftEntry_parent_lt {m n : ℕ} (off : ℕ) (hlen : off + m ≤ n + 1)
    {dChild : Fin m → Fin m × Finset V} (hchild : ∀ j : Fin m, j.val ≠ 0 → (dChild j).1 < j)
    {j : Fin m} {i : Fin (n + 1)} (hoff : 0 < off) (hi : i.val = off + j.val) :
    (shiftEntry off hlen dChild j).1 < i := by
  dsimp only [shiftEntry]
  split_ifs with hj
  · exact Fin.lt_def.2 (by dsimp; omega)
  · exact Fin.lt_def.2 (by have := Fin.lt_def.1 (hchild j hj); dsimp; omega)

private def unaryRootedData (rootBag : Finset V) (child : NiceTree V)
    (dChild : Fin (child.sizePred + 1) → Fin (child.sizePred + 1) × Finset V)
    (i : Fin (child.sizePred + 1 + 1)) : Fin (child.sizePred + 1 + 1) × Finset V :=
  if _ : i.val = 0 then (0, rootBag)
  else shiftEntry 1 (by omega) dChild ⟨i.val - 1, by have := i.isLt; omega⟩

/-- Pre-order parent and bag tables for `T : NiceTree V` indexed by `Fin (T.sizePred + 1)`. -/
private def rootedData : (T : NiceTree V) →
    Fin (T.sizePred + 1) → Fin (T.sizePred + 1) × Finset V
  | .leaf, _ => (0, ∅)
  | .introduce v child, i => unaryRootedData (insert v child.bag) child (rootedData child) i
  | .forget v child, i => unaryRootedData (child.bag.erase v) child (rootedData child) i
  | .join left right, i =>
    if _ : i.val = 0 then (0, left.bag)
    else if _ : i.val ≤ left.sizePred + 1 then
      shiftEntry 1 (by simp only [sizePred]; omega) (rootedData left) ⟨i.val - 1, by omega⟩
    else
      shiftEntry (left.sizePred + 2) (by simp only [sizePred]; omega) (rootedData right)
        ⟨i.val - (left.sizePred + 2), by have := i.isLt; simp only [sizePred] at this; omega⟩

private theorem rootedData_zero (T : NiceTree V) : rootedData T 0 = (0, T.bag) := by
  cases T with
  | leaf => rfl
  | introduce _ _ | forget _ _ =>
    change unaryRootedData _ _ _ 0 = (0, _)
    simp [unaryRootedData, bag]
  | join _ _ => simp [rootedData, bag]

private theorem rootedData_parent_zero (T : NiceTree V) : (rootedData T 0).1 = 0 := by
  rw [rootedData_zero]

private theorem rootedData_bag_zero (T : NiceTree V) : (rootedData T 0).2 = T.bag := by
  rw [rootedData_zero]

private theorem rootedData_parent_lt :
    ∀ (T : NiceTree V) (i : Fin (T.sizePred + 1)), i.val ≠ 0 → (rootedData T i).1 < i
  | .leaf, i, hi => absurd (by have := i.isLt; simp only [sizePred] at this; omega) hi
  | .introduce _ child, i, hi | .forget _ child, i, hi => by
    simp only [rootedData, unaryRootedData, hi, ↓reduceDIte]
    exact shiftEntry_parent_lt 1 _ (rootedData_parent_lt child) one_pos (by dsimp; omega)
  | .join left right, i, hi => by
    dsimp only [sizePred] at i hi
    simp only [rootedData, hi, ↓reduceDIte]
    split_ifs with hL
    · exact shiftEntry_parent_lt 1 _ (rootedData_parent_lt left) one_pos (by dsimp; omega)
    · exact shiftEntry_parent_lt (left.sizePred + 2) _ (rootedData_parent_lt right)
        (by omega) (by dsimp; omega)

/-- Shifted copy embedding of child table `C` inside parent table `T` starting at offset `off`. -/
private structure RootedShift (T C : NiceTree V) (off : ℕ) : Prop where
  pos : 0 < off
  bound : off + (C.sizePred + 1) ≤ T.sizePred + 1
  bag : ∀ k : Fin (C.sizePred + 1),
    (rootedData T ⟨off + k.val, by have := k.isLt; omega⟩).2 = (rootedData C k).2
  parent_zero : ((rootedData T ⟨off, by omega⟩).1).val = 0
  parent_ne : ∀ k : Fin (C.sizePred + 1), k.val ≠ 0 →
    ((rootedData T ⟨off + k.val, by have := k.isLt; omega⟩).1).val =
      off + ((rootedData C k).1).val

private theorem RootedShift.of_shiftEntry {T C : NiceTree V} {off : ℕ} (pos : 0 < off)
    (bound : off + (C.sizePred + 1) ≤ T.sizePred + 1)
    (heq : ∀ k : Fin (C.sizePred + 1),
      rootedData T ⟨off + k.val, by have := k.isLt; omega⟩ =
        shiftEntry off bound (rootedData C) k) :
    RootedShift T C off where
  pos := pos
  bound := bound
  bag k := by rw [heq k]; rfl
  parent_zero := by simpa [shiftEntry] using congrArg (fun p => p.1.val) (heq 0)
  parent_ne k hk := by simp [heq k, shiftEntry, hk]

omit [DecidableEq V] in
private theorem unaryShift_eq {rootBag : Finset V} {child : NiceTree V}
    (dChild : Fin (child.sizePred + 1) → Fin (child.sizePred + 1) × Finset V)
    (k : Fin (child.sizePred + 1)) :
    unaryRootedData rootBag child dChild ⟨1 + k.val, by have := k.isLt; omega⟩ =
      shiftEntry 1 (by omega) dChild k := by
  simp only [unaryRootedData, show 1 + k.val ≠ 0 by omega, ↓reduceDIte]
  congr 1; exact Fin.ext (by dsimp; omega)

private theorem introduceShift (v : V) (child : NiceTree V) :
    RootedShift (.introduce v child) child 1 :=
  RootedShift.of_shiftEntry one_pos (by simp only [sizePred]; omega)
    fun k => unaryShift_eq (rootedData child) k

private theorem forgetShift (v : V) (child : NiceTree V) :
    RootedShift (.forget v child) child 1 :=
  RootedShift.of_shiftEntry one_pos (by simp only [sizePred]; omega)
    fun k => unaryShift_eq (rootedData child) k

private theorem joinLeftShift (left right : NiceTree V) :
    RootedShift (.join left right) left 1 :=
  RootedShift.of_shiftEntry one_pos (by simp only [sizePred]; omega) fun k => by
    have hkL : 1 + k.val ≤ left.sizePred + 1 := by have := k.isLt; omega
    simp only [rootedData, show 1 + k.val ≠ 0 by omega, ↓reduceDIte, hkL]
    congr 1; exact Fin.ext (by dsimp; omega)

private theorem joinRightShift (left right : NiceTree V) :
    RootedShift (.join left right) right (left.sizePred + 2) :=
  RootedShift.of_shiftEntry (by omega) (by simp only [sizePred]; omega) fun k => by
    have hnot : ¬left.sizePred + 2 + k.val ≤ left.sizePred + 1 := by omega
    simp only [rootedData, show left.sizePred + 2 + k.val ≠ 0 by omega, ↓reduceDIte, hnot]
    congr 1; exact Fin.ext (by dsimp; omega)

private theorem mem_subtreeVerts_of_rootedData :
    ∀ {T : NiceTree V} {i : Fin (T.sizePred + 1)} {v : V},
      v ∈ (rootedData T i).2 → v ∈ T.subtreeVerts
  | .leaf, _, _, hv => by simp [rootedData] at hv
  | .introduce w child, i, v, hv => by
    by_cases hi0 : i.val = 0
    · rw [(Fin.ext hi0 : i = 0), rootedData_bag_zero] at hv
      exact Finset.insert_subset_insert w child.bag_subset_subtreeVerts hv
    · simp only [rootedData, unaryRootedData, hi0, ↓reduceDIte, shiftEntry] at hv
      exact Finset.mem_insert_of_mem (mem_subtreeVerts_of_rootedData (T := child) hv)
  | .forget w child, i, v, hv => by
    by_cases hi0 : i.val = 0
    · rw [(Fin.ext hi0 : i = 0), rootedData_bag_zero] at hv
      exact (Finset.erase_subset w _).trans child.bag_subset_subtreeVerts hv
    · simp only [rootedData, unaryRootedData, hi0, ↓reduceDIte, shiftEntry] at hv
      exact mem_subtreeVerts_of_rootedData (T := child) hv
  | .join left right, i, v, hv => by
    dsimp only [rootedData] at hv
    split_ifs at hv
    · exact Finset.mem_union_left _ (left.bag_subset_subtreeVerts hv)
    · exact Finset.mem_union_left _ (mem_subtreeVerts_of_rootedData (T := left) hv)
    · exact Finset.mem_union_right _ (mem_subtreeVerts_of_rootedData (T := right) hv)

private theorem rootedData_coversFinset {T : NiceTree V} {K : Finset V}
    (h : T.CoversFinset K) : ∃ i : Fin (T.sizePred + 1), K ⊆ (rootedData T i).2 := by
  have shiftCov : ∀ {A C : NiceTree V} {off : ℕ}, RootedShift A C off →
      (∃ j, K ⊆ (rootedData C j).2) → ∃ i, K ⊆ (rootedData A i).2 := fun {A C off} s ⟨j, hj⟩ =>
    ⟨⟨off + j.val, by have := j.isLt; have := s.bound; omega⟩, by simpa only [s.bag j] using hj⟩
  induction T with
  | leaf => exact ⟨0, h⟩
  | introduce w child ih =>
    exact h.elim (fun h => ⟨0, by rwa [rootedData_bag_zero]⟩)
      (fun h => shiftCov (introduceShift w child) (ih h))
  | forget w child ih =>
    exact h.elim (fun h => ⟨0, by rwa [rootedData_bag_zero]⟩)
      (fun h => shiftCov (forgetShift w child) (ih h))
  | join left right ihL ihR =>
    rcases h with h | h | h
    · exact ⟨0, by rwa [rootedData_bag_zero]⟩
    · exact shiftCov (joinLeftShift left right) (ihL h)
    · exact shiftCov (joinRightShift left right) (ihR h)

private theorem rootedData_card_le_maxBagCard (T : NiceTree V) (i : Fin (T.sizePred + 1)) :
    (rootedData T i).2.card ≤ T.maxBagCard := by
  induction T with
  | leaf => simp [rootedData, maxBagCard]
  | introduce _ child ih | forget _ child ih =>
    by_cases hi0 : i.val = 0
    · rw [(Fin.ext hi0 : i = 0), rootedData_bag_zero]; exact le_max_left _ _
    · simp only [rootedData, unaryRootedData, hi0, ↓reduceDIte, shiftEntry]
      exact (ih _).trans (le_max_right _ _)
  | join left right ihL ihR =>
    dsimp only [rootedData]
    split_ifs
    · exact le_max_left _ _
    · exact (ihL _).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (ihR _).trans ((le_max_right _ _).trans (le_max_right _ _))

private theorem exists_rootedData_card_eq_maxBagCard (T : NiceTree V) :
    ∃ i : Fin (T.sizePred + 1), T.maxBagCard ≤ (rootedData T i).2.card := by
  have shiftMax : ∀ {A C : NiceTree V} {off : ℕ}, RootedShift A C off →
      (∃ j, C.maxBagCard ≤ (rootedData C j).2.card) →
      ∃ i : Fin (A.sizePred + 1), C.maxBagCard ≤ (rootedData A i).2.card :=
    fun {A C off} s ⟨j, hj⟩ =>
      ⟨⟨off + j.val, by have := j.isLt; have := s.bound; omega⟩, by simpa only [s.bag j] using hj⟩
  induction T with
  | leaf => exact ⟨0, by simp [rootedData, maxBagCard]⟩
  | introduce w child ih =>
    rcases le_total (insert w child.bag).card child.maxBagCard with h | h
    · simpa only [maxBagCard, max_eq_right h] using shiftMax (introduceShift w child) ih
    · exact ⟨0, by rw [rootedData_bag_zero]; simp only [bag, maxBagCard, max_eq_left h, le_rfl]⟩
  | forget w child ih =>
    rcases le_total (child.bag.erase w).card child.maxBagCard with h | h
    · simpa only [maxBagCard, max_eq_right h] using shiftMax (forgetShift w child) ih
    · exact ⟨0, by rw [rootedData_bag_zero]; simp only [bag, maxBagCard, max_eq_left h, le_rfl]⟩
  | join left right ihL ihR =>
    rcases max_cases left.bag.card (max left.maxBagCard right.maxBagCard) with ⟨hm, _⟩ | ⟨hm, _⟩
    · exact ⟨0, by rw [rootedData_bag_zero]; simp [maxBagCard, bag, hm]⟩
    · simp only [maxBagCard, hm]
      rcases max_cases left.maxBagCard right.maxBagCard with ⟨hLR, _⟩ | ⟨hLR, _⟩
      · simpa only [hLR] using shiftMax (joinLeftShift left right) ihL
      · simpa only [hLR] using shiftMax (joinRightShift left right) ihR

private abbrev bagInduce (T : NiceTree V) (v : V) :=
  (parentTree (fun k => (rootedData T k).1)).induce {k | v ∈ (rootedData T k).2}

/-- Embed a child's induced bag-subtree into a parent `NiceTree`'s induced bag-subtree along
`s : RootedShift T C off`. -/
private def RootedShift.induceHom {T C : NiceTree V} {off : ℕ} (s : RootedShift T C off) (v : V) :
    bagInduce C v →g bagInduce T v where
  toFun k := ⟨⟨off + k.1.val, by have := k.1.isLt; have := s.bound; omega⟩, by
    change v ∈ (rootedData T _).2; rw [s.bag k.1]; exact k.2⟩
  map_rel' {a b} hab := by
    have step : ∀ {x y : Fin (C.sizePred + 1)},
        x ≠ 0 → (rootedData C x).1 = y →
        (⟨off + x.val, by have := x.isLt; have := s.bound; omega⟩ : Fin (T.sizePred + 1)) ≠ 0 ∧
          (rootedData T ⟨off + x.val, by have := x.isLt; have := s.bound; omega⟩).1 =
            ⟨off + y.val, by have := y.isLt; have := s.bound; omega⟩ := by
      intro x y hx hpx
      refine ⟨Fin.ne_of_val_ne (by dsimp; have := s.pos; omega), Fin.ext ?_⟩
      dsimp; rw [s.parent_ne x (Fin.val_ne_of_ne hx), hpx]
    change (parentTree _).Adj a.1 b.1 at hab
    change (parentTree _).Adj _ _
    rw [parentTree_adj (fun k hk => rootedData_parent_lt C k (Fin.val_ne_of_ne hk))] at hab
    rw [parentTree_adj (fun k hk => rootedData_parent_lt T k (Fin.val_ne_of_ne hk))]
    exact hab.imp (fun h => step h.1 h.2) (fun h => step h.1 h.2)

private theorem RootedShift.exists_eq {T C : NiceTree V} {off : ℕ} (s : RootedShift T C off)
    {v : V} (a : {k | v ∈ (rootedData T k).2}) (h₁ : off ≤ a.1.val)
    (h₂ : a.1.val < off + (C.sizePred + 1)) :
    ∃ (j : {k | v ∈ (rootedData C k).2}), a = s.induceHom v j := by
  let k : Fin (C.sizePred + 1) := ⟨a.1.val - off, by omega⟩
  have hk : (⟨off + k.val, by have := k.isLt; have := s.bound; omega⟩ : Fin (T.sizePred + 1)) =
      a.1 := Fin.ext (by dsimp [k]; omega)
  exact ⟨⟨k, by change v ∈ (rootedData C k).2; rw [← s.bag k, hk]; exact a.2⟩,
    Subtype.ext hk.symm⟩

private theorem RootedShift.reach_of_preconnected {T C : NiceTree V} {off : ℕ}
    (s : RootedShift T C off) {v : V} (hc : (bagInduce C v).Preconnected)
    {a b : {k | v ∈ (rootedData T k).2}}
    (ha₁ : off ≤ a.1.val) (ha₂ : a.1.val < off + (C.sizePred + 1))
    (hb₁ : off ≤ b.1.val) (hb₂ : b.1.val < off + (C.sizePred + 1)) :
    (bagInduce T v).Reachable a b := by
  obtain ⟨ja, rfl⟩ := s.exists_eq a ha₁ ha₂
  obtain ⟨jb, rfl⟩ := s.exists_eq b hb₁ hb₂
  exact (hc ja jb).map (s.induceHom v)

private theorem RootedShift.reach_root {T C : NiceTree V} {off : ℕ}
    (s : RootedShift T C off) {v : V} (hv : v ∈ T.bag) (hvc : v ∈ C.bag)
    (hc : ∀ (j : Fin (C.sizePred + 1)) (hj : v ∈ (rootedData C j).2),
      (bagInduce C v).Reachable ⟨j, hj⟩
        ⟨0, by change v ∈ (rootedData C 0).2; rw [rootedData_bag_zero]; exact hvc⟩)
    {i : Fin (T.sizePred + 1)} (hi : v ∈ (rootedData T i).2)
    (h₁ : off ≤ i.val) (h₂ : i.val < off + (C.sizePred + 1)) :
    (bagInduce T v).Reachable ⟨i, hi⟩
      ⟨0, by change v ∈ (rootedData T 0).2; rw [rootedData_bag_zero]; exact hv⟩ := by
  obtain ⟨⟨j, hj⟩, he⟩ := s.exists_eq ⟨i, hi⟩ h₁ h₂
  rw [he]
  refine ((hc j hj).map (s.induceHom v)).trans (SimpleGraph.Adj.reachable ?_)
  change (parentTree _).Adj ⟨off, by have := s.bound; omega⟩ 0
  rw [parentTree_adj (fun k hk => rootedData_parent_lt T k (Fin.val_ne_of_ne hk))]
  exact Or.inl ⟨Fin.ne_of_val_ne (by dsimp; have := s.pos; omega), Fin.ext s.parent_zero⟩

/-- A vertex outside the root bag occurs only in the bags of non-root nodes. -/
private theorem rootedData_val_ne_zero {T : NiceTree V} {v : V} (hv : v ∉ T.bag)
    {i : Fin (T.sizePred + 1)} (hi : v ∈ (rootedData T i).2) : i.val ≠ 0 := fun h0 => by
  rw [(Fin.ext h0 : i = 0), rootedData_bag_zero] at hi
  exact hv hi

private theorem rootedData_preconnected_of_mem_bag :
    ∀ {T : NiceTree V} {v : V}, T.LocalValid → ∀ (hv : v ∈ T.bag)
      (i : Fin (T.sizePred + 1)) (hi : v ∈ (rootedData T i).2),
      (bagInduce T v).Reachable ⟨i, hi⟩
        ⟨0, by change v ∈ (rootedData T 0).2; rw [rootedData_bag_zero]; exact hv⟩
  | .leaf, _, _, _, i, _ => by obtain rfl : i = 0 := Fin.eq_zero i; rfl
  | .introduce w child, v, ⟨hw_sub, hc⟩, hv, i, hi => by
    by_cases hi0 : i.val = 0
    · obtain rfl : i = 0 := Fin.ext hi0; rfl
    · have hvc : v ∈ child.bag := (Finset.mem_insert.1 hv).resolve_left fun hvw => by
        simp only [rootedData, unaryRootedData, hi0, ↓reduceDIte, shiftEntry] at hi
        exact hw_sub (mem_subtreeVerts_of_rootedData (hvw ▸ hi))
      exact (introduceShift w child).reach_root hv hvc
        (rootedData_preconnected_of_mem_bag hc hvc) hi (by omega)
        (by have := i.isLt; simp only [sizePred] at this; omega)
  | .forget w child, v, ⟨_, hc⟩, hv, i, hi => by
    by_cases hi0 : i.val = 0
    · obtain rfl : i = 0 := Fin.ext hi0; rfl
    · have hvc : v ∈ child.bag := Finset.erase_subset w _ hv
      exact (forgetShift w child).reach_root hv hvc
        (rootedData_preconnected_of_mem_bag hc hvc) hi (by omega)
        (by have := i.isLt; simp only [sizePred] at this; omega)
  | .join left right, v, ⟨hbag, _, hcL, hcR⟩, hv, i, hi => by
    by_cases hi0 : i.val = 0
    · obtain rfl : i = 0 := Fin.ext hi0; rfl
    · by_cases hL : i.val ≤ left.sizePred + 1
      · exact (joinLeftShift left right).reach_root hv hv
          (rootedData_preconnected_of_mem_bag hcL hv) hi (by omega) (by omega)
      · exact (joinRightShift left right).reach_root hv (hbag ▸ hv)
          (rootedData_preconnected_of_mem_bag hcR (hbag ▸ hv)) hi (by omega)
          (by have := i.isLt; simp only [sizePred] at this; omega)

private theorem RootedShift.mem_subtreeVerts {T C : NiceTree V} {off : ℕ}
    (s : RootedShift T C off) {v : V} (a : {k | v ∈ (rootedData T k).2})
    (h₁ : off ≤ a.1.val) (h₂ : a.1.val < off + (C.sizePred + 1)) : v ∈ C.subtreeVerts := by
  obtain ⟨⟨_, hj⟩, -⟩ := s.exists_eq a h₁ h₂
  exact mem_subtreeVerts_of_rootedData hj

private theorem RootedShift.reach_unary {T child : NiceTree V} (s : RootedShift T child 1)
    {v : V} (hv : v ∉ T.bag) (hsz : T.sizePred = child.sizePred + 1)
    (hc : (bagInduce child v).Preconnected) (a b : {k | v ∈ (rootedData T k).2}) :
    (bagInduce T v).Reachable a b :=
  s.reach_of_preconnected hc
    (Nat.one_le_iff_ne_zero.2 (rootedData_val_ne_zero hv a.2)) (by have := a.1.isLt; omega)
    (Nat.one_le_iff_ne_zero.2 (rootedData_val_ne_zero hv b.2)) (by have := b.1.isLt; omega)

private theorem rootedData_preconnected {T : NiceTree V} {v : V} (hvalid : T.LocalValid) :
    (bagInduce T v).Preconnected := fun a b => by
  by_cases hv : v ∈ T.bag
  · exact (rootedData_preconnected_of_mem_bag hvalid hv a.1 a.2).trans
      (rootedData_preconnected_of_mem_bag hvalid hv b.1 b.2).symm
  · cases T with
    | leaf => exact absurd a.2 (Finset.notMem_empty v)
    | introduce w child =>
      exact (introduceShift w child).reach_unary hv rfl (rootedData_preconnected hvalid.2) a b
    | forget w child =>
      exact (forgetShift w child).reach_unary hv rfl (rootedData_preconnected hvalid.2) a b
    | join left right =>
      obtain ⟨_, hdisj, hcL, hcR⟩ := hvalid
      have hpos (c : {k | v ∈ (rootedData (.join left right) k).2}) : 1 ≤ c.1.val :=
        Nat.one_le_iff_ne_zero.2 (rootedData_val_ne_zero hv c.2)
      have hlast (c : {k | v ∈ (rootedData (.join left right) k).2}) :
          c.1.val < left.sizePred + 2 + (right.sizePred + 1) := by
        have := c.1.isLt; simp only [sizePred] at this; omega
      have hnotBoth : ¬(v ∈ left.subtreeVerts ∧ v ∈ right.subtreeVerts) := fun ⟨hL, hR⟩ =>
        Finset.disjoint_left.1 hdisj (Finset.mem_sdiff.2 ⟨hL, hv⟩) hR
      let sL := joinLeftShift left right
      let sR := joinRightShift left right
      by_cases haL : a.1.val ≤ left.sizePred + 1 <;> by_cases hbL : b.1.val ≤ left.sizePred + 1
      · exact sL.reach_of_preconnected (rootedData_preconnected hcL)
          (hpos a) (by omega) (hpos b) (by omega)
      · exact absurd ⟨sL.mem_subtreeVerts a (hpos a) (by omega),
          sR.mem_subtreeVerts b (by omega) (hlast b)⟩ hnotBoth
      · exact absurd ⟨sL.mem_subtreeVerts b (hpos b) (by omega),
          sR.mem_subtreeVerts a (by omega) (hlast a)⟩ hnotBoth
      · exact sR.reach_of_preconnected (rootedData_preconnected hcR)
          (by omega) (hlast a) (by omega) (hlast b)

/-- Convert a valid `NiceTree` covering all vertices and edges of `G` into a
`RootedTreeDecomposition` with the same width and `T.size` nodes. -/
def toRootedTreeDecomposition {G : SimpleGraph V} (T : NiceTree V) (hvalid : T.LocalValid)
    (hvert : ∀ v : V, v ∈ T.subtreeVerts)
    (hedge : ∀ ⦃u v : V⦄, G.Adj u v → T.CoversFinset {u, v}) :
    G.RootedTreeDecomposition T.sizePred where
  parent i := (rootedData T i).1
  parent_zero := rootedData_parent_zero T
  parent_lt i hi := rootedData_parent_lt T i (Fin.val_ne_of_ne hi)
  bag i := (rootedData T i).2
  exists_mem_bag v := by
    obtain ⟨i, hi⟩ := rootedData_coversFinset (coversFinset_singleton_of_mem_subtreeVerts (hvert v))
    exact ⟨i, hi (Finset.mem_singleton_self v)⟩
  exists_adj_mem_bag u v huv := by
    obtain ⟨i, hi⟩ := rootedData_coversFinset (hedge huv)
    exact ⟨i, hi (Finset.mem_insert_self u _),
      hi (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))⟩
  top_unique v _ _ hi hit hj hjt :=
    eq_of_preconnected_parentTree (rootedData_parent_zero T)
      (fun i h => rootedData_parent_lt T i (Fin.val_ne_of_ne h))
      (rootedData_preconnected hvalid) hi hit hj hjt

theorem toRootedTreeDecomposition_width {G : SimpleGraph V} (T : NiceTree V) (hvalid : T.LocalValid)
    (hvert : ∀ v : V, v ∈ T.subtreeVerts)
    (hedge : ∀ ⦃u v : V⦄, G.Adj u v → T.CoversFinset {u, v}) :
    (T.toRootedTreeDecomposition hvalid hvert hedge).width = T.width := by
  refine le_antisymm
    ((T.toRootedTreeDecomposition hvalid hvert hedge).width_le_iff.2 fun i => ?_) ?_
  · have hle := rootedData_card_le_maxBagCard T i
    change (rootedData T i).2.card ≤ T.width + 1
    dsimp only [width]
    omega
  · obtain ⟨i, hi⟩ := exists_rootedData_card_eq_maxBagCard T
    have hcard : (rootedData T i).2.card ≤
        (T.toRootedTreeDecomposition hvalid hvert hedge).width + 1 :=
      (T.toRootedTreeDecomposition hvalid hvert hedge).card_bag_le i
    dsimp only [width]
    omega

end NiceTree

namespace NiceTreeDecomposition

variable {V : Type uV} [DecidableEq V] {G : SimpleGraph V}

/-- Convert a bundled nice tree decomposition into a `RootedTreeDecomposition` of the same width
and `N.size` nodes. -/
def toRootedTreeDecomposition (N : G.NiceTreeDecomposition) :
    G.RootedTreeDecomposition N.tree.sizePred :=
  N.tree.toRootedTreeDecomposition N.localValid N.exists_mem_bag N.exists_adj_mem_bag

theorem toRootedTreeDecomposition_width (N : G.NiceTreeDecomposition) :
    N.toRootedTreeDecomposition.width = N.width :=
  N.tree.toRootedTreeDecomposition_width N.localValid N.exists_mem_bag N.exists_adj_mem_bag

end NiceTreeDecomposition

/-! ### Pruning redundant subset bags (`O(|V|)` nodes) -/

namespace RootedTreeDecomposition

variable {V : Type uV} {G : SimpleGraph V} [DecidableEq V]

private theorem succAbove_predAbove_of_ne {n : ℕ} {c x : Fin (n + 2)}
    (hc0 : c ≠ 0) (hx : x ≠ c) :
    c.succAbove ((c.pred hc0).predAbove x) = x := by
  have h1 := Fin.succ_succAbove_predAbove (p := c.pred hc0) (Fin.succ_pred c hc0 ▸ hx)
  rwa [Fin.succ_pred] at h1

omit [DecidableEq V] in
private theorem contractStep_reach {n : ℕ} (R : G.RootedTreeDecomposition (n + 1))
    (c : Fin (n + 2)) (hc0 : c ≠ 0) (hsub : R.bag c ⊆ R.bag (R.parent c))
    (parent' : Fin (n + 1) → Fin (n + 1))
    (hpar : ∀ j, parent' j = (c.pred hc0).predAbove
      (if R.parent (c.succAbove j) = c then R.parent c else R.parent (c.succAbove j)))
    (hplt : ∀ j : Fin (n + 1), j ≠ 0 → parent' j < j)
    (v : V) (htop_ne : R.top v ≠ c)
    (ht' : v ∈ R.bag (c.succAbove ((c.pred hc0).predAbove (R.top v))))
    (hstep_mem : ∀ k, v ∈ R.bag k → ¬R.IsTop v k → v ∈ R.bag (R.parent k)) :
    ∀ (k : Fin (n + 2)) (j : Fin (n + 1)), c.succAbove j = k →
      ∀ hj : v ∈ R.bag (c.succAbove j),
        ((parentTree parent').induce {m | v ∈ R.bag (c.succAbove m)}).Reachable
          ⟨j, hj⟩ ⟨(c.pred hc0).predAbove (R.top v), ht'⟩ := by
  have hzero : c.succAbove 0 = 0 := (Fin.succAbove_eq_zero_iff hc0).mpr rfl
  intro k
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    rintro j rfl hj
    by_cases htopj : c.succAbove j = R.top v
    · obtain rfl : j = (c.pred hc0).predAbove (R.top v) := Fin.succAbove_right_injective
        (by rw [htopj, succAbove_predAbove_of_ne hc0 htop_ne])
      rfl
    · have hnot_top : ¬R.IsTop v (c.succAbove j) := fun h => htopj (R.isTop_iff.1 h)
      have hj0 : c.succAbove j ≠ 0 := fun h0 =>
        hnot_top (R.isTop_iff_mem.2 ⟨hj, Or.inl h0⟩)
      have hmem_p : v ∈ R.bag (R.parent (c.succAbove j)) := hstep_mem _ hj hnot_top
      have hpk := R.parent_lt _ hj0
      let x := if R.parent (c.succAbove j) = c then R.parent c else R.parent (c.succAbove j)
      have ⟨hx_ne, hx_lt, hx_mem⟩ : x ≠ c ∧ x < c.succAbove j ∧ v ∈ R.bag x := by
        dsimp only [x]
        split_ifs with hpc
        · have hpc_lt := R.parent_lt c hc0
          exact ⟨ne_of_lt hpc_lt, hpc_lt.trans (lt_of_eq_of_lt hpc.symm hpk), hsub (hpc ▸ hmem_p)⟩
        · exact ⟨hpc, hpk, hmem_p⟩
      have hx_eq : c.succAbove ((c.pred hc0).predAbove x) = x :=
        succAbove_predAbove_of_ne hc0 hx_ne
      have hx' : v ∈ R.bag (c.succAbove ((c.pred hc0).predAbove x)) := by rwa [hx_eq]
      have hadj : ((parentTree parent').induce {m | v ∈ R.bag (c.succAbove m)}).Adj
          ⟨j, hj⟩ ⟨(c.pred hc0).predAbove x, hx'⟩ := by
        change (parentTree parent').Adj j ((c.pred hc0).predAbove x)
        rw [parentTree_adj hplt]
        exact Or.inl ⟨fun h0 => hj0 (h0 ▸ hzero), hpar j⟩
      exact hadj.reachable.trans (ih x hx_lt _ hx_eq hx')

/-- Contract a nonroot node `c` whose bag is a subset of its parent's bag, reducing the node
count by one without increasing the width. -/
def contractStep {n : ℕ} (R : G.RootedTreeDecomposition (n + 1)) (c : Fin (n + 2)) (hc0 : c ≠ 0)
    (hsub : R.bag c ⊆ R.bag (R.parent c)) : G.RootedTreeDecomposition n :=
  let drop : Fin (n + 2) → Fin (n + 1) := (c.pred hc0).predAbove
  let parent' : Fin (n + 1) → Fin (n + 1) := fun j =>
    let p := R.parent (c.succAbove j)
    drop (if p = c then R.parent c else p)
  have hzero : c.succAbove 0 = 0 := (Fin.succAbove_eq_zero_iff hc0).mpr rfl
  have hp0 : parent' 0 = 0 := by
    have h0 : R.parent (c.succAbove 0) = 0 := by rw [hzero, R.parent_zero]
    dsimp [parent', drop]
    rw [h0, ite_eq_right (fun h => absurd h hc0.symm)]
    exact Fin.succAbove_right_injective (p := c)
      (by rw [succAbove_predAbove_of_ne hc0 hc0.symm, hzero])
  have hplt : ∀ j : Fin (n + 1), j ≠ 0 → parent' j < j := fun j hj0 => by
    have hpk := R.parent_lt (c.succAbove j) ((Fin.succAbove_eq_zero_iff hc0).not.mpr hj0)
    dsimp [parent', drop]
    rw [← Fin.succAbove_lt_succAbove_iff (p := c)]
    split_ifs with hpc
    · have hpc_lt := R.parent_lt c hc0
      rw [succAbove_predAbove_of_ne hc0 (ne_of_lt hpc_lt)]
      exact hpc_lt.trans (lt_of_eq_of_lt hpc.symm hpk)
    · rwa [succAbove_predAbove_of_ne hc0 hpc]
  have hcov (i : Fin (n + 2)) : ∃ j : Fin (n + 1), R.bag i ⊆ R.bag (c.succAbove j) := by
    by_cases hic : i = c
    · exact ⟨drop (R.parent c), by
        rw [succAbove_predAbove_of_ne hc0 (ne_of_lt (R.parent_lt c hc0)), hic]; exact hsub⟩
    · exact ⟨drop i, by rw [succAbove_predAbove_of_ne hc0 hic]⟩
  { parent := parent'
    parent_zero := hp0
    parent_lt := hplt
    bag := fun j => R.bag (c.succAbove j)
    exists_mem_bag := fun v =>
      (R.exists_mem_bag v).elim fun i hi => (hcov i).imp fun _ hj => hj hi
    exists_adj_mem_bag := fun _ _ huv =>
      (R.exists_adj_mem_bag huv).elim fun i ⟨hu, hv⟩ => (hcov i).imp fun _ hj => ⟨hj hu, hj hv⟩
    top_unique := fun v _ _ hi hit hj hjt => by
      have htop_ne : R.top v ≠ c := fun htc => by
        have htop := R.isTop_iff_mem.1 (R.isTop_top v)
        rw [htc] at htop
        exact htop.2.elim hc0 (· (hsub htop.1))
      have ht' : v ∈ R.bag (c.succAbove (drop (R.top v))) := by
        rw [succAbove_predAbove_of_ne hc0 htop_ne]; exact R.mem_bag_top v
      have hreach := contractStep_reach R c hc0 hsub parent' (fun _ => rfl) hplt v htop_ne ht'
        fun k hk hnt => by by_contra hnot; exact hnt (R.isTop_iff_mem.2 ⟨hk, Or.inr hnot⟩)
      exact eq_of_preconnected_parentTree hp0 hplt
        (fun a b => (hreach _ a.1 rfl a.2).trans (hreach _ b.1 rfl b.2).symm) hi hit hj hjt }

theorem contractStep_width_le {n : ℕ} (R : G.RootedTreeDecomposition (n + 1)) (c : Fin (n + 2))
    (hc0 : c ≠ 0) (hsub : R.bag c ⊆ R.bag (R.parent c)) :
    (R.contractStep c hc0 hsub).width ≤ R.width :=
  (width_le_iff _).2 fun _ => by
    change (R.bag _).card ≤ R.width + 1
    exact R.card_bag_le _

/-- Iteratively contract all nonroot nodes whose bag is contained in their parent's bag. -/
def prune : ∀ {n : ℕ}, G.RootedTreeDecomposition n → Σ m : ℕ, G.RootedTreeDecomposition m
  | 0, R => ⟨0, R⟩
  | n + 1, R =>
    match h : (Finset.univ.filter fun c : Fin (n + 2) =>
        c ≠ 0 ∧ R.bag c ⊆ R.bag (R.parent c)).min with
    | none => ⟨n + 1, R⟩
    | some c =>
      have hc := (Finset.mem_filter.1 (Finset.mem_of_min h)).2
      prune (R.contractStep c hc.1 hc.2)

theorem prune_width_le : ∀ {n : ℕ} (R : G.RootedTreeDecomposition n), R.prune.2.width ≤ R.width
  | 0, _ => le_rfl
  | n + 1, R => by
    conv_lhs => rw [prune]
    split
    · exact le_rfl
    · rename_i c h
      have hc := (Finset.mem_filter.1 (Finset.mem_of_min h)).2
      exact (prune_width_le _).trans (R.contractStep_width_le c hc.1 hc.2)

theorem not_subset_parent_of_prune :
    ∀ {n : ℕ} (R : G.RootedTreeDecomposition n) (c : Fin (R.prune.1 + 1)),
      c ≠ 0 → ¬R.prune.2.bag c ⊆ R.prune.2.bag (R.prune.2.parent c)
  | 0, _, c, hc => absurd (Fin.eq_zero c) hc
  | n + 1, R, c, hc => by
    revert c hc
    rw [prune]
    split <;> dsimp only at *
    · rename_i hnone
      exact fun c hc hsub => Finset.eq_empty_iff_forall_notMem.1 (Finset.min_eq_top.1 hnone) c
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc, hsub⟩)
    · rename_i c' hsome
      intro c hc
      have hc' := (Finset.mem_filter.1 (Finset.mem_of_min hsome)).2
      exact not_subset_parent_of_prune (R.contractStep c' hc'.1 hc'.2) c hc

/-- When the vertex type `V` is finite, pruning leaves at most `card V + 1` nodes (`m ≤ card V`),
since every nonroot node introduces at least one vertex whose topmost node it is. -/
theorem prune_nodes_le [Fintype V] {n : ℕ} (R : G.RootedTreeDecomposition n) :
    R.prune.1 ≤ Fintype.card V := by
  classical
  let R' := R.prune.2
  have hdiff (c : {c : Fin (R.prune.1 + 1) // c ≠ 0}) : ∃ v : V, R'.top v = c.1 := by
    obtain ⟨v, hvc, hvp⟩ := Finset.not_subset.1 (not_subset_parent_of_prune R c.1 c.2)
    exact ⟨v, (R'.isTop_iff.1 (R'.isTop_iff_mem.2 ⟨hvc, Or.inr hvp⟩)).symm⟩
  have hcard := Fintype.card_le_of_injective (fun c => (hdiff c).choose) fun a b hab =>
    Subtype.ext (by
      rw [← (hdiff a).choose_spec, ← (hdiff b).choose_spec]; exact congrArg R'.top hab)
  simpa [Fintype.card_subtype_compl] using hcard

end RootedTreeDecomposition

/-! ### Converting `RootedTreeDecomposition` and `TreeDecomposition` to `NiceTreeDecomposition` -/

namespace NiceTree

variable {V : Type uV} [DecidableEq V]

/-- Wrap `t` in a chain of `introduce` nodes for each element of `vs`. -/
@[expose] def introduceChain : List V → NiceTree V → NiceTree V
  | [], t => t
  | v :: vs, t => .introduce v (introduceChain vs t)

/-- Wrap `t` in a chain of `forget` nodes for each element of `vs`. -/
@[expose] def forgetChain : List V → NiceTree V → NiceTree V
  | [], t => t
  | v :: vs, t => .forget v (forgetChain vs t)

/-- Join a nonempty list of nice trees using binary `join` nodes. -/
@[expose] def joinTrees : NiceTree V → List (NiceTree V) → NiceTree V
  | t, [] => t
  | t, u :: us => .join t (joinTrees u us)

omit [DecidableEq V] in
private theorem size_introduceChain (vs : List V) (t : NiceTree V) :
    (introduceChain vs t).size = vs.length + t.size := by
  induction vs with
  | nil => simp [introduceChain]
  | cons v vs ih => simp only [introduceChain, size_introduce, ih, List.length_cons]; omega

omit [DecidableEq V] in
private theorem size_forgetChain (vs : List V) (t : NiceTree V) :
    (forgetChain vs t).size = vs.length + t.size := by
  induction vs with
  | nil => simp [forgetChain]
  | cons v vs ih => simp only [forgetChain, size_forget, ih, List.length_cons]; omega

private theorem bag_introduceChain (vs : List V) (t : NiceTree V) :
    (introduceChain vs t).bag = vs.toFinset ∪ t.bag := by
  fun_induction introduceChain vs t <;> simp_all [bag]

private theorem subtreeVerts_introduceChain (vs : List V) (t : NiceTree V) :
    (introduceChain vs t).subtreeVerts = vs.toFinset ∪ t.subtreeVerts := by
  fun_induction introduceChain vs t <;> simp_all [subtreeVerts]

private theorem localValid_introduceChain {vs : List V} {t : NiceTree V}
    (hnd : vs.Nodup) (hdisj : ∀ v ∈ vs, v ∉ t.subtreeVerts) (ht : t.LocalValid) :
    (introduceChain vs t).LocalValid := by
  induction vs with
  | nil => exact ht
  | cons v vs ih =>
    rw [List.nodup_cons] at hnd
    refine ⟨?_, ih hnd.2 (fun w hw => hdisj w (List.mem_cons_of_mem _ hw))⟩
    rw [subtreeVerts_introduceChain, Finset.mem_union, List.mem_toFinset]
    rintro (hv | hv)
    · exact hnd.1 hv
    · exact hdisj v List.mem_cons_self hv

private theorem maxBagCard_introduceChain_le (vs : List V) (t : NiceTree V) :
    (introduceChain vs t).maxBagCard ≤ max (vs.toFinset ∪ t.bag).card t.maxBagCard := by
  induction vs with
  | nil => simp [introduceChain]
  | cons v vs ih =>
    simp only [introduceChain, maxBagCard]
    refine max_le ?_ (ih.trans (max_le_max ?_ le_rfl))
    · have hsub : insert v (introduceChain vs t).bag ⊆ (v :: vs).toFinset ∪ t.bag := by
        rw [bag_introduceChain, List.toFinset_cons, Finset.insert_union]
      exact (Finset.card_le_card hsub).trans (le_max_left _ _)
    · exact Finset.card_le_card (Finset.union_subset_union_left (by
        rw [List.toFinset_cons]; exact Finset.subset_insert _ _))

private theorem coversFinset_introduceChain {vs : List V} {t : NiceTree V} {K : Finset V}
    (h : t.CoversFinset K) : (introduceChain vs t).CoversFinset K := by
  induction vs with
  | nil => exact h
  | cons v vs ih => exact Or.inr ih

private theorem bag_forgetChain (vs : List V) (t : NiceTree V) :
    (forgetChain vs t).bag = t.bag \ vs.toFinset := by
  induction vs with
  | nil => simp [forgetChain]
  | cons v vs ih =>
    simp only [forgetChain, bag, ih, List.toFinset_cons]
    ext x
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
    tauto

private theorem subtreeVerts_forgetChain (vs : List V) (t : NiceTree V) :
    (forgetChain vs t).subtreeVerts = t.subtreeVerts := by
  fun_induction forgetChain vs t <;> simp_all [subtreeVerts]

private theorem localValid_forgetChain {vs : List V} {t : NiceTree V}
    (hnd : vs.Nodup) (hsub : ∀ v ∈ vs, v ∈ t.bag) (ht : t.LocalValid) :
    (forgetChain vs t).LocalValid := by
  induction vs with
  | nil => exact ht
  | cons v vs ih =>
    rw [List.nodup_cons] at hnd
    refine ⟨?_, ih hnd.2 (fun w hw => hsub w (List.mem_cons_of_mem _ hw))⟩
    rw [bag_forgetChain, Finset.mem_sdiff, List.mem_toFinset]
    exact ⟨hsub v List.mem_cons_self, hnd.1⟩

private theorem maxBagCard_forgetChain_le (vs : List V) (t : NiceTree V) :
    (forgetChain vs t).maxBagCard ≤ t.maxBagCard := by
  induction vs with
  | nil => exact le_rfl
  | cons v vs ih =>
    simp only [forgetChain, maxBagCard]
    refine max_le ?_ ih
    have hsub : (forgetChain vs t).bag.erase v ⊆ t.bag := by
      rw [bag_forgetChain]
      exact (Finset.erase_subset v _).trans Finset.sdiff_subset
    exact (Finset.card_le_card hsub).trans t.card_bag_le_maxBagCard

private theorem coversFinset_forgetChain {vs : List V} {t : NiceTree V} {K : Finset V}
    (h : t.CoversFinset K) : (forgetChain vs t).CoversFinset K := by
  induction vs with
  | nil => exact h
  | cons v vs ih => exact Or.inr ih

private theorem bag_joinTrees (t : NiceTree V) (ts : List (NiceTree V)) :
    (joinTrees t ts).bag = t.bag := by
  cases ts with
  | nil => rfl
  | cons u us => simp [joinTrees, bag]

private theorem mem_subtreeVerts_joinTrees {t : NiceTree V} {ts : List (NiceTree V)} {v : V} :
    v ∈ (joinTrees t ts).subtreeVerts ↔ v ∈ t.subtreeVerts ∨ ∃ u ∈ ts, v ∈ u.subtreeVerts := by
  fun_induction joinTrees t ts <;> simp_all [subtreeVerts]

private theorem maxBagCard_joinTrees_le (t : NiceTree V) (ts : List (NiceTree V))
    (hbags : ∀ u ∈ ts, u.bag = t.bag) :
    (joinTrees t ts).maxBagCard ≤ max t.maxBagCard ((ts.map maxBagCard).foldr max 0) := by
  induction ts generalizing t with
  | nil => simp [joinTrees]
  | cons u us ih =>
    have hus : ∀ w ∈ us, w.bag = u.bag := fun w hw =>
      (hbags w (List.mem_cons_of_mem _ hw)).trans (hbags u List.mem_cons_self).symm
    have ihu := ih (t := u) hus
    simp only [joinTrees, maxBagCard, List.map_cons, List.foldr_cons]
    refine max_le (t.card_bag_le_maxBagCard.trans (le_max_left _ _)) (max_le (le_max_left _ _) ?_)
    exact ihu.trans (max_le ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _)))

omit [DecidableEq V] in
private theorem size_joinTrees (t : NiceTree V) (ts : List (NiceTree V)) :
    (joinTrees t ts).size = t.size + ts.length + (ts.map size).sum := by
  induction ts generalizing t with
  | nil => simp [joinTrees]
  | cons u us ih =>
    simp only [joinTrees, size_join, ih u, List.length_cons, List.map_cons, List.sum_cons]
    omega

private theorem localValid_joinTrees {B : Finset V} :
    ∀ (t : NiceTree V) (ts : List (NiceTree V)),
      t.bag = B → (∀ u ∈ ts, u.bag = B) →
      t.LocalValid → (∀ u ∈ ts, u.LocalValid) →
      (t :: ts).Pairwise (fun u w => Disjoint (u.subtreeVerts \ B) w.subtreeVerts) →
      (joinTrees t ts).LocalValid
  | t, [], _, _, ht, _, _ => ht
  | t, u :: us, hBt, hBus, ht, hLus, hpair => by
    rw [List.pairwise_cons] at hpair
    have hBu : u.bag = B := hBus u List.mem_cons_self
    have hjoin_bag : (joinTrees u us).bag = B := (bag_joinTrees u us).trans hBu
    have hvalidR : (joinTrees u us).LocalValid :=
      localValid_joinTrees u us hBu (fun w hw => hBus w (List.mem_cons_of_mem _ hw))
        (hLus u List.mem_cons_self) (fun w hw => hLus w (List.mem_cons_of_mem _ hw)) hpair.2
    refine ⟨hBt.trans hjoin_bag.symm, ?_, ht, hvalidR⟩
    rw [Finset.disjoint_left]
    intro x hxt hxj
    rw [hBt] at hxt
    rcases mem_subtreeVerts_joinTrees.1 hxj with hxu | ⟨w, hw, hxw⟩
    · exact Finset.disjoint_left.1 (hpair.1 u List.mem_cons_self) hxt hxu
    · exact Finset.disjoint_left.1 (hpair.1 w (List.mem_cons_of_mem _ hw)) hxt hxw

private theorem coversFinset_joinTrees {t : NiceTree V} {ts : List (NiceTree V)} {K : Finset V}
    (h : t.CoversFinset K ∨ ∃ u ∈ ts, u.CoversFinset K) : (joinTrees t ts).CoversFinset K := by
  induction ts generalizing t with
  | nil =>
    rcases h with h | ⟨u, hu, -⟩
    · exact h
    · exact absurd hu List.not_mem_nil
  | cons u us ih =>
    rcases h with h | ⟨w, hw, hcov⟩
    · exact Or.inr (Or.inl h)
    · rcases List.mem_cons.1 hw with rfl | hwu
      · exact Or.inr (Or.inr (ih (Or.inl hcov)))
      · exact Or.inr (Or.inr (ih (Or.inr ⟨w, hwu, hcov⟩)))

end NiceTree

namespace RootedTreeDecomposition

open NiceTree

variable {V : Type uV} {G : SimpleGraph V} [DecidableEq V]

/-- Wrap a converted child subtree `sub` of `c` into the forget/introduce step matching bag `i`. -/
private def niceStep (toList : Finset V → List V) {n : ℕ} (R : G.RootedTreeDecomposition n)
    (i c : Fin (n + 1)) (sub : NiceTree V) : NiceTree V :=
  introduceChain (toList (R.bag i \ R.bag c)) (forgetChain (toList (R.bag c \ R.bag i)) sub)

omit [DecidableEq V] in
private theorem desc_measure_lt {n : ℕ} {R : G.RootedTreeDecomposition n}
    {i c : Fin (n + 1)} (hc : c ∈ R.children i) : n - c.val < n - i.val := by
  have := R.lt_of_mem_children hc
  rw [Fin.lt_def] at this
  have : c.val ≤ n := Nat.lt_succ_iff.1 c.isLt
  omega

/-- Subtree conversion from node `i` using an explicit duplicate-free list enumerator `toList` for
`Finset V`. -/
private def toNiceSubtreeCore (toList : Finset V → List V) {n : ℕ}
    (R : G.RootedTreeDecomposition n) (i : Fin (n + 1)) : NiceTree V :=
  let cs := (R.children i).sort (· ≤ ·)
  if hcs : cs = [] then
    introduceChain (toList (R.bag i)) .leaf
  else
    let branches := cs.pmap (fun c hc =>
      have hmem : c ∈ R.children i := (Finset.mem_sort _).1 hc
      have _hlt : n - c.val < n - i.val := desc_measure_lt hmem
      niceStep toList R i c (toNiceSubtreeCore toList R c)) (fun _ hc => hc)
    match hbr : branches with
    | b :: bs => joinTrees b bs
    | [] => by
      have hlen : cs.length = 0 := by
        calc
          cs.length = branches.length := List.length_pmap.symm
          _ = 0 := by rw [hbr, List.length_nil]
      exact absurd (List.eq_nil_of_length_eq_zero hlen) hcs
termination_by n - i.val

private theorem toNiceSubtreeCore_eq_joinTrees (toList : Finset V → List V) {n : ℕ}
    (R : G.RootedTreeDecomposition n) (i : Fin (n + 1)) {c₀ : Fin (n + 1)}
    {cs : List (Fin (n + 1))} (hcs : (R.children i).sort (· ≤ ·) = c₀ :: cs) :
    toNiceSubtreeCore toList R i =
      joinTrees (niceStep toList R i c₀ (toNiceSubtreeCore toList R c₀))
        (cs.map fun c => niceStep toList R i c (toNiceSubtreeCore toList R c)) := by
  have hne : (R.children i).sort (· ≤ ·) ≠ [] := by rw [hcs]; exact List.cons_ne_nil _ _
  have hpm : ((R.children i).sort (· ≤ ·)).pmap
      (fun c _ => niceStep toList R i c (toNiceSubtreeCore toList R c)) (fun _ hc => hc) =
      niceStep toList R i c₀ (toNiceSubtreeCore toList R c₀) ::
        cs.map (fun c => niceStep toList R i c (toNiceSubtreeCore toList R c)) := by
    rw [List.pmap_eq_map, hcs, List.map_cons]
  conv_lhs => rw [toNiceSubtreeCore]
  rw [dite_eq_right hne]
  dsimp only
  split
  · rename_i b' bs' heq
    have hEq := hpm.symm.trans heq
    injection hEq with hb hbs
    rw [hb, hbs]
  · rename_i heq
    exact absurd (hpm.symm.trans heq) (List.cons_ne_nil _ _)

/-- Convert a rooted tree decomposition to a nice tree decomposition using `toList` to order
each bag or difference finset. -/
private def toNiceCore (toList : Finset V → List V) {n : ℕ}
    (R : G.RootedTreeDecomposition n) : NiceTree V :=
  forgetChain (toList (R.bag 0)) (toNiceSubtreeCore toList R 0)

private structure ListSpec (toList : Finset V → List V) : Prop where
  nodup : ∀ S, (toList S).Nodup
  mem : ∀ S v, v ∈ toList S ↔ v ∈ S

private theorem toFinset_of_listSpec {toList : Finset V → List V} (hs : ListSpec toList)
    (S : Finset V) : (toList S).toFinset = S :=
  Finset.ext fun v => by simp only [List.mem_toFinset, hs.mem]

omit [DecidableEq V] in
private theorem length_le_card_of_listSpec {toList : Finset V → List V} (hs : ListSpec toList)
    (S : Finset V) : (toList S).length ≤ S.card := by
  classical
  rw [← List.toFinset_card_of_nodup (hs.nodup S), toFinset_of_listSpec hs]

omit [DecidableEq V] in
private theorem foldr_max_le_of_forall {α : Type*} (f : α → ℕ) (k : ℕ) :
    ∀ (l : List α), (∀ x ∈ l, f x ≤ k) → (l.map f).foldr max 0 ≤ k
  | [], _ => Nat.zero_le k
  | x :: xs, hx => max_le (hx x List.mem_cons_self)
      (foldr_max_le_of_forall f k xs fun y hy => hx y (List.mem_cons_of_mem _ hy))

omit [DecidableEq V] in
private theorem children_eq_empty_of_sort_nil {n : ℕ} {R : G.RootedTreeDecomposition n}
    {i : Fin (n + 1)} (hcs : (R.children i).sort (· ≤ ·) = []) : R.children i = ∅ :=
  Finset.eq_empty_of_forall_notMem fun _ hc => by simpa [hcs] using (Finset.mem_sort (· ≤ ·)).2 hc

private theorem niceStep_props {toList : Finset V → List V} (hs : ListSpec toList)
    {n : ℕ} {R : G.RootedTreeDecomposition n} {i c : Fin (n + 1)} (hc : c ∈ R.children i)
    {sub : NiceTree V} (hbag : sub.bag = R.bag c) (hsub : sub.subtreeVerts = R.subtreeVerts c)
    (hloc : sub.LocalValid) (hmax : sub.maxBagCard ≤ R.width + 1)
    (hcov : ∀ j, R.IsDescendant j c → sub.CoversFinset (R.bag j)) :
    (niceStep toList R i c sub).bag = R.bag i ∧
      (niceStep toList R i c sub).subtreeVerts = R.bag i ∪ R.subtreeVerts c ∧
      (niceStep toList R i c sub).LocalValid ∧
      (niceStep toList R i c sub).maxBagCard ≤ R.width + 1 ∧
      (∀ j, R.IsDescendant j c → (niceStep toList R i c sub).CoversFinset (R.bag j)) := by
  have hf_bag : (forgetChain (toList (R.bag c \ R.bag i)) sub).bag = R.bag c ∩ R.bag i := by
    rw [bag_forgetChain, hbag, toFinset_of_listSpec hs]
    exact Finset.ext fun _ => by simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  have hrecon : (R.bag i \ R.bag c) ∪ (R.bag c ∩ R.bag i) = R.bag i :=
    Finset.ext fun _ => by simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
  have hloc1 : (forgetChain (toList (R.bag c \ R.bag i)) sub).LocalValid :=
    localValid_forgetChain (hs.nodup _) (fun _ hv => by
      rw [hbag]; exact (Finset.mem_sdiff.1 ((hs.mem _ _).1 hv)).1) hloc
  refine ⟨?_, ?_, ?_, ?_, fun j hj => coversFinset_introduceChain (coversFinset_forgetChain
      (hcov j hj))⟩
  · dsimp only [niceStep]
    rw [bag_introduceChain, hf_bag, toFinset_of_listSpec hs, hrecon]
  · dsimp only [niceStep]
    rw [subtreeVerts_introduceChain, subtreeVerts_forgetChain, hsub, toFinset_of_listSpec hs]
    ext v
    have := fun hv => R.bag_subset_subtreeVerts c hv (x := v)
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  · refine localValid_introduceChain (hs.nodup _) (fun v hv hvc => ?_) hloc1
    rw [subtreeVerts_forgetChain, hsub] at hvc
    obtain ⟨hvi, hvc_not⟩ := Finset.mem_sdiff.1 ((hs.mem _ _).1 hv)
    exact hvc_not (R.mem_bag_of_mem_subtreeVerts_of_mem_bag_parent hvc
      (by rwa [(mem_children.1 hc).2]))
  · refine (maxBagCard_introduceChain_le _ _).trans
      (max_le ?_ ((maxBagCard_forgetChain_le _ _).trans hmax))
    rw [hf_bag, toFinset_of_listSpec hs, hrecon]
    exact R.card_bag_le i

private theorem toNiceSubtreeCore_props_nil (toList : Finset V → List V) (hs : ListSpec toList)
    {n : ℕ} (R : G.RootedTreeDecomposition n) (i : Fin (n + 1))
    (hcs : (R.children i).sort (· ≤ ·) = []) :
    (introduceChain (toList (R.bag i)) .leaf).bag = R.bag i ∧
      (introduceChain (toList (R.bag i)) .leaf).subtreeVerts = R.subtreeVerts i ∧
      (introduceChain (toList (R.bag i)) .leaf).LocalValid ∧
      (introduceChain (toList (R.bag i)) .leaf).maxBagCard ≤ R.width + 1 ∧
      (∀ j, R.IsDescendant j i → (introduceChain (toList (R.bag i)) .leaf).CoversFinset
        (R.bag j)) := by
  have hempty := children_eq_empty_of_sort_nil hcs
  have hno : ∀ c, c ∉ R.children i := fun c => hempty ▸ Finset.notMem_empty c
  have hsub_eq : R.subtreeVerts i = R.bag i :=
    Finset.Subset.antisymm (fun v hv => by_contra fun hvi => by
      obtain ⟨c, hc, -⟩ := R.exists_mem_children_of_mem_subtreeVerts hv hvi
      exact hno c hc) (R.bag_subset_subtreeVerts i)
  refine ⟨?_, ?_, localValid_introduceChain (hs.nodup _) (fun _ _ => Finset.notMem_empty _) trivial,
      ?_, fun j hj => ?_⟩
  · rw [bag_introduceChain, toFinset_of_listSpec hs]; exact Finset.union_empty _
  · rw [subtreeVerts_introduceChain, toFinset_of_listSpec hs, hsub_eq]; exact Finset.union_empty _
  · refine (maxBagCard_introduceChain_le _ _).trans (max_le ?_ (Nat.zero_le _))
    rw [toFinset_of_listSpec hs]; change (R.bag i ∪ ∅).card ≤ _; rw [Finset.union_empty]
    exact R.card_bag_le i
  · by_cases hji : j = i
    · subst hji
      exact coversFinset_of_subset_bag (by simp [bag_introduceChain, toFinset_of_listSpec hs])
    · obtain ⟨c, hc, -⟩ := exists_mem_children_of_isDescendant hj hji
      exact absurd hc (hno c)

private theorem joinBranches_subtreeVerts {n : ℕ} {R : G.RootedTreeDecomposition n}
    {i c₀ : Fin (n + 1)} {cs : List (Fin (n + 1))} (hcs : (R.children i).sort (· ≤ ·) = c₀ :: cs)
    {br : Fin (n + 1) → NiceTree V}
    (hsub : ∀ c ∈ R.children i, (br c).subtreeVerts = R.bag i ∪ R.subtreeVerts c) :
    (joinTrees (br c₀) (cs.map br)).subtreeVerts = R.subtreeVerts i := by
  have hmem_sort (c : Fin (n + 1)) : c ∈ c₀ :: cs ↔ c ∈ R.children i := by
    rw [← hcs, Finset.mem_sort]
  have hc₀ := (hmem_sort c₀).1 List.mem_cons_self
  refine Finset.Subset.antisymm (fun v hv => ?_) (fun v hv => ?_)
  · have of_child (c) (hc : c ∈ R.children i) (hvc : v ∈ (br c).subtreeVerts) :
        v ∈ R.subtreeVerts i := by
      rw [hsub c hc] at hvc
      exact (Finset.mem_union.1 hvc).elim (R.bag_subset_subtreeVerts i ·)
        (R.subtreeVerts_subset_of_mem_children hc ·)
    rcases mem_subtreeVerts_joinTrees.1 hv with h | ⟨_, hu, h⟩
    · exact of_child c₀ hc₀ h
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hu
      exact of_child c ((hmem_sort c).1 (List.mem_cons_of_mem _ hc)) h
  · by_cases hvi : v ∈ R.bag i
    · exact mem_subtreeVerts_joinTrees.2
        (Or.inl (by rw [hsub c₀ hc₀]; exact Finset.mem_union_left _ hvi))
    · obtain ⟨c, hc, hvc⟩ := R.exists_mem_children_of_mem_subtreeVerts hv hvi
      have hv_br : v ∈ (br c).subtreeVerts := by
        rw [hsub c hc]; exact Finset.mem_union_right _ hvc
      exact mem_subtreeVerts_joinTrees.2 (match (hmem_sort c).2 hc with
        | .head _ => Or.inl hv_br
        | .tail _ hmc => Or.inr ⟨br c, List.mem_map_of_mem hmc, hv_br⟩)

private theorem joinBranches_props {n : ℕ} {R : G.RootedTreeDecomposition n}
    {i c₀ : Fin (n + 1)} {cs : List (Fin (n + 1))} (hcs : (R.children i).sort (· ≤ ·) = c₀ :: cs)
    {br : Fin (n + 1) → NiceTree V}
    (hbr : ∀ c ∈ R.children i,
      (br c).bag = R.bag i ∧ (br c).subtreeVerts = R.bag i ∪ R.subtreeVerts c ∧
        (br c).LocalValid ∧ (br c).maxBagCard ≤ R.width + 1 ∧
        (∀ j, R.IsDescendant j c → (br c).CoversFinset (R.bag j))) :
    (joinTrees (br c₀) (cs.map br)).bag = R.bag i ∧
      (joinTrees (br c₀) (cs.map br)).subtreeVerts = R.subtreeVerts i ∧
      (joinTrees (br c₀) (cs.map br)).LocalValid ∧
      (joinTrees (br c₀) (cs.map br)).maxBagCard ≤ R.width + 1 ∧
      (∀ j, R.IsDescendant j i → (joinTrees (br c₀) (cs.map br)).CoversFinset (R.bag j)) := by
  have hmem_sort (c : Fin (n + 1)) : c ∈ c₀ :: cs ↔ c ∈ R.children i := by
    rw [← hcs, Finset.mem_sort]
  have hc₀ := (hmem_sort c₀).1 List.mem_cons_self
  have hcs_mem {c} (hc : c ∈ cs) := (hmem_sort c).1 (List.mem_cons_of_mem _ hc)
  have hbag_cs : ∀ u ∈ cs.map br, u.bag = R.bag i := fun _ hu => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hu; exact (hbr c (hcs_mem hc)).1
  have hpair_nd : (c₀ :: cs).Pairwise (· ≠ ·) := by
    rw [← hcs, ← List.nodup_iff_pairwise_ne]; exact (R.children i).sort_nodup _
  have hpair_br : (br c₀ :: cs.map br).Pairwise
      (fun u w => Disjoint (u.subtreeVerts \ R.bag i) w.subtreeVerts) := by
    rw [← List.map_cons, List.pairwise_map]
    refine hpair_nd.imp_of_mem fun {c₁ c₂} hc₁ hc₂ hne => ?_
    rw [hmem_sort] at hc₁ hc₂
    rw [(hbr c₁ hc₁).2.1, (hbr c₂ hc₂).2.1, Finset.disjoint_left]
    intro v hv₁ hv₂
    obtain ⟨h1, hvnot⟩ := Finset.mem_sdiff.1 hv₁
    exact hne (R.eq_of_mem_subtreeVerts_of_mem_children hc₁ hc₂
      ((Finset.mem_union.1 h1).resolve_left hvnot)
      ((Finset.mem_union.1 hv₂).resolve_left hvnot) hvnot)
  refine ⟨(bag_joinTrees _ _).trans (hbr c₀ hc₀).1,
    joinBranches_subtreeVerts hcs (fun c hc => (hbr c hc).2.1), ?_, ?_, fun j hj => ?_⟩
  · refine localValid_joinTrees (br c₀) (cs.map br) (hbr c₀ hc₀).1 hbag_cs (hbr c₀ hc₀).2.2.1
      (fun _ hu => ?_) hpair_br
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hu; exact (hbr c (hcs_mem hc)).2.2.1
  · refine (maxBagCard_joinTrees_le _ _ fun u hu =>
        (hbag_cs u hu).trans (hbr c₀ hc₀).1.symm).trans
      (max_le (hbr c₀ hc₀).2.2.2.1 (foldr_max_le_of_forall maxBagCard _ _ fun _ hu => ?_))
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hu; exact (hbr c (hcs_mem hc)).2.2.2.1
  · by_cases hji : j = i
    · subst hji; exact coversFinset_of_subset_bag (by rw [bag_joinTrees, (hbr c₀ hc₀).1])
    · obtain ⟨c, hc, hjc⟩ := exists_mem_children_of_isDescendant hj hji
      have hcov := (hbr c hc).2.2.2.2 j hjc
      exact coversFinset_joinTrees (match (hmem_sort c).2 hc with
        | .head _ => Or.inl hcov
        | .tail _ hmc => Or.inr ⟨br c, List.mem_map_of_mem hmc, hcov⟩)

private theorem toNiceSubtreeCore_props (toList : Finset V → List V) (hs : ListSpec toList)
    {n : ℕ} (R : G.RootedTreeDecomposition n) (i : Fin (n + 1)) :
    (toNiceSubtreeCore toList R i).bag = R.bag i ∧
      (toNiceSubtreeCore toList R i).subtreeVerts = R.subtreeVerts i ∧
      (toNiceSubtreeCore toList R i).LocalValid ∧
      (toNiceSubtreeCore toList R i).maxBagCard ≤ R.width + 1 ∧
      (∀ j, R.IsDescendant j i → (toNiceSubtreeCore toList R i).CoversFinset (R.bag j)) := by
  cases hcs : (R.children i).sort (· ≤ ·) with
  | nil =>
    rw [toNiceSubtreeCore, dite_eq_left hcs]
    exact toNiceSubtreeCore_props_nil toList hs R i hcs
  | cons c₀ cs =>
    rw [toNiceSubtreeCore_eq_joinTrees toList R i hcs]
    refine joinBranches_props hcs
      (br := fun c => niceStep toList R i c (toNiceSubtreeCore toList R c)) fun c hc => ?_
    have _hlt : n - c.val < n - i.val := desc_measure_lt hc
    obtain ⟨h1, h2, h3, h4, h5⟩ := toNiceSubtreeCore_props toList hs R c
    exact niceStep_props hs hc h1 h2 h3 h4 h5
termination_by n - i.val

open scoped Classical in
/-- Number of nodes in the subtree rooted at `i`. -/
private noncomputable def subtreeNodes {n : ℕ} (R : G.RootedTreeDecomposition n)
    (i : Fin (n + 1)) : ℕ :=
  (Finset.univ.filter (R.IsDescendant · i)).card

omit [DecidableEq V] in
open scoped Classical in
private theorem subtreeNodes_zero {n : ℕ} (R : G.RootedTreeDecomposition n) :
    subtreeNodes R 0 = n + 1 := by
  rw [subtreeNodes, Finset.filter_true_of_mem fun j _ => R.isDescendant_zero j, Finset.card_univ,
    Fintype.card_fin]

omit [DecidableEq V] in
open scoped Classical in
private theorem subtreeNodes_eq {n : ℕ} (R : G.RootedTreeDecomposition n) (i : Fin (n + 1)) :
    subtreeNodes R i = 1 + ∑ c ∈ R.children i, subtreeNodes R c := by
  have hpart : Finset.univ.filter (R.IsDescendant · i) =
      insert i ((R.children i).biUnion fun c => Finset.univ.filter (R.IsDescendant · c)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨fun hj => if hji : j = i then Or.inl hji
        else Or.inr (exists_mem_children_of_isDescendant hj hji), ?_⟩
    rintro (rfl | ⟨c, hc, hjc⟩)
    · exact R.isDescendant_refl _
    · exact hjc.trans (R.isDescendant_of_mem_children hc)
  have hnot : i ∉ (R.children i).biUnion fun c => Finset.univ.filter (R.IsDescendant · c) := by
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, not_exists,
      not_and]
    exact fun c hc hci => absurd (R.lt_of_mem_children hc) (not_lt.2 hci.le)
  have hdisj : Set.PairwiseDisjoint (R.children i : Set (Fin (n + 1)))
      fun c => Finset.univ.filter (R.IsDescendant · c) := by
    exact fun c₁ hc₁ c₂ hc₂ hne s h1 h2 j hj => absurd (R.eq_of_mem_children hc₁ hc₂
      (Finset.mem_filter.1 (h1 hj)).2 (Finset.mem_filter.1 (h2 hj)).2) hne
  rw [subtreeNodes, hpart, Finset.card_insert_of_notMem hnot, Finset.card_biUnion hdisj,
    Nat.add_comm]
  rfl

private theorem size_toNiceSubtreeCore_le (toList : Finset V → List V) (hs : ListSpec toList)
    {n : ℕ} (R : G.RootedTreeDecomposition n) (i : Fin (n + 1)) :
    (toNiceSubtreeCore toList R i).size + (2 * R.width + 3) ≤
      (3 * R.width + 5) * subtreeNodes R i := by
  cases hcs : (R.children i).sort (· ≤ ·) with
  | nil =>
    rw [toNiceSubtreeCore, dite_eq_left hcs, size_introduceChain, subtreeNodes_eq,
      children_eq_empty_of_sort_nil hcs, Finset.sum_empty, Nat.add_zero, size_leaf]
    have := (length_le_card_of_listSpec hs (R.bag i)).trans (R.card_bag_le i)
    omega
  | cons c₀ cs =>
    let br (c : Fin (n + 1)) := niceStep toList R i c (toNiceSubtreeCore toList R c)
    have hbr_sz (c : Fin (n + 1)) (hc : c ∈ R.children i) :
        (br c).size + 1 ≤ (3 * R.width + 5) * subtreeNodes R c := by
      have _hlt := desc_measure_lt hc
      have ih := size_toNiceSubtreeCore_le toList hs R c
      have h1 := (length_le_card_of_listSpec hs (R.bag i \ R.bag c)).trans
        ((Finset.card_le_card Finset.sdiff_subset).trans (R.card_bag_le i))
      have h2 := (length_le_card_of_listSpec hs (R.bag c \ R.bag i)).trans
        ((Finset.card_le_card Finset.sdiff_subset).trans (R.card_bag_le c))
      simp only [br, niceStep, size_introduceChain, size_forgetChain]
      omega
    have hsum_sort : ((c₀ :: cs).map fun c => (br c).size).sum =
        ∑ c ∈ R.children i, (br c).size := by
      rw [← hcs, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]; rfl
    have hlen_sort : (c₀ :: cs).length = (R.children i).card := by
      rw [← hcs, Finset.length_sort]
    have hsum_le : (joinTrees (br c₀) (cs.map br)).size + 1 ≤
        (3 * R.width + 5) * ∑ c ∈ R.children i, subtreeNodes R c := by
      have hsz : (joinTrees (br c₀) (cs.map br)).size + 1 =
          ∑ c ∈ R.children i, ((br c).size + 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, ← hsum_sort,
          ← hlen_sort, size_joinTrees, List.length_map, List.map_map]
        simp only [List.map_cons, List.sum_cons, List.length_cons, Function.comp_def]
        omega
      rw [hsz, Finset.mul_sum]
      exact Finset.sum_le_sum hbr_sz
    rw [toNiceSubtreeCore_eq_joinTrees toList R i hcs, subtreeNodes_eq, Nat.mul_add, Nat.mul_one]
    change (joinTrees (br c₀) (cs.map br)).size + _ ≤ _
    omega
termination_by n - i.val

private def toNiceDecompositionCore (toList : Finset V → List V) (hs : ListSpec toList)
    {n : ℕ} (R : G.RootedTreeDecomposition n) : G.NiceTreeDecomposition where
  tree := toNiceCore toList R
  localValid := by
    obtain ⟨hbag, _, hloc, _, _⟩ := toNiceSubtreeCore_props toList hs R 0
    exact localValid_forgetChain (hs.nodup _) (fun v hv => by
      rw [hbag]; exact (hs.mem _ v).1 hv) hloc
  bag_root := by
    obtain ⟨hbag, _, _, _, _⟩ := toNiceSubtreeCore_props toList hs R 0
    rw [toNiceCore, bag_forgetChain, hbag, toFinset_of_listSpec hs, Finset.sdiff_self]
  exists_mem_bag v := by
    obtain ⟨_, hsv, _, _, _⟩ := toNiceSubtreeCore_props toList hs R 0
    rw [toNiceCore, subtreeVerts_forgetChain, hsv]
    exact R.mem_subtreeVerts_zero v
  exists_adj_mem_bag u v huv := by
    obtain ⟨i, hu, hv⟩ := R.exists_adj_mem_bag huv
    obtain ⟨_, _, _, _, hcov⟩ := toNiceSubtreeCore_props toList hs R 0
    refine coversFinset_forgetChain (coversFinset_mono ?_ (hcov i (R.isDescendant_zero i)))
    exact Finset.insert_subset hu (Finset.singleton_subset_iff.2 hv)

private theorem toNiceDecompositionCore_width_le (toList : Finset V → List V) (hs : ListSpec toList)
    {n : ℕ} (R : G.RootedTreeDecomposition n) :
    (toNiceDecompositionCore toList hs R).width ≤ R.width := by
  obtain ⟨_, _, _, hmax, _⟩ := toNiceSubtreeCore_props toList hs R 0
  have hle : (toNiceCore toList R).maxBagCard ≤ R.width + 1 :=
    (maxBagCard_forgetChain_le _ _).trans hmax
  exact (NiceTreeDecomposition.width_le_iff _).2 hle

private theorem toNiceDecompositionCore_size_le (toList : Finset V → List V) (hs : ListSpec toList)
    {n : ℕ} (R : G.RootedTreeDecomposition n) :
    (toNiceDecompositionCore toList hs R).size ≤ (3 * R.width + 5) * (n + 1) := by
  have hsub := size_toNiceSubtreeCore_le toList hs R 0
  rw [subtreeNodes_zero] at hsub
  have hlen := (length_le_card_of_listSpec hs (R.bag 0)).trans (R.card_bag_le 0)
  change (toNiceCore toList R).size ≤ _
  rw [toNiceCore, size_forgetChain]
  omega

private theorem toNiceDecompositionCore_pruned_size_le (toList : Finset V → List V)
    (hs : ListSpec toList) [Fintype V] {n : ℕ} (R : G.RootedTreeDecomposition n) :
    (toNiceDecompositionCore toList hs R.prune.2).size ≤
      (3 * R.width + 5) * (Fintype.card V + 1) := by
  refine (toNiceDecompositionCore_size_le toList hs R.prune.2).trans ?_
  have hw := R.prune_width_le
  have hn := R.prune_nodes_le
  exact Nat.mul_le_mul (by omega) (by omega)

/-- Convert a rooted tree decomposition into a nice tree decomposition using sorted bag lists
(computable when `[LinearOrder V]`), without increasing width. -/
def toNiceTree [LinearOrder V] {n : ℕ} (R : G.RootedTreeDecomposition n) :
    G.NiceTreeDecomposition :=
  toNiceDecompositionCore (fun S => S.sort (· ≤ ·))
    ⟨fun S => S.sort_nodup _, fun _ _ => Finset.mem_sort _⟩ R

theorem toNiceTree_width_le [LinearOrder V] {n : ℕ} (R : G.RootedTreeDecomposition n) :
    R.toNiceTree.width ≤ R.width :=
  toNiceDecompositionCore_width_le _ _ R

theorem toNiceTree_size_le [LinearOrder V] {n : ℕ} (R : G.RootedTreeDecomposition n) :
    R.toNiceTree.size ≤ (3 * R.width + 5) * (n + 1) :=
  toNiceDecompositionCore_size_le _ _ R

/-- Prune and convert a rooted tree decomposition into a nice tree decomposition with at most
`(3 * R.width + 5) * (card V + 1)` nodes and width at most `R.width`. -/
def toNiceTreePruned [LinearOrder V] {n : ℕ} (R : G.RootedTreeDecomposition n) :
    G.NiceTreeDecomposition :=
  R.prune.2.toNiceTree

theorem toNiceTreePruned_width_le [LinearOrder V] {n : ℕ} (R : G.RootedTreeDecomposition n) :
    R.toNiceTreePruned.width ≤ R.width :=
  R.prune.2.toNiceTree_width_le.trans R.prune_width_le

theorem toNiceTreePruned_size_le [LinearOrder V] [Fintype V] {n : ℕ}
    (R : G.RootedTreeDecomposition n) :
    R.toNiceTreePruned.size ≤ (3 * R.width + 5) * (Fintype.card V + 1) :=
  toNiceDecompositionCore_pruned_size_le _
    ⟨fun S => S.sort_nodup _, fun _ _ => Finset.mem_sort _⟩ R

/-- Convert any rooted tree decomposition into a nice tree decomposition without requiring a
linear order on `V`. -/
noncomputable def toNice {n : ℕ} (R : G.RootedTreeDecomposition n) :
    G.NiceTreeDecomposition :=
  toNiceDecompositionCore Finset.toList
    ⟨fun S => S.nodup_toList, fun _ _ => Finset.mem_toList⟩ R

theorem toNice_width_le {n : ℕ} (R : G.RootedTreeDecomposition n) :
    R.toNice.width ≤ R.width :=
  toNiceDecompositionCore_width_le _ _ R

theorem toNice_size_le [Fintype V] {n : ℕ} (R : G.RootedTreeDecomposition n) :
    (R.prune.2.toNice).size ≤ (3 * R.width + 5) * (Fintype.card V + 1) :=
  toNiceDecompositionCore_pruned_size_le _
    ⟨fun S => S.nodup_toList, fun _ _ => Finset.mem_toList⟩ R

end RootedTreeDecomposition

namespace TreeDecomposition

variable {V : Type uV} {ι : Type uι} {G : SimpleGraph V} [DecidableEq V]

/-- Every finite tree decomposition has a nice tree decomposition of width at most `D.width` and
at most `(3 * D.width + 5) * (card V + 1)` nodes (when `V` is finite). -/
theorem exists_niceTreeDecomposition [Fintype ι] [Fintype V] (D : G.TreeDecomposition ι) :
    ∃ N : G.NiceTreeDecomposition,
      N.width ≤ D.width ∧ N.size ≤ (3 * D.width + 5) * (Fintype.card V + 1) := by
  obtain ⟨_, R, hR⟩ := D.exists_rooted_width_eq
  refine ⟨R.prune.2.toNice, ?_, ?_⟩
  · exact (R.prune.2.toNice_width_le).trans (R.prune_width_le.trans hR.le)
  · simpa [hR] using R.toNice_size_le

end TreeDecomposition

end SimpleGraph
