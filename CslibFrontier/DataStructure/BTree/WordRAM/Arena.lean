/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Copy
public import CslibFrontier.DataStructure.BTree.Height
public import CslibFrontier.DataStructure.BTree.Lookup
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Flat Word-RAM Arena Representation and Split/Insert Operations for Classic B-Trees

Pure memory-layout geometry, deterministic `BTree ℕ ℕ` decoding (`readTree`, `readNodeSet`), node
validity and key-order predicates (`ValidNode`, `SortedNode`), and index-level correctness of
proactive top-down node splitting (`memSplitRoot`, `memSplitChild`) and leaf/internal updates
(`memOverwriteVal`, `memInsertLeaf`) on a flat Word-RAM word array `mem : ℕ → ℕ`, following
[CLRS2009], Section 18.2.

## Arena layout at `base` and minimum degree `t ≥ 2`

* Header (`[base, base + 2)`):
  - `mem base`: root node index `root` (`0`-based when `mem (base + 1) > 0`).
  - `mem (base + 1)`: allocated node count `cnt` (`0` denotes the empty B-tree `.leaf`).
* Node `u` (`0 ≤ u < cnt`) occupies `nodeStride t = 6 * t` words at
  `nodeAddr base t u = base + 2 + u * (6 * t)`:
  - `+ 0`: `isLeaf` (`1` for leaf, `0` for internal node).
  - `+ 1`: `numKeys` (`m`, with `1 ≤ m ≤ 2 * t - 1`).
  - `+ 2 + i` (`0 ≤ i < 2 * t - 1`): `key[i]`.
  - `+ (2 * t + 1) + i` (`0 ≤ i < 2 * t - 1`): `val[i]`.
  - `+ 4 * t + j` (`0 ≤ j < 2 * t`): `child[j]` (`0`-based child node index when `isLeaf = 0`).

## Main definitions

* `BTree.WordRAM.nodeStride`, `BTree.WordRAM.nodeAddr`, `BTree.WordRAM.arenaWords`: arena address
  arithmetic.
* `BTree.WordRAM.leafFlag`, `BTree.WordRAM.numKeys`, `BTree.WordRAM.keyAt`,
  `BTree.WordRAM.valAt`, `BTree.WordRAM.childAt`: node field accessors on `mem : ℕ → ℕ`.
* `BTree.WordRAM.readTree`, `BTree.WordRAM.readNodeSet`: deterministic decoding of a `BTree ℕ ℕ`
  and its allocated node-index set from `(levelsBelow, base, t, mem, u)`.
* `BTree.WordRAM.ValidNode`, `BTree.WordRAM.SortedNode`: structural and strict key-order
  predicates on an allocated subtree.
* `BTree.WordRAM.slotCount`: within-node strict lower-key count computed by a counting loop.
* `BTree.WordRAM.shiftArrRight`: backward-shift memory transformer.
* `BTree.WordRAM.memInitSingle`, `BTree.WordRAM.memOverwriteVal`,
  `BTree.WordRAM.memInsertLeaf`, `BTree.WordRAM.memCopyUpper`, `BTree.WordRAM.memSplitRoot`,
  `BTree.WordRAM.memSplitChild`: pure memory transformers mirrored by the Word-RAM machine code.

## Main results

* `BTree.WordRAM.ValidNode.congr_mem`, `BTree.WordRAM.SortedNode.congr_mem`: disjoint-node memory
  framing for `ValidNode`, `SortedNode`, `readTree`, and `readNodeSet`.
* `BTree.WordRAM.SortedNode.isSortedAssoc`, `BTree.WordRAM.ValidNode.isWF`: any valid sorted node
  at `2 ≤ t` decodes to a well-formed `BTree.IsWF t` tree of height `l + 1`.
* `BTree.WordRAM.slotCount_spec`, `BTree.WordRAM.lookup_readTree_eq_some`,
  `BTree.WordRAM.lookup_readTree_leaf_none`, `BTree.WordRAM.lookup_readTree_succ_eq_child`:
  within-node search bounds and single-level reduction of `BTree.lookup`.
* `BTree.WordRAM.memSplitRoot_spec`, `BTree.WordRAM.memSplitChild_spec`: splitting a full
  (`2 * t - 1`-key) root or child preserves `ValidNode`, `SortedNode`, and exact `toList` while
  leaving `(t - 1)`-key halves.
* `BTree.WordRAM.memOverwriteVal_spec`, `BTree.WordRAM.memInsertLeaf_spec`,
  `BTree.WordRAM.childInsert_spec`: key overwrite, leaf shift-insertion, and recursive child
  insertion realize `Cslib.SortedAssoc.insert`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 18.2][CLRS2009]
-/

public section

namespace Cslib.DataStructure.BTree.WordRAM

open Cslib.DataStructure Cslib.WordRAM

/-! ## 1. Address geometry and field accessors -/

/-- Words per allocated B-tree node at minimum degree `t`. -/
@[expose] def nodeStride (t : ℕ) : ℕ := 6 * t

/-- Starting word address of `0`-based node `u` in an arena at `base` of minimum degree `t`. -/
@[expose] def nodeAddr (base t u : ℕ) : ℕ := base + 2 + u * nodeStride t

/-- Total word footprint of an arena with capacity `capNodes` at minimum degree `t`. -/
@[expose] def arenaWords (t capNodes : ℕ) : ℕ := 2 + capNodes * nodeStride t

theorem nodeAddr_lt_arena {base t u o capNodes : ℕ} (hu : u < capNodes) (ho : o < nodeStride t) :
    nodeAddr base t u + o < base + arenaWords t capNodes := by
  have hmul : (u + 1) * nodeStride t ≤ capNodes * nodeStride t :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [nodeAddr, arenaWords, Nat.add_mul, Nat.one_mul] at hmul ⊢
  omega

theorem base_lt_nodeAddr (base t u o : ℕ) : base + 1 < nodeAddr base t u + o := by
  simp only [nodeAddr]
  omega

theorem nodeAddr_sep (base t : ℕ) {u v : ℕ} (huv : u ≠ v) :
    nodeAddr base t u + nodeStride t ≤ nodeAddr base t v ∨
      nodeAddr base t v + nodeStride t ≤ nodeAddr base t u := by
  wlog hlt : u < v generalizing u v
  · exact (this huv.symm (by omega)).symm
  left
  have hmul : (u + 1) * nodeStride t ≤ v * nodeStride t := Nat.mul_le_mul_right _ hlt
  simp only [nodeAddr, Nat.add_mul, Nat.one_mul] at hmul ⊢
  omega

theorem nodeAddr_disjoint {base t u v o₁ o₂ : ℕ} (huv : u ≠ v)
    (ho₁ : o₁ < nodeStride t) (ho₂ : o₂ < nodeStride t) :
    nodeAddr base t u + o₁ ≠ nodeAddr base t v + o₂ := by
  have := nodeAddr_sep base t huv
  omega

/-- Leaf flag (`1` = leaf, `0` = internal) of node `u`. -/
@[expose] def leafFlag (base t : ℕ) (mem : ℕ → ℕ) (u : ℕ) : ℕ :=
  mem (nodeAddr base t u)

/-- Stored key count `m` of node `u`. -/
@[expose] def numKeys (base t : ℕ) (mem : ℕ → ℕ) (u : ℕ) : ℕ :=
  mem (nodeAddr base t u + 1)

/-- `i`-th stored key of node `u`. -/
@[expose] def keyAt (base t : ℕ) (mem : ℕ → ℕ) (u i : ℕ) : ℕ :=
  mem (nodeAddr base t u + 2 + i)

/-- `i`-th stored value of node `u`. -/
@[expose] def valAt (base t : ℕ) (mem : ℕ → ℕ) (u i : ℕ) : ℕ :=
  mem (nodeAddr base t u + (2 * t + 1) + i)

/-- `j`-th child node index of internal node `u`. -/
@[expose] def childAt (base t : ℕ) (mem : ℕ → ℕ) (u j : ℕ) : ℕ :=
  mem (nodeAddr base t u + 4 * t + j)

/-! ## 2. Deterministic tree & node-set decoding -/

/-- Deterministically decode a `BTree ℕ ℕ` of height `l + 1` rooted at node `u`. -/
def readTree : ℕ → ℕ → ℕ → (ℕ → ℕ) → ℕ → BTree ℕ ℕ
  | 0, base, t, mem, u =>
    let m := numKeys base t mem u
    .node .leaf (List.ofFn fun i : Fin m =>
      (keyAt base t mem u i.val, valAt base t mem u i.val, .leaf))
  | l + 1, base, t, mem, u =>
    let m := numKeys base t mem u
    let first := readTree l base t mem (childAt base t mem u 0)
    .node first (List.ofFn fun i : Fin m =>
      (keyAt base t mem u i.val, valAt base t mem u i.val,
        readTree l base t mem (childAt base t mem u (i.val + 1))))

/-- Set of allocated node indices visited when decoding `readTree l base t mem u`. -/
def readNodeSet : ℕ → ℕ → ℕ → (ℕ → ℕ) → ℕ → Finset ℕ
  | 0, _, _, _, u => {u}
  | l + 1, base, t, mem, u =>
    let m := numKeys base t mem u
    insert u ((Finset.univ : Finset (Fin (m + 1))).biUnion fun j =>
      readNodeSet l base t mem (childAt base t mem u j.val))

@[simp] theorem readNodeSet_zero (base t : ℕ) (mem : ℕ → ℕ) (u : ℕ) :
    readNodeSet 0 base t mem u = {u} := by
  simp [readNodeSet]

theorem self_mem_readNodeSet (l base t : ℕ) (mem : ℕ → ℕ) (u : ℕ) :
    u ∈ readNodeSet l base t mem u := by
  cases l <;> simp [readNodeSet]

theorem child_subset_readNodeSet (l base t : ℕ) (mem : ℕ → ℕ) (u j : ℕ)
    (hj : j < numKeys base t mem u + 1) :
    readNodeSet l base t mem (childAt base t mem u j) ⊆ readNodeSet (l + 1) base t mem u := by
  intro x hx
  simp only [readNodeSet, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact Or.inr ⟨⟨j, hj⟩, hx⟩

private theorem mem_readNodeSet_succ {l base t : ℕ} {mem : ℕ → ℕ} {u x : ℕ} :
    x ∈ readNodeSet (l + 1) base t mem u ↔
      x = u ∨ ∃ j < numKeys base t mem u + 1,
        x ∈ readNodeSet l base t mem (childAt base t mem u j) := by
  simp only [readNodeSet, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact or_congr Iff.rfl ⟨fun ⟨⟨j, hj⟩, hx⟩ => ⟨j, hj, hx⟩, fun ⟨j, hj, hx⟩ => ⟨⟨j, hj⟩, hx⟩⟩

theorem readTree_ne_leaf (l base t : ℕ) (mem : ℕ → ℕ) (u : ℕ) :
    readTree l base t mem u ≠ .leaf := by
  cases l <;> simp [readTree]

@[simp] theorem rootKeys_readTree (l base t : ℕ) (mem : ℕ → ℕ) (u : ℕ) :
    (readTree l base t mem u).rootKeys = numKeys base t mem u := by
  cases l <;> simp [readTree]

theorem mem_children_readTree_zero_iff (base t : ℕ) (mem : ℕ → ℕ) (u : ℕ) (c : BTree ℕ ℕ) :
    c ∈ (readTree 0 base t mem u).children ↔ c = .leaf := by
  simp only [readTree, BTree.children_node, List.mem_cons, List.mem_map, List.mem_ofFn]
  constructor
  · rintro (rfl | ⟨_, ⟨_, rfl⟩, rfl⟩) <;> rfl
  · rintro rfl; exact Or.inl rfl

theorem mem_children_readTree_succ_iff (l base t : ℕ) (mem : ℕ → ℕ) (u : ℕ) (c : BTree ℕ ℕ) :
    c ∈ (readTree (l + 1) base t mem u).children ↔
      ∃ j < numKeys base t mem u + 1, c = readTree l base t mem (childAt base t mem u j) := by
  simp only [readTree, BTree.children_node, List.mem_cons, List.mem_map, List.mem_ofFn]
  constructor
  · rintro (rfl | ⟨_, ⟨i, rfl⟩, rfl⟩)
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨i.val + 1, by omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    cases j with
    | zero => exact Or.inl rfl
    | succ i => exact Or.inr ⟨_, ⟨⟨i, by omega⟩, rfl⟩, rfl⟩

/-! ## 3. Structural validity (`ValidNode`) and memory framing -/

/-- Structural validity of a subtree of height `l + 1` rooted at node `u`: valid `leafFlag`,
`1 ≤ numKeys ≤ 2 * t - 1`, `t - 1 ≤ numKeys` on all proper descendants, and pairwise disjoint
node sets. -/
def ValidNode : ℕ → ℕ → ℕ → (ℕ → ℕ) → ℕ → Prop
  | 0, base, t, mem, u =>
    leafFlag base t mem u = 1 ∧ 1 ≤ numKeys base t mem u ∧ numKeys base t mem u ≤ 2 * t - 1
  | l + 1, base, t, mem, u =>
    let m := numKeys base t mem u
    leafFlag base t mem u = 0 ∧ 1 ≤ m ∧ m ≤ 2 * t - 1 ∧
      (∀ j < m + 1,
        let cid := childAt base t mem u j
        ValidNode l base t mem cid ∧
          t - 1 ≤ numKeys base t mem cid ∧
          u ∉ readNodeSet l base t mem cid) ∧
      (∀ j₁ j₂, j₁ < m + 1 → j₂ < m + 1 → j₁ ≠ j₂ →
        Disjoint (readNodeSet l base t mem (childAt base t mem u j₁))
          (readNodeSet l base t mem (childAt base t mem u j₂)))

theorem ValidNode.leafFlag_eq {l base t : ℕ} {mem : ℕ → ℕ} {u : ℕ}
    (hv : ValidNode l base t mem u) :
    leafFlag base t mem u = if l = 0 then 1 else 0 := by
  cases l <;> exact hv.1

theorem ValidNode.numKeys_pos {l base t : ℕ} {mem : ℕ → ℕ} {u : ℕ}
    (hv : ValidNode l base t mem u) : 1 ≤ numKeys base t mem u := by
  cases l <;> exact hv.2.1

theorem ValidNode.numKeys_le {l base t : ℕ} {mem : ℕ → ℕ} {u : ℕ}
    (hv : ValidNode l base t mem u) : numKeys base t mem u ≤ 2 * t - 1 := by
  cases l with
  | zero => exact hv.2.2
  | succ l => exact hv.2.2.1

theorem ValidNode.child_valid {l base t : ℕ} {mem : ℕ → ℕ} {u j : ℕ}
    (hv : ValidNode (l + 1) base t mem u) (hj : j < numKeys base t mem u + 1) :
    ValidNode l base t mem (childAt base t mem u j) :=
  (hv.2.2.2.1 j hj).1

theorem ValidNode.child_numKeys_ge {l base t : ℕ} {mem : ℕ → ℕ} {u j : ℕ}
    (hv : ValidNode (l + 1) base t mem u) (hj : j < numKeys base t mem u + 1) :
    t - 1 ≤ numKeys base t mem (childAt base t mem u j) :=
  (hv.2.2.2.1 j hj).2.1

theorem ValidNode.not_mem_child_readNodeSet {l base t : ℕ} {mem : ℕ → ℕ} {u j : ℕ}
    (hv : ValidNode (l + 1) base t mem u) (hj : j < numKeys base t mem u + 1) :
    u ∉ readNodeSet l base t mem (childAt base t mem u j) :=
  (hv.2.2.2.1 j hj).2.2

/-- Agreement on the cells of node `u` gives agreement on its decoded fields. -/
private theorem fields_eq_of_cells {base t u : ℕ} {mem mem' : ℕ → ℕ} (ht : 1 ≤ t)
    (h : ∀ o < nodeStride t, mem' (nodeAddr base t u + o) = mem (nodeAddr base t u + o)) :
    leafFlag base t mem' u = leafFlag base t mem u ∧ numKeys base t mem' u = numKeys base t mem u ∧
      ∀ i < 2 * t, keyAt base t mem' u i = keyAt base t mem u i ∧
        valAt base t mem' u i = valAt base t mem u i ∧
          childAt base t mem' u i = childAt base t mem u i := by
  have hst : nodeStride t = 6 * t := rfl
  refine ⟨h 0 (by omega), h 1 (by omega), fun i hi => ⟨?_, ?_, ?_⟩⟩ <;>
    simp only [keyAt, valAt, childAt, Nat.add_assoc] <;> exact h _ (by omega)

/-- Rebuild an internal node `w` of `mem'` whose `n` children are the window at offset `off` of
the children of `c` in `mem`, when each child in the window is unchanged and avoids `w`. -/
private theorem window_valid {l base t : ℕ} {mem mem' : ℕ → ℕ} {c w off n : ℕ}
    (hv : ValidNode (l + 1) base t mem c) (hlf : leafFlag base t mem' w = 0)
    (hnk : numKeys base t mem' w = n) (hn : 1 ≤ n) (hn₂ : n ≤ 2 * t - 1)
    (hwin : n + off ≤ numKeys base t mem c)
    (hcid : ∀ j < n + 1, childAt base t mem' w j = childAt base t mem c (j + off))
    (hvc : ∀ j < n + 1, ValidNode l base t mem' (childAt base t mem c (j + off)))
    (hset : ∀ j < n + 1, readNodeSet l base t mem' (childAt base t mem c (j + off)) =
      readNodeSet l base t mem (childAt base t mem c (j + off)))
    (hnkc : ∀ j < n + 1, numKeys base t mem' (childAt base t mem c (j + off)) =
      numKeys base t mem (childAt base t mem c (j + off)))
    (hw : ∀ j < n + 1, w ∉ readNodeSet l base t mem (childAt base t mem c (j + off))) :
    ValidNode (l + 1) base t mem' w ∧
      ∀ x, x ∈ readNodeSet (l + 1) base t mem' w ↔
        x = w ∨ ∃ j < n + 1, x ∈ readNodeSet l base t mem (childAt base t mem c (j + off)) := by
  refine ⟨?_, fun x => ?_⟩
  · simp only [ValidNode, hnk]
    refine ⟨hlf, hn, hn₂, fun j hj => ?_, fun j₁ j₂ hj₁ hj₂ hne => ?_⟩
    · rw [hcid j hj, hset j hj, hnkc j hj]
      exact ⟨hvc j hj, hv.child_numKeys_ge (by omega), hw j hj⟩
    · rw [hcid j₁ hj₁, hcid j₂ hj₂, hset j₁ hj₁, hset j₂ hj₂]
      exact hv.2.2.2.2 _ _ (by omega) (by omega) (by omega)
  · rw [mem_readNodeSet_succ, hnk]
    refine or_congr Iff.rfl (exists_congr fun j => and_congr_right fun hj => ?_)
    rw [hcid j hj, hset j hj]

/-- Every valid node decodes to a balanced `BTree` of exact height `l + 1`. -/
theorem ValidNode.balanced_and_height {l base t : ℕ} {mem : ℕ → ℕ} {u : ℕ}
    (hv : ValidNode l base t mem u) :
    BTree.Balanced (readTree l base t mem u) ∧ (readTree l base t mem u).height = l + 1 := by
  induction l generalizing u with
  | zero =>
    simp only [readTree]
    refine BTree.balanced_node_of_forall .leaf ?_
    simp only [List.forall_mem_ofFn_iff]
    intro _
    exact ⟨.leaf, trivial⟩
  | succ l ih =>
    obtain ⟨_, _, _, hch, _⟩ := hv
    obtain ⟨hb₀, hh₀⟩ := ih (hch 0 (by omega)).1
    have hboth := BTree.balanced_node_of_forall
      (first := readTree l base t mem (childAt base t mem u 0))
      (rest := List.ofFn fun i : Fin (numKeys base t mem u) =>
        (keyAt base t mem u i.val, valAt base t mem u i.val,
          readTree l base t mem (childAt base t mem u (i.val + 1))))
      hb₀ (by
        simp only [List.forall_mem_ofFn_iff]
        intro ⟨i, hi⟩
        obtain ⟨hbi, hhi⟩ := ih (hch (i + 1) (by omega)).1
        exact ⟨hbi, hhi.trans hh₀.symm⟩)
    exact ⟨hboth.1, hboth.2.trans (by omega)⟩

theorem ValidNode.occupied_of_le {l base t : ℕ} {mem : ℕ → ℕ} {u : ℕ}
    (hv : ValidNode l base t mem u) (hle : t - 1 ≤ numKeys base t mem u) :
    BTree.Occupied t (readTree l base t mem u) := by
  induction l generalizing u with
  | zero =>
    refine .node ?_ ?_ .leaf ?_
    · simp only [List.length_ofFn]; exact hle
    · simp only [List.length_ofFn]; exact hv.2.2
    · simp only [List.forall_mem_ofFn_iff]
      intro _; exact .leaf
  | succ l ih =>
    obtain ⟨_, _, hm₂, hch, _⟩ := hv
    refine .node ?_ ?_ (ih (hch 0 (by omega)).1 (hch 0 (by omega)).2.1) ?_
    · simp only [List.length_ofFn]; exact hle
    · simp only [List.length_ofFn]; exact hm₂
    · simp only [List.forall_mem_ofFn_iff]
      intro ⟨i, hi⟩
      exact ih (hch (i + 1) (by omega)).1 (hch (i + 1) (by omega)).2.1

theorem ValidNode.occupied_children {l base t : ℕ} {mem : ℕ → ℕ} {u : ℕ}
    (hv : ValidNode l base t mem u) :
    ∀ c ∈ (readTree l base t mem u).children, BTree.Occupied t c := by
  cases l with
  | zero =>
    intro c hc
    rw [mem_children_readTree_zero_iff] at hc
    subst hc
    exact .leaf
  | succ l =>
    intro c hc
    rw [mem_children_readTree_succ_iff] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    exact (hv.2.2.2.1 j hj).1.occupied_of_le (hv.2.2.2.1 j hj).2.1

/-! ## 4. Membership in `toList` and strict key-order predicate (`SortedNode`) -/

private theorem mem_toListRest_ofFn {m : ℕ} (f : Fin m → BTree.Triple ℕ ℕ) (p : ℕ × ℕ) :
    p ∈ BTree.toListRest (List.ofFn f) ↔
      ∃ i : Fin m, p = ((f i).1, (f i).val) ∨ p ∈ (f i).child.toList := by
  simp only [BTree.toListRest_eq_flatMap, List.mem_flatMap, List.mem_ofFn, List.mem_cons]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, hp⟩
    exact ⟨i, hp⟩
  · rintro ⟨i, hp⟩
    exact ⟨f i, ⟨i, rfl⟩, hp⟩

theorem toList_readTree_zero (base t : ℕ) (mem : ℕ → ℕ) (u : ℕ) :
    (readTree 0 base t mem u).toList =
      List.ofFn fun i : Fin (numKeys base t mem u) =>
        (keyAt base t mem u i.val, valAt base t mem u i.val) := by
  simpa only [readTree, BTree.toList_node, BTree.toList_leaf, List.nil_append, List.map_ofFn,
    Function.comp_def] using BTree.toListRest_map_leaf
      (List.ofFn fun i : Fin (numKeys base t mem u) =>
        (keyAt base t mem u i.val, valAt base t mem u i.val))

theorem mem_toList_readTree_zero (base t : ℕ) (mem : ℕ → ℕ) (u : ℕ) (p : ℕ × ℕ) :
    p ∈ (readTree 0 base t mem u).toList ↔
      ∃ i < numKeys base t mem u, p = (keyAt base t mem u i, valAt base t mem u i) := by
  rw [toList_readTree_zero, List.mem_ofFn]
  exact ⟨fun ⟨⟨i, hi⟩, hp⟩ => ⟨i, hi, hp.symm⟩, fun ⟨i, hi, hp⟩ => ⟨⟨i, hi⟩, hp.symm⟩⟩

theorem mem_toList_readTree_succ (l base t : ℕ) (mem : ℕ → ℕ) (u : ℕ) (p : ℕ × ℕ) :
    p ∈ (readTree (l + 1) base t mem u).toList ↔
      (∃ i < numKeys base t mem u, p = (keyAt base t mem u i, valAt base t mem u i)) ∨
        ∃ j < numKeys base t mem u + 1,
          p ∈ (readTree l base t mem (childAt base t mem u j)).toList := by
  simp only [readTree, BTree.toList_node, List.mem_append, mem_toListRest_ofFn,
    BTree.Triple.val_mk, BTree.Triple.child_mk]
  constructor
  · rintro (hp0 | ⟨⟨i, hi⟩, rfl | hpi⟩)
    · exact Or.inr ⟨0, by omega, hp0⟩
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨i + 1, by omega, hpi⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩)
    · exact Or.inr ⟨⟨i, hi⟩, Or.inl rfl⟩
    · cases j with
      | zero => exact Or.inl hpj
      | succ i => exact Or.inr ⟨⟨i, by omega⟩, Or.inr hpj⟩

/-- Index-level strict key-order predicate for a subtree of height `l + 1` at node `u`. -/
def SortedNode : ℕ → ℕ → ℕ → (ℕ → ℕ) → ℕ → Prop
  | 0, base, t, mem, u =>
    ∀ i₁ i₂, i₁ < i₂ → i₂ < numKeys base t mem u → keyAt base t mem u i₁ < keyAt base t mem u i₂
  | l + 1, base, t, mem, u =>
    let m := numKeys base t mem u
    (∀ i₁ i₂, i₁ < i₂ → i₂ < m → keyAt base t mem u i₁ < keyAt base t mem u i₂) ∧
      (∀ j < m + 1, SortedNode l base t mem (childAt base t mem u j)) ∧
      (∀ i < m, ∀ p ∈ (readTree l base t mem (childAt base t mem u i)).toList,
        p.1 < keyAt base t mem u i) ∧
      (∀ i < m, ∀ p ∈ (readTree l base t mem (childAt base t mem u (i + 1))).toList,
        keyAt base t mem u i < p.1)

theorem SortedNode.keys_strict {l base t : ℕ} {mem : ℕ → ℕ} {u i₁ i₂ : ℕ}
    (hs : SortedNode l base t mem u) (h12 : i₁ < i₂) (h2 : i₂ < numKeys base t mem u) :
    keyAt base t mem u i₁ < keyAt base t mem u i₂ := by
  cases l with
  | zero => exact hs i₁ i₂ h12 h2
  | succ _ => exact hs.1 i₁ i₂ h12 h2

theorem SortedNode.child_sorted {l base t : ℕ} {mem : ℕ → ℕ} {u j : ℕ}
    (hs : SortedNode (l + 1) base t mem u) (hj : j < numKeys base t mem u + 1) :
    SortedNode l base t mem (childAt base t mem u j) :=
  hs.2.1 j hj

/-- Order counterpart of `window_valid`: a node whose keys and children are a window of those of
a sorted node `c`, with unchanged sorted children, is sorted. -/
private theorem window_sorted {l base t : ℕ} {mem mem' : ℕ → ℕ} {c w off n : ℕ}
    (hs : SortedNode (l + 1) base t mem c) (hnk : numKeys base t mem' w = n)
    (hwin : n + off ≤ numKeys base t mem c)
    (hkey : ∀ i < n, keyAt base t mem' w i = keyAt base t mem c (i + off))
    (hcid : ∀ j < n + 1, childAt base t mem' w j = childAt base t mem c (j + off))
    (hsc : ∀ j < n + 1, SortedNode l base t mem' (childAt base t mem c (j + off)))
    (htr : ∀ j < n + 1, readTree l base t mem' (childAt base t mem c (j + off)) =
      readTree l base t mem (childAt base t mem c (j + off))) :
    SortedNode (l + 1) base t mem' w := by
  obtain ⟨hkeys, -, hleft, hright⟩ := hs
  simp only [SortedNode, hnk]
  refine ⟨fun i₁ i₂ h12 h2 => ?_, fun j hj => ?_, fun i hi p hp => ?_, fun i hi p hp => ?_⟩
  · rw [hkey i₁ (by omega), hkey i₂ h2]; exact hkeys _ _ (by omega) (by omega)
  · rw [hcid j hj]; exact hsc j hj
  · rw [hcid i (by omega), htr i (by omega)] at hp
    rw [hkey i hi]; exact hleft _ (by omega) p hp
  · rw [hcid (i + 1) (by omega), htr (i + 1) (by omega), Nat.add_right_comm i 1 off] at hp
    rw [hkey i hi]; exact hright _ (by omega) p hp

/-- Agreement on the cells of a subtree transports all of its decoding facts in one induction. -/
private theorem frame_subtree {l base t : ℕ} {mem mem' : ℕ → ℕ} {u : ℕ}
    (ht : 1 ≤ t) (hv : ValidNode l base t mem u)
    (hmem : ∀ v ∈ readNodeSet l base t mem u, ∀ o < nodeStride t,
      mem' (nodeAddr base t v + o) = mem (nodeAddr base t v + o)) :
    ValidNode l base t mem' u ∧
      readTree l base t mem' u = readTree l base t mem u ∧
      readNodeSet l base t mem' u = readNodeSet l base t mem u ∧
      (SortedNode l base t mem u → SortedNode l base t mem' u) ∧
      numKeys base t mem' u = numKeys base t mem u := by
  induction l generalizing u <;>
    obtain ⟨hflag, hcount, hfields⟩ := fields_eq_of_cells ht (hmem u (self_mem_readNodeSet ..))
  all_goals
    have hmax := hv.numKeys_le
    have hroom : numKeys base t mem u + 1 ≤ 2 * t := by lia
  case zero =>
    refine ⟨⟨hflag.trans hv.1, hcount ▸ hv.2.1, hcount ▸ hv.2.2⟩, ?_, rfl, ?_, hcount⟩
    · simp only [readTree]
      congr 1
      rw [List.ofFn_congr hcount, List.ofFn_inj]
      funext ⟨i, hi⟩
      obtain ⟨key, value, -⟩ := hfields i (hi.trans (Nat.lt_of_succ_le hroom))
      simp only [Fin.val_cast, key, value]
    · intro hs i j hij hj
      rw [hcount] at hj
      have hj' := hj.trans (Nat.lt_of_succ_le hroom)
      rw [(hfields i (hij.trans hj')).1, (hfields j hj').1]
      exact hs i j hij hj
  case succ l ih =>
    have hchild j (hj : j < numKeys base t mem u + 1) :
        childAt base t mem' u j = childAt base t mem u j := (hfields j (hj.trans_le hroom)).2.2
    have hframe j (hj : j < numKeys base t mem u + 1) :=
      ih (hv.child_valid hj)
        (fun v hv' => hmem v (child_subset_readNodeSet l base t mem u j hj hv'))
    obtain ⟨hv', hset⟩ := window_valid (off := 0) hv (hflag.trans hv.1) hcount hv.numKeys_pos
      hmax le_rfl hchild (fun j hj => (hframe j hj).1)
      (fun j hj => (hframe j hj).2.2.1) (fun j hj => (hframe j hj).2.2.2.2)
      (fun j hj => hv.not_mem_child_readNodeSet hj)
    refine ⟨hv', ?_, Finset.ext fun x => (hset x).trans mem_readNodeSet_succ.symm, ?_, hcount⟩
    · simp only [readTree]
      rw [hchild 0 (Nat.zero_lt_succ _), (hframe 0 (Nat.zero_lt_succ _)).2.1]
      congr 1
      rw [List.ofFn_congr hcount, List.ofFn_inj]
      funext ⟨i, hi⟩
      obtain ⟨key, value, -⟩ := hfields i (hi.trans (Nat.lt_of_succ_le hroom))
      have hi' : i + 1 < numKeys base t mem u + 1 := Nat.succ_lt_succ hi
      simp only [Fin.val_cast, key, value, hchild _ hi', (hframe _ hi').2.1]
    · intro hs
      exact window_sorted (off := 0) hs hcount le_rfl
        (fun i hi => (hfields i (hi.trans (Nat.lt_of_succ_le hroom))).1)
        hchild (fun j hj => (hframe j hj).2.2.2.1 (hs.child_sorted hj))
        (fun j hj => (hframe j hj).2.1)

/-- Disjoint-node framing: if `mem'` agrees with `mem` on every node in
`readNodeSet l base t mem u`, then `ValidNode`, `readTree`, and `readNodeSet` are preserved. -/
theorem ValidNode.congr_mem {l base t : ℕ} {mem mem' : ℕ → ℕ} {u : ℕ}
    (ht : 1 ≤ t) (hv : ValidNode l base t mem u)
    (hmem : ∀ v ∈ readNodeSet l base t mem u, ∀ o < nodeStride t,
      mem' (nodeAddr base t v + o) = mem (nodeAddr base t v + o)) :
    ValidNode l base t mem' u ∧
      readTree l base t mem' u = readTree l base t mem u ∧
      readNodeSet l base t mem' u = readNodeSet l base t mem u := by
  obtain ⟨valid, tree, nodes, -, -⟩ := frame_subtree ht hv hmem
  exact ⟨valid, tree, nodes⟩

theorem SortedNode.congr_mem {l base t : ℕ} {mem mem' : ℕ → ℕ} {u : ℕ}
    (ht : 1 ≤ t) (hv : ValidNode l base t mem u) (hs : SortedNode l base t mem u)
    (hmem : ∀ v ∈ readNodeSet l base t mem u, ∀ o < nodeStride t,
      mem' (nodeAddr base t v + o) = mem (nodeAddr base t v + o)) :
    SortedNode l base t mem' u :=
  (frame_subtree ht hv hmem).2.2.2.1 hs

/-- Framing for a whole subtree: if `mem'` agrees with `mem` on every node of `c`'s subtree, then
validity, decoding, node set, order and key count of `c` are preserved. -/
private theorem congr_all {l base t : ℕ} {mem mem' : ℕ → ℕ} {c : ℕ} (ht : 1 ≤ t)
    (hv : ValidNode l base t mem c) (hs : SortedNode l base t mem c)
    (hmem : ∀ v ∈ readNodeSet l base t mem c, ∀ o < nodeStride t,
      mem' (nodeAddr base t v + o) = mem (nodeAddr base t v + o)) :
    ValidNode l base t mem' c ∧ readTree l base t mem' c = readTree l base t mem c ∧
      readNodeSet l base t mem' c = readNodeSet l base t mem c ∧ SortedNode l base t mem' c ∧
      numKeys base t mem' c = numKeys base t mem c := by
  obtain ⟨valid, tree, nodes, sorted, count⟩ := frame_subtree ht hv hmem
  exact ⟨valid, tree, nodes, sorted hs, count⟩

theorem SortedNode.child_lt_key {l base t : ℕ} {mem : ℕ → ℕ} {u j i : ℕ}
    (hs : SortedNode (l + 1) base t mem u) (hji : j ≤ i) (hi : i < numKeys base t mem u)
    {p : ℕ × ℕ} (hp : p ∈ (readTree l base t mem (childAt base t mem u j)).toList) :
    p.1 < keyAt base t mem u i := by
  obtain ⟨hkeys, _, hleft, _⟩ := hs
  have h1 := hleft j (by omega) p hp
  rcases eq_or_lt_of_le hji with rfl | hlt
  · exact h1
  · exact h1.trans (hkeys j i hlt hi)

theorem SortedNode.key_lt_child {l base t : ℕ} {mem : ℕ → ℕ} {u i j : ℕ}
    (hs : SortedNode (l + 1) base t mem u) (_hi : i < numKeys base t mem u)
    (hij : i + 1 ≤ j) (hj : j < numKeys base t mem u + 1)
    {p : ℕ × ℕ} (hp : p ∈ (readTree l base t mem (childAt base t mem u j)).toList) :
    keyAt base t mem u i < p.1 := by
  obtain ⟨hkeys, _, _, hright⟩ := hs
  have h1 := hright (j - 1) (by omega) p (by
    have heq : j - 1 + 1 = j := by omega
    rwa [heq])
  rcases eq_or_lt_of_le hij with h_eq | hlt
  · have heq : j - 1 = i := by omega
    rwa [heq] at h1
  · exact (hkeys i (j - 1) (by omega) (by omega)).trans h1

private def toListUpTo (l base t : ℕ) (mem : ℕ → ℕ) (u : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => (readTree l base t mem (childAt base t mem u 0)).toList
  | n + 1 =>
    toListUpTo l base t mem u n ++
      (keyAt base t mem u n, valAt base t mem u n) ::
        (readTree l base t mem (childAt base t mem u (n + 1))).toList

private theorem toListRest_ofFn_succ {n : ℕ} (f : ℕ → BTree.Triple ℕ ℕ) :
    BTree.toListRest (List.ofFn fun i : Fin (n + 1) => f i.val) =
      BTree.toListRest (List.ofFn fun i : Fin n => f i.val) ++
        ((f n).1, (f n).val) :: (f n).child.toList := by
  rw [List.ofFn_succ_last, BTree.toListRest_append]
  simp only [Fin.val_last, Fin.val_castSucc]
  obtain ⟨k, v, c⟩ := f n
  simp only [BTree.toListRest, List.append_nil]

private theorem toList_readTree_succ_eq_upTo (l base t : ℕ) (mem : ℕ → ℕ) (u : ℕ) :
    (readTree (l + 1) base t mem u).toList =
      toListUpTo l base t mem u (numKeys base t mem u) := by
  simp only [readTree, BTree.toList_node]
  generalize numKeys base t mem u = n
  induction n with
  | zero => simp [toListUpTo]
  | succ n ih =>
    rw [toListRest_ofFn_succ
      (fun idx => (keyAt base t mem u idx, valAt base t mem u idx,
        readTree l base t mem (childAt base t mem u (idx + 1)))),
      ← List.append_assoc, ih, toListUpTo]

/-- `SortedNode` implies `List.IsSortedAssoc` on `(readTree l base t mem u).toList`. -/
theorem SortedNode.isSortedAssoc {l base t : ℕ} {mem : ℕ → ℕ} {u : ℕ}
    (hs : SortedNode l base t mem u) :
    (readTree l base t mem u).toList.IsSortedAssoc := by
  induction l generalizing u with
  | zero =>
    rw [toList_readTree_zero, List.isSortedAssoc_iff_pairwise, List.map_ofFn,
      List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_ofFn] at hi hj
    simp only [List.getElem_ofFn, Function.comp_apply]
    exact hs i j hij hj
  | succ l ih =>
    obtain ⟨hkeys, hcs, hleft, hright⟩ := hs
    rw [toList_readTree_succ_eq_upTo]
    set m := numKeys base t mem u
    suffices haux : ∀ n ≤ m,
        (toListUpTo l base t mem u n).IsSortedAssoc ∧
          (n < m → ∀ p ∈ toListUpTo l base t mem u n, p.1 < keyAt base t mem u n) from
      (haux m le_rfl).1
    intro n hn
    induction n with
    | zero =>
      exact ⟨ih (hcs 0 (by omega)), fun h0 p hp => hleft 0 h0 p hp⟩
    | succ n ihn =>
      obtain ⟨hsn, hlt_n⟩ := ihn (by omega)
      have hsc1 : (readTree l base t mem (childAt base t mem u (n + 1))).toList.IsSortedAssoc :=
        ih (hcs (n + 1) (by omega))
      have hsort : (toListUpTo l base t mem u (n + 1)).IsSortedAssoc := by
        rw [toListUpTo, List.isSortedAssoc_append_cons_iff]
        exact ⟨hsn, hsc1, hlt_n (by omega), hright n (by omega)⟩
      refine ⟨hsort, fun hn1 p hp => ?_⟩
      rw [toListUpTo, List.mem_append, List.mem_cons] at hp
      rcases hp with hp_pre | rfl | hp_c
      · exact (hlt_n (by omega) p hp_pre).trans (hkeys n (n + 1) (by omega) hn1)
      · exact hkeys n (n + 1) (by omega) hn1
      · exact hleft (n + 1) hn1 p hp_c

/-- A valid sorted node at `2 ≤ t` decodes to a well-formed `BTree.IsWF t` tree. -/
theorem ValidNode.isWF {l base t : ℕ} {mem : ℕ → ℕ} {u : ℕ}
    (ht : 2 ≤ t) (hv : ValidNode l base t mem u) (hs : SortedNode l base t mem u) :
    BTree.IsWF t (readTree l base t mem u) where
  two_le := ht
  rootKeys_le := by rw [rootKeys_readTree]; exact hv.numKeys_le
  rootKeys_pos _ := by rw [rootKeys_readTree]; exact hv.numKeys_pos
  occupied_of_mem_children := hv.occupied_children
  balanced := hv.balanced_and_height.1
  sorted := hs.isSortedAssoc

/-! ## 5. Within-node search (`slotCount`) and single-level lookup reduction -/

/-- Count how many keys in `[0, j)` of node `u` are strictly less than `k`. -/
@[expose] def slotCount (base t : ℕ) (mem : ℕ → ℕ) (u k : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => slotCount base t mem u k j + if keyAt base t mem u j < k then 1 else 0

theorem slotCount_spec {base t : ℕ} {mem : ℕ → ℕ} {u k m : ℕ}
    (hkeys : ∀ i₁ i₂, i₁ < i₂ → i₂ < m → keyAt base t mem u i₁ < keyAt base t mem u i₂)
    (j : ℕ) (hj : j ≤ m) :
    let s := slotCount base t mem u k j
    s ≤ j ∧
      (∀ i < s, keyAt base t mem u i < k) ∧
      (∀ i, s ≤ i → i < j → k ≤ keyAt base t mem u i) := by
  induction j with
  | zero =>
    refine ⟨le_rfl, ?_, ?_⟩
    · intro i hi; simp [slotCount] at hi
    · intro i _ hi; omega
  | succ j ih =>
    obtain ⟨hs_le, hlt, hge⟩ := ih (by omega)
    set sj := slotCount base t mem u k j
    dsimp only
    rw [slotCount]
    split_ifs with hjk
    · have hsj_eq : slotCount base t mem u k j = j := by
        by_contra hne
        have hlt_j : sj < j := by omega
        have hge_sj := hge sj le_rfl hlt_j
        have hinc := hkeys sj j hlt_j hj
        omega
      refine ⟨by omega, ?_, ?_⟩
      · intro i hi
        rw [hsj_eq] at hi
        rcases eq_or_lt_of_le (Nat.le_of_lt_succ hi) with rfl | hi_lt
        · exact hjk
        · exact (hkeys i j hi_lt hj).trans hjk
      · intro i hi₁ hi₂
        omega
    · refine ⟨by omega, hlt, ?_⟩
      intro i hi₁ hi₂
      rw [Nat.add_zero] at hi₁
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hi₂) with rfl | hi_lt
      · omega
      · exact hge i hi₁ hi_lt

/-- When `slot < numKeys` and `keyAt u slot = k`, `BTree.lookup k (readTree ...)` returns
`some (valAt u slot)`. -/
theorem lookup_readTree_eq_some {l base t : ℕ} {mem : ℕ → ℕ} {u slot k : ℕ}
    (hs : SortedNode l base t mem u)
    (hslot : slot < numKeys base t mem u) (heq : keyAt base t mem u slot = k) :
    BTree.lookup k (readTree l base t mem u) = some (valAt base t mem u slot) := by
  have hsort := hs.isSortedAssoc
  rw [BTree.lookup_eq_of_isSortedAssoc hsort, hsort.lookup_eq_some_iff]
  subst heq
  cases l with
  | zero => exact (mem_toList_readTree_zero ..).mpr ⟨slot, hslot, rfl⟩
  | succ l => exact (mem_toList_readTree_succ ..).mpr (Or.inl ⟨slot, hslot, rfl⟩)

/-- On a sorted leaf node `u` (`l = 0`), if `keyAt u i ≠ k` for all `i < m`, lookup returns
`none`. -/
theorem lookup_readTree_leaf_none {base t : ℕ} {mem : ℕ → ℕ} {u k : ℕ}
    (hs : SortedNode 0 base t mem u)
    (hne : ∀ i < numKeys base t mem u, keyAt base t mem u i ≠ k) :
    BTree.lookup k (readTree 0 base t mem u) = none := by
  rw [BTree.lookup_eq_of_isSortedAssoc hs.isSortedAssoc]
  apply List.lookup_eq_none_of_forall_ne
  intro p hp
  rw [mem_toList_readTree_zero] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact hne i hi

/-- On a sorted internal node `u` (`l + 1`), when `slot ≤ m` satisfies `keyAt u i < k` for
`i < slot` and `k < keyAt u i` for `slot ≤ i < m`, `BTree.lookup` reduces to child `slot`. -/
theorem lookup_readTree_succ_eq_child {l base t : ℕ} {mem : ℕ → ℕ} {u slot k : ℕ}
    (hs : SortedNode (l + 1) base t mem u)
    (hslot : slot ≤ numKeys base t mem u)
    (hlt : ∀ i < slot, keyAt base t mem u i < k)
    (hgt : ∀ i, slot ≤ i → i < numKeys base t mem u → k < keyAt base t mem u i) :
    BTree.lookup k (readTree (l + 1) base t mem u) =
      BTree.lookup k (readTree l base t mem (childAt base t mem u slot)) := by
  have hsort_u := hs.isSortedAssoc
  have hsort_c := (hs.2.1 slot (by omega)).isSortedAssoc
  rw [BTree.lookup_eq_of_isSortedAssoc hsort_u, BTree.lookup_eq_of_isSortedAssoc hsort_c]
  cases hres : List.lookup k (readTree l base t mem (childAt base t mem u slot)).toList with
  | some v =>
    rw [hsort_u.lookup_eq_some_iff, mem_toList_readTree_succ]
    exact Or.inr ⟨slot, by omega, hsort_c.lookup_eq_some_iff.mp hres⟩
  | none =>
    apply List.lookup_eq_none_of_forall_ne
    intro p hp
    rw [mem_toList_readTree_succ] at hp
    rcases hp with ⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩
    · rcases lt_or_ge i slot with hi_lt | hi_ge
      · exact (hlt i hi_lt).ne
      · exact (hgt i hi_ge hi).ne'
    · rcases lt_trichotomy j slot with hj_lt | rfl | hj_gt
      · exact ((hs.child_lt_key (by omega) (by omega) hpj).trans (hlt j hj_lt)).ne
      · intro hpk
        subst hpk
        have hsome := hsort_c.lookup_eq_some_iff.mpr hpj
        rw [hres] at hsome
        cases hsome
      · have hslot_lt : slot < numKeys base t mem u := by omega
        exact (lt_trans (hgt slot le_rfl hslot_lt)
          (hs.key_lt_child hslot_lt (by omega) hj hpj)).ne'

/-! ## 6. Generic forward-copy and backward-shift array helpers -/

/-- Shift `count` words `[upper - count .. upper - 1]` right by `1` into
`[upper - count + 1 .. upper]`. -/
@[expose] def shiftArrRight (arrBase upper : ℕ) : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | 0, mem => mem
  | j + 1, mem =>
    let prev := shiftArrRight arrBase upper j mem
    Function.update prev (arrBase + (upper - j)) (prev (arrBase + (upper - 1 - j)))

theorem shiftArrRight_outside (arrBase upper count : ℕ) (mem : ℕ → ℕ) (hcount : count ≤ upper)
    (a : ℕ) (ha : a < arrBase + (upper - count) + 1 ∨ arrBase + upper < a) :
    shiftArrRight arrBase upper count mem a = mem a := by
  induction count with
  | zero => rfl
  | succ j ih =>
    simp only [shiftArrRight]
    rw [Function.update_of_ne (by omega)]
    exact ih (by omega) (by omega)

theorem shiftArrRight_shifted (arrBase upper count : ℕ) (mem : ℕ → ℕ) (hcount : count ≤ upper)
    (i : ℕ) (hi₁ : upper - count < i) (hi₂ : i ≤ upper) :
    shiftArrRight arrBase upper count mem (arrBase + i) = mem (arrBase + (i - 1)) := by
  induction count with
  | zero => omega
  | succ j ih =>
    simp only [shiftArrRight]
    rcases eq_or_gt_of_not_lt (show ¬ (i < upper - j) by omega) with rfl | hgt
    · rw [Function.update_self]
      have hsrc : upper - j - 1 = upper - 1 - j := by omega
      rw [hsrc]
      exact shiftArrRight_outside arrBase upper j mem (by omega) _ (by omega)
    · rw [Function.update_of_ne (by omega)]
      exact ih (by omega) hgt

/-! ## 7. Pure memory operations: init, overwrite, leaf insert, and split -/

/-- Initialize a 1-key leaf root at node `0` (`root = 0, cnt = 1`). -/
@[expose] def memInitSingle (base t k v : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  let a0 := nodeAddr base t 0
  let m1 := Function.update mem a0 1
  let m2 := Function.update m1 (a0 + 1) 1
  let m3 := Function.update m2 (a0 + 2) k
  let m4 := Function.update m3 (a0 + (2 * t + 1)) v
  let m5 := Function.update m4 base 0
  Function.update m5 (base + 1) 1

theorem memInitSingle_spec {base t k v : ℕ} (ht : 2 ≤ t) (mem : ℕ → ℕ) :
    let mem' := memInitSingle base t k v mem
    mem' base = 0 ∧
      mem' (base + 1) = 1 ∧
      ValidNode 0 base t mem' 0 ∧
      SortedNode 0 base t mem' 0 ∧
      (readTree 0 base t mem' 0).toList = [(k, v)] ∧
      readNodeSet 0 base t mem' 0 = {0} := by
  intro mem'
  have hb := base_lt_nodeAddr base t 0 0
  have hnk : numKeys base t mem' 0 = 1 := by
    simp (disch := omega) only [numKeys, mem', memInitSingle, Function.update_of_ne,
      Function.update_self]
  refine ⟨?_, ?_, ⟨?_, by omega, by omega⟩, fun i₁ i₂ h12 h2 => by omega, ?_, rfl⟩
  on_goal 4 =>
    obtain ⟨hk0, hv0⟩ : keyAt base t mem' 0 0 = k ∧ valAt base t mem' 0 0 = v := by
      constructor <;> simp (disch := omega) only [keyAt, valAt, mem', memInitSingle,
        Function.update_of_ne, Function.update_self, Nat.add_zero]
    rw [toList_readTree_zero]
    refine List.ext_getElem (by simp [hnk]) fun i hi₁ _ => ?_
    simp only [List.length_ofFn, hnk] at hi₁
    obtain rfl : i = 0 := by omega
    simp [hk0, hv0]
  all_goals simp (disch := omega) only [leafFlag, mem', memInitSingle, Function.update_of_ne,
    Function.update_self]

/-- Overwrite the value at `slot` of node `u` with `v`. -/
@[expose] def memOverwriteVal (base t u slot v : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  Function.update mem (nodeAddr base t u + (2 * t + 1) + slot) v

theorem memOverwriteVal_spec {l base t u slot k v : ℕ} {mem : ℕ → ℕ}
    (ht : 2 ≤ t) (hv_u : ValidNode l base t mem u) (hs_u : SortedNode l base t mem u)
    (hslot : slot < numKeys base t mem u) (hk_eq : keyAt base t mem u slot = k) :
    let mem' := memOverwriteVal base t u slot v mem
    ValidNode l base t mem' u ∧
      SortedNode l base t mem' u ∧
      readNodeSet l base t mem' u = readNodeSet l base t mem u ∧
      (readTree l base t mem' u).toList =
        Cslib.SortedAssoc.insert k v (readTree l base t mem u).toList := by
  intro mem'
  have hst : nodeStride t = 6 * t := rfl
  have hm_le := hv_u.numKeys_le
  have hlf' : leafFlag base t mem' u = leafFlag base t mem u := Function.update_of_ne (by omega) _ _
  have hnk' : numKeys base t mem' u = numKeys base t mem u := Function.update_of_ne (by omega) _ _
  have hkey' : ∀ i < numKeys base t mem u, keyAt base t mem' u i = keyAt base t mem u i :=
    fun i hi => Function.update_of_ne (by omega) _ _
  have hval_self : valAt base t mem' u slot = v := Function.update_self ..
  have hval_ne : ∀ i < numKeys base t mem u, i ≠ slot →
      valAt base t mem' u i = valAt base t mem u i := fun i _ hne =>
    Function.update_of_ne (by omega) _ _
  have entries_iff (p : ℕ × ℕ) :
      (∃ i < numKeys base t mem u, p = (keyAt base t mem' u i, valAt base t mem' u i)) ↔
        p = (k, v) ∨
          (∃ i < numKeys base t mem u, p = (keyAt base t mem u i, valAt base t mem u i)) ∧
            p.1 ≠ k := by
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [hkey' i hi]
      by_cases his : i = slot
      · subst i
        rw [hk_eq, hval_self]
        exact Or.inl rfl
      · rw [hval_ne i hi his]
        refine Or.inr ⟨⟨i, hi, rfl⟩, ?_⟩
        rcases lt_or_gt_of_ne his with hlt | hgt
        · exact (hk_eq ▸ hs_u.keys_strict hlt hslot).ne
        · exact (hk_eq ▸ hs_u.keys_strict hgt hi).ne'
    · rintro (rfl | ⟨⟨i, hi, rfl⟩, hne⟩)
      · exact ⟨slot, hslot, by rw [hkey' slot hslot, hk_eq, hval_self]⟩
      · have his : i ≠ slot := fun heq => hne (heq ▸ hk_eq)
        exact ⟨i, hi, by rw [hkey' i hi, hval_ne i hi his]⟩
  cases l with
  | zero =>
    have hv' : ValidNode 0 base t mem' u := ⟨hlf'.trans hv_u.1, hnk' ▸ hv_u.2.1, hnk' ▸ hv_u.2.2⟩
    have hs' : SortedNode 0 base t mem' u := by
      intro i₁ i₂ h12 h2
      rw [hnk'] at h2
      rw [hkey' i₁ (by omega), hkey' i₂ h2]
      exact hs_u i₁ i₂ h12 h2
    refine ⟨hv', hs', rfl, ?_⟩
    have hsort_old := hs_u.isSortedAssoc
    apply hs'.isSortedAssoc.eq_of_forall_mem_iff (Cslib.SortedAssoc.isSortedAssoc_insert hsort_old)
    intro p
    rw [Cslib.SortedAssoc.mem_insert_iff hsort_old, mem_toList_readTree_zero,
      mem_toList_readTree_zero, hnk']
    exact entries_iff p
  | succ l =>
    have hcid' : ∀ j < numKeys base t mem u + 1, childAt base t mem' u j = childAt base t mem u j :=
      fun j hj => Function.update_of_ne (by omega) _ _
    have hchild_congr := fun j (hj : j < numKeys base t mem u + 1) =>
      congr_all (mem' := mem') (by omega) (hv_u.child_valid hj) (hs_u.child_sorted hj)
        fun w hw o ho =>
          have := nodeAddr_sep base t fun heq : w = u =>
            hv_u.not_mem_child_readNodeSet hj (by rwa [heq] at hw)
          Function.update_of_ne (by omega) _ _
    obtain ⟨hv', hset⟩ := window_valid (off := 0) hv_u (hlf'.trans hv_u.1) hnk'
      hv_u.numKeys_pos hm_le le_rfl hcid' (fun j hj => (hchild_congr j hj).1)
      (fun j hj => (hchild_congr j hj).2.2.1) (fun j hj => (hchild_congr j hj).2.2.2.2)
      fun j hj => hv_u.not_mem_child_readNodeSet hj
    have hs' := window_sorted (off := 0) hs_u hnk' le_rfl hkey' hcid'
      (fun j hj => (hchild_congr j hj).2.2.2.1) fun j hj => (hchild_congr j hj).2.1
    refine ⟨hv', hs', Finset.ext fun x => (hset x).trans mem_readNodeSet_succ.symm, ?_⟩
    have hsort_old := hs_u.isSortedAssoc
    apply hs'.isSortedAssoc.eq_of_forall_mem_iff (Cslib.SortedAssoc.isSortedAssoc_insert hsort_old)
    intro p
    rw [Cslib.SortedAssoc.mem_insert_iff hsort_old, mem_toList_readTree_succ,
      mem_toList_readTree_succ, hnk']
    rw [entries_iff]
    constructor
    · rintro (hroot | ⟨j, hj, hpj⟩)
      · exact hroot.imp_right fun ⟨hp, hne⟩ => ⟨Or.inl hp, hne⟩
      · rw [hcid' j hj, (hchild_congr j hj).2.1] at hpj
        refine Or.inr ⟨Or.inr ⟨j, hj, hpj⟩, ?_⟩
        rcases le_or_gt j slot with hj_le | hj_gt
        · exact (hk_eq ▸ hs_u.child_lt_key hj_le hslot hpj).ne
        · exact (hk_eq ▸ hs_u.key_lt_child hslot hj_gt hj hpj).ne'
    · rintro (rfl | ⟨hroot | ⟨j, hj, hpj⟩, hne⟩)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr ⟨hroot, hne⟩)
      · refine Or.inr ⟨j, hj, ?_⟩
        rwa [hcid' j hj, (hchild_congr j hj).2.1]

/-- Insert a new `(k, v)` pair into non-full leaf node `u` (`m ≤ 2 * t - 2`) at `slot ≤ m`. -/
@[expose] def memInsertLeaf (base t u m slot k v : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  let au := nodeAddr base t u
  let m1 := shiftArrRight (au + 2) m (m - slot) mem
  let m2 := shiftArrRight (au + (2 * t + 1)) m (m - slot) m1
  let m3 := Function.update m2 (au + 2 + slot) k
  let m4 := Function.update m3 (au + (2 * t + 1) + slot) v
  Function.update m4 (au + 1) (m + 1)

theorem memInsertLeaf_outside {base t u m slot k v : ℕ} (ht : 2 ≤ t) (hm_le : m ≤ 2 * t - 2)
    (hslot : slot ≤ m) (mem : ℕ → ℕ) (a : ℕ)
    (ha : a < nodeAddr base t u ∨ nodeAddr base t u + nodeStride t ≤ a) :
    memInsertLeaf base t u m slot k v mem a = mem a := by
  have hst : nodeStride t = 6 * t := rfl
  dsimp only [memInsertLeaf]
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega),
    shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
    shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]

theorem memInsertLeaf_spec {base t u slot k v : ℕ} {mem : ℕ → ℕ}
    (ht : 2 ≤ t) (hv_u : ValidNode 0 base t mem u) (hs_u : SortedNode 0 base t mem u)
    (hm_nonfull : numKeys base t mem u ≤ 2 * t - 2)
    (hslot : slot ≤ numKeys base t mem u)
    (hlt : ∀ i < slot, keyAt base t mem u i < k)
    (hgt : ∀ i, slot ≤ i → i < numKeys base t mem u → k < keyAt base t mem u i) :
    let m := numKeys base t mem u
    let mem' := memInsertLeaf base t u m slot k v mem
    ValidNode 0 base t mem' u ∧
      SortedNode 0 base t mem' u ∧
      numKeys base t mem' u = m + 1 ∧
      (readTree 0 base t mem' u).toList =
        Cslib.SortedAssoc.insert k v (readTree 0 base t mem u).toList := by
  set m := numKeys base t mem u
  set mem' := memInsertLeaf base t u m slot k v mem
  have hlf' : leafFlag base t mem' u = 1 := by
    simp (disch := omega) only [leafFlag, mem', memInsertLeaf, Function.update_of_ne,
      shiftArrRight_outside]
    exact hv_u.1
  have hnk' : numKeys base t mem' u = m + 1 := by
    simp only [numKeys, mem', memInsertLeaf, Function.update_self]
  have hkv' : ∀ i < m + 1,
      (keyAt base t mem' u i, valAt base t mem' u i) =
        if i < slot then (keyAt base t mem u i, valAt base t mem u i)
        else if i = slot then (k, v)
        else (keyAt base t mem u (i - 1), valAt base t mem u (i - 1)) := by
    intro i hi
    rcases lt_trichotomy i slot with h | rfl | h <;>
      simp (disch := omega) only [keyAt, valAt, mem', memInsertLeaf, Function.update_of_ne,
        Function.update_self, shiftArrRight_outside, shiftArrRight_shifted, ite_eq_left,
        ite_eq_right, ↓reduceIte]
  have hv' : ValidNode 0 base t mem' u := ⟨hlf', by rw [hnk']; omega, by rw [hnk']; omega⟩
  have hs' : SortedNode 0 base t mem' u := by
    intro i₁ i₂ h12 h2
    rw [hnk'] at h2
    have h1 := congrArg Prod.fst (hkv' i₁ (by omega))
    have h2' := congrArg Prod.fst (hkv' i₂ h2)
    dsimp only at h1 h2'
    rw [h1, h2']
    split_ifs <;> first
      | omega
      | exact hs_u _ _ (by omega) (by omega)
      | exact hlt _ (by omega)
      | exact hgt _ (by omega) (by omega)
  refine ⟨hv', hs', hnk', ?_⟩
  have hsort_old := hs_u.isSortedAssoc
  apply hs'.isSortedAssoc.eq_of_forall_mem_iff (Cslib.SortedAssoc.isSortedAssoc_insert hsort_old)
  intro p
  rw [Cslib.SortedAssoc.mem_insert_iff hsort_old, mem_toList_readTree_zero,
    mem_toList_readTree_zero, hnk']
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [hkv' i hi]
    rcases lt_trichotomy i slot with hi_lt | hi_eq | hi_gt
    · simp only [hi_lt, ↓reduceIte]
      exact Or.inr ⟨⟨i, by omega, rfl⟩, (hlt i hi_lt).ne⟩
    · subst hi_eq
      simp only [lt_irrefl, ↓reduceIte, true_or]
    · have hn : ¬ i < slot := by omega
      have he : i ≠ slot := by omega
      simp only [hn, he, ↓reduceIte]
      exact Or.inr ⟨⟨i - 1, by omega, rfl⟩, (hgt (i - 1) (by omega) (by omega)).ne'⟩
  · rintro (rfl | ⟨⟨i, hi, rfl⟩, _⟩)
    · refine ⟨slot, by omega, ?_⟩
      simpa only [lt_irrefl, ↓reduceIte] using (hkv' slot (by omega)).symm
    · refine ⟨if i < slot then i else i + 1, by split_ifs <;> omega, ?_⟩
      split_ifs with hi_lt <;>
        simp (disch := omega) only [hkv', hi_lt, ↓reduceIte, ite_eq_right, Nat.add_sub_cancel]

/-! ## 8. Upper-half copy, root/child splitting, and child-insertion lifting -/

/-- Split full node `c` (`2 * t - 1` keys) in place as the left `(t - 1)`-key half and initialize
newly allocated node `z` as the right `(t - 1)`-key half. -/
@[expose] def memCopyUpper (base t c z : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  let ac := nodeAddr base t c
  let az := nodeAddr base t z
  let lf := mem ac
  let m1 := ArrayCopy.copyPrefix mem (ac + 2 + t) (az + 2) (t - 1)
  let m2 := ArrayCopy.copyPrefix m1 (ac + (2 * t + 1) + t) (az + (2 * t + 1)) (t - 1)
  let m3 := if lf = 0 then ArrayCopy.copyPrefix m2 (ac + 4 * t + t) (az + 4 * t) t else m2
  let m4 := Function.update m3 az lf
  let m5 := Function.update m4 (az + 1) (t - 1)
  Function.update m5 (ac + 1) (t - 1)

theorem memCopyUpper_outside {base t c z : ℕ} (ht : 2 ≤ t) (mem : ℕ → ℕ) (a : ℕ)
    (hac : a < nodeAddr base t c ∨ nodeAddr base t c + nodeStride t ≤ a)
    (haz : a < nodeAddr base t z ∨ nodeAddr base t z + nodeStride t ≤ a) :
    memCopyUpper base t c z mem a = mem a := by
  have hst : nodeStride t = 6 * t := rfl
  simp (disch := lia) only [memCopyUpper, Function.update_of_ne, ite_apply,
    ArrayCopy.copyPrefix_outside, ite_self]

theorem memCopyUpper_spec {l base t c z : ℕ} {mem : ℕ → ℕ}
    (ht : 2 ≤ t) (hv_c : ValidNode l base t mem c) (hs_c : SortedNode l base t mem c)
    (hfull : numKeys base t mem c = 2 * t - 1)
    (hz_fresh : z ∉ readNodeSet l base t mem c) :
    let mem₁ := memCopyUpper base t c z mem
    let k_med := keyAt base t mem c (t - 1)
    let v_med := valAt base t mem c (t - 1)
    ValidNode l base t mem₁ c ∧
      SortedNode l base t mem₁ c ∧
      numKeys base t mem₁ c = t - 1 ∧
      ValidNode l base t mem₁ z ∧
      SortedNode l base t mem₁ z ∧
      numKeys base t mem₁ z = t - 1 ∧
      readNodeSet l base t mem₁ c ⊆ readNodeSet l base t mem c ∧
      readNodeSet l base t mem₁ z ⊆ insert z (readNodeSet l base t mem c) ∧
      z ∉ readNodeSet l base t mem₁ c ∧
      c ∉ readNodeSet l base t mem₁ z ∧
      Disjoint (readNodeSet l base t mem₁ c) (readNodeSet l base t mem₁ z) ∧
      (∀ p ∈ (readTree l base t mem₁ c).toList, p.1 < k_med) ∧
      (∀ p ∈ (readTree l base t mem₁ z).toList, k_med < p.1) ∧
      (∀ p, p ∈ (readTree l base t mem c).toList ↔
        p ∈ (readTree l base t mem₁ c).toList ∨ p = (k_med, v_med) ∨
          p ∈ (readTree l base t mem₁ z).toList) := by
  set mem₁ := memCopyUpper base t c z mem
  have hcz : c ≠ z := fun heq => hz_fresh (heq ▸ self_mem_readNodeSet l base t mem c)
  have hst : nodeStride t = 6 * t := rfl
  have hsep := nodeAddr_sep base t hcz
  obtain ⟨hlf_c, hnk_c, hkey_c, hval_c, hlf_z, hnk_z, hkey_z, hval_z⟩ :
      leafFlag base t mem₁ c = leafFlag base t mem c ∧ numKeys base t mem₁ c = t - 1 ∧
      (∀ i < t - 1, keyAt base t mem₁ c i = keyAt base t mem c i) ∧
      (∀ i < t - 1, valAt base t mem₁ c i = valAt base t mem c i) ∧
      leafFlag base t mem₁ z = leafFlag base t mem c ∧ numKeys base t mem₁ z = t - 1 ∧
      (∀ i < t - 1, keyAt base t mem₁ z i = keyAt base t mem c (i + t)) ∧
      (∀ i < t - 1, valAt base t mem₁ z i = valAt base t mem c (i + t)) := by
    refine ⟨?_, ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_⟩ <;>
      simp (disch := omega) only [leafFlag, numKeys, keyAt, valAt, mem₁, memCopyUpper,
        Function.update_of_ne, Function.update_self, ite_apply, ArrayCopy.copyPrefix_outside,
        ArrayCopy.copyPrefix_read, ite_self] <;> congr 1 <;> omega
  cases l with
  | zero =>
    have hv_c' : ValidNode 0 base t mem₁ c := ⟨hlf_c.trans hv_c.1, by omega, by omega⟩
    have hv_z' : ValidNode 0 base t mem₁ z := ⟨hlf_z.trans hv_c.1, by omega, by omega⟩
    have hs_c' : SortedNode 0 base t mem₁ c := fun i₁ i₂ h12 h2 => by
      rw [hkey_c i₁ (by omega), hkey_c i₂ (by omega)]; exact hs_c i₁ i₂ h12 (by omega)
    have hs_z' : SortedNode 0 base t mem₁ z := fun i₁ i₂ h12 h2 => by
      rw [hkey_z i₁ (by omega), hkey_z i₂ (by omega)]; exact hs_c _ _ (by omega) (by omega)
    refine ⟨hv_c', hs_c', hnk_c, hv_z', hs_z', hnk_z, Finset.Subset.refl _,
      Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _), hz_fresh, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [readNodeSet, Finset.mem_singleton]; exact hcz
    · simp only [readNodeSet, Finset.disjoint_singleton]; exact hcz
    · intro p hp
      rw [mem_toList_readTree_zero, hnk_c] at hp
      obtain ⟨i, hi, rfl⟩ := hp
      rw [hkey_c i hi]
      exact hs_c i (t - 1) hi (by omega)
    · intro p hp
      rw [mem_toList_readTree_zero, hnk_z] at hp
      obtain ⟨i, hi, rfl⟩ := hp
      rw [hkey_z i hi]
      exact hs_c (t - 1) (i + t) (by omega) (by omega)
    · intro p
      rw [mem_toList_readTree_zero, mem_toList_readTree_zero, mem_toList_readTree_zero,
        hfull, hnk_c, hnk_z]
      constructor
      · rintro ⟨i, hi, rfl⟩
        rcases lt_trichotomy i (t - 1) with hlt | rfl | hgt
        · exact Or.inl ⟨i, hlt, by rw [hkey_c i hlt, hval_c i hlt]⟩
        · exact Or.inr (Or.inl rfl)
        · obtain ⟨i, rfl⟩ : ∃ i', i = i' + t := ⟨i - t, by omega⟩
          exact Or.inr (Or.inr ⟨i, by omega, by rw [hkey_z i (by omega), hval_z i (by omega)]⟩)
      · rintro (⟨i, hi, rfl⟩ | rfl | ⟨i, hi, rfl⟩)
        · exact ⟨i, by omega, by rw [hkey_c i hi, hval_c i hi]⟩
        · exact ⟨t - 1, by omega, rfl⟩
        · exact ⟨i + t, by omega, by rw [hkey_z i hi, hval_z i hi]⟩
  | succ l =>
    have hkeys := hs_c.1
    have hlf0 : mem (nodeAddr base t c) = 0 := hv_c.1
    obtain ⟨hcid_c, hcid_z⟩ : (∀ j < t, childAt base t mem₁ c j = childAt base t mem c j) ∧
        ∀ j < t, childAt base t mem₁ z j = childAt base t mem c (j + t) := by
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩ <;>
        simp (disch := omega) only [childAt, mem₁, memCopyUpper, hlf0, ↓reduceIte,
          Function.update_of_ne, ArrayCopy.copyPrefix_outside,
          ArrayCopy.copyPrefix_read]
      congr 1; omega
    -- Every child `0 .. 2*t - 1` of `c` is untouched in `mem₁`:
    have hchild_congr := fun j (hj : j < 2 * t) =>
      congr_all (mem' := mem₁) (by omega) (hv_c.child_valid (j := j) (by omega))
        (hs_c.child_sorted (j := j) (by omega)) fun w hw o ho => by
          have := nodeAddr_sep base t fun heq : w = c =>
            hv_c.not_mem_child_readNodeSet (j := j) (by omega) (by rwa [heq] at hw)
          have := nodeAddr_sep base t fun heq : w = z =>
            hz_fresh (child_subset_readNodeSet l base t mem c j (by omega) (by rwa [heq] at hw))
          exact memCopyUpper_outside ht mem _ (by omega) (by omega)
    obtain ⟨hv_c', hset_c⟩ := window_valid (off := 0) hv_c (hlf_c.trans hlf0) hnk_c (by omega)
      (by omega) (by omega) (fun j hj => hcid_c j (by omega))
      (fun j hj => (hchild_congr j (by omega)).1) (fun j hj => (hchild_congr j (by omega)).2.2.1)
      (fun j hj => (hchild_congr j (by omega)).2.2.2.2)
      fun j hj => hv_c.not_mem_child_readNodeSet (by omega)
    obtain ⟨hv_z', hset_z⟩ := window_valid (off := t) hv_c (hlf_z.trans hlf0) hnk_z (by omega)
      (by omega) (by omega) (fun j hj => hcid_z j (by omega))
      (fun j hj => (hchild_congr _ (by omega)).1) (fun j hj => (hchild_congr _ (by omega)).2.2.1)
      (fun j hj => (hchild_congr _ (by omega)).2.2.2.2)
      fun j hj h => hz_fresh (child_subset_readNodeSet l base t mem c _ (by omega) h)
    have hs_c' := window_sorted (off := 0) hs_c hnk_c (by omega) hkey_c
      (fun j hj => hcid_c j (by omega)) (fun j hj => (hchild_congr j (by omega)).2.2.2.1)
      fun j hj => (hchild_congr j (by omega)).2.1
    have hs_z' := window_sorted (off := t) hs_c hnk_z (by omega) hkey_z
      (fun j hj => hcid_z j (by omega)) (fun j hj => (hchild_congr _ (by omega)).2.2.2.1)
      fun j hj => (hchild_congr _ (by omega)).2.1
    have hsub_c : readNodeSet (l + 1) base t mem₁ c ⊆ readNodeSet (l + 1) base t mem c :=
      fun x hx => by
        rcases (hset_c x).1 hx with rfl | ⟨j, hj, hx⟩
        exacts [self_mem_readNodeSet .., child_subset_readNodeSet l base t mem c _ (by omega) hx]
    have hsub_z : readNodeSet (l + 1) base t mem₁ z ⊆
        insert z (readNodeSet (l + 1) base t mem c) := fun x hx => by
      rcases (hset_z x).1 hx with rfl | ⟨j, hj, hx⟩
      exacts [Finset.mem_insert_self _ _,
        Finset.mem_insert_of_mem (child_subset_readNodeSet l base t mem c _ (by omega) hx)]
    have hc_not_z : c ∉ readNodeSet (l + 1) base t mem₁ z := fun h => by
      rcases (hset_z c).1 h with h | ⟨j, hj, hx⟩
      exacts [hcz h, hv_c.not_mem_child_readNodeSet (by omega) hx]
    have hdisj_cz : Disjoint (readNodeSet (l + 1) base t mem₁ c)
        (readNodeSet (l + 1) base t mem₁ z) := Finset.disjoint_left.mpr fun x hxc hxz => by
      rcases (hset_c x).1 hxc with rfl | ⟨j₁, hj₁, hx₁⟩
      · exact hc_not_z hxz
      rcases (hset_z x).1 hxz with heq | ⟨j₂, hj₂, hx₂⟩
      · exact hz_fresh (child_subset_readNodeSet l base t mem c j₁ (by omega) (heq ▸ hx₁))
      exact Finset.disjoint_left.mp (hv_c.2.2.2.2 _ _ (by omega) (by omega) (by omega)) hx₁ hx₂
    refine ⟨hv_c', hs_c', hnk_c, hv_z', hs_z', hnk_z, hsub_c, hsub_z, fun h => hz_fresh (hsub_c h),
      hc_not_z, hdisj_cz, ?_, ?_, ?_⟩
    · intro p hp
      rw [mem_toList_readTree_succ, hnk_c] at hp
      rcases hp with ⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩
      · rw [hkey_c i hi]; exact hkeys i (t - 1) hi (by omega)
      · rw [hcid_c j (by omega), (hchild_congr j (by omega)).2.1] at hpj
        exact hs_c.child_lt_key (by omega) (by omega) hpj
    · intro p hp
      rw [mem_toList_readTree_succ, hnk_z] at hp
      rcases hp with ⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩
      · rw [hkey_z i hi]; exact hkeys (t - 1) (i + t) (by omega) (by omega)
      · rw [hcid_z j (by omega), (hchild_congr (j + t) (by omega)).2.1] at hpj
        exact hs_c.key_lt_child (by omega) (by omega) (by omega) hpj
    · intro p
      rw [mem_toList_readTree_succ, mem_toList_readTree_succ, mem_toList_readTree_succ,
        hfull, hnk_c, hnk_z]
      constructor
      · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩)
        · rcases lt_trichotomy i (t - 1) with hlt | rfl | hgt
          · exact Or.inl (Or.inl ⟨i, hlt, by rw [hkey_c i hlt, hval_c i hlt]⟩)
          · exact Or.inr (Or.inl rfl)
          · obtain ⟨i, rfl⟩ : ∃ i', i = i' + t := ⟨i - t, by omega⟩
            exact Or.inr (Or.inr (Or.inl ⟨i, by omega, by
              rw [hkey_z i (by omega), hval_z i (by omega)]⟩))
        · rcases lt_or_ge j t with hlt | hge
          · refine Or.inl (Or.inr ⟨j, by omega, ?_⟩)
            rwa [hcid_c j hlt, (hchild_congr j (by omega)).2.1]
          · obtain ⟨j, rfl⟩ : ∃ j', j = j' + t := ⟨j - t, by omega⟩
            refine Or.inr (Or.inr (Or.inr ⟨j, by omega, ?_⟩))
            rwa [hcid_z j (by omega), (hchild_congr (j + t) (by omega)).2.1]
      · rintro ((⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩) | rfl | (⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩))
        · exact Or.inl ⟨i, by omega, by rw [hkey_c i hi, hval_c i hi]⟩
        · rw [hcid_c j (by omega), (hchild_congr j (by omega)).2.1] at hpj
          exact Or.inr ⟨j, by omega, hpj⟩
        · exact Or.inl ⟨t - 1, by omega, rfl⟩
        · exact Or.inl ⟨i + t, by omega, by rw [hkey_z i hi, hval_z i hi]⟩
        · rw [hcid_z j (by omega), (hchild_congr (j + t) (by omega)).2.1] at hpj
          exact Or.inr ⟨j + t, by omega, hpj⟩

/-- Split full root `oldRoot` (`2 * t - 1` keys), allocating right half `cnt` and new 1-key root
`cnt + 1`, and updating the arena header `mem base = cnt + 1, mem (base + 1) = cnt + 2`. -/
@[expose] def memSplitRoot (base t oldRoot cnt : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  let k_med := keyAt base t mem oldRoot (t - 1)
  let v_med := valAt base t mem oldRoot (t - 1)
  let m1 := memCopyUpper base t oldRoot cnt mem
  let ar := nodeAddr base t (cnt + 1)
  let m2 := Function.update m1 ar 0
  let m3 := Function.update m2 (ar + 1) 1
  let m4 := Function.update m3 (ar + 2) k_med
  let m5 := Function.update m4 (ar + (2 * t + 1)) v_med
  let m6 := Function.update m5 (ar + 4 * t) oldRoot
  let m7 := Function.update m6 (ar + 4 * t + 1) cnt
  let m8 := Function.update m7 base (cnt + 1)
  Function.update m8 (base + 1) (cnt + 2)

theorem memSplitRoot_spec {l base t oldRoot cnt : ℕ} {mem : ℕ → ℕ}
    (ht : 2 ≤ t) (hv_r : ValidNode l base t mem oldRoot) (hs_r : SortedNode l base t mem oldRoot)
    (hfull : numKeys base t mem oldRoot = 2 * t - 1)
    (hrange : readNodeSet l base t mem oldRoot ⊆ Finset.range cnt) :
    let mem' := memSplitRoot base t oldRoot cnt mem
    mem' base = cnt + 1 ∧
      mem' (base + 1) = cnt + 2 ∧
      ValidNode (l + 1) base t mem' (cnt + 1) ∧
      SortedNode (l + 1) base t mem' (cnt + 1) ∧
      numKeys base t mem' (cnt + 1) = 1 ∧
      readNodeSet (l + 1) base t mem' (cnt + 1) ⊆ Finset.range (cnt + 2) ∧
      (readTree (l + 1) base t mem' (cnt + 1)).toList =
        (readTree l base t mem oldRoot).toList := by
  set mem₁ := memCopyUpper base t oldRoot cnt mem
  set mem' := memSplitRoot base t oldRoot cnt mem
  have hst : nodeStride t = 6 * t := rfl
  have hcnt_not : cnt ∉ readNodeSet l base t mem oldRoot := fun h => by
    have := Finset.mem_range.mp (hrange h); omega
  obtain ⟨hv_c1, hs_c1, hnk_c1, hv_z1, hs_z1, hnk_z1, hsub_c1, hsub_z1, _, _, hdisj_cz1,
    hlt_med1, hgt_med1, hmem_iff1⟩ := memCopyUpper_spec ht hv_r hs_r hfull hcnt_not
  have hcnt1_not_c : cnt + 1 ∉ readNodeSet l base t mem₁ oldRoot := fun h => by
    have := Finset.mem_range.mp (hrange (hsub_c1 h)); omega
  have hcnt1_not_z : cnt + 1 ∉ readNodeSet l base t mem₁ cnt := fun h => by
    rcases Finset.mem_insert.mp (hsub_z1 h) with heq | h'
    · omega
    · have := Finset.mem_range.mp (hrange h'); omega
  -- Neither `oldRoot`'s node set nor `cnt`'s node set contains `cnt + 1` or header words:
  have hframe_sub : ∀ S : Finset ℕ, cnt + 1 ∉ S →
      ∀ v ∈ S, ∀ o < nodeStride t, mem' (nodeAddr base t v + o) = mem₁ (nodeAddr base t v + o) := by
    intro S hnot v hv o ho
    have hsep := nodeAddr_sep base t fun heq : v = cnt + 1 => hnot (heq ▸ hv)
    have hb := base_lt_nodeAddr base t v o
    simp (disch := omega) only [mem', memSplitRoot, mem₁, Function.update_of_ne]
  obtain ⟨hv_c', htr_c', hset_c', hs_c', hnk_c'⟩ :=
    congr_all (by omega) hv_c1 hs_c1 (hframe_sub _ hcnt1_not_c)
  obtain ⟨hv_z', htr_z', hset_z', hs_z', hnk_z'⟩ :=
    congr_all (by omega) hv_z1 hs_z1 (hframe_sub _ hcnt1_not_z)
  -- Fields of `cnt + 1` in `mem'`:
  have hb := base_lt_nodeAddr base t (cnt + 1) 0
  obtain ⟨hlf_r, hnk_r, hk0_r, hv0_r, hc0_r, hc1_r⟩ :
      leafFlag base t mem' (cnt + 1) = 0 ∧ numKeys base t mem' (cnt + 1) = 1 ∧
      keyAt base t mem' (cnt + 1) 0 = keyAt base t mem oldRoot (t - 1) ∧
      valAt base t mem' (cnt + 1) 0 = valAt base t mem oldRoot (t - 1) ∧
      childAt base t mem' (cnt + 1) 0 = oldRoot ∧ childAt base t mem' (cnt + 1) 1 = cnt := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (disch := omega) only [leafFlag, numKeys, keyAt, valAt, childAt, mem', memSplitRoot,
        Function.update_of_ne, Function.update_self, Nat.add_zero]
  have hv_new : ValidNode (l + 1) base t mem' (cnt + 1) := by
    simp only [ValidNode, hnk_r]
    refine ⟨hlf_r, le_rfl, by omega, fun j hj => ?_, fun j₁ j₂ hj₁ hj₂ hne => ?_⟩
    · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      · rw [hc0_r, hset_c', hnk_c', hnk_c1]; exact ⟨hv_c', le_rfl, hcnt1_not_c⟩
      · rw [hc1_r, hset_z', hnk_z', hnk_z1]; exact ⟨hv_z', le_rfl, hcnt1_not_z⟩
    · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (j₁ = 0 ∧ j₂ = 1) ∨ (j₁ = 1 ∧ j₂ = 0) := by omega
      · rw [hc0_r, hc1_r, hset_c', hset_z']; exact hdisj_cz1
      · rw [hc0_r, hc1_r, hset_c', hset_z']; exact hdisj_cz1.symm
  have hs_new : SortedNode (l + 1) base t mem' (cnt + 1) := by
    simp only [SortedNode, hnk_r]
    refine ⟨fun i₁ i₂ h12 h2 => by omega, fun j hj => ?_, fun i hi p hp => ?_,
      fun i hi p hp => ?_⟩
    · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      · rw [hc0_r]; exact hs_c'
      · rw [hc1_r]; exact hs_z'
    · obtain rfl : i = 0 := by omega
      rw [hc0_r, htr_c'] at hp
      rw [hk0_r]
      exact hlt_med1 p hp
    · obtain rfl : i = 0 := by omega
      rw [hc1_r, htr_z'] at hp
      rw [hk0_r]
      exact hgt_med1 p hp
  have hrange_new : readNodeSet (l + 1) base t mem' (cnt + 1) ⊆ Finset.range (cnt + 2) := by
    intro x hx
    rw [mem_readNodeSet_succ, hnk_r] at hx
    rw [Finset.mem_range]
    obtain rfl | ⟨j, hj, hx⟩ := hx
    · omega
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · rw [hc0_r, hset_c'] at hx
      have := Finset.mem_range.mp (hrange (hsub_c1 hx)); omega
    · rw [hc1_r, hset_z'] at hx
      rcases Finset.mem_insert.mp (hsub_z1 hx) with rfl | hx'
      · omega
      · have := Finset.mem_range.mp (hrange hx'); omega
  refine ⟨?_, ?_, hv_new, hs_new, hnk_r, hrange_new, ?_⟩
  · simp (disch := omega) only [mem', memSplitRoot, Function.update_of_ne, Function.update_self]
  · simp only [mem', memSplitRoot, Function.update_self]
  · apply hs_new.isSortedAssoc.eq_of_forall_mem_iff hs_r.isSortedAssoc
    intro p
    rw [mem_toList_readTree_succ, hnk_r, hmem_iff1]
    constructor
    · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩)
      · obtain rfl : i = 0 := by omega
        rw [hk0_r, hv0_r]
        exact Or.inr (Or.inl rfl)
      · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
        · rw [hc0_r, htr_c'] at hpj; exact Or.inl hpj
        · rw [hc1_r, htr_z'] at hpj; exact Or.inr (Or.inr hpj)
    · rintro (hpc | rfl | hpz)
      · exact Or.inr ⟨0, by omega, by rwa [hc0_r, htr_c']⟩
      · exact Or.inl ⟨0, by omega, by rw [hk0_r, hv0_r]⟩
      · exact Or.inr ⟨1, by omega, by rwa [hc1_r, htr_z']⟩

/-- Split full child `c = childAt u slot` (`2 * t - 1` keys) of non-full internal parent `u`
(`m ≤ 2 * t - 2`), allocating right half `cnt`, shifting `u`'s keys/values/children, inserting the
median at `slot`, and incrementing `mem (base + 1)` to `cnt + 1`. -/
@[expose] def memSplitChild (base t u m slot c cnt : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  let k_med := keyAt base t mem c (t - 1)
  let v_med := valAt base t mem c (t - 1)
  let m1 := memCopyUpper base t c cnt mem
  let au := nodeAddr base t u
  let m2 := shiftArrRight (au + 2) m (m - slot) m1
  let m3 := shiftArrRight (au + (2 * t + 1)) m (m - slot) m2
  let m4 := shiftArrRight (au + 4 * t) (m + 1) (m - slot) m3
  let m5 := Function.update m4 (au + 2 + slot) k_med
  let m6 := Function.update m5 (au + (2 * t + 1) + slot) v_med
  let m7 := Function.update m6 (au + 4 * t + (slot + 1)) cnt
  let m8 := Function.update m7 (au + 1) (m + 1)
  Function.update m8 (base + 1) (cnt + 1)

theorem memSplitChild_outside {base t u m slot c cnt : ℕ} (ht : 2 ≤ t)
    (hm_le : m ≤ 2 * t - 2) (hslot : slot ≤ m) (mem : ℕ → ℕ) (a : ℕ)
    (hne_b1 : a ≠ base + 1)
    (hau : a < nodeAddr base t u ∨ nodeAddr base t u + nodeStride t ≤ a)
    (hac : a < nodeAddr base t c ∨ nodeAddr base t c + nodeStride t ≤ a)
    (haz : a < nodeAddr base t cnt ∨ nodeAddr base t cnt + nodeStride t ≤ a) :
    memSplitChild base t u m slot c cnt mem a = mem a := by
  have hst : nodeStride t = 6 * t := rfl
  dsimp only [memSplitChild]
  rw [Function.update_of_ne hne_b1, Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega),
    shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
    shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
    shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
  exact memCopyUpper_outside ht mem a hac haz

/-- Field readbacks of `memSplitChild` on the parent node `u`: the key count grows by one, the
median of `c` enters key slot `slot`, `cnt` enters child slot `slot + 1`, and the remaining keys
and children shift right past the insertion point. -/
private theorem memSplitChild_fields {base t u m slot c cnt : ℕ} {mem : ℕ → ℕ} (ht : 2 ≤ t)
    (hm : m ≤ 2 * t - 2) (hslot : slot ≤ m) (hu_ne_c : u ≠ c) (hu_ne_cnt : u ≠ cnt) :
    let mem' := memSplitChild base t u m slot c cnt mem
    leafFlag base t mem' u = leafFlag base t mem u ∧ numKeys base t mem' u = m + 1 ∧
      (∀ i < m + 1,
        (keyAt base t mem' u i, valAt base t mem' u i) =
          if i < slot then (keyAt base t mem u i, valAt base t mem u i)
          else if i = slot then (keyAt base t mem c (t - 1), valAt base t mem c (t - 1))
          else (keyAt base t mem u (i - 1), valAt base t mem u (i - 1))) ∧
      ∀ j < m + 2,
        childAt base t mem' u j =
          if j ≤ slot then childAt base t mem u j
          else if j = slot + 1 then cnt
          else childAt base t mem u (j - 1) := by
  intro mem'
  have hst : nodeStride t = 6 * t := rfl
  have hsep_c := nodeAddr_sep base t hu_ne_c
  have hsep_z := nodeAddr_sep base t hu_ne_cnt
  have hb := base_lt_nodeAddr base t u 0
  refine ⟨?_, ?_, fun i hi => ?_, fun j hj => ?_⟩
  · simp (disch := omega) only [leafFlag, mem', memSplitChild, Function.update_of_ne,
      shiftArrRight_outside, memCopyUpper_outside]
  · simp (disch := omega) only [numKeys, mem', memSplitChild, Function.update_of_ne,
      Function.update_self]
  · rcases lt_trichotomy i slot with h | rfl | h <;>
      simp (disch := omega) only [keyAt, valAt, mem', memSplitChild, Function.update_of_ne,
        Function.update_self, shiftArrRight_outside, shiftArrRight_shifted, memCopyUpper_outside,
        ite_eq_left, ite_eq_right, ↓reduceIte]
  · rcases lt_trichotomy j (slot + 1) with h | rfl | h <;>
      simp (disch := omega) only [childAt, mem', memSplitChild, Function.update_of_ne,
        Function.update_self, shiftArrRight_outside, shiftArrRight_shifted, memCopyUpper_outside,
        ite_eq_left, ite_eq_right, ↓reduceIte]

theorem memSplitChild_spec {l base t u slot cnt : ℕ} {mem : ℕ → ℕ}
    (ht : 2 ≤ t) (hv_u : ValidNode (l + 1) base t mem u) (hs_u : SortedNode (l + 1) base t mem u)
    (hm_nonfull : numKeys base t mem u ≤ 2 * t - 2)
    (hslot : slot ≤ numKeys base t mem u)
    (hfull : numKeys base t mem (childAt base t mem u slot) = 2 * t - 1)
    (hcnt_fresh : cnt ∉ readNodeSet (l + 1) base t mem u) :
    let m := numKeys base t mem u
    let c := childAt base t mem u slot
    let mem' := memSplitChild base t u m slot c cnt mem
    mem' (base + 1) = cnt + 1 ∧
      mem' base = mem base ∧
      ValidNode (l + 1) base t mem' u ∧
      SortedNode (l + 1) base t mem' u ∧
      numKeys base t mem' u = m + 1 ∧
      keyAt base t mem' u slot = keyAt base t mem c (t - 1) ∧
      valAt base t mem' u slot = valAt base t mem c (t - 1) ∧
      childAt base t mem' u slot = c ∧
      childAt base t mem' u (slot + 1) = cnt ∧
      numKeys base t mem' c = t - 1 ∧
      numKeys base t mem' cnt = t - 1 ∧
      readNodeSet (l + 1) base t mem' u ⊆ insert cnt (readNodeSet (l + 1) base t mem u) ∧
      (readTree (l + 1) base t mem' u).toList = (readTree (l + 1) base t mem u).toList := by
  set m := numKeys base t mem u
  set c := childAt base t mem u slot
  set mem₁ := memCopyUpper base t c cnt mem
  have hst : nodeStride t = 6 * t := rfl
  have ⟨hlf_u, hm₁, _, hch_u, hdisj_u⟩ := hv_u
  have ⟨hkeys_u, hcs_u, hleft_u, hright_u⟩ := hs_u
  have hslot_lt1 : slot < m + 1 := by omega
  have hv_c : ValidNode l base t mem c := (hch_u slot hslot_lt1).1
  have hs_c : SortedNode l base t mem c := hcs_u slot hslot_lt1
  have hu_ne_c : u ≠ c := fun heq =>
    (hch_u slot hslot_lt1).2.2
      (Eq.ndrec (motive := fun x => x ∈ readNodeSet l base t mem c)
        (self_mem_readNodeSet l base t mem c) heq.symm)
  have hu_ne_cnt : u ≠ cnt := fun heq =>
    hcnt_fresh (heq ▸ self_mem_readNodeSet (l + 1) base t mem u)
  -- Readbacks on `u` after the split:
  obtain ⟨hlf_u', hnk_u', hkv_u', hcid_u'⟩ :=
    memSplitChild_fields (mem := mem) ht hm_nonfull hslot hu_ne_c hu_ne_cnt
  rw [hlf_u] at hlf_u'
  set mem' := memSplitChild base t u m slot c cnt mem
  have hcnt_not_c : cnt ∉ readNodeSet l base t mem c := fun h =>
    hcnt_fresh (child_subset_readNodeSet l base t mem u slot hslot_lt1 h)
  obtain ⟨hv_c1, hs_c1, hnk_c1, hv_z1, hs_z1, hnk_z1, hsub_c1, hsub_z1, _, _, hdisj_cz1,
    hlt_med1, hgt_med1, hmem_iff1⟩ := memCopyUpper_spec ht hv_c hs_c hfull hcnt_not_c
  -- Step 2 of `memSplitChild` modifies ONLY `u` and `base + 1`, so any node set `S` with `u ∉ S`
  -- keeps its `mem₁` cells in `mem'`:
  have hframe_not_u : ∀ S : Finset ℕ, u ∉ S →
      ∀ v ∈ S, ∀ o < nodeStride t, mem' (nodeAddr base t v + o) = mem₁ (nodeAddr base t v + o) := by
    intro S hnot v hv o ho
    have hsep := nodeAddr_sep base t fun heq : v = u => hnot (heq ▸ hv)
    have hb := base_lt_nodeAddr base t v o
    simp (disch := omega) only [mem', memSplitChild, mem₁, Function.update_of_ne,
      shiftArrRight_outside]
  have hu_not_c1 : u ∉ readNodeSet l base t mem₁ c := fun h =>
    (hch_u slot hslot_lt1).2.2 (hsub_c1 h)
  have hu_not_z1 : u ∉ readNodeSet l base t mem₁ cnt := fun h => by
    rcases Finset.mem_insert.mp (hsub_z1 h) with heq | h'
    exacts [hu_ne_cnt heq, (hch_u slot hslot_lt1).2.2 h']
  obtain ⟨hv_c', htr_c', hset_c', hs_c', hnk_c'⟩ :=
    congr_all (by omega) hv_c1 hs_c1 (hframe_not_u _ hu_not_c1)
  obtain ⟨hv_z', htr_z', hset_z', hs_z', hnk_z'⟩ :=
    congr_all (by omega) hv_z1 hs_z1 (hframe_not_u _ hu_not_z1)
  rw [hnk_c1] at hnk_c'
  rw [hnk_z1] at hnk_z'
  -- Every sibling `j ≠ slot` (`j < m + 1`) of `u` is untouched from `mem` to `mem'`:
  have hsib_congr := fun j (hj : j < m + 1) (hne : j ≠ slot) =>
    congr_all (mem' := mem') (by omega) (hch_u j hj).1 (hcs_u j hj) fun w hw o ho => by
      have := nodeAddr_sep base t fun heq : w = u => (hch_u j hj).2.2 (by rwa [heq] at hw)
      have := nodeAddr_sep base t fun heq : w = c =>
        Finset.disjoint_left.mp (hdisj_u j slot hj hslot_lt1 hne) hw
          (by rw [heq]; exact self_mem_readNodeSet l base t mem c)
      have := nodeAddr_sep base t fun heq : w = cnt =>
        hcnt_fresh (child_subset_readNodeSet l base t mem u j hj (by rwa [heq] at hw))
      have := base_lt_nodeAddr base t w o
      exact memSplitChild_outside ht hm_nonfull hslot mem _ (by omega) (by omega) (by omega)
        (by omega)
  have hk_slot : keyAt base t mem' u slot = keyAt base t mem c (t - 1) := by
    simpa only [lt_irrefl, ↓reduceIte] using congrArg Prod.fst (hkv_u' slot (by omega))
  have hv_slot : valAt base t mem' u slot = valAt base t mem c (t - 1) := by
    simpa only [lt_irrefl, ↓reduceIte] using congrArg Prod.snd (hkv_u' slot (by omega))
  have hc_slot : childAt base t mem' u slot = c := by
    simpa only [le_rfl, ↓reduceIte] using hcid_u' slot (by omega)
  have hc_slot1 : childAt base t mem' u (slot + 1) = cnt := by
    have hn : ¬ slot + 1 ≤ slot := by omega
    simpa only [hn, ↓reduceIte] using hcid_u' (slot + 1) (by omega)
  have hmed_in_c : (keyAt base t mem c (t - 1), valAt base t mem c (t - 1)) ∈
      (readTree l base t mem c).toList := (hmem_iff1 _).mpr (Or.inr (Or.inl rfl))
  -- Every other new child `j` of `u` is the old child `o` it was shifted from, and every new key
  -- other than the median is the old key it was shifted from:
  have hold : ∀ j < m + 2, j ≠ slot → j ≠ slot + 1 →
      ∃ o < m + 1, o ≠ slot ∧ (o = j ∧ j < slot ∨ o + 1 = j ∧ slot + 1 < j) ∧
        childAt base t mem' u j = childAt base t mem u o := by
    intro j hj h1 h2
    rcases Nat.lt_or_gt_of_ne h1 with h | h
    · exact ⟨j, by omega, h1, Or.inl ⟨rfl, h⟩, by simpa only [h.le, ↓reduceIte] using hcid_u' j hj⟩
    · have hn : ¬j ≤ slot := by omega
      exact ⟨j - 1, by omega, by omega, Or.inr ⟨by omega, by omega⟩,
        by simpa only [hn, h2, ↓reduceIte] using hcid_u' j hj⟩
  have hkey_old : ∀ i < m + 1, i ≠ slot →
      ∃ o < m, (o = i ∧ i < slot ∨ o + 1 = i ∧ slot < i) ∧
        (keyAt base t mem' u i, valAt base t mem' u i) =
          (keyAt base t mem u o, valAt base t mem u o) := by
    intro i hi h1
    rw [hkv_u' i hi]
    rcases Nat.lt_or_gt_of_ne h1 with h | h
    · exact ⟨i, by omega, Or.inl ⟨rfl, h⟩, by simp only [h, ↓reduceIte]⟩
    · have hn : ¬i < slot := by omega
      exact ⟨i - 1, by omega, Or.inr ⟨by omega, h⟩, by simp only [hn, h1, ↓reduceIte]⟩
  -- Each entry and node below a new child lies below the old child it came from (or is `cnt`):
  have hchild_old : ∀ j < m + 2, ∀ p ∈ (readTree l base t mem' (childAt base t mem' u j)).toList,
      ∃ o < m + 1, (o = j ∧ j ≤ slot ∨ o + 1 = j ∧ slot < j) ∧
        p ∈ (readTree l base t mem (childAt base t mem u o)).toList := by
    intro j hj p hp
    by_cases h1 : j = slot
    · rw [h1, hc_slot, htr_c'] at hp
      exact ⟨slot, hslot_lt1, by omega, (hmem_iff1 p).mpr (Or.inl hp)⟩
    by_cases h2 : j = slot + 1
    · rw [h2, hc_slot1, htr_z'] at hp
      exact ⟨slot, hslot_lt1, by omega, (hmem_iff1 p).mpr (Or.inr (Or.inr hp))⟩
    obtain ⟨o, ho, hos, hoj, hco⟩ := hold j hj h1 h2
    rw [hco, (hsib_congr o ho hos).2.1] at hp
    exact ⟨o, ho, by omega, hp⟩
  have hset_old : ∀ j < m + 2, ∀ x ∈ readNodeSet l base t mem' (childAt base t mem' u j),
      (j = slot + 1 ∧ x = cnt) ∨ ∃ o < m + 1, (o = j ∧ j ≤ slot ∨ o + 1 = j ∧ slot < j) ∧
        x ∈ readNodeSet l base t mem (childAt base t mem u o) := by
    intro j hj x hx
    by_cases h1 : j = slot
    · rw [h1, hc_slot, hset_c'] at hx
      exact Or.inr ⟨slot, hslot_lt1, by omega, hsub_c1 hx⟩
    by_cases h2 : j = slot + 1
    · rw [h2, hc_slot1, hset_z'] at hx
      rcases Finset.mem_insert.mp (hsub_z1 hx) with hxz | hxc
      exacts [Or.inl ⟨h2, hxz⟩, Or.inr ⟨slot, hslot_lt1, by omega, hxc⟩]
    obtain ⟨o, ho, hos, hoj, hco⟩ := hold j hj h1 h2
    rw [hco, (hsib_congr o ho hos).2.2.1] at hx
    exact Or.inr ⟨o, ho, by omega, hx⟩
  have hv_u' : ValidNode (l + 1) base t mem' u := by
    simp only [ValidNode, hnk_u']
    refine ⟨hlf_u', by omega, by omega, fun j hj => ?_, ?_⟩
    · by_cases h1 : j = slot
      · rw [h1, hc_slot, hset_c', hnk_c']; exact ⟨hv_c', le_rfl, hu_not_c1⟩
      by_cases h2 : j = slot + 1
      · rw [h2, hc_slot1, hset_z', hnk_z']; exact ⟨hv_z', le_rfl, hu_not_z1⟩
      obtain ⟨o, ho, hos, -, hco⟩ := hold j hj h1 h2
      obtain ⟨hvs, -, hsets, -, hnks⟩ := hsib_congr o ho hos
      rw [hco, hsets, hnks]; exact ⟨hvs, (hch_u o ho).2⟩
    · -- Pairwise disjointness of the `m + 2` child node sets:
      intro j₁ j₂ hj₁ hj₂ hne
      wlog hlt12 : j₁ < j₂ generalizing j₁ j₂
      · exact (this j₂ j₁ hj₂ hj₁ hne.symm (by omega)).symm
      by_cases hcz : j₁ = slot ∧ j₂ = slot + 1
      · rw [hcz.1, hcz.2, hc_slot, hset_c', hc_slot1, hset_z']; exact hdisj_cz1
      have hfresh := fun o (ho : o < m + 1) (h : cnt ∈ readNodeSet l base t mem
          (childAt base t mem u o)) => hcnt_fresh (child_subset_readNodeSet l base t mem u o ho h)
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      rcases hset_old j₁ hj₁ x hx₁ with ⟨h₁, hc₁⟩ | ⟨o₁, ho₁, hoj₁, hx₁⟩ <;>
        rcases hset_old j₂ hj₂ x hx₂ with ⟨h₂, hc₂⟩ | ⟨o₂, ho₂, hoj₂, hx₂⟩
      · omega
      · exact hfresh o₂ ho₂ (hc₁ ▸ hx₂)
      · exact hfresh o₁ ho₁ (hc₂ ▸ hx₁)
      · exact Finset.disjoint_left.mp (hdisj_u o₁ o₂ ho₁ ho₂ (by omega)) hx₁ hx₂
  have hs_u' : SortedNode (l + 1) base t mem' u := by
    simp only [SortedNode, hnk_u']
    refine ⟨fun i₁ i₂ h12 h2 => ?_, fun j hj => ?_, fun i hi p hp => ?_, fun i hi p hp => ?_⟩
    · -- Keys stay strictly increasing around the inserted median:
      by_cases h1 : i₁ = slot
      · obtain ⟨o₂, ho₂, hoi₂, hkv₂⟩ := hkey_old i₂ h2 (by omega)
        rw [h1, hk_slot, (Prod.mk.inj hkv₂).1]
        exact hs_u.child_lt_key (by omega) ho₂ hmed_in_c
      obtain ⟨o₁, ho₁, hoi₁, hkv₁⟩ := hkey_old i₁ (by omega) h1
      rw [(Prod.mk.inj hkv₁).1]
      by_cases h2' : i₂ = slot
      · rw [h2', hk_slot]; exact hs_u.key_lt_child ho₁ (by omega) hslot_lt1 hmed_in_c
      obtain ⟨o₂, ho₂, hoi₂, hkv₂⟩ := hkey_old i₂ h2 h2'
      rw [(Prod.mk.inj hkv₂).1]; exact hkeys_u o₁ o₂ (by omega) ho₂
    · by_cases h1 : j = slot
      · rw [h1, hc_slot]; exact hs_c'
      by_cases h2 : j = slot + 1
      · rw [h2, hc_slot1]; exact hs_z'
      obtain ⟨o, ho, hos, -, hco⟩ := hold j hj h1 h2
      rw [hco]; exact (hsib_congr o ho hos).2.2.2.1
    · by_cases h1 : i = slot
      · rw [h1, hc_slot, htr_c'] at hp; rw [h1, hk_slot]; exact hlt_med1 p hp
      obtain ⟨o, ho, hoi, hkv⟩ := hkey_old i hi h1
      obtain ⟨o', ho', hoi', hp'⟩ := hchild_old i (by omega) p hp
      obtain rfl : o' = o := by omega
      rw [(Prod.mk.inj hkv).1]; exact hleft_u o' ho p hp'
    · by_cases h1 : i = slot
      · rw [h1, hc_slot1, htr_z'] at hp; rw [h1, hk_slot]; exact hgt_med1 p hp
      obtain ⟨o, ho, hoi, hkv⟩ := hkey_old i hi h1
      obtain ⟨o', ho', hoi', hp'⟩ := hchild_old (i + 1) (by omega) p hp
      obtain rfl : o' = o + 1 := by omega
      rw [(Prod.mk.inj hkv).1]; exact hright_u o ho p hp'
  have hsub_u' : readNodeSet (l + 1) base t mem' u ⊆
      insert cnt (readNodeSet (l + 1) base t mem u) := by
    intro x hx
    rw [mem_readNodeSet_succ, hnk_u'] at hx
    rcases hx with rfl | ⟨j, hj, hx⟩
    · exact Finset.mem_insert_of_mem (self_mem_readNodeSet _ _ _ _ _)
    rcases hset_old j hj x hx with ⟨-, rfl⟩ | ⟨o, ho, -, hx⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (child_subset_readNodeSet l base t mem u o ho hx)
  have hmem_b1 : mem' (base + 1) = cnt + 1 := by
    simp only [mem', memSplitChild, Function.update_self]
  have hmem_b0 : mem' base = mem base := by
    have hb := base_lt_nodeAddr base t u 0
    have hbc := base_lt_nodeAddr base t c 0
    have hbz := base_lt_nodeAddr base t cnt 0
    exact memSplitChild_outside ht hm_nonfull hslot mem base (by omega) (by omega)
      (by omega) (by omega)
  refine ⟨hmem_b1, hmem_b0, hv_u', hs_u', hnk_u', hk_slot, hv_slot, hc_slot, hc_slot1,
    hnk_c', hnk_z', hsub_u', ?_⟩
  apply hs_u'.isSortedAssoc.eq_of_forall_mem_iff hs_u.isSortedAssoc
  intro p
  rw [mem_toList_readTree_succ, mem_toList_readTree_succ, hnk_u']
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩)
    · by_cases h1 : i = slot
      · rw [h1, hk_slot, hv_slot]; exact Or.inr ⟨slot, hslot_lt1, hmed_in_c⟩
      obtain ⟨o, ho, -, hkv⟩ := hkey_old i hi h1
      exact Or.inl ⟨o, ho, hkv⟩
    · obtain ⟨o, ho, -, hp⟩ := hchild_old j hj p hpj
      exact Or.inr ⟨o, ho, hp⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩)
    · refine Or.inl ⟨if i < slot then i else i + 1, by split_ifs <;> omega, ?_⟩
      split_ifs with hi_lt <;>
        simp (disch := omega) only [hkv_u', hi_lt, ↓reduceIte, ite_eq_right, Nat.add_sub_cancel]
    · by_cases hj_eq : j = slot
      · subst hj_eq
        rcases (hmem_iff1 p).mp hpj with hpc | rfl | hpz
        · exact Or.inr ⟨j, by omega, by rwa [hc_slot, htr_c']⟩
        · exact Or.inl ⟨j, by omega, by rw [hk_slot, hv_slot]⟩
        · exact Or.inr ⟨j + 1, by omega, by rwa [hc_slot1, htr_z']⟩
      · refine Or.inr ⟨if j < slot then j else j + 1, by split_ifs <;> omega, ?_⟩
        split_ifs with hj_lt <;>
          simp (disch := omega) only [hcid_u', ite_eq_left, ite_eq_right, Nat.add_sub_cancel] <;>
          rwa [(hsib_congr j hj hj_eq).2.1]

/-- Lift a recursive subtree insertion at `c = childAt u slot` back up to internal node `u` when
`mem'` modifies no node in `readNodeSet (l + 1) base t mem u \ readNodeSet l base t mem c`. -/
theorem childInsert_spec {l base t u slot k v cnt cnt' : ℕ} {mem mem' : ℕ → ℕ}
    (ht : 2 ≤ t)
    (hv_u : ValidNode (l + 1) base t mem u)
    (hs_u : SortedNode (l + 1) base t mem u)
    (hslot : slot ≤ numKeys base t mem u)
    (hlt : ∀ i < slot, keyAt base t mem u i < k)
    (hgt : ∀ i, slot ≤ i → i < numKeys base t mem u → k < keyAt base t mem u i)
    (hrange : readNodeSet (l + 1) base t mem u ⊆ Finset.range cnt)
    (hframe : ∀ w_id, w_id ∉ readNodeSet l base t mem (childAt base t mem u slot) ∪
        Finset.Ico cnt cnt' →
      ∀ o < nodeStride t, mem' (nodeAddr base t w_id + o) = mem (nodeAddr base t w_id + o))
    (hv_c' : ValidNode l base t mem' (childAt base t mem u slot))
    (hs_c' : SortedNode l base t mem' (childAt base t mem u slot))
    (hnk_c' : t - 1 ≤ numKeys base t mem' (childAt base t mem u slot))
    (hsub_c' : readNodeSet l base t mem' (childAt base t mem u slot) ⊆
      readNodeSet l base t mem (childAt base t mem u slot) ∪ Finset.Ico cnt cnt')
    (htr_c' : (readTree l base t mem' (childAt base t mem u slot)).toList =
      Cslib.SortedAssoc.insert k v (readTree l base t mem (childAt base t mem u slot)).toList) :
    ValidNode (l + 1) base t mem' u ∧
      SortedNode (l + 1) base t mem' u ∧
      numKeys base t mem' u = numKeys base t mem u ∧
      readNodeSet (l + 1) base t mem' u ⊆
        readNodeSet (l + 1) base t mem u ∪ Finset.Ico cnt cnt' ∧
      (readTree (l + 1) base t mem' u).toList =
        Cslib.SortedAssoc.insert k v (readTree (l + 1) base t mem u).toList := by
  set m := numKeys base t mem u
  set c := childAt base t mem u slot
  have ⟨hlf_u, hm₁, hm₂, hch_u, hdisj_u⟩ := hv_u
  have ⟨hkeys_u, hcs_u, hleft_u, hright_u⟩ := hs_u
  have hslot_lt1 : slot < m + 1 := by omega
  have hu_in_range : u < cnt :=
    Finset.mem_range.mp (hrange (self_mem_readNodeSet (l + 1) base t mem u))
  have hu_not_mod : u ∉ readNodeSet l base t mem c ∪ Finset.Ico cnt cnt' := by
    simp only [Finset.mem_union, Finset.mem_Ico, not_or]
    exact ⟨(hch_u slot hslot_lt1).2.2, by omega⟩
  obtain ⟨hlf_u', hnk_u', hf⟩ := fields_eq_of_cells (by omega) (hframe u hu_not_mod)
  rw [hlf_u] at hlf_u'
  have hkey_u' : ∀ i < m, keyAt base t mem' u i = keyAt base t mem u i := fun i hi =>
    (hf i (by omega)).1
  have hval_u' : ∀ i < m, valAt base t mem' u i = valAt base t mem u i := fun i hi =>
    (hf i (by omega)).2.1
  have hcid_u' : ∀ j < m + 1, childAt base t mem' u j = childAt base t mem u j := fun j hj =>
    (hf j (by omega)).2.2
  -- Every sibling `j ≠ slot` is untouched:
  have hsib_congr := fun j (hj : j < m + 1) (hne : j ≠ slot) =>
    congr_all (mem' := mem') (by omega) (hch_u j hj).1 (hcs_u j hj) fun w hw o ho => by
      refine hframe w ?_ o ho
      simp only [Finset.mem_union, Finset.mem_Ico, not_or]
      refine ⟨fun hwc => Finset.disjoint_left.mp (hdisj_u j slot hj hslot_lt1 hne) hw hwc, ?_⟩
      have := Finset.mem_range.mp (hrange (child_subset_readNodeSet l base t mem u j hj hw))
      omega
  have hv_u'' : ValidNode (l + 1) base t mem' u := by
    simp only [ValidNode, hnk_u']
    refine ⟨hlf_u', hm₁, hm₂, ?_, ?_⟩
    · intro j hj
      rw [hcid_u' j hj]
      by_cases hjs : j = slot
      · subst hjs
        exact ⟨hv_c', hnk_c', fun hu_in => hu_not_mod (hsub_c' hu_in)⟩
      · obtain ⟨hvs, _, hsets, _, hnks⟩ := hsib_congr j hj hjs
        rw [hsets, hnks]
        exact ⟨hvs, (hch_u j hj).2.1, (hch_u j hj).2.2⟩
    · -- Only child `slot` changed, and its new nodes lie in `Ico cnt cnt'`, above every old node:
      intro j₁ j₂ hj₁ hj₂ hne
      wlog h2 : j₂ ≠ slot generalizing j₁ j₂
      · exact (this j₂ j₁ hj₂ hj₁ hne.symm (by omega)).symm
      rw [hcid_u' j₂ hj₂, (hsib_congr j₂ hj₂ h2).2.2.1, hcid_u' j₁ hj₁, Finset.disjoint_left]
      intro x hx₁ hx₂
      by_cases h1 : j₁ = slot
      · subst h1
        rcases Finset.mem_union.mp (hsub_c' hx₁) with hx₁ | hx₁
        · exact Finset.disjoint_left.mp (hdisj_u _ j₂ hslot_lt1 hj₂ hne) hx₁ hx₂
        · have := Finset.mem_range.mp (hrange (child_subset_readNodeSet l base t mem u j₂ hj₂ hx₂))
          have := Finset.mem_Ico.mp hx₁
          omega
      · rw [(hsib_congr j₁ hj₁ h1).2.2.1] at hx₁
        exact Finset.disjoint_left.mp (hdisj_u j₁ j₂ hj₁ hj₂ hne) hx₁ hx₂
  have hs_u'' : SortedNode (l + 1) base t mem' u := by
    simp only [SortedNode, hnk_u']
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i₁ i₂ h12 h2
      rw [hkey_u' i₁ (by omega), hkey_u' i₂ h2]
      exact hkeys_u i₁ i₂ h12 h2
    · intro j hj
      rw [hcid_u' j hj]
      by_cases hjs : j = slot
      · subst hjs; exact hs_c'
      · exact (hsib_congr j hj hjs).2.2.2.1
    · intro i hi p hp
      rw [hcid_u' i (by omega)] at hp
      rw [hkey_u' i hi]
      by_cases his : i = slot
      · subst his
        rw [htr_c'] at hp
        rcases Cslib.SortedAssoc.eq_or_mem_of_mem_insert hp with rfl | hp_old
        · exact hgt i le_rfl hi
        · exact hleft_u i hi p hp_old
      · rw [(hsib_congr i (by omega) his).2.1] at hp
        exact hleft_u i hi p hp
    · intro i hi p hp
      rw [hcid_u' (i + 1) (by omega)] at hp
      rw [hkey_u' i hi]
      by_cases his1 : i + 1 = slot
      · rw [his1, htr_c'] at hp
        rcases Cslib.SortedAssoc.eq_or_mem_of_mem_insert hp with rfl | hp_old
        · exact hlt i (by omega)
        · have hp_old' : p ∈ (readTree l base t mem (childAt base t mem u (i + 1))).toList := by
            dsimp only [c] at hp_old
            rwa [← his1] at hp_old
          exact hright_u i hi p hp_old'
      · rw [(hsib_congr (i + 1) (by omega) his1).2.1] at hp
        exact hright_u i hi p hp
  have hsub_u'' : readNodeSet (l + 1) base t mem' u ⊆
      readNodeSet (l + 1) base t mem u ∪ Finset.Ico cnt cnt' := by
    intro x hx
    rw [mem_readNodeSet_succ, hnk_u'] at hx
    rcases hx with rfl | ⟨j, hj, hx⟩
    · exact Finset.mem_union_left _ (self_mem_readNodeSet _ _ _ _ _)
    · rw [hcid_u' j hj] at hx
      by_cases hjs : j = slot
      · subst hjs
        rcases Finset.mem_union.mp (hsub_c' hx) with hxc | hxico
        · exact Finset.mem_union_left _
            (child_subset_readNodeSet l base t mem u j hslot_lt1 hxc)
        · exact Finset.mem_union_right _ hxico
      · rw [(hsib_congr j hj hjs).2.2.1] at hx
        exact Finset.mem_union_left _ (child_subset_readNodeSet l base t mem u j hj hx)
  refine ⟨hv_u'', hs_u'', hnk_u', hsub_u'', ?_⟩
  have hsort_old := hs_u.isSortedAssoc
  have hsort_c_old := (hcs_u slot hslot_lt1).isSortedAssoc
  apply hs_u''.isSortedAssoc.eq_of_forall_mem_iff
    (Cslib.SortedAssoc.isSortedAssoc_insert hsort_old)
  intro p
  rw [Cslib.SortedAssoc.mem_insert_iff hsort_old, mem_toList_readTree_succ,
    mem_toList_readTree_succ, hnk_u']
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩)
    · rw [hkey_u' i hi, hval_u' i hi]
      refine Or.inr ⟨Or.inl ⟨i, hi, rfl⟩, ?_⟩
      rcases lt_or_ge i slot with hi_lt | hi_ge
      · exact (hlt i hi_lt).ne
      · exact (hgt i hi_ge hi).ne'
    · rw [hcid_u' j hj] at hpj
      by_cases hjs : j = slot
      · subst hjs
        rw [htr_c', Cslib.SortedAssoc.mem_insert_iff hsort_c_old] at hpj
        rcases hpj with rfl | ⟨hp_old, hne_k⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Or.inr ⟨j, hslot_lt1, hp_old⟩, hne_k⟩
      · rw [(hsib_congr j hj hjs).2.1] at hpj
        refine Or.inr ⟨Or.inr ⟨j, hj, hpj⟩, ?_⟩
        rcases lt_or_gt_of_ne hjs with hj_lt | hj_gt
        · exact ((hs_u.child_lt_key (by omega) (by omega) hpj).trans (hlt j hj_lt)).ne
        · exact (lt_trans (hgt slot le_rfl (by omega))
            (hs_u.key_lt_child (by omega) (by omega) hj hpj)).ne'
  · rintro (rfl | ⟨⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩, hne_k⟩)
    · refine Or.inr ⟨slot, hslot_lt1, ?_⟩
      rw [hcid_u' slot hslot_lt1, htr_c']
      exact Cslib.SortedAssoc.mem_insert_self
    · exact Or.inl ⟨i, hi, by rw [hkey_u' i hi, hval_u' i hi]⟩
    · refine Or.inr ⟨j, hj, ?_⟩
      rw [hcid_u' j hj]
      by_cases hjs : j = slot
      · subst hjs
        rw [htr_c', Cslib.SortedAssoc.mem_insert_iff hsort_c_old]
        exact Or.inr ⟨hpj, hne_k⟩
      · rwa [(hsib_congr j hj hjs).2.1]

end Cslib.DataStructure.BTree.WordRAM
