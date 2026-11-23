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
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · left
    have hmul : (u + 1) * nodeStride t ≤ v * nodeStride t := Nat.mul_le_mul_right _ hlt
    simp only [nodeAddr, Nat.add_mul, Nat.one_mul] at hmul ⊢
    omega
  · right
    have hmul : (v + 1) * nodeStride t ≤ u * nodeStride t := Nat.mul_le_mul_right _ hgt
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
  cases l with
  | zero => exact hv.1
  | succ l => exact hv.1

theorem ValidNode.numKeys_pos {l base t : ℕ} {mem : ℕ → ℕ} {u : ℕ}
    (hv : ValidNode l base t mem u) : 1 ≤ numKeys base t mem u := by
  cases l with
  | zero => exact hv.2.1
  | succ l => exact hv.2.1

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

/-- Disjoint-node framing: if `mem'` agrees with `mem` on every node in
`readNodeSet l base t mem u`, then `ValidNode`, `readTree`, and `readNodeSet` are preserved. -/
theorem ValidNode.congr_mem {l base t : ℕ} {mem mem' : ℕ → ℕ} {u : ℕ}
    (ht : 1 ≤ t) (hv : ValidNode l base t mem u)
    (hmem : ∀ v ∈ readNodeSet l base t mem u, ∀ o < nodeStride t,
      mem' (nodeAddr base t v + o) = mem (nodeAddr base t v + o)) :
    ValidNode l base t mem' u ∧
      readTree l base t mem' u = readTree l base t mem u ∧
      readNodeSet l base t mem' u = readNodeSet l base t mem u := by
  induction l generalizing u with
  | zero =>
    obtain ⟨hlf, hm₁, hm₂⟩ := hv
    have hu : u ∈ readNodeSet 0 base t mem u := self_mem_readNodeSet 0 base t mem u
    have hlf' : leafFlag base t mem' u = leafFlag base t mem u :=
      hmem u hu 0 (by simp only [nodeStride]; omega)
    have hm' : numKeys base t mem' u = numKeys base t mem u :=
      hmem u hu 1 (by simp only [nodeStride]; omega)
    refine ⟨⟨hlf'.trans hlf, hm' ▸ hm₁, hm' ▸ hm₂⟩, ?_, rfl⟩
    simp only [readTree]
    congr 1
    refine List.ext_getElem (by simp only [List.length_ofFn, hm']) fun i h₁ h₂ => ?_
    simp only [List.length_ofFn, hm'] at h₁
    simp only [List.getElem_ofFn]
    have hk : keyAt base t mem' u i = keyAt base t mem u i := by
      simpa only [keyAt, Nat.add_assoc] using
        hmem u hu (2 + i) (by simp only [nodeStride]; omega)
    have hval : valAt base t mem' u i = valAt base t mem u i := by
      simpa only [valAt, Nat.add_assoc] using
        hmem u hu (2 * t + 1 + i) (by simp only [nodeStride]; omega)
    simp only [hk, hval]
  | succ l ih =>
    obtain ⟨hlf, hm₁, hm₂, hch, hdisj⟩ := hv
    have hu : u ∈ readNodeSet (l + 1) base t mem u := self_mem_readNodeSet (l + 1) base t mem u
    have hlf' : leafFlag base t mem' u = leafFlag base t mem u :=
      hmem u hu 0 (by simp only [nodeStride]; omega)
    have hm' : numKeys base t mem' u = numKeys base t mem u :=
      hmem u hu 1 (by simp only [nodeStride]; omega)
    set m := numKeys base t mem u
    have hcid : ∀ j < m + 1, childAt base t mem' u j = childAt base t mem u j := fun j hj => by
      simpa only [childAt, Nat.add_assoc] using
        hmem u hu (4 * t + j) (by simp only [nodeStride]; omega)
    have hsub : ∀ j (hj : j < m + 1),
        ValidNode l base t mem' (childAt base t mem u j) ∧
          readTree l base t mem' (childAt base t mem u j) =
            readTree l base t mem (childAt base t mem u j) ∧
          readNodeSet l base t mem' (childAt base t mem u j) =
            readNodeSet l base t mem (childAt base t mem u j) := fun j hj =>
      ih (hch j hj).1 fun v hv_in o ho =>
        hmem v (child_subset_readNodeSet l base t mem u j hj hv_in) o ho
    have hset_eq : readNodeSet (l + 1) base t mem' u = readNodeSet (l + 1) base t mem u := by
      ext x
      rw [readNodeSet, readNodeSet, hm']
      simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
      refine or_congr Iff.rfl ⟨?_, ?_⟩
      · rintro ⟨⟨j, hj⟩, hx⟩
        rw [hcid j hj, (hsub j hj).2.2] at hx
        exact ⟨⟨j, hj⟩, hx⟩
      · rintro ⟨⟨j, hj⟩, hx⟩
        refine ⟨⟨j, hj⟩, ?_⟩
        rw [hcid j hj, (hsub j hj).2.2]
        exact hx
    have htree_eq : readTree (l + 1) base t mem' u = readTree (l + 1) base t mem u := by
      simp only [readTree]
      have h0 : childAt base t mem' u 0 = childAt base t mem u 0 := hcid 0 (by omega)
      rw [h0, (hsub 0 (by omega)).2.1]
      congr 1
      refine List.ext_getElem (by simp only [List.length_ofFn, hm']; rfl) fun i h₁ h₂ => ?_
      simp only [List.length_ofFn, hm'] at h₁
      simp only [List.getElem_ofFn]
      have hk : keyAt base t mem' u i = keyAt base t mem u i := by
        simpa only [keyAt, Nat.add_assoc] using
          hmem u hu (2 + i) (by simp only [nodeStride]; omega)
      have hval : valAt base t mem' u i = valAt base t mem u i := by
        simpa only [valAt, Nat.add_assoc] using
          hmem u hu (2 * t + 1 + i) (by simp only [nodeStride]; omega)
      have hc1 : childAt base t mem' u (i + 1) = childAt base t mem u (i + 1) :=
        hcid (i + 1) (by omega)
      rw [hk, hval, hc1, (hsub (i + 1) (by omega)).2.1]
    have hv' : ValidNode (l + 1) base t mem' u := by
      simp only [ValidNode, hm']
      refine ⟨hlf'.trans hlf, hm₁, hm₂, ?_, ?_⟩
      · intro j hj
        rw [hcid j hj, (hsub j hj).2.2]
        have hc_self := self_mem_readNodeSet l base t mem (childAt base t mem u j)
        have hm_c : numKeys base t mem' (childAt base t mem u j) =
            numKeys base t mem (childAt base t mem u j) :=
          hmem _ (child_subset_readNodeSet l base t mem u j hj hc_self) 1
            (by simp only [nodeStride]; omega)
        exact ⟨(hsub j hj).1, hm_c ▸ (hch j hj).2.1, (hch j hj).2.2⟩
      · intro j₁ j₂ hj₁ hj₂ hne
        rw [hcid j₁ hj₁, hcid j₂ hj₂, (hsub j₁ hj₁).2.2, (hsub j₂ hj₂).2.2]
        exact hdisj j₁ j₂ hj₁ hj₂ hne
    exact ⟨hv', htree_eq, hset_eq⟩

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
  simp only [readTree, BTree.toList_node, BTree.toList_leaf, List.nil_append]
  have hmap :
      (List.ofFn fun i : Fin (numKeys base t mem u) =>
          (keyAt base t mem u i.val, valAt base t mem u i.val, (BTree.leaf : BTree ℕ ℕ))) =
        (List.ofFn fun i : Fin (numKeys base t mem u) =>
          (keyAt base t mem u i.val, valAt base t mem u i.val)).map
          (fun p => (p.1, p.2, (BTree.leaf : BTree ℕ ℕ))) := by
    simp only [List.map_ofFn]
    rfl
  rw [hmap, BTree.toListRest_map_leaf]

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

theorem SortedNode.congr_mem {l base t : ℕ} {mem mem' : ℕ → ℕ} {u : ℕ}
    (ht : 1 ≤ t) (hv : ValidNode l base t mem u) (hs : SortedNode l base t mem u)
    (hmem : ∀ v ∈ readNodeSet l base t mem u, ∀ o < nodeStride t,
      mem' (nodeAddr base t v + o) = mem (nodeAddr base t v + o)) :
    SortedNode l base t mem' u := by
  induction l generalizing u with
  | zero =>
    have hu := self_mem_readNodeSet 0 base t mem u
    have hm : numKeys base t mem' u = numKeys base t mem u :=
      hmem u hu 1 (by simp only [nodeStride]; omega)
    have hm_le := hv.numKeys_le
    intro i₁ i₂ h12 h2
    rw [hm] at h2
    have hk₁ : keyAt base t mem' u i₁ = keyAt base t mem u i₁ := by
      simpa only [keyAt, Nat.add_assoc] using hmem u hu (2 + i₁) (by simp only [nodeStride]; omega)
    have hk₂ : keyAt base t mem' u i₂ = keyAt base t mem u i₂ := by
      simpa only [keyAt, Nat.add_assoc] using hmem u hu (2 + i₂) (by simp only [nodeStride]; omega)
    rw [hk₁, hk₂]
    exact hs i₁ i₂ h12 h2
  | succ l ih =>
    obtain ⟨_, _, hm_le, hch, _⟩ := hv
    obtain ⟨hkeys, hcs, hleft, hright⟩ := hs
    have hu := self_mem_readNodeSet (l + 1) base t mem u
    have hm : numKeys base t mem' u = numKeys base t mem u :=
      hmem u hu 1 (by simp only [nodeStride]; omega)
    set m := numKeys base t mem u
    have hcid : ∀ j < m + 1, childAt base t mem' u j = childAt base t mem u j := fun j hj => by
      simpa only [childAt, Nat.add_assoc] using
        hmem u hu (4 * t + j) (by simp only [nodeStride]; omega)
    have hk : ∀ i < m, keyAt base t mem' u i = keyAt base t mem u i := fun i hi => by
      simpa only [keyAt, Nat.add_assoc] using
        hmem u hu (2 + i) (by simp only [nodeStride]; omega)
    have htree_c : ∀ j (hj : j < m + 1),
        readTree l base t mem' (childAt base t mem u j) =
          readTree l base t mem (childAt base t mem u j) := fun j hj =>
      ((hch j hj).1.congr_mem ht fun v hv_in o ho =>
        hmem v (child_subset_readNodeSet l base t mem u j hj hv_in) o ho).2.1
    simp only [SortedNode, hm]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i₁ i₂ h12 h2
      rw [hk i₁ (by omega), hk i₂ h2]
      exact hkeys i₁ i₂ h12 h2
    · intro j hj
      rw [hcid j hj]
      exact ih (hch j hj).1 (hcs j hj) fun v hv_in o ho =>
        hmem v (child_subset_readNodeSet l base t mem u j hj hv_in) o ho
    · intro i hi p hp
      rw [hcid i (by omega), htree_c i (by omega)] at hp
      rw [hk i hi]
      exact hleft i hi p hp
    · intro i hi p hp
      rw [hcid (i + 1) (by omega), htree_c (i + 1) (by omega)] at hp
      rw [hk i hi]
      exact hright i hi p hp

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
  have hsnoc : (List.ofFn fun i : Fin (n + 1) => f i.val) =
      (List.ofFn fun i : Fin n => f i.val) ++ [f n] := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp only [List.getElem_ofFn]
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ (by simpa using h₁)) with hlt | rfl
      · rw [List.getElem_append_left (by simpa using hlt)]
        simp
      · rw [List.getElem_append_right (by simp)]
        simp
  rw [hsnoc, BTree.toListRest_append]
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
  | zero =>
    rw [mem_toList_readTree_zero]
    exact ⟨slot, hslot, rfl⟩
  | succ l =>
    rw [mem_toList_readTree_succ]
    exact Or.inl ⟨slot, hslot, rfl⟩

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
  have hlf : leafFlag base t mem' 0 = 1 := by
    simp only [leafFlag, mem', memInitSingle, Function.update_apply]
    have := base_lt_nodeAddr base t 0 0
    split_ifs <;> omega
  have hnk : numKeys base t mem' 0 = 1 := by
    simp only [numKeys, mem', memInitSingle, Function.update_apply]
    have := base_lt_nodeAddr base t 0 1
    split_ifs <;> omega
  have hk0 : keyAt base t mem' 0 0 = k := by
    simp only [keyAt, mem', memInitSingle, Function.update_apply]
    have := base_lt_nodeAddr base t 0 2
    split_ifs <;> omega
  have hv0 : valAt base t mem' 0 0 = v := by
    simp only [valAt, mem', memInitSingle, Function.update_apply]
    have := base_lt_nodeAddr base t 0 (2 * t + 1)
    split_ifs <;> omega
  refine ⟨?_, ?_, ⟨hlf, by omega, by omega⟩, ?_, ?_, rfl⟩
  · simp only [mem', memInitSingle, Function.update_apply]
    split_ifs <;> omega
  · simp only [mem', memInitSingle, Function.update_self]
  · intro i₁ i₂ h12 h2
    rw [hnk] at h2
    omega
  · rw [toList_readTree_zero]
    apply List.ext_getElem
    · simp [hnk]
    · intro i hi₁ hi₂
      simp only [List.length_ofFn, hnk] at hi₁
      have hi0 : i = 0 := by omega
      subst hi0
      simp [hk0, hv0]

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
  have hoff_lt : 2 * t + 1 + slot < nodeStride t := by omega
  have hlf' : leafFlag base t mem' u = leafFlag base t mem u := by
    simp only [leafFlag, mem', memOverwriteVal]
    rw [Function.update_of_ne (by omega)]
  have hnk' : numKeys base t mem' u = numKeys base t mem u := by
    simp only [numKeys, mem', memOverwriteVal]
    rw [Function.update_of_ne (by omega)]
  have hkey' : ∀ i < numKeys base t mem u, keyAt base t mem' u i = keyAt base t mem u i :=
    fun i hi => by
      simp only [keyAt, mem', memOverwriteVal]
      rw [Function.update_of_ne (by omega)]
  have hval_self : valAt base t mem' u slot = v := by
    simp only [valAt, mem', memOverwriteVal, Function.update_self]
  have hval_ne : ∀ i < numKeys base t mem u, i ≠ slot →
      valAt base t mem' u i = valAt base t mem u i := fun i _ hne => by
    simp only [valAt, mem', memOverwriteVal]
    rw [Function.update_of_ne (by omega)]
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
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [hkey' i hi]
      by_cases his : i = slot
      · subst his
        rw [hk_eq, hval_self]
        exact Or.inl rfl
      · rw [hval_ne i hi his]
        refine Or.inr ⟨⟨i, hi, rfl⟩, ?_⟩
        rcases lt_or_gt_of_ne his with hlt | hgt
        · exact (hk_eq ▸ hs_u i slot hlt hslot).ne
        · exact (hk_eq ▸ hs_u slot i hgt hi).ne'
    · rintro (rfl | ⟨⟨i, hi, rfl⟩, hne⟩)
      · exact ⟨slot, hslot, by rw [hkey' slot hslot, hk_eq, hval_self]⟩
      · have his : i ≠ slot := fun heq => hne (heq ▸ hk_eq)
        exact ⟨i, hi, by rw [hkey' i hi, hval_ne i hi his]⟩
  | succ l =>
    have ⟨hlf, hm₁, hm₂, hch, hdisj⟩ := hv_u
    have ⟨hkeys, hcs, hleft, hright⟩ := hs_u
    set m := numKeys base t mem u
    have hcid' : ∀ j < m + 1, childAt base t mem' u j = childAt base t mem u j := fun j hj => by
      simp only [childAt, mem', memOverwriteVal]
      rw [Function.update_of_ne (by omega)]
    have hchild_congr : ∀ j (hj : j < m + 1),
        ValidNode l base t mem' (childAt base t mem u j) ∧
          readTree l base t mem' (childAt base t mem u j) =
            readTree l base t mem (childAt base t mem u j) ∧
          readNodeSet l base t mem' (childAt base t mem u j) =
            readNodeSet l base t mem (childAt base t mem u j) ∧
          SortedNode l base t mem' (childAt base t mem u j) := fun j hj => by
      have hframe : ∀ w_id ∈ readNodeSet l base t mem (childAt base t mem u j),
          ∀ o < nodeStride t, mem' (nodeAddr base t w_id + o) = mem (nodeAddr base t w_id + o) := by
        intro w_id hw_in o ho
        have hne_u : w_id ≠ u := fun heq => (hch j hj).2.2 (by rw [heq] at hw_in; exact hw_in)
        have hsep := nodeAddr_sep base t hne_u
        simp only [mem', memOverwriteVal]
        rw [Function.update_of_ne (by omega)]
      obtain ⟨hv_c, htr_c, hset_c⟩ := (hch j hj).1.congr_mem (by omega) hframe
      exact ⟨hv_c, htr_c, hset_c, (hcs j hj).congr_mem (by omega) (hch j hj).1 hframe⟩
    have hv' : ValidNode (l + 1) base t mem' u := by
      simp only [ValidNode, hnk']
      refine ⟨hlf'.trans hlf, hm₁, hm₂, ?_, ?_⟩
      · intro j hj
        rw [hcid' j hj, (hchild_congr j hj).2.2.1]
        have hne_u : childAt base t mem u j ≠ u := fun heq =>
          (hch j hj).2.2
            (Eq.ndrec (motive := fun x => x ∈ readNodeSet l base t mem (childAt base t mem u j))
              (self_mem_readNodeSet l base t mem (childAt base t mem u j)) heq)
        have hsep := nodeAddr_sep base t hne_u
        have hnk_c : numKeys base t mem' (childAt base t mem u j) =
            numKeys base t mem (childAt base t mem u j) := by
          simp only [numKeys, mem', memOverwriteVal]
          rw [Function.update_of_ne (by omega)]
        exact ⟨(hchild_congr j hj).1, hnk_c ▸ (hch j hj).2.1, (hch j hj).2.2⟩
      · intro j₁ j₂ hj₁ hj₂ hne
        rw [hcid' j₁ hj₁, hcid' j₂ hj₂, (hchild_congr j₁ hj₁).2.2.1, (hchild_congr j₂ hj₂).2.2.1]
        exact hdisj j₁ j₂ hj₁ hj₂ hne
    have hs' : SortedNode (l + 1) base t mem' u := by
      simp only [SortedNode, hnk']
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i₁ i₂ h12 h2
        rw [hkey' i₁ (by omega), hkey' i₂ h2]
        exact hkeys i₁ i₂ h12 h2
      · intro j hj
        rw [hcid' j hj]
        exact (hchild_congr j hj).2.2.2
      · intro i hi p hp
        rw [hcid' i (by omega), (hchild_congr i (by omega)).2.1] at hp
        rw [hkey' i hi]
        exact hleft i hi p hp
      · intro i hi p hp
        rw [hcid' (i + 1) (by omega), (hchild_congr (i + 1) (by omega)).2.1] at hp
        rw [hkey' i hi]
        exact hright i hi p hp
    have hset_eq : readNodeSet (l + 1) base t mem' u = readNodeSet (l + 1) base t mem u := by
      ext x
      rw [readNodeSet, readNodeSet, hnk']
      simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
      refine or_congr Iff.rfl ⟨?_, ?_⟩
      · rintro ⟨⟨j, hj⟩, hx⟩
        rw [hcid' j hj, (hchild_congr j hj).2.2.1] at hx
        exact ⟨⟨j, hj⟩, hx⟩
      · rintro ⟨⟨j, hj⟩, hx⟩
        refine ⟨⟨j, hj⟩, ?_⟩
        rw [hcid' j hj, (hchild_congr j hj).2.2.1]
        exact hx
    refine ⟨hv', hs', hset_eq, ?_⟩
    have hsort_old := hs_u.isSortedAssoc
    apply hs'.isSortedAssoc.eq_of_forall_mem_iff (Cslib.SortedAssoc.isSortedAssoc_insert hsort_old)
    intro p
    rw [Cslib.SortedAssoc.mem_insert_iff hsort_old, mem_toList_readTree_succ,
      mem_toList_readTree_succ, hnk']
    constructor
    · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩)
      · rw [hkey' i hi]
        by_cases his : i = slot
        · subst his
          rw [hk_eq, hval_self]
          exact Or.inl rfl
        · rw [hval_ne i hi his]
          refine Or.inr ⟨Or.inl ⟨i, hi, rfl⟩, ?_⟩
          rcases lt_or_gt_of_ne his with hlt | hgt
          · exact (hk_eq ▸ hkeys i slot hlt hslot).ne
          · exact (hk_eq ▸ hkeys slot i hgt hi).ne'
      · rw [hcid' j hj, (hchild_congr j hj).2.1] at hpj
        refine Or.inr ⟨Or.inr ⟨j, hj, hpj⟩, ?_⟩
        rcases le_or_gt j slot with hj_le | hj_gt
        · exact (hk_eq ▸ hs_u.child_lt_key hj_le hslot hpj).ne
        · exact (hk_eq ▸ hs_u.key_lt_child hslot (by omega) hj hpj).ne'
    · rintro (rfl | ⟨⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩, hne⟩)
      · exact Or.inl ⟨slot, hslot, by rw [hkey' slot hslot, hk_eq, hval_self]⟩
      · have his : i ≠ slot := fun heq => hne (heq ▸ hk_eq)
        exact Or.inl ⟨i, hi, by rw [hkey' i hi, hval_ne i hi his]⟩
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
  set au := nodeAddr base t u
  have hlf' : leafFlag base t mem' u = 1 := by
    have hlf0 : mem au = 1 := hv_u.1
    simp only [leafFlag, mem', memInsertLeaf]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega), hlf0]
  have hnk' : numKeys base t mem' u = m + 1 := by
    simp only [numKeys, mem', memInsertLeaf, Function.update_self]
  have hkv' : ∀ i < m + 1,
      (keyAt base t mem' u i, valAt base t mem' u i) =
        if i < slot then (keyAt base t mem u i, valAt base t mem u i)
        else if i = slot then (k, v)
        else (keyAt base t mem u (i - 1), valAt base t mem u (i - 1)) := by
    intro i hi
    rcases lt_trichotomy i slot with hi_lt | hi_eq | hi_gt
    · simp only [hi_lt, ↓reduceIte]
      apply Prod.ext
      · simp only [keyAt, mem', memInsertLeaf]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
      · simp only [valAt, mem', memInsertLeaf]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
    · subst hi_eq
      simp only [lt_irrefl, ↓reduceIte]
      apply Prod.ext
      · simp only [keyAt, mem', memInsertLeaf]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self]
      · simp only [valAt, mem', memInsertLeaf]
        rw [Function.update_of_ne (by omega), Function.update_self]
    · have hnlt : ¬ i < slot := by omega
      have hne : i ≠ slot := by omega
      simp only [hnlt, hne, ↓reduceIte]
      apply Prod.ext
      · simp only [keyAt, mem', memInsertLeaf]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
          shiftArrRight_shifted (au + 2) m (m - slot) mem (by omega) i (by omega) (by omega)]
      · simp only [valAt, mem', memInsertLeaf]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega),
          shiftArrRight_shifted (au + (2 * t + 1)) m (m - slot) _ (by omega) i
            (by omega) (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
  have hv' : ValidNode 0 base t mem' u := ⟨hlf', by rw [hnk']; omega, by rw [hnk']; omega⟩
  have hs' : SortedNode 0 base t mem' u := by
    intro i₁ i₂ h12 h2
    rw [hnk'] at h2
    have h1 := congrArg Prod.fst (hkv' i₁ (by omega))
    have h2' := congrArg Prod.fst (hkv' i₂ h2)
    dsimp only at h1 h2'
    rw [h1, h2']
    rcases lt_trichotomy i₁ slot with h1_lt | h1_eq | h1_gt <;>
      rcases lt_trichotomy i₂ slot with h2_lt | h2_eq | h2_gt
    · simp only [h1_lt, h2_lt, ↓reduceIte]; exact hs_u i₁ i₂ h12 (by omega)
    · subst h2_eq; simp only [h1_lt, lt_irrefl, ↓reduceIte]; exact hlt i₁ h1_lt
    · have hn2 : ¬ i₂ < slot := by omega
      have he2 : i₂ ≠ slot := by omega
      simp only [h1_lt, hn2, he2, ↓reduceIte]
      exact (hlt i₁ h1_lt).trans (hgt (i₂ - 1) (by omega) (by omega))
    · omega
    · omega
    · subst h1_eq
      have hn2 : ¬ i₂ < i₁ := by omega
      have he2 : i₂ ≠ i₁ := by omega
      simp only [lt_irrefl, hn2, he2, ↓reduceIte]
      exact hgt (i₂ - 1) (by omega) (by omega)
    · omega
    · omega
    · have hn1 : ¬ i₁ < slot := by omega
      have he1 : i₁ ≠ slot := by omega
      have hn2 : ¬ i₂ < slot := by omega
      have he2 : i₂ ≠ slot := by omega
      simp only [hn1, he1, hn2, he2, ↓reduceIte]
      exact hs_u (i₁ - 1) (i₂ - 1) (by omega) (by omega)
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
    · rcases lt_or_ge i slot with hi_lt | hi_ge
      · refine ⟨i, by omega, ?_⟩
        simpa only [hi_lt, ↓reduceIte] using (hkv' i (by omega)).symm
      · refine ⟨i + 1, by omega, ?_⟩
        have hn : ¬ i + 1 < slot := by omega
        have he : i + 1 ≠ slot := by omega
        simpa only [hn, he, ↓reduceIte, Nat.add_sub_cancel] using (hkv' (i + 1) (by omega)).symm

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
  dsimp only [memCopyUpper]
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega)]
  have hm3 : (if mem (nodeAddr base t c) = 0 then
      ArrayCopy.copyPrefix
        (ArrayCopy.copyPrefix
          (ArrayCopy.copyPrefix mem (nodeAddr base t c + 2 + t) (nodeAddr base t z + 2) (t - 1))
          (nodeAddr base t c + (2 * t + 1) + t) (nodeAddr base t z + (2 * t + 1)) (t - 1))
        (nodeAddr base t c + 4 * t + t) (nodeAddr base t z + 4 * t) t
      else
        ArrayCopy.copyPrefix
          (ArrayCopy.copyPrefix mem (nodeAddr base t c + 2 + t) (nodeAddr base t z + 2) (t - 1))
          (nodeAddr base t c + (2 * t + 1) + t) (nodeAddr base t z + (2 * t + 1)) (t - 1)) a =
      ArrayCopy.copyPrefix
        (ArrayCopy.copyPrefix mem (nodeAddr base t c + 2 + t) (nodeAddr base t z + 2) (t - 1))
        (nodeAddr base t c + (2 * t + 1) + t) (nodeAddr base t z + (2 * t + 1)) (t - 1) a := by
    split_ifs with h0
    · exact ArrayCopy.copyPrefix_outside (by omega)
    · rfl
  rw [hm3, ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega)]

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
  let ac := nodeAddr base t c
  let az := nodeAddr base t z
  have hcz : c ≠ z := fun heq => hz_fresh (heq ▸ self_mem_readNodeSet l base t mem c)
  have hst : nodeStride t = 6 * t := rfl
  have hac_az_sep : nodeAddr base t c + 6 * t ≤ nodeAddr base t z ∨
      nodeAddr base t z + 6 * t ≤ nodeAddr base t c := by
    rcases lt_or_gt_of_ne hcz with hlt | hgt
    · left
      have hmul : (c + 1) * (6 * t) ≤ z * (6 * t) := Nat.mul_le_mul_right _ hlt
      simp only [nodeAddr, nodeStride, Nat.add_mul, Nat.one_mul] at hmul ⊢
      omega
    · right
      have hmul : (z + 1) * (6 * t) ≤ c * (6 * t) := Nat.mul_le_mul_right _ hgt
      simp only [nodeAddr, nodeStride, Nat.add_mul, Nat.one_mul] at hmul ⊢
      omega
  -- Field readbacks on `c` in `mem₁`:
  have hlf_c : leafFlag base t mem₁ c = leafFlag base t mem c := by
    simp only [leafFlag, mem₁, memCopyUpper]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    split_ifs
    · rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega),
        ArrayCopy.copyPrefix_outside (by omega)]
    · rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega)]
  have hnk_c : numKeys base t mem₁ c = t - 1 := by
    simp only [numKeys, mem₁, memCopyUpper, Function.update_self]
  have hkey_c : ∀ i < t - 1, keyAt base t mem₁ c i = keyAt base t mem c i := fun i hi => by
    simp only [keyAt, mem₁, memCopyUpper]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    split_ifs
    · rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega),
        ArrayCopy.copyPrefix_outside (by omega)]
    · rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega)]
  have hval_c : ∀ i < t - 1, valAt base t mem₁ c i = valAt base t mem c i := fun i hi => by
    simp only [valAt, mem₁, memCopyUpper]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    split_ifs
    · rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega),
        ArrayCopy.copyPrefix_outside (by omega)]
    · rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega)]
  -- Field readbacks on `z` in `mem₁`:
  have hlf_z : leafFlag base t mem₁ z = leafFlag base t mem c := by
    simp only [leafFlag, mem₁, memCopyUpper]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  have hnk_z : numKeys base t mem₁ z = t - 1 := by
    simp only [numKeys, mem₁, memCopyUpper]
    rw [Function.update_of_ne (by omega), Function.update_self]
  have hkey_z : ∀ i < t - 1, keyAt base t mem₁ z i = keyAt base t mem c (t + i) := fun i hi => by
    simp only [keyAt, mem₁, memCopyUpper]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    have hm3 : (if mem ac = 0 then
        ArrayCopy.copyPrefix
          (ArrayCopy.copyPrefix
            (ArrayCopy.copyPrefix mem (ac + 2 + t) (az + 2) (t - 1))
            (ac + (2 * t + 1) + t) (az + (2 * t + 1)) (t - 1))
          (ac + 4 * t + t) (az + 4 * t) t
        else
          ArrayCopy.copyPrefix
            (ArrayCopy.copyPrefix mem (ac + 2 + t) (az + 2) (t - 1))
            (ac + (2 * t + 1) + t) (az + (2 * t + 1)) (t - 1)) (az + 2 + i) =
        ArrayCopy.copyPrefix
          (ArrayCopy.copyPrefix mem (ac + 2 + t) (az + 2) (t - 1))
          (ac + (2 * t + 1) + t) (az + (2 * t + 1)) (t - 1) (az + 2 + i) := by
      split_ifs
      · exact ArrayCopy.copyPrefix_outside (by omega)
      · rfl
    dsimp only [ac, az] at hm3
    rw [hm3, ArrayCopy.copyPrefix_outside (by omega)]
    have hcopy := ArrayCopy.copyPrefix_read (mem := mem)
      (src := nodeAddr base t c + 2 + t) (dst := nodeAddr base t z + 2) (k := t - 1) hi
    simpa only [Nat.add_assoc] using hcopy
  have hval_z : ∀ i < t - 1, valAt base t mem₁ z i = valAt base t mem c (t + i) := fun i hi => by
    simp only [valAt, mem₁, memCopyUpper]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    have hm3 : (if mem ac = 0 then
        ArrayCopy.copyPrefix
          (ArrayCopy.copyPrefix
            (ArrayCopy.copyPrefix mem (ac + 2 + t) (az + 2) (t - 1))
            (ac + (2 * t + 1) + t) (az + (2 * t + 1)) (t - 1))
          (ac + 4 * t + t) (az + 4 * t) t
        else
          ArrayCopy.copyPrefix
            (ArrayCopy.copyPrefix mem (ac + 2 + t) (az + 2) (t - 1))
            (ac + (2 * t + 1) + t) (az + (2 * t + 1)) (t - 1)) (az + (2 * t + 1) + i) =
        ArrayCopy.copyPrefix
          (ArrayCopy.copyPrefix mem (ac + 2 + t) (az + 2) (t - 1))
          (ac + (2 * t + 1) + t) (az + (2 * t + 1)) (t - 1) (az + (2 * t + 1) + i) := by
      split_ifs
      · exact ArrayCopy.copyPrefix_outside (by omega)
      · rfl
    dsimp only [ac, az] at hm3
    rw [hm3]
    have hcopy := ArrayCopy.copyPrefix_read
      (mem := ArrayCopy.copyPrefix mem (nodeAddr base t c + 2 + t) (nodeAddr base t z + 2) (t - 1))
      (src := nodeAddr base t c + (2 * t + 1) + t) (dst := nodeAddr base t z + (2 * t + 1))
      (k := t - 1) hi
    have hout : ArrayCopy.copyPrefix mem (nodeAddr base t c + 2 + t) (nodeAddr base t z + 2) (t - 1)
        (nodeAddr base t c + (2 * t + 1) + t + i) =
        mem (nodeAddr base t c + (2 * t + 1) + t + i) :=
      ArrayCopy.copyPrefix_outside (by omega)
    simpa only [Nat.add_assoc] using hcopy.trans hout
  cases l with
  | zero =>
    have hv_c' : ValidNode 0 base t mem₁ c :=
      ⟨hlf_c.trans hv_c.1, by rw [hnk_c]; omega, by rw [hnk_c]; omega⟩
    have hv_z' : ValidNode 0 base t mem₁ z :=
      ⟨hlf_z.trans hv_c.1, by rw [hnk_z]; omega, by rw [hnk_z]; omega⟩
    have hs_c' : SortedNode 0 base t mem₁ c := by
      intro i₁ i₂ h12 h2
      rw [hnk_c] at h2
      rw [hkey_c i₁ (by omega), hkey_c i₂ h2]
      exact hs_c i₁ i₂ h12 (by omega)
    have hs_z' : SortedNode 0 base t mem₁ z := by
      intro i₁ i₂ h12 h2
      rw [hnk_z] at h2
      rw [hkey_z i₁ (by omega), hkey_z i₂ h2]
      exact hs_c (t + i₁) (t + i₂) (by omega) (by omega)
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
      exact hs_c (t - 1) (t + i) (by omega) (by omega)
    · intro p
      rw [mem_toList_readTree_zero, mem_toList_readTree_zero, mem_toList_readTree_zero,
        hfull, hnk_c, hnk_z]
      constructor
      · rintro ⟨i, hi, rfl⟩
        rcases lt_trichotomy i (t - 1) with hlt | rfl | hgt
        · exact Or.inl ⟨i, hlt, by rw [hkey_c i hlt, hval_c i hlt]⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr ⟨i - t, by omega, by
            have heq : t + (i - t) = i := by omega
            rw [hkey_z (i - t) (by omega), hval_z (i - t) (by omega), heq]⟩)
      · rintro (⟨i, hi, rfl⟩ | rfl | ⟨i, hi, rfl⟩)
        · exact ⟨i, by omega, by rw [hkey_c i hi, hval_c i hi]⟩
        · exact ⟨t - 1, by omega, rfl⟩
        · exact ⟨t + i, by omega, by rw [hkey_z i hi, hval_z i hi]⟩
  | succ l =>
    have ⟨hlf0, _, _, hch, hdisj⟩ := hv_c
    have ⟨hkeys, hcs, hleft, hright⟩ := hs_c
    have hcid_c : ∀ j < t, childAt base t mem₁ c j = childAt base t mem c j := fun j hj => by
      simp only [childAt, mem₁, memCopyUpper]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      split_ifs
      · rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega),
          ArrayCopy.copyPrefix_outside (by omega)]
      · rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega)]
    have hcid_z : ∀ j < t, childAt base t mem₁ z j = childAt base t mem c (t + j) := fun j hj => by
      have hmem_ac0 : mem (nodeAddr base t c) = 0 := hlf0
      simp only [childAt, mem₁, memCopyUpper, hmem_ac0, ↓reduceIte]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      have hcopy := ArrayCopy.copyPrefix_read
        (mem := ArrayCopy.copyPrefix
          (ArrayCopy.copyPrefix mem (nodeAddr base t c + 2 + t) (nodeAddr base t z + 2) (t - 1))
          (nodeAddr base t c + (2 * t + 1) + t) (nodeAddr base t z + (2 * t + 1)) (t - 1))
        (src := nodeAddr base t c + 4 * t + t) (dst := nodeAddr base t z + 4 * t) (k := t) hj
      have hout1 : ArrayCopy.copyPrefix
          (ArrayCopy.copyPrefix mem (nodeAddr base t c + 2 + t) (nodeAddr base t z + 2) (t - 1))
          (nodeAddr base t c + (2 * t + 1) + t) (nodeAddr base t z + (2 * t + 1)) (t - 1)
          (nodeAddr base t c + 4 * t + t + j) =
          ArrayCopy.copyPrefix mem (nodeAddr base t c + 2 + t) (nodeAddr base t z + 2) (t - 1)
            (nodeAddr base t c + 4 * t + t + j) :=
        ArrayCopy.copyPrefix_outside (by omega)
      have hout2 : ArrayCopy.copyPrefix mem
          (nodeAddr base t c + 2 + t) (nodeAddr base t z + 2) (t - 1)
          (nodeAddr base t c + 4 * t + t + j) =
          mem (nodeAddr base t c + 4 * t + t + j) :=
        ArrayCopy.copyPrefix_outside (by omega)
      simpa only [Nat.add_assoc] using (hcopy.trans hout1).trans hout2
    -- Every child `0 .. 2*t - 1` of `c` is untouched in `mem₁`:
    have hchild_congr : ∀ j < 2 * t,
        let cid := childAt base t mem c j
        ValidNode l base t mem₁ cid ∧
          readTree l base t mem₁ cid = readTree l base t mem cid ∧
          readNodeSet l base t mem₁ cid = readNodeSet l base t mem cid ∧
          SortedNode l base t mem₁ cid ∧
          numKeys base t mem₁ cid = numKeys base t mem cid := by
      intro j hj
      have hj' : j < numKeys base t mem c + 1 := by omega
      set cid := childAt base t mem c j
      have hframe : ∀ w_id ∈ readNodeSet l base t mem cid, ∀ o < nodeStride t,
          mem₁ (nodeAddr base t w_id + o) = mem (nodeAddr base t w_id + o) := by
        intro w_id hw_in o ho
        have hne_c : w_id ≠ c := fun heq => (hch j hj').2.2 (by rw [heq] at hw_in; exact hw_in)
        have hne_z : w_id ≠ z := fun heq =>
          hz_fresh (child_subset_readNodeSet l base t mem c j hj'
            (by rw [heq] at hw_in; exact hw_in))
        have hsep_c := nodeAddr_sep base t hne_c
        have hsep_z := nodeAddr_sep base t hne_z
        exact memCopyUpper_outside ht mem _ (by omega) (by omega)
      obtain ⟨hvc, htrc, hsetc⟩ := (hch j hj').1.congr_mem (by omega) hframe
      have hsc := (hcs j hj').congr_mem (by omega) (hch j hj').1 hframe
      have hnkc := hframe cid (self_mem_readNodeSet l base t mem cid) 1
        (by simp only [nodeStride]; omega)
      exact ⟨hvc, htrc, hsetc, hsc, hnkc⟩
    have hv_c' : ValidNode (l + 1) base t mem₁ c := by
      simp only [ValidNode, hnk_c, show t - 1 + 1 = t by omega]
      refine ⟨hlf_c.trans hlf0, by omega, by omega, ?_, ?_⟩
      · intro j hj
        rw [hcid_c j hj]
        obtain ⟨hvc, _, hsetc, _, hnkc⟩ := hchild_congr j (by omega)
        rw [hsetc, hnkc]
        exact ⟨hvc, (hch j (by omega)).2.1, (hch j (by omega)).2.2⟩
      · intro j₁ j₂ hj₁ hj₂ hne
        rw [hcid_c j₁ hj₁, hcid_c j₂ hj₂,
          (hchild_congr j₁ (by omega)).2.2.1, (hchild_congr j₂ (by omega)).2.2.1]
        exact hdisj j₁ j₂ (by omega) (by omega) hne
    have hv_z' : ValidNode (l + 1) base t mem₁ z := by
      simp only [ValidNode, hnk_z, show t - 1 + 1 = t by omega]
      refine ⟨hlf_z.trans hlf0, by omega, by omega, ?_, ?_⟩
      · intro j hj
        rw [hcid_z j hj]
        obtain ⟨hvc, _, hsetc, _, hnkc⟩ := hchild_congr (t + j) (by omega)
        rw [hsetc, hnkc]
        refine ⟨hvc, (hch (t + j) (by omega)).2.1, fun hz_in => hz_fresh ?_⟩
        exact child_subset_readNodeSet l base t mem c (t + j) (by omega) hz_in
      · intro j₁ j₂ hj₁ hj₂ hne
        rw [hcid_z j₁ hj₁, hcid_z j₂ hj₂,
          (hchild_congr (t + j₁) (by omega)).2.2.1, (hchild_congr (t + j₂) (by omega)).2.2.1]
        exact hdisj (t + j₁) (t + j₂) (by omega) (by omega) (by omega)
    have hs_c' : SortedNode (l + 1) base t mem₁ c := by
      simp only [SortedNode, hnk_c, show t - 1 + 1 = t by omega]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i₁ i₂ h12 h2
        rw [hkey_c i₁ (by omega), hkey_c i₂ h2]
        exact hkeys i₁ i₂ h12 (by omega)
      · intro j hj
        rw [hcid_c j hj]
        exact (hchild_congr j (by omega)).2.2.2.1
      · intro i hi p hp
        rw [hcid_c i (by omega), (hchild_congr i (by omega)).2.1] at hp
        rw [hkey_c i hi]
        exact hleft i (by omega) p hp
      · intro i hi p hp
        rw [hcid_c (i + 1) (by omega), (hchild_congr (i + 1) (by omega)).2.1] at hp
        rw [hkey_c i hi]
        exact hright i (by omega) p hp
    have hs_z' : SortedNode (l + 1) base t mem₁ z := by
      simp only [SortedNode, hnk_z, show t - 1 + 1 = t by omega]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i₁ i₂ h12 h2
        rw [hkey_z i₁ (by omega), hkey_z i₂ h2]
        exact hkeys (t + i₁) (t + i₂) (by omega) (by omega)
      · intro j hj
        rw [hcid_z j hj]
        exact (hchild_congr (t + j) (by omega)).2.2.2.1
      · intro i hi p hp
        rw [hcid_z i (by omega), (hchild_congr (t + i) (by omega)).2.1] at hp
        rw [hkey_z i hi]
        exact hleft (t + i) (by omega) p hp
      · intro i hi p hp
        have heq_idx : t + (i + 1) = t + i + 1 := by omega
        rw [hcid_z (i + 1) (by omega), heq_idx, (hchild_congr (t + i + 1) (by omega)).2.1] at hp
        rw [hkey_z i hi]
        exact hright (t + i) (by omega) p hp
    have hsub_c : readNodeSet (l + 1) base t mem₁ c ⊆ readNodeSet (l + 1) base t mem c := by
      intro x hx
      rw [readNodeSet, hnk_c] at hx
      simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
      rcases hx with rfl | ⟨⟨j, hj⟩, hx⟩
      · exact self_mem_readNodeSet _ _ _ _ _
      · rw [hcid_c j (by omega), (hchild_congr j (by omega)).2.2.1] at hx
        exact child_subset_readNodeSet l base t mem c j (by omega) hx
    have hsub_z : readNodeSet (l + 1) base t mem₁ z ⊆
        insert z (readNodeSet (l + 1) base t mem c) := by
      intro x hx
      rw [readNodeSet, hnk_z] at hx
      simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
      rcases hx with rfl | ⟨⟨j, hj⟩, hx⟩
      · exact Finset.mem_insert_self _ _
      · rw [hcid_z j (by omega), (hchild_congr (t + j) (by omega)).2.2.1] at hx
        exact Finset.mem_insert_of_mem
          (child_subset_readNodeSet l base t mem c (t + j) (by omega) hx)
    have hz_not_c : z ∉ readNodeSet (l + 1) base t mem₁ c := fun h => hz_fresh (hsub_c h)
    have hc_not_z : c ∉ readNodeSet (l + 1) base t mem₁ z := by
      intro h
      rw [readNodeSet, hnk_z] at h
      simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and] at h
      rcases h with heq | ⟨⟨j, hj⟩, hx⟩
      · exact hcz heq
      · rw [hcid_z j (by omega), (hchild_congr (t + j) (by omega)).2.2.1] at hx
        exact (hch (t + j) (by omega)).2.2 hx
    have hdisj_cz : Disjoint (readNodeSet (l + 1) base t mem₁ c)
        (readNodeSet (l + 1) base t mem₁ z) := by
      rw [Finset.disjoint_left]
      intro x hxc hxz
      rw [readNodeSet, hnk_c] at hxc
      simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and] at hxc
      rcases hxc with rfl | ⟨⟨j₁, hj₁⟩, hxc⟩
      · exact hc_not_z hxz
      · rw [readNodeSet, hnk_z] at hxz
        simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and] at hxz
        rcases hxz with rfl | ⟨⟨j₂, hj₂⟩, hxz⟩
        · rw [hcid_c j₁ (by omega), (hchild_congr j₁ (by omega)).2.2.1] at hxc
          exact hz_fresh (child_subset_readNodeSet l base t mem c j₁ (by omega) hxc)
        · rw [hcid_c j₁ (by omega), (hchild_congr j₁ (by omega)).2.2.1] at hxc
          rw [hcid_z j₂ (by omega), (hchild_congr (t + j₂) (by omega)).2.2.1] at hxz
          exact Finset.disjoint_left.mp
            (hdisj j₁ (t + j₂) (by omega) (by omega) (by omega)) hxc hxz
    refine ⟨hv_c', hs_c', hnk_c, hv_z', hs_z', hnk_z, hsub_c, hsub_z, hz_not_c, hc_not_z,
      hdisj_cz, ?_, ?_, ?_⟩
    · intro p hp
      rw [mem_toList_readTree_succ, hnk_c] at hp
      rcases hp with ⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩
      · rw [hkey_c i hi]; exact hkeys i (t - 1) hi (by omega)
      · rw [hcid_c j (by omega), (hchild_congr j (by omega)).2.1] at hpj
        exact hs_c.child_lt_key (by omega) (by omega) hpj
    · intro p hp
      rw [mem_toList_readTree_succ, hnk_z] at hp
      rcases hp with ⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩
      · rw [hkey_z i hi]; exact hkeys (t - 1) (t + i) (by omega) (by omega)
      · rw [hcid_z j (by omega), (hchild_congr (t + j) (by omega)).2.1] at hpj
        exact hs_c.key_lt_child (by omega) (by omega) (by omega) hpj
    · intro p
      rw [mem_toList_readTree_succ, mem_toList_readTree_succ, mem_toList_readTree_succ,
        hfull, hnk_c, hnk_z]
      constructor
      · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩)
        · rcases lt_trichotomy i (t - 1) with hlt | rfl | hgt
          · exact Or.inl (Or.inl ⟨i, hlt, by rw [hkey_c i hlt, hval_c i hlt]⟩)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl ⟨i - t, by omega, by
              have heq : t + (i - t) = i := by omega
              rw [hkey_z (i - t) (by omega), hval_z (i - t) (by omega), heq]⟩))
        · rcases lt_or_ge j t with hlt | hge
          · refine Or.inl (Or.inr ⟨j, by omega, ?_⟩)
            rwa [hcid_c j hlt, (hchild_congr j (by omega)).2.1]
          · refine Or.inr (Or.inr (Or.inr ⟨j - t, by omega, ?_⟩))
            have heq : t + (j - t) = j := by omega
            rwa [hcid_z (j - t) (by omega), heq, (hchild_congr j (by omega)).2.1]
      · rintro ((⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩) | rfl | (⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩))
        · exact Or.inl ⟨i, by omega, by rw [hkey_c i hi, hval_c i hi]⟩
        · rw [hcid_c j (by omega), (hchild_congr j (by omega)).2.1] at hpj
          exact Or.inr ⟨j, by omega, hpj⟩
        · exact Or.inl ⟨t - 1, by omega, rfl⟩
        · exact Or.inl ⟨t + i, by omega, by rw [hkey_z i hi, hval_z i hi]⟩
        · rw [hcid_z j (by omega), (hchild_congr (t + j) (by omega)).2.1] at hpj
          exact Or.inr ⟨t + j, by omega, hpj⟩

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
  have hst : nodeStride t = 6 * t := rfl
  have hframe_sub : ∀ S : Finset ℕ, cnt + 1 ∉ S →
      ∀ v ∈ S, ∀ o < nodeStride t, mem' (nodeAddr base t v + o) = mem₁ (nodeAddr base t v + o) := by
    intro S hnot v hv o ho
    have hv_ne : v ≠ cnt + 1 := fun heq => hnot (heq ▸ hv)
    have hsep := nodeAddr_sep base t hv_ne
    have hb := base_lt_nodeAddr base t v o
    dsimp only [mem', memSplitRoot, mem₁]
    repeat rw [Function.update_of_ne (by omega)]
  obtain ⟨hv_c', htr_c', hset_c'⟩ := hv_c1.congr_mem (by omega) (hframe_sub _ hcnt1_not_c)
  have hs_c' := hs_c1.congr_mem (by omega) hv_c1 (hframe_sub _ hcnt1_not_c)
  have hnk_c' : numKeys base t mem' oldRoot = t - 1 :=
    (hframe_sub _ hcnt1_not_c oldRoot (self_mem_readNodeSet _ _ _ _ _) 1
      (by omega)).trans hnk_c1
  obtain ⟨hv_z', htr_z', hset_z'⟩ := hv_z1.congr_mem (by omega) (hframe_sub _ hcnt1_not_z)
  have hs_z' := hs_z1.congr_mem (by omega) hv_z1 (hframe_sub _ hcnt1_not_z)
  have hnk_z' : numKeys base t mem' cnt = t - 1 :=
    (hframe_sub _ hcnt1_not_z cnt (self_mem_readNodeSet _ _ _ _ _) 1
      (by omega)).trans hnk_z1
  -- Fields of `cnt + 1` in `mem'`:
  have hlf_r : leafFlag base t mem' (cnt + 1) = 0 := by
    have hb := base_lt_nodeAddr base t (cnt + 1) 0
    dsimp only [leafFlag, mem', memSplitRoot]
    repeat rw [Function.update_of_ne (by omega)]
    rw [Function.update_self]
  have hnk_r : numKeys base t mem' (cnt + 1) = 1 := by
    have hb := base_lt_nodeAddr base t (cnt + 1) 1
    dsimp only [numKeys, mem', memSplitRoot]
    repeat rw [Function.update_of_ne (by omega)]
    rw [Function.update_self]
  have hk0_r : keyAt base t mem' (cnt + 1) 0 = keyAt base t mem oldRoot (t - 1) := by
    have hb := base_lt_nodeAddr base t (cnt + 1) 2
    dsimp only [keyAt, mem', memSplitRoot]
    simp only [Nat.add_zero]
    repeat rw [Function.update_of_ne (by omega)]
    rw [Function.update_self]
  have hv0_r : valAt base t mem' (cnt + 1) 0 = valAt base t mem oldRoot (t - 1) := by
    have hb := base_lt_nodeAddr base t (cnt + 1) (2 * t + 1)
    dsimp only [valAt, mem', memSplitRoot]
    simp only [Nat.add_zero]
    repeat rw [Function.update_of_ne (by omega)]
    rw [Function.update_self]
  have hc0_r : childAt base t mem' (cnt + 1) 0 = oldRoot := by
    have hb := base_lt_nodeAddr base t (cnt + 1) (4 * t)
    dsimp only [childAt, mem', memSplitRoot]
    simp only [Nat.add_zero]
    repeat rw [Function.update_of_ne (by omega)]
    rw [Function.update_self]
  have hc1_r : childAt base t mem' (cnt + 1) 1 = cnt := by
    have hb := base_lt_nodeAddr base t (cnt + 1) (4 * t + 1)
    dsimp only [childAt, mem', memSplitRoot]
    repeat rw [Function.update_of_ne (by omega)]
    rw [Function.update_self]
  have hv_new : ValidNode (l + 1) base t mem' (cnt + 1) := by
    simp only [ValidNode, hnk_r]
    refine ⟨hlf_r, le_rfl, by omega, ?_, ?_⟩
    · intro j hj
      have hj_cases : j = 0 ∨ j = 1 := by omega
      rcases hj_cases with rfl | rfl
      · rw [hc0_r, hset_c', hnk_c']
        exact ⟨hv_c', le_rfl, hcnt1_not_c⟩
      · rw [hc1_r, hset_z', hnk_z']
        exact ⟨hv_z', le_rfl, hcnt1_not_z⟩
    · intro j₁ j₂ hj₁ hj₂ hne
      have hcases : (j₁ = 0 ∧ j₂ = 1) ∨ (j₁ = 1 ∧ j₂ = 0) := by omega
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hc0_r, hc1_r, hset_c', hset_z']; exact hdisj_cz1
      · rw [hc0_r, hc1_r, hset_c', hset_z']; exact hdisj_cz1.symm
  have hs_new : SortedNode (l + 1) base t mem' (cnt + 1) := by
    simp only [SortedNode, hnk_r]
    refine ⟨by intro i₁ i₂ h12 h2; omega, ?_, ?_, ?_⟩
    · intro j hj
      have hj_cases : j = 0 ∨ j = 1 := by omega
      rcases hj_cases with rfl | rfl
      · rw [hc0_r]; exact hs_c'
      · rw [hc1_r]; exact hs_z'
    · intro i hi p hp
      have hi0 : i = 0 := by omega
      subst hi0
      rw [hc0_r, htr_c'] at hp
      rw [hk0_r]
      exact hlt_med1 p hp
    · intro i hi p hp
      have hi0 : i = 0 := by omega
      subst hi0
      rw [hc1_r, htr_z'] at hp
      rw [hk0_r]
      exact hgt_med1 p hp
  have hrange_new : readNodeSet (l + 1) base t mem' (cnt + 1) ⊆ Finset.range (cnt + 2) := by
    intro x hx
    rw [readNodeSet, hnk_r] at hx
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    rw [Finset.mem_range]
    rcases hx with rfl | ⟨⟨j, hj⟩, hx⟩
    · omega
    · have hj_cases : j = 0 ∨ j = 1 := by omega
      rcases hj_cases with rfl | rfl
      · rw [hc0_r, hset_c'] at hx
        have := Finset.mem_range.mp (hrange (hsub_c1 hx)); omega
      · rw [hc1_r, hset_z'] at hx
        rcases Finset.mem_insert.mp (hsub_z1 hx) with rfl | hx'
        · omega
        · have := Finset.mem_range.mp (hrange hx'); omega
  refine ⟨?_, ?_, hv_new, hs_new, hnk_r, hrange_new, ?_⟩
  · dsimp only [mem', memSplitRoot]
    rw [Function.update_of_ne (by omega), Function.update_self]
  · simp only [mem', memSplitRoot, Function.update_self]
  · apply hs_new.isSortedAssoc.eq_of_forall_mem_iff hs_r.isSortedAssoc
    intro p
    rw [mem_toList_readTree_succ, hnk_r, hmem_iff1]
    constructor
    · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩)
      · have hi0 : i = 0 := by omega
        subst hi0
        rw [hk0_r, hv0_r]
        exact Or.inr (Or.inl rfl)
      · have hj_cases : j = 0 ∨ j = 1 := by omega
        rcases hj_cases with rfl | rfl
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
  set mem' := memSplitChild base t u m slot c cnt mem
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
  have hcnt_not_c : cnt ∉ readNodeSet l base t mem c := fun h =>
    hcnt_fresh (child_subset_readNodeSet l base t mem u slot hslot_lt1 h)
  obtain ⟨hv_c1, hs_c1, hnk_c1, hv_z1, hs_z1, hnk_z1, hsub_c1, hsub_z1, _, _, hdisj_cz1,
    hlt_med1, hgt_med1, hmem_iff1⟩ := memCopyUpper_spec ht hv_c hs_c hfull hcnt_not_c
  -- `u` is disjoint from `c` and `cnt`, so `mem₁` agrees with `mem` on `u`:
  have hmem1_u :
      ∀ o < nodeStride t, mem₁ (nodeAddr base t u + o) = mem (nodeAddr base t u + o) := by
    intro o ho
    have hsep_c := nodeAddr_sep base t hu_ne_c
    have hsep_z := nodeAddr_sep base t hu_ne_cnt
    exact memCopyUpper_outside ht mem _ (by omega) (by omega)
  -- Step 2 of `memSplitChild` modifies ONLY `u` and `base + 1`, so any node set `S` with `u ∉ S`
  -- keeps its `mem₁` cells in `mem'`:
  have hframe_not_u : ∀ S : Finset ℕ, u ∉ S →
      ∀ v ∈ S, ∀ o < nodeStride t, mem' (nodeAddr base t v + o) = mem₁ (nodeAddr base t v + o) := by
    intro S hnot v hv o ho
    have hv_ne : v ≠ u := fun heq => hnot (heq ▸ hv)
    have hsep := nodeAddr_sep base t hv_ne
    have hb := base_lt_nodeAddr base t v o
    dsimp only [mem', memSplitChild, mem₁]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
  have hu_not_c1 : u ∉ readNodeSet l base t mem₁ c := fun h =>
    (hch_u slot hslot_lt1).2.2 (hsub_c1 h)
  have hu_not_z1 : u ∉ readNodeSet l base t mem₁ cnt := fun h => by
    rcases Finset.mem_insert.mp (hsub_z1 h) with heq | h'
    · exact hu_ne_cnt heq
    · exact (hch_u slot hslot_lt1).2.2 h'
  obtain ⟨hv_c', htr_c', hset_c'⟩ := hv_c1.congr_mem (by omega) (hframe_not_u _ hu_not_c1)
  have hs_c' := hs_c1.congr_mem (by omega) hv_c1 (hframe_not_u _ hu_not_c1)
  have hnk_c' : numKeys base t mem' c = t - 1 :=
    (hframe_not_u _ hu_not_c1 c (self_mem_readNodeSet _ _ _ _ _) 1
      (by omega)).trans hnk_c1
  obtain ⟨hv_z', htr_z', hset_z'⟩ := hv_z1.congr_mem (by omega) (hframe_not_u _ hu_not_z1)
  have hs_z' := hs_z1.congr_mem (by omega) hv_z1 (hframe_not_u _ hu_not_z1)
  have hnk_z' : numKeys base t mem' cnt = t - 1 :=
    (hframe_not_u _ hu_not_z1 cnt (self_mem_readNodeSet _ _ _ _ _) 1
      (by omega)).trans hnk_z1
  -- Every sibling `j ≠ slot` (`j < m + 1`) of `u` is untouched from `mem` to `mem'`:
  have hsib_congr : ∀ j < m + 1, j ≠ slot →
      let cid := childAt base t mem u j
      ValidNode l base t mem' cid ∧
        readTree l base t mem' cid = readTree l base t mem cid ∧
        readNodeSet l base t mem' cid = readNodeSet l base t mem cid ∧
        SortedNode l base t mem' cid ∧
        numKeys base t mem' cid = numKeys base t mem cid := by
    intro j hj hne
    set cid := childAt base t mem u j
    have hframe : ∀ w_id ∈ readNodeSet l base t mem cid, ∀ o < nodeStride t,
        mem' (nodeAddr base t w_id + o) = mem (nodeAddr base t w_id + o) := by
      intro w_id hw_in o ho
      have hw_ne_u : w_id ≠ u := fun heq => (hch_u j hj).2.2 (by rw [heq] at hw_in; exact hw_in)
      have hw_ne_c : w_id ≠ c := fun heq =>
        Finset.disjoint_left.mp (hdisj_u j slot hj hslot_lt1 hne) hw_in
          (by rw [heq]; exact self_mem_readNodeSet l base t mem c)
      have hw_ne_cnt : w_id ≠ cnt := fun heq =>
        hcnt_fresh (child_subset_readNodeSet l base t mem u j hj
          (by rw [heq] at hw_in; exact hw_in))
      have hb := base_lt_nodeAddr base t w_id o
      have hsep_u := nodeAddr_sep base t hw_ne_u
      have hsep_c := nodeAddr_sep base t hw_ne_c
      have hsep_z := nodeAddr_sep base t hw_ne_cnt
      exact memSplitChild_outside ht hm_nonfull hslot mem _ (by omega) (by omega)
        (by omega) (by omega)
    obtain ⟨hvs, htrs, hsets⟩ := (hch_u j hj).1.congr_mem (by omega) hframe
    have hss := (hcs_u j hj).congr_mem (by omega) (hch_u j hj).1 hframe
    have hnks := hframe cid (self_mem_readNodeSet l base t mem cid) 1 (by omega)
    exact ⟨hvs, htrs, hsets, hss, hnks⟩
  -- Readbacks on `u` in `mem'`:
  set au := nodeAddr base t u
  have hlf_u' : leafFlag base t mem' u = 0 := by
    have hb := base_lt_nodeAddr base t u 0
    simp only [leafFlag, mem', memSplitChild]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
    exact (hmem1_u 0 (by omega)).trans hlf_u
  have hnk_u' : numKeys base t mem' u = m + 1 := by
    have hb := base_lt_nodeAddr base t u 1
    simp only [numKeys, mem', memSplitChild]
    rw [Function.update_of_ne (by omega), Function.update_self]
  have hkv_u' : ∀ i < m + 1,
      (keyAt base t mem' u i, valAt base t mem' u i) =
        if i < slot then (keyAt base t mem u i, valAt base t mem u i)
        else if i = slot then (keyAt base t mem c (t - 1), valAt base t mem c (t - 1))
        else (keyAt base t mem u (i - 1), valAt base t mem u (i - 1)) := by
    intro i hi
    have hb_k := base_lt_nodeAddr base t u (2 + i)
    have hb_v := base_lt_nodeAddr base t u (2 * t + 1 + i)
    rcases lt_trichotomy i slot with hi_lt | hi_eq | hi_gt
    · simp only [hi_lt, ↓reduceIte]
      apply Prod.ext
      · simp only [keyAt, mem', memSplitChild]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
        simpa only [keyAt, Nat.add_assoc] using hmem1_u (2 + i) (by omega)
      · simp only [valAt, mem', memSplitChild]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
        simpa only [valAt, Nat.add_assoc] using hmem1_u (2 * t + 1 + i) (by omega)
    · subst hi_eq
      simp only [lt_irrefl, ↓reduceIte]
      apply Prod.ext
      · simp only [keyAt, mem', memSplitChild]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self]
      · simp only [valAt, mem', memSplitChild]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_self]
    · have hn : ¬ i < slot := by omega
      have he : i ≠ slot := by omega
      simp only [hn, he, ↓reduceIte]
      apply Prod.ext
      · simp only [keyAt, mem', memSplitChild]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
          shiftArrRight_shifted (au + 2) m (m - slot) mem₁ (by omega) i (by omega) (by omega)]
        simpa only [keyAt, Nat.add_assoc] using hmem1_u (2 + (i - 1)) (by omega)
      · simp only [valAt, mem', memSplitChild]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
          shiftArrRight_shifted (au + (2 * t + 1)) m (m - slot) _ (by omega) i
            (by omega) (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
        simpa only [valAt, Nat.add_assoc] using hmem1_u (2 * t + 1 + (i - 1)) (by omega)
  have hcid_u' : ∀ j < m + 2,
      childAt base t mem' u j =
        if j ≤ slot then childAt base t mem u j
        else if j = slot + 1 then cnt
        else childAt base t mem u (j - 1) := by
    intro j hj
    have hb_c := base_lt_nodeAddr base t u (4 * t + j)
    by_cases hj_le : j ≤ slot
    · simp only [hj_le, ↓reduceIte]
      simp only [childAt, mem', memSplitChild]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega),
        shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
        shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
        shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
      simpa only [childAt, Nat.add_assoc] using hmem1_u (4 * t + j) (by omega)
    · by_cases hj_eq : j = slot + 1
      · subst hj_eq
        simp only [hj_le, ↓reduceIte]
        simp only [childAt, mem', memSplitChild]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self]
      · simp only [hj_le, hj_eq, ↓reduceIte]
        simp only [childAt, mem', memSplitChild]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega),
          shiftArrRight_shifted (au + 4 * t) (m + 1) (m - slot) _ (by omega) j
            (by omega) (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
          shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
        simpa only [childAt, Nat.add_assoc] using hmem1_u (4 * t + (j - 1)) (by omega)
  have hk_slot : keyAt base t mem' u slot = keyAt base t mem c (t - 1) := by
    simpa only [lt_irrefl, ↓reduceIte] using congrArg Prod.fst (hkv_u' slot (by omega))
  have hv_slot : valAt base t mem' u slot = valAt base t mem c (t - 1) := by
    simpa only [lt_irrefl, ↓reduceIte] using congrArg Prod.snd (hkv_u' slot (by omega))
  have hc_slot : childAt base t mem' u slot = c := by
    simpa only [le_rfl, ↓reduceIte] using hcid_u' slot (by omega)
  have hc_slot1 : childAt base t mem' u (slot + 1) = cnt := by
    have hn : ¬ slot + 1 ≤ slot := by omega
    simpa only [hn, ↓reduceIte] using hcid_u' (slot + 1) (by omega)
  -- Helper mapping new child index `j < m + 2` to its node-set bound:
  have hset_sub_old : ∀ j < m + 2, j ≠ slot + 1 →
      let old_j := if j ≤ slot then j else j - 1
      readNodeSet l base t mem' (childAt base t mem' u j) ⊆
        readNodeSet l base t mem (childAt base t mem u old_j) := by
    intro j hj hne1
    dsimp only
    by_cases hj_lt : j < slot
    · have hj_le : j ≤ slot := by omega
      simp only [hj_le, ↓reduceIte]
      rw [hcid_u' j hj]; simp only [hj_le, ↓reduceIte]
      rw [(hsib_congr j (by omega) (by omega)).2.2.1]
    · by_cases hj_eq : j = slot
      · subst hj_eq
        simp only [le_rfl, ↓reduceIte, hc_slot, hset_c']
        exact hsub_c1
      · have hn_le : ¬ j ≤ slot := by omega
        simp only [hn_le, ↓reduceIte]
        rw [hcid_u' j hj]; simp only [hn_le, hne1, ↓reduceIte]
        rw [(hsib_congr (j - 1) (by omega) (by omega)).2.2.1]
  have hv_u' : ValidNode (l + 1) base t mem' u := by
    simp only [ValidNode, hnk_u']
    refine ⟨hlf_u', by omega, by omega, ?_, ?_⟩
    · intro j hj
      by_cases hj_lt : j < slot
      · have hj_le : j ≤ slot := by omega
        rw [hcid_u' j hj]; simp only [hj_le, ↓reduceIte]
        obtain ⟨hvs, _, hsets, _, hnks⟩ := hsib_congr j (by omega) (by omega)
        rw [hsets, hnks]
        exact ⟨hvs, (hch_u j (by omega)).2.1, (hch_u j (by omega)).2.2⟩
      · by_cases hj_eq : j = slot
        · subst hj_eq
          rw [hc_slot, hset_c', hnk_c']
          exact ⟨hv_c', le_rfl, hu_not_c1⟩
        · by_cases hj_eq1 : j = slot + 1
          · subst hj_eq1
            rw [hc_slot1, hset_z', hnk_z']
            exact ⟨hv_z', le_rfl, hu_not_z1⟩
          · have hn_le : ¬ j ≤ slot := by omega
            rw [hcid_u' j hj]; simp only [hn_le, hj_eq1, ↓reduceIte]
            obtain ⟨hvs, _, hsets, _, hnks⟩ := hsib_congr (j - 1) (by omega) (by omega)
            rw [hsets, hnks]
            exact ⟨hvs, (hch_u (j - 1) (by omega)).2.1, (hch_u (j - 1) (by omega)).2.2⟩
    · -- Pairwise disjointness of the `m + 2` child node sets:
      intro j₁ j₂ hj₁ hj₂ hne
      wlog hlt12 : j₁ < j₂ generalizing j₁ j₂
      · exact (this j₂ j₁ hj₂ hj₁ hne.symm (by omega)).symm
      by_cases h1_s1 : j₁ = slot + 1
      · subst h1_s1
        have h2_ne : j₂ ≠ slot + 1 := by omega
        have hn2 : ¬ j₂ ≤ slot := by omega
        have hsub2 := hset_sub_old j₂ hj₂ h2_ne
        simp only [hn2, ↓reduceIte] at hsub2
        rw [hc_slot1, hset_z', Finset.disjoint_left]
        intro x hxz hx2
        have hx2' := hsub2 hx2
        rcases Finset.mem_insert.mp (hsub_z1 hxz) with rfl | hxc
        · exact hcnt_fresh (child_subset_readNodeSet l base t mem u (j₂ - 1) (by omega) hx2')
        · exact Finset.disjoint_left.mp
            (hdisj_u slot (j₂ - 1) hslot_lt1 (by omega) (by omega)) hxc hx2'
      · by_cases h2_s1 : j₂ = slot + 1
        · subst h2_s1
          rw [hc_slot1, hset_z']
          by_cases h1_s : j₁ = slot
          · subst h1_s
            rw [hc_slot, hset_c']
            exact hdisj_cz1
          · have h1_le : j₁ ≤ slot := by omega
            have hsub1 := hset_sub_old j₁ hj₁ h1_s1
            simp only [h1_le, ↓reduceIte] at hsub1
            rw [Finset.disjoint_left]
            intro x hx1 hxz
            have hx1' := hsub1 hx1
            rcases Finset.mem_insert.mp (hsub_z1 hxz) with rfl | hxc
            · exact hcnt_fresh (child_subset_readNodeSet l base t mem u j₁ (by omega) hx1')
            · exact Finset.disjoint_left.mp
                (hdisj_u j₁ slot (by omega) hslot_lt1 h1_s) hx1' hxc
        · have hsub1 := hset_sub_old j₁ hj₁ h1_s1
          have hsub2 := hset_sub_old j₂ hj₂ h2_s1
          dsimp only at hsub1 hsub2
          have hold_ne : (if j₁ ≤ slot then j₁ else j₁ - 1) ≠
              (if j₂ ≤ slot then j₂ else j₂ - 1) := by
            split_ifs <;> omega
          have hold1_lt : (if j₁ ≤ slot then j₁ else j₁ - 1) < m + 1 := by split_ifs <;> omega
          have hold2_lt : (if j₂ ≤ slot then j₂ else j₂ - 1) < m + 1 := by split_ifs <;> omega
          exact Finset.disjoint_of_subset_left hsub1
            (Finset.disjoint_of_subset_right hsub2 (hdisj_u _ _ hold1_lt hold2_lt hold_ne))
  have hs_u' : SortedNode (l + 1) base t mem' u := by
    simp only [SortedNode, hnk_u']
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i₁ i₂ h12 h2
      have hk1 := congrArg Prod.fst (hkv_u' i₁ (by omega))
      have hk2 := congrArg Prod.fst (hkv_u' i₂ h2)
      dsimp only at hk1 hk2
      rw [hk1, hk2]
      have hmed_in_c : (keyAt base t mem c (t - 1), valAt base t mem c (t - 1)) ∈
          (readTree l base t mem c).toList := by
        rw [hmem_iff1]; exact Or.inr (Or.inl rfl)
      rcases lt_trichotomy i₁ slot with h1_lt | h1_eq | h1_gt <;>
        rcases lt_trichotomy i₂ slot with h2_lt | h2_eq | h2_gt
      · simp only [h1_lt, h2_lt, ↓reduceIte]; exact hkeys_u i₁ i₂ h12 (by omega)
      · subst h2_eq
        simp only [h1_lt, lt_irrefl, ↓reduceIte]
        exact hs_u.key_lt_child (by omega) (by omega) hslot_lt1 hmed_in_c
      · have hn2 : ¬ i₂ < slot := by omega
        have he2 : i₂ ≠ slot := by omega
        simp only [h1_lt, hn2, he2, ↓reduceIte]
        exact hkeys_u i₁ (i₂ - 1) (by omega) (by omega)
      · omega
      · omega
      · subst h1_eq
        have hn2 : ¬ i₂ < i₁ := by omega
        have he2 : i₂ ≠ i₁ := by omega
        simp only [lt_irrefl, hn2, he2, ↓reduceIte]
        exact hs_u.child_lt_key (by omega) (by omega) hmed_in_c
      · omega
      · omega
      · have hn1 : ¬ i₁ < slot := by omega
        have he1 : i₁ ≠ slot := by omega
        have hn2 : ¬ i₂ < slot := by omega
        have he2 : i₂ ≠ slot := by omega
        simp only [hn1, he1, hn2, he2, ↓reduceIte]
        exact hkeys_u (i₁ - 1) (i₂ - 1) (by omega) (by omega)
    · intro j hj
      by_cases hj_lt : j < slot
      · have hj_le : j ≤ slot := by omega
        rw [hcid_u' j hj]; simp only [hj_le, ↓reduceIte]
        exact (hsib_congr j (by omega) (by omega)).2.2.2.1
      · by_cases hj_eq : j = slot
        · subst hj_eq; rw [hc_slot]; exact hs_c'
        · by_cases hj_eq1 : j = slot + 1
          · subst hj_eq1; rw [hc_slot1]; exact hs_z'
          · have hn_le : ¬ j ≤ slot := by omega
            rw [hcid_u' j hj]; simp only [hn_le, hj_eq1, ↓reduceIte]
            exact (hsib_congr (j - 1) (by omega) (by omega)).2.2.2.1
    · intro i hi p hp
      have hki := congrArg Prod.fst (hkv_u' i hi)
      dsimp only at hki
      rw [hki]
      rcases lt_trichotomy i slot with hi_lt | hi_eq | hi_gt
      · have hi_le : i ≤ slot := by omega
        rw [hcid_u' i (by omega)] at hp; simp only [hi_le, ↓reduceIte] at hp
        rw [(hsib_congr i (by omega) (by omega)).2.1] at hp
        simp only [hi_lt, ↓reduceIte]
        exact hleft_u i (by omega) p hp
      · subst hi_eq
        rw [hc_slot, htr_c'] at hp
        simp only [lt_irrefl, ↓reduceIte]
        exact hlt_med1 p hp
      · have hn : ¬ i < slot := by omega
        have he : i ≠ slot := by omega
        simp only [hn, he, ↓reduceIte]
        by_cases hi_s1 : i = slot + 1
        · subst hi_s1
          rw [hc_slot1, htr_z'] at hp
          have hin_old : p ∈ (readTree l base t mem c).toList := by
            rw [hmem_iff1]; exact Or.inr (Or.inr hp)
          simpa only [Nat.add_sub_cancel] using hleft_u slot (by omega) p hin_old
        · have hn_le : ¬ i ≤ slot := by omega
          rw [hcid_u' i (by omega)] at hp; simp only [hn_le, hi_s1, ↓reduceIte] at hp
          rw [(hsib_congr (i - 1) (by omega) (by omega)).2.1] at hp
          exact hleft_u (i - 1) (by omega) p hp
    · intro i hi p hp
      have hki := congrArg Prod.fst (hkv_u' i hi)
      dsimp only at hki
      rw [hki]
      rcases lt_trichotomy i slot with hi_lt | hi_eq | hi_gt
      · simp only [hi_lt, ↓reduceIte]
        by_cases hi1_s : i + 1 = slot
        · rw [hi1_s, hc_slot, htr_c'] at hp
          have hin_old : p ∈ (readTree l base t mem (childAt base t mem u (i + 1))).toList := by
            have hin_c : p ∈ (readTree l base t mem c).toList :=
              (hmem_iff1 p).mpr (Or.inl hp)
            dsimp only [c] at hin_c
            rwa [← hi1_s] at hin_c
          exact hright_u i (by omega) p hin_old
        · have hi1_le : i + 1 ≤ slot := by omega
          rw [hcid_u' (i + 1) (by omega)] at hp; simp only [hi1_le, ↓reduceIte] at hp
          rw [(hsib_congr (i + 1) (by omega) (by omega)).2.1] at hp
          exact hright_u i (by omega) p hp
      · subst hi_eq
        rw [hc_slot1, htr_z'] at hp
        simp only [lt_irrefl, ↓reduceIte]
        exact hgt_med1 p hp
      · have hn : ¬ i < slot := by omega
        have he : i ≠ slot := by omega
        have hn1_le : ¬ i + 1 ≤ slot := by omega
        have hn1_eq : i + 1 ≠ slot + 1 := by omega
        simp only [hn, he, ↓reduceIte]
        rw [hcid_u' (i + 1) (by omega)] at hp; simp only [hn1_le, hn1_eq, ↓reduceIte] at hp
        have hsub_idx : i + 1 - 1 = i := by omega
        have heq_s : i - 1 + 1 = i := by omega
        rw [hsub_idx, (hsib_congr i (by omega) (by omega)).2.1, ← heq_s] at hp
        exact hright_u (i - 1) (by omega) p hp
  have hsub_u' : readNodeSet (l + 1) base t mem' u ⊆
      insert cnt (readNodeSet (l + 1) base t mem u) := by
    intro x hx
    rw [readNodeSet, hnk_u'] at hx
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    rcases hx with rfl | ⟨⟨j, hj⟩, hx⟩
    · exact Finset.mem_insert_of_mem (self_mem_readNodeSet _ _ _ _ _)
    · by_cases hj_s1 : j = slot + 1
      · subst hj_s1
        rw [hc_slot1, hset_z'] at hx
        rcases Finset.mem_insert.mp (hsub_z1 hx) with rfl | hxc
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem
            (child_subset_readNodeSet l base t mem u slot hslot_lt1 hxc)
      · have hsub_j := hset_sub_old j hj hj_s1 hx
        have hold_lt : (if j ≤ slot then j else j - 1) < m + 1 := by split_ifs <;> omega
        exact Finset.mem_insert_of_mem
          (child_subset_readNodeSet l base t mem u _ hold_lt hsub_j)
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
    · rw [hkv_u' i hi]
      rcases lt_trichotomy i slot with hi_lt | hi_eq | hi_gt
      · simp only [hi_lt, ↓reduceIte]
        exact Or.inl ⟨i, by omega, rfl⟩
      · subst hi_eq
        simp only [lt_irrefl, ↓reduceIte]
        exact Or.inr ⟨i, hslot_lt1, (hmem_iff1 _).mpr (Or.inr (Or.inl rfl))⟩
      · have hn : ¬ i < slot := by omega
        have he : i ≠ slot := by omega
        simp only [hn, he, ↓reduceIte]
        exact Or.inl ⟨i - 1, by omega, rfl⟩
    · by_cases hj_lt : j < slot
      · have hj_le : j ≤ slot := by omega
        rw [hcid_u' j hj] at hpj; simp only [hj_le, ↓reduceIte] at hpj
        rw [(hsib_congr j (by omega) (by omega)).2.1] at hpj
        exact Or.inr ⟨j, by omega, hpj⟩
      · by_cases hj_eq : j = slot
        · subst hj_eq
          rw [hc_slot, htr_c'] at hpj
          exact Or.inr ⟨j, hslot_lt1, (hmem_iff1 _).mpr (Or.inl hpj)⟩
        · by_cases hj_eq1 : j = slot + 1
          · subst hj_eq1
            rw [hc_slot1, htr_z'] at hpj
            exact Or.inr ⟨slot, hslot_lt1, (hmem_iff1 _).mpr (Or.inr (Or.inr hpj))⟩
          · have hn_le : ¬ j ≤ slot := by omega
            rw [hcid_u' j hj] at hpj; simp only [hn_le, hj_eq1, ↓reduceIte] at hpj
            rw [(hsib_congr (j - 1) (by omega) (by omega)).2.1] at hpj
            exact Or.inr ⟨j - 1, by omega, hpj⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, hpj⟩)
    · rcases lt_or_ge i slot with hi_lt | hi_ge
      · refine Or.inl ⟨i, by omega, ?_⟩
        simpa only [hi_lt, ↓reduceIte] using (hkv_u' i (by omega)).symm
      · refine Or.inl ⟨i + 1, by omega, ?_⟩
        have hn : ¬ i + 1 < slot := by omega
        have he : i + 1 ≠ slot := by omega
        simpa only [hn, he, ↓reduceIte, Nat.add_sub_cancel] using (hkv_u' (i + 1) (by omega)).symm
    · rcases lt_trichotomy j slot with hj_lt | hj_eq | hj_gt
      · refine Or.inr ⟨j, by omega, ?_⟩
        have hj_le : j ≤ slot := by omega
        rw [hcid_u' j (by omega)]; simp only [hj_le, ↓reduceIte]
        rwa [(hsib_congr j hj (by omega)).2.1]
      · subst hj_eq
        rcases (hmem_iff1 p).mp hpj with hpc | rfl | hpz
        · exact Or.inr ⟨j, by omega, by rwa [hc_slot, htr_c']⟩
        · exact Or.inl ⟨j, by omega, by rw [hk_slot, hv_slot]⟩
        · exact Or.inr ⟨j + 1, by omega, by rwa [hc_slot1, htr_z']⟩
      · refine Or.inr ⟨j + 1, by omega, ?_⟩
        have hn_le : ¬ j + 1 ≤ slot := by omega
        have hne1 : j + 1 ≠ slot + 1 := by omega
        rw [hcid_u' (j + 1) (by omega)]; simp only [hn_le, hne1, ↓reduceIte, Nat.add_sub_cancel]
        rwa [(hsib_congr j hj (by omega)).2.1]

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
  have hu_cell : ∀ o < nodeStride t, mem' (nodeAddr base t u + o) = mem (nodeAddr base t u + o) :=
    hframe u hu_not_mod
  have hlf_u' : leafFlag base t mem' u = 0 :=
    (hu_cell 0 (by simp only [nodeStride]; omega)).trans hlf_u
  have hnk_u' : numKeys base t mem' u = m :=
    hu_cell 1 (by simp only [nodeStride]; omega)
  have hkey_u' : ∀ i < m, keyAt base t mem' u i = keyAt base t mem u i := fun i hi => by
    simpa only [keyAt, Nat.add_assoc] using hu_cell (2 + i) (by simp only [nodeStride]; omega)
  have hval_u' : ∀ i < m, valAt base t mem' u i = valAt base t mem u i := fun i hi => by
    simpa only [valAt, Nat.add_assoc] using
      hu_cell (2 * t + 1 + i) (by simp only [nodeStride]; omega)
  have hcid_u' : ∀ j < m + 1, childAt base t mem' u j = childAt base t mem u j := fun j hj => by
    simpa only [childAt, Nat.add_assoc] using hu_cell (4 * t + j) (by simp only [nodeStride]; omega)
  -- Every sibling `j ≠ slot` is untouched:
  have hsib_congr : ∀ j < m + 1, j ≠ slot →
      let cid := childAt base t mem u j
      ValidNode l base t mem' cid ∧
        readTree l base t mem' cid = readTree l base t mem cid ∧
        readNodeSet l base t mem' cid = readNodeSet l base t mem cid ∧
        SortedNode l base t mem' cid ∧
        numKeys base t mem' cid = numKeys base t mem cid := by
    intro j hj hne
    set cid := childAt base t mem u j
    have hfr_sib : ∀ w_id ∈ readNodeSet l base t mem cid, ∀ o < nodeStride t,
        mem' (nodeAddr base t w_id + o) = mem (nodeAddr base t w_id + o) := by
      intro w_id hw_in o ho
      apply hframe w_id _ o ho
      simp only [Finset.mem_union, Finset.mem_Ico, not_or]
      refine ⟨fun hwc => Finset.disjoint_left.mp (hdisj_u j slot hj hslot_lt1 hne) hw_in hwc, ?_⟩
      have hw_lt : w_id < cnt :=
        Finset.mem_range.mp (hrange (child_subset_readNodeSet l base t mem u j hj hw_in))
      omega
    obtain ⟨hvs, htrs, hsets⟩ := (hch_u j hj).1.congr_mem (by omega) hfr_sib
    have hss := (hcs_u j hj).congr_mem (by omega) (hch_u j hj).1 hfr_sib
    have hnks := hfr_sib cid (self_mem_readNodeSet l base t mem cid) 1
      (by simp only [nodeStride]; omega)
    exact ⟨hvs, htrs, hsets, hss, hnks⟩
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
    · intro j₁ j₂ hj₁ hj₂ hne
      rw [hcid_u' j₁ hj₁, hcid_u' j₂ hj₂]
      by_cases h1 : j₁ = slot
      · subst h1
        rw [(hsib_congr j₂ hj₂ hne.symm).2.2.1]
        refine Finset.disjoint_of_subset_left hsub_c' ?_
        rw [Finset.disjoint_union_left]
        refine ⟨hdisj_u j₁ j₂ hslot_lt1 hj₂ hne, ?_⟩
        rw [Finset.disjoint_left]
        intro x hx_ico hx2
        have hx_lt : x < cnt :=
          Finset.mem_range.mp (hrange (child_subset_readNodeSet l base t mem u j₂ hj₂ hx2))
        have := Finset.mem_Ico.mp hx_ico
        omega
      · by_cases h2 : j₂ = slot
        · subst h2
          rw [(hsib_congr j₁ hj₁ h1).2.2.1]
          refine Finset.disjoint_of_subset_right hsub_c' ?_
          rw [Finset.disjoint_union_right]
          refine ⟨hdisj_u j₁ j₂ hj₁ hslot_lt1 hne, ?_⟩
          rw [Finset.disjoint_left]
          intro x hx1 hx_ico
          have hx_lt : x < cnt :=
            Finset.mem_range.mp (hrange (child_subset_readNodeSet l base t mem u j₁ hj₁ hx1))
          have := Finset.mem_Ico.mp hx_ico
          omega
        · rw [(hsib_congr j₁ hj₁ h1).2.2.1, (hsib_congr j₂ hj₂ h2).2.2.1]
          exact hdisj_u j₁ j₂ hj₁ hj₂ hne
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
    rw [readNodeSet, hnk_u'] at hx
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    rcases hx with rfl | ⟨⟨j, hj⟩, hx⟩
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
