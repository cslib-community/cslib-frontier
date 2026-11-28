/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Program
public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.While
public import CslibFrontier.Computability.WordRAM.Realization.Loop
-- `import all` reads `Program`'s private `updateSuffixMin*`, `extractPopItem`, and
-- `shInsertLinkRoot`, plus the unexposed `allocPool` body.
import all CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Program
import CslibFrontier.Foundations.Data.List.Range
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.DataStructure.Memory.Frame
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebraic Model, Representation Invariants, and Pool Specs for Soft Heaps

Algebraic tree representation `SHTree`, heap/rank/corruption invariant `SHTree.Valid`,
in-memory linked item and root-list predicates (`ItemListRep`, `TreeMemRep`, `RootListRep`),
the full soft-heap invariant `SHInv`, pool initialization/allocation specifications
(`shInit_inv`, `allocPool_spec`), and the global corruption bounds
(`shInv_corrupted_le`, `shInv_corrupted_le_eps`).

## Main definitions

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.SHItem`, `SHTree`, `SHTree.Valid`:
  algebraic soft-heap items (`(id, val, origKey)`) and valid multi-item binary trees.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.totalPhi`, `popDeficit`, `rootCredit`:
  exact rational potential function over the root list parameterized by rank threshold `rt`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.SHInv`: full pool, structural, and
  amortized rank-birth invariant.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.shInit_inv`: empty `SHInv` initialization.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.allocPool_spec`: pool allocator correctness
  at exact memory cost `2`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.SHInv.origKey_le_ckey`: surviving entries
  never have keys lowered below `origKey`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.shInv_corrupted_le`,
  `shInv_corrupted_le_eps`: global corruption bounds for arbitrary threshold `h.rankThreshold` and
  rational `ε > 0`.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory

/-- Item stored inside a soft-heap node: slot index `id`, payload `val`, and key `origKey`. -/
structure SHItem where
  /-- 1-based slot index in the item pool. -/
  id : ℕ
  /-- Payload value stored with the item. -/
  val : ℕ
  /-- Original key of the item. -/
  origKey : ℕ
  deriving DecidableEq

/-- Algebraic soft-heap binary tree with explicit corrupted key `ckey`, item list, and optional
left/right children. -/
inductive SHTree where
  /-- Internal or leaf soft-heap node. -/
  | node (id rank ckey : ℕ) (items : List SHItem) (left right : Option SHTree) : SHTree

/-- Structural induction principle for `SHTree` across optional left/right subtrees. -/
private theorem SHTree.ind {motive : SHTree → Prop}
    (node : ∀ id r ck items l r',
      (∀ c, l = some c → motive c) → (∀ c, r' = some c → motive c) →
      motive (.node id r ck items l r')) : ∀ t, motive t
  | .node id r ck items l r' =>
      node id r ck items l r'
        (fun c hc => by subst hc; exact SHTree.ind node c)
        (fun c hc => by subst hc; exact SHTree.ind node c)

/-- 1-based node pool slot index of the root of `t`. -/
@[expose] def SHTree.rootId : SHTree → ℕ
  | .node id _ _ _ _ _ => id

/-- Rank of the root of `t`. -/
@[expose] def SHTree.rank : SHTree → ℕ
  | .node _ r _ _ _ _ => r

/-- Corrupted upper-bound key stored at the root of `t`. -/
@[expose] def SHTree.ckey : SHTree → ℕ
  | .node _ _ ck _ _ _ => ck

/-- Item list stored directly at the root of `t`. -/
@[expose] def SHTree.items : SHTree → List SHItem
  | .node _ _ _ items _ _ => items

/-- Left child subtree of the root of `t`. -/
@[expose] def SHTree.left : SHTree → Option SHTree
  | .node _ _ _ _ l _ => l

/-- Right child subtree of the root of `t`. -/
@[expose] def SHTree.right : SHTree → Option SHTree
  | .node _ _ _ _ _ r => r

/-- All 1-based node pool indices appearing in `t`. -/
@[expose] def SHTree.nodeIds : SHTree → List ℕ
  | .node id _ _ _ l r =>
      id :: (match l with | none => [] | some c => c.nodeIds) ++
        (match r with | none => [] | some c => c.nodeIds)

/-- Reduction equation for `SHTree.nodeIds` in terms of `Option.elim`. -/
@[simp] theorem SHTree.nodeIds_node (id r ck : ℕ) (items : List SHItem)
    (l r' : Option SHTree) :
    (SHTree.node id r ck items l r').nodeIds =
      id :: l.elim [] SHTree.nodeIds ++ r'.elim [] SHTree.nodeIds := by
  cases l <;> cases r' <;> rfl

/-- All `(item, ckey)` entries appearing in `t`. -/
@[expose] def SHTree.allEntries : SHTree → List (SHItem × ℕ)
  | .node _ _ ck items l r =>
      items.map (fun it => (it, ck)) ++
        (match l with | none => [] | some c => c.allEntries) ++
        (match r with | none => [] | some c => c.allEntries)

/-- Reduction equation for `SHTree.allEntries` in terms of `Option.elim`. -/
@[simp] theorem SHTree.allEntries_node (id r ck : ℕ) (items : List SHItem)
    (l r' : Option SHTree) :
    (SHTree.node id r ck items l r').allEntries =
      items.map (fun it => (it, ck)) ++
        l.elim [] SHTree.allEntries ++ r'.elim [] SHTree.allEntries := by
  cases l <;> cases r' <;> rfl

/-- All items appearing anywhere in `t`. -/
@[expose] def SHTree.allItems (t : SHTree) : List SHItem :=
  t.allEntries.map Prod.fst

/-- All 1-based item pool indices appearing in `t`. -/
@[expose] def SHTree.itemIds (t : SHTree) : List ℕ :=
  t.allItems.map SHItem.id

/-- Total number of nodes in `t`. -/
@[expose] def SHTree.nodeCount : SHTree → ℕ
  | .node _ _ _ _ l r =>
      1 + (match l with | none => 0 | some c => c.nodeCount) +
        (match r with | none => 0 | some c => c.nodeCount)

/-- Reduction equation for `SHTree.nodeCount` in terms of `Option.elim`. -/
@[simp] theorem SHTree.nodeCount_node (id r ck : ℕ) (items : List SHItem)
    (l r' : Option SHTree) :
    (SHTree.node id r ck items l r').nodeCount =
      1 + l.elim 0 SHTree.nodeCount + r'.elim 0 SHTree.nodeCount := by
  cases l <;> cases r' <;> rfl

/-- Number of nodes of rank `k` in `t`. -/
@[expose] def SHTree.countRank (k : ℕ) : SHTree → ℕ
  | .node _ r _ _ l r' =>
      (if r = k then 1 else 0) +
        (match l with | none => 0 | some c => c.countRank k) +
        (match r' with | none => 0 | some c => c.countRank k)

/-- Reduction equation for `SHTree.countRank` in terms of `Option.elim`. -/
@[simp] theorem SHTree.countRank_node (k id r ck : ℕ) (items : List SHItem)
    (l r' : Option SHTree) :
    (SHTree.node id r ck items l r').countRank k =
      (if r = k then 1 else 0) +
        l.elim 0 (SHTree.countRank k) + r'.elim 0 (SHTree.countRank k) := by
  cases l <;> cases r' <;> rfl

/-- Sum of `itemPhi rt` across all items in `t`. -/
@[expose] def SHTree.itemPhiSum (rt : ℕ) : SHTree → ℚ
  | .node _ r _ items l r' =>
      (items.length : ℚ) * itemPhi rt r +
        (match l with | none => 0 | some c => c.itemPhiSum rt) +
        (match r' with | none => 0 | some c => c.itemPhiSum rt)

/-- Reduction equation for `SHTree.itemPhiSum` in terms of `Option.elim`. -/
@[simp] theorem SHTree.itemPhiSum_node (rt id r ck : ℕ) (items : List SHItem)
    (l r' : Option SHTree) :
    (SHTree.node id r ck items l r').itemPhiSum rt =
      (items.length : ℚ) * itemPhi rt r +
        l.elim 0 (SHTree.itemPhiSum rt) + r'.elim 0 (SHTree.itemPhiSum rt) := by
  cases l <;> cases r' <;> rfl

/-- Amortized tree potential combining item potential (`120`) and node credit (`30`). -/
@[expose] def SHTree.phi (rt : ℕ) (t : SHTree) : ℚ :=
  120 * t.itemPhiSum rt + 30 * (t.nodeCount : ℚ)

/-- Structural, heap-order, rank, and corruption invariants of a soft-heap tree relative to
rank threshold `rt` and parent lower bound `lb`. -/
inductive SHTree.Valid (rt : ℕ) : ℕ → SHTree → Prop where
  /-- Valid soft-heap tree node relative to lower bound `lb`. -/
  | node {lb id r ck : ℕ} {items : List SHItem} {l r' : Option SHTree} :
      items ≠ [] →
      items.length ≤ sizeCap rt r →
      lb ≤ ck →
      (∀ it ∈ items, it.origKey ≤ ck) →
      (r ≤ rt → ∀ it ∈ items, it.origKey = ck) →
      ((l.isSome ∨ r'.isSome) → targetSize rt r ≤ 2 * items.length) →
      (∀ c, l = some c → c.rank + 1 = r) →
      (∀ c, l = some c → SHTree.Valid rt ck c) →
      (∀ c, r' = some c → c.rank + 1 = r) →
      (∀ c, r' = some c → SHTree.Valid rt ck c) →
      SHTree.Valid rt lb (.node id r ck items l r')

private theorem SHTree.Valid.items_ne {rt lb : ℕ} {t : SHTree} (h : t.Valid rt lb) :
    t.items ≠ [] := by cases h; assumption

private theorem SHTree.Valid.cap {rt lb : ℕ} {t : SHTree} (h : t.Valid rt lb) :
    t.items.length ≤ sizeCap rt t.rank := by cases h; assumption

private theorem SHTree.Valid.lb_le {rt lb : ℕ} {t : SHTree} (h : t.Valid rt lb) :
    lb ≤ t.ckey := by cases h; assumption

private theorem SHTree.Valid.origKey_le {rt lb : ℕ} {t : SHTree} (h : t.Valid rt lb) :
    ∀ it ∈ t.items, it.origKey ≤ t.ckey := by cases h; assumption

private theorem SHTree.Valid.rank_le_threshold {rt lb : ℕ} {t : SHTree} (h : t.Valid rt lb) :
    t.rank ≤ rt → ∀ it ∈ t.items, it.origKey = t.ckey := by cases h; assumption

private theorem SHTree.Valid.half_full {rt lb : ℕ} {t : SHTree} (h : t.Valid rt lb) :
    (t.left.isSome ∨ t.right.isSome) → targetSize rt t.rank ≤ 2 * t.items.length := by
  cases h; assumption

private theorem SHTree.Valid.left_valid {rt lb : ℕ} {t : SHTree} (h : t.Valid rt lb) :
    ∀ c, t.left = some c → c.rank + 1 = t.rank ∧ c.Valid rt t.ckey := by
  cases h with
  | node _ _ _ _ _ _ hl_rk hl_v _ _ => exact fun c hc => ⟨hl_rk c hc, hl_v c hc⟩

private theorem SHTree.Valid.right_valid {rt lb : ℕ} {t : SHTree} (h : t.Valid rt lb) :
    ∀ c, t.right = some c → c.rank + 1 = t.rank ∧ c.Valid rt t.ckey := by
  cases h with
  | node _ _ _ _ _ _ _ _ hr_rk hr_v => exact fun c hc => ⟨hr_rk c hc, hr_v c hc⟩

/-- Weakening lower bound preserves `SHTree.Valid`. -/
private theorem SHTree.Valid.mono_lb {rt lb₁ lb₂ : ℕ} {t : SHTree} (h : lb₁ ≤ lb₂)
    (ht : t.Valid rt lb₂) : t.Valid rt lb₁ := by
  cases ht with
  | node hne hcap hlb hle hrt hhalf hl_rk hl_v hr_rk hr_v =>
    exact .node hne hcap (Nat.le_trans h hlb) hle hrt hhalf hl_rk hl_v hr_rk hr_v

/-- `SHTree.nodeIds.length = SHTree.nodeCount`. -/
private theorem SHTree.nodeIds_length (t : SHTree) : t.nodeIds.length = t.nodeCount := by
  induction t using SHTree.ind with
  | node id r ck items l r' ihL ihR =>
    cases l <;> cases r' <;> simp [ihL, ihR] <;> omega

/-- `SHTree.nodeCount ≥ 1`. -/
private theorem SHTree.nodeCount_pos (t : SHTree) : 0 < t.nodeCount := by
  cases t; simp

/-- `rootId` is the head of `nodeIds`. -/
private theorem SHTree.rootId_mem_nodeIds (t : SHTree) : t.rootId ∈ t.nodeIds := by
  cases t; simp [SHTree.rootId]

/-- `itemPhiSum` is always non-negative. -/
private theorem SHTree.itemPhiSum_nonneg (rt : ℕ) (t : SHTree) : 0 ≤ t.itemPhiSum rt := by
  induction t using SHTree.ind with
  | node id r ck items l r' ihL ihR =>
    simp only [SHTree.itemPhiSum_node]
    refine add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (itemPhi_nonneg rt r)) ?_) ?_
    · cases l with
      | none => exact le_rfl
      | some c => exact ihL c rfl
    · cases r' with
      | none => exact le_rfl
      | some c => exact ihR c rfl

/-- `phi` is always non-negative. -/
private theorem SHTree.phi_nonneg (rt : ℕ) (t : SHTree) : 0 ≤ t.phi rt := by
  unfold SHTree.phi
  have := t.itemPhiSum_nonneg rt
  positivity

/-- `itemPhiSum ≤ (2 * rt + 3) * allEntries.length`. -/
private theorem SHTree.itemPhiSum_le (rt : ℕ) (t : SHTree) :
    t.itemPhiSum rt ≤ (2 * (rt : ℚ) + 3) * (t.allEntries.length : ℚ) := by
  induction t using SHTree.ind with
  | node id r ck items l r' ihL ihR =>
    simp only [SHTree.itemPhiSum_node, SHTree.allEntries_node,
      List.length_append, List.length_map]
    have hi : (items.length : ℚ) * itemPhi rt r ≤ (2 * (rt : ℚ) + 3) * (items.length : ℚ) :=
      (mul_le_mul_of_nonneg_left (itemPhi_le_zero rt r) (Nat.cast_nonneg _)).trans_eq
        (mul_comm _ _)
    have hL : l.elim 0 (SHTree.itemPhiSum rt) ≤
        (2 * (rt : ℚ) + 3) * (l.elim [] SHTree.allEntries).length := by
      cases l with
      | none => simp
      | some c => exact ihL c rfl
    have hR : r'.elim 0 (SHTree.itemPhiSum rt) ≤
        (2 * (rt : ℚ) + 3) * (r'.elim [] SHTree.allEntries).length := by
      cases r' with
      | none => simp
      | some c => exact ihR c rfl
    push_cast
    linarith

/-- Lower bound preserved throughout a valid tree: every entry has `lb ≤ ckey`. -/
private theorem SHTree.Valid.lb_le_allEntries {rt lb : ℕ} {t : SHTree} (ht : t.Valid rt lb) :
    ∀ p ∈ t.allEntries, lb ≤ p.2 := by
  induction t using SHTree.ind generalizing lb with
  | node id r ck items l r' ihL ihR =>
    rcases ht with ⟨_, _, hlb, _, _, _, _, hl, _, hr⟩
    intro p hp
    simp only [SHTree.allEntries_node, List.mem_append, List.mem_map] at hp
    rcases hp with (⟨it, _, rfl⟩ | hL) | hR
    · exact hlb
    · cases l with
      | none => simp at hL
      | some c => exact Nat.le_trans hlb (ihL c rfl (hl c rfl) p hL)
    · cases r' with
      | none => simp at hR
      | some c => exact Nat.le_trans hlb (ihR c rfl (hr c rfl) p hR)

private theorem SHTree.Valid.origKey_le_allEntries {rt lb : ℕ} {t : SHTree} (ht : t.Valid rt lb) :
    ∀ p ∈ t.allEntries, p.1.origKey ≤ p.2 := by
  induction t using SHTree.ind generalizing lb with
  | node id r ck items l r' ihL ihR =>
    rcases ht with ⟨_, _, _, hle, _, _, _, hl, _, hr⟩
    intro p hp
    simp only [SHTree.allEntries_node, List.mem_append, List.mem_map] at hp
    rcases hp with (⟨it, hit, rfl⟩ | hL) | hR
    · exact hle it hit
    · cases l with
      | none => simp at hL
      | some c => exact ihL c rfl (hl c rfl) p hL
    · cases r' with
      | none => simp at hR
      | some c => exact ihR c rfl (hr c rfl) p hR

/-- Number of corrupted items in a valid tree is bounded by the rank-`> rt` node capacities. -/
private theorem SHTree.corrupted_le_sum_countRank {rt lb K : ℕ} {t : SHTree} (ht : t.Valid rt lb)
    (hK : ∀ r, 0 < t.countRank r → r ≤ K) :
    (t.allEntries.filter (fun p => decide (p.1.origKey < p.2))).length ≤
      ∑ k ∈ Finset.Icc (rt + 1) K, t.countRank k * sizeCap rt k := by
  induction t using SHTree.ind generalizing lb with
  | node id r ck items l r' ihL ihR =>
    rcases ht with ⟨_, hcap, _, _, hrt, _, _, hl, _, hr⟩
    have hrK : r ≤ K := hK r (by simp)
    have hK_L : ∀ c, l = some c → ∀ k, 0 < c.countRank k → k ≤ K := fun c hc k hk =>
      hK k (by simp only [SHTree.countRank_node, hc, Option.elim_some]; omega)
    have hK_R : ∀ c, r' = some c → ∀ k, 0 < c.countRank k → k ≤ K := fun c hc k hk =>
      hK k (by simp only [SHTree.countRank_node, hc, Option.elim_some]; omega)
    have hroot : ((items.map (fun it => (it, ck))).filter
        (fun p => decide (p.1.origKey < p.2))).length ≤
        if rt + 1 ≤ r then sizeCap rt r else 0 := by
      by_cases hgt : rt + 1 ≤ r
      · simp only [hgt, ↓reduceIte]
        exact Nat.le_trans (List.length_filter_le _ _) (by simpa using hcap)
      · simp only [hgt, ↓reduceIte, Nat.le_zero, List.length_eq_zero_iff, List.filter_eq_nil_iff,
          List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        exact fun it hit => by simp [hrt (by omega) it hit]
    have hL_bound : ((l.elim [] SHTree.allEntries).filter
        (fun p => decide (p.1.origKey < p.2))).length ≤
        ∑ k ∈ Finset.Icc (rt + 1) K, (l.elim 0 (SHTree.countRank k)) * sizeCap rt k := by
      cases l with
      | none => simp
      | some c => exact ihL c rfl (hl c rfl) (hK_L c rfl)
    have hR_bound : ((r'.elim [] SHTree.allEntries).filter
        (fun p => decide (p.1.origKey < p.2))).length ≤
        ∑ k ∈ Finset.Icc (rt + 1) K, (r'.elim 0 (SHTree.countRank k)) * sizeCap rt k := by
      cases r' with
      | none => simp
      | some c => exact ihR c rfl (hr c rfl) (hK_R c rfl)
    have hsum_eq : ∑ k ∈ Finset.Icc (rt + 1) K,
        SHTree.countRank k (.node id r ck items l r') * sizeCap rt k =
        (if rt + 1 ≤ r then sizeCap rt r else 0) +
          (∑ k ∈ Finset.Icc (rt + 1) K, l.elim 0 (SHTree.countRank k) * sizeCap rt k) +
          (∑ k ∈ Finset.Icc (rt + 1) K, r'.elim 0 (SHTree.countRank k) * sizeCap rt k) := by
      have hterm : ∀ k ∈ Finset.Icc (rt + 1) K,
          SHTree.countRank k (.node id r ck items l r') * sizeCap rt k =
          (if r = k then sizeCap rt k else 0) +
            l.elim 0 (SHTree.countRank k) * sizeCap rt k +
            r'.elim 0 (SHTree.countRank k) * sizeCap rt k := by
        intro k _
        simp only [SHTree.countRank_node]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_ite_eq]
      simp [Finset.mem_Icc, hrK]
    simp only [SHTree.allEntries_node, List.filter_append, List.length_append]
    omega

/-- Credit carried by each root of rank `r` in the doubly-linked root list. -/
@[expose] def rootCredit (r : ℕ) : ℚ :=
  86 + 6 * (r : ℚ)

/-- Deficit potential stored on a non-leaf root whose item list dropped below `targetSize`. -/
@[expose] def popDeficit (rt : ℕ) (t : SHTree) : ℚ :=
  if t.left.isSome ∨ t.right.isSome then
    12 * ((targetSize rt t.rank - min t.items.length (targetSize rt t.rank) : ℕ) : ℚ)
  else 0

/-- Total soft-heap potential over the list of root trees under rank threshold `rt`. -/
@[expose] def totalPhi (rt : ℕ) (roots : List SHTree) : ℚ :=
  (roots.map (fun t => t.phi rt + rootCredit t.rank + popDeficit rt t)).sum

/-- `popDeficit` is always non-negative. -/
private theorem popDeficit_nonneg (rt : ℕ) (t : SHTree) : 0 ≤ popDeficit rt t := by
  unfold popDeficit
  split_ifs <;> positivity

/-- `totalPhi` is always non-negative. -/
theorem totalPhi_nonneg (rt : ℕ) (roots : List SHTree) : 0 ≤ totalPhi rt roots := by
  refine List.sum_nonneg fun x hx => ?_
  rcases List.mem_map.mp hx with ⟨t, _, rfl⟩
  have h2 : (0 : ℚ) ≤ rootCredit t.rank := by unfold rootCredit; positivity
  linarith [t.phi_nonneg rt, popDeficit_nonneg rt t]

/-- All `(item, ckey)` pairs across all roots in `roots`. -/
@[expose] def forestEntries (roots : List SHTree) : List (SHItem × ℕ) :=
  roots.flatMap SHTree.allEntries

/-- All items across all roots in `roots`. -/
@[expose] def forestItems (roots : List SHTree) : List SHItem :=
  (forestEntries roots).map Prod.fst

/-- All 1-based node pool indices across all roots in `roots`. -/
@[expose] def forestNodeIds (roots : List SHTree) : List ℕ :=
  roots.flatMap SHTree.nodeIds

/-- All 1-based item pool indices across all roots in `roots`. -/
@[expose] def forestItemIds (roots : List SHTree) : List ℕ :=
  roots.flatMap SHTree.itemIds

/-- Cells belonging to the soft-heap pool slice anchored at `(ic₀, nc₀)` with capacities
`(maxItems, maxNodes)`. -/
@[expose] def InSHPool (ic₀ nc₀ maxItems maxNodes : ℕ) (h : SHHandle) (a : ℕ) : Prop :=
  (h.itemBase + 3 * (ic₀ + 1) ≤ a ∧ a < h.itemBase + 3 * (maxItems + 1)) ∨
  (h.nodeBase + 12 * (nc₀ + 1) ≤ a ∧ a < h.nodeBase + 12 * (maxNodes + 1))

/-- Singly-linked item-pool list representation from `head` to `tail`. -/
@[expose] def ItemListRep (itemBase : ℕ) (mem : ℕ → ℕ) (head tail : ℕ) : List SHItem → Prop
  | [] => head = 0 ∧ tail = 0
  | [it] =>
      head = it.id ∧ tail = it.id ∧ it.id ≠ 0 ∧
      mem (itemBase + 3 * it.id) = it.val ∧
      mem (itemBase + 3 * it.id + 1) = it.origKey ∧
      mem (itemBase + 3 * it.id + 2) = 0
  | it :: it2 :: rest =>
      head = it.id ∧ it.id ≠ 0 ∧
      mem (itemBase + 3 * it.id) = it.val ∧
      mem (itemBase + 3 * it.id + 1) = it.origKey ∧
      mem (itemBase + 3 * it.id + 2) = it2.id ∧
      ItemListRep itemBase mem it2.id tail (it2 :: rest)

/-- Item list representation depends only on cells `itemBase + 3 * it.id + {0, 1, 2}` for
`it ∈ items`. -/
theorem ItemListRep.congr {itemBase : ℕ} {mem₁ mem₂ : ℕ → ℕ} {head tail : ℕ}
    {items : List SHItem}
    (hagree : ∀ it ∈ items, ∀ j < 3, mem₁ (itemBase + 3 * it.id + j) =
      mem₂ (itemBase + 3 * it.id + j))
    (hrep : ItemListRep itemBase mem₁ head tail items) :
    ItemListRep itemBase mem₂ head tail items := by
  induction items generalizing head with
  | nil => exact hrep
  | cons it rest ih =>
    cases rest with
    | nil =>
      rcases hrep with ⟨hh, ht, hid, h0, h1, h2⟩
      refine ⟨hh, ht, hid, ?_, ?_, ?_⟩
      · simpa using (hagree it (by simp) 0 (by decide)).symm.trans h0
      · simpa using (hagree it (by simp) 1 (by decide)).symm.trans h1
      · simpa using (hagree it (by simp) 2 (by decide)).symm.trans h2
    | cons it2 rest2 =>
      rcases hrep with ⟨hh, hid, h0, h1, h2, htail⟩
      refine ⟨hh, hid, ?_, ?_, ?_, ?_⟩
      · simpa using (hagree it (by simp) 0 (by decide)).symm.trans h0
      · simpa using (hagree it (by simp) 1 (by decide)).symm.trans h1
      · simpa using (hagree it (by simp) 2 (by decide)).symm.trans h2
      · exact ih (fun x hx => hagree x (by simp [hx])) htail

/-- If `xs ≠ []`, `tail` equals `it.id` for some `it ∈ xs`. -/
private theorem ItemListRep.tail_mem {itemBase : ℕ} {mem : ℕ → ℕ} {head tail : ℕ}
    {xs : List SHItem} (hne : xs ≠ []) (h : ItemListRep itemBase mem head tail xs) :
    ∃ it ∈ xs, tail = it.id ∧ it.id ≠ 0 := by
  induction xs generalizing head with
  | nil => contradiction
  | cons x rest ih =>
    cases rest with
    | nil =>
      rcases h with ⟨_, ht, hid, _⟩
      exact ⟨x, by simp, ht, hid⟩
    | cons x2 rest2 =>
      rcases h with ⟨_, _, _, _, _, hrest⟩
      rcases ih (by simp) hrest with ⟨it, hit, htail, hid⟩
      exact ⟨it, by simp [hit], htail, hid⟩

/-- Appending a non-empty list onto `ItemListRep` updates either `head` (if empty) or
`curTail.nextItem` (`+2`), provided item IDs do not alias. -/
private theorem ItemListRep.append {itemBase : ℕ} {mem : ℕ → ℕ} {h₁ t₁ h₂ t₂ : ℕ}
    {xs ys : List SHItem} (hy : ys ≠ [])
    (hnodup : (xs.map SHItem.id).Nodup)
    (hdisj : ∀ x ∈ xs, ∀ y ∈ ys, x.id ≠ y.id)
    (hx_rep : ItemListRep itemBase mem h₁ t₁ xs)
    (hy_rep : ItemListRep itemBase mem h₂ t₂ ys) :
    let mem' := if h₁ = 0 then mem else Function.update mem (itemBase + 3 * t₁ + 2) h₂
    let h' := if h₁ = 0 then h₂ else h₁
    ItemListRep itemBase mem' h' t₂ (xs ++ ys) := by
  induction xs generalizing h₁ with
  | nil =>
    rcases hx_rep with ⟨rfl, _⟩
    simp [hy_rep]
  | cons x rest ih =>
    have hx_id : x.id ≠ 0 := by
      cases rest with
      | nil => exact hx_rep.2.2.1
      | cons _ _ => exact hx_rep.2.1
    have h₁_ne : h₁ ≠ 0 := by
      cases rest with
      | nil => rw [hx_rep.1]; exact hx_id
      | cons _ _ => rw [hx_rep.1]; exact hx_id
    simp only [h₁_ne, ↓reduceIte, List.cons_append]
    cases rest with
    | nil =>
      rcases hx_rep with ⟨rfl, rfl, _, h0, h1, _⟩
      cases ys with
      | nil => contradiction
      | cons y ys' =>
        have hhd_y : h₂ = y.id := by
          cases ys' with
          | nil => exact hy_rep.1
          | cons _ _ => exact hy_rep.1
        have hagree_y : ∀ z ∈ y :: ys', ∀ j < 3,
            mem (itemBase + 3 * z.id + j) =
              Function.update mem (itemBase + 3 * x.id + 2) h₂ (itemBase + 3 * z.id + j) := by
          intro z hz j hj
          have hzx : x.id ≠ z.id := hdisj x (by simp) z hz
          rw [Function.update_of_ne (by omega)]
        refine ⟨rfl, hx_id, ?_, ?_, ?_, ?_⟩
        · rw [Function.update_of_ne (by omega)]; exact h0
        · rw [Function.update_of_ne (by omega)]; exact h1
        · rw [Function.update_self, hhd_y]
        · rw [← hhd_y]
          exact ItemListRep.congr hagree_y hy_rep
    | cons x2 rest2 =>
      rcases hx_rep with ⟨rfl, _, h0, h1, h2, hrest⟩
      have hx2_ne : x2.id ≠ 0 := by
        cases rest2 with
        | nil => exact hrest.2.2.1
        | cons _ _ => exact hrest.2.1
      obtain ⟨it_t, hit_t, htail_eq, _⟩ := ItemListRep.tail_mem (by simp) hrest
      have hnodup' : x.id ∉ (x2 :: rest2).map SHItem.id ∧
          ((x2 :: rest2).map SHItem.id).Nodup := by
        rw [List.map_cons, List.nodup_cons] at hnodup
        exact hnodup
      have hx_ne_t₁ : x.id ≠ t₁ := fun heq =>
        hnodup'.1 (heq ▸ htail_eq ▸ List.mem_map_of_mem hit_t)
      have hih := ih hnodup'.2 (fun a ha => hdisj a (by simp [ha])) hrest
      simp only [hx2_ne, ↓reduceIte] at hih
      refine ⟨rfl, hx_id, ?_, ?_, ?_, hih⟩
      · rw [Function.update_of_ne (by omega)]; exact h0
      · rw [Function.update_of_ne (by omega)]; exact h1
      · rw [Function.update_of_ne (by omega)]; exact h2

/-- Head of a non-empty `ItemListRep` cannot be `0`. -/
private theorem ItemListRep.head_ne_zero {itemBase : ℕ} {mem : ℕ → ℕ} {head tail : ℕ}
    {xs : List SHItem} (hne : xs ≠ []) (h : ItemListRep itemBase mem head tail xs) :
    head ≠ 0 := by
  cases xs with
  | nil => contradiction
  | cons x rest =>
    cases rest with
    | nil => rw [h.1]; exact h.2.2.1
    | cons _ _ => rw [h.1]; exact h.2.1

/-- Empty list iff `head = 0` in `ItemListRep`. -/
private theorem ItemListRep.head_eq_zero_iff {itemBase : ℕ} {mem : ℕ → ℕ} {head tail : ℕ}
    {xs : List SHItem} (h : ItemListRep itemBase mem head tail xs) :
    head = 0 ↔ xs = [] := by
  exact ⟨fun hz => by_contra fun hne => h.head_ne_zero hne hz, fun h0 => (h0 ▸ h).1⟩

/-- Popping the head of a non-empty `ItemListRep` matches `extractPopItem`. -/
private theorem ItemListRep.pop {itemBase : ℕ} {mem : ℕ → ℕ} {head tail : ℕ} {it : SHItem}
    {rest : List SHItem} (h : ItemListRep itemBase mem head tail (it :: rest)) :
    head = it.id ∧
    mem (itemBase + 3 * it.id) = it.val ∧
    mem (itemBase + 3 * it.id + 1) = it.origKey ∧
    let nxt := mem (itemBase + 3 * it.id + 2)
    ItemListRep itemBase mem nxt (if nxt = 0 then 0 else tail) rest := by
  cases rest with
  | nil =>
    rcases h with ⟨hh, ht, hid, h0, h1, h2⟩
    refine ⟨hh, h0, h1, ?_⟩
    simp [h2, ItemListRep]
  | cons it2 rest2 =>
    rcases h with ⟨hh, hid, h0, h1, h2, htail⟩
    have h2_ne : it2.id ≠ 0 := by
      cases rest2 with
      | nil => exact htail.2.2.1
      | cons _ _ => exact htail.2.1
    refine ⟨hh, h0, h1, ?_⟩
    simpa [h2, h2_ne] using htail

/-- Soft-heap node and subtree fields in memory (offsets `+0..+7` plus item pool; offsets `+8..+11`
are managed separately for parent links during `defill` and root links in `RootListRep`). -/
inductive TreeMemRep (rt itemBase nodeBase : ℕ) (mem : ℕ → ℕ) : SHTree → Prop where
  /-- Valid in-memory node representation (`+0..+7` and linked item list). -/
  | node {id r ck : ℕ} {items : List SHItem} {l r' : Option SHTree} :
      id ≠ 0 →
      mem (nodeBase + 12 * id) = ck →
      mem (nodeBase + 12 * id + 1) = r →
      mem (nodeBase + 12 * id + 2) = targetSize rt r →
      mem (nodeBase + 12 * id + 3) = items.length →
      ItemListRep itemBase mem (mem (nodeBase + 12 * id + 4)) (mem (nodeBase + 12 * id + 5))
        items →
      mem (nodeBase + 12 * id + 6) = l.elim 0 SHTree.rootId →
      mem (nodeBase + 12 * id + 7) = r'.elim 0 SHTree.rootId →
      (∀ c, l = some c → TreeMemRep rt itemBase nodeBase mem c) →
      (∀ c, r' = some c → TreeMemRep rt itemBase nodeBase mem c) →
      TreeMemRep rt itemBase nodeBase mem (.node id r ck items l r')

private theorem TreeMemRep.rootId_ne {rt itemBase nodeBase : ℕ} {mem : ℕ → ℕ} {t : SHTree}
    (h : TreeMemRep rt itemBase nodeBase mem t) : t.rootId ≠ 0 := by cases h; assumption

private theorem TreeMemRep.ckey_eq {rt itemBase nodeBase : ℕ} {mem : ℕ → ℕ} {t : SHTree}
    (h : TreeMemRep rt itemBase nodeBase mem t) :
    mem (nodeBase + 12 * t.rootId) = t.ckey := by cases h; assumption

private theorem TreeMemRep.rank_eq {rt itemBase nodeBase : ℕ} {mem : ℕ → ℕ} {t : SHTree}
    (h : TreeMemRep rt itemBase nodeBase mem t) :
    mem (nodeBase + 12 * t.rootId + 1) = t.rank := by cases h; assumption

private theorem TreeMemRep.target_eq {rt itemBase nodeBase : ℕ} {mem : ℕ → ℕ} {t : SHTree}
    (h : TreeMemRep rt itemBase nodeBase mem t) :
    mem (nodeBase + 12 * t.rootId + 2) = targetSize rt t.rank := by cases h; assumption

private theorem TreeMemRep.size_eq {rt itemBase nodeBase : ℕ} {mem : ℕ → ℕ} {t : SHTree}
    (h : TreeMemRep rt itemBase nodeBase mem t) :
    mem (nodeBase + 12 * t.rootId + 3) = t.items.length := by cases h; assumption

private theorem TreeMemRep.items_rep {rt itemBase nodeBase : ℕ} {mem : ℕ → ℕ} {t : SHTree}
    (h : TreeMemRep rt itemBase nodeBase mem t) :
    ItemListRep itemBase mem (mem (nodeBase + 12 * t.rootId + 4))
      (mem (nodeBase + 12 * t.rootId + 5)) t.items := by cases h; assumption

private theorem TreeMemRep.left_eq {rt itemBase nodeBase : ℕ} {mem : ℕ → ℕ} {t : SHTree}
    (h : TreeMemRep rt itemBase nodeBase mem t) :
    mem (nodeBase + 12 * t.rootId + 6) = t.left.elim 0 SHTree.rootId := by cases h; assumption

private theorem TreeMemRep.right_eq {rt itemBase nodeBase : ℕ} {mem : ℕ → ℕ} {t : SHTree}
    (h : TreeMemRep rt itemBase nodeBase mem t) :
    mem (nodeBase + 12 * t.rootId + 7) = t.right.elim 0 SHTree.rootId := by cases h; assumption

private theorem TreeMemRep.left_mem {rt itemBase nodeBase : ℕ} {mem : ℕ → ℕ} {t : SHTree}
    (h : TreeMemRep rt itemBase nodeBase mem t) :
    ∀ c, t.left = some c → TreeMemRep rt itemBase nodeBase mem c := by cases h; assumption

private theorem TreeMemRep.right_mem {rt itemBase nodeBase : ℕ} {mem : ℕ → ℕ} {t : SHTree}
    (h : TreeMemRep rt itemBase nodeBase mem t) :
    ∀ c, t.right = some c → TreeMemRep rt itemBase nodeBase mem c := by cases h; assumption

/-- `TreeMemRep` depends only on node offsets `+0..+7` for `id ∈ t.nodeIds` and item offsets
`+0..+2` for `it ∈ t.allItems`. -/
theorem TreeMemRep.congr {rt itemBase nodeBase : ℕ} {mem₁ mem₂ : ℕ → ℕ} {t : SHTree}
    (hnode : ∀ id ∈ t.nodeIds, ∀ j < 8, mem₁ (nodeBase + 12 * id + j) =
      mem₂ (nodeBase + 12 * id + j))
    (hitem : ∀ it ∈ t.allItems, ∀ j < 3, mem₁ (itemBase + 3 * it.id + j) =
      mem₂ (itemBase + 3 * it.id + j))
    (hrep : TreeMemRep rt itemBase nodeBase mem₁ t) :
    TreeMemRep rt itemBase nodeBase mem₂ t := by
  induction t using SHTree.ind with
  | node id r ck items l r' ihL ihR =>
    rcases hrep with ⟨hid, h0, h1, h2, h3, h45, h6, h7, hl, hr⟩
    have hn : ∀ j < 8, mem₁ (nodeBase + 12 * id + j) = mem₂ (nodeBase + 12 * id + j) :=
      hnode id (by simp)
    have hi : ItemListRep itemBase mem₂ (mem₂ (nodeBase + 12 * id + 4))
        (mem₂ (nodeBase + 12 * id + 5)) items := by
      rw [← hn 4 (by decide), ← hn 5 (by decide)]
      exact ItemListRep.congr (fun it hit j hj => hitem it (by simp [SHTree.allItems, hit]) j hj)
        h45
    refine .node hid ?_ ?_ ?_ ?_ hi ?_ ?_ ?_ ?_
    · simpa using (hn 0 (by decide)).symm.trans h0
    · simpa using (hn 1 (by decide)).symm.trans h1
    · simpa using (hn 2 (by decide)).symm.trans h2
    · simpa using (hn 3 (by decide)).symm.trans h3
    · simpa using (hn 6 (by decide)).symm.trans h6
    · simpa using (hn 7 (by decide)).symm.trans h7
    · exact fun c hc => ihL c hc
        (fun nid hnid => hnode nid (by simp [hc, hnid]))
        (fun it hit => hitem it (by
          simp only [SHTree.allItems, SHTree.allEntries_node, hc, Option.elim_some,
            List.map_append, List.mem_append]
          exact Or.inl (Or.inr hit))) (hl c hc)
    · exact fun c hc => ihR c hc
        (fun nid hnid => hnode nid (by simp [hc, hnid]))
        (fun it hit => hitem it (by
          simp only [SHTree.allItems, SHTree.allEntries_node, hc, Option.elim_some,
            List.map_append, List.mem_append]
          exact Or.inr hit)) (hr c hc)

/-- Suffix-minimum root selector breaking ties to the front (`t.ckey ≤ sm.ckey`), matching
`updateSuffixMinStep` and `shInsertLinkRoot`. -/
@[expose] def suffixMinTree : List SHTree → Option SHTree
  | [] => none
  | [t] => some t
  | t :: rest =>
      match suffixMinTree rest with
      | none => some t
      | some sm => if t.ckey ≤ sm.ckey then some t else some sm

/-- `suffixMinTree` returns a member of `roots` with minimum `ckey` whenever `roots ≠ []`. -/
private theorem suffixMinTree_spec (roots : List SHTree) :
    match suffixMinTree roots with
    | none => roots = []
    | some sm => sm ∈ roots ∧ ∀ t ∈ roots, sm.ckey ≤ t.ckey := by
  induction roots with
  | nil => simp [suffixMinTree]
  | cons t rest ih =>
    cases rest with
    | nil => simp [suffixMinTree]
    | cons t2 rest2 =>
      simp only [suffixMinTree]
      cases hsm : suffixMinTree (t2 :: rest2) with
      | none => simp [hsm] at ih
      | some sm =>
        rw [hsm] at ih
        rcases ih with ⟨hmem, hmin⟩
        dsimp only
        split_ifs with hle
        · exact ⟨by simp, fun u hu =>
            (List.mem_cons.mp hu).elim (fun h => h ▸ le_rfl) fun hu' => hle.trans (hmin u hu')⟩
        · exact ⟨by simp [hmem], fun u hu =>
            (List.mem_cons.mp hu).elim (fun h => h ▸ Nat.le_of_not_ge hle) (hmin u)⟩

/-- Doubly-linked root-list links (`+9 prevRoot`, `+10 nextRoot`, `+11 suffixMin`) with strictly
increasing ranks. -/
@[expose] def RootListRep (nodeBase : ℕ) (mem : ℕ → ℕ) (prev : ℕ) : List SHTree → Prop
  | [] => True
  | t :: rest =>
      (∀ u ∈ rest, t.rank < u.rank) ∧
      mem (nodeBase + 12 * t.rootId + 9) = prev ∧
      mem (nodeBase + 12 * t.rootId + 10) = rest.head?.elim 0 SHTree.rootId ∧
      mem (nodeBase + 12 * t.rootId + 11) =
        (suffixMinTree (t :: rest)).elim 0 SHTree.rootId ∧
      RootListRep nodeBase mem t.rootId rest

/-- `RootListRep` implies pairwise strictly increasing root ranks. -/
private theorem RootListRep.pairwise_rank {nodeBase : ℕ} {mem : ℕ → ℕ} {prev : ℕ}
    {roots : List SHTree} (h : RootListRep nodeBase mem prev roots) :
    roots.Pairwise (fun a b => a.rank < b.rank) := by
  induction roots generalizing prev with
  | nil => simp
  | cons t rest ih =>
    exact List.pairwise_cons.mpr ⟨h.1, ih h.2.2.2.2⟩

/-- Framing lemma for `RootListRep`: if `mem₁` and `mem₂` agree on `{9, 10, 11}` of every root
in `roots`, then `RootListRep` is preserved. -/
theorem RootListRep.congr {nodeBase : ℕ} {mem₁ mem₂ : ℕ → ℕ} {prev : ℕ}
    {roots : List SHTree}
    (hagree : ∀ t ∈ roots, ∀ j, j = 9 ∨ j = 10 ∨ j = 11 →
      mem₁ (nodeBase + 12 * t.rootId + j) = mem₂ (nodeBase + 12 * t.rootId + j))
    (hrep : RootListRep nodeBase mem₁ prev roots) :
    RootListRep nodeBase mem₂ prev roots := by
  induction roots generalizing prev with
  | nil => trivial
  | cons t rest ih =>
    rcases hrep with ⟨hrank, h9, h10, h11, hrest⟩
    refine ⟨hrank, ?_, ?_, ?_, ih (fun u hu => hagree u (by simp [hu])) hrest⟩
    · rw [← hagree t (by simp) 9 (Or.inl rfl)]; exact h9
    · rw [← hagree t (by simp) 10 (Or.inr (Or.inl rfl))]; exact h10
    · rw [← hagree t (by simp) 11 (Or.inr (Or.inr rfl))]; exact h11

/-- Complete invariant for a dynamic soft heap operating in a pool slice `(ic₀, nc₀)` up to
capacities `(maxItems, maxNodes)` with amortized root list `roots` and rank birth counts
`created`. -/
structure SHInv (w ic₀ nc₀ maxItems maxNodes : ℕ) (h : SHHandle)
    (roots : List SHTree) (created : ℕ → ℕ) (s : Memory.State) : Prop where
  /-- Word size at least 17 bits (`Fits w 16`). -/
  fits16 : Fits w 16
  /-- Well-formed memory state. -/
  wf : Memory.WellFormed w s
  /-- Initial item floor. -/
  ic_le : ic₀ ≤ h.itemCount
  /-- Item capacity bound. -/
  ic_max : h.itemCount ≤ maxItems
  /-- Initial node floor. -/
  nc_le : nc₀ ≤ h.nodeCount
  /-- Node capacity bound. -/
  nc_max : h.nodeCount ≤ maxNodes
  /-- Guaranteed node pool headroom for `2 * (maxItems - ic₀)` allocated nodes. -/
  pool_cap : nc₀ + 2 * (maxItems - ic₀) ≤ maxNodes
  /-- Binomial forest bound `(nodeCount - nc₀) + roots.length ≤ 2 * (itemCount - ic₀)`. -/
  nc_roots_le : (h.nodeCount - nc₀) + roots.length ≤ 2 * (h.itemCount - ic₀)
  /-- Item pool lies below `s.frontier`. -/
  item_pool_lt : h.itemBase + 3 * (maxItems + 1) ≤ s.frontier
  /-- Node pool lies below `s.frontier`. -/
  node_pool_lt : h.nodeBase + 12 * (maxNodes + 1) ≤ s.frontier
  /-- Item and node pools are disjoint. -/
  pools_disj : h.itemBase + 3 * (maxItems + 1) ≤ h.nodeBase ∨
    h.nodeBase + 12 * (maxNodes + 1) ≤ h.itemBase
  /-- `defill` fuel fits in a machine word. -/
  fits_fuel : Fits w (shFuelBound h.rankThreshold maxItems)
  /-- All live node IDs are distinct. -/
  nodeIds_nodup : (forestNodeIds roots).Nodup
  /-- All live node IDs lie in `(nc₀, h.nodeCount]`. -/
  nodeIds_range : ∀ id ∈ forestNodeIds roots, nc₀ < id ∧ id ≤ h.nodeCount
  /-- All live item IDs are distinct. -/
  itemIds_nodup : (forestItemIds roots).Nodup
  /-- All live item IDs lie in `(ic₀, h.itemCount]`. -/
  itemIds_range : ∀ id ∈ forestItemIds roots, ic₀ < id ∧ id ≤ h.itemCount
  /-- Deallocated nodes in `(nc₀, h.nodeCount]` have `head = 0` so `shCollectCorrupted`
  skips them. -/
  dead_nodes_empty : ∀ idx, nc₀ < idx → idx ≤ h.nodeCount →
    idx ∉ forestNodeIds roots → s.mem (h.nodeBase + 12 * idx + 4) = 0
  /-- All root trees satisfy `SHTree.Valid h.rankThreshold 0`. -/
  trees_valid : ∀ t ∈ roots, t.Valid h.rankThreshold 0
  /-- All root trees match memory offsets `+0..+7`. -/
  trees_mem : ∀ t ∈ roots, TreeMemRep h.rankThreshold h.itemBase h.nodeBase s.mem t
  /-- Root list pointers and suffix minima match `roots`. -/
  rootList : RootListRep h.nodeBase s.mem 0 roots
  /-- Handle `firstRoot` equals head of `roots` (or `0` when empty). -/
  firstRoot_eq : h.firstRoot = roots.head?.elim 0 SHTree.rootId
  /-- `created 0` equals total items inserted since `ic₀`. -/
  created_zero : created 0 = h.itemCount - ic₀
  /-- Amortized birth inequality across ranks. -/
  created_step : ∀ k, 2 * created (k + 1) +
    roots.countP (fun t => decide (t.rank = k)) ≤ created k
  /-- Total live nodes at rank `k` are bounded by `created k`. -/
  live_rank_le : ∀ k, (roots.map (SHTree.countRank k)).sum ≤ created k
  /-- Root ranks are bounded by `h.nodeCount - nc₀`. -/
  rank_le : ∀ t ∈ roots, t.rank ≤ h.nodeCount - nc₀

private theorem subperm_length_fits {w B : ℕ} {xs ys : List ℕ}
    (hsub : ∀ x ∈ xs, x ∈ ys) (hxs : xs.Nodup)
    (hle : ∀ y ∈ ys, y < B) (hB : B < 2 ^ w) : Fits w xs.length := by
  have hlen : xs.length ≤ B := List.length_le_of_nodup_lt hxs (fun x hx => hle x (hsub x hx))
  exact Nat.lt_of_le_of_lt hlen hB

private theorem list_nodup_append_disj {α : Type} {xs ys : List α}
    (h : (xs ++ ys).Nodup) : xs.Nodup ∧ ys.Nodup ∧ ∀ x ∈ xs, x ∉ ys :=
  ⟨(List.nodup_append.mp h).1, (List.nodup_append.mp h).2.1,
    fun x hx hy => (List.nodup_append.mp h).2.2 x hx x hy rfl⟩


private theorem SHTree.allItems_node (id r ck : ℕ) (items : List SHItem)
    (l r' : Option SHTree) :
    (SHTree.node id r ck items l r').allItems =
      items ++ l.elim [] SHTree.allItems ++ r'.elim [] SHTree.allItems := by
  simp only [SHTree.allItems, SHTree.allEntries_node, List.map_append, List.map_map]
  cases l <;> cases r' <;> simp [SHTree.allItems, Function.comp_def]

private theorem SHTree.itemIds_node (id r ck : ℕ) (items : List SHItem)
    (l r' : Option SHTree) :
    (SHTree.node id r ck items l r').itemIds =
      items.map SHItem.id ++ l.elim [] SHTree.itemIds ++ r'.elim [] SHTree.itemIds := by
  simp only [SHTree.itemIds, SHTree.allItems_node, List.map_append]
  cases l <;> cases r' <;> simp [SHTree.itemIds]

private theorem SHTree.nodeIds_head_not_mem {id r ck : ℕ} {items : List SHItem}
    {l r' : Option SHTree} (h : (SHTree.node id r ck items l r').nodeIds.Nodup) :
    id ∉ l.elim [] SHTree.nodeIds ++ r'.elim [] SHTree.nodeIds := by
  rw [SHTree.nodeIds_node, List.cons_append, List.nodup_cons] at h
  exact h.1


private theorem whileSafe_succ_pos {δ σ : Type}
    {guard : δ → σ → Prop} [∀ d a, Decidable (guard d a)]
    {body : δ × σ → Memory.Prog σ} {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {w : ℕ} {d : δ} {n : ℕ} {a : σ} {s : Memory.State}
    (hg : guard d a) (hs : safe w (d, a) s)
    (hnext : whileSafe guard body safe w d n
      ((Memory.spec 0).clientResult s (body (d, a)))
      ((Memory.spec 0).clientState s (body (d, a)))) :
    whileSafe guard body safe w d (n + 1) a s := by
  simp only [whileSafe, hg, ↓reduceIte]
  exact ⟨hs, hnext⟩

private theorem whileSafe_of_not {δ σ : Type}
    {guard : δ → σ → Prop} [∀ d a, Decidable (guard d a)]
    {body : δ × σ → Memory.Prog σ} {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {w : ℕ} {d : δ} {n : ℕ} {a : σ} {s : Memory.State}
    (hg : ¬ guard d a) : whileSafe guard body safe w d n a s := by
  cases n <;> simp [whileSafe, hg]


/-- Potential of an empty soft-heap root list is `0`. -/
@[simp] theorem totalPhi_nil (rt : ℕ) : totalPhi rt [] = 0 := by
  simp [totalPhi]

/-- Potential of `t :: ts` splits into root `t` and tail `ts`. -/
@[simp] theorem totalPhi_cons (rt : ℕ) (t : SHTree) (ts : List SHTree) :
    totalPhi rt (t :: ts) = t.phi rt + rootCredit t.rank + popDeficit rt t + totalPhi rt ts := by
  simp [totalPhi]

/-- Potential distributes over list append. -/
theorem totalPhi_append (rt : ℕ) (xs ys : List SHTree) :
    totalPhi rt (xs ++ ys) = totalPhi rt xs + totalPhi rt ys := by
  simp [totalPhi, List.map_append, List.sum_append]

private theorem targetSize_le_two_pow (rt r : ℕ) : targetSize rt r ≤ 2 ^ r := by
  by_cases hr : r ≤ rt
  · rw [targetSize_le_threshold hr]; exact Nat.one_le_two_pow
  · simp only [targetSize, hr, ↓reduceIte]
    exact Nat.pow_le_pow_right (by decide) (by omega)

private theorem rootList_pre_length_le_rank {pre suf : List SHTree} {x : SHTree}
    (hpw : (pre ++ [x] ++ suf).Pairwise (fun a b => a.rank < b.rank)) :
    pre.length ≤ x.rank := by
  rw [List.append_assoc] at hpw
  rcases List.pairwise_append.mp hpw with ⟨h1, _, h2⟩
  rw [← List.length_map (as := pre) (f := SHTree.rank)]
  refine List.length_le_of_nodup_lt ((List.pairwise_map.mpr h1).imp fun h => Nat.ne_of_lt h)
    fun r hr => ?_
  rcases List.mem_map.mp hr with ⟨u, hu, rfl⟩
  exact h2 u hu x (by simp)

private theorem SHInv.pools_disj_node_item {w ic₀ nc₀ maxItems maxNodes : ℕ}
    {h : SHHandle} {roots : List SHTree} {created : ℕ → ℕ} {s : Memory.State}
    (hinv : SHInv w ic₀ nc₀ maxItems maxNodes h roots created s)
    {nid iid j k : ℕ} (hnid : nid ≤ maxNodes) (hiid : iid ≤ maxItems)
    (hj : j < 12) (hk : k < 3) :
    h.nodeBase + 12 * nid + j ≠ h.itemBase + 3 * iid + k := by
  rcases hinv.pools_disj with hd | hd <;> omega

private theorem tree_phi_le_fuel {rt ic₀ nc₀ maxItems : ℕ} {t : SHTree}
    (hid_nd : t.itemIds.Nodup)
    (hid_rng : ∀ id ∈ t.itemIds, ic₀ < id ∧ id ≤ maxItems)
    (hnd : t.nodeIds.Nodup)
    (hnd_rng : ∀ id ∈ t.nodeIds, nc₀ < id ∧ id ≤ nc₀ + 2 * (maxItems - ic₀)) :
    t.phi rt + 5 ≤ 5 * ((shFuelBound rt maxItems : ℕ) : ℚ) := by
  have hit_nd : (t.itemIds.map (fun id => id - (ic₀ + 1))).Nodup := by
    refine List.Nodup.map_on ?_ hid_nd
    intro a ha b hb hab
    have := (hid_rng a ha).1
    have := (hid_rng b hb).1
    omega
  have hall_len : t.allItems.length ≤ maxItems := by
    rw [← List.length_map (f := SHItem.id), ← List.length_map (f := fun id => id - (ic₀ + 1))]
    refine List.length_le_of_nodup_lt hit_nd ?_
    intro y hy
    rcases List.mem_map.mp hy with ⟨id, hid, rfl⟩
    have := hid_rng id hid
    omega
  have hnc_nd : (t.nodeIds.map (fun id => id - (nc₀ + 1))).Nodup := by
    refine List.Nodup.map_on ?_ hnd
    intro a ha b hb hab
    have := (hnd_rng a ha).1
    have := (hnd_rng b hb).1
    omega
  have hnc_len : t.nodeCount ≤ 2 * maxItems := by
    rw [← t.nodeIds_length, ← List.length_map (fun id => id - (nc₀ + 1))]
    refine List.length_le_of_nodup_lt hnc_nd ?_
    intro y hy
    rcases List.mem_map.mp hy with ⟨id, hid, rfl⟩
    have := hnd_rng id hid
    omega
  have hphi_it : t.itemPhiSum rt ≤ (2 * (rt : ℚ) + 3) * (t.allItems.length : ℚ) := by
    simpa [SHTree.allItems] using t.itemPhiSum_le rt
  have hall_q : (t.allItems.length : ℚ) ≤ (maxItems : ℚ) := by exact_mod_cast hall_len
  have hnc_q : (t.nodeCount : ℚ) ≤ 2 * (maxItems : ℚ) := by exact_mod_cast hnc_len
  have hmul : (2 * (rt : ℚ) + 3) * (t.allItems.length : ℚ) ≤
      (2 * (rt : ℚ) + 3) * (maxItems : ℚ) :=
    mul_le_mul_of_nonneg_left hall_q (by positivity)
  have hrtm : (0 : ℚ) ≤ (rt : ℚ) * (maxItems : ℚ) := by positivity
  unfold SHTree.phi shFuelBound
  push_cast
  linarith

/-- Empty initial Soft Heap invariant at handle
`⟨itemBase, nodeBase, 0, ic₀, nc₀, rankThreshold⟩`. -/
theorem shInit_inv {w itemBase nodeBase ic₀ nc₀ maxItems maxNodes rankThreshold : ℕ}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hic : ic₀ ≤ maxItems) (hcap : nc₀ + 2 * (maxItems - ic₀) ≤ maxNodes)
    (hi_lt : itemBase + 3 * (maxItems + 1) ≤ s.frontier)
    (hn_lt : nodeBase + 12 * (maxNodes + 1) ≤ s.frontier)
    (hdisj : itemBase + 3 * (maxItems + 1) ≤ nodeBase ∨
      nodeBase + 12 * (maxNodes + 1) ≤ itemBase)
    (hfuel : Fits w (shFuelBound rankThreshold maxItems)) :
    SHInv w ic₀ nc₀ maxItems maxNodes
      ⟨itemBase, nodeBase, 0, ic₀, nc₀, rankThreshold⟩ [] (fun _ => 0) s := by
  refine ⟨h16, hwf, le_rfl, hic, le_rfl, by dsimp; omega, hcap, by simp, hi_lt, hn_lt, hdisj,
    hfuel, by simp [forestNodeIds], fun _ h => by simp [forestNodeIds] at h,
    by simp [forestItemIds], fun _ h => by simp [forestItemIds] at h,
    fun idx h1 h2 => absurd h1 (by dsimp at h2; omega),
    fun _ h => by simp at h, fun _ h => by simp at h, trivial, rfl,
    by simp, fun _ => by simp, fun _ => by simp, fun _ h => by simp at h⟩

/-- Pool allocator specification returning disjoint `(itemBase, nodeBase)` blocks below the
updated frontier at exact cost `2`. -/
theorem allocPool_spec {w maxItems maxNodes : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hfit : Fits w (s.frontier + 3 * (maxItems + 1) + 12 * (maxNodes + 1) + 16)) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (allocPool maxItems maxNodes)) ∧
    memoryCost (allocPool maxItems maxNodes) s = 2 ∧
    let res := (Memory.spec 0).clientResult s (allocPool maxItems maxNodes)
    let s' := (Memory.spec 0).clientState s (allocPool maxItems maxNodes)
    res.1 = s.frontier ∧
    res.2 = s.frontier + 3 * (maxItems + 1) ∧
    s'.frontier = s.frontier + 3 * (maxItems + 1) + 12 * (maxNodes + 1) ∧
    (∀ a < s.frontier, s'.mem a = s.mem a) ∧
    Memory.WellFormed w s' := by
  have hk1 : Fits w (s.frontier + 3 * (maxItems + 1)) := hfit.of_le (by omega)
  have hk2 : Fits w (s.frontier + 3 * (maxItems + 1) + 12 * (maxNodes + 1)) :=
    hfit.of_le (by omega)
  have hv : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (allocPool maxItems maxNodes)) := by
    dsimp only [allocPool]
    exact validHistory_allocDirty_bind hk1 (validHistory_allocDirty_bind hk2
      (validHistory_pure w _ _))
  have hm : memoryCost (allocPool maxItems maxNodes) s = 2 := by
    dsimp only [allocPool]
    rw [memoryCost_bind', memoryCost_allocDirty, clientState_allocDirty, memoryCost_bind',
      memoryCost_allocDirty, memoryCost_pure, add_zero]
  have hres : (Memory.spec 0).clientResult s (allocPool maxItems maxNodes) =
      (s.frontier, s.frontier + 3 * (maxItems + 1)) := by
    dsimp only [allocPool]
    rw [StateTransitionSpec.clientResult_bind, clientState_allocDirty, clientResult_allocDirty,
      StateTransitionSpec.clientResult_bind, clientResult_allocDirty]
    rfl
  have hs' : (Memory.spec 0).clientState s (allocPool maxItems maxNodes) =
      ⟨s.mem, s.frontier + 3 * (maxItems + 1) + 12 * (maxNodes + 1)⟩ := by
    dsimp only [allocPool]
    rw [StateTransitionSpec.clientState_bind, clientState_allocDirty,
      StateTransitionSpec.clientState_bind, clientState_allocDirty]
    rfl
  exact ⟨hv, hm, congrArg Prod.fst hres, congrArg Prod.snd hres,
    by simp [hs', Nat.add_assoc],
    fun _ _ => by simp [hs'], wellFormed_clientState hwf hv⟩

private def RootListLinksOnly (nodeBase : ℕ) (mem : ℕ → ℕ) (prev : ℕ) (suf : List SHTree) :
    List SHTree → Prop
  | [] => True
  | t :: rest =>
      (∀ u ∈ rest ++ suf, t.rank < u.rank) ∧
      mem (nodeBase + 12 * t.rootId + 9) = prev ∧
      mem (nodeBase + 12 * t.rootId + 10) = (rest ++ suf).head?.elim 0 SHTree.rootId ∧
      RootListLinksOnly nodeBase mem t.rootId suf rest

private theorem rootListLinksOnly_of_rootListRep {nodeBase : ℕ} {mem : ℕ → ℕ} {prev : ℕ}
    {pre suf : List SHTree} (hrep : RootListRep nodeBase mem prev (pre ++ suf)) :
    RootListLinksOnly nodeBase mem prev suf pre := by
  induction pre generalizing prev with
  | nil => trivial
  | cons t rest ih =>
    rcases hrep with ⟨hrk, h9, h10, _, hrest⟩
    exact ⟨hrk, h9, h10, ih hrest⟩

private theorem rootListLinksOnly_congr {nodeBase : ℕ} {mem₁ mem₂ : ℕ → ℕ} {prev : ℕ}
    {pre suf : List SHTree}
    (hagree : ∀ t ∈ pre, ∀ j, j = 9 ∨ j = 10 →
      mem₁ (nodeBase + 12 * t.rootId + j) = mem₂ (nodeBase + 12 * t.rootId + j))
    (hrep : RootListLinksOnly nodeBase mem₁ prev suf pre) :
    RootListLinksOnly nodeBase mem₂ prev suf pre := by
  induction pre generalizing prev with
  | nil => trivial
  | cons t rest ih =>
    rcases hrep with ⟨hrk, h9, h10, hrest⟩
    refine ⟨hrk, ?_, ?_, ih (fun u hu => hagree u (by simp [hu])) hrest⟩
    · rw [← hagree t (by simp) 9 (Or.inl rfl)]; exact h9
    · rw [← hagree t (by simp) 10 (Or.inr rfl)]; exact h10

private theorem rootListLinksOnly_snoc {nodeBase : ℕ} {mem : ℕ → ℕ} {prev : ℕ}
    {pre suf : List SHTree} {x : SHTree} :
    RootListLinksOnly nodeBase mem prev suf (pre ++ [x]) ↔
      RootListLinksOnly nodeBase mem prev (x :: suf) pre ∧
      (∀ u ∈ suf, x.rank < u.rank) ∧
      mem (nodeBase + 12 * x.rootId + 9) = pre.getLast?.elim prev SHTree.rootId ∧
      mem (nodeBase + 12 * x.rootId + 10) = suf.head?.elim 0 SHTree.rootId := by
  induction pre generalizing prev with
  | nil =>
    simp only [List.nil_append, RootListLinksOnly, List.getLast?_nil, Option.elim_none,
      and_true, true_and]
  | cons a rest ih =>
    rw [List.cons_append]
    simp only [RootListLinksOnly, List.append_assoc, List.singleton_append]
    have hlast : (a :: rest).getLast?.elim prev SHTree.rootId =
        rest.getLast?.elim a.rootId SHTree.rootId := by
      cases rest <;> rfl
    have hhead : (rest ++ x :: suf).head? = ((rest ++ [x]) ++ suf).head? := by
      cases rest <;> simp [List.append_assoc]
    rw [ih, hlast, hhead]
    tauto

private theorem updateSuffixMinStep_spec {w nodeBase prev : ℕ} {s : Memory.State}
    {x : SHTree} {suf : List SHTree}
    (hwf : Memory.WellFormed w s)
    (hrk : ∀ u ∈ suf, x.rank < u.rank)
    (hx_9 : s.mem (nodeBase + 12 * x.rootId + 9) = prev)
    (hx_10 : s.mem (nodeBase + 12 * x.rootId + 10) = suf.head?.elim 0 SHTree.rootId)
    (hsuf_rep : RootListRep nodeBase s.mem x.rootId suf)
    (hinfo : ∀ t ∈ x :: suf, s.mem (nodeBase + 12 * t.rootId) = t.ckey ∧ 0 < t.rootId ∧
      nodeBase + 12 * t.rootId + 11 < s.frontier)
    (hnd : ((x :: suf).map SHTree.rootId).Nodup) :
    let d : Fin 2 → ℕ := ![nodeBase, x.rootId]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (updateSuffixMinStep d)) ∧
    memoryCost (updateSuffixMinStep d) s ≤ 6 ∧
    (Memory.spec 0).clientResult s (updateSuffixMinStep d) = prev ∧
    let s' := (Memory.spec 0).clientState s (updateSuffixMinStep d)
    s'.frontier = s.frontier ∧
    (∀ a, a ≠ nodeBase + 12 * x.rootId + 11 → s'.mem a = s.mem a) ∧
    RootListRep nodeBase s'.mem prev (x :: suf) := by
  obtain ⟨hx_ck, hx_pos, hx_lt⟩ := hinfo x (by simp)
  have hx_fit : Fits w x.rootId := hwf.fits_of_lt_frontier (by omega)
  cases suf with
  | nil =>
    have hn0 : ([] : List SHTree).head?.elim 0 SHTree.rootId = 0 := rfl
    rw [hn0] at hx_10
    have hv : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (updateSuffixMinStep ![nodeBase, x.rootId])) := by
      dsimp only [updateSuffixMinStep]
      simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
      simp only [hx_10, ↓reduceIte]
      exact validHistory_write_bind (by omega) hx_fit (validHistory_read_bind (by dsimp; omega)
        (validHistory_pure w _ _))
    have hm : memoryCost (updateSuffixMinStep ![nodeBase, x.rootId]) s ≤ 6 := by
      dsimp only [updateSuffixMinStep]
      simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one]
      repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
      simp only [hx_10, ↓reduceIte]
      rw [memoryCost_bind', memoryCost_write, clientState_write, memoryCost_read]
      decide
    have hres : (Memory.spec 0).clientResult s (updateSuffixMinStep ![nodeBase, x.rootId]) =
        prev := by
      dsimp only [updateSuffixMinStep]
      simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one]
      repeat rw [clientResult_bind_read]
      simp only [hx_10, ↓reduceIte]
      rw [StateTransitionSpec.clientResult_bind, clientState_write]
      simp only [clientResult_read]
      rw [Function.update_of_ne (by omega), hx_9]
    have hs' : (Memory.spec 0).clientState s (updateSuffixMinStep ![nodeBase, x.rootId]) =
        ⟨Function.update s.mem (nodeBase + 12 * x.rootId + 11) x.rootId, s.frontier⟩ := by
      dsimp only [updateSuffixMinStep]
      simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one]
      repeat rw [clientState_bind_read]
      simp only [hx_10, ↓reduceIte]
      rw [clientState_bind_write, clientState_read]
    refine ⟨hv, hm, hres, ?_, ?_, ?_⟩
    · simp [hs']
    · intro a ha; simp [hs', Function.update_of_ne ha]
    · simp only [RootListRep, hs']
      refine ⟨hrk, ?_, ?_, ?_, trivial⟩
      · rw [Function.update_of_ne (by omega)]; exact hx_9
      · rw [Function.update_of_ne (by omega)]; exact hx_10
      · rw [Function.update_self]; rfl
  | cons y suf' =>
    have hsm_spec := suffixMinTree_spec (y :: suf')
    cases hsm_eq : suffixMinTree (y :: suf') with
    | none => rw [hsm_eq] at hsm_spec; simp at hsm_spec
    | some sm =>
      rw [hsm_eq] at hsm_spec
      rcases hsm_spec with ⟨hsm_mem, _⟩
      obtain ⟨hy_ck, hy_pos, hy_lt⟩ := hinfo y (by simp)
      obtain ⟨hsm_ck, hsm_pos, hsm_lt⟩ := hinfo sm (by simp [hsm_mem])
      have hy_ne0 : y.rootId ≠ 0 := by omega
      have hx_10' : s.mem (nodeBase + 12 * x.rootId + 10) = y.rootId := by
        simpa using hx_10
      have hy_11 : s.mem (nodeBase + 12 * y.rootId + 11) = sm.rootId := by
        rcases hsuf_rep with ⟨_, _, _, h11, _⟩
        simpa [hsm_eq] using h11
      have hsm_fit : Fits w sm.rootId := hwf.fits_of_lt_frontier (by omega)
      have hv : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (updateSuffixMinStep ![nodeBase, x.rootId])) := by
        dsimp only [updateSuffixMinStep]
        simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one]
        refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
        simp only [hx_10', hy_ne0, ↓reduceIte]
        refine validHistory_read_bind (by omega) ?_
        rw [hy_11]
        refine validHistory_read_bind (by omega) ?_
        split_ifs
        · exact validHistory_write_bind (by omega) hx_fit (validHistory_read (by dsimp; omega))
        · exact validHistory_write_bind (by omega) hsm_fit (validHistory_read (by dsimp; omega))
      have hm : memoryCost (updateSuffixMinStep ![nodeBase, x.rootId]) s ≤ 6 := by
        dsimp only [updateSuffixMinStep]
        simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one]
        repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
        simp only [hx_10', hy_ne0, ↓reduceIte]
        repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
        rw [hy_11]
        split_ifs <;> rw [memoryCost_bind', memoryCost_write, memoryCost_read]
      have hres : (Memory.spec 0).clientResult s (updateSuffixMinStep ![nodeBase, x.rootId]) =
          prev := by
        dsimp only [updateSuffixMinStep]
        simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one]
        repeat rw [clientResult_bind_read]
        simp only [hx_10', hy_ne0, ↓reduceIte]
        repeat rw [clientResult_bind_read]
        rw [hy_11]
        split_ifs <;>
          (rw [StateTransitionSpec.clientResult_bind, clientState_write]
           simp [clientResult_read, hx_9])
      have hs' : (Memory.spec 0).clientState s (updateSuffixMinStep ![nodeBase, x.rootId]) =
          ⟨Function.update s.mem (nodeBase + 12 * x.rootId + 11)
            ((suffixMinTree (x :: y :: suf')).elim 0 SHTree.rootId), s.frontier⟩ := by
        dsimp only [updateSuffixMinStep]
        simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one]
        repeat rw [clientState_bind_read]
        simp only [hx_10', hy_ne0, ↓reduceIte]
        repeat rw [clientState_bind_read]
        rw [hy_11, hx_ck, hsm_ck]
        split_ifs with hck_le
        · rw [clientState_bind_write, clientState_read]; simp [suffixMinTree, hsm_eq, hck_le]
        · rw [clientState_bind_write, clientState_read]; simp [suffixMinTree, hsm_eq, hck_le]
      have hsuf_rep' : RootListRep nodeBase
          (Function.update s.mem (nodeBase + 12 * x.rootId + 11)
            ((suffixMinTree (x :: y :: suf')).elim 0 SHTree.rootId)) x.rootId (y :: suf') := by
        refine RootListRep.congr (fun t ht j hj => ?_) hsuf_rep
        have hne : t.rootId ≠ x.rootId := by
          rw [List.map_cons, List.nodup_cons] at hnd
          intro heq
          exact hnd.1 (heq ▸ List.mem_map_of_mem ht)
        rcases hj with rfl | rfl | rfl <;>
          exact (Function.update_of_ne (by omega) _ _).symm
      refine ⟨hv, hm, hres, ?_, ?_, ?_⟩
      · simp [hs']
      · intro a ha; simp [hs', Function.update_of_ne ha]
      · simp only [RootListRep, hs']
        refine ⟨hrk, ?_, ?_, ?_, hsuf_rep'⟩
        · rw [Function.update_of_ne (by omega)]; exact hx_9
        · rw [Function.update_of_ne (by omega)]; exact hx_10
        · rw [Function.update_self]

private theorem updateSuffixMinUp_while_spec {w nodeBase fuel : ℕ} {s : Memory.State}
    {pre suf : List SHTree}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hpre_links : RootListLinksOnly nodeBase s.mem 0 suf pre)
    (hsuf_rep : RootListRep nodeBase s.mem (pre.getLast?.elim 0 SHTree.rootId) suf)
    (hinfo : ∀ t ∈ pre ++ suf, s.mem (nodeBase + 12 * t.rootId) = t.ckey ∧ 0 < t.rootId ∧
      nodeBase + 12 * t.rootId + 11 < s.frontier)
    (hnd : ((pre ++ suf).map SHTree.rootId).Nodup)
    (hfuel : pre.length ≤ fuel) :
    let startIdx := pre.getLast?.elim 0 SHTree.rootId
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (boundedWhile (fun (_ : Unit) (cur : ℕ) => cur ≠ 0)
        (fun x => updateSuffixMinStep ![nodeBase, x.2]) () fuel startIdx)) ∧
    whileSafe (fun (_ : Unit) (cur : ℕ) => cur ≠ 0)
      (fun x : Unit × ℕ => updateSuffixMinStep ![nodeBase, x.2])
      (fun w _ _ => Fits w 16) w () fuel startIdx s ∧
    memoryCost (boundedWhile (fun (_ : Unit) (cur : ℕ) => cur ≠ 0)
      (fun x => updateSuffixMinStep ![nodeBase, x.2]) () fuel startIdx) s ≤ 6 * pre.length ∧
    let s' := (Memory.spec 0).clientState s
      (boundedWhile (fun (_ : Unit) (cur : ℕ) => cur ≠ 0)
        (fun x => updateSuffixMinStep ![nodeBase, x.2]) () fuel startIdx)
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a →
      ∃ t ∈ pre, a = nodeBase + 12 * t.rootId + 11) ∧
    RootListRep nodeBase s'.mem 0 (pre ++ suf) := by
  induction fuel generalizing pre suf s with
  | zero =>
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    simp only [List.getLast?_nil, Option.elim_none, List.length_nil, mul_zero, List.nil_append]
    rw [boundedWhile_of_not _ _ _ _ _ (by simp)]
    refine ⟨validHistory_pure w _ _, whileSafe_of_not (by simp), by simp [memoryCost_pure],
      rfl, fun _ h => absurd rfl h, hsuf_rep⟩
  | succ fuel' ih =>
    rcases List.eq_nil_or_concat' pre with rfl | ⟨pre', x, rfl⟩
    · simp only [List.getLast?_nil, Option.elim_none, List.length_nil, mul_zero, List.nil_append]
      rw [boundedWhile_of_not _ _ _ _ _ (by simp)]
      refine ⟨validHistory_pure w _ _, whileSafe_of_not (by simp), by simp [memoryCost_pure],
        rfl, fun _ h => absurd rfl h, hsuf_rep⟩
    · have hpre_links' := rootListLinksOnly_snoc.mp hpre_links
      rcases hpre_links' with ⟨hlinks', hrk_x, hx_9, hx_10⟩
      have hx_info := hinfo x (by simp)
      have hstart : (pre' ++ [x]).getLast?.elim 0 SHTree.rootId = x.rootId := by
        simp
      have hx_ne0 : x.rootId ≠ 0 := by omega
      have hnd' : ((x :: suf).map SHTree.rootId).Nodup := by
        have hsub : ((pre' ++ (x :: suf)).map SHTree.rootId).Nodup := by
          simpa [List.append_assoc] using hnd
        rw [List.map_append] at hsub
        exact (list_nodup_append_disj hsub).2.1
      have hstep := updateSuffixMinStep_spec hwf hrk_x hx_9 hx_10
        (by simpa [hstart] using hsuf_rep) (fun t ht => hinfo t (by simp at ht; simp [ht])) hnd'
      rcases hstep with ⟨hv_st, hm_st, hres_st, hfr_st, hmem_st, hrep_x⟩
      obtain ⟨s₁, hs₁_eq⟩ : ∃ s₁, s₁ = (Memory.spec 0).clientState s
          (updateSuffixMinStep ![nodeBase, x.rootId]) := ⟨_, rfl⟩
      rw [← hs₁_eq] at hfr_st hmem_st hrep_x
      have hwf₁ : Memory.WellFormed w s₁ := by
        rw [hs₁_eq]; exact wellFormed_clientState hwf hv_st
      have hlinks₁ : RootListLinksOnly nodeBase s₁.mem 0 (x :: suf) pre' := by
        refine rootListLinksOnly_congr (fun t ht j hj => ?_) hlinks'
        rcases hj with rfl | rfl <;> exact (hmem_st _ (by omega)).symm
      have hinfo₁ : ∀ t ∈ pre' ++ (x :: suf), s₁.mem (nodeBase + 12 * t.rootId) = t.ckey ∧
          0 < t.rootId ∧ nodeBase + 12 * t.rootId + 11 < s₁.frontier := by
        intro t ht
        have hi := hinfo t (by simp only [List.mem_append, List.mem_cons] at ht ⊢; tauto)
        refine ⟨?_, hi.2.1, hfr_st ▸ hi.2.2⟩
        rw [hmem_st _ (by omega)]; exact hi.1
      have hnd₁ : ((pre' ++ (x :: suf)).map SHTree.rootId).Nodup := by
        simpa [List.append_assoc] using hnd
      have hlen₁ : pre'.length ≤ fuel' := by
        simp only [List.length_append, List.length_singleton] at hfuel; omega
      have hih := ih hwf₁ hlinks₁ hrep_x hinfo₁ hnd₁ hlen₁
      rcases hih with ⟨hv_ih, hsafe_ih, hm_ih, hfr_ih, hmem_ih, hrep_ih⟩
      have hbw : boundedWhile (fun (_ : Unit) (cur : ℕ) => cur ≠ 0)
          (fun x => updateSuffixMinStep ![nodeBase, x.2]) () (fuel' + 1) x.rootId =
          (updateSuffixMinStep ![nodeBase, x.rootId] >>= fun nxt =>
            boundedWhile (fun (_ : Unit) (cur : ℕ) => cur ≠ 0)
              (fun x => updateSuffixMinStep ![nodeBase, x.2]) () fuel' nxt) := by
        simp [boundedWhile, hx_ne0]
      dsimp only
      rw [hstart]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hbw]
        refine validHistory_bind_step hv_st ?_
        rw [← hs₁_eq, hres_st]
        exact hv_ih
      · exact whileSafe_succ_pos hx_ne0 h16 (by rw [← hs₁_eq, hres_st]; exact hsafe_ih)
      · rw [hbw, memoryCost_bind', ← hs₁_eq, hres_st]
        simp only [List.length_append, List.length_singleton]
        omega
      · rw [hbw, StateTransitionSpec.clientState_bind, ← hs₁_eq, hres_st]
        exact hfr_ih.trans hfr_st
      · intro a ha
        rw [hbw, StateTransitionSpec.clientState_bind, ← hs₁_eq, hres_st] at ha
        by_cases h1 : ((Memory.spec 0).clientState s₁
            (boundedWhile (fun (_ : Unit) (cur : ℕ) => cur ≠ 0)
              (fun x => updateSuffixMinStep ![nodeBase, x.2]) () fuel'
              (pre'.getLast?.elim 0 SHTree.rootId))).mem a = s₁.mem a
        · rw [h1] at ha
          by_cases ha11 : a = nodeBase + 12 * x.rootId + 11
          · exact ⟨x, by simp, ha11⟩
          · exact absurd (hmem_st a ha11) ha
        · rcases hmem_ih a h1 with ⟨t, ht, ha'⟩
          exact ⟨t, by simp [ht], ha'⟩
      · rw [hbw, StateTransitionSpec.clientState_bind, ← hs₁_eq, hres_st]
        simpa [List.append_assoc] using hrep_ih

private theorem updateSuffixMinUp_spec {w nodeBase fuel : ℕ} {s : Memory.State}
    {pre suf : List SHTree}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hpre_links : RootListLinksOnly nodeBase s.mem 0 suf pre)
    (hsuf_rep : RootListRep nodeBase s.mem (pre.getLast?.elim 0 SHTree.rootId) suf)
    (hinfo : ∀ t ∈ pre ++ suf, s.mem (nodeBase + 12 * t.rootId) = t.ckey ∧ 0 < t.rootId ∧
      nodeBase + 12 * t.rootId + 11 < s.frontier)
    (hnd : ((pre ++ suf).map SHTree.rootId).Nodup)
    (hfuel : pre.length ≤ fuel) :
    let startIdx := pre.getLast?.elim 0 SHTree.rootId
    let d : Fin 3 → ℕ := ![nodeBase, startIdx, fuel]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (updateSuffixMinUp d)) ∧
    updateSuffixMinSafe w d s ∧
    memoryCost (updateSuffixMinUp d) s ≤ 6 * pre.length ∧
    let s' := (Memory.spec 0).clientState s (updateSuffixMinUp d)
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a →
      ∃ t ∈ pre, a = nodeBase + 12 * t.rootId + 11) ∧
    RootListRep nodeBase s'.mem 0 (pre ++ suf) := by
  have hbw := updateSuffixMinUp_while_spec h16 hwf hpre_links hsuf_rep hinfo hnd hfuel
  rcases hbw with ⟨hv_bw, hsafe_bw, hm_bw, hfr_bw, hmem_bw, hrep_bw⟩
  have hstate : (Memory.spec 0).clientState s
      (updateSuffixMinUp ![nodeBase, pre.getLast?.elim 0 SHTree.rootId, fuel]) =
      (Memory.spec 0).clientState s
        (boundedWhile (fun (_ : Unit) (cur : ℕ) => cur ≠ 0)
          (fun x => updateSuffixMinStep ![nodeBase, x.2]) () fuel
          (pre.getLast?.elim 0 SHTree.rootId)) := by
    dsimp only [updateSuffixMinUp]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [StateTransitionSpec.clientState_bind]
    rfl
  have hm : memoryCost (updateSuffixMinUp ![nodeBase, pre.getLast?.elim 0 SHTree.rootId, fuel]) s ≤
      6 * pre.length := by
    dsimp only [updateSuffixMinUp]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [memoryCost_bind', memoryCost_pure, add_zero]
    exact hm_bw
  refine ⟨?_, ⟨h16, hsafe_bw⟩, hm, ?_, ?_, ?_⟩
  · dsimp only [updateSuffixMinUp]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    exact validHistory_bind_step hv_bw (validHistory_pure w _ _)
  · rw [hstate]; exact hfr_bw
  · intro a ha; rw [hstate] at ha; exact hmem_bw a ha
  · rw [hstate]; exact hrep_bw

private def InPoolRaw (ic₀ nc₀ maxItems maxNodes itemBase nodeBase a : ℕ) : Prop :=
  (itemBase + 3 * (ic₀ + 1) ≤ a ∧ a < itemBase + 3 * (maxItems + 1)) ∨
  (nodeBase + 12 * (nc₀ + 1) ≤ a ∧ a < nodeBase + 12 * (maxNodes + 1))

private theorem inPoolRaw_iff_inSHPool {ic₀ nc₀ maxItems maxNodes : ℕ} {h : SHHandle} {a : ℕ} :
    InPoolRaw ic₀ nc₀ maxItems maxNodes h.itemBase h.nodeBase a ↔
      InSHPool ic₀ nc₀ maxItems maxNodes h a :=
  Iff.rfl

private theorem mem_forestNodeIds {t : SHTree} {roots : List SHTree} (ht : t ∈ roots)
    {id : ℕ} (hid : id ∈ t.nodeIds) : id ∈ forestNodeIds roots :=
  List.mem_flatMap.mpr ⟨t, ht, hid⟩

private theorem mem_forestItemIds {t : SHTree} {roots : List SHTree} (ht : t ∈ roots)
    {it : SHItem} (hit : it ∈ t.allItems) : it.id ∈ forestItemIds roots :=
  List.mem_flatMap.mpr ⟨t, ht, List.mem_map_of_mem hit⟩


private theorem SHTree.Valid.rank_le_of_countRank_pos {rt lb r : ℕ} {t : SHTree}
    (ht : t.Valid rt lb) (hpos : 0 < t.countRank r) : r ≤ t.rank := by
  induction t using SHTree.ind generalizing lb with
  | node id rk ck items l r' ihL ihR =>
    rcases ht with ⟨_, _, _, _, _, _, hlr, hlv, hrr, hrv⟩
    simp only [SHTree.countRank_node] at hpos
    dsimp only [SHTree.rank]
    split_ifs at hpos with heq
    · omega
    · have hcase : 0 < l.elim 0 (SHTree.countRank r) ∨
          0 < r'.elim 0 (SHTree.countRank r) := by omega
      rcases hcase with hl | hr
      · cases hl_eq : l with
        | none => rw [hl_eq] at hl; simp at hl
        | some c =>
          rw [hl_eq] at hl
          have hcr := hlr c hl_eq
          have hle := ihL c hl_eq (hlv c hl_eq) hl
          omega
      · cases hr_eq : r' with
        | none => rw [hr_eq] at hr; simp at hr
        | some c =>
          rw [hr_eq] at hr
          have hcr := hrr c hr_eq
          have hle := ihR c hr_eq (hrv c hr_eq) hr
          omega

private theorem forest_corrupted_le {rt K : ℕ} {roots : List SHTree}
    (hval : ∀ t ∈ roots, t.Valid rt 0) (hrk : ∀ t ∈ roots, t.rank ≤ K) :
    ((forestEntries roots).filter (fun p => decide (p.1.origKey < p.2))).length ≤
      ∑ k ∈ Finset.Icc (rt + 1) K, (roots.map (SHTree.countRank k)).sum * sizeCap rt k := by
  induction roots with
  | nil => simp [forestEntries]
  | cons t rest ih =>
    have ht_val := hval t List.mem_cons_self
    have ht_bd := SHTree.corrupted_le_sum_countRank (K := K) ht_val
      fun r hr => (ht_val.rank_le_of_countRank_pos hr).trans (hrk t List.mem_cons_self)
    have hrest := ih (fun u hu => hval u (List.mem_cons_of_mem _ hu))
      fun u hu => hrk u (List.mem_cons_of_mem _ hu)
    dsimp only [forestEntries] at hrest
    simp only [forestEntries, List.flatMap_cons, List.filter_append, List.length_append,
      List.map_cons, List.sum_cons, Nat.add_mul, Finset.sum_add_distrib]
    omega

/-- Every surviving entry in a valid soft heap has `origKey ≤ ckey` (keys are only ever
increased by corruption, never lowered). -/
theorem SHInv.origKey_le_ckey {w ic₀ nc₀ maxItems maxNodes : ℕ}
    {h : SHHandle} {roots : List SHTree} {created : ℕ → ℕ} {s : Memory.State}
    (hinv : SHInv w ic₀ nc₀ maxItems maxNodes h roots created s) :
    ∀ p ∈ forestEntries roots, p.1.origKey ≤ p.2 := by
  intro p hp
  rcases List.mem_flatMap.mp hp with ⟨t, ht, hpt⟩
  exact (hinv.trees_valid t ht).origKey_le_allEntries p hpt

/-- Global corruption bound under `SHInv` (from this module's `12 / 2 ^ r` `sizeCap`
recurrence): `2 ^ h.rankThreshold * #corrupted ≤ 12 * (h.itemCount - ic₀)` for any threshold. -/
theorem shInv_corrupted_le {w ic₀ nc₀ maxItems maxNodes : ℕ}
    {h : SHHandle} {roots : List SHTree} {created : ℕ → ℕ} {s : Memory.State}
    (hinv : SHInv w ic₀ nc₀ maxItems maxNodes h roots created s) :
    2 ^ h.rankThreshold *
      ((forestEntries roots).filter (fun p => decide (p.1.origKey < p.2))).length ≤
      12 * (h.itemCount - ic₀) := by
  have h1 := forest_corrupted_le hinv.trees_valid hinv.rank_le
  have hmono := Finset.sum_le_sum (s := Finset.Icc (h.rankThreshold + 1) (h.nodeCount - nc₀))
    fun k _ => Nat.mul_le_mul_right (sizeCap h.rankThreshold k) (hinv.live_rank_le k)
  have hc := corrupt_sum_bound h.rankThreshold created (h.nodeCount - nc₀)
    fun k => Nat.le_of_add_right_le (hinv.created_step k)
  rw [hinv.created_zero] at hc
  exact (Nat.mul_le_mul_left (2 ^ h.rankThreshold) (h1.trans hmono)).trans hc

/-- Rational error-rate specialization under `SHInv`: when `h.rankThreshold = rankThresholdForEps ε`
with `0 < ε`, at most `ε * (h.itemCount - ic₀)` surviving items are corrupted. -/
theorem shInv_corrupted_le_eps {ε : ℚ} (hε : 0 < ε)
    {w ic₀ nc₀ maxItems maxNodes : ℕ}
    {h : SHHandle} {roots : List SHTree} {created : ℕ → ℕ} {s : Memory.State}
    (hinv : SHInv w ic₀ nc₀ maxItems maxNodes h roots created s)
    (hrt : h.rankThreshold = rankThresholdForEps ε) :
    (((forestEntries roots).filter (fun p => decide (p.1.origKey < p.2))).length : ℚ) ≤
      ε * ((h.itemCount - ic₀ : ℕ) : ℚ) :=
  rat_le_eps_mul_of_pow_mul_le hε (hrt ▸ shInv_corrupted_le hinv)

/-- `SHInv` is preserved under memory updates outside `InSHPool` that keep `WellFormed` and
`frontier`. -/
theorem SHInv.congr_outside {w ic₀ nc₀ maxItems maxNodes : ℕ}
    {h : SHHandle} {roots : List SHTree} {created : ℕ → ℕ} {s s' : Memory.State}
    (hinv : SHInv w ic₀ nc₀ maxItems maxNodes h roots created s)
    (hwf' : Memory.WellFormed w s') (hfr' : s'.frontier = s.frontier)
    (hagree : ∀ a, InSHPool ic₀ nc₀ maxItems maxNodes h a → s'.mem a = s.mem a) :
    SHInv w ic₀ nc₀ maxItems maxNodes h roots created s' := by
  refine ⟨hinv.fits16, hwf', hinv.ic_le, hinv.ic_max, hinv.nc_le, hinv.nc_max, hinv.pool_cap,
    hinv.nc_roots_le, hfr' ▸ hinv.item_pool_lt, hfr' ▸ hinv.node_pool_lt, hinv.pools_disj,
    hinv.fits_fuel, hinv.nodeIds_nodup, hinv.nodeIds_range, hinv.itemIds_nodup,
    hinv.itemIds_range, ?_, hinv.trees_valid, ?_, ?_, hinv.firstRoot_eq, hinv.created_zero,
    hinv.created_step, hinv.live_rank_le, hinv.rank_le⟩
  · intro idx h1 h2 hnot
    have := hinv.nc_max
    rw [hagree (h.nodeBase + 12 * idx + 4) (Or.inr ⟨by omega, by omega⟩)]
    exact hinv.dead_nodes_empty idx h1 h2 hnot
  · intro t ht
    refine TreeMemRep.congr (fun id hid j hj => ?_) (fun it hit k hk => ?_)
      (hinv.trees_mem t ht)
    · have := hinv.nodeIds_range id (mem_forestNodeIds ht hid)
      have := hinv.nc_max
      exact (hagree (h.nodeBase + 12 * id + j) (Or.inr ⟨by omega, by omega⟩)).symm
    · have := hinv.itemIds_range it.id (mem_forestItemIds ht hit)
      have := hinv.ic_max
      exact (hagree (h.itemBase + 3 * it.id + k) (Or.inl ⟨by omega, by omega⟩)).symm
  · refine RootListRep.congr (fun t ht j hj => ?_) hinv.rootList
    have := hinv.nodeIds_range t.rootId (mem_forestNodeIds ht t.rootId_mem_nodeIds)
    have := hinv.nc_max
    rcases hj with rfl | rfl | rfl <;>
      exact (hagree _ (Or.inr ⟨by omega, by omega⟩)).symm

private theorem SHInv.forestEntries_length_le {w ic₀ nc₀ maxItems maxNodes : ℕ}
    {h : SHHandle} {roots : List SHTree} {created : ℕ → ℕ} {s : Memory.State}
    (hinv : SHInv w ic₀ nc₀ maxItems maxNodes h roots created s) :
    (forestEntries roots).length ≤ h.itemCount - ic₀ := by
  have hlen : (forestItemIds roots).length = (forestEntries roots).length := by
    simp [forestItemIds, forestEntries, SHTree.itemIds, SHTree.allItems]
  have hnd : ((forestItemIds roots).map (fun id => id - (ic₀ + 1))).Nodup := by
    refine List.Nodup.map_on ?_ hinv.itemIds_nodup
    intro a ha b hb _
    have ha' := (hinv.itemIds_range a ha).1
    have hb' := (hinv.itemIds_range b hb).1
    omega
  have hle : (forestItemIds roots).length ≤ h.itemCount - ic₀ := by
    rw [← List.length_map (f := fun id => id - (ic₀ + 1))]
    refine List.length_le_of_nodup_lt hnd ?_
    intro y hy
    rcases List.mem_map.mp hy with ⟨id, hid, rfl⟩
    have hid' := hinv.itemIds_range id hid
    omega
  omega

end Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap
