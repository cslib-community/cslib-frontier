/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.InstDP
public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.Scan
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Tactic.Realize
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Node-descriptor layout, telescoping table-entry sum, and `initNodesProg`

This module defines the memory-layout invariant `NodeLayout` for all `numNodes + 1` bag descriptors
and DP tables, the telescoping prefix-maximum potential `prefixMaxSum` that prevents `2 ^ numNodes`
table-entry growth, and the Word-RAM parser/allocator `initNodesProg`. It has no dependency on any
bag-scan or DP-pass submodule (`IndepScan`, `MaskOps`, `WeightScan`, `ChildPass`, `ParentPass`,
`RootPass`).

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.NodeLayout`: memory-layout invariant over weights,
  adjacency matrix, parent pointers, 4-word node descriptors, and pairwise-disjoint DP tables.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.prefixMaxSum`: sum of per-table maximum entries across
  nodes `0 .. m`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.InitNodesArgs`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.initNodesProg`: register arguments and Word-RAM
  routine parsing length-prefixed bags and zero-allocating all `n + 1` DP tables.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.NodeLayout.mono_frontier`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.NodeLayout.update_table`: framing under frontier
  allocations and single-table in-place updates.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.prefixMaxSum_update_le`: telescoping potential step
  when child `k + 1` accumulates into strictly smaller parent `p < k + 1`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.initNodesProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.initNodesProg_realizes`: initial `NodeLayout`
  establishment, cost bound, and exact-basis realization certificate.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Memory layout invariant (`NodeLayout`) -/

/-- Memory-layout invariant over `inst`'s input slices, 4-word node descriptors at `descBase`, and
disjoint materialized DP tables `tblList i` of length `2 ^ |bagAt i|`. -/
structure NodeLayout (inst : MWISInstance) (descBase : ℕ)
    (tblList : Fin (inst.numNodes + 1) → List ℕ) (s : Memory.State) : Prop where
  /-- Weights array at word address `3`. -/
  wt_holds : HoldsIn 3 inst.weights s
  /-- Row-major adjacency matrix at `3 + numVerts`. -/
  adj_holds : HoldsIn (3 + inst.numVerts) inst.adjMatrix s
  /-- Parent array at `3 + numVerts + numVerts * numVerts`. -/
  par_holds : HoldsIn (3 + inst.numVerts + inst.numVerts * inst.numVerts) inst.parents s
  /-- Descriptor block starts after the input prefix. -/
  desc_lo : 3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1) ≤ descBase
  /-- All `4 * (numNodes + 1)` descriptor words lie within `s.frontier`. -/
  desc_hi : descBase + 4 * (inst.numNodes + 1) ≤ s.frontier
  /-- Each node `i` descriptor stores `(bagPtr, bagLen, tblPtr, 2 ^ bagLen)` with `bagAt i` below
  `descBase`. -/
  bags_holds : ∀ i : Fin (inst.numNodes + 1),
    s.mem (descBase + 4 * i.val + 1) = (inst.bagAt i).length ∧
    s.mem (descBase + 4 * i.val + 3) = 2 ^ (inst.bagAt i).length ∧
    s.mem (descBase + 4 * i.val) + (inst.bagAt i).length ≤ descBase ∧
    HoldsIn (s.mem (descBase + 4 * i.val)) (inst.bagAt i) s
  /-- Each node `i` DP table lies at or above `descBase + 4 * (numNodes + 1)` and holds
  `tblList i`. -/
  tbl_holds : ∀ i : Fin (inst.numNodes + 1),
    (tblList i).length = 2 ^ (inst.bagAt i).length ∧
    descBase + 4 * (inst.numNodes + 1) ≤ s.mem (descBase + 4 * i.val + 2) ∧
    HoldsIn (s.mem (descBase + 4 * i.val + 2)) (tblList i) s
  /-- Distinct node DP tables occupy strictly ordered, non-overlapping address ranges. -/
  tbl_disj : ∀ i j : Fin (inst.numNodes + 1), i.val < j.val →
    s.mem (descBase + 4 * i.val + 2) + 2 ^ (inst.bagAt i).length ≤
      s.mem (descBase + 4 * j.val + 2)

/-- `NodeLayout` is preserved by allocations or writes at or above `s.frontier`. -/
theorem NodeLayout.mono_frontier {inst : MWISInstance} {descBase : ℕ}
    {tblList : Fin (inst.numNodes + 1) → List ℕ} {s s' : Memory.State}
    (h : NodeLayout inst descBase tblList s) (hp : PreservesBelow s.frontier s s') :
    NodeLayout inst descBase tblList s' where
  wt_holds := h.wt_holds.mono_frontier hp
  adj_holds := h.adj_holds.mono_frontier hp
  par_holds := h.par_holds.mono_frontier hp
  desc_lo := h.desc_lo
  desc_hi := h.desc_hi.trans hp.2.1
  bags_holds i := by
    obtain ⟨h1, h3, hlo, hb⟩ := h.bags_holds i
    have hd_hi := h.desc_hi
    have hi_lt := i.isLt
    have hm0 : s'.mem (descBase + 4 * i.val) = s.mem (descBase + 4 * i.val) :=
      hp.2.2 _ (by omega)
    have hm1 : s'.mem (descBase + 4 * i.val + 1) = s.mem (descBase + 4 * i.val + 1) :=
      hp.2.2 _ (by omega)
    have hm3 : s'.mem (descBase + 4 * i.val + 3) = s.mem (descBase + 4 * i.val + 3) :=
      hp.2.2 _ (by omega)
    rw [hm0, hm1, hm3]
    exact ⟨h1, h3, hlo, hb.mono_frontier hp⟩
  tbl_holds i := by
    obtain ⟨hlen, hlo, ht⟩ := h.tbl_holds i
    have hd_hi := h.desc_hi
    have hi_lt := i.isLt
    have hm2 : s'.mem (descBase + 4 * i.val + 2) = s.mem (descBase + 4 * i.val + 2) :=
      hp.2.2 _ (by omega)
    rw [hm2]
    exact ⟨hlen, hlo, ht.mono_frontier hp⟩
  tbl_disj i j hij := by
    have hd_hi := h.desc_hi
    have hi_lt := i.isLt
    have hj_lt := j.isLt
    rw [hp.2.2 (descBase + 4 * i.val + 2) (by omega),
      hp.2.2 (descBase + 4 * j.val + 2) (by omega)]
    exact h.tbl_disj i j hij

/-- `NodeLayout` updates cleanly when node `p`'s DP table is overwritten in-place. -/
theorem NodeLayout.update_table {inst : MWISInstance} {descBase : ℕ}
    {tblList : Fin (inst.numNodes + 1) → List ℕ} {s s' : Memory.State}
    (h : NodeLayout inst descBase tblList s)
    (p : Fin (inst.numNodes + 1)) (newP : List ℕ)
    (hnew_len : newP.length = 2 ^ (inst.bagAt p).length)
    (hfr : s'.frontier = s.frontier)
    (hout : ∀ addr,
      (addr < s.mem (descBase + 4 * p.val + 2) ∨
        s.mem (descBase + 4 * p.val + 2) + 2 ^ (inst.bagAt p).length ≤ addr) →
      s'.mem addr = s.mem addr)
    (hholdP : HoldsIn (s.mem (descBase + 4 * p.val + 2)) newP s') :
    NodeLayout inst descBase (Function.update tblList p newP) s' := by
  have hp_lo : descBase + 4 * (inst.numNodes + 1) ≤ s.mem (descBase + 4 * p.val + 2) :=
    (h.tbl_holds p).2.1
  have hdesc_lo := h.desc_lo
  have hlow_eq : ∀ addr < descBase + 4 * (inst.numNodes + 1), s'.mem addr = s.mem addr :=
    fun addr ha => hout addr (.inl (lt_of_lt_of_le ha hp_lo))
  refine
    { wt_holds := ⟨by rw [hfr]; exact h.wt_holds.1,
        h.wt_holds.2.frame fun a _ ha =>
          hlow_eq a (by rw [inst.weights_len] at ha; omega)⟩
      adj_holds := ⟨by rw [hfr]; exact h.adj_holds.1,
        h.adj_holds.2.frame fun a _ ha =>
          hlow_eq a (by rw [inst.adjMatrix_len] at ha; omega)⟩
      par_holds := ⟨by rw [hfr]; exact h.par_holds.1,
        h.par_holds.2.frame fun a _ ha =>
          hlow_eq a (by rw [inst.parents_len] at ha; omega)⟩
      desc_lo := h.desc_lo
      desc_hi := by rw [hfr]; exact h.desc_hi
      bags_holds := fun i => by
        obtain ⟨h1, h3, hblo, hb⟩ := h.bags_holds i
        have hi_lt := i.isLt
        rw [hlow_eq (descBase + 4 * i.val) (by omega),
          hlow_eq (descBase + 4 * i.val + 1) (by omega),
          hlow_eq (descBase + 4 * i.val + 3) (by omega)]
        exact ⟨h1, h3, hblo,
          ⟨by rw [hfr]; exact hb.1, hb.2.frame fun a _ ha => hlow_eq a (by omega)⟩⟩
      tbl_holds := fun i => by
        have hi_lt := i.isLt
        rw [hlow_eq (descBase + 4 * i.val + 2) (by omega)]
        by_cases hip : i = p
        · subst hip
          rw [Function.update_self]
          exact ⟨hnew_len, hp_lo, hholdP⟩
        · rw [Function.update_of_ne hip]
          obtain ⟨hlen, hlo, ht⟩ := h.tbl_holds i
          refine ⟨hlen, hlo, ⟨by rw [hfr]; exact ht.1, ht.2.frame fun a ha1 ha2 => ?_⟩⟩
          have hne_val : i.val ≠ p.val := fun hv => hip (Fin.ext hv)
          rcases Nat.lt_or_gt_of_ne hne_val with hilt | hpilt
          · have hdisj := h.tbl_disj i p hilt
            exact hout a (.inl (by omega))
          · have hdisj := h.tbl_disj p i hpilt
            exact hout a (.inr (by omega))
      tbl_disj := fun i j hij => by
        have hi_lt := i.isLt
        have hj_lt := j.isLt
        rw [hlow_eq (descBase + 4 * i.val + 2) (by omega),
          hlow_eq (descBase + 4 * j.val + 2) (by omega)]
        exact h.tbl_disj i j hij }

/-! ### Telescoping prefix-sum potential (`prefixMaxSum`) -/

private def nodeMax {n : ℕ} (tblList : Fin (n + 1) → List ℕ) (i : ℕ) : ℕ :=
  if hi : i < n + 1 then (tblList ⟨i, hi⟩).foldl max 0 else 0

/-- Sum of per-table maximum entries across nodes `0, …, m`. -/
def prefixMaxSum {n : ℕ} (tblList : Fin (n + 1) → List ℕ) (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (m + 1), nodeMax tblList i

/-- All-zero tables have `prefixMaxSum = 0`. -/
theorem prefixMaxSum_replicate_zero {n : ℕ} (len : Fin (n + 1) → ℕ) (m : ℕ) :
    prefixMaxSum (fun i => List.replicate (len i) 0) m = 0 := by
  unfold prefixMaxSum
  refine Finset.sum_eq_zero fun i _ => ?_
  unfold nodeMax
  split_ifs with hi
  · refine Nat.eq_zero_of_le_zero (List.foldl_max_le le_rfl fun x hx => ?_)
    rw [List.eq_of_mem_replicate hx]
  · rfl

private theorem nodeMax_le_prefixMaxSum {n : ℕ} (tblList : Fin (n + 1) → List ℕ)
    {i m : ℕ} (him : i ≤ m) :
    nodeMax tblList i ≤ prefixMaxSum tblList m :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le him))

/-- Node `i`'s maximum table entry is bounded by `prefixMaxSum tblList m` whenever `i ≤ m`. -/
theorem foldl_max_le_prefixMaxSum {n : ℕ} (tblList : Fin (n + 1) → List ℕ)
    (i : Fin (n + 1)) {m : ℕ} (him : i.val ≤ m) :
    (tblList i).foldl max 0 ≤ prefixMaxSum tblList m := by
  have h := nodeMax_le_prefixMaxSum tblList him
  unfold nodeMax at h
  rwa [dite_eq_left i.isLt, Fin.eta] at h

/-- Splitting `prefixMaxSum tblList (k + 1)` off node `k + 1` when `k + 1 ≤ n`. -/
theorem prefixMaxSum_succ {n : ℕ} (tblList : Fin (n + 1) → List ℕ) {k : ℕ} (hk : k + 1 ≤ n) :
    prefixMaxSum tblList (k + 1) =
      prefixMaxSum tblList k + (tblList ⟨k + 1, by omega⟩).foldl max 0 := by
  unfold prefixMaxSum
  rw [Finset.sum_range_succ]
  unfold nodeMax
  rw [dite_eq_left (by omega)]

/-- Telescoping step: folding node `k + 1`'s table into strictly earlier parent `p < k + 1`
increases the remaining prefix sum `0 .. k` by at most `B` relative to `0 .. k + 1`. -/
theorem prefixMaxSum_update_le {n : ℕ} (tblList : Fin (n + 1) → List ℕ)
    {k B : ℕ} (hk : k + 1 ≤ n) (p : Fin (n + 1)) (hp_lt : p.val < k + 1)
    (newP : List ℕ)
    (hnew : newP.foldl max 0 ≤
      (tblList p).foldl max 0 + B + (tblList ⟨k + 1, by omega⟩).foldl max 0) :
    prefixMaxSum (Function.update tblList p newP) k ≤ prefixMaxSum tblList (k + 1) + B := by
  have hp_mem : p.val ∈ Finset.range (k + 1) := Finset.mem_range.2 hp_lt
  have hsum_succ := prefixMaxSum_succ tblList hk
  have herase_old : nodeMax tblList p.val +
      ∑ i ∈ (Finset.range (k + 1)).erase p.val, nodeMax tblList i =
      prefixMaxSum tblList k := Finset.add_sum_erase _ _ hp_mem
  have herase_new : prefixMaxSum (Function.update tblList p newP) k =
      nodeMax (Function.update tblList p newP) p.val +
      ∑ i ∈ (Finset.range (k + 1)).erase p.val,
        nodeMax (Function.update tblList p newP) i :=
    (Finset.add_sum_erase _ _ hp_mem).symm
  have hrest_eq : ∑ i ∈ (Finset.range (k + 1)).erase p.val,
      nodeMax (Function.update tblList p newP) i =
      ∑ i ∈ (Finset.range (k + 1)).erase p.val, nodeMax tblList i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hine : i ≠ p.val := (Finset.mem_erase.1 hi).1
    unfold nodeMax
    split_ifs with hlt
    · rw [Function.update_of_ne (fun h => hine (congrArg Fin.val h))]
    · rfl
  have hp_new : nodeMax (Function.update tblList p newP) p.val = newP.foldl max 0 := by
    unfold nodeMax
    rw [dite_eq_left p.isLt, Fin.eta, Function.update_self]
  have hp_old : nodeMax tblList p.val = (tblList p).foldl max 0 := by
    unfold nodeMax
    rw [dite_eq_left p.isLt, Fin.eta]
  rw [herase_new, hrest_eq, hp_new, hsum_succ, ← herase_old, hp_old]
  omega

/-! ### Node descriptor initialization (`initNodesProg`) -/

/-- Register arguments `(rawBagsPtr, count)` for `initNodesProg`. -/
structure InitNodesArgs where
  /-- Base memory address of `inst.bags.flatMap encodeBag`. -/
  rawBagsPtr : ℕ
  /-- Number of tree-decomposition nodes `numNodes + 1`. -/
  count : ℕ

/-- Tuple equivalence encoding `InitNodesArgs` into Word-RAM registers. -/
@[expose] def InitNodesArgs.equiv : InitNodesArgs ≃ ℕ × ℕ where
  toFun a := (a.rawBagsPtr, a.count)
  invFun := fun (r, c) => ⟨r, c⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding InitNodesArgs := .ofEquiv InitNodesArgs.equiv

private structure InitNodeState where
  curRaw : ℕ
  curIdx : ℕ

private def InitNodeState.equiv : InitNodeState ≃ ℕ × ℕ where
  toFun s := (s.curRaw, s.curIdx)
  invFun := fun (r, i) => ⟨r, i⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding InitNodeState := .ofEquiv InitNodeState.equiv

private def initNodeStep (p : ℕ × InitNodeState) : Memory.Prog InitNodeState := do
  let descBase := p.1
  let st := p.2
  let bagLen ← Memory.read st.curRaw
  let bagPtr := st.curRaw + 1
  let tblLen ← powProg ⟨2, bagLen⟩
  let tblPtr ← Memory.alloc tblLen
  let dAddr := descBase + 4 * st.curIdx
  Memory.write dAddr bagPtr
  Memory.write (dAddr + 1) bagLen
  Memory.write (dAddr + 2) tblPtr
  Memory.write (dAddr + 3) tblLen
  pure ⟨bagPtr + bagLen, st.curIdx + 1⟩

/-- Allocate `4 * args.count` descriptor words, parse each length-prefixed bag, zero-allocate its
`2 ^ bagLen`-word DP table, and return `descBase`. -/
def initNodesProg (args : InitNodesArgs) : Memory.Prog ℕ := do
  let descBase ← Memory.allocDirty (4 * args.count)
  let _ ← iterate initNodeStep descBase args.count ⟨args.rawBagsPtr, 0⟩
  pure descBase

private theorem initNodeStep_eval (descBase : ℕ) (st : InitNodeState) (t : Memory.State) :
    let bagLen := t.mem st.curRaw
    let bagPtr := st.curRaw + 1
    let tblLen := 2 ^ bagLen
    let tblPtr := t.frontier
    let dAddr := descBase + 4 * st.curIdx
    let m0 := clear t.mem tblPtr tblLen
    let m1 := Function.update m0 dAddr bagPtr
    let m2 := Function.update m1 (dAddr + 1) bagLen
    let m3 := Function.update m2 (dAddr + 2) tblPtr
    let m4 := Function.update m3 (dAddr + 3) tblLen
    (Memory.spec 0).clientState t (initNodeStep (descBase, st)) = ⟨m4, t.frontier + tblLen⟩ ∧
    (Memory.spec 0).clientResult t (initNodeStep (descBase, st)) =
      ⟨bagPtr + bagLen, st.curIdx + 1⟩ := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold initNodeStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    powProg_state, powProg_result]
  exact ⟨rfl, rfl⟩

/-- `initNodesProg` establishes `NodeLayout` with zero-initialized tables in
`≤ 1 + (numNodes + 1) * (2 ^ maxBagLen + maxBagLen + 6)` memory operations. -/
theorem initNodesProg_spec {w : ℕ} (inst : MWISInstance) {s₀ : Memory.State}
    (hwt₀ : HoldsIn 3 inst.weights s₀)
    (hadj₀ : HoldsIn (3 + inst.numVerts) inst.adjMatrix s₀)
    (hpar₀ : HoldsIn (3 + inst.numVerts + inst.numVerts * inst.numVerts) inst.parents s₀)
    (hbags₀ : HoldsIn
      (3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1))
      (inst.bags.flatMap encodeBag) s₀)
    (hfit_peak : Fits w (s₀.frontier + 4 * (inst.numNodes + 1) +
      (inst.numNodes + 1) * 2 ^ inst.maxBagLen))
    (hfit_raw : Fits w s₀.frontier) :
    let rawBagsPtr := 3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1)
    let count := inst.numNodes + 1
    let s₁ := (Memory.spec 0).clientState s₀ (initNodesProg ⟨rawBagsPtr, count⟩)
    let descBase := (Memory.spec 0).clientResult s₀ (initNodesProg ⟨rawBagsPtr, count⟩)
    (Memory.spec w).ValidHistory s₀
      ((Memory.spec w).clientHistory s₀ (initNodesProg ⟨rawBagsPtr, count⟩)) ∧
    descBase = s₀.frontier ∧
    s₁.frontier ≤ s₀.frontier + 4 * count + count * 2 ^ inst.maxBagLen ∧
    NodeLayout inst descBase
      (fun i => List.replicate (2 ^ (inst.bagAt i).length) 0) s₁ ∧
    memoryCost (initNodesProg ⟨rawBagsPtr, count⟩) s₀ ≤
      1 + count * (2 ^ inst.maxBagLen + inst.maxBagLen + 6) := by
  let rawBagsPtr := 3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1)
  let count := inst.numNodes + 1
  let M := inst.maxBagLen
  let descBase := s₀.frontier
  let s_d := (Memory.spec 0).clientState s₀ (Memory.allocDirty (4 * count))
  have hs_d_fr : s_d.frontier = descBase + 4 * count := rfl
  have hp_d : PreservesBelow descBase s₀ s_d := preservesBelow_allocDirty s₀ (4 * count)
  have hfit_d : Fits w (s₀.frontier + 4 * count) := hfit_peak.of_le (by omega)
  have hv_d : (Memory.spec w).ValidHistory s₀
      ((Memory.spec w).clientHistory s₀ (Memory.allocDirty (4 * count))) :=
    validHistory_allocDirty hfit_d
  have hraw_lo : rawBagsPtr ≤ descBase := by have := hbags₀.1; omega
  let stepCost := 2 ^ M + M + 6
  suffices ∀ rem k curRaw st,
      (hsum : k + rem = count) →
      descBase + 4 * count ≤ st.frontier →
      st.frontier ≤ descBase + 4 * count + k * 2 ^ M →
      PreservesBelow descBase s₀ st →
      HoldsIn curRaw ((inst.bags.drop k).flatMap encodeBag) st →
      curRaw + ((inst.bags.drop k).flatMap encodeBag).length ≤ descBase →
      (∀ i (hi : i < k),
        have hif : i < count := lt_of_lt_of_le hi (by omega)
        st.mem (descBase + 4 * i + 1) = (inst.bagAt ⟨i, hif⟩).length ∧
        st.mem (descBase + 4 * i + 3) = 2 ^ (inst.bagAt ⟨i, hif⟩).length ∧
        st.mem (descBase + 4 * i) + (inst.bagAt ⟨i, hif⟩).length ≤ descBase ∧
        HoldsIn (st.mem (descBase + 4 * i)) (inst.bagAt ⟨i, hif⟩) st ∧
        descBase + 4 * count ≤ st.mem (descBase + 4 * i + 2) ∧
        HoldsIn (st.mem (descBase + 4 * i + 2))
          (List.replicate (2 ^ (inst.bagAt ⟨i, hif⟩).length) 0) st) →
      (∀ i j (hi : i < k) (hj : j < k), i < j →
        st.mem (descBase + 4 * i + 2) +
          2 ^ (inst.bagAt ⟨i, lt_of_lt_of_le hi (by omega)⟩).length ≤
          st.mem (descBase + 4 * j + 2)) →
      (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (iterate initNodeStep descBase rem ⟨curRaw, k⟩)) ∧
      (let sEnd := (Memory.spec 0).clientState st (iterate initNodeStep descBase rem ⟨curRaw, k⟩)
       descBase + 4 * count ≤ sEnd.frontier ∧
       sEnd.frontier ≤ descBase + 4 * count + count * 2 ^ M ∧
       PreservesBelow descBase s₀ sEnd ∧
       (∀ i : Fin count,
         sEnd.mem (descBase + 4 * i.val + 1) = (inst.bagAt i).length ∧
         sEnd.mem (descBase + 4 * i.val + 3) = 2 ^ (inst.bagAt i).length ∧
         sEnd.mem (descBase + 4 * i.val) + (inst.bagAt i).length ≤ descBase ∧
         HoldsIn (sEnd.mem (descBase + 4 * i.val)) (inst.bagAt i) sEnd ∧
         descBase + 4 * count ≤ sEnd.mem (descBase + 4 * i.val + 2) ∧
         HoldsIn (sEnd.mem (descBase + 4 * i.val + 2))
           (List.replicate (2 ^ (inst.bagAt i).length) 0) sEnd) ∧
       (∀ i j : Fin count, i.val < j.val →
         sEnd.mem (descBase + 4 * i.val + 2) + 2 ^ (inst.bagAt i).length ≤
           sEnd.mem (descBase + 4 * j.val + 2))) ∧
      memoryCost (iterate initNodeStep descBase rem ⟨curRaw, k⟩) st ≤ rem * stepCost by
    have hrun := this count 0 rawBagsPtr s_d (Nat.zero_add _)
      (by rw [hs_d_fr]) (by rw [hs_d_fr]; omega) hp_d
      (by simpa only [List.drop_zero] using hbags₀.mono_frontier hp_d)
      hbags₀.1
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (fun _ _ hi _ _ => absurd hi (Nat.not_lt_zero _))
    obtain ⟨hv_loop, ⟨hfr_lo, hfr_hi, hpres_end, hnodes_end, hdisj_end⟩, hc_loop⟩ := hrun
    unfold initNodesProg
    dsimp only
    have ha_st : (Memory.spec 0).clientState s₀ (Memory.allocDirty (4 * count)) = s_d := rfl
    have ha_res : (Memory.spec 0).clientResult s₀ (Memory.allocDirty (4 * count)) = descBase := rfl
    refine ⟨validHistory_bind_step hv_d ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha_st, ha_res]
      exact validHistory_bind_step hv_loop (validHistory_pure w _ _)
    · rw [StateTransitionSpec.clientResult_bind, ha_st, ha_res,
        StateTransitionSpec.clientResult_bind]
      rfl
    · rw [StateTransitionSpec.clientState_bind, ha_st, ha_res,
        StateTransitionSpec.clientState_bind]
      exact hfr_hi
    · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
        ha_st, ha_res, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
      change NodeLayout inst descBase _
        ((Memory.spec 0).clientState s_d (iterate initNodeStep descBase count ⟨rawBagsPtr, 0⟩))
      exact
        { wt_holds := hwt₀.mono_frontier hpres_end
          adj_holds := hadj₀.mono_frontier hpres_end
          par_holds := hpar₀.mono_frontier hpres_end
          desc_lo := hraw_lo
          desc_hi := hfr_lo
          bags_holds := fun i => by
            obtain ⟨h1, h3, hblo, hb, _, _⟩ := hnodes_end i
            exact ⟨h1, h3, hblo, hb⟩
          tbl_holds := fun i => by
            obtain ⟨_, _, _, _, htlo, ht⟩ := hnodes_end i
            exact ⟨List.length_replicate, htlo, ht⟩
          tbl_disj := hdisj_end }
    · rw [memoryCost_bind', memoryCost_allocDirty, ha_st, ha_res,
        memoryCost_bind', memoryCost_pure, Nat.add_zero]
      dsimp only [count, stepCost, M, descBase, rawBagsPtr] at hc_loop ⊢
      omega
  intro rem
  induction rem with
  | zero =>
    intro k curRaw st hsum hfr_lo hfr_hi hpres _ _ hdone hdisj
    have hk_eq : k = count := by omega
    subst hk_eq
    have h0 : iterate initNodeStep descBase 0 ⟨curRaw, count⟩ = pure ⟨curRaw, count⟩ := rfl
    rw [h0]
    refine ⟨validHistory_pure w st _, ⟨hfr_lo, hfr_hi, hpres, ?_, ?_⟩,
      by simp [memoryCost_pure]⟩
    · intro i
      exact hdone i.val i.isLt
    · intro i j hij
      exact hdisj i.val j.val i.isLt j.isLt hij
  | succ rem ih =>
    intro k curRaw st hsum hfr_lo hfr_hi hpres hdrop hdrop_end hdone hdisj
    have hk_lt : k < count := by omega
    have hk_bags : k < inst.bags.length := by rw [inst.bags_len]; exact hk_lt
    let kFin : Fin count := ⟨k, hk_lt⟩
    have hdrop_cons : inst.bags.drop k = inst.bagAt kFin :: inst.bags.drop (k + 1) :=
      List.drop_eq_getElem_cons hk_bags
    rw [hdrop_cons, List.flatMap_cons, encodeBag, List.cons_append] at hdrop hdrop_end
    rw [HoldsIn.cons_iff] at hdrop
    obtain ⟨_, hmem_len, hafter_len⟩ := hdrop
    rw [HoldsIn.append_iff] at hafter_len
    obtain ⟨hbag_k, hrest_raw⟩ := hafter_len
    let bagLen := (inst.bagAt kFin).length
    let bagPtr := curRaw + 1
    let tblLen := 2 ^ bagLen
    let tblPtr := st.frontier
    let dAddr := descBase + 4 * k
    have hbagLen_le : bagLen ≤ M := inst.bagAt_length_le kFin
    have htblLen_le : tblLen ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) hbagLen_le
    have hcur_lt_fr : curRaw < st.frontier := by omega
    have hfr_pos : 0 < st.frontier := by omega
    obtain ⟨hv_pow, hst_pow, hr_pow, hc_pow⟩ := powProg_spec (w := w) ⟨2, bagLen⟩ hfr_pos
    dsimp only at hr_pow hc_pow
    have hfr_next_le : st.frontier + tblLen ≤ descBase + 4 * count + (k + 1) * 2 ^ M := by
      calc st.frontier + tblLen
          ≤ (descBase + 4 * count + k * 2 ^ M) + 2 ^ M := Nat.add_le_add hfr_hi htblLen_le
        _ = descBase + 4 * count + (k + 1) * 2 ^ M := by rw [Nat.add_assoc, ← Nat.succ_mul]
    have hfit_alloc : Fits w (st.frontier + tblLen) := hfit_peak.of_le (by
      have hk1 : k + 1 ≤ count := by omega
      have hmul : (k + 1) * 2 ^ M ≤ count * 2 ^ M := Nat.mul_le_mul_right _ hk1
      dsimp only [count, M, descBase] at hfr_next_le hmul ⊢
      omega)
    have hv_alloc : (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (Memory.alloc tblLen)) :=
      validHistory_alloc hfit_alloc
    have hbagPtr_fit : Fits w bagPtr := hfit_raw.of_le (by
      simp only [List.length_cons, List.length_append] at hdrop_end
      dsimp only [bagPtr, bagLen, descBase] at *; omega)
    have hbagLen_fit : Fits w bagLen := hfit_raw.of_le (by
      simp only [List.length_cons, List.length_append] at hdrop_end
      dsimp only [bagPtr, bagLen, descBase] at *; omega)
    have htblPtr_fit : Fits w tblPtr := hfit_alloc.of_le (Nat.le_add_right _ _)
    have htblLen_fit : Fits w tblLen := hfit_alloc.of_le (Nat.le_add_left _ _)
    let st_a := (Memory.spec 0).clientState st (Memory.alloc tblLen)
    have hp_a : PreservesBelow st.frontier st st_a := preservesBelow_alloc st tblLen
    have htbl_zero_a : HoldsIn tblPtr (List.replicate tblLen 0) st_a :=
      holdsIn_alloc_zero st tblLen
    let m1 := Function.update st_a.mem dAddr bagPtr
    let m2 := Function.update m1 (dAddr + 1) bagLen
    let m3 := Function.update m2 (dAddr + 2) tblPtr
    let m4 := Function.update m3 (dAddr + 3) tblLen
    let st₁ : Memory.State := ⟨m4, st.frontier + tblLen⟩
    obtain ⟨hst_step, hres_step⟩ := initNodeStep_eval descBase ⟨curRaw, k⟩ st
    have hst_step' : (Memory.spec 0).clientState st (initNodeStep (descBase, ⟨curRaw, k⟩)) =
        st₁ := by
      rw [hst_step]
      dsimp only [st₁, m4, m3, m2, m1, st_a, bagLen, bagPtr, tblLen, tblPtr, dAddr]
      simp only [hmem_len]
      rfl
    have hres_step' : (Memory.spec 0).clientResult st (initNodeStep (descBase, ⟨curRaw, k⟩)) =
        ⟨bagPtr + bagLen, k + 1⟩ := by
      rw [hres_step]
      dsimp only [bagPtr, bagLen]
      simp only [hmem_len]
    have hd3_lt : dAddr + 3 < st.frontier + tblLen := by omega
    have hv_step : (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (initNodeStep (descBase, ⟨curRaw, k⟩))) := by
      unfold initNodeStep
      dsimp only
      refine validHistory_read_bind hcur_lt_fr ?_
      rw [hmem_len]
      refine validHistory_bind_step hv_pow ?_
      rw [hst_pow, hr_pow]
      refine validHistory_bind_step hv_alloc ?_
      change (Memory.spec w).ValidHistory st_a
        ((Memory.spec w).clientHistory st_a
          (Memory.write dAddr bagPtr >>= fun _ =>
            Memory.write (dAddr + 1) bagLen >>= fun _ =>
            Memory.write (dAddr + 2) tblPtr >>= fun _ =>
            Memory.write (dAddr + 3) tblLen >>= fun _ => pure _))
      have hd0 : dAddr < st_a.frontier := by change dAddr < st.frontier + tblLen; omega
      have hd1 : dAddr + 1 < st_a.frontier := by change dAddr + 1 < st.frontier + tblLen; omega
      have hd2 : dAddr + 2 < st_a.frontier := by change dAddr + 2 < st.frontier + tblLen; omega
      have hd3 : dAddr + 3 < st_a.frontier := hd3_lt
      exact validHistory_write_bind hd0 hbagPtr_fit
        (validHistory_write_bind hd1 hbagLen_fit
          (validHistory_write_bind hd2 htblPtr_fit
            (validHistory_write_bind hd3 htblLen_fit
              (validHistory_pure w st₁ _))))
    have hp_writes : ∀ addr, (addr < dAddr ∨ dAddr + 4 ≤ addr) → st₁.mem addr = st_a.mem addr :=
      fun addr haddr => by
        change m4 addr = st_a.mem addr
        dsimp only [m4, m3, m2, m1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hpres₁ : PreservesBelow descBase s₀ st₁ := by
      refine hpres.trans ⟨by omega, by change st.frontier ≤ st.frontier + tblLen; omega,
        fun addr ha => ?_⟩
      rw [hp_writes addr (.inl (by dsimp only [dAddr]; omega)), hp_a.2.2 addr (by omega)]
    have hbag_k_st₁ : HoldsIn bagPtr (inst.bagAt kFin) st₁ :=
      hbag_k.mono (F := descBase) (by
          simp only [List.length_cons, List.length_append] at hdrop_end
          dsimp only [bagPtr, bagLen, descBase, kFin] at *; omega)
        ⟨by dsimp only [bagPtr, bagLen, tblLen, descBase, kFin] at *; omega,
         by change st.frontier ≤ st.frontier + tblLen; omega,
         fun a ha => by
          rw [hp_writes a
              (.inl (by dsimp only [bagPtr, bagLen, dAddr, descBase, kFin] at *; omega)),
            hp_a.2.2 a (by dsimp only [bagPtr, bagLen, descBase, kFin] at *; omega)]⟩
    have hrest_st₁ : HoldsIn (bagPtr + bagLen) ((inst.bags.drop (k + 1)).flatMap encodeBag) st₁ :=
      hrest_raw.mono (F := descBase) (by
          simp only [List.length_cons, List.length_append] at hdrop_end
          dsimp only [bagPtr, bagLen, descBase, kFin] at *; omega)
        ⟨by dsimp only [bagPtr, bagLen, tblLen, descBase, kFin] at *; omega,
         by change st.frontier ≤ st.frontier + tblLen; omega,
         fun a ha => by
          rw [hp_writes a
              (.inl (by dsimp only [bagPtr, bagLen, dAddr, descBase, kFin] at *; omega)),
            hp_a.2.2 a (by dsimp only [bagPtr, bagLen, descBase, kFin] at *; omega)]⟩
    have htbl_k_st₁ : HoldsIn tblPtr (List.replicate tblLen 0) st₁ :=
      ⟨htbl_zero_a.1, htbl_zero_a.2.frame fun a ha _ =>
        hp_writes a (.inr (by dsimp only [tblPtr, tblLen, dAddr, descBase, count] at *; omega))⟩
    have hm4_0 : st₁.mem dAddr = bagPtr := by
      change m4 dAddr = bagPtr
      dsimp only [m4, m3, m2, m1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
    have hm4_1 : st₁.mem (dAddr + 1) = bagLen := by
      change m4 (dAddr + 1) = bagLen
      dsimp only [m4, m3, m2, m1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    have hm4_2 : st₁.mem (dAddr + 2) = tblPtr := by
      change m4 (dAddr + 2) = tblPtr
      dsimp only [m4, m3, m2, m1]
      rw [Function.update_of_ne (by omega), Function.update_self]
    have hm4_3 : st₁.mem (dAddr + 3) = tblLen := by
      change m4 (dAddr + 3) = tblLen
      dsimp only [m4]
      rw [Function.update_self]
    have hdone₁ : ∀ i (hi : i < k + 1),
        have hif : i < count := lt_of_lt_of_le hi (by omega)
        st₁.mem (descBase + 4 * i + 1) = (inst.bagAt ⟨i, hif⟩).length ∧
        st₁.mem (descBase + 4 * i + 3) = 2 ^ (inst.bagAt ⟨i, hif⟩).length ∧
        st₁.mem (descBase + 4 * i) + (inst.bagAt ⟨i, hif⟩).length ≤ descBase ∧
        HoldsIn (st₁.mem (descBase + 4 * i)) (inst.bagAt ⟨i, hif⟩) st₁ ∧
        descBase + 4 * count ≤ st₁.mem (descBase + 4 * i + 2) ∧
        HoldsIn (st₁.mem (descBase + 4 * i + 2))
          (List.replicate (2 ^ (inst.bagAt ⟨i, hif⟩).length) 0) st₁ := by
      intro i hi
      by_cases hik : i = k
      · subst hik
        rw [hm4_0, hm4_1, hm4_2, hm4_3]
        refine ⟨rfl, rfl, ?_, hbag_k_st₁, hfr_lo, htbl_k_st₁⟩
        simp only [List.length_cons, List.length_append] at hdrop_end
        dsimp only [bagPtr, bagLen, descBase, kFin] at *
        omega
      · have hik_lt : i < k := by omega
        obtain ⟨h1, h3, hblo, hb, htlo, ht⟩ := hdone i hik_lt
        have heq_m0 : st₁.mem (descBase + 4 * i) = st.mem (descBase + 4 * i) := by
          rw [hp_writes _ (.inl (by dsimp only [dAddr]; omega)),
            hp_a.2.2 _ (by dsimp only [descBase, count] at *; omega)]
        have heq_m (off : ℕ) (hoff : off < 4) :
            st₁.mem (descBase + 4 * i + off) = st.mem (descBase + 4 * i + off) := by
          rw [hp_writes _ (.inl (by dsimp only [dAddr]; omega)),
            hp_a.2.2 _ (by dsimp only [descBase, count] at *; omega)]
        rw [heq_m0, heq_m 1 (by decide), heq_m 2 (by decide), heq_m 3 (by decide)]
        refine ⟨h1, h3, hblo, ?_, htlo, ?_⟩
        · exact hb.mono hblo
            ⟨by dsimp only [descBase, count] at *; omega,
             by change st.frontier ≤ st.frontier + tblLen; omega,
             fun a ha => by
              rw [hp_writes a (.inl (by dsimp only [dAddr, descBase] at *; omega)),
                hp_a.2.2 a (by dsimp only [descBase, count] at *; omega)]⟩
        · refine ⟨ht.1.trans (Nat.le_add_right _ _), ht.2.frame fun a ha hlt => ?_⟩
          rw [hp_writes a (.inr (by dsimp only [dAddr, descBase, count] at *; omega)),
            hp_a.2.2 a (lt_of_lt_of_le hlt ht.1)]
    have hdisj₁ : ∀ i j (hi : i < k + 1) (hj : j < k + 1), i < j →
        st₁.mem (descBase + 4 * i + 2) +
          2 ^ (inst.bagAt ⟨i, lt_of_lt_of_le hi (by omega)⟩).length ≤
          st₁.mem (descBase + 4 * j + 2) := by
      intro i j hi hj hij
      have hi_lt_k : i < k := by omega
      have hmi : st₁.mem (descBase + 4 * i + 2) = st.mem (descBase + 4 * i + 2) := by
        rw [hp_writes _ (.inl (by dsimp only [dAddr]; omega)),
          hp_a.2.2 _ (by dsimp only [descBase, count] at *; omega)]
      rw [hmi]
      by_cases hjk : j = k
      · subst hjk
        rw [hm4_2]
        obtain ⟨_, _, _, _, _, ht⟩ := hdone i hi_lt_k
        simpa only [List.length_replicate] using ht.1
      · have hj_lt_k : j < k := by omega
        have hmj : st₁.mem (descBase + 4 * j + 2) = st.mem (descBase + 4 * j + 2) := by
          rw [hp_writes _ (.inl (by dsimp only [dAddr]; omega)),
            hp_a.2.2 _ (by dsimp only [descBase, count] at *; omega)]
        rw [hmj]
        exact hdisj i j hi_lt_k hj_lt_k hij
    have hc_step : memoryCost (initNodeStep (descBase, ⟨curRaw, k⟩)) st ≤ stepCost := by
      have hr_s (x : ℕ) : (Memory.spec 0).clientState st (Memory.read x) = st := rfl
      have hr_r (x : ℕ) : (Memory.spec 0).clientResult st (Memory.read x) = st.mem x := rfl
      unfold initNodeStep
      dsimp only
      rw [memoryCost_bind', memoryCost_read, hr_s, hr_r, hmem_len,
        memoryCost_bind', hst_pow, hr_pow,
        memoryCost_bind', memoryCost_alloc]
      change 1 + (memoryCost (powProg ⟨2, bagLen⟩) st +
        ((tblLen + 1) + memoryCost
          (Memory.write dAddr bagPtr >>= fun _ =>
            Memory.write (dAddr + 1) bagLen >>= fun _ =>
            Memory.write (dAddr + 2) tblPtr >>= fun _ =>
            Memory.write (dAddr + 3) tblLen >>= fun _ => pure _) st_a)) ≤ stepCost
      rw [memoryCost_bind', memoryCost_write,
        memoryCost_bind', memoryCost_write,
        memoryCost_bind', memoryCost_write,
        memoryCost_bind', memoryCost_write, memoryCost_pure]
      dsimp only [stepCost]
      omega
    obtain ⟨hv_rem, hprops_rem, hc_rem⟩ :=
      ih (k + 1) (bagPtr + bagLen) st₁ (by omega)
        (by change descBase + 4 * count ≤ st.frontier + tblLen; omega)
        hfr_next_le hpres₁ hrest_st₁
        (by simp only [List.length_cons, List.length_append] at hdrop_end; omega)
        hdone₁ hdisj₁
    have hiter_eq : iterate initNodeStep descBase (rem + 1) ⟨curRaw, k⟩ =
        (initNodeStep (descBase, ⟨curRaw, k⟩) >>= iterate initNodeStep descBase rem) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step', hres_step']), ?_, ?_⟩
    · rw [StateTransitionSpec.clientState_bind, hst_step', hres_step']
      exact hprops_rem
    · rw [memoryCost_bind', hst_step', hres_step']
      calc memoryCost (initNodeStep (descBase, ⟨curRaw, k⟩)) st +
            memoryCost (iterate initNodeStep descBase rem ⟨bagPtr + bagLen, k + 1⟩) st₁
          ≤ stepCost + rem * stepCost := Nat.add_le_add hc_step hc_rem
        _ = (rem + 1) * stepCost := by rw [Nat.succ_mul, Nat.add_comm]

/-- Exact-basis Word-RAM realization certificate for `initNodesProg`. -/
theorem initNodesProg_realizes :
    Realizes .exact initNodesProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 4 ∧
        ∃ (bags : List (List ℕ)) (M : ℕ),
          bags.length = args.count ∧
          (∀ B ∈ bags, B.length ≤ M) ∧
          HoldsIn args.rawBagsPtr (bags.flatMap encodeBag) s ∧
          Fits w (s.frontier + 4 * args.count + args.count * 2 ^ M))
      (fun _ _ => 0) := by
  unfold initNodesProg
  realize [powProg_realizes]
  · obtain ⟨_, _, _, _, _, _, hfit_peak⟩ := h
    exact hfit_peak.of_le (by omega)
  · exact h.1
  · obtain ⟨h4, bags, M, hbags_len, hbags_M, hraw_h, hfit_peak⟩ := h
    have h1 : Fits w 1 := h4.of_le (by decide)
    have h2 : Fits w 2 := h4.of_le (by decide)
    have h3 : Fits w 3 := h4.of_le (by decide)
    let descBase := s.frontier
    let s_d := (Memory.spec 0).clientState s (Memory.allocDirty (4 * d.count))
    have hp_d : PreservesBelow descBase s s_d := preservesBelow_allocDirty s (4 * d.count)
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : InitNodeState) (t : Memory.State) =>
        j ≤ d.count ∧ st.curIdx + j = d.count ∧
        descBase + 4 * d.count ≤ t.frontier ∧
        t.frontier ≤ descBase + 4 * d.count + st.curIdx * 2 ^ M ∧
        HoldsIn st.curRaw ((bags.drop st.curIdx).flatMap encodeBag) t ∧
        st.curRaw + ((bags.drop st.curIdx).flatMap encodeBag).length ≤ descBase)
      (fun j st t ⟨hj_le, hidx, hfr_lo, hfr_hi, hrem_raw, hrem_end⟩ => ?_)
      ⟨le_rfl, Nat.zero_add _, le_rfl, by simp [descBase],
        by
          dsimp only
          rw [List.drop_zero]
          exact hraw_h.mono_frontier hp_d,
        hraw_h.1⟩
    have hk_lt : st.curIdx < bags.length := by omega
    have hdrop_cons : bags.drop st.curIdx = bags[st.curIdx] :: bags.drop (st.curIdx + 1) :=
      List.drop_eq_getElem_cons hk_lt
    rw [hdrop_cons, List.flatMap_cons, encodeBag, List.cons_append] at hrem_raw hrem_end
    rw [HoldsIn.cons_iff] at hrem_raw
    obtain ⟨_, hmem_len, hafter_len⟩ := hrem_raw
    rw [HoldsIn.append_iff] at hafter_len
    obtain ⟨_, hrest_raw⟩ := hafter_len
    have hblen_le : t.mem st.curRaw ≤ M := by
      rw [hmem_len]
      exact hbags_M _ (List.getElem_mem hk_lt)
    have hpow_le : 2 ^ t.mem st.curRaw ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) hblen_le
    have hfr_next : t.frontier + 2 ^ t.mem st.curRaw ≤
        descBase + 4 * d.count + (st.curIdx + 1) * 2 ^ M := by
      calc t.frontier + 2 ^ t.mem st.curRaw
          ≤ (descBase + 4 * d.count + st.curIdx * 2 ^ M) + 2 ^ M := Nat.add_le_add hfr_hi hpow_le
        _ = descBase + 4 * d.count + (st.curIdx + 1) * 2 ^ M := by
          rw [Nat.add_assoc, ← Nat.succ_mul]
    have hpeak_sub : descBase + 4 * d.count + (st.curIdx + 1) * 2 ^ M ≤
        descBase + 4 * d.count + d.count * 2 ^ M := by
      have hle_dc : st.curIdx + 1 ≤ d.count := by omega
      have hmul : (st.curIdx + 1) * 2 ^ M ≤ d.count * 2 ^ M := Nat.mul_le_mul_right _ hle_dc
      omega
    have hpow_safe : Fits w 1 ∧ Fits w (2 ^ t.mem st.curRaw) :=
      ⟨h1, hfit_peak.of_le (by omega)⟩
    have hpow_res : (Memory.spec 0).clientResult t (powProg ⟨2, t.mem st.curRaw⟩) =
        2 ^ t.mem st.curRaw := powProg_result _ t
    simp only [List.length_cons, List.length_append] at hrem_end
    have hfit_bp : Fits w (st.curRaw + 1) := hfit_peak.of_le (by omega)
    have hfit_mul4 : Fits w (4 * st.curIdx) := hfit_peak.of_le (by omega)
    have hfit_d0 : Fits w (descBase + 4 * st.curIdx) := hfit_peak.of_le (by omega)
    have hfit_d1 : Fits w (descBase + 4 * st.curIdx + 1) := hfit_peak.of_le (by omega)
    have hfit_d2 : Fits w (descBase + 4 * st.curIdx + 2) := hfit_peak.of_le (by omega)
    have hfit_d3 : Fits w (descBase + 4 * st.curIdx + 3) := hfit_peak.of_le (by omega)
    have hfit_next_raw : Fits w (st.curRaw + 1 + t.mem st.curRaw) :=
      hfit_peak.of_le (by omega)
    have hfit_next_idx : Fits w (st.curIdx + 1) := hfit_peak.of_le (by omega)
    obtain ⟨hst_ev, hres_ev⟩ := initNodeStep_eval descBase st t
    refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [initNodeStep]
      repeat (first | exact hpow_safe | assumption | refine And.intro ?_ ?_)
    · rw [hres_ev]; change (st.curIdx + 1) + j = d.count; omega
    · rw [hst_ev]; change descBase + 4 * d.count ≤ t.frontier + _; omega
    · rw [hst_ev, hres_ev]; exact hfr_next
    · rw [hst_ev, hres_ev]
      change HoldsIn (st.curRaw + 1 + t.mem st.curRaw)
        ((bags.drop (st.curIdx + 1)).flatMap encodeBag) _
      rw [hmem_len]
      refine ⟨hrest_raw.1.trans (Nat.le_add_right _ _), hrest_raw.2.frame fun a _ ha => ?_⟩
      dsimp only
      rw [Function.update_of_ne (by dsimp only [descBase] at *; omega),
        Function.update_of_ne (by dsimp only [descBase] at *; omega),
        Function.update_of_ne (by dsimp only [descBase] at *; omega),
        Function.update_of_ne (by dsimp only [descBase] at *; omega)]
      exact clear_of_not_owns (by dsimp only [Block.Owns, descBase] at *; omega)
    · rw [hres_ev]
      change (st.curRaw + 1 + t.mem st.curRaw) + _ ≤ descBase
      dsimp only [descBase] at *
      omega

end Cslib.Algorithms.WordRAM.TreeDecomposition
