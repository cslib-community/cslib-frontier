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
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
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
    rw [hp.2.2 (descBase + 4 * i.val) (Nat.lt_of_lt_of_le (by omega) h.desc_hi),
      hp.2.2 (descBase + 4 * i.val + 1) (Nat.lt_of_lt_of_le (by omega) h.desc_hi),
      hp.2.2 (descBase + 4 * i.val + 3) (Nat.lt_of_lt_of_le (by omega) h.desc_hi)]
    exact ⟨h1, h3, hlo, hb.mono_frontier hp⟩
  tbl_holds i := by
    obtain ⟨hlen, hlo, ht⟩ := h.tbl_holds i
    rw [hp.2.2 (descBase + 4 * i.val + 2) (Nat.lt_of_lt_of_le (by omega) h.desc_hi)]
    exact ⟨hlen, hlo, ht.mono_frontier hp⟩
  tbl_disj i j hij := by
    rw [hp.2.2 (descBase + 4 * i.val + 2) (Nat.lt_of_lt_of_le (by omega) h.desc_hi),
      hp.2.2 (descBase + 4 * j.val + 2) (Nat.lt_of_lt_of_le (by omega) h.desc_hi)]
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
  have hlow_holds {addr : ℕ} {xs : List ℕ} (hs : HoldsIn addr xs s)
      (hhi : addr + xs.length ≤ descBase + 4 * (inst.numNodes + 1)) : HoldsIn addr xs s' :=
    ⟨hfr ▸ hs.1, hs.2.frame fun a _ ha => hlow_eq a (lt_of_lt_of_le ha hhi)⟩
  refine
    { wt_holds := hlow_holds h.wt_holds (by rw [inst.weights_len]; omega)
      adj_holds := hlow_holds h.adj_holds (by rw [inst.adjMatrix_len]; omega)
      par_holds := hlow_holds h.par_holds (by rw [inst.parents_len]; omega)
      desc_lo := h.desc_lo
      desc_hi := hfr ▸ h.desc_hi
      bags_holds := fun i => by
        obtain ⟨h1, h3, hblo, hb⟩ := h.bags_holds i
        have := i.isLt
        rw [hlow_eq (descBase + 4 * i.val) (by omega),
          hlow_eq (descBase + 4 * i.val + 1) (by omega),
          hlow_eq (descBase + 4 * i.val + 3) (by omega)]
        exact ⟨h1, h3, hblo, hlow_holds hb (by omega)⟩
      tbl_holds := fun i => by
        have := i.isLt
        rw [hlow_eq (descBase + 4 * i.val + 2) (by omega)]
        by_cases hip : i = p
        · subst hip
          simpa only [Function.update_self] using ⟨hnew_len, hp_lo, hholdP⟩
        · rw [Function.update_of_ne hip]
          obtain ⟨hlen, hlo, ht⟩ := h.tbl_holds i
          refine ⟨hlen, hlo, ⟨hfr ▸ ht.1, ht.2.frame fun a ha1 ha2 => ?_⟩⟩
          rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hip) with hilt | hpilt
          · exact hout a (.inl (lt_of_lt_of_le (hlen ▸ ha2) (h.tbl_disj i p hilt)))
          · exact hout a (.inr ((h.tbl_disj p i hpilt).trans ha1))
      tbl_disj := fun i j hij => by
        have := i.isLt
        have := j.isLt
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
  refine Finset.sum_eq_zero fun i _ => ?_
  unfold nodeMax
  split_ifs with hi
  · exact Nat.eq_zero_of_le_zero
      (List.foldl_max_le le_rfl fun x hx => (List.eq_of_mem_replicate hx).le)
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
  simp only [prefixMaxSum, Finset.sum_range_succ, nodeMax, dite_eq_left (Nat.lt_succ_of_le hk)]

/-- Telescoping step: folding node `k + 1`'s table into strictly earlier parent `p < k + 1`
increases the remaining prefix sum `0 .. k` by at most `B` relative to `0 .. k + 1`. -/
theorem prefixMaxSum_update_le {n : ℕ} (tblList : Fin (n + 1) → List ℕ)
    {k B : ℕ} (hk : k + 1 ≤ n) (p : Fin (n + 1)) (hp_lt : p.val < k + 1)
    (newP : List ℕ)
    (hnew : newP.foldl max 0 ≤
      (tblList p).foldl max 0 + B + (tblList ⟨k + 1, by omega⟩).foldl max 0) :
    prefixMaxSum (Function.update tblList p newP) k ≤ prefixMaxSum tblList (k + 1) + B := by
  have hp_mem : p.val ∈ Finset.range (k + 1) := Finset.mem_range.2 hp_lt
  have herase : _ = prefixMaxSum tblList k := Finset.add_sum_erase _ (nodeMax tblList) hp_mem
  have hrest : ∑ i ∈ (Finset.range (k + 1)).erase p.val,
      nodeMax (Function.update tblList p newP) i =
      ∑ i ∈ (Finset.range (k + 1)).erase p.val, nodeMax tblList i :=
    Finset.sum_congr rfl fun i hi => by
      unfold nodeMax
      split_ifs with hlt
      · rw [Function.update_of_ne (Fin.ne_of_val_ne (Finset.mem_erase.1 hi).1)]
      · rfl
  rw [nodeMax, dite_eq_left p.isLt, Fin.eta] at herase
  rw [prefixMaxSum, ← Finset.add_sum_erase _ _ hp_mem, hrest, nodeMax, dite_eq_left p.isLt,
    Fin.eta, Function.update_self, prefixMaxSum_succ tblList hk, ← herase]
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
  let descBase := s₀.frontier
  have hfit_d : Fits w (s₀.frontier + 4 * count) := hfit_peak.of_le (by omega)
  have hraw_lo : rawBagsPtr ≤ descBase := by have := hbags₀.1; omega
  let NodeInv (m : ℕ) (t : Memory.State) : Prop :=
    (∀ i : Fin count, i.val < m →
      t.mem (descBase + 4 * i.val + 1) = (inst.bagAt i).length ∧
      t.mem (descBase + 4 * i.val + 3) = 2 ^ (inst.bagAt i).length ∧
      t.mem (descBase + 4 * i.val) + (inst.bagAt i).length ≤ descBase ∧
      HoldsIn (t.mem (descBase + 4 * i.val)) (inst.bagAt i) t ∧
      descBase + 4 * count ≤ t.mem (descBase + 4 * i.val + 2) ∧
      HoldsIn (t.mem (descBase + 4 * i.val + 2))
        (List.replicate (2 ^ (inst.bagAt i).length) 0) t) ∧
    ∀ i j : Fin count, i.val < m → j.val < m → i.val < j.val →
      t.mem (descBase + 4 * i.val + 2) + 2 ^ (inst.bagAt i).length ≤
        t.mem (descBase + 4 * j.val + 2)
  obtain ⟨-, hloop⟩ := Memory.FramedTriple.iterate (w := w)
    (s := ⟨s₀.mem, s₀.frontier + 4 * count⟩) (body := initNodeStep)
    (c := 2 ^ inst.maxBagLen + inst.maxBagLen + 6) (S := Set.Ici descBase)
    (safe := fun _ _ _ => True) (d := descBase) (n := count) (a₀ := ⟨rawBagsPtr, 0⟩)
    (Q := fun _ t => descBase + 4 * count ≤ t.frontier ∧
      t.frontier ≤ descBase + 4 * count + count * 2 ^ inst.maxBagLen ∧ NodeInv count t)
    (fun k st t => st.curIdx = k ∧
      t.frontier ≤ descBase + 4 * count + k * 2 ^ inst.maxBagLen ∧
      HoldsIn st.curRaw ((inst.bags.drop k).flatMap encodeBag) t ∧
      st.curRaw + ((inst.bags.drop k).flatMap encodeBag).length ≤ descBase ∧ NodeInv k t)
    ⟨rfl, by dsimp only; omega, by
      rw [List.drop_zero]; exact hbags₀.mono_frontier (preservesBelow_allocDirty s₀ (4 * count)),
      hbags₀.1, fun _ hi => absurd hi (Nat.not_lt_zero _),
      fun _ _ hi _ _ => absurd hi (Nat.not_lt_zero _)⟩
    (fun k hk ⟨curRaw, idx⟩ t ⟨hidx, hfr_hi, hdrop, hdrop_end, hdone, hdisj⟩ hmod => ⟨trivial, by
      dsimp only at hidx hdrop hdrop_end
      subst idx
      have hfr_lo : descBase + 4 * count ≤ t.frontier := hmod.1
      have hpres : PreservesBelow descBase s₀ t :=
        ⟨le_rfl, (Nat.le_add_right _ _).trans hmod.1,
          fun a ha => hmod.2 a (by dsimp only; omega) (by simpa using ha)⟩
      have hk_bags : k < inst.bags.length := by rw [inst.bags_len]; exact hk
      let kFin : Fin count := ⟨k, hk⟩
      have hdrop_cons : inst.bags.drop k = inst.bagAt kFin :: inst.bags.drop (k + 1) :=
        List.drop_eq_getElem_cons hk_bags
      rw [hdrop_cons, List.flatMap_cons, encodeBag, List.cons_append] at hdrop hdrop_end
      obtain ⟨_, hmem_len, hafter_len⟩ := HoldsIn.cons_iff.mp hdrop
      obtain ⟨hbag_k, hrest_raw⟩ := HoldsIn.append_iff.mp hafter_len
      simp only [List.length_cons, List.length_append] at hdrop_end
      have hlenM := inst.bagAt_length_le kFin
      have hpowM : 2 ^ (inst.bagAt kFin).length ≤ 2 ^ inst.maxBagLen :=
        Nat.pow_le_pow_right (by decide) hlenM
      have hfr_next_le : t.frontier + 2 ^ (inst.bagAt kFin).length ≤
          descBase + 4 * count + (k + 1) * 2 ^ inst.maxBagLen :=
        (Nat.add_le_add hfr_hi hpowM).trans_eq (by rw [Nat.add_assoc, ← Nat.succ_mul])
      have hfit_alloc : Fits w (t.frontier + 2 ^ (inst.bagAt kFin).length) := hfit_peak.of_le (by
        have hmul : (k + 1) * 2 ^ inst.maxBagLen ≤ count * 2 ^ inst.maxBagLen :=
          Nat.mul_le_mul_right _ (by omega)
        dsimp only [count, descBase] at hfr_next_le hmul ⊢; omega)
      have hfit_fr : Fits w t.frontier := hfit_alloc.of_le (Nat.le_add_right _ _)
      have hfit_pow : Fits w (2 ^ (inst.bagAt kFin).length) :=
        hfit_alloc.of_le (Nat.le_add_left _ _)
      have hbagPtr_fit : Fits w (curRaw + 1) :=
        hfit_raw.of_le (by dsimp only [descBase] at *; omega)
      have hbagLen_fit : Fits w (inst.bagAt kFin).length :=
        hfit_raw.of_le (by dsimp only [descBase] at *; omega)
      have hpow := powProg_framed (w := w) ⟨2, (inst.bagAt kFin).length⟩ (by omega : 0 < t.frontier)
      dsimp only at hpow
      let bagLen := (inst.bagAt kFin).length
      let bagPtr := curRaw + 1
      let tblLen := 2 ^ bagLen
      let tblPtr := t.frontier
      let dAddr := descBase + 4 * k
      let m1 := Function.update (clear t.mem t.frontier tblLen) dAddr bagPtr
      let m2 := Function.update m1 (dAddr + 1) bagLen
      let m3 := Function.update m2 (dAddr + 2) tblPtr
      let m4 := Function.update m3 (dAddr + 3) tblLen
      let st₁ : Memory.State := ⟨m4, t.frontier + tblLen⟩
      have hp_writes : ∀ addr, (addr < dAddr ∨ dAddr + 4 ≤ addr) →
          st₁.mem addr = clear t.mem t.frontier tblLen addr := fun addr _ => by
        dsimp only [st₁, m4, m3, m2, m1]
        repeat rw [Function.update_of_ne (by omega)]
      have hp_a : PreservesBelow t.frontier t
          ⟨clear t.mem t.frontier tblLen, t.frontier + tblLen⟩ := preservesBelow_alloc t tblLen
      have hmem_lt : ∀ a < dAddr, st₁.mem a = t.mem a := fun a ha =>
        (hp_writes a (.inl ha)).trans
          (hp_a.2.2 a (by dsimp only [dAddr, descBase, count] at *; omega))
      have hpres_step : PreservesBelow descBase t st₁ :=
        ⟨by omega, Nat.le_add_right _ _, fun a ha => hmem_lt a (by dsimp only [dAddr]; omega)⟩
      have hbag_k_st₁ : HoldsIn bagPtr (inst.bagAt kFin) st₁ :=
        hbag_k.mono (by dsimp only [bagPtr, descBase] at *; omega) hpres_step
      have hrest_st₁ :
          HoldsIn (bagPtr + bagLen) ((inst.bags.drop (k + 1)).flatMap encodeBag) st₁ :=
        hrest_raw.mono (by dsimp only [bagPtr, bagLen, descBase] at *; omega) hpres_step
      have htbl_zero_a := holdsIn_alloc_zero t tblLen
      have htbl_k_st₁ : HoldsIn tblPtr (List.replicate tblLen 0) st₁ :=
        ⟨htbl_zero_a.1, htbl_zero_a.2.frame fun a ha _ =>
          hp_writes a (.inr (by dsimp only [tblPtr, tblLen, dAddr, descBase, count] at *; omega))⟩
      obtain ⟨hm4_0, hm4_1, hm4_2, hm4_3⟩ :
          st₁.mem dAddr = bagPtr ∧ st₁.mem (dAddr + 1) = bagLen ∧
            st₁.mem (dAddr + 2) = tblPtr ∧ st₁.mem (dAddr + 3) = tblLen := by
        simp [st₁, m4, m3, m2, m1, Nat.left_eq_add]
      have hinv₁ : NodeInv (k + 1) st₁ := by
        refine ⟨fun i hi => ?_, fun i j hi hj hij => ?_⟩
        · by_cases hik : i = kFin
          · subst hik
            change st₁.mem (dAddr + 1) = _ ∧ st₁.mem (dAddr + 3) = _ ∧
              st₁.mem dAddr + _ ≤ _ ∧ HoldsIn (st₁.mem dAddr) _ _ ∧
              _ ≤ st₁.mem (dAddr + 2) ∧ HoldsIn (st₁.mem (dAddr + 2)) _ _
            rw [hm4_0, hm4_1, hm4_2, hm4_3]
            exact ⟨rfl, rfl, by dsimp only [bagPtr, descBase] at *; omega,
              hbag_k_st₁, hfr_lo, htbl_k_st₁⟩
          · have hik_lt : i.val < k :=
              Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) (Fin.val_ne_of_ne hik)
            obtain ⟨h1, h3, hblo, hb, htlo, ht⟩ := hdone i hik_lt
            rw [hmem_lt (descBase + 4 * i.val) (by dsimp only [dAddr]; omega),
              hmem_lt (descBase + 4 * i.val + 1) (by dsimp only [dAddr]; omega),
              hmem_lt (descBase + 4 * i.val + 2) (by dsimp only [dAddr]; omega),
              hmem_lt (descBase + 4 * i.val + 3) (by dsimp only [dAddr]; omega)]
            refine ⟨h1, h3, hblo, hb.mono hblo hpres_step, htlo,
              ⟨ht.1.trans (Nat.le_add_right _ _), ht.2.frame fun a ha hlt => ?_⟩⟩
            exact (hp_writes a (.inr (by dsimp only [dAddr, descBase, count] at *; omega))).trans
              (hp_a.2.2 a (lt_of_lt_of_le hlt ht.1))
        · have hi_lt_k : i.val < k := by omega
          rw [hmem_lt (descBase + 4 * i.val + 2) (by dsimp only [dAddr]; omega)]
          by_cases hjk : j = kFin
          · subst hjk
            obtain ⟨-, -, -, -, -, ht⟩ := hdone i hi_lt_k
            exact (List.length_replicate ▸ ht.1).trans_eq hm4_2.symm
          · have hj_lt_k : j.val < k :=
              Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hj) (Fin.val_ne_of_ne hjk)
            rw [hmem_lt (descBase + 4 * j.val + 2) (by dsimp only [dAddr]; omega)]
            exact hdisj i j hi_lt_k hj_lt_k hij
      unfold initNodeStep
      dsimp only
      refine Memory.FramedTriple.read_bind (by omega) ?_
      rw [hmem_len]
      framed_walk
      exact ⟨rfl, hfr_next_le, hrest_st₁, by dsimp only [bagPtr, bagLen] at *; omega, hinv₁⟩⟩)
    fun _ t ⟨_, hfr, _, _, hinv⟩ hmod => ⟨hmod.1, hfr, hinv⟩
  have hft : Memory.FramedTriple w s₀ (initNodesProg ⟨rawBagsPtr, count⟩)
      (1 + count * (2 ^ inst.maxBagLen + inst.maxBagLen + 6)) (Set.Ici descBase) fun r t =>
        r = descBase ∧ descBase + 4 * count ≤ t.frontier ∧
          t.frontier ≤ descBase + 4 * count + count * 2 ^ inst.maxBagLen ∧ NodeInv count t := by
    unfold initNodesProg
    exact Memory.FramedTriple.mono (Memory.FramedTriple.allocDirty_bind hfit_d
      (Memory.FramedTriple.call (c₂ := 0) hloop subset_rfl fun _ _ h _ =>
        Memory.FramedTriple.pure ⟨rfl, h⟩)) (by rw [Nat.mul_comm]; omega) fun _ _ => id
  obtain ⟨hv, hc, hmod, hres, hfr_lo, hfr_hi, hnodes_end, hdisj_end⟩ :=
    framedTriple_iff_realization.mp hft
  have hpres_end : PreservesBelow descBase s₀ ((Memory.spec 0).clientState s₀
      (initNodesProg ⟨rawBagsPtr, count⟩)) :=
    ⟨le_rfl, hmod.1, fun a ha => hmod.2 a ha (by simpa using ha)⟩
  refine ⟨hv, hres, hfr_hi, hres ▸
    { wt_holds := hwt₀.mono_frontier hpres_end
      adj_holds := hadj₀.mono_frontier hpres_end
      par_holds := hpar₀.mono_frontier hpres_end
      desc_lo := hraw_lo
      desc_hi := hfr_lo
      bags_holds := fun i =>
        let ⟨h1, h3, hblo, hb, _, _⟩ := hnodes_end i i.isLt
        ⟨h1, h3, hblo, hb⟩
      tbl_holds := fun i =>
        let ⟨_, _, _, _, htlo, ht⟩ := hnodes_end i i.isLt
        ⟨List.length_replicate, htlo, ht⟩
      tbl_disj := fun i j => hdisj_end i j i.isLt j.isLt }, hc⟩

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
      ⟨le_rfl, Nat.zero_add _, le_rfl, by simp [descBase], hraw_h.mono_frontier hp_d, hraw_h.1⟩
    have hk_lt : st.curIdx < bags.length := by omega
    have hdrop_cons : bags.drop st.curIdx = bags[st.curIdx] :: bags.drop (st.curIdx + 1) :=
      List.drop_eq_getElem_cons hk_lt
    rw [hdrop_cons, List.flatMap_cons, encodeBag, List.cons_append] at hrem_raw hrem_end
    obtain ⟨_, hmem_len, hafter_len⟩ := HoldsIn.cons_iff.mp hrem_raw
    obtain ⟨_, hrest_raw⟩ := HoldsIn.append_iff.mp hafter_len
    have hblen_le : t.mem st.curRaw ≤ M := hmem_len ▸ hbags_M _ (List.getElem_mem hk_lt)
    have hpow_le : 2 ^ t.mem st.curRaw ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) hblen_le
    have hfr_next : t.frontier + 2 ^ t.mem st.curRaw ≤
        descBase + 4 * d.count + (st.curIdx + 1) * 2 ^ M := by
      calc t.frontier + 2 ^ t.mem st.curRaw
          ≤ (descBase + 4 * d.count + st.curIdx * 2 ^ M) + 2 ^ M := Nat.add_le_add hfr_hi hpow_le
        _ = descBase + 4 * d.count + (st.curIdx + 1) * 2 ^ M := by
          rw [Nat.add_assoc, ← Nat.succ_mul]
    have hmul : (st.curIdx + 1) * 2 ^ M ≤ d.count * 2 ^ M :=
      Nat.mul_le_mul_right _ (by omega)
    have hpow_safe : Fits w 1 ∧ Fits w (2 ^ t.mem st.curRaw) :=
      ⟨h1, hfit_peak.of_le (by omega)⟩
    have hpow_res : (Memory.spec 0).clientResult t (powProg ⟨2, t.mem st.curRaw⟩) =
        2 ^ t.mem st.curRaw := powProg_result _ t
    simp only [List.length_cons, List.length_append] at hrem_end
    obtain ⟨hst_ev, hres_ev⟩ := initNodeStep_eval s.frontier st t
    refine ⟨?_, Nat.le_of_succ_le hj_le,
      by simp only [hres_ev]; omega,
      by simp only [hst_ev, descBase] at *; omega,
      by rwa [hst_ev, hres_ev], ?_,
      by simp only [hres_ev, descBase] at *; omega⟩
    · dsimp only [initNodeStep]
      repeat (first
        | exact hpow_safe
        | assumption
        | refine And.intro ?_ ?_
        | exact hfit_peak.of_le (by omega))
    · simp only [hst_ev, hres_ev, hmem_len]
      refine ⟨hrest_raw.1.trans (Nat.le_add_right _ _), hrest_raw.2.frame fun a _ ha => ?_⟩
      dsimp only
      repeat rw [Function.update_of_ne (by dsimp only [descBase] at *; omega)]
      exact clear_of_not_owns (by dsimp only [Block.Owns, descBase] at *; omega)

end Cslib.Algorithms.WordRAM.TreeDecomposition
