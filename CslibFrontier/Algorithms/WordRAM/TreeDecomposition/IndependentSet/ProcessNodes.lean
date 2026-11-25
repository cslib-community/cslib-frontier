/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.NodeLayout
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.ChildPass
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.MaskOps
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.ParentPass
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.WeightScan
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Tactic.Realize

/-!
# Bottom-up node-processing loop (`processNodesProg`)

This module certifies `processNodesProg`, which visits all nonroot decomposition nodes
`numNodes, numNodes - 1, …, 1` in reverse index order, allocates the `2 ^ |LP|`-word scratch
array `best`, runs `childPassProg` and `parentPassProg`, preserves `NodeLayout`, maintains the
telescoping entry bound `prefixMaxSum tblList k ≤ (numNodes - k) * maxBagLen * maxWeight`, and
agrees pointwise with `tablesInst`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.ProcessNodesArgs`: register arguments for
  `processNodesProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.processNodesProg`: reverse-index bottom-up DP loop.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.processNodesProg_spec`: layout preservation,
  telescoping table-entry bound, pointwise agreement with `tablesInst`, and cost bound.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.processNodesProg_realizes`: exact-basis Word-RAM
  realization certificate.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-- Register arguments for `processNodesProg`. -/
structure ProcessNodesArgs where
  /-- Number of graph vertices `m`. -/
  numVerts : ℕ
  /-- Base memory address of the `m × m` adjacency matrix. -/
  adjPtr : ℕ
  /-- Base memory address of the `m`-word weight array. -/
  wtPtr : ℕ
  /-- Base memory address of the `(numNodes + 1)`-word parent array. -/
  parPtr : ℕ
  /-- Base memory address of the `4 * (numNodes + 1)`-word node descriptor block. -/
  descBase : ℕ
  /-- Number `n` of nonroot nodes (`1 .. n`). -/
  numNodes : ℕ

/-- Tuple equivalence encoding `ProcessNodesArgs` into Word-RAM registers. -/
@[expose] def ProcessNodesArgs.equiv :
    ProcessNodesArgs ≃ ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := (((((a.numVerts, a.adjPtr), a.wtPtr), a.parPtr), a.descBase), a.numNodes)
  invFun := fun (((((nv, ap), wp), pp), db), nn) => ⟨nv, ap, wp, pp, db, nn⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding ProcessNodesArgs := .ofEquiv ProcessNodesArgs.equiv

private def processNodeStep (q : ProcessNodesArgs × ℕ) : Memory.Prog ℕ := do
  let a := q.1
  let curNode := q.2
  let p ← Memory.read (a.parPtr + curNode)
  let dJ := a.descBase + 4 * curNode
  let bagBPtr ← Memory.read dJ
  let bagBLen ← Memory.read (dJ + 1)
  let tblBPtr ← Memory.read (dJ + 2)
  let tblBLen ← Memory.read (dJ + 3)
  let dP := a.descBase + 4 * p
  let bagPPtr ← Memory.read dP
  let bagPLen ← Memory.read (dP + 1)
  let tblPPtr ← Memory.read (dP + 2)
  let tblPLen ← Memory.read (dP + 3)
  let bestPtr ← Memory.alloc tblPLen
  let _ ← childPassProg
    ⟨a.numVerts, a.adjPtr, a.wtPtr, bagBPtr, bagBLen, tblBPtr, tblBLen,
      bagPPtr, bagPLen, bestPtr⟩
  let _ ← parentPassProg
    ⟨bagBPtr, bagBLen, bagPPtr, bagPLen, tblPPtr, tblPLen, bestPtr⟩
  pure (curNode - 1)

/-- Process all `args.numNodes` nonroot nodes `n, n - 1, …, 1` bottom-up. -/
def processNodesProg (args : ProcessNodesArgs) : Memory.Prog Unit := do
  let _ ← iterate processNodeStep args args.numNodes args.numNodes
  pure ()

private theorem processNodeStep_eval (a : ProcessNodesArgs) (curNode : ℕ) (t : Memory.State) :
    let p := t.mem (a.parPtr + curNode)
    let dJ := a.descBase + 4 * curNode
    let bagBPtr := t.mem dJ
    let bagBLen := t.mem (dJ + 1)
    let tblBPtr := t.mem (dJ + 2)
    let tblBLen := t.mem (dJ + 3)
    let dP := a.descBase + 4 * p
    let bagPPtr := t.mem dP
    let bagPLen := t.mem (dP + 1)
    let tblPPtr := t.mem (dP + 2)
    let tblPLen := t.mem (dP + 3)
    let bestPtr := t.frontier
    let t_a := (Memory.spec 0).clientState t (Memory.alloc tblPLen)
    let t_c := (Memory.spec 0).clientState t_a
      (childPassProg ⟨a.numVerts, a.adjPtr, a.wtPtr, bagBPtr, bagBLen, tblBPtr, tblBLen,
        bagPPtr, bagPLen, bestPtr⟩)
    let t_p := (Memory.spec 0).clientState t_c
      (parentPassProg ⟨bagBPtr, bagBLen, bagPPtr, bagPLen, tblPPtr, tblPLen, bestPtr⟩)
    (Memory.spec 0).clientState t (processNodeStep (a, curNode)) = t_p ∧
    (Memory.spec 0).clientResult t (processNodeStep (a, curNode)) = curNode - 1 := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold processNodeStep
  dsimp only
  iterate 9 rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    hr_st, hr_res]
  have ha_res : (Memory.spec 0).clientResult t
      (Memory.alloc (t.mem (a.descBase + 4 * t.mem (a.parPtr + curNode) + 3))) = t.frontier := rfl
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, ha_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
  exact ⟨rfl, rfl⟩

private theorem cp_cost_poly_le {bj bp M : ℕ} (hj : bj ≤ M) (hp : bp ≤ M) :
    bj * (2 * bj + 1) + bp * (bj + 1) + bj * (bp + 2) + 3 ≤ 4 * M ^ 2 + 4 * M + 3 := by
  nlinarith

private theorem pp_cost_poly_le {bj bp M : ℕ} (hj : bj ≤ M) (hp : bp ≤ M) :
    bp * (bj + 1) + 3 ≤ M ^ 2 + M + 3 := by
  nlinarith

private theorem step_pow_sum_le {P t : ℕ} (ht : t ≤ P) (M : ℕ) :
    P * (4 * M ^ 2 + 4 * M + 3) + P * (M ^ 2 + M + 3) + t ≤ P * (5 * M ^ 2 + 5 * M + 7) := by
  nlinarith

private abbrev ChildPassPre (w : ℕ) (args : ChildPassArgs) (s : Memory.State) : Prop :=
  Fits w 2 ∧
  ∃ m adjL wtL LB LP tblB initL cap,
    adjL.length = m * m ∧ wtL.length = m ∧ args.numVerts = m ∧
    HoldsIn args.adjPtr adjL s ∧ args.adjPtr + adjL.length ≤ args.bestPtr ∧
    HoldsIn args.wtPtr wtL s ∧ args.wtPtr + wtL.length ≤ args.bestPtr ∧
    HoldsIn args.bagBPtr LB s ∧ LB.length = args.bagBLen ∧
    args.bagBPtr + args.bagBLen ≤ args.bestPtr ∧ (∀ u ∈ LB, u < m) ∧
    HoldsIn args.tblBPtr tblB s ∧ tblB.length = args.tblBLen ∧
    args.tblBPtr + args.tblBLen ≤ args.bestPtr ∧
    HoldsIn args.bagPPtr LP s ∧ LP.length = args.bagPLen ∧
    args.bagPPtr + args.bagPLen ≤ args.bestPtr ∧
    HoldsIn args.bestPtr initL s ∧ initL.length = 2 ^ args.bagPLen ∧
    args.bagBLen * wtL.foldl max 0 + tblB.foldl max 0 ≤ cap ∧
    Fits w (args.adjPtr + m * m) ∧ Fits w (args.wtPtr + m) ∧
    Fits w (args.bagBPtr + args.bagBLen) ∧ Fits w (args.tblBPtr + args.tblBLen) ∧
    Fits w (args.bagPPtr + args.bagPLen) ∧ Fits w (2 ^ args.bagPLen) ∧
    Fits w (args.bestPtr + 2 ^ args.bagPLen) ∧ Fits w cap

private abbrev ParentPassPre (w : ℕ) (args : ParentPassArgs) (s : Memory.State) : Prop :=
  Fits w 2 ∧
  ∃ LB LP oldL bestL capO capB,
    HoldsIn args.bagBPtr LB s ∧ LB.length = args.bagBLen ∧
    args.bagBPtr + args.bagBLen ≤ args.tblPPtr ∧
    HoldsIn args.bagPPtr LP s ∧ LP.length = args.bagPLen ∧
    args.bagPPtr + args.bagPLen ≤ args.tblPPtr ∧
    HoldsIn args.tblPPtr oldL s ∧ oldL.length = args.tblPLen ∧
    args.tblPLen = 2 ^ args.bagPLen ∧
    args.tblPPtr + args.tblPLen ≤ args.bestPtr ∧
    HoldsIn args.bestPtr bestL s ∧ bestL.length = 2 ^ args.bagPLen ∧
    oldL.foldl max 0 ≤ capO ∧ bestL.foldl max 0 ≤ capB ∧
    Fits w (args.bagBPtr + args.bagBLen) ∧ Fits w (args.bagPPtr + args.bagPLen) ∧
    Fits w (args.tblPPtr + args.tblPLen) ∧ Fits w (2 ^ args.bagPLen) ∧
    Fits w (args.bestPtr + 2 ^ args.bagPLen) ∧ Fits w (capO + capB)

private theorem processNodeStep_full {w : ℕ} (inst : MWISInstance) (descBase : ℕ)
    {a : ProcessNodesArgs}
    (ha : a = ⟨inst.numVerts, 3 + inst.numVerts, 3,
      3 + inst.numVerts + inst.numVerts * inst.numVerts, descBase, inst.numNodes⟩)
    {k : ℕ} (hk : k + 1 ≤ inst.numNodes)
    {tblList : Fin (inst.numNodes + 1) → List ℕ} {t : Memory.State}
    (hlay : NodeLayout inst descBase tblList t)
    (hpfx : prefixMaxSum tblList (k + 1) ≤
      (inst.numNodes - (k + 1)) * (inst.maxBagLen * inst.maxWeight))
    (hfit_fr : Fits w (t.frontier + 2 ^ inst.maxBagLen))
    (hfit_val : Fits w ((inst.numNodes + 1) * inst.maxBagLen * inst.maxWeight)) :
    let jFin : Fin (inst.numNodes + 1) := ⟨k + 1, by omega⟩
    let pFin := inst.parFin jFin
    let bestL := childPassList inst.adj inst.wt (inst.bagAt jFin) (inst.bagAt pFin)
      (tblList jFin) (List.replicate (2 ^ (inst.bagAt pFin).length) 0)
      (2 ^ (inst.bagAt jFin).length)
    let newTblP := parentPassPrefix (inst.bagAt jFin) (inst.bagAt pFin)
      (tblList pFin) bestL (2 ^ (inst.bagAt pFin).length)
    let tblList' := Function.update tblList pFin newTblP
    let t' := (Memory.spec 0).clientState t (processNodeStep (a, k + 1))
    (Memory.spec w).ValidHistory t
      ((Memory.spec w).clientHistory t (processNodeStep (a, k + 1))) ∧
    (Memory.spec 0).clientResult t (processNodeStep (a, k + 1)) = k ∧
    t'.frontier ≤ t.frontier + 2 ^ inst.maxBagLen ∧
    NodeLayout inst descBase tblList' t' ∧
    prefixMaxSum tblList' k ≤ (inst.numNodes - k) * (inst.maxBagLen * inst.maxWeight) ∧
    memoryCost (processNodeStep (a, k + 1)) t ≤
      10 + 2 ^ inst.maxBagLen * (5 * inst.maxBagLen ^ 2 + 5 * inst.maxBagLen + 7) ∧
    (Fits w 4 →
      let dJ := a.descBase + 4 * (k + 1)
      let p := t.mem (a.parPtr + (k + 1))
      let dP := a.descBase + 4 * p
      let t_alloc : Memory.State :=
        { mem := clear t.mem t.frontier (t.mem (dP + 3))
          frontier := t.frontier + t.mem (dP + 3) }
      let cpA : ChildPassArgs :=
        ⟨a.numVerts, a.adjPtr, a.wtPtr,
          t.mem dJ, t.mem (dJ + 1), t.mem (dJ + 2), t.mem (dJ + 3),
          t.mem dP, t.mem (dP + 1), t.frontier⟩
      let t_cp := (Memory.spec 0).clientState t_alloc (childPassProg cpA)
      let ppA : ParentPassArgs :=
        ⟨t.mem dJ, t.mem (dJ + 1), t.mem dP, t.mem (dP + 1),
          t.mem (dP + 2), t.mem (dP + 3), t.frontier⟩
      Fits w (a.parPtr + (k + 1)) ∧
      (Fits w dJ ∧ Fits w 4) ∧ (Fits w (dJ + 1) ∧ Fits w 4) ∧
      (Fits w (dJ + 2) ∧ Fits w 4) ∧ (Fits w (dJ + 3) ∧ Fits w 4) ∧
      (Fits w dP ∧ Fits w 4) ∧ (Fits w (dP + 1) ∧ Fits w 4) ∧
      (Fits w (dP + 2) ∧ Fits w 4) ∧ (Fits w (dP + 3) ∧ Fits w 4) ∧
      ChildPassPre w cpA t_alloc ∧
      ParentPassPre w ppA t_cp ∧
      1 ≤ k + 1) := by
  subst ha
  let a : ProcessNodesArgs := ⟨inst.numVerts, 3 + inst.numVerts, 3,
    3 + inst.numVerts + inst.numVerts * inst.numVerts, descBase, inst.numNodes⟩
  let m := inst.numVerts
  let n := inst.numNodes
  let M := inst.maxBagLen
  let W := inst.maxWeight
  let B := M * W
  let jFin : Fin (inst.numNodes + 1) := ⟨k + 1, by omega⟩
  have hj_val : jFin.val = k + 1 := rfl
  let pFin := inst.parFin jFin
  have hp_idx : k + 1 < inst.parents.length := by rw [inst.parents_len]; omega
  have hp_lt : pFin.val < k + 1 := by
    dsimp only [pFin, MWISInstance.parFin, jFin]
    rw [dite_eq_left (by omega)]
    exact inst.parents_lt ⟨k + 1, hp_idx⟩ (by omega)
  have hp_read :
      t.mem (3 + inst.numVerts + inst.numVerts * inst.numVerts + (k + 1)) = pFin.val := by
    dsimp only [pFin, MWISInstance.parFin, jFin]
    rw [dite_eq_left (by omega), hlay.par_holds.get (k + 1) hp_idx]; rfl
  obtain ⟨hj_len_m, hj_pow_m, hj_blo, hj_bag⟩ := hlay.bags_holds jFin
  rw [hj_val] at hj_len_m hj_pow_m hj_blo
  obtain ⟨hj_tlen, hj_tlo, hj_tbl⟩ := hlay.tbl_holds jFin
  obtain ⟨hp_len_m, hp_pow_m, hp_blo, hp_bag⟩ := hlay.bags_holds pFin
  obtain ⟨hp_tlen, hp_tlo, hp_tbl⟩ := hlay.tbl_holds pFin
  have hj_len_le : (inst.bagAt jFin).length ≤ M := inst.bagAt_length_le jFin
  have hp_len_le : (inst.bagAt pFin).length ≤ M := inst.bagAt_length_le pFin
  have hj_pow_le : 2 ^ (inst.bagAt jFin).length ≤ 2 ^ M :=
    Nat.pow_le_pow_right (by decide) hj_len_le
  have hp_pow_le : 2 ^ (inst.bagAt pFin).length ≤ 2 ^ M :=
    Nat.pow_le_pow_right (by decide) hp_len_le
  let tblPLen := 2 ^ (inst.bagAt pFin).length
  let bestPtr := t.frontier
  let t_a := (Memory.spec 0).clientState t (Memory.alloc tblPLen)
  have hp_a : PreservesBelow t.frontier t t_a := preservesBelow_alloc t tblPLen
  have hlay_a : NodeLayout inst descBase tblList t_a := hlay.mono_frontier hp_a
  have hbest_init : HoldsIn bestPtr (List.replicate tblPLen 0) t_a := holdsIn_alloc_zero t tblPLen
  have hv_alloc : (Memory.spec w).ValidHistory t
      ((Memory.spec w).clientHistory t (Memory.alloc tblPLen)) :=
    validHistory_alloc (hfit_fr.of_le (by dsimp only [tblPLen, M] at hp_pow_le ⊢; omega))
  let capB := B + (tblList jFin).foldl max 0
  let capO := (tblList pFin).foldl max 0
  have hsum_caps_le : capO + capB ≤ (n + 1) * M * W := by
    have h1 := prefixMaxSum_succ tblList hk
    have h2 : capO ≤ prefixMaxSum tblList k := foldl_max_le_prefixMaxSum tblList pFin (by omega)
    calc capO + capB
        ≤ prefixMaxSum tblList (k + 1) + B := by
          dsimp only [capO, capB, jFin] at h1 h2 ⊢
          omega
      _ ≤ (n - (k + 1) + 1) * B := by rw [Nat.succ_mul]; exact Nat.add_le_add_right hpfx B
      _ ≤ (n + 1) * B := Nat.mul_le_mul_right B (by dsimp only [n]; omega)
      _ = (n + 1) * M * W := (Nat.mul_assoc (n + 1) M W).symm
  have hfit_capB : Fits w capB := hfit_val.of_le (by dsimp only [n, M, W] at hsum_caps_le; omega)
  have hfit_sum : Fits w (capO + capB) := hfit_val.of_le hsum_caps_le
  have hcand_le (mask : ℕ) (_ : mask < 2 ^ (inst.bagAt jFin).length) :
      forgetWeight inst.wt (inst.bagAt pFin) (inst.bagAt jFin) mask +
        (tblList jFin).getD mask 0 ≤ capB := by
    have hfw : forgetWeight inst.wt (inst.bagAt pFin) (inst.bagAt jFin) mask ≤ B :=
      (forgetWeight_le_foldl_max inst.weights (inst.bagAt pFin) (inst.bagAt jFin) mask
        (inst.weights_len ▸ inst.bagAt_mem_lt jFin)).trans (Nat.mul_le_mul_right W hj_len_le)
    have hfc : (tblList jFin).getD mask 0 ≤ (tblList jFin).foldl max 0 := by
      rw [List.getD_eq_getElem?_getD]
      cases hget : (tblList jFin)[mask]? with
      | none => exact Nat.zero_le _
      | some v => exact List.mem_le_foldl_max (List.mem_of_getElem? hget)
    dsimp only [capB]; omega
  let cpArgs : ChildPassArgs :=
    ⟨m, 3 + m, 3, t.mem (descBase + 4 * jFin.val), (inst.bagAt jFin).length,
      t.mem (descBase + 4 * jFin.val + 2), 2 ^ (inst.bagAt jFin).length,
      t.mem (descBase + 4 * pFin.val), (inst.bagAt pFin).length, bestPtr⟩
  obtain ⟨hv_cp, hfr_cp, hp_cp, hbest_cp, hc_cp⟩ :=
    childPassProg_spec (w := w) cpArgs (inst := inst)
      (LB := inst.bagAt jFin) (LP := inst.bagAt pFin) (tblB := tblList jFin)
    (initL := List.replicate tblPLen 0) (cap := capB) (s := t_a)
    hlay_a.adj_holds hlay.adj_holds.1 hlay_a.wt_holds hlay.wt_holds.1 rfl
    (hj_bag.mono_frontier hp_a) rfl (hj_blo.trans (le_trans (by omega) hlay.desc_hi))
    (inst.bagAt_mem_lt jFin) (hj_tbl.mono_frontier hp_a) hj_tlen
    (by simpa only [hj_tlen] using hj_tbl.1)
    (hp_bag.mono_frontier hp_a) rfl (hp_blo.trans (le_trans (by omega) hlay.desc_hi))
    hbest_init List.length_replicate
    (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact Nat.zero_le _) hcand_le hfit_capB
  let t_c := (Memory.spec 0).clientState t_a (childPassProg cpArgs)
  have hlay_c : NodeLayout inst descBase tblList t_c :=
    hlay.mono_frontier (hp_a.trans hp_cp)
  let bestL := childPassList inst.adj inst.wt (inst.bagAt jFin) (inst.bagAt pFin)
    (tblList jFin) (List.replicate tblPLen 0) (2 ^ (inst.bagAt jFin).length)
  have hbestL_le : ∀ x ∈ bestL, x ≤ capB :=
    mem_childPassList_le
      (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact Nat.zero_le _) hcand_le
  have hbestL_len : bestL.length = tblPLen := by
    rw [length_childPassList, List.length_replicate]
  have hp_mem_c (off : ℕ) (hoff : off < 4) :
      t_c.mem (descBase + 4 * pFin.val + off) = t.mem (descBase + 4 * pFin.val + off) :=
    (hp_a.trans hp_cp).2.2 _ (by have := hlay.desc_hi; have := pFin.isLt; omega)
  let ppArgs : ParentPassArgs :=
    ⟨t.mem (descBase + 4 * jFin.val), (inst.bagAt jFin).length,
      t.mem (descBase + 4 * pFin.val), (inst.bagAt pFin).length,
      t.mem (descBase + 4 * pFin.val + 2), tblPLen, bestPtr⟩
  obtain ⟨hv_pp, hfr_pp, hout_pp, hpfx_pp, hc_pp⟩ := parentPassProg_spec (w := w) ppArgs
    (LB := inst.bagAt jFin) (LP := inst.bagAt pFin) (oldL := tblList pFin) (bestL := bestL)
    (capO := capO) (capB := capB) (s := t_c)
    (hj_bag.mono_frontier (hp_a.trans hp_cp)) rfl
    (by dsimp only [ppArgs]; rw [hj_val] at *; exact hj_blo.trans (le_trans (by omega) hp_tlo))
    (hp_bag.mono_frontier (hp_a.trans hp_cp)) rfl
    (by dsimp only [ppArgs]; exact hp_blo.trans (le_trans (by omega) hp_tlo))
    (hp_tbl.mono_frontier (hp_a.trans hp_cp)) hp_tlen rfl
    (by simpa only [hp_tlen] using hp_tbl.1)
    hbest_cp hbestL_len (fun _ hx => List.mem_le_foldl_max hx) hbestL_le hfit_sum
  let t_p := (Memory.spec 0).clientState t_c (parentPassProg ppArgs)
  obtain ⟨hst_ev, hres_ev⟩ := processNodeStep_eval a (k + 1) t
  have hst_eq : (Memory.spec 0).clientState t (processNodeStep (a, k + 1)) = t_p := by
    rw [hst_ev]
    dsimp only [a, m, n, t_p, t_c, t_a, ppArgs, cpArgs, tblPLen, bestPtr, jFin]
    rw [hp_read, hj_len_m, hj_pow_m, hp_len_m, hp_pow_m]
  have hlay_p : NodeLayout inst descBase
      (Function.update tblList pFin
        (parentPassPrefix (inst.bagAt jFin) (inst.bagAt pFin) (tblList pFin) bestL tblPLen))
      t_p :=
    hlay_c.update_table pFin _ (by rw [length_parentPassPrefix, hp_tlen]) hfr_pp
      (by simpa only [hp_mem_c 2 (by decide)] using hout_pp)
      (by simpa only [hp_mem_c 2 (by decide)] using hpfx_pp)
  have hpfx_next : prefixMaxSum
      (Function.update tblList pFin
        (parentPassPrefix (inst.bagAt jFin) (inst.bagAt pFin) (tblList pFin) bestL tblPLen))
      k ≤ (n - k) * B := by
    have hnewP_max : (parentPassPrefix (inst.bagAt jFin) (inst.bagAt pFin) (tblList pFin)
        bestL tblPLen).foldl max 0 ≤
          (tblList pFin).foldl max 0 + B + (tblList jFin).foldl max 0 :=
      (List.foldl_max_le (Nat.zero_le _) (mem_parentPassPrefix_le
        (fun _ hx => List.mem_le_foldl_max (a := 0) hx) hbestL_le)).trans
        (by dsimp only [capB]; omega)
    calc prefixMaxSum _ k
        ≤ (n - (k + 1) + 1) * B := by
          rw [Nat.succ_mul]
          exact (prefixMaxSum_update_le tblList hk pFin hp_lt _ hnewP_max).trans
            (Nat.add_le_add_right hpfx B)
      _ = (n - k) * B := by rw [show n - (k + 1) + 1 = n - k by omega]
  have hpar_lt_fr : a.parPtr + (k + 1) < t.frontier := by
    have h := hlay.par_holds.1
    rw [inst.parents_len] at h
    dsimp only [a]; omega
  have hdJ_lt (off : ℕ) (hoff : off < 4) : descBase + 4 * (k + 1) + off < t.frontier := by
    have := hlay.desc_hi; omega
  have hdP_lt (off : ℕ) (hoff : off < 4) : descBase + 4 * pFin.val + off < t.frontier := by
    have := hlay.desc_hi
    have := pFin.isLt
    omega
  have hv_step : (Memory.spec w).ValidHistory t
      ((Memory.spec w).clientHistory t (processNodeStep (a, k + 1))) := by
    unfold processNodeStep
    dsimp only
    refine validHistory_read_bind hpar_lt_fr ?_
    rw [hp_read]
    refine validHistory_read_bind (by simpa only [Nat.add_zero] using hdJ_lt 0 (by decide)) <|
      validHistory_read_bind (hdJ_lt 1 (by decide)) <|
      validHistory_read_bind (hdJ_lt 2 (by decide)) <|
      validHistory_read_bind (hdJ_lt 3 (by decide)) <|
      validHistory_read_bind (by simpa only [Nat.add_zero] using hdP_lt 0 (by decide)) <|
      validHistory_read_bind (hdP_lt 1 (by decide)) <|
      validHistory_read_bind (hdP_lt 2 (by decide)) <|
      validHistory_read_bind (hdP_lt 3 (by decide)) ?_
    rw [hj_len_m, hj_pow_m, hp_len_m, hp_pow_m]
    exact validHistory_bind_step hv_alloc
      (validHistory_bind_step hv_cp (validHistory_bind_step hv_pp (validHistory_pure w _ _)))
  have hc_step : memoryCost (processNodeStep (a, k + 1)) t ≤
      10 + 2 ^ M * (5 * M ^ 2 + 5 * M + 7) := by
    have hr_s (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
    have hr_r (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
    unfold processNodeStep
    dsimp only
    iterate 9 rw [memoryCost_bind', memoryCost_read, hr_s, hr_r]
    rw [hp_read, hj_len_m, hj_pow_m, hp_len_m, hp_pow_m, memoryCost_bind', memoryCost_alloc,
      show (Memory.spec 0).clientState t (Memory.alloc tblPLen) = t_a from rfl,
      show (Memory.spec 0).clientResult t (Memory.alloc tblPLen) = bestPtr from rfl,
      memoryCost_bind', memoryCost_bind', memoryCost_pure, Nat.add_zero]
    have hc_cp_M : memoryCost (childPassProg cpArgs) t_a ≤ 2 ^ M * (4 * M ^ 2 + 4 * M + 3) :=
      hc_cp.trans (Nat.mul_le_mul hj_pow_le (cp_cost_poly_le hj_len_le hp_len_le))
    have hc_pp_M : memoryCost (parentPassProg ppArgs) t_c ≤
        2 ^ M * (M ^ 2 + M + 3) :=
      hc_pp.trans (Nat.mul_le_mul hp_pow_le (pp_cost_poly_le hj_len_le hp_len_le))
    have hsum_pow := step_pow_sum_le hp_pow_le M
    change 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + ((tblPLen + 1) +
      (memoryCost (childPassProg cpArgs) t_a +
        memoryCost (parentPassProg ppArgs) t_c)))))))))) ≤ _
    omega
  refine ⟨hv_step, by rw [hres_ev]; omega,
    by rw [hst_eq, hfr_pp, hfr_cp]; change t.frontier + tblPLen ≤ t.frontier + 2 ^ M; omega,
    by rwa [hst_eq], hpfx_next, hc_step, fun h4 => ?_⟩
  have h2 : Fits w 2 := h4.of_le (by decide)
  have hfit_tfr : Fits w t.frontier := hfit_fr.of_le (Nat.le_add_right _ _)
  dsimp only [a]
  rw [hp_read, hj_len_m, hj_pow_m, hp_len_m, hp_pow_m]
  have hdJ_f (off : ℕ) (h : off < 4) : Fits w (descBase + 4 * (k + 1) + off) ∧ Fits w 4 :=
    ⟨hfit_tfr.of_le (hdJ_lt off h).le, h4⟩
  have hdP_f (off : ℕ) (h : off < 4) : Fits w (descBase + 4 * pFin.val + off) ∧ Fits w 4 :=
    ⟨hfit_tfr.of_le (hdP_lt off h).le, h4⟩
  have hcp_safe : ChildPassPre w cpArgs t_a :=
    ⟨h2, inst.numVerts, inst.adjMatrix, inst.weights,
      inst.bagAt jFin, inst.bagAt pFin, tblList jFin, List.replicate tblPLen 0, capB,
      inst.adjMatrix_len, inst.weights_len, rfl,
      hlay_a.adj_holds, hlay.adj_holds.1, hlay_a.wt_holds, hlay.wt_holds.1,
      hj_bag.mono_frontier hp_a, rfl, hj_blo.trans (le_trans (by omega) hlay.desc_hi),
      inst.bagAt_mem_lt jFin, hj_tbl.mono_frontier hp_a, hj_tlen,
      by simpa only [hj_tlen] using hj_tbl.1,
      hp_bag.mono_frontier hp_a, rfl, hp_blo.trans (le_trans (by omega) hlay.desc_hi),
      hbest_init, List.length_replicate,
      by have : (inst.bagAt jFin).length * inst.maxWeight ≤ B := Nat.mul_le_mul_right _ hj_len_le
         dsimp only [cpArgs, capB, B, W, M, MWISInstance.maxWeight] at *; omega,
      hfit_tfr.of_le (by
        have h := hlay.adj_holds.1
        rw [inst.adjMatrix_len] at h
        dsimp only [cpArgs, m]; omega),
      hfit_tfr.of_le (by
        have h := hlay.wt_holds.1
        rw [inst.weights_len] at h
        dsimp only [cpArgs]; omega),
      hfit_tfr.of_le (by have := hj_bag.1; dsimp only [cpArgs, jFin]; omega),
      hfit_tfr.of_le (by
        have h := hj_tbl.1
        rw [hj_tlen] at h
        dsimp only [cpArgs, jFin]; omega),
      hfit_tfr.of_le (by have := hp_bag.1; dsimp only [cpArgs]; omega),
      hfit_fr.of_le (le_trans hp_pow_le (Nat.le_add_left _ _)),
      hfit_fr.of_le (Nat.add_le_add_left hp_pow_le _), hfit_capB⟩
  have hpp_safe : ParentPassPre w ppArgs t_c :=
    ⟨h2, inst.bagAt jFin, inst.bagAt pFin, tblList pFin, bestL, capO, capB,
      hj_bag.mono_frontier (hp_a.trans hp_cp), rfl,
      by rw [hj_val] at *; dsimp only [ppArgs]; exact hj_blo.trans (le_trans (by omega) hp_tlo),
      hp_bag.mono_frontier (hp_a.trans hp_cp), rfl,
      by dsimp only [ppArgs]; exact hp_blo.trans (le_trans (by omega) hp_tlo),
      hp_tbl.mono_frontier (hp_a.trans hp_cp), hp_tlen, rfl,
      by simpa only [hp_tlen] using hp_tbl.1,
      hbest_cp, hbestL_len, le_rfl, List.foldl_max_le (Nat.zero_le _) hbestL_le,
      hfit_tfr.of_le (by have := hj_bag.1; dsimp only [ppArgs, jFin]; omega),
      hfit_tfr.of_le (by have := hp_bag.1; dsimp only [ppArgs]; omega),
      hfit_tfr.of_le (by
        have h := hp_tbl.1
        rw [hp_tlen] at h
        dsimp only [ppArgs, tblPLen]; omega),
      hfit_fr.of_le (le_trans hp_pow_le (Nat.le_add_left _ _)),
      hfit_fr.of_le (Nat.add_le_add_left hp_pow_le _), hfit_sum⟩
  exact ⟨hfit_tfr.of_le (by dsimp only [a] at hpar_lt_fr; omega),
    by simpa only [Nat.add_zero] using hdJ_f 0 (by decide), hdJ_f 1 (by decide),
    hdJ_f 2 (by decide), hdJ_f 3 (by decide),
    by simpa only [Nat.add_zero] using hdP_f 0 (by decide), hdP_f 1 (by decide),
    hdP_f 2 (by decide), hdP_f 3 (by decide), hcp_safe, hpp_safe, by omega⟩

private theorem step_frontier_bound {w s_fr t_fr n j M : ℕ} (hj : j + 1 ≤ n)
    (hfr : t_fr ≤ s_fr + (n - (j + 1)) * 2 ^ M) (hpeak : Fits w (s_fr + n * 2 ^ M)) :
    t_fr + 2 ^ M ≤ s_fr + (n - j) * 2 ^ M ∧ Fits w (t_fr + 2 ^ M) := by
  have hsub : t_fr + 2 ^ M ≤ s_fr + (n - j) * 2 ^ M := by
    calc t_fr + 2 ^ M
        ≤ (s_fr + (n - (j + 1)) * 2 ^ M) + 2 ^ M := Nat.add_le_add_right hfr _
      _ = s_fr + (n - (j + 1) + 1) * 2 ^ M := by rw [Nat.add_assoc, ← Nat.succ_mul]
      _ = s_fr + (n - j) * 2 ^ M := by rw [show n - (j + 1) + 1 = n - j by omega]
  exact ⟨hsub, hpeak.of_le (hsub.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _))⟩

/-- Layout preservation, telescoping table-entry bound, agreement with `tablesInst`, and cost bound
for `processNodesProg`. -/
theorem processNodesProg_spec {w : ℕ} (inst : MWISInstance) (descBase : ℕ)
    {s₁ : Memory.State}
    (hlay₁ : NodeLayout inst descBase
      (fun i => List.replicate (2 ^ (inst.bagAt i).length) 0) s₁)
    (hfit_peak : Fits w (s₁.frontier + inst.numNodes * 2 ^ inst.maxBagLen))
    (hfit_val : Fits w ((inst.numNodes + 1) * inst.maxBagLen * inst.maxWeight)) :
    let m := inst.numVerts
    let n := inst.numNodes
    let M := inst.maxBagLen
    let args : ProcessNodesArgs := ⟨m, 3 + m, 3, 3 + m + m * m, descBase, n⟩
    let s₂ := (Memory.spec 0).clientState s₁ (processNodesProg args)
    (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (processNodesProg args)) ∧
    s₂.frontier ≤ s₁.frontier + n * 2 ^ M ∧
    (∃ tblFinal : Fin (n + 1) → List ℕ,
      NodeLayout inst descBase tblFinal s₂ ∧
      prefixMaxSum tblFinal 0 ≤ n * (M * inst.maxWeight) ∧
      (∀ i : Fin (n + 1), ∀ s < 2 ^ (inst.bagAt i).length,
        (tblFinal i).getD s 0 =
          (tablesInst inst.adj inst.wt n inst.parFin inst.bagAt n)[i].getD s 0)) ∧
    memoryCost (processNodesProg args) s₁ ≤
      n * (10 + 2 ^ M * (5 * M ^ 2 + 5 * M + 7)) := by
  let m := inst.numVerts
  let n := inst.numNodes
  let M := inst.maxBagLen
  let B := M * inst.maxWeight
  let args : ProcessNodesArgs := ⟨m, 3 + m, 3, 3 + m + m * m, descBase, n⟩
  let stepCost := 10 + 2 ^ M * (5 * M ^ 2 + 5 * M + 7)
  suffices ∀ k st (tblList : Fin (n + 1) → List ℕ),
      k ≤ n →
      st.frontier ≤ s₁.frontier + (n - k) * 2 ^ M →
      NodeLayout inst descBase tblList st →
      prefixMaxSum tblList k ≤ (n - k) * B →
      (∀ i : Fin (n + 1), ∀ s < 2 ^ (inst.bagAt i).length,
        (tblList i).getD s 0 =
          (tablesInst inst.adj inst.wt n inst.parFin inst.bagAt (n - k))[i].getD s 0) →
      (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (iterate processNodeStep args k k)) ∧
      (let sEnd := (Memory.spec 0).clientState st (iterate processNodeStep args k k)
       sEnd.frontier ≤ s₁.frontier + n * 2 ^ M ∧
       ∃ tblFinal : Fin (n + 1) → List ℕ,
         NodeLayout inst descBase tblFinal sEnd ∧
         prefixMaxSum tblFinal 0 ≤ n * B ∧
         (∀ i : Fin (n + 1), ∀ s < 2 ^ (inst.bagAt i).length,
           (tblFinal i).getD s 0 =
             (tablesInst inst.adj inst.wt n inst.parFin inst.bagAt n)[i].getD s 0)) ∧
      memoryCost (iterate processNodeStep args k k) st ≤ k * stepCost by
    obtain ⟨hv_l, ⟨hfr_l, hfin_l⟩, hc_l⟩ := this n s₁
      (fun i => List.replicate (2 ^ (inst.bagAt i).length) 0) le_rfl (by simp) hlay₁
      (by rw [prefixMaxSum_replicate_zero]; simp) fun i s hs => by
        simp [tablesInst_zero, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, hs]
    unfold processNodesProg
    exact ⟨validHistory_bind_step hv_l (validHistory_pure w _ ()),
      by rwa [StateTransitionSpec.clientState_bind],
      by rwa [StateTransitionSpec.clientState_bind],
      by rwa [memoryCost_bind', memoryCost_pure, Nat.add_zero]⟩
  intro k
  induction k with
  | zero =>
    intro st tblList _ hfr hlay hpfx hagree
    have h0 : iterate processNodeStep args 0 0 = pure 0 := rfl
    rw [h0]
    simp only [Nat.sub_zero] at hfr hpfx hagree
    exact ⟨validHistory_pure w st 0, ⟨hfr, tblList, hlay, hpfx, hagree⟩, by simp [memoryCost_pure]⟩
  | succ k ih =>
    intro st tblList hk hfr hlay hpfx hagree
    obtain ⟨hfr_sub, hfit_fr⟩ := step_frontier_bound hk hfr hfit_peak
    obtain ⟨hv_step, hres_step, hfr_step, hlay_next, hpfx_next, hc_step, _⟩ :=
      processNodeStep_full (w := w) inst descBase rfl hk hlay hpfx hfit_fr hfit_val
    let jFin : Fin (n + 1) := ⟨k + 1, by omega⟩
    let pFin := inst.parFin jFin
    let bestL := childPassList inst.adj inst.wt (inst.bagAt jFin) (inst.bagAt pFin)
      (tblList jFin) (List.replicate (2 ^ (inst.bagAt pFin).length) 0)
      (2 ^ (inst.bagAt jFin).length)
    let newTblP := parentPassPrefix (inst.bagAt jFin) (inst.bagAt pFin)
      (tblList pFin) bestL (2 ^ (inst.bagAt pFin).length)
    let tblList' := Function.update tblList pFin newTblP
    have hagree_next (i : Fin (n + 1)) (s : ℕ) (hs : s < 2 ^ (inst.bagAt i).length) :
        (tblList' i).getD s 0 =
          (tablesInst inst.adj inst.wt n inst.parFin inst.bagAt (n - k))[i].getD s 0 := by
      have hj_ofNat : Fin.ofNat (n + 1) (n - (n - (k + 1))) = jFin := Fin.ext <| by
        rw [Fin.val_ofNat, show n - (n - (k + 1)) = k + 1 by omega, Nat.mod_eq_of_lt (by omega)]
      rw [show n - k = (n - (k + 1)) + 1 by omega, tablesInst_succ]
      simp only [hj_ofNat]
      by_cases hip : i = pFin
      · subst hip
        dsimp only [tblList']
        have hs_lt_old : s < (tblList pFin).length := (hlay.tbl_holds pFin).1.symm ▸ hs
        have hold_eq : (tblList pFin)[s] =
            (tablesInst inst.adj inst.wt n inst.parFin inst.bagAt
              (n - (k + 1)))[pFin].getD s 0 := by
          rw [← hagree pFin s hs, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hs_lt_old, Option.getD_some]
        rw [Function.update_self, Fin.getElem_fin, Vector.getElem_set_self,
          getD_parentPass_raw _ _ _ _ hs,
          getD_parentPassPrefix _ _ _ _ hs_lt_old hs, hold_eq,
          getD_childPassList_eq inst.adj inst.wt (inst.bagAt jFin) (inst.bagAt pFin)
            (tblList jFin) _ (2 ^ (inst.bagAt jFin).length) (hagree jFin) _
            (restrictMask_lt_two_pow _ _ s)]
      · dsimp only [tblList']
        rw [Function.update_of_ne hip, Fin.getElem_fin,
          Vector.getElem_set_ne _ _ fun h => hip (Fin.ext h).symm]
        exact hagree i s hs
    obtain ⟨hv_rem, hprops_rem, hc_rem⟩ := ih _ tblList' (by omega)
      (hfr_step.trans hfr_sub) hlay_next hpfx_next hagree_next
    have hiter_eq : iterate processNodeStep args (k + 1) (k + 1) =
        (processNodeStep (args, k + 1) >>= iterate processNodeStep args k) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hres_step]),
      by rw [StateTransitionSpec.clientState_bind, hres_step]; exact hprops_rem, ?_⟩
    rw [memoryCost_bind', hres_step, Nat.succ_mul, Nat.add_comm (k * stepCost)]
    exact Nat.add_le_add hc_step hc_rem

/-- Exact-basis Word-RAM realization certificate for `processNodesProg`. -/
theorem processNodesProg_realizes :
    Realizes .exact processNodesProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 4 ∧
        ∃ (inst : MWISInstance) (tblList : Fin (inst.numNodes + 1) → List ℕ),
          args.numVerts = inst.numVerts ∧
          args.adjPtr = 3 + inst.numVerts ∧
          args.wtPtr = 3 ∧
          args.parPtr = 3 + inst.numVerts + inst.numVerts * inst.numVerts ∧
          args.numNodes = inst.numNodes ∧
          NodeLayout inst args.descBase tblList s ∧
          prefixMaxSum tblList inst.numNodes = 0 ∧
          Fits w (s.frontier + inst.numNodes * 2 ^ inst.maxBagLen) ∧
          Fits w ((inst.numNodes + 1) * inst.maxBagLen * inst.maxWeight))
      (fun _ _ => 0) := by
  unfold processNodesProg
  realize [childPassProg_realizes, parentPassProg_realizes]
  obtain ⟨h4, inst, tblInit, hnv, hadjP, hwtP, hparP, hnn, hlay₀, hpfx₀, hfit_peak, hfit_val⟩ := h
  have hd_eq : d = ⟨inst.numVerts, 3 + inst.numVerts, 3,
      3 + inst.numVerts + inst.numVerts * inst.numVerts, d.descBase, inst.numNodes⟩ := by
    cases d
    dsimp only at hnv hadjP hwtP hparP hnn
    subst hnv hadjP hwtP hparP hnn
    rfl
  refine iterationSafe_of_stepInv _ _ w d
    (fun (j : ℕ) (curNode : ℕ) (t : Memory.State) =>
      j ≤ inst.numNodes ∧ curNode = j ∧
      t.frontier ≤ s.frontier + (inst.numNodes - j) * 2 ^ inst.maxBagLen ∧
      ∃ tblList : Fin (inst.numNodes + 1) → List ℕ,
        NodeLayout inst d.descBase tblList t ∧
        prefixMaxSum tblList j ≤ (inst.numNodes - j) * (inst.maxBagLen * inst.maxWeight))
    (fun j curNode t ⟨hj_le, hcur_eq, hfr_t, tblList, hlay_t, hpfx_t⟩ => ?_)
    ⟨by rw [hnn], rfl, by rw [hnn]; simp, tblInit, hlay₀, by rw [hnn, hpfx₀]; simp⟩
  subst hcur_eq
  obtain ⟨hfr_sub, hfit_fr⟩ := step_frontier_bound hj_le hfr_t hfit_peak
  obtain ⟨_, hres_s, hfr_s, hlay_s, hpfx_s, _, hsafe_fn⟩ :=
    processNodeStep_full (w := w) inst d.descBase hd_eq hj_le hlay_t hpfx_t hfit_fr hfit_val
  exact ⟨by dsimp only [processNodeStep]; exact hsafe_fn h4,
    Nat.le_of_succ_le hj_le, hres_s, hfr_s.trans hfr_sub, _, hlay_s, hpfx_s⟩

end Cslib.Algorithms.WordRAM.TreeDecomposition
