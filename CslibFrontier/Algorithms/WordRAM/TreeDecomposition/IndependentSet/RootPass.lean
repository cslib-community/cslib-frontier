/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.InstDP
public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.Scan
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.IndepScan
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.WeightScan
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Tactic.Realize

/-!
# Root-bag maximization pass (`rootPassProg`)

This module certifies `rootPassProg`, which scans all `2 ^ |L₀|` subsets of the root bag `L₀`,
filters for pairwise independent subsets (`indepBagProg`), adds the root subset weight
(`forgetWeightProg` against an empty parent bag) to `tbl₀[curC]`, and returns the maximum value
(`rootPassInst`).

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.RootPassArgs`: register arguments for `rootPassProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.rootPassProg`: Word-RAM root-table maximization loop.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.rootPassProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.rootPassProg_realizes`: read-only state preservation,
  functional equality with `rootPassInst`, cost bound, and exact-basis realization certificate.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-- Register arguments for `rootPassProg`. -/
structure RootPassArgs where
  /-- Number of graph vertices `m`. -/
  numVerts : ℕ
  /-- Base memory address of the `m × m` adjacency matrix. -/
  adjPtr : ℕ
  /-- Base memory address of the `m`-word weight array. -/
  wtPtr : ℕ
  /-- Base memory address of root bag `L₀`. -/
  bag0Ptr : ℕ
  /-- Length of root bag `L₀`. -/
  bag0Len : ℕ
  /-- Base memory address of root DP table `tbl₀`. -/
  tbl0Ptr : ℕ
  /-- Length `2 ^ |L₀|` of root DP table `tbl₀`. -/
  tbl0Len : ℕ

/-- Tuple equivalence encoding `RootPassArgs` into Word-RAM registers. -/
@[expose] def RootPassArgs.equiv :
    RootPassArgs ≃ (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((((a.numVerts, a.adjPtr), a.wtPtr), a.bag0Ptr), a.bag0Len), a.tbl0Ptr), a.tbl0Len)
  invFun := fun ((((((nv, ap), wp), b0p), b0l), t0p), t0l) => ⟨nv, ap, wp, b0p, b0l, t0p, t0l⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding RootPassArgs := .ofEquiv RootPassArgs.equiv

private structure RootState where
  curC : ℕ
  best : ℕ

private def RootState.equiv : RootState ≃ ℕ × ℕ where
  toFun s := (s.curC, s.best)
  invFun := fun (c, b) => ⟨c, b⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding RootState := .ofEquiv RootState.equiv

private def rootPassStep (p : RootPassArgs × RootState) : Memory.Prog RootState := do
  let a := p.1
  let st := p.2
  let fc ← Memory.read (a.tbl0Ptr + st.curC)
  let ind ← indepBagProg ⟨a.numVerts, a.adjPtr, a.bag0Ptr, a.bag0Len, st.curC⟩
  let fw ← forgetWeightProg ⟨a.wtPtr, a.bag0Ptr, 0, a.bag0Ptr, a.bag0Len, st.curC⟩
  let cand := fw + fc
  let upd := if st.best < cand then cand else st.best
  let best' := if ind = 1 then upd else st.best
  pure ⟨st.curC + 1, best'⟩

/-- Maximize `forgetWeight wt [] L₀ c + tbl₀[c]` over independent root masks `c < tbl0Len`. -/
def rootPassProg (args : RootPassArgs) : Memory.Prog ℕ := do
  let res ← iterate rootPassStep args args.tbl0Len ⟨0, 0⟩
  pure res.best

private theorem rootPassStep_eval (a : RootPassArgs) (st : RootState) (t : Memory.State) :
    let fc := t.mem (a.tbl0Ptr + st.curC)
    let ind := (Memory.spec 0).clientResult t
      (indepBagProg ⟨a.numVerts, a.adjPtr, a.bag0Ptr, a.bag0Len, st.curC⟩)
    let fw := (Memory.spec 0).clientResult t
      (forgetWeightProg ⟨a.wtPtr, a.bag0Ptr, 0, a.bag0Ptr, a.bag0Len, st.curC⟩)
    let cand := fw + fc
    let best' := if ind = 1 then (if st.best < cand then cand else st.best) else st.best
    (Memory.spec 0).clientState t (rootPassStep (a, st)) = t ∧
    (Memory.spec 0).clientResult t (rootPassStep (a, st)) = ⟨st.curC + 1, best'⟩ := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold rootPassStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    indepBagProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    forgetWeightProg_state]
  exact ⟨rfl, rfl⟩

/-- `rootPassProg` is read-only and leaves memory unchanged. -/
theorem rootPassProg_state (args : RootPassArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (rootPassProg args) = s := by
  unfold rootPassProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of rootPassStep args
    (fun st m => (rootPassStep_eval args st m).1) args.tbl0Len ⟨0, 0⟩ s

/-- Correctness against `rootPassInst` and memory-cost bound for `rootPassProg`. -/
theorem rootPassProg_spec {w : ℕ} (args : RootPassArgs) {inst : MWISInstance}
    {L0 tbl0 : List ℕ} {arr0 : Array ℕ} {s : Memory.State}
    (hadj : HoldsIn args.adjPtr inst.adjMatrix s)
    (hwt : HoldsIn args.wtPtr inst.weights s)
    (hnv : args.numVerts = inst.numVerts)
    (hL0 : HoldsIn args.bag0Ptr L0 s) (hlen0 : L0.length = args.bag0Len)
    (hL0_lt : ∀ u ∈ L0, u < inst.numVerts)
    (htbl0 : HoldsIn args.tbl0Ptr tbl0 s) (htbl0_len : tbl0.length = args.tbl0Len)
    (harr0 : ∀ c < args.tbl0Len, tbl0.getD c 0 = arr0.getD c 0) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (rootPassProg args)) ∧
    (Memory.spec 0).clientState s (rootPassProg args) = s ∧
    (Memory.spec 0).clientResult s (rootPassProg args) =
      rootPassInst inst.adj inst.wt L0 arr0 args.tbl0Len ∧
    memoryCost (rootPassProg args) s ≤
      args.tbl0Len * (args.bag0Len * (2 * args.bag0Len + 1) + args.bag0Len * 2 + 1) := by
  let stepCost := args.bag0Len * (2 * args.bag0Len + 1) + args.bag0Len * 2 + 1
  have hnil : HoldsIn args.bag0Ptr [] s := HoldsIn.nil (by have := hL0.1; omega)
  have hL0_lt_wt : ∀ u ∈ L0, u < inst.weights.length := inst.weights_len.symm ▸ hL0_lt
  suffices ∀ rem curC,
      curC + rem = args.tbl0Len →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate rootPassStep args rem ⟨curC, rootPassInst inst.adj inst.wt L0 arr0 curC⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate rootPassStep args rem ⟨curC, rootPassInst inst.adj inst.wt L0 arr0 curC⟩)).best =
        rootPassInst inst.adj inst.wt L0 arr0 (curC + rem) ∧
      memoryCost
        (iterate rootPassStep args rem ⟨curC, rootPassInst inst.adj inst.wt L0 arr0 curC⟩) s ≤
        rem * stepCost by
    obtain ⟨hv_run, hr_run, hc_run⟩ := this args.tbl0Len 0 (Nat.zero_add _)
    rw [Nat.zero_add] at hr_run
    unfold rootPassProg
    exact ⟨validHistory_bind_step hv_run (validHistory_pure w _ _), rootPassProg_state args s,
      by rwa [StateTransitionSpec.clientResult_bind],
      by rwa [memoryCost_bind', memoryCost_pure, Nat.add_zero]⟩
  intro rem curC hsum
  induction rem generalizing curC with
  | zero => exact ⟨validHistory_pure w s _, rfl, by simp [iterate, memoryCost_pure]⟩
  | succ rem ih =>
    let bCur := rootPassInst inst.adj inst.wt L0 arr0 curC
    have hcur_lt : curC < args.tbl0Len := by omega
    have hcur_tbl : curC < tbl0.length := by omega
    obtain ⟨hv_ind, hst_ind, hr_ind, hc_ind⟩ :=
      indepBagProg_spec (w := w) ⟨args.numVerts, args.adjPtr, args.bag0Ptr, args.bag0Len, curC⟩
        hadj inst.adjMatrix_len hnv hL0 hlen0 hL0_lt
    obtain ⟨hv_fw, hst_fw, hr_fw, hc_fw⟩ :=
      forgetWeightProg_spec (w := w)
        ⟨args.wtPtr, args.bag0Ptr, 0, args.bag0Ptr, args.bag0Len, curC⟩
        hwt hnil rfl hL0 hlen0 hL0_lt_wt
    dsimp only at hr_ind hc_ind hr_fw hc_fw
    have hfc_addr : args.tbl0Ptr + curC < s.frontier := by have := htbl0.1; omega
    have hfc_eq : s.mem (args.tbl0Ptr + curC) = arr0.getD curC 0 := by
      rw [htbl0.get curC hcur_tbl, ← harr0 curC hcur_lt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hcur_tbl, Option.getD_some]
    obtain ⟨hst_step, hres_step⟩ := rootPassStep_eval args ⟨curC, bCur⟩ s
    have hb_next : (if (if indepInst inst.adj L0 curC then 1 else 0) = 1 then
          if bCur < forgetWeight inst.wt [] L0 curC + s.mem (args.tbl0Ptr + curC) then
            forgetWeight inst.wt [] L0 curC + s.mem (args.tbl0Ptr + curC)
          else bCur
        else bCur) = rootPassInst inst.adj inst.wt L0 arr0 (curC + 1) := by
      dsimp only [rootPassInst, bCur]
      rw [hfc_eq]
      cases indepInst inst.adj L0 curC <;> simp [Nat.max_def]
      split_ifs <;> omega
    unfold MWISInstance.adj MWISInstance.wt at hb_next
    dsimp only at hres_step
    rw [hr_ind, hr_fw, hb_next] at hres_step
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (rootPassStep (args, ⟨curC, bCur⟩))) := by
      unfold rootPassStep
      dsimp only
      refine validHistory_read_bind hfc_addr (validHistory_bind_step hv_ind ?_)
      rw [hst_ind, hr_ind]
      exact validHistory_bind_step hv_fw (validHistory_pure w _ _)
    have hc_step : memoryCost (rootPassStep (args, ⟨curC, bCur⟩)) s ≤ stepCost := by
      unfold rootPassStep
      dsimp only
      rw [memoryCost_bind', memoryCost_read]
      change 1 + memoryCost _ s ≤ stepCost
      rw [memoryCost_bind', hst_ind, hr_ind, memoryCost_bind', hst_fw, memoryCost_pure]
      omega
    obtain ⟨hv_rem, hr_rem, hc_rem⟩ := ih (curC + 1) (by omega)
    dsimp only [iterate]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step, ← Nat.add_assoc,
        Nat.add_right_comm]
      exact hr_rem
    · rw [memoryCost_bind', hst_step, hres_step]
      calc memoryCost (rootPassStep (args, ⟨curC, bCur⟩)) s +
            memoryCost
              (iterate rootPassStep args rem
                ⟨curC + 1, rootPassInst inst.adj inst.wt L0 arr0 (curC + 1)⟩) s
          ≤ stepCost + rem * stepCost := Nat.add_le_add hc_step hc_rem
        _ = (rem + 1) * stepCost := by rw [Nat.succ_mul, Nat.add_comm]

/-- Exact-basis Word-RAM realization certificate for `rootPassProg`. -/
theorem rootPassProg_realizes :
    Realizes .exact rootPassProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 2 ∧
        ∃ m adjL wtL L0 tbl0 cap,
          adjL.length = m * m ∧ wtL.length = m ∧ args.numVerts = m ∧
          HoldsIn args.adjPtr adjL s ∧ HoldsIn args.wtPtr wtL s ∧
          HoldsIn args.bag0Ptr L0 s ∧ L0.length = args.bag0Len ∧ (∀ u ∈ L0, u < m) ∧
          HoldsIn args.tbl0Ptr tbl0 s ∧ tbl0.length = args.tbl0Len ∧
          args.bag0Len * wtL.foldl max 0 + tbl0.foldl max 0 ≤ cap ∧
          Fits w (args.adjPtr + m * m) ∧ Fits w (args.wtPtr + m) ∧
          Fits w (args.bag0Ptr + args.bag0Len) ∧ Fits w (args.tbl0Ptr + args.tbl0Len) ∧
          Fits w cap)
      (fun _ _ => 0) := by
  unfold rootPassProg
  realize [indepBagProg_realizes, forgetWeightProg_realizes]
  obtain ⟨h2, m, adjL, wtL, L0, tbl0, cap,
    hadjL_len, hwtL_len, hnv, hadj_h, hwt_h,
    hL0_h, hL0_len, hL0_lt, htbl0_h, htbl0_len, hcap_bound,
    hfit_adj, hfit_wt, hfit_bag0, hfit_tbl0, hfit_cap⟩ := h
  have h1 : Fits w 1 := h2.of_le (by decide)
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : RootState) (t : Memory.State) =>
      j ≤ d.tbl0Len ∧ st.curC + j = d.tbl0Len ∧ st.best ≤ cap ∧
      HoldsIn d.adjPtr adjL t ∧ HoldsIn d.wtPtr wtL t ∧
      HoldsIn d.bag0Ptr L0 t ∧ HoldsIn d.tbl0Ptr tbl0 t)
    (fun j st t ⟨hj_le, hcur, hbest_le, hadj_t, hwt_t, hL0_t, htbl0_t⟩ => ?_)
    ⟨le_rfl, Nat.zero_add _, Nat.zero_le _, hadj_h, hwt_h, hL0_h, htbl0_h⟩
  have hL0_lt_wt : ∀ u ∈ L0, u < wtL.length := hwtL_len ▸ hL0_lt
  have hnil_t : HoldsIn d.bag0Ptr [] t := HoldsIn.nil (by have := hL0_t.1; omega)
  have hind_safe : Fits w 2 ∧ ∃ m' adjL' xs',
      adjL'.length = m' * m' ∧ d.numVerts = m' ∧
      HoldsIn d.adjPtr adjL' t ∧ HoldsIn d.bag0Ptr xs' t ∧ xs'.length = d.bag0Len ∧
      (∀ u ∈ xs', u < m') ∧ Fits w (d.adjPtr + m' * m') ∧ Fits w (d.bag0Ptr + d.bag0Len) :=
    ⟨h2, m, adjL, L0, hadjL_len, hnv, hadj_t, hL0_t, hL0_len, hL0_lt, hfit_adj, hfit_bag0⟩
  have hfw_safe : Fits w 2 ∧ ∃ wtL' LB',
      HoldsIn d.wtPtr wtL' t ∧ HoldsIn d.bag0Ptr LB' t ∧ LB'.length = d.bag0Len ∧
      (∀ u ∈ LB', u < wtL'.length) ∧ Fits w (d.wtPtr + wtL'.length) ∧
      Fits w (d.bag0Ptr + 0) ∧ Fits w (d.bag0Ptr + d.bag0Len) ∧
      Fits w (d.bag0Len * wtL'.foldl max 0) :=
    ⟨h2, wtL, L0, hwt_t, hL0_t, hL0_len, hL0_lt_wt, hwtL_len ▸ hfit_wt, hfit_bag0.of_le (by omega),
      hfit_bag0, hfit_cap.of_le (by omega)⟩
  have hfw_le := forgetWeightProg_result_le
    ⟨d.wtPtr, d.bag0Ptr, 0, d.bag0Ptr, d.bag0Len, st.curC⟩
    hwt_t hnil_t rfl hL0_t hL0_len hL0_lt_wt
  have hcur_tbl : st.curC < tbl0.length := by omega
  have hfc_le : t.mem (d.tbl0Ptr + st.curC) ≤ tbl0.foldl max 0 :=
    htbl0_t.get st.curC hcur_tbl ▸ List.mem_le_foldl_max (List.getElem_mem hcur_tbl)
  have hcand_le : (Memory.spec 0).clientResult t
      (forgetWeightProg ⟨d.wtPtr, d.bag0Ptr, 0, d.bag0Ptr, d.bag0Len, st.curC⟩) +
      t.mem (d.tbl0Ptr + st.curC) ≤ cap := by dsimp only at hfw_le; omega
  have hfit_tbl_addr : Fits w (d.tbl0Ptr + st.curC) := hfit_tbl0.of_le (by omega)
  have hfit_cand := hfit_cap.of_le hcand_le
  have hfit_cur1 : Fits w (st.curC + 1) := hfit_tbl0.of_le (by omega)
  obtain ⟨hst_ev, hres_ev⟩ := rootPassStep_eval d st t
  refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_,
    by rwa [hst_ev], by rwa [hst_ev], by rwa [hst_ev], by rwa [hst_ev]⟩
  · dsimp only [rootPassStep]
    rw [indepBagProg_state]
    repeat (first | split | exact hind_safe | exact hfw_safe | assumption | refine And.intro ?_ ?_)
  · simp only [hres_ev]; omega
  · simp only [hres_ev]
    split_ifs <;> omega

end Cslib.Algorithms.WordRAM.TreeDecomposition
