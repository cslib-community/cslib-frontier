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
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
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
  have hnil : HoldsIn args.bag0Ptr [] s := HoldsIn.nil (by have := hL0.1; omega)
  have hL0_lt_wt : ∀ u ∈ L0, u < inst.weights.length := inst.weights_len.symm ▸ hL0_lt
  have htf := htbl0.1
  obtain ⟨-, hloop⟩ := Memory.FramedTriple.iterate (s := s) (body := rootPassStep)
    (c := args.bag0Len * (2 * args.bag0Len + 1) + args.bag0Len * 2 + 1) (S := ∅)
    (safe := fun _ _ _ => True) (d := args) (n := args.tbl0Len) (a₀ := ⟨0, 0⟩)
    (Q := fun st _ => st.best = rootPassInst inst.adj inst.wt L0 arr0 args.tbl0Len)
    (fun k st t => t = s ∧ st = ⟨k, rootPassInst inst.adj inst.wt L0 arr0 k⟩) ⟨rfl, rfl⟩
    (fun k hk st t ⟨ht, hst⟩ _ => ⟨trivial, by
      subst t hst
      obtain ⟨hv_ind, hst_ind, hr_ind, hc_ind⟩ :=
        indepBagProg_spec (w := w) ⟨args.numVerts, args.adjPtr, args.bag0Ptr, args.bag0Len, k⟩
          hadj inst.adjMatrix_len hnv hL0 hlen0 hL0_lt
      have hind := Memory.FramedTriple.of_readOnly hv_ind hst_ind hr_ind hc_ind
      obtain ⟨hv_fw, hst_fw, hr_fw, hc_fw⟩ := forgetWeightProg_spec (w := w)
        ⟨args.wtPtr, args.bag0Ptr, 0, args.bag0Ptr, args.bag0Len, k⟩ hwt hnil rfl hL0 hlen0
        hL0_lt_wt
      have hfw := Memory.FramedTriple.of_readOnly hv_fw hst_fw hr_fw hc_fw
      unfold rootPassStep
      framed_triple
      have hfc_eq : s.mem (args.tbl0Ptr + k) = arr0.getD k 0 := by
        rw [htbl0.get k (by omega), ← harr0 k hk, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega), Option.getD_some]
      refine ⟨rfl, congrArg _ ?_⟩
      dsimp only [rootPassInst]
      unfold MWISInstance.adj MWISInstance.wt
      rw [hfc_eq]
      cases indepInst _ L0 k <;> simp [Nat.max_def]
      split_ifs <;> omega⟩)
    fun st t ⟨_, h⟩ _ => by rw [h]
  have hft : Memory.FramedTriple w s (rootPassProg args)
      (args.tbl0Len * (args.bag0Len * (2 * args.bag0Len + 1) + args.bag0Len * 2 + 1)) ∅
      fun r _ => r = rootPassInst inst.adj inst.wt L0 arr0 args.tbl0Len :=
    Memory.FramedTriple.mono (Memory.FramedTriple.call (c₂ := 0) hloop subset_rfl
      fun st _ h _ => Memory.FramedTriple.pure h) (by rw [Nat.mul_comm]; omega) fun _ _ => id
  obtain ⟨hv, hc, -, hres⟩ := framedTriple_iff_realization.mp hft
  exact ⟨hv, rootPassProg_state args s, hres, hc⟩

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
    refine ⟨hfit_tbl_addr,
      ⟨h2, m, adjL, L0, hadjL_len, hnv, hadj_t, hL0_t, hL0_len, hL0_lt, hfit_adj, hfit_bag0⟩,
      ⟨h2, wtL, L0, hwt_t, hL0_t, hL0_len, hL0_lt_wt, hwtL_len ▸ hfit_wt,
        hfit_bag0.of_le (by omega), hfit_bag0, hfit_cap.of_le (by omega)⟩, ?_⟩
    repeat (first | split | assumption | refine And.intro ?_ ?_)
  · simp only [hres_ev]; omega
  · simp only [hres_ev]
    split_ifs <;> omega

end Cslib.Algorithms.WordRAM.TreeDecomposition
