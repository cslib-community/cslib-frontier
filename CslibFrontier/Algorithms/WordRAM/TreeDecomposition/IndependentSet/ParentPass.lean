/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSetFPT
public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.Scan
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.MaskOps
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Tactic.Realize
import Mathlib.Data.List.OfFn

/-!
# In-place parent-table accumulation pass (`parentPassProg`)

This module certifies `parentPassProg`, which iterates over all `2 ^ |LP|` parent masks `curS`,
computes `restrictMask LB LP curS` via `restrictMaskProg`, and adds `best[rKey]` in-place into
`tblP[curS]`, with no dependency on `MWISInstance`, `IndepScan`, `WeightScan`, or `ChildPass`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.parentPassPrefix`: prefix-updated list representation
  of `parentPass`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.ParentPassArgs`: register arguments for
  `parentPassProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.parentPassProg`: Word-RAM in-place parent-table
  accumulation loop.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.getD_parentPass_raw`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.mem_parentPassPrefix_le`: agreement with `parentPass`
  and `capO + capB` entry bound.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.parentPassProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.parentPassProg_realizes`: in-place framing outside
  `[tblPPtr, tblPPtr + tblPLen)`, correctness, cost bound, and exact-basis realization certificate.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Prefix-updated list representation of `parentPass` -/

/-- List state of `tblP` after updating the first `k` parent masks in-place. -/
def parentPassPrefix (LB LP oldL bestL : List ℕ) (k : ℕ) : List ℕ :=
  List.ofFn fun i : Fin oldL.length =>
    if i.val < k then oldL[i] + bestL.getD (restrictMask LB LP i.val) 0 else oldL[i]

/-- `parentPassPrefix` preserves the length of `oldL`. -/
theorem length_parentPassPrefix (LB LP oldL bestL : List ℕ) (k : ℕ) :
    (parentPassPrefix LB LP oldL bestL k).length = oldL.length :=
  List.length_ofFn

/-- Pointwise lookup on `parentPassPrefix` at index `s < oldL.length` with `s < k`. -/
theorem getD_parentPassPrefix (LB LP oldL bestL : List ℕ) {k s : ℕ}
    (hs_len : s < oldL.length) (hs_k : s < k) :
    (parentPassPrefix LB LP oldL bestL k).getD s 0 =
      oldL[s] + bestL.getD (restrictMask LB LP s) 0 := by
  simp [parentPassPrefix, List.getD_eq_getElem?_getD, hs_len, hs_k]

private theorem parentPassPrefix_zero (LB LP oldL bestL : List ℕ) :
    parentPassPrefix LB LP oldL bestL 0 = oldL :=
  List.ext_getElem List.length_ofFn fun _ _ _ => by simp [parentPassPrefix]

private theorem parentPassPrefix_step (LB LP oldL bestL : List ℕ) {k : ℕ}
    (hk : k < oldL.length) :
    (parentPassPrefix LB LP oldL bestL k).set k
        (oldL[k] + bestL.getD (restrictMask LB LP k) 0) =
      parentPassPrefix LB LP oldL bestL (k + 1) := by
  refine List.ext_getElem (by simp [parentPassPrefix]) fun i hi1 hi2 => ?_
  rcases eq_or_ne k i with rfl | hik
  · simp [parentPassPrefix]
  · have hlt : (i < k) ↔ (i < k + 1) := by omega
    simp [parentPassPrefix, hik, hlt]

/-- Pointwise formula for `(parentPass LB LP old best c).getD s 0` without requiring `LP.Nodup`. -/
theorem getD_parentPass_raw (LB LP : List ℕ) (old best : Array ℕ) {c s : ℕ}
    (hs : s < c) :
    (parentPass LB LP old best c).getD s 0 =
      old.getD s 0 + best.getD (restrictMask LB LP s) 0 := by
  induction c with
  | zero => omega
  | succ c ih =>
    simp only [parentPass]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, size_parentPass]
    by_cases hsc : s = c
    · simp [hsc]
    · simp only [hsc, ↓reduceIte, ← Array.getD_eq_getD_getElem?, ih (by omega)]

/-- Every entry of `parentPassPrefix` is bounded by `capO + capB`. -/
theorem mem_parentPassPrefix_le {LB LP oldL bestL : List ℕ} {capO capB k : ℕ}
    (hold : ∀ x ∈ oldL, x ≤ capO) (hbest : ∀ x ∈ bestL, x ≤ capB) :
    ∀ x ∈ parentPassPrefix LB LP oldL bestL k, x ≤ capO + capB := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  have ho : oldL[i] ≤ capO := hold _ (List.getElem_mem i.isLt)
  split_ifs
  · rw [List.getD_eq_getElem?_getD]
    cases hget : bestL[restrictMask LB LP i.val]? with
    | none => exact Nat.add_le_add ho (Nat.zero_le _)
    | some v => exact Nat.add_le_add ho (hbest v (List.mem_of_getElem? hget))
  · exact ho.trans (Nat.le_add_right _ _)

/-! ### Word-RAM parent pass (`parentPassProg`) -/

/-- Register arguments for `parentPassProg`. -/
structure ParentPassArgs where
  /-- Base memory address of child bag `LB`. -/
  bagBPtr : ℕ
  /-- Length of child bag `LB`. -/
  bagBLen : ℕ
  /-- Base memory address of parent bag `LP`. -/
  bagPPtr : ℕ
  /-- Length of parent bag `LP`. -/
  bagPLen : ℕ
  /-- Base memory address of parent DP table `tblP`. -/
  tblPPtr : ℕ
  /-- Length `2 ^ |LP|` of parent DP table `tblP`. -/
  tblPLen : ℕ
  /-- Base memory address of the scratch `best` array of length `2 ^ |LP|`. -/
  bestPtr : ℕ

/-- Tuple equivalence encoding `ParentPassArgs` into Word-RAM registers. -/
@[expose] def ParentPassArgs.equiv :
    ParentPassArgs ≃ (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a :=
    ((((((a.bagBPtr, a.bagBLen), a.bagPPtr), a.bagPLen), a.tblPPtr), a.tblPLen), a.bestPtr)
  invFun := fun ((((((bbp, bbl), bpp), bpl), tpp), tpl), bp) => ⟨bbp, bbl, bpp, bpl, tpp, tpl, bp⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding ParentPassArgs := .ofEquiv ParentPassArgs.equiv

private def parentPassStep (p : ParentPassArgs × ℕ) : Memory.Prog ℕ := do
  let a := p.1
  let curS := p.2
  let oldVal ← Memory.read (a.tblPPtr + curS)
  let rKey ← restrictMaskProg ⟨a.bagBPtr, a.bagBLen, a.bagPPtr, a.bagPLen, curS⟩
  let bestVal ← Memory.read (a.bestPtr + rKey)
  Memory.write (a.tblPPtr + curS) (oldVal + bestVal)
  pure (curS + 1)

/-- Accumulate `best[restrictMask LB LP s]` into `tblP[s]` in-place across `0 .. tblPLen - 1`. -/
def parentPassProg (args : ParentPassArgs) : Memory.Prog Unit := do
  let _ ← iterate parentPassStep args args.tblPLen 0
  pure ()

private theorem parentPassStep_eval (a : ParentPassArgs) (curS : ℕ) (t : Memory.State) :
    let oldVal := t.mem (a.tblPPtr + curS)
    let rKey := (Memory.spec 0).clientResult t
      (restrictMaskProg ⟨a.bagBPtr, a.bagBLen, a.bagPPtr, a.bagPLen, curS⟩)
    let bestVal := t.mem (a.bestPtr + rKey)
    (Memory.spec 0).clientState t (parentPassStep (a, curS)) =
      ⟨Function.update t.mem (a.tblPPtr + curS) (oldVal + bestVal), t.frontier⟩ ∧
    (Memory.spec 0).clientResult t (parentPassStep (a, curS)) = curS + 1 := by
  unfold parentPassStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    restrictMaskProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
  exact ⟨rfl, rfl⟩

/-- Correctness, outside-table framing, and memory-cost bound for `parentPassProg`. -/
theorem parentPassProg_spec {w : ℕ} (args : ParentPassArgs)
    {LB LP oldL bestL : List ℕ} {capO capB : ℕ} {s : Memory.State}
    (hLB : HoldsIn args.bagBPtr LB s) (hlenB : LB.length = args.bagBLen)
    (hLB_disj : args.bagBPtr + args.bagBLen ≤ args.tblPPtr)
    (hLP : HoldsIn args.bagPPtr LP s) (hlenP : LP.length = args.bagPLen)
    (hLP_disj : args.bagPPtr + args.bagPLen ≤ args.tblPPtr)
    (hold : HoldsIn args.tblPPtr oldL s) (hold_len : oldL.length = args.tblPLen)
    (htblP_pow : args.tblPLen = 2 ^ LP.length)
    (hbest_disj : args.tblPPtr + args.tblPLen ≤ args.bestPtr)
    (hbest : HoldsIn args.bestPtr bestL s) (hbest_len : bestL.length = 2 ^ LP.length)
    (hold_le : ∀ x ∈ oldL, x ≤ capO) (hbest_le : ∀ x ∈ bestL, x ≤ capB)
    (hfit_sum : Fits w (capO + capB)) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (parentPassProg args)) ∧
    ((Memory.spec 0).clientState s (parentPassProg args)).frontier = s.frontier ∧
    (∀ addr, (addr < args.tblPPtr ∨ args.tblPPtr + args.tblPLen ≤ addr) →
      ((Memory.spec 0).clientState s (parentPassProg args)).mem addr = s.mem addr) ∧
    HoldsIn args.tblPPtr (parentPassPrefix LB LP oldL bestL args.tblPLen)
      ((Memory.spec 0).clientState s (parentPassProg args)) ∧
    memoryCost (parentPassProg args) s ≤
      args.tblPLen * (args.bagPLen * (args.bagBLen + 1) + 3) := by
  let stepCost := args.bagPLen * (args.bagBLen + 1) + 3
  suffices ∀ rem curS st,
      curS + rem = args.tblPLen →
      st.frontier = s.frontier →
      (∀ addr, (addr < args.tblPPtr ∨ args.tblPPtr + args.tblPLen ≤ addr) →
        st.mem addr = s.mem addr) →
      HoldsIn args.tblPPtr (parentPassPrefix LB LP oldL bestL curS) st →
      (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (iterate parentPassStep args rem curS)) ∧
      ((Memory.spec 0).clientState st (iterate parentPassStep args rem curS)).frontier =
        s.frontier ∧
      (∀ addr, (addr < args.tblPPtr ∨ args.tblPPtr + args.tblPLen ≤ addr) →
        ((Memory.spec 0).clientState st (iterate parentPassStep args rem curS)).mem addr =
          s.mem addr) ∧
      HoldsIn args.tblPPtr (parentPassPrefix LB LP oldL bestL (curS + rem))
        ((Memory.spec 0).clientState st (iterate parentPassStep args rem curS)) ∧
      memoryCost (iterate parentPassStep args rem curS) st ≤ rem * stepCost by
    obtain ⟨hv_run, hfr_run, hout_run, hpfx_run, hc_run⟩ :=
      this args.tblPLen 0 s (Nat.zero_add _) rfl (fun _ _ => rfl)
        (by rwa [parentPassPrefix_zero])
    rw [Nat.zero_add] at hpfx_run
    unfold parentPassProg
    refine ⟨validHistory_bind_step hv_run (validHistory_pure w _ ()), ?_, ?_, ?_,
      by simpa only [memoryCost_bind', memoryCost_pure, Nat.add_zero] using hc_run⟩
    all_goals rwa [StateTransitionSpec.clientState_bind]
  intro rem
  induction rem with
  | zero =>
    intro curS st _ hfr hout hcur_st
    dsimp only [iterate, Nat.add_zero]
    exact ⟨validHistory_pure w st curS, hfr, hout, hcur_st, by simp [memoryCost_pure]⟩
  | succ rem ih =>
    intro curS st hsum hfr hout hcur_st
    have hcur_lt : curS < oldL.length := by omega
    have hLB_st : HoldsIn args.bagBPtr LB st :=
      ⟨hfr ▸ hLB.1, hLB.2.frame fun a _ ha => hout a (.inl (by omega))⟩
    have hLP_st : HoldsIn args.bagPPtr LP st :=
      ⟨hfr ▸ hLP.1, hLP.2.frame fun a _ ha => hout a (.inl (by omega))⟩
    have hbest_st : HoldsIn args.bestPtr bestL st :=
      ⟨hfr ▸ hbest.1, hbest.2.frame fun a ha _ => hout a (.inr (by omega))⟩
    obtain ⟨hv_rk, hst_rk, hr_rk, hc_rk⟩ :=
      restrictMaskProg_spec (w := w)
        ⟨args.bagBPtr, args.bagBLen, args.bagPPtr, args.bagPLen, curS⟩
        hLB_st hlenB hLP_st hlenP
    dsimp only at hr_rk hc_rk
    let rKey := restrictMask LB LP curS
    have hrk_lt : rKey < bestL.length := hbest_len ▸ restrictMask_lt_two_pow LB LP curS
    have hcur_pfx_lt : curS < (parentPassPrefix LB LP oldL bestL curS).length :=
      (length_parentPassPrefix LB LP oldL bestL curS).symm ▸ hcur_lt
    have hold_addr_lt : args.tblPPtr + curS < st.frontier := by have := hcur_st.1; omega
    have hbest_addr_lt : args.bestPtr + rKey < st.frontier := by have := hbest_st.1; omega
    have holdVal_eq : st.mem (args.tblPPtr + curS) = oldL[curS] := by
      simpa [parentPassPrefix] using hcur_st.get curS hcur_pfx_lt
    have hbestVal_eq : st.mem (args.bestPtr + rKey) = bestL.getD rKey 0 := by
      simp [hbest_st.get rKey hrk_lt, List.getD_eq_getElem?_getD, hrk_lt]
    have hnew_fit : Fits w (st.mem (args.tblPPtr + curS) + st.mem (args.bestPtr + rKey)) := by
      rw [holdVal_eq, hbest_st.get rKey hrk_lt]
      exact hfit_sum.of_le (Nat.add_le_add (hold_le _ (List.getElem_mem hcur_lt))
        (hbest_le _ (List.getElem_mem hrk_lt)))
    let newVal := st.mem (args.tblPPtr + curS) + st.mem (args.bestPtr + rKey)
    let st₁ : Memory.State := ⟨Function.update st.mem (args.tblPPtr + curS) newVal, st.frontier⟩
    obtain ⟨hst_step, hres_step⟩ := parentPassStep_eval args curS st
    rw [hr_rk] at hst_step
    have hv_step : (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (parentPassStep (args, curS))) := by
      unfold parentPassStep
      dsimp only
      refine validHistory_read_bind hold_addr_lt (validHistory_bind_step hv_rk ?_)
      rw [hst_rk, hr_rk]
      exact validHistory_read_bind hbest_addr_lt
        (validHistory_write_bind hold_addr_lt hnew_fit (validHistory_pure w st₁ _))
    have hout₁ : ∀ addr, (addr < args.tblPPtr ∨ args.tblPPtr + args.tblPLen ≤ addr) →
        st₁.mem addr = s.mem addr := fun addr haddr =>
      (Function.update_of_ne (by omega) _ _).trans (hout addr haddr)
    have hpfx_next : HoldsIn args.tblPPtr (parentPassPrefix LB LP oldL bestL (curS + 1)) st₁ := by
      rw [← parentPassPrefix_step LB LP oldL bestL hcur_lt]
      dsimp only [st₁, newVal, rKey]
      rw [holdVal_eq, hbestVal_eq]
      exact holdsIn_set hcur_st
    have hc_step : memoryCost (parentPassStep (args, curS)) st ≤ stepCost := by
      have hr_s (x : ℕ) : (Memory.spec 0).clientState st (Memory.read x) = st := rfl
      have hr_r (x : ℕ) : (Memory.spec 0).clientResult st (Memory.read x) = st.mem x := rfl
      simp only [parentPassStep, memoryCost_bind', memoryCost_read, hr_s, hr_r, hst_rk, hr_rk,
        memoryCost_write, memoryCost_pure, stepCost]
      omega
    obtain ⟨hv_rem, hfr_rem, hout_rem, hpfx_rem, hc_rem⟩ :=
      ih (curS + 1) st₁ (by omega) hfr hout₁ hpfx_next
    dsimp only [iterate]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]),
      by rwa [StateTransitionSpec.clientState_bind, hst_step, hres_step],
      by rwa [StateTransitionSpec.clientState_bind, hst_step, hres_step],
      by rwa [StateTransitionSpec.clientState_bind, hst_step, hres_step, ← Nat.add_assoc,
        Nat.add_right_comm curS rem 1], ?_⟩
    rw [memoryCost_bind', hst_step, hres_step]
    calc memoryCost (parentPassStep (args, curS)) st +
          memoryCost (iterate parentPassStep args rem (curS + 1)) st₁
        ≤ stepCost + rem * stepCost := Nat.add_le_add hc_step hc_rem
      _ = (rem + 1) * stepCost := by ring

/-- Exact-basis Word-RAM realization certificate for `parentPassProg`. -/
theorem parentPassProg_realizes :
    Realizes .exact parentPassProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
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
          Fits w (args.bestPtr + 2 ^ args.bagPLen) ∧ Fits w (capO + capB))
      (fun _ _ => 0) := by
  unfold parentPassProg
  realize [restrictMaskProg_realizes]
  obtain ⟨h2, LB, LP, oldL, bestL, capO, capB,
    hLB_h, hLB_len, hLB_disj, hLP_h, hLP_len, hLP_disj,
    hold_h, hold_len, htblP_pow, hbest_disj, hbest_h, hbest_len,
    hold_cap, hbest_cap,
    hfit_bagB, hfit_bagP, hfit_tblP, hfit_powP, hfit_best, hfit_sum⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (curS : ℕ) (t : Memory.State) =>
      j ≤ d.tblPLen ∧ curS + j = d.tblPLen ∧
      t.frontier = s.frontier ∧
      (∀ addr, (addr < d.tblPPtr ∨ d.tblPPtr + d.tblPLen ≤ addr) → t.mem addr = s.mem addr) ∧
      HoldsIn d.tblPPtr (parentPassPrefix LB LP oldL bestL curS) t)
    (fun j curS t ⟨hj_le, hcur, hfr, hout, hpfx_t⟩ => ?_)
    ⟨le_rfl, Nat.zero_add _, rfl, fun _ _ => rfl, (parentPassPrefix_zero _ _ _ _).symm ▸ hold_h⟩
  have hLB_t : HoldsIn d.bagBPtr LB t :=
    ⟨hfr.symm ▸ hLB_h.1, hLB_h.2.frame fun a _ ha => hout a (.inl (by omega))⟩
  have hLP_t : HoldsIn d.bagPPtr LP t :=
    ⟨hfr.symm ▸ hLP_h.1, hLP_h.2.frame fun a _ ha => hout a (.inl (by omega))⟩
  have hbest_t : HoldsIn d.bestPtr bestL t :=
    ⟨hfr.symm ▸ hbest_h.1, hbest_h.2.frame fun a ha _ => hout a (.inr (by omega))⟩
  obtain ⟨_, _, hr_rk, _⟩ :=
    restrictMaskProg_spec (w := w) ⟨d.bagBPtr, d.bagBLen, d.bagPPtr, d.bagPLen, curS⟩
      hLB_t hLB_len hLP_t hLP_len
  dsimp only at hr_rk
  let rk := (Memory.spec 0).clientResult t
    (restrictMaskProg ⟨d.bagBPtr, d.bagBLen, d.bagPPtr, d.bagPLen, curS⟩)
  have hrk_lt : rk < bestL.length := by
    simpa only [rk, hr_rk, hbest_len, ← hLP_len] using restrictMask_lt_two_pow LB LP curS
  have hcur_lt : curS < oldL.length := by omega
  have hold_val : t.mem (d.tblPPtr + curS) = oldL[curS] := by
    simpa [parentPassPrefix] using
      hpfx_t.get curS ((length_parentPassPrefix LB LP oldL bestL curS).symm ▸ hcur_lt)
  have hold_le : t.mem (d.tblPPtr + curS) ≤ capO :=
    hold_val ▸ (List.mem_le_foldl_max (List.getElem_mem hcur_lt)).trans hold_cap
  have hbest_le : t.mem (d.bestPtr + rk) ≤ capB :=
    hbest_t.get _ hrk_lt ▸ (List.mem_le_foldl_max (List.getElem_mem hrk_lt)).trans hbest_cap
  have hfit_old_addr : Fits w (d.tblPPtr + curS) := hfit_tblP.of_le (by omega)
  have hfit_best_addr : Fits w (d.bestPtr + rk) := hfit_best.of_le (by omega)
  have hfit_new : Fits w (t.mem (d.tblPPtr + curS) + t.mem (d.bestPtr + rk)) :=
    hfit_sum.of_le (Nat.add_le_add hold_le hbest_le)
  have hfit_cur1 : Fits w (curS + 1) := hfit_tblP.of_le (by omega)
  obtain ⟨hst_ev, hres_ev⟩ := parentPassStep_eval d curS t
  refine ⟨?_, Nat.le_of_succ_le hj_le, by rw [hres_ev]; omega, hst_ev ▸ hfr, ?_, ?_⟩
  · dsimp only [parentPassStep]
    rw [restrictMaskProg_state]
    repeat (first | assumption | refine And.intro ?_ ?_)
  · exact hst_ev ▸ fun addr haddr => (Function.update_of_ne (by omega) _ _).trans (hout addr haddr)
  · have hrk_lt' : restrictMask LB LP curS < bestL.length := hr_rk ▸ hrk_lt
    rw [hst_ev, hres_ev, ← parentPassPrefix_step LB LP oldL bestL hcur_lt,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrk_lt', Option.getD_some,
      ← hold_val, ← hbest_t.get _ hrk_lt', ← hr_rk]
    exact holdsIn_set hpfx_t

end Cslib.Algorithms.WordRAM.TreeDecomposition
