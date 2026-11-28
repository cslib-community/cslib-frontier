/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.NodeDesc
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.BagOps
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.Radix
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
import CslibFrontier.Tactic.Realize

/-!
# Word-RAM `forget` node handler

This module certifies `forgetNodeProg` (along with the private loops `forgetInnerProg` and
`forgetFillProg`). It uses `eraseBagProg`, `radixProjProg`, `powProg`, `bagMemProg`, and the shared
descriptor/table-fill infrastructure (`NodeDesc`), and has no dependency on `ConstraintScan`,
`LeafIntro`, or `Join`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.ForgetNodeArgs`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.forgetNodeProg`: `forget` node handler.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.forgetNodeProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.forgetNodeProg_realizes`: correctness and realization
  of `forgetNodeProg`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open SimpleGraph
open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! #### 3. Forget node handler (`forgetInnerProg`, `forgetFillProg`, `forgetNodeProg`) -/

private structure ForgetInnerArgs where
  mode : ℕ
  q : ℕ
  v : ℕ
  bagPtr : ℕ
  bagLen : ℕ
  m : ℕ
  cBagPtr : ℕ
  cBagLen : ℕ
  cTblPtr : ℕ
  dLim : ℕ

private def ForgetInnerArgs.equiv :
    ForgetInnerArgs ≃ ((((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a :=
    (((((((((a.mode, a.q), a.v), a.bagPtr), a.bagLen), a.m), a.cBagPtr), a.cBagLen),
      a.cTblPtr), a.dLim)
  invFun := fun (((((((((md, q), v), bp), bl), m), cbp), cbl), ctp), dl) =>
    ⟨md, q, v, bp, bl, m, cbp, cbl, ctp, dl⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ForgetInnerArgs := .ofEquiv ForgetInnerArgs.equiv

private def forgetInnerStep (p : ForgetInnerArgs × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let a := p.1
  let d := p.2.1
  let acc := p.2.2
  let idx ← radixProjProg ⟨a.q, a.bagPtr, a.bagLen, a.m, a.v, d, 1, a.cBagPtr, a.cBagLen⟩
  let cVal ← Memory.read (a.cTblPtr + idx)
  let nextAcc := if a.mode = 1 then acc + cVal else (if cVal = 0 then acc else 1)
  pure (d + 1, nextAcc)

private def forgetInnerProg (a : ForgetInnerArgs) : Memory.Prog ℕ := do
  let res ← iterate forgetInnerStep a a.dLim (0, 0)
  pure res.2

private theorem forgetInnerStep_eval (a : ForgetInnerArgs) (d acc : ℕ) (t : Memory.State) :
    let idx := (Memory.spec 0).clientResult t
      (radixProjProg ⟨a.q, a.bagPtr, a.bagLen, a.m, a.v, d, 1, a.cBagPtr, a.cBagLen⟩)
    let cVal := t.mem (a.cTblPtr + idx)
    let nextAcc := if a.mode = 1 then acc + cVal else (if cVal = 0 then acc else 1)
    (Memory.spec 0).clientState t (forgetInnerStep (a, (d, acc))) = t ∧
    (Memory.spec 0).clientResult t (forgetInnerStep (a, (d, acc))) = (d + 1, nextAcc) := by
  unfold forgetInnerStep
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    radixProjProg_state]
  exact ⟨rfl, rfl⟩

private theorem forgetInnerProg_state (a : ForgetInnerArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (forgetInnerProg a) = s := by
  unfold forgetInnerProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of forgetInnerStep a
    (fun st m => (forgetInnerStep_eval a st.1 st.2 m).1) a.dLim (0, 0) s

private theorem forgetInnerProg_spec {w : ℕ} (counting : Bool) (a : ForgetInnerArgs)
    (hq : 0 < a.q) (hmode : a.mode = if counting then 1 else 0)
    {LB cBagL cTbl : List ℕ} {s : Memory.State}
    (hLB : HoldsIn a.bagPtr LB s) (hLB_len : LB.length = a.bagLen)
    (hcBag : HoldsIn a.cBagPtr cBagL s) (hcBag_len : cBagL.length = a.cBagLen)
    (hcTbl : HoldsIn a.cTblPtr cTbl s) (hcTbl_len : cTbl.length = a.q ^ a.cBagLen) :
    let addFn : ℕ → ℕ → ℕ :=
      if counting then (· + ·) else fun acc val => if val = 0 then acc else 1
    Memory.FramedTriple w s (forgetInnerProg a) (a.dLim * (a.cBagLen * (a.bagLen + 1) + 1)) ∅
      fun r t => r = dpAlgFold 0 addFn a.dLim
        (fun d => cTbl.getD (toRadix a.q cBagL (Function.update (ofRadix a.q LB a.m) a.v d)) 0) ∧
        t = s := by
  intro addFn
  set g := fun d => cTbl.getD (toRadix a.q cBagL (Function.update (ofRadix a.q LB a.m) a.v d)) 0
  have htf := hcTbl.1
  obtain ⟨-, hloop⟩ := Memory.FramedTriple.iterate (s := s) (body := forgetInnerStep)
    (c := a.cBagLen * (a.bagLen + 1) + 1) (S := ∅) (safe := fun _ _ _ => True) (d := a)
    (n := a.dLim) (a₀ := (0, 0)) (Q := fun st t => st.2 = dpAlgFold 0 addFn a.dLim g ∧ t = s)
    (fun k st t => t = s ∧ st = (k, dpAlgFold 0 addFn k g)) ⟨rfl, rfl⟩
    (fun k hk st t ⟨ht, hst⟩ _ => ⟨trivial, by
      subst t hst
      obtain ⟨hv_rp, hst_rp, hr_rp, hc_rp⟩ := radixProjProg_spec (w := w)
        ⟨a.q, a.bagPtr, a.bagLen, a.m, a.v, k, 1, a.cBagPtr, a.cBagLen⟩ hLB hLB_len hcBag hcBag_len
      simp only [radixProjAssign, ↓reduceIte] at hr_rp hc_rp
      have hrp := Memory.FramedTriple.of_readOnly hv_rp hst_rp hr_rp hc_rp
      have hidx_lt :
          toRadix a.q cBagL (Function.update (ofRadix a.q LB a.m) a.v k) < cTbl.length :=
        hcTbl_len ▸ hcBag_len ▸ toRadix_lt hq _ _
      unfold forgetInnerStep
      framed_triple
      refine ⟨rfl, ?_⟩
      rw [hcTbl.get _ hidx_lt, List.getElem_eq_getD 0, hmode]
      cases counting <;> rfl⟩)
    fun st t h _ => ⟨by rw [h.2], h.1⟩
  unfold forgetInnerProg
  exact Memory.FramedTriple.mono (Memory.FramedTriple.call (c₂ := 0) hloop subset_rfl
    fun st t h _ => Memory.FramedTriple.pure h) (by rw [Nat.mul_comm]; omega) fun _ _ => id

private theorem forgetInnerProg_realizes :
    Realizes .exact forgetInnerProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        0 < a.q ∧ Fits w 1 ∧ Fits w a.q ∧ Fits w a.m ∧ Fits w a.dLim ∧
        Fits w (a.bagPtr + a.bagLen) ∧
        Fits w (a.cBagPtr + a.cBagLen) ∧
        Fits w (a.q ^ a.cBagLen) ∧
        Fits w (a.cTblPtr + a.q ^ a.cBagLen) ∧
        ∃ (cTbl : List ℕ) (cCap : ℕ),
          HoldsIn a.cTblPtr cTbl s ∧
          cTbl.length = a.q ^ a.cBagLen ∧
          (∀ x ∈ cTbl, x ≤ cCap) ∧
          (a.mode = 1 → Fits w (a.dLim * cCap)))
      (fun _ _ => 0) := by
  refine Realizes.mono_mul (work := fun a _ => a.dLim) ?_ 1 fun a s => ?_
  · unfold forgetInnerProg
    realize [radixProjProg_realizes]
    · obtain ⟨hq_pos, h1, hfit_q, hfit_m, hfit_dLim, hfit_bag, hfit_cBag, hfit_cPow, hfit_cTbl,
        cTbl, cCap, hcTbl_h, hcTbl_len, hcTbl_le, hfit_sumCap⟩ := h
      refine iterationSafe_of_stepInv _ _ w _
        (fun (j : ℕ) (st : ℕ × ℕ) (t : Memory.State) =>
          j ≤ d.dLim ∧ st.1 + j = d.dLim ∧
          HoldsIn d.cTblPtr cTbl t ∧
          (if d.mode = 1 then st.2 ≤ st.1 * cCap else st.2 ≤ 1))
        (fun j st t ⟨hj_le, hd_eq, hcTbl_t, hacc_bound⟩ => ?_)
        ⟨le_rfl, Nat.zero_add _, hcTbl_h, by split_ifs <;> simp⟩
      let rpArgs : RadixProjArgs :=
        ⟨d.q, d.bagPtr, d.bagLen, d.m, d.v, st.1, 1, d.cBagPtr, d.cBagLen⟩
      have hidx_lt : (Memory.spec 0).clientResult t (radixProjProg rpArgs) < d.q ^ d.cBagLen :=
        radixProjProg_result_lt (args := rpArgs) hq_pos t
      have hlt_len : (Memory.spec 0).clientResult t (radixProjProg rpArgs) < cTbl.length :=
        hcTbl_len ▸ hidx_lt
      have hcVal_le :
          t.mem (d.cTblPtr + (Memory.spec 0).clientResult t (radixProjProg rpArgs)) ≤ cCap :=
        hcTbl_t.get _ hlt_len ▸ hcTbl_le _ (List.getElem_mem hlt_len)
      have hfit_d1 : Fits w (st.1 + 1) := hfit_dLim.of_le (by omega)
      have hacc_next (hm1 : d.mode = 1) :
          st.2 + t.mem (d.cTblPtr + (Memory.spec 0).clientResult t (radixProjProg rpArgs)) ≤
            (st.1 + 1) * cCap := by
        simp only [hm1, ↓reduceIte] at hacc_bound
        exact Nat.succ_mul st.1 cCap ▸ Nat.add_le_add hacc_bound hcVal_le
      obtain ⟨hst_ev, hres_ev⟩ := forgetInnerStep_eval d st.1 st.2 t
      refine ⟨?_, Nat.le_of_succ_le hj_le, by simp only [hres_ev]; omega,
        by rwa [hst_ev], ?_⟩
      · dsimp only [forgetInnerStep]
        rw [radixProjProg_state]
        refine ⟨⟨h1, hq_pos, h1, hfit_q, hfit_m, hfit_bag, hfit_cBag, hfit_cPow⟩,
          hfit_cTbl.of_le (by dsimp only [rpArgs] at hidx_lt; omega), h1, ?_⟩
        by_cases hm1 : d.mode = 1
        · simp only [hm1, ↓reduceIte]
          exact ⟨hfit_d1, (hfit_sumCap hm1).of_le
            ((hacc_next hm1).trans (Nat.mul_le_mul_right cCap (by omega)))⟩
        · simp only [hm1, ↓reduceIte] at hacc_bound ⊢
          split_ifs
          exacts [hfit_d1, ⟨hfit_d1, h1⟩]
      · rw [hres_ev]
        by_cases hm1 : d.mode = 1
        · simpa only [hm1, ↓reduceIte] using hacc_next hm1
        · simp only [hm1, ↓reduceIte] at hacc_bound ⊢
          split_ifs <;> omega
    · simp only [iterationWork_zero]; exact le_rfl
  · unfold forgetInnerProg
    rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
    have hquery : ∀ x m, 1 ≤ memoryCost (forgetInnerStep x) m := fun ⟨a', d', acc'⟩ m => by
      dsimp only [forgetInnerStep]
      rw [memoryCost_bind', radixProjProg_state, memoryCost_bind', memoryCost_read]
      omega
    simpa only [iterationWork_zero, Nat.one_mul] using
      Nat.le_succ_of_le (iterationWork_zero_le forgetInnerStep hquery a a.dLim (0, 0) s)

private structure ForgetFillArgs where
  mode : ℕ
  q : ℕ
  v : ℕ
  bagPtr : ℕ
  bagLen : ℕ
  cBagPtr : ℕ
  cBagLen : ℕ
  cTblPtr : ℕ
  dLim : ℕ
  tblPtr : ℕ
  tblLen : ℕ

private def ForgetFillArgs.equiv :
    ForgetFillArgs ≃ (((((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a :=
    ((((((((((a.mode, a.q), a.v), a.bagPtr), a.bagLen), a.cBagPtr), a.cBagLen), a.cTblPtr),
      a.dLim), a.tblPtr), a.tblLen)
  invFun := fun ((((((((((md, q), v), bp), bl), cbp), cbl), ctp), dl), tp), tl) =>
    ⟨md, q, v, bp, bl, cbp, cbl, ctp, dl, tp, tl⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ForgetFillArgs := .ofEquiv ForgetFillArgs.equiv

private def forgetOuterStep (p : ForgetFillArgs × ℕ) : Memory.Prog ℕ := do
  let a := p.1
  let m := p.2
  let val ← forgetInnerProg
    ⟨a.mode, a.q, a.v, a.bagPtr, a.bagLen, m, a.cBagPtr, a.cBagLen, a.cTblPtr, a.dLim⟩
  Memory.write (a.tblPtr + m) val
  pure (m + 1)

private def forgetFillProg (a : ForgetFillArgs) : Memory.Prog Unit := do
  let _ ← iterate forgetOuterStep a a.tblLen 0
  pure ()

private theorem forgetOuterStep_eval (a : ForgetFillArgs) (m : ℕ) (t : Memory.State) :
    let val := (Memory.spec 0).clientResult t
      (forgetInnerProg
        ⟨a.mode, a.q, a.v, a.bagPtr, a.bagLen, m, a.cBagPtr, a.cBagLen, a.cTblPtr, a.dLim⟩)
    (Memory.spec 0).clientState t (forgetOuterStep (a, m)) =
      ⟨Function.update t.mem (a.tblPtr + m) val, t.frontier⟩ ∧
    (Memory.spec 0).clientResult t (forgetOuterStep (a, m)) = m + 1 := by
  unfold forgetOuterStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    forgetInnerProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
  exact ⟨rfl, rfl⟩

private theorem forgetFillProg_spec {w : ℕ} (counting : Bool) (a : ForgetFillArgs)
    (hq : 0 < a.q) (hmode : a.mode = if counting then 1 else 0)
    {child : NiceTree ℕ} {cs : List (ConstraintTable a.q)} {vars : List ℕ}
    {s : Memory.State}
    (hdLim : a.dLim = if a.v ∈ vars then a.q else 1)
    (hLB : HoldsIn a.bagPtr ((bagList child).erase a.v) s)
    (hLB_len : ((bagList child).erase a.v).length = a.bagLen)
    (hLB_hi : a.bagPtr + a.bagLen ≤ a.tblPtr)
    (hcBag : HoldsIn a.cBagPtr (bagList child) s)
    (hcBag_len : (bagList child).length = a.cBagLen)
    (hcBag_hi : a.cBagPtr + a.cBagLen ≤ a.tblPtr)
    (hcTbl : HoldsIn a.cTblPtr (dpInstTree counting a.q cs vars child) s)
    (hcTbl_hi : a.cTblPtr + a.q ^ a.cBagLen ≤ a.tblPtr)
    (htblLen : a.tblLen = a.q ^ a.bagLen)
    (htbl_hi : a.tblPtr + a.tblLen ≤ s.frontier)
    (hfit_cap : Fits w (if counting then a.q ^ (NiceTree.forget a.v child).size else 1)) :
    let targetTbl := dpInstTree counting a.q cs vars (.forget a.v child)
    let s₁ := (Memory.spec 0).clientState s (forgetFillProg a)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (forgetFillProg a)) ∧
    s₁.frontier = s.frontier ∧
    PreservesBelow a.tblPtr s s₁ ∧
    HoldsIn a.tblPtr targetTbl s₁ ∧
    memoryCost (forgetFillProg a) s ≤
      a.tblLen * (a.dLim * (a.cBagLen * (a.bagLen + 1) + 1) + 1) := by
  let targetTbl := dpInstTree counting a.q cs vars (.forget a.v child)
  have htarget_len : targetTbl.length = a.tblLen := by
    simp [targetTbl, bagList, hLB_len, htblLen]
  let stepCost := a.dLim * (a.cBagLen * (a.bagLen + 1) + 1) + 1
  refine tableFillProg_spec forgetOuterStep a a.tblPtr a.tblLen stepCost targetTbl s
    (fun _ => True) trivial htarget_len htbl_hi fun k t hk_le _ hfr_t hp_t _ => ?_
  let m := a.tblLen - (k + 1)
  have hm_lt : m < a.tblLen := by omega
  have hLB_t : HoldsIn a.bagPtr ((bagList child).erase a.v) t :=
    hLB.mono (F := a.tblPtr) (by rw [hLB_len]; exact hLB_hi) hp_t
  have hcBag_t : HoldsIn a.cBagPtr (bagList child) t :=
    hcBag.mono (F := a.tblPtr) (by rw [hcBag_len]; exact hcBag_hi) hp_t
  have hcTbl_t : HoldsIn a.cTblPtr (dpInstTree counting a.q cs vars child) t :=
    hcTbl.mono (F := a.tblPtr) (by rw [length_dpInstTree, hcBag_len]; exact hcTbl_hi) hp_t
  have hin := forgetInnerProg_spec (w := w) counting
    ⟨a.mode, a.q, a.v, a.bagPtr, a.bagLen, m, a.cBagPtr, a.cBagLen, a.cTblPtr, a.dLim⟩
    hq hmode hLB_t hLB_len hcBag_t hcBag_len hcTbl_t (by rw [length_dpInstTree, hcBag_len])
  obtain ⟨-, -, -, hr_in, -⟩ := framedTriple_iff_realization.mp hin
  let entryVal := targetTbl[m]'(by rw [htarget_len]; exact hm_lt)
  have hval_eq :
      (Memory.spec 0).clientResult t
        (forgetInnerProg
          ⟨a.mode, a.q, a.v, a.bagPtr, a.bagLen, m, a.cBagPtr, a.cBagLen, a.cTblPtr, a.dLim⟩) =
        entryVal := by
    rw [hr_in]
    simp only [entryVal, targetTbl, dpInstTree, List.getElem_ofFn, hdLim]
    by_cases hv : a.v ∈ vars
    · simp [hv]
    · simp only [hv, ↓reduceIte, dpAlgFold]
      cases counting
      · have hlt : toRadix a.q (bagList child)
            (Function.update (ofRadix a.q ((bagList child).erase a.v) m) a.v 0) <
              (dpInstTree false a.q cs vars child).length :=
          (length_dpInstTree false a.q cs vars child).symm ▸ toRadix_lt hq _ _
        have := mem_dpInstTree_le false hq cs vars child _ (List.getElem_mem hlt)
        simp only [Bool.false_eq_true, ↓reduceIte, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some] at this ⊢
        split_ifs <;> omega
      · simp
  have hentry_fit : Fits w entryVal :=
    hfit_cap.of_le
      (mem_dpInstTree_le counting hq cs vars (.forget a.v child) _ (List.getElem_mem _))
  have hin' := Memory.FramedTriple.mono (Q' := fun r t' => r = entryVal ∧ t' = t) hin le_rfl
    fun r t' h => ⟨h.1.trans (hr_in.symm.trans hval_eq), h.2⟩
  obtain ⟨hv, hc, -, hr, hst⟩ := framedTriple_iff_realization.mp (show Memory.FramedTriple w t
      (forgetOuterStep (a, m)) (a.dLim * (a.cBagLen * (a.bagLen + 1) + 1) + 1) Set.univ
      fun r t' => r = m + 1 ∧ t' = ⟨Function.update t.mem (a.tblPtr + m) entryVal, t.frontier⟩ by
    unfold forgetOuterStep; framed_triple)
  exact ⟨hv, hst, hr, trivial, hc⟩

private theorem forgetFillProg_realizes :
    Realizes .exact forgetFillProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        0 < a.q ∧ Fits w 1 ∧ Fits w a.q ∧ Fits w a.dLim ∧
        Fits w (a.bagPtr + a.bagLen) ∧
        Fits w (a.cBagPtr + a.cBagLen) ∧
        Fits w (a.q ^ a.cBagLen) ∧
        Fits w (a.cTblPtr + a.q ^ a.cBagLen) ∧
        Fits w (a.tblPtr + a.tblLen) ∧
        ∃ (cTbl : List ℕ) (cCap : ℕ),
          a.cTblPtr + a.q ^ a.cBagLen ≤ a.tblPtr ∧
          HoldsIn a.cTblPtr cTbl s ∧
          cTbl.length = a.q ^ a.cBagLen ∧
          (∀ x ∈ cTbl, x ≤ cCap) ∧
          (a.mode = 1 → Fits w (a.dLim * cCap)))
      (fun _ _ => 0) := by
  refine Realizes.mono_mul (work := fun a _ => a.tblLen) ?_ 1 fun a s => ?_
  · unfold forgetFillProg
    realize [forgetInnerProg_realizes]
    · obtain ⟨hq_pos, h1, hfit_q, hfit_dLim, hfit_bag, hfit_cBag, hfit_cPow, hfit_cTbl, hfit_tbl,
        cTbl, cCap, hcTbl_hi, hcTbl_h, hcTbl_len, hcTbl_le, hfit_sumCap⟩ := h
      refine iterationSafe_of_stepInv _ _ w _
        (fun (j : ℕ) (m : ℕ) (t : Memory.State) =>
          j ≤ d.tblLen ∧ m + j = d.tblLen ∧
          HoldsIn d.cTblPtr cTbl t)
        (fun j m t ⟨hj_le, hm_eq, hcTbl_t⟩ => ?_)
        ⟨le_rfl, Nat.zero_add _, hcTbl_h⟩
      obtain ⟨hst_ev, hres_ev⟩ := forgetOuterStep_eval d m t
      refine ⟨?_, Nat.le_of_succ_le hj_le, by rw [hres_ev]; omega, ?_⟩
      · dsimp only [forgetOuterStep]
        exact ⟨⟨hq_pos, h1, hfit_q, hfit_tbl.of_le (by omega), hfit_dLim, hfit_bag, hfit_cBag,
          hfit_cPow, hfit_cTbl, cTbl, cCap, hcTbl_t, hcTbl_len, hcTbl_le, hfit_sumCap⟩,
          hfit_tbl.of_le (by omega), hfit_tbl.of_le (by omega)⟩
      · rw [hst_ev]
        exact holdsIn_write_outside hcTbl_t (.inr (by rw [hcTbl_len]; omega))
    · simp only [iterationWork_zero]; exact le_rfl
  · unfold forgetFillProg
    rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
    have hquery : ∀ x m, 1 ≤ memoryCost (forgetOuterStep x) m := fun ⟨a', m'⟩ st => by
      dsimp only [forgetOuterStep]
      rw [memoryCost_bind', forgetInnerProg_state, memoryCost_bind', memoryCost_write]
      omega
    simpa only [iterationWork_zero, Nat.one_mul] using
      Nat.le_succ_of_le (iterationWork_zero_le forgetOuterStep hquery a a.tblLen 0 s)

/-- Register arguments for the `forget` node handler `forgetNodeProg`. -/
structure ForgetNodeArgs where
  /-- Mode flag (`1` for exact model counting, `0` for satisfiability). -/
  mode : ℕ
  /-- Domain size `q`. -/
  q : ℕ
  /-- Forgotten variable label `v`. -/
  v : ℕ
  /-- Base address of the serialized CSP active-variable list `vars`. -/
  varsPtr : ℕ
  /-- Length of the serialized `vars` list. -/
  varsLen : ℕ
  /-- Base address of the child node's 4-word descriptor slot. -/
  dChild : ℕ
  /-- Base address of the current node's 4-word descriptor slot. -/
  dCur : ℕ

/-- Tuple equivalence encoding `ForgetNodeArgs` into Word-RAM registers. -/
@[expose] def ForgetNodeArgs.equiv :
    ForgetNodeArgs ≃ (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((((a.mode, a.q), a.v), a.varsPtr), a.varsLen), a.dChild), a.dCur)
  invFun := fun ((((((md, q), v), vp), vl), dch), dc) => ⟨md, q, v, vp, vl, dch, dc⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding ForgetNodeArgs := .ofEquiv ForgetNodeArgs.equiv

private theorem ite_pure_do {α β : Type} (c : Prop) [Decidable c] (x y : α)
    (k : α → Memory.Prog β) :
    (if c then (pure x >>= k) else (pure y >>= k)) = k (if c then x else y) := by
  split_ifs <;> simp

/-- Erase `a.v` from the child bag, aggregate DP entries over `a.v`, and write the descriptor
for a `forget` node. -/
def forgetNodeProg (a : ForgetNodeArgs) : Memory.Prog Unit := do
  let cBagPtr ← Memory.read a.dChild
  let cBagLen ← Memory.read (a.dChild + 1)
  let cTblPtr ← Memory.read (a.dChild + 2)
  let p ← eraseBagProg ⟨a.v, cBagPtr, cBagLen⟩
  let bagPtr := p.1
  let bagLen := p.2
  let tblLen ← powProg ⟨a.q, bagLen⟩
  let tblPtr ← Memory.allocDirty tblLen
  let inVars ← bagMemProg ⟨a.v, a.varsPtr, a.varsLen⟩
  let dLim ← if inVars = 1 then pure a.q else pure 1
  let _ ← forgetFillProg
    ⟨a.mode, a.q, a.v, bagPtr, bagLen, cBagPtr, cBagLen, cTblPtr, dLim, tblPtr, tblLen⟩
  writeDescProg ⟨a.dCur, bagPtr, bagLen, tblPtr, tblLen⟩

/-- Memory validity, framing, `NodeDescAt`, and cost bound for `forgetNodeProg`. -/
theorem forgetNodeProg_spec {w F_lo : ℕ} (counting : Bool) (a : ForgetNodeArgs)
    (hq : 0 < a.q) (hmode : a.mode = if counting then 1 else 0)
    {child : NiceTree ℕ} {cs : List (ConstraintTable a.q)} {vars : List ℕ}
    {s : Memory.State}
    (hvars : HoldsIn a.varsPtr vars s)
    (hvars_len : vars.length = a.varsLen)
    (hfit_bag_elems : ∀ u ∈ bagList child, Fits w u)
    (hchild : NodeDescAt F_lo counting a.q cs vars child a.dChild s)
    (hdCur : a.dCur + 4 ≤ F_lo)
    (hFlo : F_lo ≤ s.frontier)
    (hfit_peak : Fits w (s.frontier +
      max (bagList child).length
        (((bagList child).erase a.v).length + a.q ^ ((bagList child).erase a.v).length)))
    (hfit_cap : Fits w (if counting then a.q ^ (NiceTree.forget a.v child).size else 1)) :
    let LB := (bagList child).erase a.v
    let sEnd := (Memory.spec 0).clientState s (forgetNodeProg a)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (forgetNodeProg a)) ∧
    sEnd.frontier ≤ s.frontier + (LB.length + a.q ^ LB.length) ∧
    FrameOutsideRange a.dCur (a.dCur + 4) s sEnd ∧
    NodeDescAt F_lo counting a.q cs vars (.forget a.v child) a.dCur sEnd ∧
    memoryCost (forgetNodeProg a) s ≤
      14 + 3 * (bagList child).length + LB.length + a.varsLen +
        a.q ^ LB.length *
          (a.q * ((bagList child).length * (LB.length + 1) + 1) + 1) := by
  have hd_ch := hchild.desc_hi
  have hm_cbLen : s.mem (a.dChild + 1) = (bagList child).length := hchild.bag_len
  let cBagPtr := s.mem a.dChild
  let cBagLen := (bagList child).length
  let cTblPtr := s.mem (a.dChild + 2)
  let LB := (bagList child).erase a.v
  let bagPtr := s.frontier
  let bagLen := LB.length
  obtain ⟨hv_er, hr_er, hfr_er, hp_er, hLB_s₁, hc_er⟩ :=
    eraseBagProg_spec (w := w) ⟨a.v, cBagPtr, cBagLen⟩ hchild.bag_holds rfl hfit_bag_elems
      (hfit_peak.of_le (by dsimp only [LB]; omega))
  dsimp only at hr_er hfr_er hc_er
  let s₁ := (Memory.spec 0).clientState s (eraseBagProg ⟨a.v, cBagPtr, cBagLen⟩)
  have hs₁_fr_pos : 0 < s₁.frontier := by
    rw [hfr_er]
    omega
  obtain ⟨hv_pw, hst_pw, hr_pw, hc_pw⟩ := powProg_spec (w := w) ⟨a.q, bagLen⟩ hs₁_fr_pos
  dsimp only at hr_pw hc_pw
  let tblLen := a.q ^ bagLen
  let tblPtr := s₁.frontier
  have hs_tbl : s.frontier ≤ tblPtr := by dsimp only [tblPtr, s₁]; omega
  let s₂ := (Memory.spec 0).clientState s₁ (Memory.allocDirty tblLen)
  have hp₂ : PreservesBelow tblPtr s₁ s₂ := preservesBelow_allocDirty s₁ tblLen
  have hfit_fr₂ : Fits w (s₁.frontier + tblLen) := by
    rw [hfr_er]
    exact hfit_peak.of_le (by dsimp only [LB, tblLen, bagLen]; omega)
  have hp_s_s₂ : PreservesBelow bagPtr s s₂ := hp_er.trans (hp₂.mono_bound hs_tbl)
  obtain ⟨hv_bm, hst_bm, hr_bm, hc_bm⟩ :=
    bagMemProg_spec (w := w) ⟨a.v, a.varsPtr, a.varsLen⟩ (hvars.mono_frontier hp_s_s₂) hvars_len
  dsimp only at hr_bm hc_bm
  let dLim := if (if memBag a.v vars then 1 else 0) = 1 then a.q else 1
  have hdLim_eq : dLim = if a.v ∈ vars then a.q else 1 := by simp [dLim, memBag_eq_decide]
  have hdLim_le : dLim ≤ a.q := by
    rw [hdLim_eq]
    split_ifs <;> omega
  let fillArgs : ForgetFillArgs :=
    ⟨a.mode, a.q, a.v, bagPtr, bagLen, cBagPtr, cBagLen, cTblPtr, dLim, tblPtr, tblLen⟩
  obtain ⟨hv_fill, hfr_fill, hp_fill, htbl_fill, hc_fill⟩ :=
    forgetFillProg_spec (w := w) counting fillArgs hq hmode hdLim_eq
      (hLB_s₁.mono_frontier hp₂) rfl
      (by dsimp only [fillArgs, tblPtr, bagPtr, bagLen, LB]; rw [hfr_er])
      (hchild.bag_holds.mono_frontier hp_s_s₂) rfl
      (hchild.bag_holds.1.trans hs_tbl)
      (hchild.tbl_holds.mono_frontier hp_s_s₂)
      ((length_dpInstTree counting a.q cs vars child ▸ hchild.tbl_holds.1).trans hs_tbl)
      rfl le_rfl hfit_cap
  let s₃ := (Memory.spec 0).clientState s₂ (forgetFillProg fillArgs)
  have hp_s_s₃ : PreservesBelow bagPtr s s₃ := hp_s_s₂.trans (hp_fill.mono_bound hs_tbl)
  have hLB_s₃ : HoldsIn bagPtr LB s₃ :=
    (hLB_s₁.mono_frontier hp₂).mono (F := tblPtr)
      (by dsimp only [tblPtr, bagPtr, LB]; rw [hfr_er]) hp_fill
  have hFlo_tbl : F_lo ≤ tblPtr := hFlo.trans hs_tbl
  have hd_s₃ : a.dCur + 4 ≤ s₃.frontier :=
    (hdCur.trans hFlo_tbl).trans (hfr_fill ▸ Nat.le_add_right _ _)
  have hfit_bt : Fits w (s.frontier + bagLen + tblLen) := hfr_er ▸ hfit_fr₂
  obtain ⟨hv_wd, hfr_wd, hframe_wd, hm0, hm1, hm2, hm3, hc_wd⟩ :=
    writeDescProg_spec (w := w) ⟨a.dCur, bagPtr, bagLen, tblPtr, tblLen⟩ hd_s₃
      (hfit_bt.of_le ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
      (hfit_bt.of_le ((Nat.le_add_left _ _).trans (Nat.le_add_right _ _)))
      (hfit_fr₂.of_le (Nat.le_add_right _ _)) (hfit_fr₂.of_le (Nat.le_add_left _ _))
  dsimp only at hm0 hm1 hm2 hm3
  let sEnd := (Memory.spec 0).clientState s₃
    (writeDescProg ⟨a.dCur, bagPtr, bagLen, tblPtr, tblLen⟩)
  have ha2_r : (Memory.spec 0).clientResult s₁ (Memory.allocDirty tblLen) = tblPtr := rfl
  have hsEnd_eq : (Memory.spec 0).clientState s (forgetNodeProg a) = sEnd := by
    dsimp only [forgetNodeProg]
    iterate 3 rw [clientState_bind_read]
    rw [hm_cbLen, StateTransitionSpec.clientState_bind, hr_er]
    dsimp only
    rw [StateTransitionSpec.clientState_bind, hst_pw, hr_pw,
      StateTransitionSpec.clientState_bind, ha2_r, StateTransitionSpec.clientState_bind,
      hst_bm, hr_bm, ite_pure_do, StateTransitionSpec.clientState_bind]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [forgetNodeProg]
    iterate 3 refine validHistory_read_bind (by omega) ?_
    refine hm_cbLen ▸ validHistory_bind_step hv_er ?_
    change (Memory.spec w).ValidHistory s₁ _
    rw [hr_er]
    refine validHistory_bind_step hv_pw ?_
    rw [hst_pw, hr_pw]
    refine validHistory_bind_step (validHistory_allocDirty hfit_fr₂)
      (validHistory_bind_step hv_bm ?_)
    rw [hst_bm, hr_bm, ite_pure_do]
    exact validHistory_bind_step hv_fill hv_wd
  · rw [hsEnd_eq, hfr_wd, hfr_fill]
    dsimp only [s₂]
    rw [clientState_allocDirty, hfr_er]
    exact (Nat.add_assoc _ _ _).le
  · rw [hsEnd_eq]
    exact (FrameOutsideRange.of_preservesBelow a.dCur (a.dCur + 4) hp_s_s₃).trans hframe_wd
  · rw [hsEnd_eq]
    exact ⟨hdCur, hm0 ▸ hFlo, hm1,
      hm0 ▸ hLB_s₃.frame_outsideRange (.inr (le_trans hdCur hFlo)) hframe_wd,
      hm2 ▸ hFlo_tbl, hm3,
      hm2 ▸ htbl_fill.frame_outsideRange (.inr (hdCur.trans hFlo_tbl)) hframe_wd⟩
  · dsimp only [forgetNodeProg]
    iterate 3 rw [memoryCost_bind', memoryCost_read, clientState_read, clientResult_read]
    rw [hm_cbLen, memoryCost_bind', hr_er]
    dsimp only
    rw [memoryCost_bind', hst_pw, hr_pw, memoryCost_bind', memoryCost_allocDirty, ha2_r,
      memoryCost_bind', hst_bm, hr_bm, ite_pure_do, memoryCost_bind']
    have hmul_dLim :
        tblLen * (dLim * (cBagLen * (bagLen + 1) + 1) + 1) ≤
          tblLen * (a.q * (cBagLen * (bagLen + 1) + 1) + 1) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_right _ hdLim_le) 1)
    dsimp only [s₁, s₂, s₃, fillArgs, cBagPtr, cBagLen, cTblPtr, bagPtr, bagLen, tblPtr, tblLen,
      dLim, LB] at hc_er hc_pw hc_bm hc_fill hmul_dLim hc_wd ⊢
    omega

/-- Exact-basis Word-RAM realization certificate for `forgetNodeProg`. -/
theorem forgetNodeProg_realizes :
    Realizes .exact forgetNodeProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        0 < a.q ∧ Fits w 3 ∧ Fits w a.q ∧
        Fits w (a.varsPtr + a.varsLen) ∧
        Fits w (a.dChild + 3) ∧ Fits w (a.dCur + 3) ∧
        ∃ (F_lo : ℕ) (counting : Bool) (child : NiceTree ℕ)
          (cs : List (ConstraintTable a.q)) (vars : List ℕ),
          a.mode = (if counting then 1 else 0) ∧
          (∀ u ∈ bagList child, Fits w u) ∧
          NodeDescAt F_lo counting a.q cs vars child a.dChild s ∧
          F_lo ≤ s.frontier ∧
          Fits w (a.q ^ (bagList child).length) ∧
          Fits w (s.frontier +
            max (bagList child).length
              (((bagList child).erase a.v).length + a.q ^ ((bagList child).erase a.v).length)) ∧
          Fits w (if counting then a.q ^ (NiceTree.forget a.v child).size else 1))
      (fun _ _ => 0) := by
  unfold forgetNodeProg
  realize [eraseBagProg_realizes, powProg_realizes, bagMemProg_realizes,
    forgetFillProg_realizes, writeDescProg_realizes]
  all_goals
    obtain ⟨hq, h3, hfit_q, hfit_vars, hdCh, hdCur, F_lo, counting, child, cs, vars, hmode,
      hfit_elems, hch, hFlo, hfit_cPow, hfit_peak, hfit_cap⟩ := h
    have h1 : Fits w 1 := h3.of_le (by decide)
    try rw [hch.bag_len]
    obtain ⟨_, hr_er, hfr_er, hp_er, _, _⟩ :=
      eraseBagProg_spec (w := w) ⟨d.v, s.mem d.dChild, (bagList child).length⟩
        hch.bag_holds rfl hfit_elems (hfit_peak.of_le (by dsimp only; omega))
    dsimp only at hr_er hfr_er
    let s₁ :=
      (Memory.spec 0).clientState s (eraseBagProg ⟨d.v, s.mem d.dChild, (bagList child).length⟩)
    try rw [hr_er]; dsimp only
    try rw [powProg_state]
    try rw [powProg_result]; dsimp only
    let bagLen := ((bagList child).erase d.v).length
    let tblLen := d.q ^ bagLen
    let s₂ := (Memory.spec 0).clientState s₁ (Memory.allocDirty tblLen)
    have hp₂ : PreservesBelow s₁.frontier s₁ s₂ := preservesBelow_allocDirty s₁ tblLen
    try rw [bagMemProg_state]
    have hp_all : PreservesBelow s.frontier s s₂ :=
      hp_er.trans (hp₂.mono_bound (by rw [hfr_er]; omega))
    have hc_bag := hch.bag_holds.1
    have hc_tbl : s.mem (d.dChild + 2) + d.q ^ (bagList child).length ≤ s.frontier :=
      length_dpInstTree counting d.q cs vars child ▸ hch.tbl_holds.1
    let cCap := if counting then d.q ^ child.size else 1
    have hex_er : ∃ xs : List ℕ,
        HoldsIn (s.mem d.dChild) xs s ∧
        xs.length = (bagList child).length ∧
        s.mem d.dChild + (bagList child).length ≤ s.frontier ∧
        (∀ u ∈ xs, Fits w u) ∧
        Fits w (s.frontier + (bagList child).length) :=
      ⟨bagList child, hch.bag_holds, rfl, hc_bag, hfit_elems, hfit_peak.of_le (by omega)⟩
    have hf_tblEnd : Fits w (s₁.frontier + tblLen) :=
      hfit_peak.of_le (by rw [hfr_er]; dsimp only [bagLen, tblLen]; omega)
    have hex_fill (dLim : ℕ) (hdLim_le : dLim ≤ d.q) :
        ∃ (cTbl : List ℕ) (cCap' : ℕ),
          s.mem (d.dChild + 2) + d.q ^ (bagList child).length ≤ s₁.frontier ∧
          HoldsIn (s.mem (d.dChild + 2)) cTbl s₂ ∧
          cTbl.length = d.q ^ (bagList child).length ∧
          (∀ x ∈ cTbl, x ≤ cCap') ∧
          (d.mode = 1 → Fits w (dLim * cCap')) := by
      refine ⟨dpInstTree counting d.q cs vars child, cCap, by rw [hfr_er]; omega,
        hch.tbl_holds.mono_frontier hp_all, length_dpInstTree _ _ _ _ _,
        mem_dpInstTree_le counting hq cs vars child, fun hm1 => ?_⟩
      cases counting
      · exact absurd hm1 (by simp [hmode])
      · simp only [↓reduceIte, NiceTree.size_forget, Nat.pow_succ, Nat.mul_comm] at hfit_cap
        exact hfit_cap.of_le (Nat.mul_le_mul_right _ hdLim_le)
    repeat (
      first
      | assumption
      | exact hex_fill d.q le_rfl
      | exact hex_fill 1 (by omega)
      | exact hdCh.of_le (by omega)
      | exact hfit_peak.of_le (by omega))

end Cslib.Algorithms.WordRAM.TreeDecomposition
