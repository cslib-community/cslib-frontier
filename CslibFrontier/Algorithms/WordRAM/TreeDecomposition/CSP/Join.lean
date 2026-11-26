/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.NodeDesc
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.Radix
import CslibFrontier.Tactic.Realize

/-!
# Word-RAM `join` node handler

This module certifies `joinNodeProg` (along with the private loop `joinFillProg`). It combines left
and right child DP tables entrywise by projecting each left-bag assignment onto the right child bag
via `radixProjProg`, and has no dependency on `BagOps`, `ConstraintScan`, `LeafIntro`, or `Forget`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.JoinNodeArgs`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.joinNodeProg`: `join` node handler.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.joinNodeProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.joinNodeProg_realizes`: correctness and realization
  of `joinNodeProg`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open SimpleGraph
open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! #### 4. Join node handler (`joinFillProg`, `joinNodeProg`) -/

private structure JoinFillArgs where
  q : ℕ
  lBagPtr : ℕ
  lBagLen : ℕ
  lTblPtr : ℕ
  rBagPtr : ℕ
  rBagLen : ℕ
  rTblPtr : ℕ
  tblPtr : ℕ
  tblLen : ℕ

private def JoinFillArgs.equiv :
    JoinFillArgs ≃ (((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a :=
    ((((((((a.q, a.lBagPtr), a.lBagLen), a.lTblPtr), a.rBagPtr), a.rBagLen), a.rTblPtr),
      a.tblPtr), a.tblLen)
  invFun := fun ((((((((q, lbp), lbl), ltp), rbp), rbl), rtp), tp), tl) =>
    ⟨q, lbp, lbl, ltp, rbp, rbl, rtp, tp, tl⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding JoinFillArgs := .ofEquiv JoinFillArgs.equiv

private def joinFillStep (p : JoinFillArgs × ℕ) : Memory.Prog ℕ := do
  let a := p.1
  let m := p.2
  let lv ← Memory.read (a.lTblPtr + m)
  let mr ← radixProjProg ⟨a.q, a.lBagPtr, a.lBagLen, m, 0, 0, 0, a.rBagPtr, a.rBagLen⟩
  let rv ← Memory.read (a.rTblPtr + mr)
  Memory.write (a.tblPtr + m) (lv * rv)
  pure (m + 1)

private def joinFillProg (a : JoinFillArgs) : Memory.Prog Unit := do
  let _ ← iterate joinFillStep a a.tblLen 0
  pure ()

private theorem joinFillStep_eval (a : JoinFillArgs) (m : ℕ) (t : Memory.State) :
    let mr := (Memory.spec 0).clientResult t
      (radixProjProg ⟨a.q, a.lBagPtr, a.lBagLen, m, 0, 0, 0, a.rBagPtr, a.rBagLen⟩)
    let lv := t.mem (a.lTblPtr + m)
    let rv := t.mem (a.rTblPtr + mr)
    (Memory.spec 0).clientState t (joinFillStep (a, m)) =
      ⟨Function.update t.mem (a.tblPtr + m) (lv * rv), t.frontier⟩ ∧
    (Memory.spec 0).clientResult t (joinFillStep (a, m)) = m + 1 := by
  unfold joinFillStep
  dsimp only
  rw [clientState_bind_read, clientResult_bind_read, StateTransitionSpec.clientState_bind,
    StateTransitionSpec.clientResult_bind, radixProjProg_state]
  exact ⟨rfl, rfl⟩

private theorem joinFillProg_spec {w : ℕ} (counting : Bool) (a : JoinFillArgs)
    (hq : 0 < a.q) {left right : NiceTree ℕ} {cs : List (ConstraintTable a.q)} {vars : List ℕ}
    {s : Memory.State}
    (hlBag : HoldsIn a.lBagPtr (bagList left) s)
    (hlBag_len : (bagList left).length = a.lBagLen)
    (hlBag_hi : a.lBagPtr + a.lBagLen ≤ a.tblPtr)
    (hlTbl : HoldsIn a.lTblPtr (dpInstTree counting a.q cs vars left) s)
    (hlTbl_hi : a.lTblPtr + a.tblLen ≤ a.tblPtr)
    (hrBag : HoldsIn a.rBagPtr (bagList right) s)
    (hrBag_len : (bagList right).length = a.rBagLen)
    (hrBag_hi : a.rBagPtr + a.rBagLen ≤ a.tblPtr)
    (hrTbl : HoldsIn a.rTblPtr (dpInstTree counting a.q cs vars right) s)
    (hrTbl_hi : a.rTblPtr + a.q ^ a.rBagLen ≤ a.tblPtr)
    (htblLen : a.tblLen = a.q ^ a.lBagLen)
    (htbl_hi : a.tblPtr + a.tblLen ≤ s.frontier)
    (hfit_cap : Fits w (if counting then a.q ^ (NiceTree.join left right).size else 1)) :
    let targetTbl := dpInstTree counting a.q cs vars (.join left right)
    let s₁ := (Memory.spec 0).clientState s (joinFillProg a)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (joinFillProg a)) ∧
    s₁.frontier = s.frontier ∧
    PreservesBelow a.tblPtr s s₁ ∧
    HoldsIn a.tblPtr targetTbl s₁ ∧
    memoryCost (joinFillProg a) s ≤
      a.tblLen * (a.rBagLen * (a.lBagLen + 1) + 3) := by
  let targetTbl := dpInstTree counting a.q cs vars (.join left right)
  have htarget_len : targetTbl.length = a.tblLen := by
    simp [targetTbl, bagList, hlBag_len, htblLen]
  let stepCost := a.rBagLen * (a.lBagLen + 1) + 3
  refine tableFillProg_spec joinFillStep a a.tblPtr a.tblLen stepCost targetTbl s
    (fun _ => True) trivial htarget_len htbl_hi fun k t hk_le _ hfr_t hp_t _ => ?_
  let m := a.tblLen - (k + 1)
  have hm_lt : m < a.tblLen := by omega
  have hlBag_t : HoldsIn a.lBagPtr (bagList left) t :=
    hlBag.mono (F := a.tblPtr) (by rw [hlBag_len]; exact hlBag_hi) hp_t
  have hrBag_t : HoldsIn a.rBagPtr (bagList right) t :=
    hrBag.mono (F := a.tblPtr) (by rw [hrBag_len]; exact hrBag_hi) hp_t
  have hlTbl_t : HoldsIn a.lTblPtr (dpInstTree counting a.q cs vars left) t :=
    hlTbl.mono (F := a.tblPtr) (by rw [length_dpInstTree, hlBag_len, ← htblLen]; exact hlTbl_hi)
      hp_t
  have hrTbl_t : HoldsIn a.rTblPtr (dpInstTree counting a.q cs vars right) t :=
    hrTbl.mono (F := a.tblPtr) (by rw [length_dpInstTree, hrBag_len]; exact hrTbl_hi) hp_t
  obtain ⟨hv_rp, hst_rp, hr_rp, hc_rp⟩ :=
    radixProjProg_spec (w := w)
      ⟨a.q, a.lBagPtr, a.lBagLen, m, 0, 0, 0, a.rBagPtr, a.rBagLen⟩
      hlBag_t hlBag_len hrBag_t hrBag_len
  simp only [radixProjAssign, Nat.zero_ne_one, ↓reduceIte] at hr_rp hc_rp
  let mr := toRadix a.q (bagList right) (ofRadix a.q (bagList left) m)
  have hmr_lt : mr < a.q ^ a.rBagLen := hrBag_len ▸ toRadix_lt hq _ _
  have hm_lv : t.mem (a.lTblPtr + m) = (dpInstTree counting a.q cs vars left).getD m 0 :=
    (hlTbl_t.get m (by rw [length_dpInstTree, hlBag_len, ← htblLen]; omega)).trans
      (List.getElem_eq_getD 0)
  have hm_rv : t.mem (a.rTblPtr + mr) = (dpInstTree counting a.q cs vars right).getD mr 0 :=
    (hrTbl_t.get mr (by rw [length_dpInstTree, hrBag_len]; omega)).trans
      (List.getElem_eq_getD 0)
  let entryVal := targetTbl[m]'(by rw [htarget_len]; exact hm_lt)
  have hprod_eq : t.mem (a.lTblPtr + m) * t.mem (a.rTblPtr + mr) = entryVal := by
    rw [hm_lv, hm_rv]
    simp only [entryVal, targetTbl, dpInstTree, mr, List.getElem_ofFn]
  have hentry_fit : Fits w entryVal :=
    hfit_cap.of_le (mem_dpInstTree_le counting hq cs vars (.join left right) _ (List.getElem_mem _))
  obtain ⟨hst_ev, hres_ev⟩ := joinFillStep_eval a m t
  dsimp only [mr] at hprod_eq
  have hv_step : (Memory.spec w).ValidHistory t
      ((Memory.spec w).clientHistory t (joinFillStep (a, m))) := by
    unfold joinFillStep
    dsimp only
    refine validHistory_read_bind (by rw [hfr_t]; omega) ?_
    refine validHistory_bind_step hv_rp ?_
    rw [hst_rp, hr_rp]
    refine validHistory_read_bind (by rw [hfr_t]; omega) ?_
    rw [hprod_eq]
    exact validHistory_write_bind (by rw [hfr_t]; omega) hentry_fit (validHistory_pure w _ _)
  have hc_step : memoryCost (joinFillStep (a, m)) t ≤ stepCost := by
    unfold joinFillStep
    dsimp only
    rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind', hst_rp,
      memoryCost_bind', memoryCost_read, clientState_read,
      memoryCost_bind', memoryCost_write, memoryCost_pure]
    dsimp only [stepCost]
    omega
  exact ⟨hv_step, by rw [hst_ev, hr_rp, hprod_eq], hres_ev, trivial, hc_step⟩

private theorem joinFillProg_realizes :
    Realizes .exact joinFillProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        0 < a.q ∧ Fits w 1 ∧ Fits w a.q ∧
        Fits w (a.lBagPtr + a.lBagLen) ∧
        Fits w (a.lTblPtr + a.tblLen) ∧
        Fits w (a.rBagPtr + a.rBagLen) ∧
        Fits w (a.q ^ a.rBagLen) ∧
        Fits w (a.rTblPtr + a.q ^ a.rBagLen) ∧
        Fits w (a.tblPtr + a.tblLen) ∧
        ∃ (lTbl rTbl : List ℕ) (lCap rCap : ℕ),
          a.lTblPtr + a.tblLen ≤ a.tblPtr ∧
          a.rTblPtr + a.q ^ a.rBagLen ≤ a.tblPtr ∧
          HoldsIn a.lTblPtr lTbl s ∧ lTbl.length = a.tblLen ∧ (∀ x ∈ lTbl, x ≤ lCap) ∧
          HoldsIn a.rTblPtr rTbl s ∧ rTbl.length = a.q ^ a.rBagLen ∧ (∀ x ∈ rTbl, x ≤ rCap) ∧
          Fits w (lCap * rCap))
      (fun _ _ => 0) := by
  unfold joinFillProg
  realize [radixProjProg_realizes]
  obtain ⟨hq_pos, h1, hfit_q, hfit_lBag, hfit_lTbl, hfit_rBag, hfit_rPow, hfit_rTbl, hfit_tbl,
    lTbl, rTbl, lCap, rCap, hl_hi, hr_hi, hl_h, hl_len, hl_le, hr_h, hr_len, hr_le, hfit_prod⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (m : ℕ) (t : Memory.State) =>
      j ≤ d.tblLen ∧ m + j = d.tblLen ∧
      HoldsIn d.lTblPtr lTbl t ∧ HoldsIn d.rTblPtr rTbl t)
    (fun j m t ⟨hj_le, hm_eq, hl_t, hr_t⟩ => ?_)
    ⟨le_rfl, Nat.zero_add _, hl_h, hr_h⟩
  have hm_lt : m < d.tblLen := by omega
  have hmr_lt : (Memory.spec 0).clientResult t
      (radixProjProg ⟨d.q, d.lBagPtr, d.lBagLen, m, 0, 0, 0, d.rBagPtr, d.rBagLen⟩) <
        d.q ^ d.rBagLen :=
    radixProjProg_result_lt hq_pos t
  have hlv_le : t.mem (d.lTblPtr + m) ≤ lCap :=
    hl_t.get m (hl_len ▸ hm_lt) ▸ hl_le _ (List.getElem_mem _)
  have hrv_le : t.mem (d.rTblPtr + (Memory.spec 0).clientResult t
      (radixProjProg ⟨d.q, d.lBagPtr, d.lBagLen, m, 0, 0, 0, d.rBagPtr, d.rBagLen⟩)) ≤ rCap :=
    hr_t.get _ (hr_len ▸ hmr_lt) ▸ hr_le _ (List.getElem_mem _)
  have hfit_mul : Fits w (t.mem (d.lTblPtr + m) * t.mem (d.rTblPtr +
      (Memory.spec 0).clientResult t
        (radixProjProg ⟨d.q, d.lBagPtr, d.lBagLen, m, 0, 0, 0, d.rBagPtr, d.rBagLen⟩))) :=
    hfit_prod.of_le (Nat.mul_le_mul hlv_le hrv_le)
  obtain ⟨hst_ev, hres_ev⟩ := joinFillStep_eval d m t
  refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_⟩
  · dsimp only [joinFillStep]
    rw [radixProjProg_state]
    exact ⟨hfit_lTbl.of_le (by omega),
      ⟨hq_pos, h1, hfit_q, hfit_tbl.of_le (by omega), hfit_lBag, hfit_rBag, hfit_rPow⟩,
      hfit_rTbl.of_le (by omega),
      ⟨hfit_tbl.of_le (by omega), hfit_mul⟩,
      hfit_tbl.of_le (by omega)⟩
  · rw [hres_ev]; omega
  · rw [hst_ev]
    exact holdsIn_write_outside hl_t (.inr (by rw [hl_len]; omega))
  · rw [hst_ev]
    exact holdsIn_write_outside hr_t (.inr (by rw [hr_len]; omega))

/-- Register arguments for the `join` node handler `joinNodeProg`. -/
structure JoinNodeArgs where
  /-- Domain size `q`. -/
  q : ℕ
  /-- Base address of the left child's 4-word descriptor slot. -/
  dLeft : ℕ
  /-- Base address of the right child's 4-word descriptor slot. -/
  dRight : ℕ
  /-- Base address of the current node's 4-word descriptor slot. -/
  dCur : ℕ

/-- Tuple equivalence encoding `JoinNodeArgs` into Word-RAM registers. -/
@[expose] def JoinNodeArgs.equiv : JoinNodeArgs ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun a := (((a.q, a.dLeft), a.dRight), a.dCur)
  invFun := fun (((q, dl), dr), dc) => ⟨q, dl, dr, dc⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding JoinNodeArgs := .ofEquiv JoinNodeArgs.equiv

/-- Combine two child DP tables entrywise via `radixProjProg` and write the descriptor for a
`join` node. -/
def joinNodeProg (a : JoinNodeArgs) : Memory.Prog Unit := do
  let lBagPtr ← Memory.read a.dLeft
  let lBagLen ← Memory.read (a.dLeft + 1)
  let lTblPtr ← Memory.read (a.dLeft + 2)
  let lTblLen ← Memory.read (a.dLeft + 3)
  let rBagPtr ← Memory.read a.dRight
  let rBagLen ← Memory.read (a.dRight + 1)
  let rTblPtr ← Memory.read (a.dRight + 2)
  let tblPtr ← Memory.allocDirty lTblLen
  let _ ← joinFillProg
    ⟨a.q, lBagPtr, lBagLen, lTblPtr, rBagPtr, rBagLen, rTblPtr, tblPtr, lTblLen⟩
  writeDescProg ⟨a.dCur, lBagPtr, lBagLen, tblPtr, lTblLen⟩

/-- Memory validity, framing, `NodeDescAt`, and cost bound for `joinNodeProg`. -/
theorem joinNodeProg_spec {w F_lo : ℕ} (counting : Bool) (a : JoinNodeArgs)
    (hq : 0 < a.q) {left right : NiceTree ℕ} {cs : List (ConstraintTable a.q)} {vars : List ℕ}
    {s : Memory.State}
    (hleft : NodeDescAt F_lo counting a.q cs vars left a.dLeft s)
    (hright : NodeDescAt F_lo counting a.q cs vars right a.dRight s)
    (hdCur : a.dCur + 4 ≤ F_lo)
    (hFlo : F_lo ≤ s.frontier)
    (hfit_peak : Fits w (s.frontier + a.q ^ (bagList left).length))
    (hfit_cap : Fits w (if counting then a.q ^ (NiceTree.join left right).size else 1)) :
    let sEnd := (Memory.spec 0).clientState s (joinNodeProg a)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (joinNodeProg a)) ∧
    sEnd.frontier ≤ s.frontier + a.q ^ (bagList left).length ∧
    FrameOutsideRange a.dCur (a.dCur + 4) s sEnd ∧
    NodeDescAt F_lo counting a.q cs vars (.join left right) a.dCur sEnd ∧
    memoryCost (joinNodeProg a) s ≤
      12 + a.q ^ (bagList left).length *
        ((bagList right).length * ((bagList left).length + 1) + 3) := by
  have hd_l := hleft.desc_hi
  have hd_r := hright.desc_hi
  let lBagPtr := s.mem a.dLeft
  let lBagLen := (bagList left).length
  let lTblPtr := s.mem (a.dLeft + 2)
  let lTblLen := a.q ^ lBagLen
  let rBagPtr := s.mem a.dRight
  let rBagLen := (bagList right).length
  let rTblPtr := s.mem (a.dRight + 2)
  let tblPtr := s.frontier
  let s₁ := (Memory.spec 0).clientState s (Memory.allocDirty lTblLen)
  have hs₁_fr : s₁.frontier = tblPtr + lTblLen := rfl
  have hp₁ : PreservesBelow tblPtr s s₁ := preservesBelow_allocDirty s lTblLen
  have hv₁ : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty lTblLen)) :=
    validHistory_allocDirty hfit_peak
  let fillArgs : JoinFillArgs :=
    ⟨a.q, lBagPtr, lBagLen, lTblPtr, rBagPtr, rBagLen, rTblPtr, tblPtr, lTblLen⟩
  obtain ⟨hv_fill, hfr_fill, hp_fill, htbl_fill, hc_fill⟩ :=
    joinFillProg_spec (w := w) counting fillArgs hq
      (hleft.bag_holds.mono_frontier hp₁) rfl hleft.bag_holds.1
      (hleft.tbl_holds.mono_frontier hp₁)
      (by simpa only [length_dpInstTree] using hleft.tbl_holds.1)
      (hright.bag_holds.mono_frontier hp₁) rfl hright.bag_holds.1
      (hright.tbl_holds.mono_frontier hp₁)
      (by simpa only [length_dpInstTree] using hright.tbl_holds.1)
      rfl (by rw [hs₁_fr]) hfit_cap
  let s₂ := (Memory.spec 0).clientState s₁ (joinFillProg fillArgs)
  have hs₂_fr : s₂.frontier = tblPtr + lTblLen := by rw [hfr_fill, hs₁_fr]
  have hp_s_s₂ : PreservesBelow tblPtr s s₂ := hp₁.trans hp_fill
  have hlBag_s₂ : HoldsIn lBagPtr (bagList left) s₂ :=
    hleft.bag_holds.mono_frontier hp_s_s₂
  have hd_s₂ : a.dCur + 4 ≤ s₂.frontier := by rw [hs₂_fr]; dsimp only [tblPtr]; omega
  obtain ⟨hv_wd, hfr_wd, hframe_wd, hm0, hm1, hm2, hm3, hc_wd⟩ :=
    writeDescProg_spec (w := w) ⟨a.dCur, lBagPtr, lBagLen, tblPtr, lTblLen⟩ hd_s₂
      (hfit_peak.of_le (by have := hleft.bag_holds.1; dsimp only [lBagPtr]; omega))
      (hfit_peak.of_le (by have := hleft.bag_holds.1; dsimp only [lBagLen]; omega))
      (hfit_peak.of_le (by dsimp only [tblPtr]; omega))
      (hfit_peak.of_le (by dsimp only [lTblLen, lBagLen]; omega))
  dsimp only at hm0 hm1 hm2 hm3
  let sEnd := (Memory.spec 0).clientState s₂
    (writeDescProg ⟨a.dCur, lBagPtr, lBagLen, tblPtr, lTblLen⟩)
  have ha1_s : (Memory.spec 0).clientState s (Memory.allocDirty lTblLen) = s₁ := rfl
  have ha1_r : (Memory.spec 0).clientResult s (Memory.allocDirty lTblLen) = tblPtr := rfl
  have hsEnd_eq : (Memory.spec 0).clientState s (joinNodeProg a) = sEnd := by
    unfold joinNodeProg
    iterate 7 rw [clientState_bind_read]
    rw [hleft.bag_len, hleft.tbl_len, hright.bag_len,
      StateTransitionSpec.clientState_bind, ha1_s, ha1_r,
      StateTransitionSpec.clientState_bind]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold joinNodeProg
    iterate 7 (refine validHistory_read_bind (by omega) ?_)
    rw [hleft.bag_len, hleft.tbl_len, hright.bag_len]
    refine validHistory_bind_step hv₁ ?_
    rw [ha1_s, ha1_r]
    exact validHistory_bind_step hv_fill hv_wd
  · rw [hsEnd_eq, hfr_wd, hs₂_fr]
  · rw [hsEnd_eq]
    exact (FrameOutsideRange.of_preservesBelow a.dCur (a.dCur + 4) hp_s_s₂).trans hframe_wd
  · rw [hsEnd_eq]
    exact ⟨hdCur, hm0 ▸ hleft.bag_lo, hm1,
      hm0 ▸ hlBag_s₂.frame_outsideRange (.inr (le_trans hdCur hleft.bag_lo)) hframe_wd,
      hm2 ▸ hFlo, hm3,
      hm2 ▸ htbl_fill.frame_outsideRange (.inr (le_trans hdCur hFlo)) hframe_wd⟩
  · unfold joinNodeProg
    iterate 7 rw [memoryCost_bind', memoryCost_read, clientState_read, clientResult_read]
    rw [hleft.bag_len, hleft.tbl_len, hright.bag_len, memoryCost_bind', memoryCost_allocDirty,
      ha1_s, ha1_r, memoryCost_bind']
    dsimp only [s₂, fillArgs, lBagPtr, lBagLen, lTblPtr, lTblLen, rBagPtr, rBagLen, rTblPtr,
      tblPtr] at hc_fill hc_wd ⊢
    omega

/-- Exact-basis Word-RAM realization certificate for `joinNodeProg`. -/
theorem joinNodeProg_realizes :
    Realizes .exact joinNodeProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        0 < a.q ∧ Fits w 3 ∧ Fits w a.q ∧
        Fits w (a.dLeft + 3) ∧ Fits w (a.dRight + 2) ∧ Fits w (a.dCur + 3) ∧
        ∃ (F_lo : ℕ) (counting : Bool) (left right : NiceTree ℕ)
          (cs : List (ConstraintTable a.q)) (vars : List ℕ),
          NodeDescAt F_lo counting a.q cs vars left a.dLeft s ∧
          NodeDescAt F_lo counting a.q cs vars right a.dRight s ∧
          Fits w (a.q ^ (bagList right).length) ∧
          Fits w (s.frontier + a.q ^ (bagList left).length) ∧
          Fits w (if counting then a.q ^ (NiceTree.join left right).size else 1))
      (fun _ _ => 0) := by
  unfold joinNodeProg
  realize [joinFillProg_realizes, writeDescProg_realizes]
  all_goals
    obtain ⟨hq, _, hfit_q, hdL, hdR, hdCur, F_lo, counting, left, right, cs, vars,
      hl, hr, hfit_rPow, hfit_peak, hfit_cap⟩ := h
    try rw [hl.bag_len]
    try rw [hl.tbl_len]
    try rw [hr.bag_len]
    let lTblLen := d.q ^ (bagList left).length
    let s₁ := (Memory.spec 0).clientState s (Memory.allocDirty lTblLen)
    have hp₁ : PreservesBelow s.frontier s s₁ := preservesBelow_allocDirty s lTblLen
    have hl_bag := hl.bag_holds.1
    have hl_tbl := hl.tbl_holds.1
    rw [length_dpInstTree] at hl_tbl
    have hr_bag := hr.bag_holds.1
    have hr_tbl := hr.tbl_holds.1
    rw [length_dpInstTree] at hr_tbl
    let lCap := if counting then d.q ^ left.size else 1
    let rCap := if counting then d.q ^ right.size else 1
    have hprod_cap : Fits w (lCap * rCap) := by
      cases counting
      · simpa [lCap, rCap] using hfit_cap
      · simp only [lCap, rCap, ↓reduceIte, ← Nat.pow_add] at hfit_cap ⊢
        exact hfit_cap.of_le (Nat.pow_le_pow_right hq (by simp [NiceTree.size_join]))
    first
    | exact hdL.of_le (by omega)
    | exact hdR.of_le (by omega)
    | exact hdCur
    | exact hq
    | exact hfit_q
    | exact hfit_rPow
    | exact hfit_peak.of_le (by omega)
    | exact ⟨dpInstTree counting d.q cs vars left, dpInstTree counting d.q cs vars right,
        lCap, rCap, hl_tbl, hr_tbl,
        hl.tbl_holds.mono_frontier hp₁, length_dpInstTree _ _ _ _ _,
        mem_dpInstTree_le counting hq cs vars left,
        hr.tbl_holds.mono_frontier hp₁, length_dpInstTree _ _ _ _ _,
        mem_dpInstTree_le counting hq cs vars right,
        hprod_cap⟩

end Cslib.Algorithms.WordRAM.TreeDecomposition
