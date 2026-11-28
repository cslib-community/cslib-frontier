/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.NodeDesc
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.ConstraintScan
import CslibFrontier.Tactic.Realize

/-!
# Word-RAM `leaf` and `introduce` node handlers

This module certifies `leafNodeProg` and `introNodeProg` (along with the private helpers
`introFillProg` and `copyBagProg`). It builds in parallel with the `Forget` and `Join` handler
modules.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.LeafNodeArgs`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.leafNodeProg`: `leaf` node handler.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.IntroNodeArgs`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.introNodeProg`: `introduce` node handler.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.leafNodeProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.leafNodeProg_realizes`: correctness and realization
  of `leafNodeProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.introNodeProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.introNodeProg_realizes`: correctness and realization
  of `introNodeProg`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open SimpleGraph
open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! #### 1. Leaf node handler (`leafNodeProg`) -/

/-- Register arguments for the `leaf` node handler `leafNodeProg`. -/
structure LeafNodeArgs where
  /-- Base address of the serialized constraint-table array. -/
  consRawPtr : ℕ
  /-- Number of serialized constraint tables. -/
  numCons : ℕ
  /-- Base address of the 4-word destination descriptor slot. -/
  dCur : ℕ

/-- Tuple equivalence encoding `LeafNodeArgs` into Word-RAM registers. -/
@[expose] def LeafNodeArgs.equiv : LeafNodeArgs ≃ (ℕ × ℕ) × ℕ where
  toFun a := ((a.consRawPtr, a.numCons), a.dCur)
  invFun := fun ((cp, nc), dc) => ⟨cp, nc, dc⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding LeafNodeArgs := .ofEquiv LeafNodeArgs.equiv

/-- Allocate and populate the 1-entry DP table and descriptor for a `leaf` node. -/
def leafNodeProg (a : LeafNodeArgs) : Memory.Prog Unit := do
  let ok ← checkLeafConstraintsProg (a.consRawPtr, a.numCons)
  let tblPtr ← Memory.allocDirty 1
  Memory.write tblPtr ok
  writeDescProg ⟨a.dCur, tblPtr, 0, tblPtr, 1⟩

/-- Memory validity, framing, `NodeDescAt`, and cost bound for `leafNodeProg`. -/
theorem leafNodeProg_spec {w q F_lo : ℕ} (counting : Bool) (hq : 0 < q)
    (a : LeafNodeArgs) {cs : List (ConstraintTable q)} {vars : List ℕ} {s : Memory.State}
    (hcs : HoldsIn a.consRawPtr (cs.flatMap ConstraintTable.encode) s)
    (hcs_len : cs.length = a.numCons)
    (hdCur : a.dCur + 4 ≤ F_lo)
    (hFlo : F_lo ≤ s.frontier)
    (hfit_fr1 : Fits w (s.frontier + 1)) :
    let sEnd := (Memory.spec 0).clientState s (leafNodeProg a)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (leafNodeProg a)) ∧
    sEnd.frontier ≤ s.frontier + 1 ∧
    FrameOutsideRange a.dCur (a.dCur + 4) s sEnd ∧
    NodeDescAt F_lo counting q cs vars .leaf a.dCur sEnd ∧
    memoryCost (leafNodeProg a) s ≤ 6 + 3 * a.numCons := by
  obtain ⟨hv_cl, hst_cl, hr_cl, hc_cl⟩ :=
    checkLeafConstraintsProg_spec (w := w) hq (a.consRawPtr, a.numCons) hcs hcs_len
  dsimp only at hr_cl hc_cl
  let okVal := if cs.all fun ct => !decide (ct.scope = []) || ct.eval (fun _ => 0) then 1 else 0
  have hok_fit : Fits w okVal := by
    dsimp only [okVal]
    split_ifs
    · exact hfit_fr1.of_le (by omega)
    · exact fits_zero w
  let s_a := (Memory.spec 0).clientState s (Memory.allocDirty 1)
  have ha_fr : s_a.frontier = s.frontier + 1 := rfl
  have hp_a : PreservesBelow s.frontier s s_a := preservesBelow_allocDirty s 1
  have hv_a : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty 1)) :=
    validHistory_allocDirty hfit_fr1
  let s_w : Memory.State := ⟨Function.update s_a.mem s.frontier okVal, s_a.frontier⟩
  have hlt_w : s.frontier < s_a.frontier := by rw [ha_fr]; omega
  have hp_w : PreservesBelow s.frontier s_a s_w := preservesBelow_write le_rfl hlt_w
  have htbl_w : HoldsIn s.frontier [okVal] s_w := by
    have h0 : HoldsIn s.frontier [] s_a := HoldsIn.nil (by rw [ha_fr]; omega)
    simpa only [List.nil_append, List.length_nil, Nat.add_zero] using
      holdsIn_append_one h0 (by rw [ha_fr]; simp)
  have hd_w : a.dCur + 4 ≤ s_w.frontier := by dsimp only [s_w]; rw [ha_fr]; omega
  have hfit_ptr : Fits w s.frontier := hfit_fr1.of_le (by omega)
  have hfit_1 : Fits w 1 := hfit_fr1.of_le (by omega)
  obtain ⟨hv_wd, hfr_wd, hframe_wd, hm0, hm1, hm2, hm3, hc_wd⟩ :=
    writeDescProg_spec (w := w) ⟨a.dCur, s.frontier, 0, s.frontier, 1⟩
      hd_w hfit_ptr (fits_zero w) hfit_ptr hfit_1
  dsimp only at hm0 hm1 hm2 hm3
  let sEnd :=
    (Memory.spec 0).clientState s_w (writeDescProg ⟨a.dCur, s.frontier, 0, s.frontier, 1⟩)
  have hsEnd_eq : (Memory.spec 0).clientState s (leafNodeProg a) = sEnd := by
    unfold leafNodeProg
    rw [StateTransitionSpec.clientState_bind, hst_cl, hr_cl,
      StateTransitionSpec.clientState_bind]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold leafNodeProg
    refine validHistory_bind_step hv_cl ?_
    rw [hst_cl, hr_cl]
    refine validHistory_bind_step hv_a ?_
    exact validHistory_write_bind hlt_w hok_fit hv_wd
  · rw [hsEnd_eq, hfr_wd]
    exact le_rfl
  · rw [hsEnd_eq]
    exact (FrameOutsideRange.of_preservesBelow a.dCur (a.dCur + 4) (hp_a.trans hp_w)).trans
      hframe_wd
  · rw [hsEnd_eq]
    refine ⟨hdCur, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm0]; exact hFlo
    · rw [hm1]; rfl
    · rw [hm0]; exact HoldsIn.nil (by rw [hfr_wd]; dsimp only [s_w]; rw [ha_fr]; omega)
    · rw [hm2]; exact hFlo
    · rw [hm3]; simp [bagList]
    · rw [hm2]
      have htbl_eq : [okVal] = dpInstTree counting q cs vars .leaf := rfl
      rw [← htbl_eq]
      exact htbl_w.frame_outsideRange (.inr (le_trans hdCur hFlo)) hframe_wd
  · unfold leafNodeProg
    rw [memoryCost_bind', hst_cl, hr_cl, memoryCost_bind', memoryCost_allocDirty]
    change _ + (1 + memoryCost (Memory.write s.frontier okVal >>= _) s_a) ≤ _
    rw [memoryCost_bind', memoryCost_write]
    change _ + (1 + (1 +
      memoryCost (writeDescProg ⟨a.dCur, s.frontier, 0, s.frontier, 1⟩) s_w)) ≤ _
    omega

/-- Exact-basis Word-RAM realization certificate for `leafNodeProg`. -/
theorem leafNodeProg_realizes :
    Realizes .exact leafNodeProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        Fits w 2 ∧
        Fits w (a.dCur + 3) ∧
        ∃ (q : ℕ) (cs : List (ConstraintTable q)),
          0 < q ∧
          cs.length = a.numCons ∧
          HoldsIn a.consRawPtr (cs.flatMap ConstraintTable.encode) s ∧
          Fits w (a.consRawPtr + (cs.flatMap ConstraintTable.encode).length))
      (fun _ _ => 0) := by
  unfold leafNodeProg
  realize [checkLeafConstraintsProg_realizes, writeDescProg_realizes]
  · exact h.1
  · obtain ⟨_, _, q, cs, hq, hlen, hcs, hend⟩ := h
    exact ⟨q, cs, hq, hlen, hcs, hend⟩
  · exact h.1.of_le (by decide)
  · exact h.2.1

/-! #### 2. Introduce node handler (`introFillProg` & `introNodeProg`) -/

private structure IntroFillArgs where
  q : ℕ
  v : ℕ
  bagPtr : ℕ
  bagLen : ℕ
  consRawPtr : ℕ
  numCons : ℕ
  cTblPtr : ℕ
  tblPtr : ℕ
  tblLen : ℕ

private def IntroFillArgs.equiv :
    IntroFillArgs ≃ (((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a :=
    ((((((((a.q, a.v), a.bagPtr), a.bagLen), a.consRawPtr), a.numCons), a.cTblPtr), a.tblPtr),
      a.tblLen)
  invFun := fun ((((((((q, v), bp), bl), cp), nc), ctp), tp), tl) =>
    ⟨q, v, bp, bl, cp, nc, ctp, tp, tl⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding IntroFillArgs := .ofEquiv IntroFillArgs.equiv

private def introFillStep (p : IntroFillArgs × ℕ) : Memory.Prog ℕ := do
  let a := p.1
  let m := p.2
  let cVal ← Memory.read (a.cTblPtr + m / a.q)
  let ok ← checkIntroConstraintsProg ⟨a.q, a.v, a.bagPtr, a.bagLen, m, a.consRawPtr, a.numCons⟩
  let val := if ok = 1 then cVal else 0
  Memory.write (a.tblPtr + m) val
  pure (m + 1)

private def introFillProg (a : IntroFillArgs) : Memory.Prog Unit := do
  let _ ← iterate introFillStep a a.tblLen 0
  pure ()

private theorem introFillStep_eval (a : IntroFillArgs) (m : ℕ) (t : Memory.State) :
    let ok := (Memory.spec 0).clientResult t
      (checkIntroConstraintsProg ⟨a.q, a.v, a.bagPtr, a.bagLen, m, a.consRawPtr, a.numCons⟩)
    let cVal := t.mem (a.cTblPtr + m / a.q)
    let val := if ok = 1 then cVal else 0
    (Memory.spec 0).clientState t (introFillStep (a, m)) =
      ⟨Function.update t.mem (a.tblPtr + m) val, t.frontier⟩ ∧
    (Memory.spec 0).clientResult t (introFillStep (a, m)) = m + 1 := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold introFillStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    checkIntroConstraintsProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
  exact ⟨rfl, rfl⟩

private theorem introFillProg_spec {w : ℕ} (counting : Bool) (a : IntroFillArgs)
    (hq : 0 < a.q) {child : NiceTree ℕ} {cs : List (ConstraintTable a.q)} {vars : List ℕ}
    {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hLB : HoldsIn a.bagPtr (a.v :: bagList child) s)
    (hLB_len : (a.v :: bagList child).length = a.bagLen)
    (hLB_hi : a.bagPtr + a.bagLen ≤ a.tblPtr)
    (hcs : HoldsIn a.consRawPtr (cs.flatMap ConstraintTable.encode) s)
    (hcs_len : cs.length = a.numCons)
    (hcs_hi : a.consRawPtr + (cs.flatMap ConstraintTable.encode).length ≤ a.tblPtr)
    (hcTbl : HoldsIn a.cTblPtr (dpInstTree counting a.q cs vars child) s)
    (hcTbl_hi : a.cTblPtr + a.q ^ (bagList child).length ≤ a.tblPtr)
    (htblLen : a.tblLen = a.q ^ a.bagLen)
    (htbl_hi : a.tblPtr + a.tblLen ≤ s.frontier) :
    let targetTbl := dpInstTree counting a.q cs vars (.introduce a.v child)
    let s₁ := (Memory.spec 0).clientState s (introFillProg a)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (introFillProg a)) ∧
    s₁.frontier = s.frontier ∧
    PreservesBelow a.tblPtr s s₁ ∧
    HoldsIn a.tblPtr targetTbl s₁ ∧
    memoryCost (introFillProg a) s ≤
      a.tblLen *
        (2 + 3 * a.numCons +
          (cs.map fun ct => ct.scope.length).sum * (2 * a.bagLen + 3)) := by
  let targetTbl := dpInstTree counting a.q cs vars (.introduce a.v child)
  have htarget_len : targetTbl.length = a.tblLen := by
    simp [targetTbl, bagList, hLB_len, htblLen]
  let stepCost :=
    2 + 3 * a.numCons + (cs.map fun ct => ct.scope.length).sum * (2 * a.bagLen + 3)
  refine tableFillProg_spec introFillStep a a.tblPtr a.tblLen stepCost targetTbl s
    (Memory.WellFormed w) hwf htarget_len htbl_hi fun k t hk_le hwf_t hfr_t hp_t _ => ?_
  let m := a.tblLen - (k + 1)
  have hm_lt : m < a.tblLen := by omega
  have hm_pow : a.tblLen = a.q * a.q ^ (bagList child).length := by
    rw [htblLen, ← hLB_len, List.length_cons, Nat.pow_succ, Nat.mul_comm]
  have hdiv_lt : m / a.q < a.q ^ (bagList child).length := by
    rw [Nat.div_lt_iff_lt_mul hq, Nat.mul_comm]
    omega
  have hcTbl_t : HoldsIn a.cTblPtr (dpInstTree counting a.q cs vars child) t :=
    hcTbl.mono (F := a.tblPtr) (by simpa using hcTbl_hi) hp_t
  have hLB_t : HoldsIn a.bagPtr (a.v :: bagList child) t :=
    hLB.mono (F := a.tblPtr) (by rw [hLB_len]; exact hLB_hi) hp_t
  have hcs_t : HoldsIn a.consRawPtr (cs.flatMap ConstraintTable.encode) t :=
    hcs.mono (F := a.tblPtr) hcs_hi hp_t
  obtain ⟨hv_ci, hst_ci, hr_ci, hc_ci⟩ :=
    checkIntroConstraintsProg_spec (w := w)
      ⟨a.q, a.v, a.bagPtr, a.bagLen, m, a.consRawPtr, a.numCons⟩ hq
      hLB_t hLB_len hcs_t hcs_len
  dsimp only at hr_ci hc_ci
  have hc_len : (dpInstTree counting a.q cs vars child).length = a.q ^ (bagList child).length :=
    length_dpInstTree _ _ _ _ _
  have hm_cval : t.mem (a.cTblPtr + m / a.q) =
      (dpInstTree counting a.q cs vars child).getD (m / a.q) 0 := by
    rw [hcTbl_t.get (m / a.q) (by rw [hc_len]; exact hdiv_lt), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hc_len]; exact hdiv_lt), Option.getD_some]
  have hc_addr_lt : a.cTblPtr + m / a.q < t.frontier := by rw [hfr_t]; omega
  have hdst_addr_lt : a.tblPtr + m < t.frontier := by rw [hfr_t]; omega
  have hcval_fit : Fits w (t.mem (a.cTblPtr + m / a.q)) := hwf_t.mem_fits _
  obtain ⟨hst_ev, hres_ev⟩ := introFillStep_eval a m t
  let entryVal := targetTbl[m]'(by rw [htarget_len]; exact hm_lt)
  have hval_eq :
      (if (Memory.spec 0).clientResult t
          (checkIntroConstraintsProg
            ⟨a.q, a.v, a.bagPtr, a.bagLen, m, a.consRawPtr, a.numCons⟩) =
            1 then t.mem (a.cTblPtr + m / a.q) else 0) = entryVal := by
    rw [hr_ci, hm_cval]
    simp only [entryVal, targetTbl, dpInstTree, List.getElem_ofFn]
    cases cs.all fun ct =>
      !(decide (ct.scope.toFinset ⊆ (a.v :: bagList child).toFinset) &&
        decide (a.v ∈ ct.scope)) ||
        ct.eval (ofRadix a.q (a.v :: bagList child) m) <;> rfl
  have hst_t₁ : (Memory.spec 0).clientState t (introFillStep (a, m)) =
      ⟨Function.update t.mem (a.tblPtr + m) entryVal, t.frontier⟩ := by
    rw [hst_ev, hval_eq]
  have hv_step : (Memory.spec w).ValidHistory t
      ((Memory.spec w).clientHistory t (introFillStep (a, m))) := by
    unfold introFillStep
    dsimp only
    refine validHistory_read_bind hc_addr_lt ?_
    refine validHistory_bind_step hv_ci ?_
    rw [hst_ci]
    refine validHistory_write_bind hdst_addr_lt ?_ (validHistory_pure w _ _)
    split_ifs
    · exact hcval_fit
    · exact fits_zero w
  have hc_step : memoryCost (introFillStep (a, m)) t ≤ stepCost := by
    have hr_s (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
    unfold introFillStep
    dsimp only
    rw [memoryCost_bind', memoryCost_read, hr_s, memoryCost_bind', hst_ci,
      memoryCost_bind', memoryCost_write, memoryCost_pure]
    dsimp only [stepCost]
    omega
  exact ⟨hv_step, hst_t₁, hres_ev, hst_t₁ ▸ wellFormed_clientState hwf_t hv_step, hc_step⟩

private theorem introFillProg_realizes :
    Realizes .exact introFillProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        0 < a.q ∧ Fits w 2 ∧ Fits w a.q ∧
        Fits w (a.bagPtr + a.bagLen) ∧
        Fits w (a.cTblPtr + a.tblLen) ∧
        Fits w (a.tblPtr + a.tblLen) ∧
        ∃ cs : List (ConstraintTable a.q),
          cs.length = a.numCons ∧
          a.consRawPtr + (cs.flatMap ConstraintTable.encode).length ≤ a.tblPtr ∧
          HoldsIn a.consRawPtr (cs.flatMap ConstraintTable.encode) s ∧
          Fits w (a.consRawPtr + (cs.flatMap ConstraintTable.encode).length))
      (fun _ _ => 0) := by
  unfold introFillProg
  realize [checkIntroConstraintsProg_realizes]
  obtain ⟨hq_pos, h2, hfit_q, hfit_bag, hfit_cTbl, hfit_tbl,
    cs, hcs_len, hcs_hi, hcs_h, hfit_cs⟩ := h
  have h1 : Fits w 1 := h2.of_le (by decide)
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (m : ℕ) (t : Memory.State) =>
      j ≤ d.tblLen ∧ m + j = d.tblLen ∧
      HoldsIn d.consRawPtr (cs.flatMap ConstraintTable.encode) t)
    (fun j m t ⟨hj_le, hm_eq, hcs_t⟩ => ?_)
    ⟨le_rfl, Nat.zero_add _, hcs_h⟩
  have hm_lt : m < d.tblLen := by omega
  have hfit_m : Fits w m := hfit_tbl.of_le (by omega)
  have hfit_m1 : Fits w (m + 1) := hfit_tbl.of_le (by omega)
  have hq_ne : d.q ≠ 0 := by omega
  have hdiv_le : m / d.q ≤ m := Nat.div_le_self m d.q
  have hfit_caddr : Fits w (d.cTblPtr + m / d.q) := hfit_cTbl.of_le (by omega)
  have hfit_taddr : Fits w (d.tblPtr + m) := hfit_tbl.of_le (by omega)
  have hci_safe :
      0 < d.q ∧ Fits w 2 ∧ Fits w d.q ∧ Fits w m ∧ Fits w (d.bagPtr + d.bagLen) ∧
        ∃ cs : List (ConstraintTable d.q),
          cs.length = d.numCons ∧
          HoldsIn d.consRawPtr (cs.flatMap ConstraintTable.encode) t ∧
          Fits w (d.consRawPtr + (cs.flatMap ConstraintTable.encode).length) :=
    ⟨hq_pos, h2, hfit_q, hfit_m, hfit_bag, cs, hcs_len, hcs_t, hfit_cs⟩
  obtain ⟨hst_ev, hres_ev⟩ := introFillStep_eval d m t
  refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_⟩
  · dsimp only [introFillStep]
    refine ⟨⟨hq_ne, hfit_caddr⟩, hci_safe, ⟨hfit_taddr, h1, ?_⟩, hfit_m1⟩
    split_ifs
  · rw [hres_ev]; omega
  · rw [hst_ev]
    exact holdsIn_write_outside hcs_t (.inr (by omega))

private structure CopyBagState where
  srcCur : ℕ
  dstCur : ℕ

private def CopyBagState.equiv : CopyBagState ≃ ℕ × ℕ where
  toFun s := (s.srcCur, s.dstCur)
  invFun := fun (srcCur, dstCur) => ⟨srcCur, dstCur⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding CopyBagState := .ofEquiv CopyBagState.equiv

private structure BagCopyArgs where
  src : ℕ
  dst : ℕ
  len : ℕ

private def BagCopyArgs.equiv : BagCopyArgs ≃ (ℕ × ℕ) × ℕ where
  toFun a := ((a.src, a.dst), a.len)
  invFun := fun ((src, dst), len) => ⟨src, dst, len⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding BagCopyArgs := .ofEquiv BagCopyArgs.equiv

private def copyBagStep (env : Unit × CopyBagState) : Memory.Prog CopyBagState := do
  let v ← Memory.read env.2.srcCur
  Memory.write env.2.dstCur v
  pure ⟨env.2.srcCur + 1, env.2.dstCur + 1⟩

private def copyBagProg (args : BagCopyArgs) : Memory.Prog Unit := do
  let _ ← iterate copyBagStep () args.len ⟨args.src, args.dst⟩
  pure ()

private theorem copyBagProg_spec {w : ℕ} (args : BagCopyArgs) {xs : List ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hxs : HoldsIn args.src xs s) (hlen : xs.length = args.len)
    (hdisj : args.src + args.len ≤ args.dst) (hdst : args.dst + args.len ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (copyBagProg args)) ∧
    ((Memory.spec 0).clientState s (copyBagProg args)).frontier = s.frontier ∧
    PreservesBelow args.dst s ((Memory.spec 0).clientState s (copyBagProg args)) ∧
    HoldsIn args.dst xs ((Memory.spec 0).clientState s (copyBagProg args)) ∧
    memoryCost (copyBagProg args) s ≤ 2 * args.len := by
  have hcost : memoryCost (copyBagProg args) s ≤ 2 * args.len := by
    unfold copyBagProg
    rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
    have hle := memoryCost_iterate_le_of copyBagStep 2 () (fun _ _ => le_rfl)
      args.len ⟨args.src, args.dst⟩ s
    omega
  suffices ∀ ys src dst st,
      Memory.WellFormed w st →
      HoldsIn src ys st →
      src + ys.length ≤ dst →
      dst + ys.length ≤ st.frontier →
      (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (iterate copyBagStep () ys.length ⟨src, dst⟩)) ∧
      ((Memory.spec 0).clientState st
        (iterate copyBagStep () ys.length ⟨src, dst⟩)).frontier = st.frontier ∧
      PreservesBelow dst st
        ((Memory.spec 0).clientState st (iterate copyBagStep () ys.length ⟨src, dst⟩)) ∧
      HoldsIn dst ys
        ((Memory.spec 0).clientState st (iterate copyBagStep () ys.length ⟨src, dst⟩)) by
    have hrun := this xs args.src args.dst s hwf hxs (by omega) (by omega)
    rw [hlen] at hrun
    unfold copyBagProg
    rw [StateTransitionSpec.clientState_bind]
    exact ⟨validHistory_bind_step hrun.1 (validHistory_pure w _ ()), hrun.2.1, hrun.2.2.1,
      hrun.2.2.2, hcost⟩
  intro ys
  induction ys with
  | nil =>
    intro src dst st _ _ _ hdst_st
    simp only [List.length_nil, Nat.add_zero] at hdst_st ⊢
    exact ⟨validHistory_pure w st _, rfl, PreservesBelow.refl hdst_st, HoldsIn.nil hdst_st⟩
  | cons u rest ih =>
    intro src dst st hwf_st hsrc_st hdisj_st hdst_st
    obtain ⟨hsrc_b, hmem_u, hrest_src⟩ := HoldsIn.cons_iff.1 hsrc_st
    simp only [List.length_cons] at hdisj_st hdst_st ⊢
    let st₁ : Memory.State := ⟨Function.update st.mem dst (st.mem src), st.frontier⟩
    have hv_step : (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (copyBagStep ((), ⟨src, dst⟩))) :=
      validHistory_read_bind (show src < st.frontier by omega) (validHistory_write_bind
        (show dst < st.frontier by omega) (hwf_st.mem_fits src) (validHistory_pure w st₁ _))
    have hp₁ : PreservesBelow dst st st₁ := preservesBelow_write le_rfl (by omega)
    have hst₁ : (Memory.spec 0).clientState st (copyBagStep ((), ⟨src, dst⟩)) = st₁ := rfl
    have hres₁ : (Memory.spec 0).clientResult st (copyBagStep ((), ⟨src, dst⟩)) =
        ⟨src + 1, dst + 1⟩ := rfl
    have hiter : iterate copyBagStep () (rest.length + 1) ⟨src, dst⟩ =
        copyBagStep ((), ⟨src, dst⟩) >>= iterate copyBagStep () rest.length := rfl
    obtain ⟨hv_rest, hfr_rest, hp_rest, hhold_rest⟩ :=
      ih (src + 1) (dst + 1) st₁ (hst₁ ▸ wellFormed_clientState hwf_st hv_step)
        (hrest_src.mono (by omega) hp₁) (by omega) (by dsimp only [st₁]; omega)
    rw [hiter, StateTransitionSpec.clientState_bind, hst₁, hres₁]
    refine ⟨validHistory_bind_step hv_step hv_rest, hfr_rest,
      hp₁.trans (hp_rest.mono_bound (by omega)),
      HoldsIn.cons_iff.2 ⟨by rw [hfr_rest]; dsimp only [st₁]; omega, ?_, hhold_rest⟩⟩
    rw [hp_rest.2.2 dst (by omega)]
    simp only [st₁, Function.update_self, hmem_u]

private theorem copyBagProg_realizes :
    Realizes .exact copyBagProg WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w 1 ∧ Fits w (args.src + args.len) ∧ Fits w (args.dst + args.len))
      (fun _ _ => 0) := by
  unfold copyBagProg
  realize
  obtain ⟨_, hsrc_fit, hdst_fit⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : CopyBagState) (_ : Memory.State) =>
      st.srcCur + j = d.src + d.len ∧ st.dstCur + j = d.dst + d.len)
    (fun j st _ ⟨hsrc, hdst⟩ => ?_)
    ⟨rfl, rfl⟩
  dsimp only [copyBagStep]
  refine ⟨⟨hsrc_fit.of_le (by omega), hdst_fit.of_le (by omega)⟩, ?_, ?_⟩
  · change (st.srcCur + 1) + j = d.src + d.len
    omega
  · change (st.dstCur + 1) + j = d.dst + d.len
    omega

/-- Register arguments for the `introduce` node handler `introNodeProg`. -/
structure IntroNodeArgs where
  /-- Domain size `q`. -/
  q : ℕ
  /-- Introduced variable label `v`. -/
  v : ℕ
  /-- Base address of the serialized constraint-table array. -/
  consRawPtr : ℕ
  /-- Number of serialized constraint tables. -/
  numCons : ℕ
  /-- Base address of the child node's 4-word descriptor slot. -/
  dChild : ℕ
  /-- Base address of the current node's 4-word descriptor slot. -/
  dCur : ℕ

/-- Tuple equivalence encoding `IntroNodeArgs` into Word-RAM registers. -/
@[expose] def IntroNodeArgs.equiv :
    IntroNodeArgs ≃ ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := (((((a.q, a.v), a.consRawPtr), a.numCons), a.dChild), a.dCur)
  invFun := fun (((((q, v), cp), nc), dch), dc) => ⟨q, v, cp, nc, dch, dc⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding IntroNodeArgs := .ofEquiv IntroNodeArgs.equiv

/-- Materialize the bag `v :: childBag`, fill the expanded DP table, and write the descriptor
for an `introduce` node. -/
def introNodeProg (a : IntroNodeArgs) : Memory.Prog Unit := do
  let cBagPtr ← Memory.read a.dChild
  let cBagLen ← Memory.read (a.dChild + 1)
  let cTblPtr ← Memory.read (a.dChild + 2)
  let cTblLen ← Memory.read (a.dChild + 3)
  let bagLen := cBagLen + 1
  let bagPtr ← Memory.allocDirty bagLen
  Memory.write bagPtr a.v
  let _ ← copyBagProg ⟨cBagPtr, bagPtr + 1, cBagLen⟩
  let tblLen := a.q * cTblLen
  let tblPtr ← Memory.allocDirty tblLen
  let _ ← introFillProg
    ⟨a.q, a.v, bagPtr, bagLen, a.consRawPtr, a.numCons, cTblPtr, tblPtr, tblLen⟩
  writeDescProg ⟨a.dCur, bagPtr, bagLen, tblPtr, tblLen⟩

/-- Memory validity, framing, `NodeDescAt`, and cost bound for `introNodeProg`. -/
theorem introNodeProg_spec {w F_lo : ℕ} (counting : Bool) (a : IntroNodeArgs)
    (hq : 0 < a.q) {child : NiceTree ℕ} {cs : List (ConstraintTable a.q)} {vars : List ℕ}
    {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hfit_v : Fits w a.v)
    (hcs : HoldsIn a.consRawPtr (cs.flatMap ConstraintTable.encode) s)
    (hcs_len : cs.length = a.numCons)
    (hcs_hi : a.consRawPtr + (cs.flatMap ConstraintTable.encode).length ≤ F_lo)
    (hchild : NodeDescAt F_lo counting a.q cs vars child a.dChild s)
    (hdCur : a.dCur + 4 ≤ F_lo)
    (hFlo : F_lo ≤ s.frontier)
    (hfit_peak : Fits w (s.frontier + ((a.v :: bagList child).length +
      a.q ^ (a.v :: bagList child).length))) :
    let sEnd := (Memory.spec 0).clientState s (introNodeProg a)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (introNodeProg a)) ∧
    sEnd.frontier ≤
      s.frontier + ((a.v :: bagList child).length + a.q ^ (a.v :: bagList child).length) ∧
    FrameOutsideRange a.dCur (a.dCur + 4) s sEnd ∧
    NodeDescAt F_lo counting a.q cs vars (.introduce a.v child) a.dCur sEnd ∧
    memoryCost (introNodeProg a) s ≤
      11 + 2 * (bagList child).length +
        a.q ^ (a.v :: bagList child).length *
          (2 + 3 * a.numCons +
            (cs.map fun ct => ct.scope.length).sum *
              (2 * (a.v :: bagList child).length + 3)) := by
  have hd_ch := hchild.desc_hi
  have hm_cbLen : s.mem (a.dChild + 1) = (bagList child).length := hchild.bag_len
  have hm_ctLen : s.mem (a.dChild + 3) = a.q ^ (bagList child).length := hchild.tbl_len
  let cBagPtr := s.mem a.dChild
  let cBagLen := (bagList child).length
  let cTblPtr := s.mem (a.dChild + 2)
  let cTblLen := a.q ^ cBagLen
  let bagLen := cBagLen + 1
  have hbagLen_eq : (a.v :: bagList child).length = bagLen := rfl
  let tblLen := a.q * cTblLen
  have htblLen_eq : tblLen = a.q ^ bagLen := by
    dsimp only [tblLen, cTblLen, bagLen]
    rw [Nat.pow_succ, Nat.mul_comm]
  let bagPtr := s.frontier
  let s₁ := (Memory.spec 0).clientState s (Memory.allocDirty bagLen)
  have hs₁_fr : s₁.frontier = bagPtr + bagLen := rfl
  have hp₁ : PreservesBelow bagPtr s s₁ := preservesBelow_allocDirty s bagLen
  have hfit_fr₁ : Fits w (s.frontier + bagLen) :=
    hfit_peak.of_le (by rw [hbagLen_eq, ← htblLen_eq]; omega)
  have hv₁ : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty bagLen)) :=
    validHistory_allocDirty hfit_fr₁
  have hwf₁ : Memory.WellFormed w s₁ := wellFormed_clientState hwf hv₁
  let s₂ : Memory.State := ⟨Function.update s₁.mem bagPtr a.v, s₁.frontier⟩
  have hlt_bp : bagPtr < s₁.frontier := by rw [hs₁_fr]; dsimp only [bagLen]; omega
  have hp₂ : PreservesBelow bagPtr s₁ s₂ := preservesBelow_write le_rfl hlt_bp
  have hv₂ : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (Memory.write bagPtr a.v)) :=
    validHistory_write hlt_bp hfit_v
  have hwf₂ : Memory.WellFormed w s₂ := wellFormed_clientState hwf₁ hv₂
  have hcBag_s₂ : HoldsIn cBagPtr (bagList child) s₂ :=
    hchild.bag_holds.mono_frontier (hp₁.trans hp₂)
  obtain ⟨hv_cp, hfr_cp, hp_cp, hcp_holds, hc_cp⟩ :=
    copyBagProg_spec (w := w) ⟨cBagPtr, bagPtr + 1, cBagLen⟩ hwf₂ hcBag_s₂ rfl
      (by have := hchild.bag_holds.1; dsimp only [cBagPtr, cBagLen, bagPtr]; omega)
      (by dsimp only [s₂]; rw [hs₁_fr]; dsimp only [bagLen]; omega)
  let s₃ := (Memory.spec 0).clientState s₂ (copyBagProg ⟨cBagPtr, bagPtr + 1, cBagLen⟩)
  have hwf₃ : Memory.WellFormed w s₃ := wellFormed_clientState hwf₂ hv_cp
  have hs₃_fr : s₃.frontier = bagPtr + bagLen := by rw [hfr_cp]; exact hs₁_fr
  have hp_s_s₃ : PreservesBelow bagPtr s s₃ :=
    (hp₁.trans hp₂).trans (hp_cp.mono_bound (Nat.le_succ bagPtr))
  have hLB_s₃ : HoldsIn bagPtr (a.v :: bagList child) s₃ := by
    rw [HoldsIn.cons_iff]
    refine ⟨by rw [hs₃_fr]; dsimp only [bagLen, cBagLen]; omega, ?_, hcp_holds⟩
    rw [hp_cp.2.2 bagPtr (Nat.lt_succ_self bagPtr)]
    exact Function.update_self _ _ _
  let tblPtr := s₃.frontier
  let s₄ := (Memory.spec 0).clientState s₃ (Memory.allocDirty tblLen)
  have hs₄_fr : s₄.frontier = tblPtr + tblLen := rfl
  have hp₄ : PreservesBelow tblPtr s₃ s₄ := preservesBelow_allocDirty s₃ tblLen
  have hfit_fr₄ : Fits w (s₃.frontier + tblLen) := by
    rw [hs₃_fr]
    exact hfit_peak.of_le (by rw [hbagLen_eq, ← htblLen_eq]; dsimp only [bagPtr]; omega)
  have hv₄ : (Memory.spec w).ValidHistory s₃
      ((Memory.spec w).clientHistory s₃ (Memory.allocDirty tblLen)) :=
    validHistory_allocDirty hfit_fr₄
  have hwf₄ : Memory.WellFormed w s₄ := wellFormed_clientState hwf₃ hv₄
  have hp_s_s₄ : PreservesBelow bagPtr s s₄ :=
    hp_s_s₃.trans (hp₄.mono_bound (by dsimp only [tblPtr]; rw [hs₃_fr]; omega))
  let fillArgs : IntroFillArgs :=
    ⟨a.q, a.v, bagPtr, bagLen, a.consRawPtr, a.numCons, cTblPtr, tblPtr, tblLen⟩
  obtain ⟨hv_fill, hfr_fill, hp_fill, htbl_fill, hc_fill⟩ :=
    introFillProg_spec (w := w) counting fillArgs hq hwf₄
      (hLB_s₃.mono_frontier hp₄) hbagLen_eq
      (by dsimp only [fillArgs, tblPtr]; rw [hs₃_fr])
      (hcs.mono_frontier hp_s_s₄) hcs_len
      (by dsimp only [fillArgs, tblPtr]; rw [hs₃_fr]; dsimp only [bagPtr]; omega)
      (hchild.tbl_holds.mono_frontier hp_s_s₄)
      (by have := hchild.tbl_holds.1; rw [length_dpInstTree] at this
          dsimp only [fillArgs, cTblPtr, tblPtr]; rw [hs₃_fr]; dsimp only [bagPtr]; omega)
      htblLen_eq
      (by rw [hs₄_fr])
  let s₅ := (Memory.spec 0).clientState s₄ (introFillProg fillArgs)
  have hs₅_fr : s₅.frontier = tblPtr + tblLen := by rw [hfr_fill, hs₄_fr]
  have hp_s_s₅ : PreservesBelow bagPtr s s₅ :=
    hp_s_s₄.trans (hp_fill.mono_bound (by dsimp only [fillArgs, tblPtr]; rw [hs₃_fr]; omega))
  have hLB_s₅ : HoldsIn bagPtr (a.v :: bagList child) s₅ :=
    (hLB_s₃.mono_frontier hp₄).mono (F := tblPtr)
      (by rw [hbagLen_eq, ← hs₃_fr]) hp_fill
  have hd_s₅ : a.dCur + 4 ≤ s₅.frontier := by
    rw [hs₅_fr]; dsimp only [tblPtr]; rw [hs₃_fr]; dsimp only [bagPtr]; omega
  have hfit_bt : Fits w (bagPtr + bagLen + tblLen) := by rwa [hs₃_fr] at hfit_fr₄
  obtain ⟨hv_wd, hfr_wd, hframe_wd, hm0, hm1, hm2, hm3, hc_wd⟩ :=
    writeDescProg_spec (w := w) ⟨a.dCur, bagPtr, bagLen, tblPtr, tblLen⟩ hd_s₅
      (hfit_bt.of_le (by dsimp only [bagPtr, bagLen, tblLen]; omega))
      (hfit_bt.of_le (by dsimp only [bagPtr, bagLen, tblLen]; omega))
      (hfit_bt.of_le (by dsimp only [tblPtr]; rw [hs₃_fr]; omega))
      (hfit_bt.of_le (by dsimp only [bagPtr, bagLen, tblLen]; omega))
  dsimp only at hm0 hm1 hm2 hm3
  let sEnd := (Memory.spec 0).clientState s₅
    (writeDescProg ⟨a.dCur, bagPtr, bagLen, tblPtr, tblLen⟩)
  have ha1_s : (Memory.spec 0).clientState s (Memory.allocDirty bagLen) = s₁ := rfl
  have ha1_r : (Memory.spec 0).clientResult s (Memory.allocDirty bagLen) = bagPtr := rfl
  have hw_s : (Memory.spec 0).clientState s₁ (Memory.write bagPtr a.v) = s₂ := rfl
  have ha4_s : (Memory.spec 0).clientState s₃ (Memory.allocDirty tblLen) = s₄ := rfl
  have ha4_r : (Memory.spec 0).clientResult s₃ (Memory.allocDirty tblLen) = tblPtr := rfl
  have hsEnd_eq : (Memory.spec 0).clientState s (introNodeProg a) = sEnd := by
    unfold introNodeProg
    dsimp only
    iterate 4 rw [clientState_bind_read]
    rw [hm_cbLen, hm_ctLen]
    rw [StateTransitionSpec.clientState_bind, ha1_s, ha1_r,
      StateTransitionSpec.clientState_bind, hw_s,
      StateTransitionSpec.clientState_bind]
    change (Memory.spec 0).clientState s₃
      (Memory.allocDirty tblLen >>= fun tp =>
        introFillProg ⟨a.q, a.v, bagPtr, bagLen, a.consRawPtr, a.numCons, cTblPtr, tp, tblLen⟩ >>=
          fun _ => writeDescProg ⟨a.dCur, bagPtr, bagLen, tp, tblLen⟩) = sEnd
    rw [StateTransitionSpec.clientState_bind, ha4_s, ha4_r,
      StateTransitionSpec.clientState_bind]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold introNodeProg
    refine validHistory_read_bind (by omega) <| validHistory_read_bind (by omega) <|
      validHistory_read_bind (by omega) <| validHistory_read_bind (by omega) ?_
    rw [hm_cbLen, hm_ctLen]
    exact validHistory_bind_step hv₁ <| validHistory_bind_step hv₂ <|
      validHistory_bind_step hv_cp <| validHistory_bind_step hv₄ <|
        validHistory_bind_step hv_fill hv_wd
  · rw [hsEnd_eq, hfr_wd, hs₅_fr]
    dsimp only [tblPtr]
    rw [hs₃_fr, hbagLen_eq, ← htblLen_eq]
    dsimp only [bagPtr]
    omega
  · rw [hsEnd_eq]
    exact (FrameOutsideRange.of_preservesBelow a.dCur (a.dCur + 4) hp_s_s₅).trans hframe_wd
  · rw [hsEnd_eq]
    refine ⟨hdCur, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm0]; exact hFlo
    · rw [hm1]; rfl
    · rw [hm0]
      exact hLB_s₅.frame_outsideRange (.inr (le_trans hdCur hFlo)) hframe_wd
    · rw [hm2]; dsimp only [tblPtr]; rw [hs₃_fr]; dsimp only [bagPtr]; omega
    · rw [hm3]; exact htblLen_eq
    · rw [hm2]
      exact htbl_fill.frame_outsideRange
        (.inr (by dsimp only [fillArgs, tblPtr]; rw [hs₃_fr]; dsimp only [bagPtr]; omega))
        hframe_wd
  · have hcost_eq :
        a.q ^ (a.v :: bagList child).length *
          (2 + 3 * a.numCons +
            (cs.map fun ct => ct.scope.length).sum * (2 * (a.v :: bagList child).length + 3)) =
          tblLen *
            (2 + 3 * a.numCons + (cs.map fun ct => ct.scope.length).sum * (2 * bagLen + 3)) := by
      rw [htblLen_eq, hbagLen_eq]
    unfold introNodeProg
    dsimp only
    iterate 4 rw [memoryCost_bind', memoryCost_read, clientState_read, clientResult_read]
    rw [hm_cbLen, hm_ctLen, memoryCost_bind', memoryCost_allocDirty, ha1_s, ha1_r,
      memoryCost_bind', memoryCost_write, hw_s, memoryCost_bind']
    change 1 + (1 + (1 + (1 + (1 + (1 + (memoryCost (copyBagProg _) s₂ +
      memoryCost (Memory.allocDirty tblLen >>= _) s₃)))))) ≤ _
    rw [memoryCost_bind', memoryCost_allocDirty, ha4_s, ha4_r, memoryCost_bind']
    change 1 + (1 + (1 + (1 + (1 + (1 + (memoryCost (copyBagProg _) s₂ +
      (1 + (memoryCost (introFillProg fillArgs) s₄ +
        memoryCost (writeDescProg ⟨a.dCur, bagPtr, bagLen, tblPtr, tblLen⟩) s₅)))))))) ≤ _
    dsimp only [s₅, fillArgs, cBagPtr, cBagLen, cTblPtr, cTblLen, bagPtr, bagLen, tblPtr, tblLen]
      at hc_cp hc_fill hc_wd hcost_eq ⊢
    omega

/-- Exact-basis Word-RAM realization certificate for `introNodeProg`. -/
theorem introNodeProg_realizes :
    Realizes .exact introNodeProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        0 < a.q ∧ Fits w 3 ∧ Fits w a.q ∧ Fits w a.v ∧
        Fits w (a.dChild + 3) ∧ Fits w (a.dCur + 3) ∧
        ∃ (F_lo : ℕ) (counting : Bool) (child : NiceTree ℕ)
          (cs : List (ConstraintTable a.q)) (vars : List ℕ),
          Memory.WellFormed w s ∧
          cs.length = a.numCons ∧
          HoldsIn a.consRawPtr (cs.flatMap ConstraintTable.encode) s ∧
          a.consRawPtr + (cs.flatMap ConstraintTable.encode).length ≤ F_lo ∧
          NodeDescAt F_lo counting a.q cs vars child a.dChild s ∧
          F_lo ≤ s.frontier ∧
          Fits w (s.frontier + ((a.v :: bagList child).length +
            a.q ^ (a.v :: bagList child).length)))
      (fun _ _ => 0) := by
  unfold introNodeProg
  realize [copyBagProg_realizes, introFillProg_realizes, writeDescProg_realizes]
  all_goals
    obtain ⟨hq, h3, hfit_q, hfit_v, hdCh, hdCur, F_lo, counting, child, cs, vars, hwf, hcs_len,
      hcs_h, hcs_hi, hch, hFlo, hfit_peak⟩ := h
    have h1 : Fits w 1 := h3.of_le (by decide)
    have h2 : Fits w 2 := h3.of_le (by decide)
    try rw [hch.bag_len]
    try rw [hch.tbl_len]
    let bagLen := (bagList child).length + 1
    let tblLen := d.q * d.q ^ (bagList child).length
    have htblLen_eq : tblLen = d.q ^ (d.v :: bagList child).length := by
      dsimp only [tblLen]; simp [Nat.pow_succ, Nat.mul_comm]
    let s₁ := (Memory.spec 0).clientState s (Memory.allocDirty bagLen)
    have hp₁ : PreservesBelow s.frontier s s₁ := preservesBelow_allocDirty s bagLen
    have hv₁ : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (Memory.allocDirty bagLen)) :=
      validHistory_allocDirty
        (hfit_peak.of_le (by dsimp only [bagLen]; rw [List.length_cons]; omega))
    have hwf₁ : Memory.WellFormed w s₁ := wellFormed_clientState hwf hv₁
    let s₂ : Memory.State := ⟨Function.update s₁.mem s.frontier d.v, s₁.frontier⟩
    have hlt_bp : s.frontier < s₁.frontier := by
      change s.frontier < s.frontier + bagLen; dsimp only [bagLen]; omega
    have hp₂ : PreservesBelow s.frontier s₁ s₂ := preservesBelow_write le_rfl hlt_bp
    have hwf₂ : Memory.WellFormed w s₂ :=
      wellFormed_clientState hwf₁ (validHistory_write hlt_bp hfit_v)
    obtain ⟨_, hfr_cp, hp_cp, _, _⟩ :=
      copyBagProg_spec (w := w) ⟨s.mem d.dChild, s.frontier + 1, (bagList child).length⟩
        hwf₂ (hch.bag_holds.mono_frontier (hp₁.trans hp₂)) rfl
        (by have := hch.bag_holds.1; dsimp only; omega)
        (by dsimp only [s₂, s₁, bagLen]; change s.frontier + 1 + _ ≤ s.frontier + _; omega)
    let s₃ := (Memory.spec 0).clientState s₂
      (copyBagProg ⟨s.mem d.dChild, s.frontier + 1, (bagList child).length⟩)
    have hs₃_fr : s₃.frontier = s.frontier + bagLen := hfr_cp
    let s₄ := (Memory.spec 0).clientState s₃ (Memory.allocDirty tblLen)
    have hp₄ : PreservesBelow s₃.frontier s₃ s₄ := preservesBelow_allocDirty s₃ tblLen
    have hp_all : PreservesBelow s.frontier s s₄ :=
      ((hp₁.trans hp₂).trans (hp_cp.mono_bound (Nat.le_succ s.frontier))).trans
        (hp₄.mono_bound (by rw [hs₃_fr]; omega))
    have hc_bag := hch.bag_holds.1
    have hc_tbl := hch.tbl_holds.1
    rw [length_dpInstTree] at hc_tbl
    have hpow_ge : d.q ^ (bagList child).length ≤ tblLen := by
      rw [htblLen_eq]; exact Nat.pow_le_pow_right hq (Nat.le_succ _)
    have hf_ch1 : Fits w (d.dChild + 1) := hdCh.of_le (by omega)
    have hf_ch2 : Fits w (d.dChild + 2) := hdCh.of_le (by omega)
    have hf_bagLen : Fits w bagLen :=
      hfit_peak.of_le (by dsimp only [bagLen]; rw [List.length_cons]; omega)
    have hf_fr1 : Fits w (s.frontier + 1) :=
      hfit_peak.of_le (by rw [List.length_cons]; omega)
    have hf_csrc : Fits w (s.mem d.dChild + (bagList child).length) := hfit_peak.of_le (by omega)
    have hf_cdst : Fits w (s.frontier + 1 + (bagList child).length) :=
      hfit_peak.of_le (by rw [List.length_cons]; omega)
    have hf_tblLen : Fits w tblLen := hfit_peak.of_le (by rw [htblLen_eq]; omega)
    have hf_bagEnd : Fits w (s.frontier + bagLen) :=
      hfit_peak.of_le (by dsimp only [bagLen]; rw [List.length_cons]; omega)
    have hf_ctEnd : Fits w (s.mem (d.dChild + 2) + tblLen) :=
      hfit_peak.of_le (by rw [htblLen_eq] at *; omega)
    have hf_tEnd : Fits w (s₃.frontier + tblLen) :=
      hfit_peak.of_le
        (by rw [hs₃_fr, htblLen_eq]; dsimp only [bagLen]; rw [List.length_cons]; omega)
    have hexists_cs : ∃ cs : List (ConstraintTable d.q),
        cs.length = d.numCons ∧
        d.consRawPtr + (cs.flatMap ConstraintTable.encode).length ≤ s₃.frontier ∧
        HoldsIn d.consRawPtr (cs.flatMap ConstraintTable.encode) s₄ ∧
        Fits w (d.consRawPtr + (cs.flatMap ConstraintTable.encode).length) :=
      ⟨cs, hcs_len, by rw [hs₃_fr]; omega, hcs_h.mono_frontier hp_all, hfit_peak.of_le (by omega)⟩
    assumption

end Cslib.Algorithms.WordRAM.TreeDecomposition
