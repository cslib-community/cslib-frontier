/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.Memory
import CslibFrontier.Tactic.Realize

/-!
# Live Factor-Descriptor Partitioning (`partitionLive`)

Partitions the active array of 4-word factor descriptors into two freshly allocated descriptor
arrays: `bucket` (those whose scope contains `x`) and `rest` (all other live factors).

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.partitionLive`: bucket/rest descriptor splitter.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-- Arguments `(x, livePtr, liveLen)` for `partitionLive`. -/
structure PartitionArgs where
  /-- Field `x` of `PartitionArgs`. -/
  x : ℕ
  /-- Field `livePtr` of `PartitionArgs`. -/
  livePtr : ℕ
  /-- Field `liveLen` of `PartitionArgs`. -/
  liveLen : ℕ

/-- Product equivalence encoding `PartitionArgs` as words. -/
@[expose] def PartitionArgs.equiv : PartitionArgs ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.x, s.livePtr), s.liveLen)
  invFun := fun ((x, livePtr), liveLen) => ⟨x, livePtr, liveLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding PartitionArgs := .ofEquiv PartitionArgs.equiv

private structure PartitionState where
  curDesc : ℕ
  bDst : ℕ
  bCnt : ℕ
  rDst : ℕ
  rCnt : ℕ

private def PartitionState.equiv : PartitionState ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := ((((s.curDesc, s.bDst), s.bCnt), s.rDst), s.rCnt)
  invFun := fun ((((curDesc, bDst), bCnt), rDst), rCnt) => ⟨curDesc, bDst, bCnt, rDst, rCnt⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding PartitionState := .ofEquiv PartitionState.equiv

/-- Return record holding pointer/length pairs for bucket and rest factors. -/
structure PartitionRes where
  /-- Field `bucketPtr` of `PartitionRes`. -/
  bucketPtr : ℕ
  /-- Field `bucketLen` of `PartitionRes`. -/
  bucketLen : ℕ
  /-- Field `newLiveBuf` of `PartitionRes`. -/
  newLiveBuf : ℕ
  /-- Field `restLen` of `PartitionRes`. -/
  restLen : ℕ

/-- Product equivalence encoding `PartitionRes` as words. -/
@[expose] def PartitionRes.equiv : PartitionRes ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun s := (((s.bucketPtr, s.bucketLen), s.newLiveBuf), s.restLen)
  invFun := fun (((bucketPtr, bucketLen), newLiveBuf), restLen) =>
    ⟨bucketPtr, bucketLen, newLiveBuf, restLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding PartitionRes := .ofEquiv PartitionRes.equiv

private def partitionStep (p : ℕ × PartitionState) : Memory.Prog PartitionState :=
  Memory.read p.2.curDesc >>= fun scPtr =>
  Memory.read (p.2.curDesc + 1) >>= fun scLen =>
  Memory.read (p.2.curDesc + 2) >>= fun enPtr =>
  Memory.read (p.2.curDesc + 3) >>= fun enLen =>
  memScan ⟨p.1, scPtr, scLen⟩ >>= fun flag =>
  if flag = 1 then
    writeDesc ⟨p.2.bDst, scPtr, scLen, enPtr, enLen⟩ >>= fun _ =>
      pure ⟨p.2.curDesc + 4, p.2.bDst + 4, p.2.bCnt + 1, p.2.rDst, p.2.rCnt⟩
  else
    writeDesc ⟨p.2.rDst, scPtr, scLen, enPtr, enLen⟩ >>= fun _ =>
      pure ⟨p.2.curDesc + 4, p.2.bDst, p.2.bCnt, p.2.rDst + 4, p.2.rCnt + 1⟩

/-- Split the live descriptor array into bucket (containing `x`) and rest. -/
def partitionLive (args : PartitionArgs) : Memory.Prog PartitionRes :=
  Memory.allocDirty (4 * args.liveLen) >>= fun bucketPtr =>
  Memory.allocDirty (4 + 4 * args.liveLen) >>= fun newLiveBuf =>
  iterate partitionStep args.x args.liveLen
    ⟨args.livePtr, bucketPtr, 0, newLiveBuf + 4, 0⟩ >>= fun res =>
  pure ⟨bucketPtr, res.bCnt, newLiveBuf, res.rCnt⟩

theorem partitionLive_spec {w : ℕ} {args : PartitionArgs}
    {live : List (FactorTable ℕ ℕ)} {maxScope : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hlive : HoldsFactorList args.livePtr live s) (hlen : live.length = args.liveLen)
    (hmax : ∀ f ∈ live, f.scope.length ≤ maxScope)
    (hfit : Fits w (s.frontier + 4 + 8 * args.liveLen)) :
    let res := (Memory.spec 0).clientResult s (partitionLive args)
    let s' := (Memory.spec 0).clientState s (partitionLive args)
    let bucket := live.filter fun f => decide (args.x ∈ f.scope)
    let rest := live.filter fun f => decide (args.x ∉ f.scope)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partitionLive args)) ∧
      s'.frontier = s.frontier + 4 + 8 * args.liveLen ∧
      PreservesBelow s.frontier s s' ∧
      res.bucketPtr = s.frontier ∧
      res.newLiveBuf = s.frontier + 4 * args.liveLen ∧
      res.bucketLen = bucket.length ∧
      res.restLen = rest.length ∧
      HoldsFactorList res.bucketPtr bucket s' ∧
      AllDataBelow s.frontier res.bucketPtr bucket s' ∧
      HoldsFactorList (res.newLiveBuf + 4) rest s' ∧
      AllDataBelow s.frontier (res.newLiveBuf + 4) rest s' ∧
      memoryCost (partitionLive args) s ≤ 2 + args.liveLen * (8 + maxScope) := by
  dsimp only
  unfold partitionLive
  let bBase := s.frontier
  let rBuf := s.frontier + 4 * args.liveLen
  have hfit1 : Fits w (s.frontier + 4 * args.liveLen) := hfit.of_le (by omega)
  have hfit2 : Fits w ((s.frontier + 4 * args.liveLen) + (4 + 4 * args.liveLen)) :=
    hfit.of_le (by omega)
  have hv_a1 : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty (4 * args.liveLen))) :=
    validHistory_allocDirty hfit1
  let s₁ : Memory.State := ⟨s.mem, s.frontier + 4 * args.liveLen⟩
  have hwf₁ : Memory.WellFormed w s₁ := hwf.step (o := .allocDirty _) hfit1
  have hv_a2 : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (Memory.allocDirty (4 + 4 * args.liveLen))) :=
    validHistory_allocDirty hfit2
  let s₂ : Memory.State := ⟨s.mem, (s.frontier + 4 * args.liveLen) + (4 + 4 * args.liveLen)⟩
  have hwf₂ : Memory.WellFormed w s₂ := hwf₁.step (o := .allocDirty _) hfit2
  have hpres₂ : PreservesBelow s.frontier s s₂ :=
    ⟨le_rfl, by dsimp only [s₂]; omega, fun _ _ => rfl⟩
  have hlive_data : AllDataBelow s.frontier args.livePtr live s₂ :=
    (AllDataBelow.of_holdsFactorList hlive).frame fun _ _ _ => rfl
  have hlive₂ : HoldsFactorList args.livePtr live s₂ := hlive.mono_frontier hpres₂
  have hloop : ∀ (rem : List (FactorTable ℕ ℕ)) (cur : ℕ)
      (bAcc rAcc : List (FactorTable ℕ ℕ)) (t : Memory.State),
      Memory.WellFormed w t →
      t.frontier = s.frontier + 4 + 8 * args.liveLen →
      PreservesBelow s.frontier s t →
      cur + 4 * rem.length ≤ bBase →
      HoldsFactorList cur rem t →
      AllDataBelow s.frontier cur rem t →
      (∀ f ∈ rem, f.scope.length ≤ maxScope) →
      bAcc.length + rem.length ≤ args.liveLen →
      rAcc.length + rem.length ≤ args.liveLen →
      HoldsFactorList bBase bAcc t →
      AllDataBelow s.frontier bBase bAcc t →
      HoldsFactorList (rBuf + 4) rAcc t →
      AllDataBelow s.frontier (rBuf + 4) rAcc t →
      let st₀ : PartitionState :=
        ⟨cur, bBase + 4 * bAcc.length, bAcc.length, rBuf + 4 + 4 * rAcc.length, rAcc.length⟩
      let p := iterate partitionStep args.x rem.length st₀
      let r := (Memory.spec 0).clientResult t p
      let t' := (Memory.spec 0).clientState t p
      let bOut := bAcc ++ rem.filter fun f => decide (args.x ∈ f.scope)
      let rOut := rAcc ++ rem.filter fun f => decide (args.x ∉ f.scope)
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
        t'.frontier = s.frontier + 4 + 8 * args.liveLen ∧
        PreservesBelow s.frontier s t' ∧
        r.bCnt = bOut.length ∧
        r.rCnt = rOut.length ∧
        HoldsFactorList bBase bOut t' ∧
        AllDataBelow s.frontier bBase bOut t' ∧
        HoldsFactorList (rBuf + 4) rOut t' ∧
        AllDataBelow s.frontier (rBuf + 4) rOut t' ∧
        memoryCost p t ≤ rem.length * (8 + maxScope) := by
    intro rem
    induction rem with
    | nil =>
      intro cur bAcc rAcc t _ hfr hpres _ _ _ _ _ _ hbAcc hbData hrAcc hrData
      simp only [List.length_nil, List.filter_nil, List.append_nil, Nat.zero_mul]
      exact ⟨validHistory_pure w t _, hfr, hpres, rfl, rfl, hbAcc, hbData, hrAcc, hrData,
        by simp [iterate]⟩
    | cons f rest ih =>
      intro cur bAcc rAcc t hwf_t hfr hpres hcur_b ⟨hf, hrest⟩ ⟨hf_scF, hf_enF, hrest_data⟩
        hmax_rem hb_room hr_room hbAcc hbData hrAcc hrData
      simp only [List.length_cons] at hcur_b hb_room hr_room
      obtain ⟨hd, hsl, hel, hsc, hent⟩ := hf
      have hf_max : f.scope.length ≤ maxScope := hmax_rem f (List.mem_cons_self ..)
      have hrest_max : ∀ g ∈ rest, g.scope.length ≤ maxScope :=
        fun g hg => hmax_rem g (List.mem_cons_of_mem f hg)
      let st₀ : PartitionState :=
        ⟨cur, bBase + 4 * bAcc.length, bAcc.length, rBuf + 4 + 4 * rAcc.length, rAcc.length⟩
      let msArgs : MemScanArgs := ⟨args.x, t.mem cur, t.mem (cur + 1)⟩
      have hms_val : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (memScan msArgs)) :=
        memScan_valid msArgs (by dsimp only [msArgs]; rw [hsl]; exact hsc.1)
      have hms_res : (Memory.spec 0).clientResult t (memScan msArgs) =
          if args.x ∈ f.scope then 1 else 0 := memScan_result hsc.2 hsl.symm
      have hms_cost : memoryCost (memScan msArgs) t ≤ maxScope := by
        refine (memScan_cost msArgs t).trans ?_
        dsimp only [msArgs]
        rw [hsl]
        exact hf_max
      have hr_t (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
      have hres_t (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
      have hiter_eq : iterate partitionStep args.x (f :: rest).length st₀ =
          (partitionStep (args.x, st₀) >>= iterate partitionStep args.x rest.length) := rfl
      dsimp only
      rw [hiter_eq]
      by_cases hxf : args.x ∈ f.scope
      · have hflag1 : ((Memory.spec 0).clientResult t (memScan msArgs) = 1) := by
          rw [hms_res, ite_eq_left hxf]
        let wdArgs : WriteDescArgs :=
          ⟨bBase + 4 * bAcc.length, t.mem cur, t.mem (cur + 1), t.mem (cur + 2), t.mem (cur + 3)⟩
        obtain ⟨hwd_val, hwd_fr, hwf₁, hwd_pres, hwd_out, hf_new, hm0, hm2⟩ :=
          writeDesc_spec (w := w) wdArgs hwf_t
            (F := s.frontier) (by dsimp only [wdArgs, bBase]; omega)
            (by dsimp only [wdArgs, bBase]; omega)
            hf_scF hf_enF hsl hel hsc hent
        let t₁ := (Memory.spec 0).clientState t (writeDesc wdArgs)
        have hstep_val : (Memory.spec w).ValidHistory t
            ((Memory.spec w).clientHistory t (partitionStep (args.x, st₀))) := by
          unfold partitionStep
          dsimp only [st₀]
          refine validHistory_read_bind (by omega) ?_
          refine validHistory_read_bind (by omega) ?_
          refine validHistory_read_bind (by omega) ?_
          refine validHistory_read_bind (by omega) ?_
          refine validHistory_bind_step hms_val ?_
          rw [memScan_state, ite_eq_left hflag1]
          exact validHistory_bind_step hwd_val (validHistory_pure w _ _)
        have hstep_st : (Memory.spec 0).clientState t (partitionStep (args.x, st₀)) = t₁ := by
          unfold partitionStep
          dsimp only [st₀]
          rw [StateTransitionSpec.clientState_bind, hr_t, hres_t,
            StateTransitionSpec.clientState_bind, hr_t, hres_t,
            StateTransitionSpec.clientState_bind, hr_t, hres_t,
            StateTransitionSpec.clientState_bind, hr_t, hres_t,
            StateTransitionSpec.clientState_bind, memScan_state, ite_eq_left hflag1,
            StateTransitionSpec.clientState_bind]
          rfl
        have hstep_res : (Memory.spec 0).clientResult t (partitionStep (args.x, st₀)) =
            ⟨cur + 4, bBase + 4 * (bAcc.length + 1), bAcc.length + 1,
              rBuf + 4 + 4 * rAcc.length, rAcc.length⟩ := by
          unfold partitionStep
          dsimp only [st₀]
          rw [StateTransitionSpec.clientResult_bind, hr_t, hres_t,
            StateTransitionSpec.clientResult_bind, hr_t, hres_t,
            StateTransitionSpec.clientResult_bind, hr_t, hres_t,
            StateTransitionSpec.clientResult_bind, hr_t, hres_t,
            StateTransitionSpec.clientResult_bind, memScan_state, ite_eq_left hflag1,
            StateTransitionSpec.clientResult_bind]
          change (⟨cur + 4, bBase + 4 * bAcc.length + 4, bAcc.length + 1,
            rBuf + 4 + 4 * rAcc.length, rAcc.length⟩ : PartitionState) = _
          have heq : bBase + 4 * bAcc.length + 4 = bBase + 4 * (bAcc.length + 1) := by ring
          rw [heq]
        have hstep_cost : memoryCost (partitionStep (args.x, st₀)) t ≤ 8 + maxScope := by
          unfold partitionStep
          dsimp only [st₀]
          rw [memoryCost_bind', memoryCost_read, hr_t, hres_t,
            memoryCost_bind', memoryCost_read, hr_t, hres_t,
            memoryCost_bind', memoryCost_read, hr_t, hres_t,
            memoryCost_bind', memoryCost_read, hr_t, hres_t,
            memoryCost_bind', memScan_state, ite_eq_left hflag1,
            memoryCost_bind', writeDesc_cost, memoryCost_pure]
          change 1 + (1 + (1 + (1 + (memoryCost (memScan msArgs) t + (4 + 0))))) ≤ 8 + maxScope
          omega
        have hpres₁ : PreservesBelow s.frontier s t₁ := hpres.trans hwd_pres
        have hrest₁ : HoldsFactorList (cur + 4) rest t₁ :=
          hrest.frame_outside hrest_data hwd_pres fun a hlo hhi =>
            hwd_out a (Or.inl (by dsimp only [wdArgs, bBase]; omega))
        have hrest_data₁ : AllDataBelow s.frontier (cur + 4) rest t₁ :=
          hrest_data.frame fun a hlo hhi =>
            hwd_out a (Or.inl (by dsimp only [wdArgs, bBase]; omega))
        have hbAcc₁ : HoldsFactorList bBase (bAcc ++ [f]) t₁ := by
          refine holdsFactorList_append.mpr ⟨?_, hf_new, ?_⟩
          · exact hbAcc.frame_outside hbData hwd_pres fun a hlo hhi =>
              hwd_out a (Or.inl (by dsimp only [wdArgs]; omega))
          · unfold HoldsFactorList
            have ht₁_fr : t₁.frontier = t.frontier := hwd_fr
            rw [ht₁_fr, hfr]
            dsimp only [bBase]
            omega
        have hbData₁ : AllDataBelow s.frontier bBase (bAcc ++ [f]) t₁ := by
          refine allDataBelow_append.mpr ⟨?_, ?_⟩
          · exact hbData.frame fun a hlo hhi => hwd_out a (Or.inl (by dsimp only [wdArgs]; omega))
          · refine ⟨?_, ?_, trivial⟩
            · change t₁.mem wdArgs.dst + f.scope.length ≤ s.frontier
              rw [hm0]; exact hf_scF
            · change t₁.mem (wdArgs.dst + 2) + f.entries.size ≤ s.frontier
              rw [hm2]; exact hf_enF
        have hrAcc₁ : HoldsFactorList (rBuf + 4) rAcc t₁ :=
          hrAcc.frame_outside hrData hwd_pres fun a hlo hhi =>
            hwd_out a (Or.inr (by dsimp only [wdArgs, bBase, rBuf]; omega))
        have hrData₁ : AllDataBelow s.frontier (rBuf + 4) rAcc t₁ :=
          hrData.frame fun a hlo hhi =>
            hwd_out a (Or.inr (by dsimp only [wdArgs, bBase, rBuf]; omega))
        obtain ⟨hv_i, hfr_i, hpres_i, hbCnt_i, hrCnt_i, hbH_i, hbD_i, hrH_i, hrD_i, hcost_i⟩ :=
          ih (cur + 4) (bAcc ++ [f]) rAcc t₁ hwf₁ (hwd_fr.trans hfr) hpres₁ (by omega)
            hrest₁ hrest_data₁ hrest_max (by simp; omega) (by omega)
            hbAcc₁ hbData₁ hrAcc₁ hrData₁
        rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
          hstep_st, hstep_res, memoryCost_bind', hstep_st, hstep_res]
        have hbOut_eq : bAcc ++ (f :: rest).filter (fun g => decide (args.x ∈ g.scope)) =
            (bAcc ++ [f]) ++ rest.filter (fun g => decide (args.x ∈ g.scope)) := by
          simp [decide_eq_true hxf, List.append_assoc]
        have hrOut_eq : rAcc ++ (f :: rest).filter (fun g => decide (args.x ∉ g.scope)) =
            rAcc ++ rest.filter (fun g => decide (args.x ∉ g.scope)) := by
          simp [hxf]
        rw [hbOut_eq, hrOut_eq]
        refine ⟨validHistory_bind_step hstep_val
          (by simpa [hstep_st, hstep_res, List.length_append] using hv_i),
          by simpa [List.length_append] using hfr_i,
          by simpa [List.length_append] using hpres_i,
          by simpa [List.length_append] using hbCnt_i,
          by simpa [List.length_append] using hrCnt_i,
          by simpa [List.length_append] using hbH_i,
          by simpa [List.length_append] using hbD_i,
          by simpa [List.length_append] using hrH_i,
          by simpa [List.length_append] using hrD_i, ?_⟩
        have hcost_i' : memoryCost (iterate partitionStep args.x rest.length
            ⟨cur + 4, bBase + 4 * (bAcc.length + 1), bAcc.length + 1,
              rBuf + 4 + 4 * rAcc.length, rAcc.length⟩) t₁ ≤ rest.length * (8 + maxScope) := by
          simpa [List.length_append] using hcost_i
        calc memoryCost (partitionStep (args.x, st₀)) t + _
            ≤ (8 + maxScope) + rest.length * (8 + maxScope) := Nat.add_le_add hstep_cost hcost_i'
          _ = (f :: rest).length * (8 + maxScope) := by simp only [List.length_cons]; ring
      · have hflag0 : ¬ ((Memory.spec 0).clientResult t (memScan msArgs) = 1) := by
          rw [hms_res, ite_eq_right hxf]; decide
        let wdArgs : WriteDescArgs :=
          ⟨rBuf + 4 + 4 * rAcc.length, t.mem cur, t.mem (cur + 1), t.mem (cur + 2),
            t.mem (cur + 3)⟩
        obtain ⟨hwd_val, hwd_fr, hwf₁, hwd_pres, hwd_out, hf_new, hm0, hm2⟩ :=
          writeDesc_spec (w := w) wdArgs hwf_t
            (F := s.frontier) (by dsimp only [wdArgs, rBuf]; omega)
            (by dsimp only [wdArgs, rBuf]; omega)
            hf_scF hf_enF hsl hel hsc hent
        let t₁ := (Memory.spec 0).clientState t (writeDesc wdArgs)
        have hstep_val : (Memory.spec w).ValidHistory t
            ((Memory.spec w).clientHistory t (partitionStep (args.x, st₀))) := by
          unfold partitionStep
          dsimp only [st₀]
          refine validHistory_read_bind (by omega) ?_
          refine validHistory_read_bind (by omega) ?_
          refine validHistory_read_bind (by omega) ?_
          refine validHistory_read_bind (by omega) ?_
          refine validHistory_bind_step hms_val ?_
          rw [memScan_state, ite_eq_right hflag0]
          exact validHistory_bind_step hwd_val (validHistory_pure w _ _)
        have hstep_st : (Memory.spec 0).clientState t (partitionStep (args.x, st₀)) = t₁ := by
          unfold partitionStep
          dsimp only [st₀]
          rw [StateTransitionSpec.clientState_bind, hr_t, hres_t,
            StateTransitionSpec.clientState_bind, hr_t, hres_t,
            StateTransitionSpec.clientState_bind, hr_t, hres_t,
            StateTransitionSpec.clientState_bind, hr_t, hres_t,
            StateTransitionSpec.clientState_bind, memScan_state, ite_eq_right hflag0,
            StateTransitionSpec.clientState_bind]
          rfl
        have hstep_res : (Memory.spec 0).clientResult t (partitionStep (args.x, st₀)) =
            ⟨cur + 4, bBase + 4 * bAcc.length, bAcc.length,
              rBuf + 4 + 4 * (rAcc.length + 1), rAcc.length + 1⟩ := by
          unfold partitionStep
          dsimp only [st₀]
          rw [StateTransitionSpec.clientResult_bind, hr_t, hres_t,
            StateTransitionSpec.clientResult_bind, hr_t, hres_t,
            StateTransitionSpec.clientResult_bind, hr_t, hres_t,
            StateTransitionSpec.clientResult_bind, hr_t, hres_t,
            StateTransitionSpec.clientResult_bind, memScan_state, ite_eq_right hflag0,
            StateTransitionSpec.clientResult_bind]
          change (⟨cur + 4, bBase + 4 * bAcc.length, bAcc.length,
            rBuf + 4 + 4 * rAcc.length + 4, rAcc.length + 1⟩ : PartitionState) = _
          have heq : rBuf + 4 + 4 * rAcc.length + 4 = rBuf + 4 + 4 * (rAcc.length + 1) := by ring
          rw [heq]
        have hstep_cost : memoryCost (partitionStep (args.x, st₀)) t ≤ 8 + maxScope := by
          unfold partitionStep
          dsimp only [st₀]
          rw [memoryCost_bind', memoryCost_read, hr_t, hres_t,
            memoryCost_bind', memoryCost_read, hr_t, hres_t,
            memoryCost_bind', memoryCost_read, hr_t, hres_t,
            memoryCost_bind', memoryCost_read, hr_t, hres_t,
            memoryCost_bind', memScan_state, ite_eq_right hflag0,
            memoryCost_bind', writeDesc_cost, memoryCost_pure]
          change 1 + (1 + (1 + (1 + (memoryCost (memScan msArgs) t + (4 + 0))))) ≤ 8 + maxScope
          omega
        have hpres₁ : PreservesBelow s.frontier s t₁ := hpres.trans hwd_pres
        have hrest₁ : HoldsFactorList (cur + 4) rest t₁ :=
          hrest.frame_outside hrest_data hwd_pres fun a hlo hhi =>
            hwd_out a (Or.inl (by dsimp only [wdArgs, bBase, rBuf]; omega))
        have hrest_data₁ : AllDataBelow s.frontier (cur + 4) rest t₁ :=
          hrest_data.frame fun a hlo hhi =>
            hwd_out a (Or.inl (by dsimp only [wdArgs, bBase, rBuf]; omega))
        have hbAcc₁ : HoldsFactorList bBase bAcc t₁ :=
          hbAcc.frame_outside hbData hwd_pres fun a hlo hhi =>
            hwd_out a (Or.inl (by dsimp only [wdArgs, bBase, rBuf]; omega))
        have hbData₁ : AllDataBelow s.frontier bBase bAcc t₁ :=
          hbData.frame fun a hlo hhi =>
            hwd_out a (Or.inl (by dsimp only [wdArgs, bBase, rBuf]; omega))
        have hrAcc₁ : HoldsFactorList (rBuf + 4) (rAcc ++ [f]) t₁ := by
          refine holdsFactorList_append.mpr ⟨?_, hf_new, ?_⟩
          · exact hrAcc.frame_outside hrData hwd_pres fun a hlo hhi =>
              hwd_out a (Or.inl (by dsimp only [wdArgs]; omega))
          · unfold HoldsFactorList
            have ht₁_fr : t₁.frontier = t.frontier := hwd_fr
            rw [ht₁_fr, hfr]
            dsimp only [rBuf]
            omega
        have hrData₁ : AllDataBelow s.frontier (rBuf + 4) (rAcc ++ [f]) t₁ := by
          refine allDataBelow_append.mpr ⟨?_, ?_⟩
          · exact hrData.frame fun a hlo hhi => hwd_out a (Or.inl (by dsimp only [wdArgs]; omega))
          · refine ⟨?_, ?_, trivial⟩
            · change t₁.mem wdArgs.dst + f.scope.length ≤ s.frontier
              rw [hm0]; exact hf_scF
            · change t₁.mem (wdArgs.dst + 2) + f.entries.size ≤ s.frontier
              rw [hm2]; exact hf_enF
        obtain ⟨hv_i, hfr_i, hpres_i, hbCnt_i, hrCnt_i, hbH_i, hbD_i, hrH_i, hrD_i, hcost_i⟩ :=
          ih (cur + 4) bAcc (rAcc ++ [f]) t₁ hwf₁ (hwd_fr.trans hfr) hpres₁ (by omega)
            hrest₁ hrest_data₁ hrest_max (by omega) (by simp; omega)
            hbAcc₁ hbData₁ hrAcc₁ hrData₁
        rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
          hstep_st, hstep_res, memoryCost_bind', hstep_st, hstep_res]
        have hbOut_eq : bAcc ++ (f :: rest).filter (fun g => decide (args.x ∈ g.scope)) =
            bAcc ++ rest.filter (fun g => decide (args.x ∈ g.scope)) := by
          simp [hxf]
        have hrOut_eq : rAcc ++ (f :: rest).filter (fun g => decide (args.x ∉ g.scope)) =
            (rAcc ++ [f]) ++ rest.filter (fun g => decide (args.x ∉ g.scope)) := by
          simp [hxf, List.append_assoc]
        rw [hbOut_eq, hrOut_eq]
        refine ⟨validHistory_bind_step hstep_val
          (by simpa [hstep_st, hstep_res, List.length_append] using hv_i),
          by simpa [List.length_append] using hfr_i,
          by simpa [List.length_append] using hpres_i,
          by simpa [List.length_append] using hbCnt_i,
          by simpa [List.length_append] using hrCnt_i,
          by simpa [List.length_append] using hbH_i,
          by simpa [List.length_append] using hbD_i,
          by simpa [List.length_append] using hrH_i,
          by simpa [List.length_append] using hrD_i, ?_⟩
        have hcost_i' : memoryCost (iterate partitionStep args.x rest.length
            ⟨cur + 4, bBase + 4 * bAcc.length, bAcc.length,
              rBuf + 4 + 4 * (rAcc.length + 1), rAcc.length + 1⟩) t₁ ≤
            rest.length * (8 + maxScope) := by
          simpa [List.length_append] using hcost_i
        calc memoryCost (partitionStep (args.x, st₀)) t + _
            ≤ (8 + maxScope) + rest.length * (8 + maxScope) := Nat.add_le_add hstep_cost hcost_i'
          _ = (f :: rest).length * (8 + maxScope) := by simp only [List.length_cons]; ring
  obtain ⟨hv_l, hfr_l, hpres_l, hbCnt_l, hrCnt_l, hbH_l, hbD_l, hrH_l, hrD_l, hcost_l⟩ :=
    hloop live args.livePtr [] [] s₂ hwf₂ (by dsimp only [s₂]; omega) hpres₂
      hlive.bound hlive₂ hlive_data hmax (by simp [hlen]) (by simp [hlen])
      (by dsimp only [HoldsFactorList, s₂, bBase]; omega) trivial
      (by dsimp only [HoldsFactorList, s₂, rBuf]; omega) trivial
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hv_l hfr_l hpres_l hcost_l
  simp only [List.nil_append, List.length_nil, Nat.mul_zero, Nat.add_zero] at hbCnt_l hrCnt_l
  simp only [List.nil_append, List.length_nil, Nat.mul_zero, Nat.add_zero] at hbH_l hbD_l
  simp only [List.nil_append, List.length_nil, Nat.mul_zero, Nat.add_zero] at hrH_l hrD_l
  have ha1_st : (Memory.spec 0).clientState s (Memory.allocDirty (4 * args.liveLen)) = s₁ := rfl
  have ha1_res : (Memory.spec 0).clientResult s (Memory.allocDirty (4 * args.liveLen)) =
      bBase := rfl
  have ha2_st : (Memory.spec 0).clientState s₁ (Memory.allocDirty (4 + 4 * args.liveLen)) =
      s₂ := rfl
  have ha2_res : (Memory.spec 0).clientResult s₁ (Memory.allocDirty (4 + 4 * args.liveLen)) =
      rBuf := rfl
  have hpure_st {α : Type} (x : α) (t : Memory.State) :
      (Memory.spec 0).clientState t (pure x) = t := rfl
  have hpure_res {α : Type} (x : α) (t : Memory.State) :
      (Memory.spec 0).clientResult t (pure x) = x := rfl
  rw [← hlen]
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
  rw [hlen]
  rw [ha1_st, ha1_res,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    ha2_st, ha2_res,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    hpure_res, hpure_st]
  rw [← hlen]
  refine ⟨validHistory_bind_step (by rw [hlen]; exact hv_a1) ?_,
    by rw [hlen] at hfr_l ⊢; exact hfr_l, hpres_l, rfl, by rw [hlen],
    hbCnt_l, hrCnt_l, hbH_l, hbD_l, ?_, ?_, ?_⟩
  · rw [hlen, ha1_st, ha1_res]
    refine validHistory_bind_step hv_a2 ?_
    rw [ha2_st, ha2_res, ← hlen]
    exact validHistory_bind_step hv_l (validHistory_pure w _ _)
  · dsimp only; exact hrH_l
  · dsimp only; exact hrD_l
  · rw [memoryCost_bind', memoryCost_allocDirty]
    rw [hlen, ha1_st, ha1_res, memoryCost_bind', memoryCost_allocDirty, ha2_st, ha2_res,
      memoryCost_bind', memoryCost_pure, Nat.add_zero, ← hlen]
    omega

theorem partitionLive_realizes :
    Realizes .exact partitionLive WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 1 ∧ Fits w (s.frontier + 4 + 8 * args.liveLen) ∧
        ∃ live, live.length = args.liveLen ∧ HoldsFactorList args.livePtr live s)
      (fun _ _ => 0) := by
  unfold partitionLive
  realize [memScan_realizes, writeDesc_realizes]
  · exact h.2.1.of_le (by omega)
  · exact h.2.1.of_le (by omega)
  · exact h.2.1.of_le (by omega)
  · exact h.2.1.of_le (by omega)
  · obtain ⟨h1, hfit, live, hlen, hlive⟩ := h
    let bBase := s.frontier
    let rBuf := s.frontier + 4 * d.liveLen
    have hlive_b : d.livePtr + 4 * d.liveLen ≤ s.frontier := by rw [← hlen]; exact hlive.bound
    let stInit : PartitionState :=
      ⟨d.livePtr, s.frontier, 0, s.frontier + 4 * d.liveLen + 4, 0⟩
    let sInit : Memory.State := ⟨s.mem, s.frontier + 4 * d.liveLen + (4 + 4 * d.liveLen)⟩
    have hinit : sInit.frontier = s.frontier + 4 * d.liveLen + (4 + 4 * d.liveLen) ∧
        PreservesBelow s.frontier s sInit ∧
        bBase ≤ stInit.bDst ∧ rBuf + 4 ≤ stInit.rDst ∧
        stInit.curDesc + 4 * d.liveLen ≤ s.frontier ∧
        stInit.bDst + 4 * d.liveLen ≤ rBuf ∧
        stInit.bCnt + d.liveLen ≤ d.liveLen ∧
        stInit.rDst + 4 * d.liveLen ≤ s.frontier + 4 + 8 * d.liveLen ∧
        stInit.rCnt + d.liveLen ≤ d.liveLen ∧
        ∃ rem, rem.length = d.liveLen ∧ HoldsFactorList stInit.curDesc rem s :=
      ⟨rfl, ⟨le_rfl, by dsimp only [sInit]; omega, fun _ _ => rfl⟩,
        le_rfl, le_rfl, hlive_b, le_rfl, Nat.zero_add _ |>.le,
        by dsimp only [stInit, rBuf]; omega, Nat.zero_add _ |>.le, live, hlen, hlive⟩
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : PartitionState) (t : Memory.State) =>
        t.frontier = s.frontier + 4 * d.liveLen + (4 + 4 * d.liveLen) ∧
        PreservesBelow s.frontier s t ∧
        bBase ≤ st.bDst ∧
        rBuf + 4 ≤ st.rDst ∧
        st.curDesc + 4 * j ≤ s.frontier ∧
        st.bDst + 4 * j ≤ rBuf ∧
        st.bCnt + j ≤ d.liveLen ∧
        st.rDst + 4 * j ≤ s.frontier + 4 + 8 * d.liveLen ∧
        st.rCnt + j ≤ d.liveLen ∧
        ∃ rem, rem.length = j ∧ HoldsFactorList st.curDesc rem s)
      (fun j st t ⟨hfr, hpres, hb_lo, hr_lo, hcur_b, hb_b, hb_c, hr_b, hr_c, rem, hrem_l,
        hrem_h⟩ => ?_)
      hinit
    dsimp only
    rcases rem with _ | ⟨f, rest⟩
    · cases hrem_l
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hrem_l
    obtain ⟨hf, hrest⟩ := hrem_h
    obtain ⟨hd, hsl, hel, hsc, hent⟩ := hf
    have hm0 : t.mem st.curDesc = s.mem st.curDesc := hpres.2.2 _ (by omega)
    have hm1 : t.mem (st.curDesc + 1) = s.mem (st.curDesc + 1) := hpres.2.2 _ (by omega)
    have hr_t (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
    have hres_t (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
    refine ⟨?_, ?_⟩
    · refine ⟨hfit.of_le (by omega), hfit.of_le (by omega), hfit.of_le (by omega),
        ⟨h1, hfit.of_le (by rw [hm0, hm1, hsl]; have := hsc.1; omega)⟩, h1, ?_⟩
      split_ifs
      · exact ⟨hfit.of_le (by omega), hfit.of_le (by omega), hfit.of_le (by omega),
          hfit.of_le (by omega)⟩
      · exact ⟨hfit.of_le (by omega), hfit.of_le (by omega), hfit.of_le (by omega),
          hfit.of_le (by omega)⟩
    · unfold partitionStep
      dsimp only
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_t, hres_t,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_t, hres_t,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_t, hres_t,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_t, hres_t,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, memScan_state]
      split_ifs
      · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
        obtain ⟨hwf_fr, hwf_mem⟩ := writeDesc_frame
          ⟨st.bDst, t.mem st.curDesc, t.mem (st.curDesc + 1), t.mem (st.curDesc + 2),
            t.mem (st.curDesc + 3)⟩ t
        have hpure_st {α : Type} (x : α) (u : Memory.State) :
            (Memory.spec 0).clientState u (pure x) = u := rfl
        have hpure_res {α : Type} (x : α) (u : Memory.State) :
            (Memory.spec 0).clientResult u (pure x) = x := rfl
        rw [hpure_st, hpure_res]
        dsimp only
        refine ⟨hwf_fr.trans hfr, ?_, by omega, hr_lo, by omega, by omega, by omega, by omega,
          by omega, rest, hrem_l, hrest⟩
        exact ⟨le_rfl, by rw [hwf_fr]; exact hpres.2.1, fun a ha =>
          (hwf_mem a (Or.inl (by dsimp only; omega))).trans (hpres.2.2 a ha)⟩
      · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
        obtain ⟨hwf_fr, hwf_mem⟩ := writeDesc_frame
          ⟨st.rDst, t.mem st.curDesc, t.mem (st.curDesc + 1), t.mem (st.curDesc + 2),
            t.mem (st.curDesc + 3)⟩ t
        have hpure_st {α : Type} (x : α) (u : Memory.State) :
            (Memory.spec 0).clientState u (pure x) = u := rfl
        have hpure_res {α : Type} (x : α) (u : Memory.State) :
            (Memory.spec 0).clientResult u (pure x) = x := rfl
        rw [hpure_st, hpure_res]
        dsimp only
        refine ⟨hwf_fr.trans hfr, ?_, hb_lo, by omega, by omega, by omega, by omega, by omega,
          by omega, rest, hrem_l, hrest⟩
        exact ⟨le_rfl, by rw [hwf_fr]; exact hpres.2.1, fun a ha =>
          (hwf_mem a (Or.inl (by dsimp only; omega))).trans (hpres.2.2 a ha)⟩

end Cslib.Algorithms.WordRAM.VariableElimination
