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

/-- One `partitionStep` scans the current descriptor's scope for `x`, then copies the descriptor to
the bucket array on a hit and to the rest array otherwise. -/
private theorem partitionStep_run (x : ℕ) (st : PartitionState) (t : Memory.State) :
    let c := st.curDesc
    let hit := (Memory.spec 0).clientResult t (memScan ⟨x, t.mem c, t.mem (c + 1)⟩) = 1
    (Memory.spec 0).clientState t (partitionStep (x, st)) =
        (Memory.spec 0).clientState t (writeDesc ⟨if hit then st.bDst else st.rDst, t.mem c,
          t.mem (c + 1), t.mem (c + 2), t.mem (c + 3)⟩) ∧
      (Memory.spec 0).clientResult t (partitionStep (x, st)) =
        (if hit then ⟨c + 4, st.bDst + 4, st.bCnt + 1, st.rDst, st.rCnt⟩
          else ⟨c + 4, st.bDst, st.bCnt, st.rDst + 4, st.rCnt + 1⟩) ∧
      memoryCost (partitionStep (x, st)) t =
        memoryCost (memScan ⟨x, t.mem c, t.mem (c + 1)⟩) t + 8 := by
  have hs := memScan_state ⟨x, t.mem st.curDesc, t.mem (st.curDesc + 1)⟩ t
  simp only [StateTransitionSpec.clientState] at hs
  unfold partitionStep
  dsimp only
  split_ifs with h <;>
    simp only [StateTransitionSpec.clientState, client_simps, runClient_read, hs, h, ite_true,
      ite_false, writeDesc_cost, true_and] <;> omega

private theorem partitionStep_valid {w x : ℕ} {st : PartitionState} {t : Memory.State}
    (hc : st.curDesc + 4 ≤ t.frontier)
    (hms : (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t
      (memScan ⟨x, t.mem st.curDesc, t.mem (st.curDesc + 1)⟩)))
    (hwd : (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (writeDesc
      ⟨if (Memory.spec 0).clientResult t
          (memScan ⟨x, t.mem st.curDesc, t.mem (st.curDesc + 1)⟩) = 1 then st.bDst else st.rDst,
        t.mem st.curDesc, t.mem (st.curDesc + 1), t.mem (st.curDesc + 2),
        t.mem (st.curDesc + 3)⟩))) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (partitionStep (x, st))) := by
  unfold partitionStep
  dsimp only
  refine validHistory_read_bind (by omega) <| validHistory_read_bind (by omega) <|
    validHistory_read_bind (by omega) <| validHistory_read_bind (by omega) <|
    validHistory_bind_step hms ?_
  rw [memScan_state]
  split_ifs at hwd ⊢ <;> exact validHistory_bind_step hwd (validHistory_pure w _ _)

/-- A descriptor list and the bound on its data survive a step that preserves memory below `F`
and the list's descriptor cells. -/
private theorem holdsFactorList_frame {F base : ℕ} {fs : List (FactorTable ℕ ℕ)}
    {s₀ s₁ : Memory.State} (h : HoldsFactorList base fs s₀ ∧ AllDataBelow F base fs s₀)
    (hpres : PreservesBelow F s₀ s₁)
    (hdesc : ∀ a, base ≤ a → a < base + 4 * fs.length → s₁.mem a = s₀.mem a) :
    HoldsFactorList base fs s₁ ∧ AllDataBelow F base fs s₁ :=
  ⟨h.1.frame_outside h.2 hpres hdesc, h.2.frame hdesc⟩

/-- Writing the descriptor of `f` just past a descriptor list extends the list by `f`. -/
private theorem holdsFactorList_snoc {F base : ℕ} {fs : List (FactorTable ℕ ℕ)}
    {f : FactorTable ℕ ℕ} {s₀ s₁ : Memory.State}
    (h : HoldsFactorList base fs s₀ ∧ AllDataBelow F base fs s₀)
    (hpres : PreservesBelow F s₀ s₁)
    (hdesc : ∀ a, a < base + 4 * fs.length → s₁.mem a = s₀.mem a)
    (hf : HoldsFactor (base + 4 * fs.length) f s₁)
    (hsc : s₁.mem (base + 4 * fs.length) + f.scope.length ≤ F)
    (hen : s₁.mem (base + 4 * fs.length + 2) + f.entries.size ≤ F) :
    HoldsFactorList base (fs ++ [f]) s₁ ∧ AllDataBelow F base (fs ++ [f]) s₁ := by
  obtain ⟨hl, hd⟩ := holdsFactorList_frame h hpres fun a _ ha => hdesc a ha
  exact ⟨holdsFactorList_append.mpr ⟨hl, hf, by have := hf.1; dsimp only [HoldsFactorList]; omega⟩,
    allDataBelow_append.mpr ⟨hd, hsc, hen, trivial⟩⟩

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
  let s₁ : Memory.State := ⟨s.mem, s.frontier + 4 * args.liveLen⟩
  have hwf₁ : Memory.WellFormed w s₁ := hwf.step (o := .allocDirty _) hfit1
  let s₂ : Memory.State := ⟨s.mem, (s.frontier + 4 * args.liveLen) + (4 + 4 * args.liveLen)⟩
  have hwf₂ : Memory.WellFormed w s₂ := hwf₁.step (o := .allocDirty _) hfit2
  have hpres₂ : PreservesBelow s.frontier s s₂ :=
    ⟨le_rfl, by dsimp only [s₂]; omega, fun _ _ => rfl⟩
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
      HoldsFactorList bBase bAcc t ∧ AllDataBelow s.frontier bBase bAcc t →
      HoldsFactorList (rBuf + 4) rAcc t ∧ AllDataBelow s.frontier (rBuf + 4) rAcc t →
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
    intro rem cur bAcc rAcc t
    induction rem generalizing cur bAcc rAcc t with
    | nil =>
      intro _ hfr hpres _ _ _ _ _ _ hb hr
      simp only [List.length_nil, List.filter_nil, List.append_nil, Nat.zero_mul]
      exact ⟨validHistory_pure w t _, hfr, hpres, rfl, rfl, hb.1, hb.2, hr.1, hr.2,
        by simp [iterate]⟩
    | cons f rest ih =>
      intro hwf_t hfr hpres hcur_b ⟨hf, hrest⟩ ⟨hf_scF, hf_enF, hrest_data⟩
        hmax_rem hb_room hr_room hb hr
      simp only [List.length_cons] at hcur_b hb_room hr_room
      obtain ⟨hd, hsl, hel, hsc, hent⟩ := hf
      let st₀ : PartitionState :=
        ⟨cur, bBase + 4 * bAcc.length, bAcc.length, rBuf + 4 + 4 * rAcc.length, rAcc.length⟩
      have hhit :
          (Memory.spec 0).clientResult t (memScan ⟨args.x, t.mem cur, t.mem (cur + 1)⟩) = 1 ↔
            args.x ∈ f.scope := by
        rw [memScan_result hsc.2 hsl.symm]; split_ifs with h <;> simp [h]
      obtain ⟨hstep_st, hstep_res, hstep_cost⟩ := partitionStep_run args.x st₀ t
      dsimp only [st₀] at hstep_st hstep_res hstep_cost
      -- The step writes `f`'s descriptor at the end of the bucket or of the rest array.
      let wdArgs : WriteDescArgs :=
        ⟨if (Memory.spec 0).clientResult t (memScan ⟨args.x, t.mem cur, t.mem (cur + 1)⟩) = 1
            then st₀.bDst else st₀.rDst,
          t.mem cur, t.mem (cur + 1), t.mem (cur + 2), t.mem (cur + 3)⟩
      have hdst : wdArgs.dst = if args.x ∈ f.scope then bBase + 4 * bAcc.length
          else rBuf + 4 + 4 * rAcc.length := by
        simp only [wdArgs, st₀, hhit]
      have hdst_lo : bBase ≤ wdArgs.dst := by rw [hdst]; split_ifs <;> omega
      obtain ⟨hwd_val, hwd_fr, hwf₁, hwd_pres, hwd_out, hf_new, hm0, hm2⟩ :=
        writeDesc_spec (F := s.frontier) wdArgs hwf_t hdst_lo
          (by rw [hdst]; split_ifs <;> omega) hf_scF hf_enF hsl hel hsc hent
      set t₁ := (Memory.spec 0).clientState t (writeDesc wdArgs)
      let bAcc' := if args.x ∈ f.scope then bAcc ++ [f] else bAcc
      let rAcc' := if args.x ∈ f.scope then rAcc else rAcc ++ [f]
      have hacc : (HoldsFactorList bBase bAcc' t₁ ∧ AllDataBelow s.frontier bBase bAcc' t₁) ∧
          (HoldsFactorList (rBuf + 4) rAcc' t₁ ∧
            AllDataBelow s.frontier (rBuf + 4) rAcc' t₁) := by
        by_cases hxf : args.x ∈ f.scope <;>
          simp only [bAcc', rAcc', hxf, ↓reduceIte] at hdst ⊢ <;>
          rw [hdst] at hf_new hm0 hm2
        · exact ⟨holdsFactorList_snoc hb hwd_pres (fun a ha => hwd_out a (Or.inl (by omega)))
              hf_new (hm0.symm ▸ hf_scF) (hm2.symm ▸ hf_enF),
            holdsFactorList_frame hr hwd_pres fun a ha _ => hwd_out a (Or.inr (by omega))⟩
        · exact ⟨holdsFactorList_frame hb hwd_pres fun a _ ha => hwd_out a (Or.inl (by omega)),
            holdsFactorList_snoc hr hwd_pres (fun a ha => hwd_out a (Or.inl (by omega)))
              hf_new (hm0.symm ▸ hf_scF) (hm2.symm ▸ hf_enF)⟩
      have hres : (Memory.spec 0).clientResult t (partitionStep (args.x, st₀)) =
          ⟨cur + 4, bBase + 4 * bAcc'.length, bAcc'.length, rBuf + 4 + 4 * rAcc'.length,
            rAcc'.length⟩ := by
        simp only [st₀, hstep_res, hhit, bAcc', rAcc']
        split_ifs <;> simp <;> omega
      have hcost : memoryCost (partitionStep (args.x, st₀)) t ≤ 8 + maxScope := by
        have hms := memScan_cost ⟨args.x, t.mem cur, t.mem (cur + 1)⟩ t
        have := hmax_rem f (List.mem_cons_self ..)
        dsimp only [st₀] at hms ⊢
        omega
      have hb' : bAcc'.length ≤ bAcc.length + 1 := by simp only [bAcc']; split_ifs <;> simp
      have hr' : rAcc'.length ≤ rAcc.length + 1 := by simp only [rAcc']; split_ifs <;> simp
      have hrest₁ := holdsFactorList_frame ⟨hrest, hrest_data⟩ hwd_pres fun a _ ha =>
        hwd_out a (Or.inl (by omega))
      obtain ⟨hv_i, hfr_i, hpres_i, hbCnt_i, hrCnt_i, hbH_i, hbD_i, hrH_i, hrD_i, hcost_i⟩ :=
        ih (cur + 4) bAcc' rAcc' t₁ hwf₁ (hwd_fr.trans hfr) (hpres.trans hwd_pres) (by omega)
          hrest₁.1 hrest₁.2 (fun g hg => hmax_rem g (List.mem_cons_of_mem f hg))
          (by omega) (by omega) hacc.1 hacc.2
      have hbOut : bAcc ++ (f :: rest).filter (fun g => decide (args.x ∈ g.scope)) =
          bAcc' ++ rest.filter (fun g => decide (args.x ∈ g.scope)) := by
        by_cases hxf : args.x ∈ f.scope <;> simp [bAcc', hxf]
      have hrOut : rAcc ++ (f :: rest).filter (fun g => decide (args.x ∉ g.scope)) =
          rAcc' ++ rest.filter (fun g => decide (args.x ∉ g.scope)) := by
        by_cases hxf : args.x ∈ f.scope <;> simp [rAcc', hxf]
      dsimp only
      rw [List.length_cons, iterate, StateTransitionSpec.clientResult_bind,
        StateTransitionSpec.clientState_bind, memoryCost_bind', hstep_st, hres, hbOut, hrOut]
      refine ⟨validHistory_bind_step
          (partitionStep_valid (by omega) (memScan_valid _ (hsl.symm ▸ hsc.1)) hwd_val)
          (by simpa only [st₀, hstep_st, hres] using hv_i), hfr_i, hpres_i, hbCnt_i, hrCnt_i,
        hbH_i, hbD_i, hrH_i, hrD_i, ?_⟩
      dsimp only [st₀] at hcost
      rw [add_one_mul]; omega
  have h := hloop live args.livePtr [] [] s₂ hwf₂ (by dsimp only [s₂]; omega) hpres₂
      hlive.bound (hlive.mono_frontier hpres₂)
      ((AllDataBelow.of_holdsFactorList hlive).frame fun _ _ _ => rfl) hmax
      (by simp [hlen]) (by simp [hlen])
      ⟨by dsimp only [HoldsFactorList, s₂, bBase]; omega, trivial⟩
      ⟨by dsimp only [HoldsFactorList, s₂, rBuf]; omega, trivial⟩
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, List.nil_append, hlen] at h
  obtain ⟨hv_l, hfr_l, hpres_l, hbCnt_l, hrCnt_l, hbH_l, hbD_l, hrH_l, hrD_l, hcost_l⟩ := h
  refine ⟨validHistory_allocDirty_bind hfit1 (validHistory_allocDirty_bind hfit2
      (validHistory_bind_step hv_l (validHistory_pure w _ _))), ?_⟩
  simp only [client_simps, memoryCost_bind', clientResult_allocDirty,
    memoryCost_allocDirty, memoryCost_pure]
  rw [clientState_allocDirty, clientState_allocDirty]
  exact ⟨hfr_l, hpres_l, trivial, rfl, hbCnt_l, hrCnt_l, hbH_l, hbD_l, hrH_l, hrD_l,
    by have := hcost_l; dsimp only [bBase, rBuf, s₂] at this ⊢; omega⟩

theorem partitionLive_realizes :
    Realizes .exact partitionLive WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 1 ∧ Fits w (s.frontier + 4 + 8 * args.liveLen) ∧
        ∃ live, live.length = args.liveLen ∧ HoldsFactorList args.livePtr live s)
      (fun _ _ => 0) := by
  unfold partitionLive
  realize [memScan_realizes, writeDesc_realizes]
  iterate 4 · exact h.2.1.of_le (by omega)
  · obtain ⟨h1, hfit, live, hlen, hlive⟩ := h
    let bBase := s.frontier
    let rBuf := s.frontier + 4 * d.liveLen
    have hlive_b : d.livePtr + 4 * d.liveLen ≤ s.frontier := hlen ▸ hlive.bound
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
      ⟨rfl, ⟨le_rfl, (Nat.le_add_right _ _).trans (Nat.le_add_right _ _), fun _ _ => rfl⟩,
        le_rfl, le_rfl, hlive_b, le_rfl, (Nat.zero_add _).le,
        (by omega : (s.frontier + 4 * d.liveLen + 4) + 4 * d.liveLen ≤ _), (Nat.zero_add _).le,
        live, hlen, hlive⟩
    dsimp only
    obtain ⟨f, rest, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_eq_add_one hrem_l)
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hrem_l
    obtain ⟨⟨hd, hsl, hel, hsc, hent⟩, hrest⟩ := hrem_h
    have hm0 : t.mem st.curDesc = s.mem st.curDesc := hpres.2.2 _ (by omega)
    have hm1 : t.mem (st.curDesc + 1) = s.mem (st.curDesc + 1) := hpres.2.2 _ (by omega)
    refine ⟨?_, ?_⟩
    · refine ⟨hfit.of_le (by omega), hfit.of_le (by omega), hfit.of_le (by omega),
        ⟨h1, hfit.of_le (by rw [hm0, hm1, hsl]; have := hsc.1; omega)⟩, h1, ?_⟩
      split_ifs <;> exact ⟨hfit.of_le (by omega), hfit.of_le (by omega), hfit.of_le (by omega),
        hfit.of_le (by omega)⟩
    · obtain ⟨hst, hres, -⟩ := partitionStep_run d.x st t
      rw [hst, hres]
      refine ⟨(writeDesc_frame _ t).1.trans hfr,
        ⟨le_rfl, hpres.2.1.trans_eq (writeDesc_frame _ t).1.symm, fun a ha =>
          ((writeDesc_frame _ t).2 a (Or.inl (by
            dsimp only
            split_ifs <;> omega))).trans (hpres.2.2 a ha)⟩, ?_⟩
      split_ifs <;> dsimp only <;> exact ⟨by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, rest, hrem_l, hrest⟩

end Cslib.Algorithms.WordRAM.VariableElimination
