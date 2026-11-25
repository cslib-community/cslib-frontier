/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.FlattenScope
import CslibFrontier.Tactic.Realize

/-!
# Deduplicated Output Scope Materialization (`buildOutScope`)

Deduplicates a flattened bucket-scope buffer backwards (`dedupFilterBack`) skipping the eliminated
variable `x`, producing `bucketOutScope x bucket` in exact canonical order.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.buildOutScope`: output-scope builder `Memory.Prog`.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

private structure DedupArgs where
  x : ℕ
  flatPtr : ℕ
  flatLen : ℕ

private def DedupArgs.equiv : DedupArgs ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.x, s.flatPtr), s.flatLen)
  invFun := fun ((x, flatPtr), flatLen) => ⟨x, flatPtr, flatLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding DedupArgs := .ofEquiv DedupArgs.equiv

private structure DedupState where
  remPos : ℕ
  outStart : ℕ
  outLen : ℕ

private def DedupState.equiv : DedupState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.remPos, s.outStart), s.outLen)
  invFun := fun ((remPos, outStart), outLen) => ⟨remPos, outStart, outLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding DedupState := .ofEquiv DedupState.equiv

private def dedupBackStep (p : (ℕ × ℕ) × DedupState) : Memory.Prog DedupState :=
  let pos := p.2.remPos - 1
  Memory.read (p.1.2 + pos) >>= fun v =>
  memScan ⟨v, p.2.outStart, p.2.outLen⟩ >>= fun inAcc =>
  if v = p.1.1 ∨ inAcc = 1 then
    pure ⟨pos, p.2.outStart, p.2.outLen⟩
  else
    Memory.write (p.2.outStart - 1) v >>= fun _ =>
      pure ⟨pos, p.2.outStart - 1, p.2.outLen + 1⟩

private def dedupFilterBack (args : DedupArgs) : Memory.Prog (ℕ × ℕ) :=
  Memory.allocDirty args.flatLen >>= fun outBuf =>
  iterate dedupBackStep (args.x, args.flatPtr) args.flatLen
    ⟨args.flatLen, outBuf + args.flatLen, 0⟩ >>= fun res =>
  pure (res.outStart, res.outLen)

private theorem dedupFilterBack_spec {w : ℕ} {args : DedupArgs} {flat : List ℕ} {W_out : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hflat : HoldsIn args.flatPtr flat s) (hlen : flat.length = args.flatLen)
    (hW : (flat.foldr (dedupStepPure args.x) []).length ≤ W_out)
    (hfit : Fits w (s.frontier + args.flatLen)) :
    let res := (Memory.spec 0).clientResult s (dedupFilterBack args)
    let s' := (Memory.spec 0).clientState s (dedupFilterBack args)
    let outScope := flat.foldr (dedupStepPure args.x) []
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dedupFilterBack args)) ∧
      s'.frontier = s.frontier + args.flatLen ∧
      PreservesBelow s.frontier s s' ∧
      s.frontier ≤ res.1 ∧
      res.2 = outScope.length ∧
      HoldsIn res.1 outScope s' ∧
      memoryCost (dedupFilterBack args) s ≤ 1 + args.flatLen * (2 + W_out) := by
  dsimp only
  unfold dedupFilterBack
  let outBuf := s.frontier
  have hv_a : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty args.flatLen)) :=
    validHistory_allocDirty hfit
  let s₀ : Memory.State := ⟨s.mem, outBuf + args.flatLen⟩
  have hwf₀ : Memory.WellFormed w s₀ := hwf.step (o := .allocDirty args.flatLen) hfit
  have hloop : ∀ (ys : List ℕ) (acc : List ℕ) (t : Memory.State),
      Memory.WellFormed w t →
      t.frontier = outBuf + args.flatLen →
      PreservesBelow outBuf s t →
      args.flatPtr + ys.length ≤ outBuf →
      Block.HoldsList args.flatPtr ys s.mem →
      ys.length + acc.length ≤ args.flatLen →
      (ys.foldr (dedupStepPure args.x) acc).length ≤ W_out →
      Block.HoldsList (outBuf + args.flatLen - acc.length) acc t.mem →
      let st₀ : DedupState := ⟨ys.length, outBuf + args.flatLen - acc.length, acc.length⟩
      let p := iterate dedupBackStep (args.x, args.flatPtr) ys.length st₀
      let r := (Memory.spec 0).clientResult t p
      let t' := (Memory.spec 0).clientState t p
      let out := ys.foldr (dedupStepPure args.x) acc
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
        t'.frontier = outBuf + args.flatLen ∧
        PreservesBelow outBuf s t' ∧
        r.outStart = outBuf + args.flatLen - out.length ∧
        r.outLen = out.length ∧
        out.length ≤ args.flatLen ∧
        Block.HoldsList r.outStart out t'.mem ∧
        memoryCost p t ≤ ys.length * (2 + W_out) := by
    intro ys
    induction ys using List.reverseRecOn with
    | nil =>
      intro acc t _ hfr hpres _ _ hroom _ hacc
      simp only [List.length_nil, Nat.zero_add, List.foldr_nil, Nat.zero_mul] at hroom ⊢
      exact ⟨validHistory_pure w t _, hfr, hpres, rfl, rfl, hroom, hacc, by simp [iterate]⟩
    | append_singleton ys' v ih =>
      intro acc t hwf_t hfr hpres hys_b hys_h hroom hW_cur hacc
      rw [List.length_append, List.length_singleton] at hys_b hroom
      obtain ⟨hys'_h, hv_h⟩ := Block.holdsList_append_iff.mp hys_h
      have hv_mem_s : s.mem (args.flatPtr + ys'.length) = v :=
        (Block.holdsList_cons_iff.mp hv_h).1
      have hv_mem_t : t.mem (args.flatPtr + ys'.length) = v :=
        (hpres.2.2 _ (by omega)).trans hv_mem_s
      have hacc_W : acc.length ≤ W_out :=
        (length_le_foldr_dedupStepPure args.x (ys' ++ [v]) acc).trans hW_cur
      let outStart := outBuf + args.flatLen - acc.length
      let st₀ : DedupState := ⟨(ys' ++ [v]).length, outStart, acc.length⟩
      have hpos_eq : st₀.remPos - 1 = ys'.length := by
        dsimp only [st₀]; rw [List.length_append, List.length_singleton]; omega
      let msArgs : MemScanArgs := ⟨v, outStart, acc.length⟩
      have hms_val : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (memScan msArgs)) :=
        memScan_valid msArgs (by dsimp only [msArgs, outStart]; omega)
      have hms_res : (Memory.spec 0).clientResult t (memScan msArgs) =
          if v ∈ acc then 1 else 0 := memScan_result hacc rfl
      have hms_cost : memoryCost (memScan msArgs) t ≤ W_out :=
        (memScan_cost msArgs t).trans hacc_W
      have hr_t (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
      have hres_t (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
      have hlen_ys : (ys' ++ [v]).length = ys'.length + 1 := by simp
      dsimp only
      rw [hlen_ys]
      have hiter_eq : iterate dedupBackStep (args.x, args.flatPtr) (ys'.length + 1)
          ⟨ys'.length + 1, outStart, acc.length⟩ =
          (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩) >>=
            iterate dedupBackStep (args.x, args.flatPtr) ys'.length) := rfl
      rw [hiter_eq]
      have hfoldr_eq : (ys' ++ [v]).foldr (dedupStepPure args.x) acc =
          ys'.foldr (dedupStepPure args.x) (dedupStepPure args.x v acc) := by
        rw [List.foldr_append, List.foldr_cons, List.foldr_nil]
      rw [hfoldr_eq] at hW_cur ⊢
      by_cases hcond : v = args.x ∨ v ∈ acc
      · have hguard : v = args.x ∨ (Memory.spec 0).clientResult t (memScan msArgs) = 1 := by
          rcases hcond with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (by rw [hms_res, ite_eq_left h2])
        have hstep_val : (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t
            (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩))) := by
          unfold dedupBackStep
          dsimp only
          rw [Nat.add_sub_cancel]
          refine validHistory_read_bind (by omega) ?_
          rw [hv_mem_t]
          refine validHistory_bind_step hms_val ?_
          rw [memScan_state, ite_eq_left hguard]
          exact validHistory_pure w t _
        have hstep_st : (Memory.spec 0).clientState t
            (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩)) =
            t := by
          unfold dedupBackStep
          dsimp only
          rw [Nat.add_sub_cancel, StateTransitionSpec.clientState_bind, hr_t, hres_t, hv_mem_t,
            StateTransitionSpec.clientState_bind, memScan_state, ite_eq_left hguard]
          rfl
        have hstep_res : (Memory.spec 0).clientResult t
            (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩)) =
            ⟨ys'.length, outStart, acc.length⟩ := by
          unfold dedupBackStep
          dsimp only
          rw [Nat.add_sub_cancel, StateTransitionSpec.clientResult_bind, hr_t, hres_t, hv_mem_t,
            StateTransitionSpec.clientResult_bind, memScan_state, ite_eq_left hguard]
          rfl
        have hstep_cost : memoryCost
            (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩)) t ≤
            2 + W_out := by
          unfold dedupBackStep
          dsimp only
          rw [Nat.add_sub_cancel, memoryCost_bind', memoryCost_read, hr_t, hres_t, hv_mem_t,
            memoryCost_bind', memScan_state, ite_eq_left hguard, memoryCost_pure]
          dsimp only [msArgs] at hms_cost
          omega
        have hdedup_eq : dedupStepPure args.x v acc = acc := by
          unfold dedupStepPure; exact ite_eq_left hcond
        rw [hdedup_eq] at hW_cur ⊢
        obtain ⟨hv_i, hfr_i, hpres_i, hst_i, hlen_i, hle_i, hholds_i, hcost_i⟩ :=
          ih acc t hwf_t hfr hpres (by omega) hys'_h (by omega) hW_cur hacc
        rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
          hstep_st, hstep_res, memoryCost_bind', hstep_st, hstep_res]
        refine ⟨validHistory_bind_step hstep_val (by simpa [hstep_st, hstep_res] using hv_i),
          hfr_i, hpres_i, hst_i, hlen_i, hle_i, hholds_i, ?_⟩
        calc memoryCost _ t + _
            ≤ (2 + W_out) + ys'.length * (2 + W_out) := Nat.add_le_add hstep_cost hcost_i
          _ = (ys'.length + 1) * (2 + W_out) := by ring
      · have hnot_guard : ¬ (v = args.x ∨ (Memory.spec 0).clientResult t (memScan msArgs) = 1) := by
          rintro (h1 | h2)
          · exact hcond (Or.inl h1)
          · have hnot_in : v ∉ acc := fun hm => hcond (Or.inr hm)
            rw [hms_res, ite_eq_right hnot_in] at h2
            cases h2
        have hv_fit : Fits w v := hv_mem_t ▸ hwf_t.mem_fits (args.flatPtr + ys'.length)
        have hout_lt : outStart - 1 < t.frontier := by dsimp only [outStart]; omega
        let t₁ : Memory.State := ⟨Function.update t.mem (outStart - 1) v, t.frontier⟩
        have hwf₁ : Memory.WellFormed w t₁ :=
          hwf_t.step (o := .write (outStart - 1) v) ⟨hout_lt, hv_fit⟩
        have hstep_val : (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t
            (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩))) := by
          unfold dedupBackStep
          dsimp only
          rw [Nat.add_sub_cancel]
          refine validHistory_read_bind (by omega) ?_
          rw [hv_mem_t]
          refine validHistory_bind_step hms_val ?_
          rw [memScan_state, ite_eq_right hnot_guard]
          exact validHistory_write_bind hout_lt hv_fit (validHistory_pure w _ _)
        have hstep_st : (Memory.spec 0).clientState t
            (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩)) =
            t₁ := by
          unfold dedupBackStep
          dsimp only
          rw [Nat.add_sub_cancel, StateTransitionSpec.clientState_bind, hr_t, hres_t, hv_mem_t,
            StateTransitionSpec.clientState_bind, memScan_state, ite_eq_right hnot_guard,
            StateTransitionSpec.clientState_bind]
          rfl
        have hout_sub : outStart - 1 = outBuf + args.flatLen - (v :: acc).length := by
          dsimp only [outStart]; simp only [List.length_cons]; omega
        have hstep_res : (Memory.spec 0).clientResult t
            (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩)) =
            ⟨ys'.length, outBuf + args.flatLen - (v :: acc).length, (v :: acc).length⟩ := by
          unfold dedupBackStep
          dsimp only
          rw [Nat.add_sub_cancel, StateTransitionSpec.clientResult_bind, hr_t, hres_t, hv_mem_t,
            StateTransitionSpec.clientResult_bind, memScan_state, ite_eq_right hnot_guard,
            StateTransitionSpec.clientResult_bind]
          change (⟨ys'.length, outStart - 1, acc.length + 1⟩ : DedupState) = _
          rw [hout_sub]
          rfl
        have hstep_cost : memoryCost
            (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩)) t ≤
            2 + W_out := by
          unfold dedupBackStep
          dsimp only
          rw [Nat.add_sub_cancel, memoryCost_bind', memoryCost_read, hr_t, hres_t, hv_mem_t,
            memoryCost_bind', memScan_state, ite_eq_right hnot_guard,
            memoryCost_bind', memoryCost_write, memoryCost_pure]
          dsimp only [msArgs] at hms_cost
          omega
        have hpres₁ : PreservesBelow outBuf s t₁ := by
          refine ⟨le_rfl, by dsimp only [t₁]; omega, fun a ha => ?_⟩
          have hne : a ≠ outStart - 1 := by dsimp only [outStart]; omega
          change Function.update t.mem (outStart - 1) v a = s.mem a
          rw [Function.update_of_ne hne]
          exact hpres.2.2 a ha
        have hacc₁ : Block.HoldsList (outBuf + args.flatLen - (v :: acc).length) (v :: acc)
            t₁.mem := by
          rw [← hout_sub]
          refine Block.holdsList_cons_iff.mpr ⟨Function.update_self _ v t.mem, ?_⟩
          have hpos1 : outStart - 1 + 1 = outStart := by dsimp only [outStart]; omega
          rw [hpos1]
          exact hacc.frame fun a hlo hhi =>
            Function.update_of_ne (by dsimp only [outStart] at hlo ⊢; omega) v t.mem
        have hdedup_eq : dedupStepPure args.x v acc = v :: acc := by
          unfold dedupStepPure; exact ite_eq_right hcond
        rw [hdedup_eq] at hW_cur ⊢
        obtain ⟨hv_i, hfr_i, hpres_i, hst_i, hlen_i, hle_i, hholds_i, hcost_i⟩ :=
          ih (v :: acc) t₁ hwf₁ hfr hpres₁ (by omega) hys'_h (by simp; omega) hW_cur hacc₁
        rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
          hstep_st, hstep_res, memoryCost_bind', hstep_st, hstep_res]
        refine ⟨validHistory_bind_step hstep_val (by simpa [hstep_st, hstep_res] using hv_i),
          hfr_i, hpres_i, hst_i, hlen_i, hle_i, hholds_i, ?_⟩
        calc memoryCost _ t + _
            ≤ (2 + W_out) + ys'.length * (2 + W_out) := Nat.add_le_add hstep_cost hcost_i
          _ = (ys'.length + 1) * (2 + W_out) := by ring
  obtain ⟨hv_l, hfr_l, hpres_l, hst_l, hlen_l, hle_l, hholds_l, hcost_l⟩ :=
    hloop flat [] s₀ hwf₀ rfl ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩
      hflat.1 hflat.2 (by simp [hlen]) hW (Block.holdsList_nil _ _)
  simp only [List.length_nil, Nat.sub_zero] at hv_l hfr_l hpres_l hst_l hlen_l hholds_l hcost_l
  have ha_st : (Memory.spec 0).clientState s (Memory.allocDirty args.flatLen) = s₀ := rfl
  have ha_res : (Memory.spec 0).clientResult s (Memory.allocDirty args.flatLen) = outBuf := rfl
  have hpure_st {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientState u (pure x) = u := rfl
  have hpure_res {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientResult u (pure x) = x := rfl
  rw [← hlen]
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
  rw [hlen, ha_st, ha_res,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    hpure_res, hpure_st, ← hlen]
  refine ⟨validHistory_bind_step (by rw [hlen]; exact hv_a) ?_,
    by simpa [hlen] using hfr_l,
    by simpa [outBuf, hlen] using hpres_l,
    ?_,
    by simpa [hlen] using hlen_l, ?_, ?_⟩
  · rw [hlen, ha_st, ha_res]
    exact validHistory_bind_step (by simpa [hlen] using hv_l) (validHistory_pure w _ _)
  · have hst' : ((Memory.spec 0).clientResult s₀
        (iterate dedupBackStep (args.x, args.flatPtr) flat.length
          ⟨flat.length, outBuf + flat.length, 0⟩)).outStart =
        outBuf + flat.length - (flat.foldr (dedupStepPure args.x) []).length := by
      simpa [hlen] using hst_l
    have hle' : (flat.foldr (dedupStepPure args.x) []).length ≤ flat.length := by
      simpa [hlen] using hle_l
    dsimp only [outBuf] at hst' ⊢
    rw [hst']
    omega
  · refine ⟨?_, by simpa [hlen] using hholds_l⟩
    have hfr' : ((Memory.spec 0).clientState s₀
        (iterate dedupBackStep (args.x, args.flatPtr) flat.length
          ⟨flat.length, outBuf + flat.length, 0⟩)).frontier = outBuf + flat.length := by
      simpa [hlen] using hfr_l
    have hst' : ((Memory.spec 0).clientResult s₀
        (iterate dedupBackStep (args.x, args.flatPtr) flat.length
          ⟨flat.length, outBuf + flat.length, 0⟩)).outStart =
        outBuf + flat.length - (flat.foldr (dedupStepPure args.x) []).length := by
      simpa [hlen] using hst_l
    rw [hfr', hst']
    omega
  · rw [hlen, memoryCost_bind', memoryCost_allocDirty, ha_st, ha_res,
      memoryCost_bind', memoryCost_pure, Nat.add_zero]
    have hc' : memoryCost (iterate dedupBackStep (args.x, args.flatPtr) args.flatLen
        ⟨args.flatLen, outBuf + args.flatLen, 0⟩) s₀ ≤ args.flatLen * (2 + W_out) := by
      simpa [hlen] using hcost_l
    rw [← hlen] at hc' ⊢
    omega

private theorem bool_rec_reflects {p : Prop} {b : Bool} (hr : b.Reflects p)
    {f : false.Reflects p → Prop} {t : true.Reflects p → Prop}
    (hf : ∀ h, f h) (ht : ∀ h, t h) :
    Bool.rec (motive := fun x => x.Reflects p → Prop) f t b hr := by
  cases b
  · exact hf hr
  · exact ht hr

private theorem dedupFilterBack_realizes :
    Realizes .exact dedupFilterBack WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 1 ∧ args.flatPtr + args.flatLen ≤ s.frontier ∧
        Fits w (s.frontier + args.flatLen))
      (fun _ _ => 0) := by
  unfold dedupFilterBack
  realize [memScan_realizes]
  · exact h.2.2
  · obtain ⟨h1, hflat_b, hfit⟩ := h
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : DedupState) (_ : Memory.State) =>
        st.remPos = j ∧
        st.outStart + st.outLen = s.frontier + d.flatLen ∧
        s.frontier + j ≤ st.outStart)
      (fun j st t ⟨hrem, hsum, hlo⟩ => ?_)
      ⟨rfl, Nat.add_zero _, le_rfl⟩
    dsimp only
    have hr_t (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
    have hres_t (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
    refine ⟨?_, ?_⟩
    · refine ⟨⟨by omega, hfit.of_le (by omega)⟩, ⟨h1, hfit.of_le (by omega)⟩, ?_⟩
      refine bool_rec_reflects _ (fun _ => ⟨h1, ?_⟩) (fun _ => by omega)
      split_ifs
      · omega
      · exact ⟨by omega, ⟨by omega, by omega⟩, hfit.of_le (by omega)⟩
    · unfold dedupBackStep
      dsimp only
      rw [StateTransitionSpec.clientResult_bind, hr_t, hres_t,
        StateTransitionSpec.clientResult_bind, memScan_state]
      have hpure_res {α : Type} (x : α) (u : Memory.State) :
          (Memory.spec 0).clientResult u (pure x) = x := rfl
      split_ifs
      · rw [hpure_res]; dsimp only; exact ⟨by omega, hsum, by omega⟩
      · rw [StateTransitionSpec.clientResult_bind, hpure_res]
        dsimp only
        exact ⟨by omega, by omega, by omega⟩

/-- Arguments `(x, bucketPtr, bucketLen)` for `buildOutScope`. -/
structure BuildOutScopeArgs where
  /-- Field `x` of `BuildOutScopeArgs`. -/
  x : ℕ
  /-- Field `bucketPtr` of `BuildOutScopeArgs`. -/
  bucketPtr : ℕ
  /-- Field `bucketLen` of `BuildOutScopeArgs`. -/
  bucketLen : ℕ

/-- Product equivalence encoding `BuildOutScopeArgs` as words. -/
@[expose] def BuildOutScopeArgs.equiv : BuildOutScopeArgs ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.x, s.bucketPtr), s.bucketLen)
  invFun := fun ((x, bucketPtr), bucketLen) => ⟨x, bucketPtr, bucketLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding BuildOutScopeArgs := .ofEquiv BuildOutScopeArgs.equiv

/-- Materialize the deduplicated output scope `bucketOutScope x bucket`. -/
def buildOutScope (args : BuildOutScopeArgs) : Memory.Prog (ℕ × ℕ) :=
  sumScopeLen ⟨args.bucketPtr, args.bucketLen⟩ >>= fun flatLen =>
  flattenScopes ⟨args.bucketPtr, args.bucketLen, flatLen⟩ >>= fun flatPtr =>
  dedupFilterBack ⟨args.x, flatPtr, flatLen⟩

theorem buildOutScope_spec {w : ℕ} {args : BuildOutScopeArgs}
    {bucket : List (FactorTable ℕ ℕ)} {maxScope W_out : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hb : HoldsFactorList args.bucketPtr bucket s) (hlen : bucket.length = args.bucketLen)
    (hmax : ∀ f ∈ bucket, f.scope.length ≤ maxScope)
    (hW : (bucketOutScope args.x bucket).length ≤ W_out)
    (hfit : Fits w (s.frontier + 2 * (args.bucketLen * maxScope))) :
    let res := (Memory.spec 0).clientResult s (buildOutScope args)
    let s' := (Memory.spec 0).clientState s (buildOutScope args)
    let outScope := bucketOutScope args.x bucket
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (buildOutScope args)) ∧
      s'.frontier ≤ s.frontier + 2 * (args.bucketLen * maxScope) ∧
      PreservesBelow s.frontier s s' ∧
      s.frontier ≤ res.1 ∧
      res.2 = outScope.length ∧
      HoldsIn res.1 outScope s' ∧
      memoryCost (buildOutScope args) s ≤
        2 + args.bucketLen * (3 + 2 * maxScope + maxScope * (2 + W_out)) := by
  dsimp only
  unfold buildOutScope
  let flat := bucket.flatMap FactorTable.scope
  let K := flat.length
  have hK_le : K ≤ args.bucketLen * maxScope := by
    rw [← hlen]
    dsimp only [K, flat]
    rw [List.length_flatMap]
    have hsum := List.sum_le_length_nsmul (bucket.map fun a => a.scope.length) maxScope
      fun _ hn => by
        rcases List.mem_map.mp hn with ⟨f, hf, rfl⟩
        exact hmax f hf
    simpa [smul_eq_mul] using hsum
  have hss_val := sumScopeLen_valid (w := w) (args := ⟨args.bucketPtr, args.bucketLen⟩) hb hlen
  have hss_st := sumScopeLen_state ⟨args.bucketPtr, args.bucketLen⟩ s
  have hss_res : (Memory.spec 0).clientResult s (sumScopeLen ⟨args.bucketPtr, args.bucketLen⟩) =
      K := sumScopeLen_result hb hlen
  have hss_cost := sumScopeLen_cost ⟨args.bucketPtr, args.bucketLen⟩ s
  obtain ⟨hfl_val, hfl_fr, hfl_pres, hfl_res, hfl_holds, hfl_cost⟩ :=
    flattenScopes_spec (w := w) (args := ⟨args.bucketPtr, args.bucketLen, K⟩) hwf hb hlen rfl hmax
      (hfit.of_le (by dsimp only; omega))
  let s₁ := (Memory.spec 0).clientState s (flattenScopes ⟨args.bucketPtr, args.bucketLen, K⟩)
  have hwf₁ : Memory.WellFormed w s₁ := wellFormed_clientState hwf hfl_val
  have hW_foldr : (flat.foldr (dedupStepPure args.x) []).length ≤ W_out := by
    rw [← bucketOutScope_eq_foldr]; exact hW
  obtain ⟨hdd_val, hdd_fr, hdd_pres, hdd_lo, hdd_len, hdd_holds, hdd_cost⟩ :=
    dedupFilterBack_spec (w := w) (args := ⟨args.x, s.frontier, K⟩) hwf₁
      (by simpa [hfl_res] using hfl_holds) rfl hW_foldr
      (hfit.of_le (by
        change s₁.frontier + K ≤ s.frontier + 2 * (args.bucketLen * maxScope)
        have h1 : s₁.frontier = s.frontier + K := hfl_fr
        rw [h1]; omega))
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    hss_st, hss_res,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    hfl_res, bucketOutScope_eq_foldr]
  refine ⟨validHistory_bind_step hss_val ?_, ?_, hfl_pres.trans (hdd_pres.mono_bound hfl_pres.2.1),
    hfl_pres.2.1.trans hdd_lo, hdd_len, hdd_holds, ?_⟩
  · rw [hss_st, hss_res]
    refine validHistory_bind_step hfl_val ?_
    rw [hfl_res]
    exact hdd_val
  · change ((Memory.spec 0).clientState s₁ (dedupFilterBack ⟨args.x, s.frontier, K⟩)).frontier ≤
        s.frontier + 2 * (args.bucketLen * maxScope)
    have h1 : s₁.frontier = s.frontier + K := hfl_fr
    have h2 : ((Memory.spec 0).clientState s₁
        (dedupFilterBack ⟨args.x, s.frontier, K⟩)).frontier = s₁.frontier + K := hdd_fr
    rw [h2, h1]
    omega
  · rw [memoryCost_bind', hss_st, hss_res, memoryCost_bind', hfl_res]
    dsimp only at hss_cost hfl_cost hdd_cost
    have hdd_le : K * (2 + W_out) ≤ args.bucketLen * maxScope * (2 + W_out) :=
      Nat.mul_le_mul_right _ hK_le
    calc memoryCost (sumScopeLen ⟨args.bucketPtr, args.bucketLen⟩) s +
          (memoryCost (flattenScopes ⟨args.bucketPtr, args.bucketLen, K⟩) s +
            memoryCost (dedupFilterBack ⟨args.x, s.frontier, K⟩) s₁)
        ≤ args.bucketLen + ((1 + args.bucketLen * (2 + 2 * maxScope)) +
            (1 + args.bucketLen * maxScope * (2 + W_out))) :=
          Nat.add_le_add hss_cost (Nat.add_le_add hfl_cost (by omega))
      _ = 2 + args.bucketLen * (3 + 2 * maxScope + maxScope * (2 + W_out)) := by ring

theorem buildOutScope_realizes :
    Realizes .exact buildOutScope WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 1 ∧
        ∃ bucket, bucket.length = args.bucketLen ∧ HoldsFactorList args.bucketPtr bucket s ∧
          Fits w (s.frontier + 2 * (bucket.flatMap FactorTable.scope).length))
      (fun _ _ => 0) := by
  unfold buildOutScope
  realize [sumScopeLen_realizes, flattenScopes_realizes, dedupFilterBack_realizes]
  · obtain ⟨_, bucket, hlen, hb, hfit⟩ := h
    exact ⟨bucket, hlen, hb, hfit.of_le (by omega)⟩
  · obtain ⟨_, bucket, hlen, hb, hfit⟩ := h
    rw [sumScopeLen_state, sumScopeLen_result hb hlen]
    exact hfit.of_le (by omega)
  · obtain ⟨_, bucket, hlen, hb, _⟩ := h
    rw [sumScopeLen_state, sumScopeLen_result hb hlen]
    exact ⟨bucket, hlen, hb, rfl⟩
  · exact h.1
  · obtain ⟨_, bucket, hlen, hb, hfit⟩ := h
    let K := (bucket.flatMap FactorTable.scope).length
    have hscK : ∀ f ∈ bucket, f.scope.length ≤ K := fun f hf => by
      dsimp only [K]
      rw [List.length_flatMap]
      exact List.le_sum_of_mem
        (List.mem_map_of_mem (f := fun g : FactorTable ℕ ℕ => g.scope.length) hf)
    rw [sumScopeLen_state, sumScopeLen_result hb hlen]
    obtain ⟨_, hfl_fr, _, hfl_res, _, _⟩ :=
      flattenScopes_spec (w := w) (args := ⟨d.bucketPtr, d.bucketLen, K⟩) hmem hb hlen rfl
        hscK (hfit.of_le (by dsimp only [K]; omega))
    rw [hfl_res, hfl_fr]
  · obtain ⟨_, bucket, hlen, hb, hfit⟩ := h
    let K := (bucket.flatMap FactorTable.scope).length
    have hscK : ∀ f ∈ bucket, f.scope.length ≤ K := fun f hf => by
      dsimp only [K]
      rw [List.length_flatMap]
      exact List.le_sum_of_mem
        (List.mem_map_of_mem (f := fun g : FactorTable ℕ ℕ => g.scope.length) hf)
    rw [sumScopeLen_state, sumScopeLen_result hb hlen]
    obtain ⟨_, hfl_fr, _, _, _, _⟩ :=
      flattenScopes_spec (w := w) (args := ⟨d.bucketPtr, d.bucketLen, K⟩) hmem hb hlen rfl
        hscK (hfit.of_le (by dsimp only [K]; omega))
    rw [hfl_fr]
    exact hfit.of_le (by dsimp only [K]; omega)

end Cslib.Algorithms.WordRAM.VariableElimination
