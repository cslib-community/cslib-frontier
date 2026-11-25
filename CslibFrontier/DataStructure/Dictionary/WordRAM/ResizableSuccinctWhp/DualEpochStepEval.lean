/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvBase
-- Unfolds control/tick/step programs to expose pure state/result/cost equations.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochTable
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochProgs
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochCtrlBase
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochCtrl
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochStep

/-!
# Background Tick and Post-Randomization Program Evaluation Equations (`DualEpochStepEval`)

Exposes pure `clientState`, `clientResult`, and `memoryCost` equations for `DualEpochCtrl` and
`DualEpochStep` programs so `DualEpochInv` requires zero `import all` on control modules.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: `DualEpochCtrlBase` Slot-I/O & Context Loader Equations -/

/-- Evaluates `setDirectSlotIoProg` in terms of `setSlotIoProg` and `directSlotIo`. -/
theorem setDirectSlotIoProg_eval (base pBase ib qb nc : ℕ) (s : Memory.State) :
    let io := directSlotIo (s.mem (base + hdrW)) (s.mem (base + hdrValBits)) base ib qb nc
    (Memory.spec 0).clientState s (setDirectSlotIoProg ((base, pBase), ((ib, qb), nc))) =
      (Memory.spec 0).clientState s (setSlotIoProg (pBase, io.toCtx)) ∧
    memoryCost (setDirectSlotIoProg ((base, pBase), ((ib, qb), nc))) s = 15 := by
  dsimp only [directSlotIo, SlotIoLayout.toCtx, PageArenaLayout.toCtx]
  unfold setDirectSlotIoProg
  iterate 2 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 2 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [memoryCost_setSlotIoProg]
  exact ⟨rfl, rfl⟩

/-- Evaluates `setSplitSlotIoProg` in terms of `setSlotIoProg` and `splitSlotIo`. -/
theorem setSplitSlotIoProg_eval (base pBase nc : ℕ) (s : Memory.State) :
    let io := splitSlotIo (s.mem (base + hdrW)) (s.mem (base + hdrValBits)) base
      (s.mem (base + hdrItemLo)) (s.mem (base + hdrQLo))
      (s.mem (base + hdrItemHi)) (s.mem (base + hdrQHi)) nc
    (Memory.spec 0).clientState s (setSplitSlotIoProg ((base, pBase), nc)) =
      (Memory.spec 0).clientState s (setSlotIoProg (pBase, io.toCtx)) ∧
    memoryCost (setSplitSlotIoProg ((base, pBase), nc)) s = 19 := by
  dsimp only [splitSlotIo, SlotIoLayout.toCtx, PageArenaLayout.toCtx]
  unfold setSplitSlotIoProg
  iterate 6 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 6 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [memoryCost_setSlotIoProg]
  exact ⟨rfl, rfl⟩

/-- Evaluates `loadSplitPairCtxProg` state, `SplitPairCtx` result, and `memoryCost = 6`. -/
theorem loadSplitPairCtxProg_eval (base : ℕ) (s : Memory.State) :
    let cfg : SplitPairCfg :=
      { baseLo := s.mem (base + hdrItemLo)
        qBitsLo := s.mem (base + hdrQLo)
        vBitsLo := s.mem (base + hdrValBits)
        baseHi := s.mem (base + hdrItemHi)
        qBitsHi := s.mem (base + hdrQHi)
        vBitsHi := s.mem (base + hdrValBits)
        w := s.mem (base + hdrW) }
    (Memory.spec 0).clientState s (loadSplitPairCtxProg base) = s ∧
    (Memory.spec 0).clientResult s (loadSplitPairCtxProg base) = cfg.toCtx ∧
    memoryCost (loadSplitPairCtxProg base) s = 6 := by
  dsimp only [SplitPairCfg.toCtx]
  unfold loadSplitPairCtxProg
  iterate 6 rw [prog_clientResult_bind, cstate_rd, cres_rd]
  iterate 6 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [memoryCost_pure]
  exact ⟨clientState_loadSplitPairCtxProg base s, rfl, rfl⟩

/-- Evaluates `loadHostCtxProg` state, `PageArenaCtx` result, and `memoryCost = 14`. -/
theorem loadHostCtxProg_eval (base metaOnly : ℕ) (s : Memory.State) :
    let stg := s.mem (base + hdrStage)
    let nSrc := s.mem (base + hdrNSrc)
    let nDst := s.mem (base + hdrNDst)
    let pad := s.mem (base + hdrPad)
    let off0 := if nDst = 0 then hdrSrcOd else hdrDstOd
    let mbHost := if nDst = 0 then base + 192
      else if stg = 0 then base + 192 + pad else base + 192
    let nHost := if nDst = 0 then nSrc else nDst
    let qv := if metaOnly = 0 then (s.mem (base + hdrQHi), s.mem (base + hdrValBits)) else (0, 0)
    let nc := if metaOnly = 0 then s.mem (base + hdrLive) else nHost
    (Memory.spec 0).clientState s (loadHostCtxProg (base, metaOnly)) = s ∧
    (Memory.spec 0).clientResult s (loadHostCtxProg (base, metaOnly)) =
      ((((mbHost, s.mem (base + off0)), (s.mem (base + off0 + 1), s.mem (base + off0 + 2))),
        ((s.mem (base + hdrW), s.mem (base + off0 + 3)),
          (s.mem (base + off0 + 4), s.mem (base + hdrItemHi)))),
       (qv, nc)) ∧
    memoryCost (loadHostCtxProg (base, metaOnly)) s = 14 := by
  dsimp only
  have hst := clientState_loadHostCtxProg (base, metaOnly) s
  unfold loadHostCtxProg
  rw [prog_clientResult_bind, clientState_loadHostPartAProg,
    Realization.memoryCost_bind', clientState_loadHostPartAProg]
  have hpA :
      (Memory.spec 0).clientResult s (loadHostPartAProg base) =
        (((s.mem (base + hdrW), s.mem (base + hdrValBits)), s.mem (base + hdrLive)),
         ((if s.mem (base + hdrNDst) = 0 then base + 192
           else if s.mem (base + hdrStage) = 0 then base + 192 + s.mem (base + hdrPad)
           else base + 192,
           if s.mem (base + hdrNDst) = 0 then s.mem (base + hdrNSrc) else s.mem (base + hdrNDst)),
          if s.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd)) ∧
      memoryCost (loadHostPartAProg base) s = 7 := by
    unfold loadHostPartAProg
    iterate 7 rw [prog_clientResult_bind, cstate_rd, cres_rd]
    iterate 7 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
    iterate 4 rw [prog_clientResult_bind, clientState_selectEq0Prog, clientResult_selectEq0Prog]
    iterate 4 rw [Realization.memoryCost_bind', memoryCost_selectEq0Prog, clientState_selectEq0Prog,
      clientResult_selectEq0Prog]
    rw [memoryCost_pure]
    exact ⟨rfl, rfl⟩
  rw [hpA.1, hpA.2]
  unfold loadHostPartBProg; dsimp only
  iterate 7 rw [prog_clientResult_bind, cstate_rd, cres_rd]
  iterate 7 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [prog_clientResult_bind, clientState_selectEq0PairProg, clientResult_selectEq0PairProg,
    prog_clientResult_bind, clientState_selectEq0Prog, clientResult_selectEq0Prog,
    Realization.memoryCost_bind', memoryCost_selectEq0PairProg, clientState_selectEq0PairProg,
    clientResult_selectEq0PairProg,
    Realization.memoryCost_bind', memoryCost_selectEq0Prog, clientState_selectEq0Prog,
    clientResult_selectEq0Prog, memoryCost_pure]
  exact ⟨hst, rfl, rfl⟩

/-! ## Section 2: Per-Phase Tick Evaluation Equations (`0..10`) -/

/-- Evaluates Phase `0` (`tickIdleProg`). -/
theorem tickIdleProg_eval (base : ℕ) (s : Memory.State) :
    let nSrc := s.mem (base + hdrNSrc)
    let ops' := if nSrc = 0 then 0 else s.mem (base + hdrEpochOps) + 1
    let s1 : Memory.State :=
      { mem := Function.update s.mem (base + hdrEpochOps) ops', frontier := s.frontier }
    let tr := (Memory.spec 0).clientResult s1 (checkTriggerProg base)
    let m_base := Function.update (Function.update
      (Function.update s1.mem (base + hdrNDst) tr.2) (base + hdrStage) 0) (base + hdrEpochOps) 0
    let m_out :=
      if tr.1 = 0 then s1.mem
      else if tr.2 = 0 then
        Function.update (Function.update (Function.update (Function.update
          (Function.update m_base (base + hdrMDst) 0)
            (base + hdrPad) (s.mem (base + hdrMSrc)))
            (base + hdrItemHi) (base + 196 + s.mem (base + hdrMSrc)))
            (base + hdrQHi) (s.mem (base + hdrKeyBits)))
            (base + hdrPhase) 2
      else
        Function.update (Function.update (Function.update
          (Function.update m_base (base + hdrLogSub) 0)
            (base + hdrLogAcc) tr.2)
            (base + hdrLogK) 0)
            (base + hdrPhase) 1
    (Memory.spec 0).clientState s (tickIdleProg base) =
      { mem := m_out, frontier := s.frontier } ∧
    memoryCost (tickIdleProg base) s ≤ 20 := by
  dsimp only
  set nSrc := s.mem (base + hdrNSrc)
  set ops' := if nSrc = 0 then 0 else s.mem (base + hdrEpochOps) + 1
  set s1 : Memory.State :=
    { mem := Function.update s.mem (base + hdrEpochOps) ops', frontier := s.frontier }
  have hinc : (Memory.spec 0).clientState s (incEpochOpsProg (base, nSrc)) = s1 ∧
      memoryCost (incEpochOpsProg (base, nSrc)) s ≤ 2 := by
    unfold incEpochOpsProg; dsimp only [s1, ops']
    by_cases h0 : nSrc = 0
    · rw [ite_eq_left h0, ite_eq_left h0, cstate_wr, mcost_wr]
      exact ⟨rfl, by omega⟩
    · rw [ite_eq_right h0, ite_eq_right h0, StateTransitionSpec.clientState_bind, cstate_rd,
        cres_rd, cstate_wr, Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd, mcost_wr]
      exact ⟨rfl, by omega⟩
  have hct_mc : memoryCost (checkTriggerProg base) s1 = 5 := by
    unfold checkTriggerProg
    iterate 5 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
    rw [Realization.memoryCost_bind', memoryCost_capDoubleProg, clientState_capDoubleProg,
      Realization.memoryCost_bind', memoryCost_selectEq0Prog, clientState_selectEq0Prog,
      memoryCost_decideTriggerProg]
  unfold tickIdleProg
  rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd,
    StateTransitionSpec.clientState_bind, hinc.1,
    StateTransitionSpec.clientState_bind, clientState_checkTriggerProg,
    Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd,
    Realization.memoryCost_bind', hinc.1,
    Realization.memoryCost_bind', hct_mc, clientState_checkTriggerProg]
  set tr := (Memory.spec 0).clientResult s1 (checkTriggerProg base)
  have hc_inc := hinc.2; dsimp only [nSrc] at hc_inc
  by_cases htr0 : tr.1 = 0
  · rw [ite_eq_left htr0, ite_eq_left htr0, memoryCost_pure]
    exact ⟨rfl, by omega⟩
  · rw [ite_eq_right htr0, ite_eq_right htr0]
    iterate 3 rw [StateTransitionSpec.clientState_bind, cstate_wr]
    iterate 3 rw [Realization.memoryCost_bind', mcost_wr, cstate_wr]
    dsimp only
    by_cases htr2 : tr.2 = 0
    · rw [ite_eq_left htr2, ite_eq_left htr2]
      iterate 2 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
      iterate 2 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
      iterate 4 rw [StateTransitionSpec.clientState_bind, cstate_wr]
      iterate 4 rw [Realization.memoryCost_bind', mcost_wr, cstate_wr]
      rw [cstate_wr, mcost_wr]
      dsimp only [s1]
      have hmS : Function.update (Function.update (Function.update
          (Function.update s.mem (base + hdrEpochOps) ops')
          (base + hdrNDst) tr.2) (base + hdrStage) 0) (base + hdrEpochOps) 0 (base + hdrMSrc) =
          s.mem (base + hdrMSrc) := by
        unfold hdrMSrc hdrEpochOps hdrStage hdrNDst
        iterate 4 rw [Function.update_of_ne (by omega)]
      have hkb : Function.update (Function.update (Function.update
          (Function.update s.mem (base + hdrEpochOps) ops')
          (base + hdrNDst) tr.2) (base + hdrStage) 0) (base + hdrEpochOps) 0 (base + hdrKeyBits) =
          s.mem (base + hdrKeyBits) := by
        unfold hdrKeyBits hdrEpochOps hdrStage hdrNDst
        iterate 4 rw [Function.update_of_ne (by omega)]
      rw [hmS, hkb]
      exact ⟨rfl, by omega⟩
    · rw [ite_eq_right htr2, ite_eq_right htr2]
      iterate 3 rw [StateTransitionSpec.clientState_bind, cstate_wr]
      iterate 3 rw [Realization.memoryCost_bind', mcost_wr, cstate_wr]
      rw [cstate_wr, mcost_wr]
      exact ⟨rfl, by omega⟩

/-- Evaluates `calcLogDerivedProg (k, nDst)` when `k = Nat.log 2 nDst` and `2 ≤ nDst`. -/
private theorem calcLogDerivedProg_eval_of_log {nDst : ℕ} (hn : 2 ≤ nDst) (s : Memory.State) :
    let k := Nat.log 2 nDst
    (Memory.spec 0).clientState s (calcLogDerivedProg (k, nDst)) = s ∧
    (Memory.spec 0).clientResult s (calcLogDerivedProg (k, nDst)) =
      (Nat.clog 2 nDst, pageSizeWhp nDst) ∧
    memoryCost (calcLogDerivedProg (k, nDst)) s = 0 := by
  dsimp only
  set k := Nat.log 2 nDst
  have hn_pos : 0 < nDst := by omega
  have hk_ge1 : 1 ≤ k := Nat.le_log_of_pow_le Nat.one_lt_two (by omega)
  have hp_lo : 2 ^ k ≤ nDst := Nat.pow_log_le_self 2 hn_pos.ne'
  have hp_ge2 : 2 ≤ 2 ^ k := (by decide : 2 = 2 ^ 1) ▸ Nat.pow_le_pow_right (by decide) hk_ge1
  have hcl1 := clog_eq_of_log hn_pos
  have hcl2 := clog_add_two_eq_of_log hn_pos; dsimp only at hcl2
  have hcc : (Memory.spec 0).clientResult s (calcClogPairProg ((k, nDst), (1 : ℕ) <<< k)) =
      (Nat.clog 2 nDst, Nat.clog 2 (nDst + 2)) ∧
      memoryCost (calcClogPairProg ((k, nDst), (1 : ℕ) <<< k)) s = 0 := by
    unfold calcClogPairProg; dsimp only
    rw [shift_one_eq]
    by_cases heq : nDst = 2 ^ k
    · rw [ite_eq_left heq, hcl1, ite_eq_left heq, hcl2,
        ite_eq_right (by omega : nDst - 2 ^ k ≠ 2 ^ k - 1), memoryCost_pure]
      exact ⟨rfl, rfl⟩
    · rw [ite_eq_right heq, ite_eq_right (by omega : ¬(nDst < 2 ^ k)),
        ite_eq_right (by omega : ¬(2 ^ k < 1)), hcl1, ite_eq_right heq, hcl2]
      by_cases htop : nDst - 2 ^ k = 2 ^ k - 1
      · rw [ite_eq_left htop, ite_eq_left htop, memoryCost_pure]; exact ⟨rfl, rfl⟩
      · rw [ite_eq_right htop, ite_eq_right htop, memoryCost_pure]; exact ⟨rfl, rfl⟩
  refine ⟨clientState_calcLogDerivedProg _ s, ?_⟩
  unfold calcLogDerivedProg; dsimp only
  rw [prog_clientResult_bind, clientState_calcClogPairProg, hcc.1,
    prog_clientResult_bind, clientState_max2Prog, clientResult_max2Prog,
    Realization.memoryCost_bind', hcc.2, clientState_calcClogPairProg, hcc.1,
    Realization.memoryCost_bind', memoryCost_max2Prog, clientState_max2Prog, memoryCost_pure]
  exact ⟨rfl, rfl⟩

/-- Evaluates Phase `1` shift step (`tickLogShiftProg`). -/
theorem tickLogShiftProg_eval {base : ℕ} (s : Memory.State)
    (hn : 2 ≤ s.mem (base + hdrNDst))
    (hlog : ¬(1 < s.mem (base + hdrLogAcc)) → s.mem (base + hdrLogSub) = 0 →
      s.mem (base + hdrLogK) = Nat.log 2 (s.mem (base + hdrNDst))) :
    let sub := s.mem (base + hdrLogSub)
    let acc := s.mem (base + hdrLogAcc)
    let k := s.mem (base + hdrLogK)
    let nDst := s.mem (base + hdrNDst)
    (Memory.spec 0).clientState s (tickLogShiftProg base) =
      (if 1 < acc then
        { mem := Function.update (Function.update s.mem (base + hdrLogAcc) (acc / 2))
            (base + hdrLogK) (k + 1)
          frontier := s.frontier }
       else if sub = 0 then
        { mem := Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update
              (Function.update s.mem (base + hdrLogN) k)
              (base + hdrClogN) (Nat.clog 2 nDst))
              (base + hdrPtrB) (k + 1))
              (base + hdrPgB) (pageSizeWhp nDst))
              (base + hdrLogSub) 1)
              (base + hdrLogAcc) (Nat.clog 2 nDst - 1))
              (base + hdrLogK) 0
          frontier := s.frontier }
       else
        { mem := Function.update (Function.update s.mem (base + hdrEll) (k + 1))
            (base + hdrLogSub) 2
          frontier := s.frontier }) ∧
    memoryCost (tickLogShiftProg base) s ≤ 12 := by
  dsimp only
  have hmc_cl : ∀ k', memoryCost (calcLogDerivedProg (k', s.mem (base + hdrNDst))) s = 0 := by
    intro k'; unfold calcLogDerivedProg calcClogPairProg; dsimp only
    rw [Realization.memoryCost_bind',
      show memoryCost (if s.mem (base + hdrNDst) = (1 : ℕ) <<< k' then _ else _) s = 0 by
        split_ifs <;> rfl]
    simp
  unfold tickLogShiftProg
  iterate 4 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 4 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  by_cases hacc : 1 < s.mem (base + hdrLogAcc)
  · rw [ite_eq_left hacc, ite_eq_left hacc, StateTransitionSpec.clientState_bind, cstate_wr,
      cstate_wr, Realization.memoryCost_bind', mcost_wr, cstate_wr, mcost_wr]
    exact ⟨rfl, by omega⟩
  · rw [ite_eq_right hacc, ite_eq_right hacc]
    by_cases hsub : s.mem (base + hdrLogSub) = 0
    · have hk_eq := hlog hacc hsub
      have hcp := (calcLogDerivedProg_eval_of_log hn s).2.1
      rw [ite_eq_left hsub, ite_eq_left hsub,
        StateTransitionSpec.clientState_bind, clientState_calcLogDerivedProg,
        hk_eq, hcp,
        StateTransitionSpec.clientState_bind, clientState_clampSubProg, clientResult_clampSubProg,
        Realization.memoryCost_bind', hmc_cl, clientState_calcLogDerivedProg,
        Realization.memoryCost_bind', memoryCost_clampSubProg, clientState_clampSubProg,
        clientResult_clampSubProg]
      unfold writeLogSub0Prog; dsimp only
      iterate 6 rw [StateTransitionSpec.clientState_bind, cstate_wr]
      iterate 6 rw [Realization.memoryCost_bind', mcost_wr, cstate_wr]
      rw [cstate_wr, mcost_wr, ← hk_eq]
      exact ⟨rfl, by omega⟩
    · rw [ite_eq_right hsub, ite_eq_right hsub,
        StateTransitionSpec.clientState_bind, cstate_wr, cstate_wr,
        Realization.memoryCost_bind', mcost_wr, cstate_wr, mcost_wr]
      exact ⟨rfl, by omega⟩

/-- Evaluates Phase `1` finish step (`tickLogFinishProg`). -/
theorem tickLogFinishProg_eval (base : ℕ) (s : Memory.State) :
    let nDst := s.mem (base + hdrNDst)
    let logN := s.mem (base + hdrLogN)
    let ell := s.mem (base + hdrEll)
    let ptrB := s.mem (base + hdrPtrB)
    let pgB := s.mem (base + hdrPgB)
    let mSrc := s.mem (base + hdrMSrc)
    let kb := s.mem (base + hdrKeyBits)
    let qLo := s.mem (base + hdrQLo)
    let p1 := base + hdrPBase1
    let wlp := writeLargeParamTableProg
      ((base, p1), ((nDst, base + 192), ((logN, ell), pgB)))
    let s1 := (Memory.spec 0).clientState s wlp
    let res := (Memory.spec 0).clientResult s wlp
    let mDst := res.2
    let pad := max mSrc mDst
    let qHi := max qLo (kb - (logN - 12 * ell))
    let offFp := s1.mem (p1 + 30)
    let meta1 := base + 192 + pad
    (Memory.spec 0).clientState s (tickLogFinishProg base) =
      { mem := Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (Function.update
            (Function.update s1.mem (p1 + 1) meta1)
            (p1 + 61) (meta1 + 32))
            (p1 + 62) (meta1 + offFp))
            (base + hdrMDst) mDst)
            (base + hdrPad) pad)
            (base + hdrItemHi) (meta1 + mDst + 4))
            (base + hdrQHi) qHi)
            (base + hdrDstOd) (paramTableOd res))
            (base + hdrDstOt) (paramTableOt res))
            (base + hdrDstPb) ptrB)
            (base + hdrDstPg) pgB)
            (base + hdrDstMp) (nDst / pgB + 4))
            (base + hdrPhase) 2,
        frontier := s1.frontier } ∧
    memoryCost (tickLogFinishProg base) s = 22 + memoryCost wlp s := by
  dsimp only
  have hla_mc : memoryCost (loadLogFinishArgsProg base) s = 8 := by
    unfold loadLogFinishArgsProg
    iterate 8 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
    rw [memoryCost_pure]
  unfold tickLogFinishProg
  rw [StateTransitionSpec.clientState_bind, clientState_loadLogFinishArgsProg,
    clientResult_loadLogFinishArgsProg,
    Realization.memoryCost_bind', hla_mc, clientState_loadLogFinishArgsProg,
    clientResult_loadLogFinishArgsProg]
  dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  set s1 := (Memory.spec 0).clientState s _
  set res := (Memory.spec 0).clientResult s _
  rw [StateTransitionSpec.clientState_bind, clientState_max2Prog, clientResult_max2Prog,
    StateTransitionSpec.clientState_bind, clientState_clampSubProg, clientResult_clampSubProg,
    StateTransitionSpec.clientState_bind, clientState_clampSubProg, clientResult_clampSubProg,
    StateTransitionSpec.clientState_bind, clientState_max2Prog, clientResult_max2Prog,
    StateTransitionSpec.clientState_bind, cstate_rd, cres_rd,
    Realization.memoryCost_bind', memoryCost_max2Prog, clientState_max2Prog, clientResult_max2Prog,
    Realization.memoryCost_bind', memoryCost_clampSubProg, clientState_clampSubProg,
    clientResult_clampSubProg,
    Realization.memoryCost_bind', memoryCost_clampSubProg, clientState_clampSubProg,
    clientResult_clampSubProg,
    Realization.memoryCost_bind', memoryCost_max2Prog, clientState_max2Prog, clientResult_max2Prog,
    Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  unfold writeLogFinishHdrProg; dsimp only
  iterate 12 rw [StateTransitionSpec.clientState_bind, cstate_wr]
  iterate 12 rw [Realization.memoryCost_bind', mcost_wr, cstate_wr]
  rw [cstate_wr, mcost_wr]
  exact ⟨rfl, by omega⟩

/-- Evaluates Phase `1` dispatcher (`tickLogProg`). -/
theorem tickLogProg_eval (base : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (tickLogProg base) =
      (if s.mem (base + hdrLogSub) < 2 then
        (Memory.spec 0).clientState s (tickLogShiftProg base)
       else
        (Memory.spec 0).clientState s (tickLogFinishProg base)) ∧
    memoryCost (tickLogProg base) s =
      1 + (if s.mem (base + hdrLogSub) < 2 then memoryCost (tickLogShiftProg base) s
           else memoryCost (tickLogFinishProg base) s) := by
  unfold tickLogProg
  rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd,
    Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  by_cases h : s.mem (base + hdrLogSub) < 2 <;> simp [h]

/-- Evaluates Phase `2` (`tickGrowPreProg`) when `0 < s.mem (base + hdrW)`. -/
theorem tickGrowPreProg_eval {base newFr : ℕ} {s : Memory.State}
    (hw : 0 < s.mem (base + hdrW)) :
    let wv := s.mem (base + hdrW)
    let vb := s.mem (base + hdrValBits)
    let nLive := s.mem (base + hdrLive)
    let ibHi := s.mem (base + hdrItemHi)
    let qHi := s.mem (base + hdrQHi)
    let pw := pairStreamWords nLive qHi vb wv
    let s_sp : Memory.State :=
      { mem := Function.update s.mem (base + hdrSplit) nLive, frontier := s.frontier }
    let s_io := (Memory.spec 0).clientState s_sp
      (setSplitSlotIoProg ((base, base + hdrPBase0), nLive))
    (Memory.spec 0).clientState s (tickGrowPreProg (base, newFr)) =
      (if newFr < ibHi + pw then s
       else { mem := Function.update s_io.mem (base + hdrPhase) 3, frontier := s_io.frontier }) ∧
    memoryCost (tickGrowPreProg (base, newFr)) s ≤ 26 := by
  dsimp only
  have hps := pairStreamWordsSafeProg_spec (s.mem (base + hdrLive)) (s.mem (base + hdrQHi))
    (s.mem (base + hdrValBits)) (s.mem (base + hdrW)) hw s
  unfold tickGrowPreProg; dsimp only
  iterate 5 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 5 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [StateTransitionSpec.clientState_bind, hps.1, hps.2.1,
    Realization.memoryCost_bind', hps.2.2, hps.1, hps.2.1]
  by_cases hlt : newFr < s.mem (base + hdrItemHi) +
      pairStreamWords (s.mem (base + hdrLive)) (s.mem (base + hdrQHi))
        (s.mem (base + hdrValBits)) (s.mem (base + hdrW))
  · rw [ite_eq_left hlt, ite_eq_left hlt, memoryCost_pure]; exact ⟨rfl, by omega⟩
  · rw [ite_eq_right hlt, ite_eq_right hlt,
      StateTransitionSpec.clientState_bind, cstate_wr,
      StateTransitionSpec.clientState_bind, cstate_wr,
      Realization.memoryCost_bind', mcost_wr, cstate_wr,
      Realization.memoryCost_bind', (setSplitSlotIoProg_eval _ _ _ _).2, mcost_wr]
    exact ⟨rfl, by omega⟩

/-- Evaluates Phase `3` (`tickSlideUpProg`). -/
theorem tickSlideUpProg_eval (base : ℕ) (s : Memory.State) :
    let sp := s.mem (base + hdrSplit)
    let nLive := s.mem (base + hdrLive)
    let nDst := s.mem (base + hdrNDst)
    let ibHi := s.mem (base + hdrItemHi)
    let qHi := s.mem (base + hdrQHi)
    let ctx := (Memory.spec 0).clientResult s (loadSplitPairCtxProg base)
    let sb := slideUpBatchProg ((ctx, sp), itemBatchWhp)
    let s2 := (Memory.spec 0).clientState s sb
    let sp' := (Memory.spec 0).clientResult s sb
    let s3 : Memory.State :=
      { mem := Function.update s2.mem (base + hdrSplit) sp', frontier := s2.frontier }
    let s4 := (Memory.spec 0).clientState s3
      (setDirectSlotIoProg ((base, base + hdrPBase0), ((ibHi, qHi), nLive)))
    (Memory.spec 0).clientState s (tickSlideUpProg base) =
      (if sp' = 0 then
        if nDst = 0 then
          { mem := Function.update (Function.update (Function.update
              (Function.update s4.mem (base + hdrCur) 0)
              (base + hdrSmallMeta1) 0)
              (base + hdrSmallMeta1 + 1) 0)
              (base + hdrPhase) 6,
            frontier := s4.frontier }
        else
          { mem := Function.update (Function.update s4.mem (base + hdrCur) 0) (base + hdrPhase) 4,
            frontier := s4.frontier }
       else s3) ∧
    memoryCost (tickSlideUpProg base) s ≤ 32 + memoryCost sb s := by
  dsimp only
  have hctx := loadSplitPairCtxProg_eval base s
  unfold tickSlideUpProg
  iterate 5 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 5 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [StateTransitionSpec.clientState_bind, hctx.1,
    Realization.memoryCost_bind', hctx.2.2, hctx.1]
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  set sb := slideUpBatchProg
    (((Memory.spec 0).clientResult s (loadSplitPairCtxProg base), s.mem (base + hdrSplit)),
      itemBatchWhp)
  set s2 := (Memory.spec 0).clientState s sb
  set sp' := (Memory.spec 0).clientResult s sb
  rw [StateTransitionSpec.clientState_bind, cstate_wr,
    Realization.memoryCost_bind', mcost_wr, cstate_wr]
  by_cases h0 : sp' = 0
  · rw [ite_eq_left h0, ite_eq_left h0,
      StateTransitionSpec.clientState_bind,
      Realization.memoryCost_bind', (setDirectSlotIoProg_eval _ _ _ _ _ _).2,
      StateTransitionSpec.clientState_bind, cstate_wr,
      Realization.memoryCost_bind', mcost_wr, cstate_wr]
    by_cases hd0 : s.mem (base + hdrNDst) = 0
    · rw [ite_eq_left hd0, ite_eq_left hd0,
        StateTransitionSpec.clientState_bind, cstate_wr,
        StateTransitionSpec.clientState_bind, cstate_wr, cstate_wr,
        Realization.memoryCost_bind', mcost_wr, cstate_wr,
        Realization.memoryCost_bind', mcost_wr, cstate_wr, mcost_wr]
      exact ⟨rfl, by omega⟩
    · rw [ite_eq_right hd0, ite_eq_right hd0, cstate_wr, mcost_wr]
      exact ⟨rfl, by omega⟩
  · rw [ite_eq_right h0, ite_eq_right h0, memoryCost_pure]
    exact ⟨rfl, by omega⟩

/-- Evaluates Phase `4` (`tickZeroMetaProg`). -/
theorem tickZeroMetaProg_eval (base : ℕ) (s : Memory.State) :
    let stg := s.mem (base + hdrStage)
    let cur := s.mem (base + hdrCur)
    let mDst := s.mem (base + hdrMDst)
    let pad := s.mem (base + hdrPad)
    let nDst := s.mem (base + hdrNDst)
    let logN := s.mem (base + hdrLogN)
    let ell := s.mem (base + hdrEll)
    let pgB := s.mem (base + hdrPgB)
    let metaDst := if stg = 0 then base + 192 + pad else base + 192
    let zb := zeroWordsBatchProg (((metaDst, mDst), cur), bulkBatchWhp)
    let s1 := (Memory.spec 0).clientState s zb
    let cur' := (Memory.spec 0).clientResult s zb
    let wlp := writeLargeParamTableProg
      ((base, base + hdrPBase0), ((nDst, base + 192), ((logN, ell), pgB)))
    let s2 := if stg = 0 then s1 else (Memory.spec 0).clientState s1 wlp
    (Memory.spec 0).clientState s (tickZeroMetaProg base) =
      (if cur' < mDst then
        { mem := Function.update s1.mem (base + hdrCur) cur', frontier := s1.frontier }
       else
        { mem := Function.update (Function.update s2.mem (base + hdrCur) 32) (base + hdrPhase) 5,
          frontier := s2.frontier }) ∧
    memoryCost (tickZeroMetaProg base) s ≤
      11 + memoryCost zb s +
        (if cur' < mDst then 0 else if stg = 0 then 0 else memoryCost wlp s1) := by
  dsimp only
  unfold tickZeroMetaProg
  iterate 8 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 8 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [StateTransitionSpec.clientState_bind, clientState_metaDstAddrProg,
    clientResult_metaDstAddrProg,
    Realization.memoryCost_bind', memoryCost_metaDstAddrProg, clientState_metaDstAddrProg,
    clientResult_metaDstAddrProg]
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  set zb := zeroWordsBatchProg _
  set s1 := (Memory.spec 0).clientState s zb
  set cur' := (Memory.spec 0).clientResult s zb
  by_cases hlt : cur' < s.mem (base + hdrMDst)
  · rw [ite_eq_left hlt, ite_eq_left hlt, ite_eq_left hlt, cstate_wr, mcost_wr]
    exact ⟨rfl, by omega⟩
  · rw [ite_eq_right hlt, ite_eq_right hlt, ite_eq_right hlt,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
    unfold optWriteStageBTableProg; dsimp only
    set wlp := writeLargeParamTableProg _
    by_cases hst0 : s.mem (base + hdrStage) = 0
    · rw [ite_eq_left hst0, ite_eq_left hst0, ite_eq_left hst0, memoryCost_pure,
        show (Memory.spec 0).clientState s1 (pure ()) = s1 from rfl,
        StateTransitionSpec.clientState_bind, cstate_wr, cstate_wr,
        Realization.memoryCost_bind', mcost_wr, cstate_wr, mcost_wr]
      exact ⟨rfl, by omega⟩
    · rw [ite_eq_right hst0, ite_eq_right hst0, ite_eq_right hst0,
        StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState ((Memory.spec 0).clientState s1 wlp) (pure ()) =
          (Memory.spec 0).clientState s1 wlp from rfl,
        cstate_wr, cstate_wr,
        Realization.memoryCost_bind', memoryCost_pure,
        Realization.memoryCost_bind', mcost_wr, cstate_wr, mcost_wr]
      exact ⟨rfl, by omega⟩

/-- Evaluates Phase `5` (`tickRandPrepProg`). -/
theorem tickRandPrepProg_eval (base : ℕ) (s : Memory.State) :
    let wv := s.mem (base + hdrW)
    let stg := s.mem (base + hdrStage)
    let cur := s.mem (base + hdrCur)
    let pad := s.mem (base + hdrPad)
    let pDst := if stg = 0 then base + hdrPBase1 else base + hdrPBase0
    let metaDst := if stg = 0 then base + 192 + pad else base + 192
    let offBM := s.mem (pDst + 31)
    let endOff := cur + min bulkBatchWhp (offBM - cur)
    let rMask := (((1 : ℕ) <<< (wv - 1)) - 1) * 2 + 1
    (Memory.spec 0).clientState s (tickRandPrepProg base) =
      { mem := Function.update s.mem (base + hdrCur) endOff, frontier := s.frontier } ∧
    (Memory.spec 0).clientResult s (tickRandPrepProg base) =
      (metaDst + cur, (metaDst + endOff, rMask)) ∧
    memoryCost (tickRandPrepProg base) s = 6 := by
  dsimp only
  unfold tickRandPrepProg
  iterate 4 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 4 rw [prog_clientResult_bind, cstate_rd, cres_rd]
  iterate 4 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [StateTransitionSpec.clientState_bind, clientState_slotPairProg, clientResult_slotPairProg,
    prog_clientResult_bind, clientState_slotPairProg, clientResult_slotPairProg,
    Realization.memoryCost_bind', memoryCost_slotPairProg, clientState_slotPairProg,
    clientResult_slotPairProg]
  dsimp only
  rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd,
    prog_clientResult_bind, cstate_rd, cres_rd,
    Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd,
    StateTransitionSpec.clientState_bind, clientState_metaDstAddrProg, clientResult_metaDstAddrProg,
    prog_clientResult_bind, clientState_metaDstAddrProg, clientResult_metaDstAddrProg,
    Realization.memoryCost_bind', memoryCost_metaDstAddrProg, clientState_metaDstAddrProg,
    clientResult_metaDstAddrProg,
    StateTransitionSpec.clientState_bind, clientState_clampSubProg, clientResult_clampSubProg,
    prog_clientResult_bind, clientState_clampSubProg, clientResult_clampSubProg,
    Realization.memoryCost_bind', memoryCost_clampSubProg, clientState_clampSubProg,
    clientResult_clampSubProg,
    StateTransitionSpec.clientState_bind, clientState_min2Prog, clientResult_min2Prog,
    prog_clientResult_bind, clientState_min2Prog, clientResult_min2Prog,
    Realization.memoryCost_bind', memoryCost_min2Prog, clientState_min2Prog, clientResult_min2Prog]
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, cstate_wr, StateTransitionSpec.clientState_pure,
    prog_clientResult_bind, cstate_wr, prog_clientResult_pure,
    Realization.memoryCost_bind', mcost_wr, cstate_wr, memoryCost_pure]
  exact ⟨rfl, rfl, by omega⟩

/-- Evaluates Phase `6` (`tickInitDirProg`). -/
theorem tickInitDirProg_eval (base : ℕ) (s : Memory.State) :
    let cur := s.mem (base + hdrCur)
    let nLive := s.mem (base + hdrLive)
    let ctx := (Memory.spec 0).clientResult s (loadHostCtxProg (base, 1))
    let pgB := (PageArenaLayout.ofCtx ctx).pgB
    let mp := (PageArenaLayout.ofCtx ctx).maxPages
    let db := pageInitDirBatchProg ((ctx, cur), bulkBatchWhp)
    let s2 := (Memory.spec 0).clientState s db
    let cur' := (Memory.spec 0).clientResult s db
    let qSnap := if nLive < pgB + (pgB + pgB / 2) then 0 else (nLive - (pgB + pgB / 2)) / pgB
    (Memory.spec 0).clientState s (tickInitDirProg base) =
      (if cur' < mp then
        { mem := Function.update s2.mem (base + hdrCur) cur', frontier := s2.frontier }
       else
        { mem := Function.update (Function.update (Function.update
            (Function.update s2.mem (base + hdrNSnap) nLive)
            (base + hdrQSnap) qSnap)
            (base + hdrCur) 0)
            (base + hdrPhase) 7,
          frontier := s2.frontier }) ∧
    memoryCost (tickInitDirProg base) s ≤ 20 + memoryCost db s := by
  dsimp only
  have hhc := loadHostCtxProg_eval base 1 s
  unfold tickInitDirProg
  iterate 2 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 2 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [StateTransitionSpec.clientState_bind, hhc.1,
    Realization.memoryCost_bind', hhc.2.2, hhc.1]
  set ctx := (Memory.spec 0).clientResult s (loadHostCtxProg (base, 1))
  rw [StateTransitionSpec.clientState_bind, clientState_pageCtxScalarsProg,
    clientResult_pageCtxScalarsProg,
    Realization.memoryCost_bind', memoryCost_pageCtxScalarsProg, clientState_pageCtxScalarsProg,
    clientResult_pageCtxScalarsProg]
  dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  set db := pageInitDirBatchProg ((ctx, s.mem (base + hdrCur)), bulkBatchWhp)
  set s2 := (Memory.spec 0).clientState s db
  set cur' := (Memory.spec 0).clientResult s db
  by_cases hlt : cur' < (PageArenaLayout.ofCtx ctx).maxPages
  · rw [ite_eq_left hlt, ite_eq_left hlt, cstate_wr, mcost_wr]
    exact ⟨rfl, by omega⟩
  · rw [ite_eq_right hlt, ite_eq_right hlt]
    have hqs : (Memory.spec 0).clientResult s2
        (calcQSnapProg (s.mem (base + hdrLive), (PageArenaLayout.ofCtx ctx).pgB)) =
        (if s.mem (base + hdrLive) <
            (PageArenaLayout.ofCtx ctx).pgB +
              ((PageArenaLayout.ofCtx ctx).pgB + (PageArenaLayout.ofCtx ctx).pgB / 2)
         then 0
         else (s.mem (base + hdrLive) -
            ((PageArenaLayout.ofCtx ctx).pgB + (PageArenaLayout.ofCtx ctx).pgB / 2)) /
              (PageArenaLayout.ofCtx ctx).pgB) ∧
        memoryCost (calcQSnapProg (s.mem (base + hdrLive), (PageArenaLayout.ofCtx ctx).pgB)) s2 =
          0 := by
      unfold calcQSnapProg; dsimp only
      split_ifs <;> (rw [memoryCost_pure]; exact ⟨rfl, rfl⟩)
    rw [StateTransitionSpec.clientState_bind, clientState_calcQSnapProg, hqs.1,
      Realization.memoryCost_bind', hqs.2, clientState_calcQSnapProg, hqs.1]
    iterate 3 rw [StateTransitionSpec.clientState_bind, cstate_wr]
    iterate 3 rw [Realization.memoryCost_bind', mcost_wr, cstate_wr]
    rw [cstate_wr, mcost_wr]
    exact ⟨rfl, by omega⟩

/-- Evaluates Phase `7` completion (`finishInitTailProg`). -/
theorem finishInitTailProg_eval (base : ℕ) (s : Memory.State) :
    let stg := s.mem (base + hdrStage)
    let nDst := s.mem (base + hdrNDst)
    let nLive := s.mem (base + hdrLive)
    let qSnap := s.mem (base + hdrQSnap)
    let pgCtx := (Memory.spec 0).clientResult s (loadHostCtxProg (base, 0))
    let mb := (PageArenaLayout.ofCtx pgCtx).metaBase
    let pgB := (PageArenaLayout.ofCtx pgCtx).pgB
    let pSrc := if stg = 0 then base + hdrPBase0 else base + hdrPBase1
    let pDst := if stg = 0 then base + hdrPBase1 else base + hdrPBase0
    let s2 := (Memory.spec 0).clientState s
      (pageInitScalarsBandProg ((mb, pgB), (qSnap, nLive - qSnap * pgB)))
    let s3 := (Memory.spec 0).clientState s2 (setSlotIoProg (pSrc, ((1, 0), pgCtx)))
    let s4 := (Memory.spec 0).clientState s3
      (if nDst = 0 then writeSmallParamTableProg ((pDst, base + hdrSmallMeta1), ((1, 1), pgCtx))
       else setSlotIoProg (pDst, ((1, 1), pgCtx)))
    (Memory.spec 0).clientState s (finishInitTailProg base) =
      { mem := Function.update
          (Function.update s4.mem (base + hdrRem) (nLive / itemBatchWhp + 1))
          (base + hdrPhase) 8,
        frontier := s4.frontier } ∧
    memoryCost (finishInitTailProg base) s ≤ 65 := by
  dsimp only
  have hhc := loadHostCtxProg_eval base 0 s
  unfold finishInitTailProg
  iterate 4 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 4 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [StateTransitionSpec.clientState_bind, hhc.1,
    Realization.memoryCost_bind', hhc.2.2, hhc.1]
  set pgCtx := (Memory.spec 0).clientResult s (loadHostCtxProg (base, 0))
  rw [StateTransitionSpec.clientState_bind, clientState_pageCtxScalarsProg,
    clientResult_pageCtxScalarsProg,
    Realization.memoryCost_bind', memoryCost_pageCtxScalarsProg, clientState_pageCtxScalarsProg,
    clientResult_pageCtxScalarsProg]
  dsimp only; simp only [pure_bind]
  have hsb_mc := (pageInitScalarsBandProg_spec
    (PageArenaLayout.ofCtx pgCtx).metaBase (PageArenaLayout.ofCtx pgCtx).pgB
    (s.mem (base + hdrQSnap))
    (s.mem (base + hdrLive) - s.mem (base + hdrQSnap) * (PageArenaLayout.ofCtx pgCtx).pgB) s).2.1
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hsb_mc]
  set s2 := (Memory.spec 0).clientState s _
  rw [StateTransitionSpec.clientState_bind, clientState_slotPairProg, clientResult_slotPairProg,
    Realization.memoryCost_bind', memoryCost_slotPairProg, clientState_slotPairProg,
    clientResult_slotPairProg]
  dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', memoryCost_setSlotIoProg]
  set s3 := (Memory.spec 0).clientState s2 _
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  unfold initDstSlotIoProg; dsimp only
  have hid_mc : memoryCost
      (if s.mem (base + hdrNDst) = 0 then
        writeSmallParamTableProg
          ((if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0,
            base + hdrSmallMeta1), ((1, 1), pgCtx))
       else
        setSlotIoProg
          (if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0,
           ((1, 1), pgCtx))) s3 ≤ 15 := by
    by_cases hd0 : s.mem (base + hdrNDst) = 0
    · rw [ite_eq_left hd0]
      rcases pgCtx with ⟨⟨⟨⟨mb', od'⟩, ⟨ot', pb'⟩⟩, ⟨⟨wv', pg'⟩, ⟨mp', ib'⟩⟩⟩, ⟨⟨qb', vb'⟩, nc'⟩⟩
      have hm := (writeSmallParamTableProg_spec
        (if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0)
        ⟨base + hdrSmallMeta1, 0, 0,
          ⟨1, 1, ⟨mb', od', ot', pb', wv', pg', mp', ib', qb', vb', nc'⟩⟩⟩
        s3).2.1
      exact hm.le
    · rw [ite_eq_right hd0, memoryCost_setSlotIoProg]; omega
  rw [StateTransitionSpec.clientState_bind, cstate_wr, cstate_wr,
    Realization.memoryCost_bind', mcost_wr, cstate_wr, mcost_wr]
  exact ⟨rfl, by omega⟩

/-- Evaluates Phase `7` (`tickInitTailProg`). -/
theorem tickInitTailProg_eval (base : ℕ) (s : Memory.State) :
    let cur := s.mem (base + hdrCur)
    let nSnap := s.mem (base + hdrNSnap)
    let ctx := (Memory.spec 0).clientResult s (loadHostCtxProg (base, 1))
    let pgB := (PageArenaLayout.ofCtx ctx).pgB
    let tb := pageInitTailBatchProg (((ctx, nSnap), cur), tailBatchWhp)
    let s2 := (Memory.spec 0).clientState s tb
    let cur' := (Memory.spec 0).clientResult s tb
    (Memory.spec 0).clientState s (tickInitTailProg base) =
      (if cur' < 8 * pgB then
        { mem := Function.update s2.mem (base + hdrCur) cur', frontier := s2.frontier }
       else
        (Memory.spec 0).clientState s2 (finishInitTailProg base)) ∧
    memoryCost (tickInitTailProg base) s ≤ 82 + memoryCost tb s := by
  dsimp only
  have hhc := loadHostCtxProg_eval base 1 s
  unfold tickInitTailProg
  iterate 2 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 2 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [StateTransitionSpec.clientState_bind, hhc.1,
    Realization.memoryCost_bind', hhc.2.2, hhc.1]
  set ctx := (Memory.spec 0).clientResult s (loadHostCtxProg (base, 1))
  rw [StateTransitionSpec.clientState_bind, clientState_pageCtxScalarsProg,
    clientResult_pageCtxScalarsProg,
    Realization.memoryCost_bind', memoryCost_pageCtxScalarsProg, clientState_pageCtxScalarsProg,
    clientResult_pageCtxScalarsProg]
  dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  set tb := pageInitTailBatchProg (((ctx, s.mem (base + hdrNSnap)), s.mem (base + hdrCur)),
    tailBatchWhp)
  set s2 := (Memory.spec 0).clientState s tb
  set cur' := (Memory.spec 0).clientResult s tb
  by_cases hlt : cur' < 8 * (PageArenaLayout.ofCtx ctx).pgB
  · rw [ite_eq_left hlt, ite_eq_left hlt, cstate_wr, mcost_wr]
    exact ⟨rfl, by omega⟩
  · rw [ite_eq_right hlt, ite_eq_right hlt]
    have hfin := (finishInitTailProg_eval base s2).2
    exact ⟨rfl, by omega⟩

/-- Evaluates Phase `8` (`tickMigrateProg`). -/
theorem tickMigrateProg_eval (base : ℕ) (s : Memory.State) :
    let stg := s.mem (base + hdrStage)
    let rem := s.mem (base + hdrRem)
    let th := s.mem (base + hdrThresh)
    let nSrc := s.mem (base + hdrNSrc)
    let pSrc := if stg = 0 then base + hdrPBase0 else base + hdrPBase1
    let pDst := if stg = 0 then base + hdrPBase1 else base + hdrPBase0
    let mb := migrateBatchProg (((pSrc, pDst), 0), itemBatchWhp)
    let s1 := (Memory.spec 0).clientState s mb
    let pgCtx := (Memory.spec 0).clientResult s1 (loadHostCtxProg (base, 0))
    let pgB := (PageArenaLayout.ofCtx pgCtx).pgB
    let s3 := (Memory.spec 0).clientState s1 (pageBeginUnpermBoundedProg pgCtx)
    let uTicks := max th nSrc / 240 + pgB / 8 + 4
    (Memory.spec 0).clientState s (tickMigrateProg base) =
      (if 1 < rem then
        { mem := Function.update s1.mem (base + hdrRem) (rem - 1), frontier := s1.frontier }
       else
        { mem := Function.update (Function.update
            (Function.update s3.mem (base + hdrUnpermDone) 0)
            (base + hdrRem) uTicks)
            (base + hdrPhase) 9,
          frontier := s3.frontier }) ∧
    memoryCost (tickMigrateProg base) s ≤
      22 + memoryCost mb s +
        (if 1 < rem then 0 else memoryCost (pageBeginUnpermBoundedProg pgCtx) s1) := by
  dsimp only
  unfold tickMigrateProg
  iterate 4 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 4 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [StateTransitionSpec.clientState_bind, clientState_slotPairProg, clientResult_slotPairProg,
    Realization.memoryCost_bind', memoryCost_slotPairProg, clientState_slotPairProg,
    clientResult_slotPairProg]
  dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  set mb := migrateBatchProg _
  set s1 := (Memory.spec 0).clientState s mb
  by_cases h1 : 1 < s.mem (base + hdrRem)
  · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_left h1, cstate_wr, mcost_wr]
    exact ⟨rfl, by omega⟩
  · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right h1]
    have hhc := loadHostCtxProg_eval base 0 s1
    rw [StateTransitionSpec.clientState_bind, hhc.1,
      Realization.memoryCost_bind', hhc.2.2, hhc.1]
    set pgCtx := (Memory.spec 0).clientResult s1 (loadHostCtxProg (base, 0))
    rw [StateTransitionSpec.clientState_bind, clientState_pageCtxScalarsProg,
      clientResult_pageCtxScalarsProg,
      Realization.memoryCost_bind', memoryCost_pageCtxScalarsProg, clientState_pageCtxScalarsProg,
      clientResult_pageCtxScalarsProg]
    dsimp only
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
    set s3 := (Memory.spec 0).clientState s1 (pageBeginUnpermBoundedProg pgCtx)
    rw [StateTransitionSpec.clientState_bind, clientState_max2Prog, clientResult_max2Prog,
      Realization.memoryCost_bind', memoryCost_max2Prog, clientState_max2Prog,
      clientResult_max2Prog]
    simp only [pure_bind]
    iterate 2 rw [StateTransitionSpec.clientState_bind, cstate_wr]
    iterate 2 rw [Realization.memoryCost_bind', mcost_wr, cstate_wr]
    rw [cstate_wr, mcost_wr]
    exact ⟨rfl, by omega⟩

/-- Evaluates Phase `9` active batch (`stepUnpermBatchProg`). -/
theorem stepUnpermBatchProg_eval (base : ℕ) (s : Memory.State) :
    let stg := s.mem (base + hdrStage)
    let nLive := s.mem (base + hdrLive)
    let ibHi := s.mem (base + hdrItemHi)
    let qHi := s.mem (base + hdrQHi)
    let pgCtx := (Memory.spec 0).clientResult s (loadHostCtxProg (base, 0))
    let mb := (PageArenaLayout.ofCtx pgCtx).metaBase
    let pDst := if stg = 0 then base + hdrPBase1 else base + hdrPBase0
    let ub := pageRunUnpermBatchProg (pgCtx, itemBatchWhp)
    let s2 := (Memory.spec 0).clientState s ub
    let s3 := (Memory.spec 0).clientState s2
      (setDirectSlotIoProg ((base, pDst), ((ibHi, qHi), nLive)))
    (Memory.spec 0).clientState s (stepUnpermBatchProg base) =
      (if s2.mem (mb + 18) = 4 then
        { mem := Function.update s3.mem (base + hdrUnpermDone) 1, frontier := s3.frontier }
       else s2) ∧
    memoryCost (stepUnpermBatchProg base) s ≤ 36 + memoryCost ub s := by
  dsimp only
  have hhc := loadHostCtxProg_eval base 0 s
  unfold stepUnpermBatchProg
  iterate 4 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 4 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [StateTransitionSpec.clientState_bind, hhc.1,
    Realization.memoryCost_bind', hhc.2.2, hhc.1]
  set pgCtx := (Memory.spec 0).clientResult s (loadHostCtxProg (base, 0))
  rw [StateTransitionSpec.clientState_bind, clientState_pageCtxScalarsProg,
    clientResult_pageCtxScalarsProg,
    Realization.memoryCost_bind', memoryCost_pageCtxScalarsProg, clientState_pageCtxScalarsProg,
    clientResult_pageCtxScalarsProg]
  dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  set ub := pageRunUnpermBatchProg (pgCtx, itemBatchWhp)
  set s2 := (Memory.spec 0).clientState s ub
  rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd,
    Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  by_cases hcph : s2.mem ((PageArenaLayout.ofCtx pgCtx).metaBase + 18) = 4
  · rw [ite_eq_left hcph, ite_eq_left hcph,
      StateTransitionSpec.clientState_bind, clientState_slotPairProg, clientResult_slotPairProg,
      Realization.memoryCost_bind', memoryCost_slotPairProg, clientState_slotPairProg,
      clientResult_slotPairProg]
    dsimp only
    rw [StateTransitionSpec.clientState_bind, cstate_wr,
      Realization.memoryCost_bind', (setDirectSlotIoProg_eval _ _ _ _ _ _).2, mcost_wr]
    exact ⟨rfl, by omega⟩
  · rw [ite_eq_right hcph, ite_eq_right hcph, memoryCost_pure]
    exact ⟨rfl, by omega⟩

/-- Evaluates Phase `9` completion (`finishUnpermProg`). -/
theorem finishUnpermProg_eval (base : ℕ) (s : Memory.State) :
    let stg := s.mem (base + hdrStage)
    let nDst := s.mem (base + hdrNDst)
    let mDst := s.mem (base + hdrMDst)
    let nLive := s.mem (base + hdrLive)
    let kb := s.mem (base + hdrKeyBits)
    let logN := s.mem (base + hdrLogN)
    let ell := s.mem (base + hdrEll)
    let m_sm := if stg = 0 then
      Function.update (Function.update (Function.update
        (Function.update s.mem (base + hdrSmallMeta0) 0)
        (base + hdrSmallMeta0 + 1) nLive)
        (base + hdrPBase0) 0)
        (base + hdrPBase0 + 1) (base + hdrSmallMeta0)
      else s.mem
    let qLo := if nDst = 0 then kb else kb - (logN - 12 * ell)
    let s_pre : Memory.State :=
      { mem := Function.update (Function.update
          (Function.update m_sm (base + hdrItemLo) (base + 192 + mDst))
          (base + hdrQLo) qLo)
          (base + hdrSplit) 0,
        frontier := s.frontier }
    let s_sp := (Memory.spec 0).clientState s_pre
      (setSplitSlotIoProg ((base, base + hdrPBase0), nLive))
    (Memory.spec 0).clientState s (finishUnpermProg base) =
      (if stg = 0 ∧ 0 < nDst then
        { mem := Function.update (Function.update
            (Function.update s.mem (base + hdrStage) 1)
            (base + hdrCur) 0)
            (base + hdrPhase) 4,
          frontier := s.frontier }
       else
        { mem := Function.update s_sp.mem (base + hdrPhase) 10, frontier := s_sp.frontier }) ∧
    memoryCost (finishUnpermProg base) s ≤ 36 := by
  dsimp only
  unfold finishUnpermProg
  iterate 2 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 2 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  have hgo : (Memory.spec 0).clientResult s
      (isStageBNextProg (s.mem (base + hdrStage), s.mem (base + hdrNDst))) =
      (if s.mem (base + hdrStage) = 0 ∧ 0 < s.mem (base + hdrNDst) then 1 else 0) ∧
      memoryCost (isStageBNextProg (s.mem (base + hdrStage), s.mem (base + hdrNDst))) s = 0 := by
    unfold isStageBNextProg; dsimp only
    by_cases h0 : s.mem (base + hdrStage) = 0
    · rw [ite_eq_left h0]
      by_cases hd : 0 < s.mem (base + hdrNDst)
      · rw [ite_eq_left hd, ite_eq_left ⟨h0, hd⟩, memoryCost_pure]; exact ⟨rfl, rfl⟩
      · rw [ite_eq_right hd, ite_eq_right (fun h => hd h.2), memoryCost_pure]; exact ⟨rfl, rfl⟩
    · rw [ite_eq_right h0, ite_eq_right (fun h => h0 h.1), memoryCost_pure]; exact ⟨rfl, rfl⟩
  rw [StateTransitionSpec.clientState_bind, clientState_isStageBNextProg, hgo.1,
    Realization.memoryCost_bind', hgo.2, clientState_isStageBNextProg, hgo.1]
  by_cases hcond : s.mem (base + hdrStage) = 0 ∧ 0 < s.mem (base + hdrNDst)
  · simp only [hcond, and_self, ↓reduceIte, Realization.memoryCost_bind', mcost_wr]
    exact ⟨rfl, by omega⟩
  · simp only [hcond, ↓reduceIte, show (0 : ℕ) ≠ 1 by decide]
    unfold finishUnpermSlideProg
    iterate 7 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
    iterate 7 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
    have hos : (Memory.spec 0).clientState s
        (optInitSmallSlot0Prog (s.mem (base + hdrStage), (base, s.mem (base + hdrLive)))) =
        { mem := if s.mem (base + hdrStage) = 0 then
            Function.update (Function.update (Function.update
              (Function.update s.mem (base + hdrSmallMeta0) 0)
              (base + hdrSmallMeta0 + 1) (s.mem (base + hdrLive)))
              (base + hdrPBase0) 0)
              (base + hdrPBase0 + 1) (base + hdrSmallMeta0)
          else s.mem,
          frontier := s.frontier } ∧
        memoryCost
          (optInitSmallSlot0Prog (s.mem (base + hdrStage), (base, s.mem (base + hdrLive)))) s ≤
          4 := by
      unfold optInitSmallSlot0Prog; dsimp only
      by_cases hs0 : s.mem (base + hdrStage) = 0
      · simp only [hs0, ↓reduceIte, Realization.memoryCost_bind', mcost_wr]
        exact ⟨rfl, by omega⟩
      · simp only [hs0, ↓reduceIte, memoryCost_pure]
        exact ⟨rfl, by omega⟩
    rw [StateTransitionSpec.clientState_bind, hos.1,
      Realization.memoryCost_bind', hos.1]
    have hc_os := hos.2
    rw [StateTransitionSpec.clientState_bind, clientState_selectEq0Prog, clientResult_selectEq0Prog,
      StateTransitionSpec.clientState_bind, clientState_clampSubProg, clientResult_clampSubProg,
      StateTransitionSpec.clientState_bind, clientState_clampSubProg, clientResult_clampSubProg,
      StateTransitionSpec.clientState_bind, clientState_selectEq0Prog, clientResult_selectEq0Prog,
      Realization.memoryCost_bind', memoryCost_selectEq0Prog, clientState_selectEq0Prog,
      clientResult_selectEq0Prog,
      Realization.memoryCost_bind', memoryCost_clampSubProg, clientState_clampSubProg,
      clientResult_clampSubProg,
      Realization.memoryCost_bind', memoryCost_clampSubProg, clientState_clampSubProg,
      clientResult_clampSubProg,
      Realization.memoryCost_bind', memoryCost_selectEq0Prog, clientState_selectEq0Prog,
      clientResult_selectEq0Prog]
    have hq_if :
        (if s.mem (base + hdrNDst) = 0 then s.mem (base + hdrKeyBits)
         else s.mem (base + hdrKeyBits) -
           (s.mem (base + hdrLogN) -
             12 * (if s.mem (base + hdrNDst) = 0 then 0 else s.mem (base + hdrEll)))) =
        (if s.mem (base + hdrNDst) = 0 then s.mem (base + hdrKeyBits)
         else s.mem (base + hdrKeyBits) -
           (s.mem (base + hdrLogN) - 12 * s.mem (base + hdrEll))) := by
      split_ifs <;> rfl
    rw [hq_if]
    iterate 3 rw [StateTransitionSpec.clientState_bind, cstate_wr]
    iterate 3 rw [Realization.memoryCost_bind', mcost_wr, cstate_wr]
    rw [StateTransitionSpec.clientState_bind, cstate_wr,
      Realization.memoryCost_bind', (setSplitSlotIoProg_eval _ _ _ _).2, mcost_wr]
    exact ⟨rfl, by omega⟩

/-- Evaluates Phase `9` (`tickUnpermProg`). -/
theorem tickUnpermProg_eval (base : ℕ) (s : Memory.State) :
    let done := s.mem (base + hdrUnpermDone)
    let rem := s.mem (base + hdrRem)
    let s1 := if done = 0 then (Memory.spec 0).clientState s (stepUnpermBatchProg base) else s
    (Memory.spec 0).clientState s (tickUnpermProg base) =
      (if 1 < rem then
        { mem := Function.update s1.mem (base + hdrRem) (rem - 1), frontier := s1.frontier }
       else
        (Memory.spec 0).clientState s1 (finishUnpermProg base)) ∧
    memoryCost (tickUnpermProg base) s ≤
      39 + (if done = 0 then memoryCost (stepUnpermBatchProg base) s else 0) := by
  dsimp only
  unfold tickUnpermProg
  iterate 2 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 2 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  unfold optStepUnpermProg; dsimp only
  have hosp : (Memory.spec 0).clientState s
      (if s.mem (base + hdrUnpermDone) = 0 then stepUnpermBatchProg base else pure ()) =
      (if s.mem (base + hdrUnpermDone) = 0 then
        (Memory.spec 0).clientState s (stepUnpermBatchProg base)
       else s) ∧
      memoryCost
        (if s.mem (base + hdrUnpermDone) = 0 then stepUnpermBatchProg base else pure ()) s =
      (if s.mem (base + hdrUnpermDone) = 0 then memoryCost (stepUnpermBatchProg base) s else 0) :=
    by
    by_cases hd0 : s.mem (base + hdrUnpermDone) = 0
    · simp only [hd0, ↓reduceIte, and_self]
    · simp only [hd0, ↓reduceIte, prog_runClient_state_pure, memoryCost_pure, and_self]
  rw [hosp.1, hosp.2]
  set s1 := if s.mem (base + hdrUnpermDone) = 0 then
    (Memory.spec 0).clientState s (stepUnpermBatchProg base) else s
  by_cases h1 : 1 < s.mem (base + hdrRem)
  · rw [ite_eq_left h1, ite_eq_left h1, cstate_wr, mcost_wr]
    exact ⟨rfl, by omega⟩
  · rw [ite_eq_right h1, ite_eq_right h1]
    have hf := (finishUnpermProg_eval base s1).2
    exact ⟨rfl, by omega⟩

/-- Evaluates Phase `10` (`tickSlideDownProg`). -/
theorem tickSlideDownProg_eval (base : ℕ) (s : Memory.State) :
    let sp := s.mem (base + hdrSplit)
    let nLive := s.mem (base + hdrLive)
    let ibLo := s.mem (base + hdrItemLo)
    let qLo := s.mem (base + hdrQLo)
    let ctx := (Memory.spec 0).clientResult s (loadSplitPairCtxProg base)
    let sb := slideDownBatchProg (((ctx, nLive), sp), itemBatchWhp)
    let s2 := (Memory.spec 0).clientState s sb
    let sp' := (Memory.spec 0).clientResult s sb
    let s3 : Memory.State :=
      { mem := Function.update s2.mem (base + hdrSplit) sp', frontier := s2.frontier }
    let s4 := (Memory.spec 0).clientState s3
      (setDirectSlotIoProg ((base, base + hdrPBase0), ((ibLo, qLo), nLive)))
    (Memory.spec 0).clientState s (tickSlideDownProg base) =
      (if nLive ≤ sp' then
        { mem := Function.update s4.mem (base + hdrPhase) 11, frontier := s4.frontier }
       else s3) ∧
    memoryCost (tickSlideDownProg base) s ≤ 27 + memoryCost sb s := by
  dsimp only
  have hctx := loadSplitPairCtxProg_eval base s
  unfold tickSlideDownProg
  iterate 4 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 4 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [StateTransitionSpec.clientState_bind, hctx.1,
    Realization.memoryCost_bind', hctx.2.2, hctx.1]
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  set sb := slideDownBatchProg _
  set s2 := (Memory.spec 0).clientState s sb
  set sp' := (Memory.spec 0).clientResult s sb
  rw [StateTransitionSpec.clientState_bind, cstate_wr,
    Realization.memoryCost_bind', mcost_wr, cstate_wr]
  by_cases hle : s.mem (base + hdrLive) ≤ sp'
  · rw [ite_eq_left hle, ite_eq_left hle,
      StateTransitionSpec.clientState_bind, cstate_wr,
      Realization.memoryCost_bind', (setDirectSlotIoProg_eval _ _ _ _ _ _).2, mcost_wr]
    exact ⟨rfl, by omega⟩
  · rw [ite_eq_right hle, ite_eq_right hle, memoryCost_pure]
    exact ⟨rfl, by omega⟩

/-! ## Section 3: Top-Level Dispatcher & Post-Randomization Equations -/

/-- Evaluates `bgTickProg (base, newFr)` across phases `0..11`. -/
theorem bgTickProg_eval (base newFr : ℕ) (s : Memory.State) :
    let ph := s.mem (base + hdrPhase)
    (Memory.spec 0).clientState s (bgTickProg (base, newFr)) =
      (if ph = 0 then (Memory.spec 0).clientState s (tickIdleProg base)
       else if ph = 1 then (Memory.spec 0).clientState s (tickLogProg base)
       else if ph = 2 then (Memory.spec 0).clientState s (tickGrowPreProg (base, newFr))
       else if ph = 3 then (Memory.spec 0).clientState s (tickSlideUpProg base)
       else if ph = 4 then (Memory.spec 0).clientState s (tickZeroMetaProg base)
       else if ph = 5 then (Memory.spec 0).clientState s (tickRandPrepProg base)
       else if ph = 6 then (Memory.spec 0).clientState s (tickInitDirProg base)
       else if ph = 7 then (Memory.spec 0).clientState s (tickInitTailProg base)
       else if ph = 8 then (Memory.spec 0).clientState s (tickMigrateProg base)
       else if ph = 9 then (Memory.spec 0).clientState s (tickUnpermProg base)
       else if ph = 10 then (Memory.spec 0).clientState s (tickSlideDownProg base)
       else s) ∧
    (Memory.spec 0).clientResult s (bgTickProg (base, newFr)) =
      (if ph = 5 then (Memory.spec 0).clientResult s (tickRandPrepProg base)
       else (0, (0, 0))) ∧
    memoryCost (bgTickProg (base, newFr)) s =
      1 + (if ph = 0 then memoryCost (tickIdleProg base) s
           else if ph = 1 then memoryCost (tickLogProg base) s
           else if ph = 2 then memoryCost (tickGrowPreProg (base, newFr)) s
           else if ph = 3 then memoryCost (tickSlideUpProg base) s
           else if ph = 4 then memoryCost (tickZeroMetaProg base) s
           else if ph = 5 then memoryCost (tickRandPrepProg base) s
           else if ph = 6 then memoryCost (tickInitDirProg base) s
           else if ph = 7 then memoryCost (tickInitTailProg base) s
           else if ph = 8 then memoryCost (tickMigrateProg base) s
           else if ph = 9 then memoryCost (tickUnpermProg base) s
           else if ph = 10 then memoryCost (tickSlideDownProg base) s
           else 0) := by
  dsimp only
  unfold bgTickProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd,
    prog_clientResult_bind, cstate_rd, cres_rd,
    Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  set ph := s.mem (base + hdrPhase)
  by_cases h0 : ph = 0
  · simp [h0]
  · rw [ite_eq_right h0, ite_eq_right h0]
    by_cases h1 : ph = 1
    · simp [h1]
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : ph = 2
      · simp [h2]
      · rw [ite_eq_right h2, ite_eq_right h2]
        by_cases h3 : ph = 3
        · simp [h3]
        · rw [ite_eq_right h3, ite_eq_right h3]
          by_cases h4 : ph = 4
          · simp [h4]
          · rw [ite_eq_right h4, ite_eq_right h4]
            by_cases h5 : ph = 5
            · simp [h5]
            · rw [ite_eq_right h5, ite_eq_right h5, ite_eq_right h5]
              by_cases h6 : ph = 6
              · simp [h6]
              · rw [ite_eq_right h6, ite_eq_right h6]
                by_cases h7 : ph = 7
                · simp [h7]
                · rw [ite_eq_right h7, ite_eq_right h7]
                  by_cases h8 : ph = 8
                  · simp [h8]
                  · rw [ite_eq_right h8, ite_eq_right h8]
                    by_cases h9 : ph = 9
                    · simp [h9]
                    · rw [ite_eq_right h9, ite_eq_right h9]
                      by_cases h10 : ph = 10
                      · simp [h10]
                      · simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, memoryCost_pure]

/-- Evaluates `stepOpProg (((base, newFr), opTag), (u_val, v_val))`. -/
theorem stepOpProg_eval (base newFr opTag u_val v_val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (stepOpProg (((base, newFr), opTag), (u_val, v_val))) =
      (if opTag = 0 then (Memory.spec 0).clientState s (userQueryProg (base, u_val))
       else (Memory.spec 0).clientState
         ((Memory.spec 0).clientState s (userMutateProg ((base, opTag), (u_val, v_val))))
         (bgTickProg (base, newFr))) ∧
    (Memory.spec 0).clientResult s (stepOpProg (((base, newFr), opTag), (u_val, v_val))) =
      (if opTag = 0 then ((Memory.spec 0).clientResult s (userQueryProg (base, u_val)), (0, (0, 0)))
       else ((0, 0),
         (Memory.spec 0).clientResult
           ((Memory.spec 0).clientState s (userMutateProg ((base, opTag), (u_val, v_val))))
           (bgTickProg (base, newFr)))) ∧
    memoryCost (stepOpProg (((base, newFr), opTag), (u_val, v_val))) s =
      (if opTag = 0 then memoryCost (userQueryProg (base, u_val)) s
       else memoryCost (userMutateProg ((base, opTag), (u_val, v_val))) s +
         memoryCost (bgTickProg (base, newFr))
           ((Memory.spec 0).clientState s (userMutateProg ((base, opTag), (u_val, v_val))))) := by
  unfold stepOpProg; dsimp only
  by_cases h0 : opTag = 0
  · simp [h0]
  · simp [h0]

/-- Evaluates `finishRandFillProg base`. -/
theorem finishRandFillProg_eval (base : ℕ) (s : Memory.State) :
    let redW := s.mem (base + hdrRedW)
    let stg := s.mem (base + hdrStage)
    let pad := s.mem (base + hdrPad)
    let nLive := s.mem (base + hdrLive)
    let ibHi := s.mem (base + hdrItemHi)
    let qHi := s.mem (base + hdrQHi)
    let pDst := if stg = 0 then base + hdrPBase1 else base + hdrPBase0
    let metaDst := if stg = 0 then base + 192 + pad else base + 192
    let mask := ((1 : ℕ) <<< (redW - 1)) - 1
    let s1 : Memory.State :=
      { mem := Function.update
          (Function.update s.mem (metaDst + 32) (s.mem (metaDst + 32) &&& mask))
          (metaDst + s.mem (pDst + 30)) (s.mem (metaDst + s.mem (pDst + 30)) &&& mask),
        frontier := s.frontier }
    let s2 := (Memory.spec 0).clientState s1
      (setDirectSlotIoProg ((base, pDst), ((ibHi, qHi), nLive)))
    let s3 := (Memory.spec 0).clientState s2 (epochInitZeroedProg pDst)
    (Memory.spec 0).clientState s (finishRandFillProg base) =
      { mem := Function.update (Function.update s3.mem (base + hdrCur) 0) (base + hdrPhase) 6,
        frontier := s3.frontier } ∧
    memoryCost (finishRandFillProg base) s = 28 + memoryCost (epochInitZeroedProg pDst) s2 := by
  dsimp only
  unfold finishRandFillProg
  iterate 6 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 6 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [StateTransitionSpec.clientState_bind, clientState_slotPairProg, clientResult_slotPairProg,
    Realization.memoryCost_bind', memoryCost_slotPairProg, clientState_slotPairProg,
    clientResult_slotPairProg]
  dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_metaDstAddrProg,
    clientResult_metaDstAddrProg,
    Realization.memoryCost_bind', memoryCost_metaDstAddrProg, clientState_metaDstAddrProg,
    clientResult_metaDstAddrProg]
  have hmm_mc : ∀ rw md pd, memoryCost (maskRandMultsProg ((rw, md), (pd, 0))) s = 5 := by
    intro rw md pd; unfold maskRandMultsProg; dsimp only
    rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd, pure_bind,
      Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd,
      Realization.memoryCost_bind', mcost_wr, cstate_wr,
      Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd, mcost_wr]
  rw [StateTransitionSpec.clientState_bind, maskRandMultsProg_state,
    Realization.memoryCost_bind', hmm_mc, maskRandMultsProg_state,
    StateTransitionSpec.clientState_bind,
    Realization.memoryCost_bind', (setDirectSlotIoProg_eval _ _ _ _ _ _).2,
    StateTransitionSpec.clientState_bind,
    Realization.memoryCost_bind',
    StateTransitionSpec.clientState_bind, cstate_wr, cstate_wr,
    Realization.memoryCost_bind', mcost_wr, cstate_wr, mcost_wr]
  exact ⟨rfl, by omega⟩

/-- Evaluates `finishShrinkPostProg base`. -/
theorem finishShrinkPostProg_eval (base : ℕ) (s : Memory.State) :
    let nDst := s.mem (base + hdrNDst)
    let mDst := s.mem (base + hdrMDst)
    let ibLo := s.mem (base + hdrItemLo)
    let qLo := s.mem (base + hdrQLo)
    let s1 := if 0 < nDst then (Memory.spec 0).clientState s (copyDstToSrcHostProg base) else s
    (Memory.spec 0).clientState s (finishShrinkPostProg base) =
      { mem := Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (Function.update
            (Function.update s1.mem (base + hdrNSrc) nDst)
            (base + hdrMSrc) mDst)
            (base + hdrNDst) 0)
            (base + hdrMDst) 0)
            (base + hdrStage) 0)
            (base + hdrEpochOps) 0)
            (base + hdrItemHi) ibLo)
            (base + hdrQHi) qLo)
            (base + hdrPhase) 0,
        frontier := s1.frontier } ∧
    memoryCost (finishShrinkPostProg base) s ≤ 23 := by
  dsimp only
  unfold finishShrinkPostProg
  iterate 4 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 4 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  unfold optCopyDstToSrcProg; dsimp only
  have hoc : (Memory.spec 0).clientState s
      (if 0 < s.mem (base + hdrNDst) then copyDstToSrcHostProg base else pure ()) =
      (if 0 < s.mem (base + hdrNDst) then
        (Memory.spec 0).clientState s (copyDstToSrcHostProg base)
       else s) ∧
      memoryCost
        (if 0 < s.mem (base + hdrNDst) then copyDstToSrcHostProg base else pure ()) s ≤ 10 := by
    by_cases hd : 0 < s.mem (base + hdrNDst)
    · rw [ite_eq_left hd, ite_eq_left hd, (copyDstToSrcHostProg_spec base s).2.1]
      exact ⟨rfl, le_rfl⟩
    · rw [ite_eq_right hd, ite_eq_right hd, memoryCost_pure]
      exact ⟨rfl, by omega⟩
  rw [hoc.1]
  have hc_oc := hoc.2
  iterate 8 rw [StateTransitionSpec.clientState_bind, cstate_wr]
  iterate 8 rw [Realization.memoryCost_bind', mcost_wr, cstate_wr]
  rw [cstate_wr, mcost_wr]
  exact ⟨rfl, by omega⟩

/-- Evaluates `calcPostShrinkProg (base, curFr)` when `0 < s.mem (base + hdrW)`. -/
theorem calcPostShrinkProg_eval {base curFr : ℕ} {s : Memory.State}
    (hw : 0 < s.mem (base + hdrW)) :
    let ph := s.mem (base + hdrPhase)
    let wv := s.mem (base + hdrW)
    let vb := s.mem (base + hdrValBits)
    let nLive := s.mem (base + hdrLive)
    let ibLo := s.mem (base + hdrItemLo)
    let ibHi := s.mem (base + hdrItemHi)
    let qLo := s.mem (base + hdrQLo)
    let qHi := s.mem (base + hdrQHi)
    let diffLo := curFr - (ibLo + pairStreamWords nLive qLo vb wv)
    let diffHi := curFr - (ibHi + pairStreamWords nLive qHi vb wv)
    (Memory.spec 0).clientState s (calcPostShrinkProg (base, curFr)) =
      (if ph = 11 ∧ diffLo ≤ bulkBatchWhp then
        (Memory.spec 0).clientState s (finishShrinkPostProg base)
       else s) ∧
    (Memory.spec 0).clientResult s (calcPostShrinkProg (base, curFr)) =
      (if ph < 2 then diffLo
       else if ph = 11 then min diffLo bulkBatchWhp
       else diffHi) ∧
    memoryCost (calcPostShrinkProg (base, curFr)) s ≤ 31 := by
  dsimp only
  have hpsLo := pairStreamWordsSafeProg_spec (s.mem (base + hdrLive)) (s.mem (base + hdrQLo))
    (s.mem (base + hdrValBits)) (s.mem (base + hdrW)) hw s
  have hpsHi := pairStreamWordsSafeProg_spec (s.mem (base + hdrLive)) (s.mem (base + hdrQHi))
    (s.mem (base + hdrValBits)) (s.mem (base + hdrW)) hw s
  unfold calcPostShrinkProg; dsimp only
  iterate 8 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
  iterate 8 rw [prog_clientResult_bind, cstate_rd, cres_rd]
  iterate 8 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
  by_cases hp2 : s.mem (base + hdrPhase) < 2
  · have hn11 : ¬(s.mem (base + hdrPhase) = 11 ∧
        curFr - (s.mem (base + hdrItemLo) +
          pairStreamWords (s.mem (base + hdrLive)) (s.mem (base + hdrQLo))
            (s.mem (base + hdrValBits)) (s.mem (base + hdrW))) ≤ bulkBatchWhp) := by omega
    simp only [hp2, hn11, ↓reduceIte]
    rw [
      StateTransitionSpec.clientState_bind, hpsLo.1, hpsLo.2.1, clientState_clampSubProg,
      prog_clientResult_bind, hpsLo.1, hpsLo.2.1, clientResult_clampSubProg,
      Realization.memoryCost_bind', hpsLo.2.2, hpsLo.1, hpsLo.2.1, memoryCost_clampSubProg]
    exact ⟨rfl, rfl, by omega⟩
  · simp only [hp2, ↓reduceIte]
    by_cases hp11 : s.mem (base + hdrPhase) = 11
    · simp only [hp11, ↓reduceIte]
      rw [
        StateTransitionSpec.clientState_bind, hpsLo.1, hpsLo.2.1,
        StateTransitionSpec.clientState_bind, clientState_clampSubProg, clientResult_clampSubProg,
        prog_clientResult_bind, hpsLo.1, hpsLo.2.1,
        prog_clientResult_bind, clientState_clampSubProg, clientResult_clampSubProg,
        Realization.memoryCost_bind', hpsLo.2.2, hpsLo.1, hpsLo.2.1,
        Realization.memoryCost_bind', memoryCost_clampSubProg, clientState_clampSubProg,
        clientResult_clampSubProg]
      set diffLo := curFr - (s.mem (base + hdrItemLo) +
        pairStreamWords (s.mem (base + hdrLive)) (s.mem (base + hdrQLo))
          (s.mem (base + hdrValBits)) (s.mem (base + hdrW)))
      by_cases hd : diffLo ≤ bulkBatchWhp
      · simp only [hd, and_self, ↓reduceIte, min_eq_left hd]
        rw [StateTransitionSpec.clientState_bind,
          show (Memory.spec 0).clientState ((Memory.spec 0).clientState s
            (finishShrinkPostProg base)) (pure diffLo) =
            (Memory.spec 0).clientState s (finishShrinkPostProg base) from rfl,
          prog_clientResult_bind, prog_clientResult_pure,
          Realization.memoryCost_bind', memoryCost_pure]
        have hf := (finishShrinkPostProg_eval base s).2
        exact ⟨rfl, rfl, by omega⟩
      · simp only [hd, and_false, ↓reduceIte, memoryCost_pure,
          min_eq_right (Nat.le_of_not_le hd)]
        exact ⟨rfl, rfl, by omega⟩
    · simp only [hp11, false_and, ↓reduceIte]
      rw [
        StateTransitionSpec.clientState_bind, hpsHi.1, hpsHi.2.1, clientState_clampSubProg,
        prog_clientResult_bind, hpsHi.1, hpsHi.2.1, clientResult_clampSubProg,
        Realization.memoryCost_bind', hpsHi.2.2, hpsHi.1, hpsHi.2.1, memoryCost_clampSubProg]
      exact ⟨rfl, rfl, by omega⟩

/-- Evaluates `postRandShrinkProg ((base, curFr), opTag)`. -/
theorem postRandShrinkProg_eval (base curFr opTag : ℕ) (s : Memory.State) :
    let ph0 := s.mem (base + hdrPhase)
    let stg0 := s.mem (base + hdrStage)
    let cur0 := s.mem (base + hdrCur)
    let pDst0 := if stg0 = 0 then base + hdrPBase1 else base + hdrPBase0
    let doRF : Prop := ph0 = 5 ∧ s.mem (pDst0 + 31) ≤ cur0
    haveI : Decidable doRF := inferInstance
    let s1 := if doRF then (Memory.spec 0).clientState s (finishRandFillProg base) else s
    (Memory.spec 0).clientState s (postRandShrinkProg ((base, curFr), opTag)) =
      (if opTag = 0 then s
       else (Memory.spec 0).clientState s1 (calcPostShrinkProg (base, curFr))) ∧
    (Memory.spec 0).clientResult s (postRandShrinkProg ((base, curFr), opTag)) =
      (if opTag = 0 then 0
       else (Memory.spec 0).clientResult s1 (calcPostShrinkProg (base, curFr))) ∧
    memoryCost (postRandShrinkProg ((base, curFr), opTag)) s ≤
      (if opTag = 0 then 0
       else 4 + (if doRF then memoryCost (finishRandFillProg base) s else 0) +
         memoryCost (calcPostShrinkProg (base, curFr)) s1) := by
  dsimp only
  unfold postRandShrinkProg; dsimp only
  by_cases h0 : opTag = 0
  · rw [ite_eq_left h0, ite_eq_left h0, ite_eq_left h0, ite_eq_left h0, memoryCost_pure]
    exact ⟨rfl, rfl, le_rfl⟩
  · rw [ite_eq_right h0, ite_eq_right h0, ite_eq_right h0, ite_eq_right h0]
    iterate 3 rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
    iterate 3 rw [prog_clientResult_bind, cstate_rd, cres_rd]
    iterate 3 rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
    rw [StateTransitionSpec.clientState_bind, clientState_optFinishRandFillProg,
      prog_clientResult_bind, clientState_optFinishRandFillProg,
      Realization.memoryCost_bind', clientState_optFinishRandFillProg]
    have horf :
        (if s.mem (base + hdrPhase) = 5 then
          if s.mem ((if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) +
              31) ≤ s.mem (base + hdrCur) then
            (Memory.spec 0).clientState s (finishRandFillProg base)
          else s
         else s) =
        (if s.mem (base + hdrPhase) = 5 ∧
            s.mem ((if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) +
              31) ≤ s.mem (base + hdrCur) then
          (Memory.spec 0).clientState s (finishRandFillProg base)
         else s) ∧
        memoryCost (optFinishRandFillProg
          ((s.mem (base + hdrPhase), s.mem (base + hdrStage)),
           (s.mem (base + hdrCur), base))) s ≤
        1 + (if s.mem (base + hdrPhase) = 5 ∧
            s.mem ((if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) +
              31) ≤ s.mem (base + hdrCur) then
          memoryCost (finishRandFillProg base) s
         else 0) := by
      unfold optFinishRandFillProg; dsimp only
      by_cases hp5 : s.mem (base + hdrPhase) = 5
      · rw [ite_eq_left hp5,ite_eq_left hp5,
          Realization.memoryCost_bind', memoryCost_slotPairProg, clientState_slotPairProg,
          clientResult_slotPairProg]
        dsimp only
        rw [Realization.memoryCost_bind', mcost_rd, cstate_rd, cres_rd]
        by_cases hle : s.mem ((if s.mem (base + hdrStage) = 0 then base + hdrPBase1
            else base + hdrPBase0) + 31) ≤ s.mem (base + hdrCur)
        · rw [ite_eq_left hle, ite_eq_left ⟨hp5, hle⟩, ite_eq_left hle, ite_eq_left ⟨hp5, hle⟩]
          exact ⟨rfl, by omega⟩
        · rw [ite_eq_right hle, ite_eq_right (fun h => hle h.2), ite_eq_right hle,
            ite_eq_right (fun h => hle h.2), memoryCost_pure]
          exact ⟨rfl, by omega⟩
      · rw [ite_eq_right hp5, ite_eq_right (fun h => hp5 h.1), ite_eq_right hp5,
          ite_eq_right (fun h => hp5 h.1), memoryCost_pure]
        exact ⟨rfl, by omega⟩
    rw [horf.1]
    have hc := horf.2
    exact ⟨rfl, rfl, by omega⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
