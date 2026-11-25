/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochCtrlBase
-- Unfolds `pageBeginUnpermBoundedProg` / `pageRunUnpermBatchProg` for frontier preservation.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargePageProg
-- Unfolds `slideUpStepProg` / `slideDownStepProg` for frontier preservation.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.SplitPairProg
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deamortized Dual-Epoch 12-Phase Background Dispatcher (`DualEpochCtrl`)

This module implements and certifies (`RealizesBounded .exact`, `¬ReadsWidth`, and `ValidHistory`)
the individual 12-phase (`0..10`) background tick programs for the resizable succinct worst-case
WHP dictionary ([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.tickIdleProg` ..
  `tickSlideDownProg`: individual phase tick programs (`0..10`) for background dual-epoch rebuilds.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

theorem slideUpBatchProg_fr_and_le (ctx : SplitPairCtx) (fuel sp : ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (slideUpBatchProg ((ctx, sp), fuel))).frontier = s.frontier ∧
    (Memory.spec 0).clientResult s (slideUpBatchProg ((ctx, sp), fuel)) ≤ sp := by
  unfold slideUpBatchProg; dsimp only
  induction fuel generalizing sp s with
  | zero => exact ⟨rfl, le_rfl⟩
  | succ k ih =>
    unfold iterate
    rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind]
    have h1 : ((Memory.spec 0).clientState s (slideUpStepProg (ctx, sp))).frontier = s.frontier ∧
        (Memory.spec 0).clientResult s (slideUpStepProg (ctx, sp)) ≤ sp := by
      rcases ctx with ⟨⟨⟨_, ⟨_, _⟩⟩, ⟨_, ⟨_, _⟩⟩⟩, _⟩
      unfold slideUpStepProg StateTransitionSpec.clientState StateTransitionSpec.clientResult
      dsimp only
      split_ifs
      · simp
      · simp
    obtain ⟨hfr_k, hle_k⟩ := ih ((Memory.spec 0).clientResult s (slideUpStepProg (ctx, sp)))
      ((Memory.spec 0).clientState s (slideUpStepProg (ctx, sp)))
    exact ⟨hfr_k.trans h1.1, hle_k.trans h1.2⟩

theorem slideDownBatchProg_fr (ctx : SplitPairCtx) (nL sp fuel : ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (slideDownBatchProg (((ctx, nL), sp), fuel))).frontier =
      s.frontier := by
  unfold slideDownBatchProg; dsimp only
  induction fuel generalizing sp s with
  | zero => rfl
  | succ k ih =>
    unfold iterate
    rw [StateTransitionSpec.clientState_bind, ih]
    rcases ctx with ⟨⟨⟨_, ⟨_, _⟩⟩, ⟨_, ⟨_, _⟩⟩⟩, _⟩
    unfold slideDownStepProg StateTransitionSpec.clientState; dsimp only
    split_ifs
    · simp [runClient_state_writePairGenProg]
    · simp

theorem pageBeginUnpermBoundedProg_fr (ctx : PageArenaCtx) (s : Memory.State) :
    ((Memory.spec 0).clientState s (pageBeginUnpermBoundedProg ctx)).frontier = s.frontier := by
  rcases ctx with ⟨⟨⟨⟨mb, _⟩, _⟩, _⟩, _⟩
  unfold pageBeginUnpermBoundedProg StateTransitionSpec.clientState; dsimp only
  simp only [pure_bind, prog_runClient_state_bind, prog_runClient_state_read,
    runClient_state_pageReadFullPagesProg, runClient_state_pageReadTailCountsProg]
  split_ifs
  · simp [runClient_frontier_pageWriteCleanProg]
  · simp

theorem pageRunUnpermBatchProg_fr (ctx : PageArenaCtx) (fuel : ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (pageRunUnpermBatchProg (ctx, fuel))).frontier = s.frontier := by
  unfold pageRunUnpermBatchProg pageRunUnpermIterProg; dsimp only
  have hiter : ∀ k acc (st : Memory.State),
      ((Memory.spec 0).clientState st (iterate pageUnpermIterStepProg ctx k acc)).frontier =
        st.frontier := by
    intro k; induction k with
    | zero => intro _ _; rfl
    | succ m ih =>
      intro acc st; unfold iterate
      rw [StateTransitionSpec.clientState_bind, ih]
      unfold pageUnpermIterStepProg StateTransitionSpec.clientState; dsimp only
      simp [runClient_frontier_pageUnpermStepBoundedProg]
  rw [StateTransitionSpec.clientState_bind]; exact hiter fuel 0 s

theorem writeSmallParamTableProg_fr (x : (ℕ × ℕ) × ((ℕ × ℕ) × PageArenaCtx)) (s : Memory.State) :
    ((Memory.spec 0).clientState s (writeSmallParamTableProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨pDst, sm1⟩, ⟨⟨up, sb⟩,
    ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩⟩⟩
  exact (writeSmallParamTableProg_spec pDst
    ⟨sm1, 0, 0, ⟨up, sb, ⟨mb, od, ot, pb, wv, pg, mp, ib, qb, vb, nc⟩⟩⟩ s).1

theorem setSlotIoProg_fr (x : ℕ × ((ℕ × ℕ) × PageArenaCtx)) (s : Memory.State) :
    ((Memory.spec 0).clientState s (setSlotIoProg x)).frontier = s.frontier :=
  runClient_frontier_setSlotIoProg x s

theorem pageInitScalarsBandProg_fr (x : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientState s (pageInitScalarsBandProg x)).frontier = s.frontier :=
  (pageInitScalarsBandProg_spec x.1.1 x.1.2 x.2.1 x.2.2 s).1

/-! ## Section 4: Per-Phase Deterministic Background Tick Programs (`0..11`) -/

/-- Increment `hdrEpochOps` when `nSrc ≠ 0`, or write `0` when `nSrc = 0` (`0` `__do_jp`). -/
private def incEpochOpsProg : ℕ × ℕ → Memory.Prog Unit
  | (base, nSrc) =>
    if nSrc = 0 then
      Memory.write (base + hdrEpochOps) 0
    else do
      let ops ← Memory.read (base + hdrEpochOps)
      Memory.write (base + hdrEpochOps) (ops + 1)

private theorem validHistory_incEpochOpsProg {w base nSrc : ℕ} {s : Memory.State}
    (hb : base + 16 ≤ s.frontier)
    (hops : nSrc ≠ 0 → Fits w (s.mem (base + hdrEpochOps) + 1)) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (incEpochOpsProg (base, nSrc))) := by
  unfold incEpochOpsProg hdrEpochOps at *
  rcases s with ⟨m, fr⟩; dsimp only at hb hops ⊢
  exact vh_ite (nSrc = 0)
    (fun _ => vh_wr_only (by omega) (Nat.two_pow_pos w))
    (fun hne => vh_rd (by dsimp only; omega) <| vh_wr_only (by omega) (hops hne))

private theorem realizesBounded_incEpochOps :
    RealizesBounded .exact incEpochOpsProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (base, nSrc) s =>
        1 ≤ w ∧ base + 16 ≤ s.frontier ∧
        (nSrc ≠ 0 → Fits w (s.mem (base + hdrEpochOps) + 1)))
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨base, nSrc⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hw1, hb, hops⟩ := h
    have h1_w : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
    have hfr_w := hmem.1
    try (have hops' := hops ‹_›; dsimp only [Fits] at hops')
    try simp only [hdrEpochOps, Fits] at *; omega)

private theorem incEpochOps_frame {base nSrc : ℕ} (s : Memory.State) :
    let s1 := (Memory.spec 0).clientState s (incEpochOpsProg (base, nSrc))
    s1.frontier = s.frontier ∧
    ∀ a, a ≠ base + hdrEpochOps → s1.mem a = s.mem a := by
  dsimp only; unfold incEpochOpsProg; dsimp only
  by_cases h0 : nSrc = 0
  · rw [ite_eq_left h0, cstate_wr]; exact ⟨rfl, fun a ha => Function.update_of_ne ha _ _⟩
  · rw [ite_eq_right h0, StateTransitionSpec.clientState_bind, cstate_rd, cres_rd, cstate_wr]
    exact ⟨rfl, fun a ha => Function.update_of_ne ha _ _⟩

attribute [local irreducible] incEpochOpsProg

/-- Phase `0` (`idle`) tick: increments `epochOps` (when `nSrc > 0`), runs `checkTriggerProg`, and
starts either `growPre` (`nDst = 0`, `Large → Small`) or `log2Calc` (`nDst > 0`). -/
def tickIdleProg (base : ℕ) : Memory.Prog Unit := do
  let nSrc ← Memory.read (base + hdrNSrc)
  incEpochOpsProg (base, nSrc)
  let tr ← checkTriggerProg base
  if tr.1 = 0 then
    pure ()
  else do
    Memory.write (base + hdrNDst) tr.2
    Memory.write (base + hdrStage) 0
    Memory.write (base + hdrEpochOps) 0
    if tr.2 = 0 then do
      let mSrc ← Memory.read (base + hdrMSrc)
      let kb ← Memory.read (base + hdrKeyBits)
      Memory.write (base + hdrMDst) 0
      Memory.write (base + hdrPad) mSrc
      Memory.write (base + hdrItemHi) (base + 196 + mSrc)
      Memory.write (base + hdrQHi) kb
      Memory.write (base + hdrPhase) 2
    else do
      Memory.write (base + hdrLogSub) 0
      Memory.write (base + hdrLogAcc) tr.2
      Memory.write (base + hdrLogK) 0
      Memory.write (base + hdrPhase) 1

/-- Precondition for `tickIdleProg`. -/
@[expose] def TickIdlePre (w base : ℕ) (s : Memory.State) : Prop :=
  4 ≤ w ∧ base + 192 ≤ s.frontier ∧ Fits w (s.mem (base + hdrU1) + 1) ∧
  s.mem (base + hdrLive) ≤ s.mem (base + hdrU1) + 1 ∧
  s.mem (base + hdrNSrc) ≤ s.mem (base + hdrU1) + 1 ∧
  (s.mem (base + hdrNSrc) ≠ 0 → Fits w (s.mem (base + hdrEpochOps) + 1)) ∧
  Fits w (base + 196 + s.mem (base + hdrMSrc))

theorem validHistory_tickIdleProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : TickIdlePre w base s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (tickIdleProg base)) := by
  obtain ⟨hw4, hb, hu1, _, hns, hops, hms⟩ := hpre
  have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) hw4
  have hz : Fits w 0 := Nat.two_pow_pos w
  have h1 : Fits w 1 := by dsimp only [Fits]; omega
  have h2 : Fits w 2 := by dsimp only [Fits]; omega
  unfold tickIdleProg
  refine vh_rd (by unfold hdrNSrc; omega) ?_
  have vhi := validHistory_incEpochOpsProg (w := w) (by omega) hops
  refine vh_seq vhi fun s1 hs1 _ _ => ?_
  have hwf1 := wf_step hwf vhi
  obtain ⟨hfr1, hmem1⟩ := incEpochOps_frame (base := base) (nSrc := s.mem (base + hdrNSrc)) s
  have hfr1' : s1.frontier = s.frontier := hs1 ▸ hfr1
  have hu1_1 : s1.mem (base + hdrU1) = s.mem (base + hdrU1) :=
    hs1 ▸ hmem1 _ (by simp [hdrU1, hdrEpochOps])
  have hns_1 : s1.mem (base + hdrNSrc) = s.mem (base + hdrNSrc) :=
    hs1 ▸ hmem1 _ (by simp [hdrNSrc, hdrEpochOps])
  refine vh_seq (validHistory_checkTriggerProg (s := s1) (by rw [hfr1']; omega))
    fun s2 hs2 tr htr => ?_
  rw [hs2, clientState_checkTriggerProg]
  have htr2_f : Fits w tr.2 :=
    htr ▸ checkTriggerProg_res2_fits (s := s1) (by rw [hu1_1]; exact hu1)
      (by rw [hu1_1, hns_1]; exact hns)
  refine vh_ite (tr.1 = 0) (fun _ => trivial) fun _ => ?_
  have hwf1' : Memory.WellFormed w s1 := hs1.symm ▸ hwf1
  rcases s1 with ⟨m1, fr1⟩; dsimp only at hfr1' hwf1'
  refine vh_wr (by unfold hdrNDst; omega) htr2_f <|
    vh_wr (by unfold hdrStage; omega) hz <|
    vh_wr (by unfold hdrEpochOps; omega) hz ?_
  refine vh_ite (tr.2 = 0) (fun _ => ?_) (fun _ => ?_)
  · refine vh_rd (by dsimp only; unfold hdrMSrc; omega) <|
      vh_rd (by dsimp only; unfold hdrKeyBits; omega) ?_
    dsimp only
    have hms_eq : Function.update (Function.update (Function.update m1 (base + hdrNDst) tr.2)
        (base + hdrStage) 0) (base + hdrEpochOps) 0 (base + hdrMSrc) = s.mem (base + hdrMSrc) := by
      rw [Function.update_of_ne (by simp [hdrMSrc, hdrEpochOps]),
        Function.update_of_ne (by simp [hdrMSrc, hdrStage]),
        Function.update_of_ne (by simp [hdrMSrc, hdrNDst])]
      have hm := congrArg (fun st : Memory.State => st.mem (base + hdrMSrc)) hs1
      dsimp only at hm
      exact hm.trans (hmem1 _ (by simp [hdrMSrc, hdrEpochOps]))
    have hkb_f : Fits w (Function.update (Function.update (Function.update m1
        (base + hdrNDst) tr.2) (base + hdrStage) 0) (base + hdrEpochOps) 0
        (base + hdrKeyBits)) := by
      rw [Function.update_of_ne (by simp [hdrKeyBits, hdrEpochOps]),
        Function.update_of_ne (by simp [hdrKeyBits, hdrStage]),
        Function.update_of_ne (by simp [hdrKeyBits, hdrNDst])]
      exact hwf1'.2 (base + hdrKeyBits)
    rw [hms_eq]
    exact vh_wr (by unfold hdrMDst; omega) hz <|
      vh_wr (by unfold hdrPad; omega) (hwf.2 _) <|
      vh_wr (by unfold hdrItemHi; omega) hms <|
      vh_wr (by unfold hdrQHi; omega) hkb_f <|
      vh_wr_only (by unfold hdrPhase; omega) h2
  · exact vh_wr (by unfold hdrLogSub; omega) hz <|
      vh_wr (by unfold hdrLogAcc; omega) htr2_f <|
      vh_wr (by unfold hdrLogK; omega) hz <|
      vh_wr_only (by unfold hdrPhase; omega) h1

theorem realizesBounded_tickIdle :
    RealizesBounded .exact tickIdleProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      TickIdlePre (fun _ _ => 0) := by
  have hio := realizesBounded_incEpochOps
  have hct := realizesBounded_checkTrigger
  realize
  all_goals (
    obtain ⟨hw4, hb, hu1, hnl, hns, hops, hms⟩ := h
    have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) hw4
    have hfr_w := hmem.1
    set s1 := (Memory.spec 0).clientState s (incEpochOpsProg (d, s.mem (d + hdrNSrc)))
    obtain ⟨hfr1, hmem1⟩ := incEpochOps_frame (base := d) (nSrc := s.mem (d + hdrNSrc)) s
    have hu1_1 : s1.mem (d + hdrU1) = s.mem (d + hdrU1) :=
      hmem1 _ (by simp [hdrU1, hdrEpochOps])
    have hnl_1 : s1.mem (d + hdrLive) = s.mem (d + hdrLive) :=
      hmem1 _ (by simp [hdrLive, hdrEpochOps])
    have hns_1 : s1.mem (d + hdrNSrc) = s.mem (d + hdrNSrc) :=
      hmem1 _ (by simp [hdrNSrc, hdrEpochOps])
    have htr2_f : Fits w ((Memory.spec 0).clientResult s1 (checkTriggerProg d)).2 :=
      checkTriggerProg_res2_fits (s := s1) (by rw [hu1_1]; exact hu1)
        (by rw [hu1_1, hns_1]; exact hns)
    repeat rw [clientState_checkTriggerProg] at *
    try rw [hfr1]
    try rw [hu1_1] at *
    try rw [hnl_1] at *
    try rw [hns_1] at *
    try simp only [Function.update_of_ne (by simp [hdrMSrc, hdrEpochOps] :
      d + hdrMSrc ≠ d + hdrEpochOps),
      Function.update_of_ne (by simp [hdrMSrc, hdrStage] : d + hdrMSrc ≠ d + hdrStage),
      Function.update_of_ne (by simp [hdrMSrc, hdrNDst] : d + hdrMSrc ≠ d + hdrNDst)] at *
    try rw [hmem1 (d + hdrMSrc) (by simp [hdrMSrc, hdrEpochOps])]
    try simp only [hdrNSrc, hdrEpochOps, hdrU1, hdrLive, hdrNDst, hdrStage, hdrMSrc, hdrKeyBits,
      hdrMDst, hdrPad, hdrItemHi, hdrQHi, hdrPhase, hdrLogSub, hdrLogAcc, hdrLogK, Fits] at *
    omega)

attribute [local irreducible] tickIdleProg

/-- Pure helper computing `(clogN, cl2)` from `(k, nDst, p)` (`0` queries, `0` `__do_jp`). -/
private def calcClogPairProg : (ℕ × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((k, nDst), p) =>
    if nDst = p then pure (k, k + 1)
    else if nDst < p then pure (k + 1, k + 1)
    else if p < 1 then pure (k + 1, k + 1)
    else if nDst - p = p - 1 then pure (k + 1, k + 2)
    else pure (k + 1, k + 1)

@[simp] private theorem runClient_state_calcClogPairProg (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (calcClogPairProg x)).2.1 = s := by
  rcases x with ⟨⟨_, _⟩, _⟩; unfold calcClogPairProg; dsimp only; split_ifs <;> rfl

@[simp] private theorem clientState_calcClogPairProg (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (calcClogPairProg x) = s :=
  runClient_state_calcClogPairProg x s

private theorem clientResult_calcClogPairProg_le (k nDst p : ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (calcClogPairProg ((k, nDst), p))).1 ≤ k + 1 ∧
    ((Memory.spec 0).clientResult s (calcClogPairProg ((k, nDst), p))).2 ≤ k + 2 := by
  unfold calcClogPairProg; dsimp only
  split_ifs <;> (simp only [StateTransitionSpec.clientResult, prog_clientResult_pure]; omega)

private theorem validHistory_calcClogPairProg (w : ℕ) (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (calcClogPairProg x)) := by
  rcases x with ⟨⟨_, _⟩, _⟩; unfold calcClogPairProg; dsimp only; split_ifs <;> exact trivial

private theorem add_two_lt_two_pow_of_six {w : ℕ} (hw : 6 ≤ w) : w + 2 < 2 ^ w := by
  obtain ⟨d, rfl⟩ : ∃ d, w = d + 6 := ⟨w - 6, by omega⟩
  clear hw
  induction d with
  | zero => decide
  | succ d ih =>
    rw [show d + 1 + 6 = (d + 6) + 1 by omega, Nat.pow_succ]
    omega

private theorem realizesBounded_calcClogPair :
    RealizesBounded .exact calcClogPairProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((k, _), _) _ => 6 ≤ w ∧ k < w)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨k, nDst⟩, p⟩
    dsimp only [Fits] at *
    obtain ⟨hw6, hk_lt⟩ := h
    have hw_lt := add_two_lt_two_pow_of_six hw6
    omega)

attribute [local irreducible] calcClogPairProg

/-- Pure helper computing `(clogN, pgB)` from `(k, nDst)` when `k = Nat.log 2 nDst`. -/
private def calcLogDerivedProg : ℕ × ℕ → Memory.Prog (ℕ × ℕ)
  | (k, nDst) => do
    let p := (1 : ℕ) <<< k
    let cc ← calcClogPairProg ((k, nDst), p)
    let pgB ← max2Prog (32, cc.2)
    pure (cc.1, pgB)

@[simp] private theorem runClient_state_calcLogDerivedProg (x : ℕ × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (calcLogDerivedProg x)).2.1 = s := by
  rcases x with ⟨k, nDst⟩
  simp [calcLogDerivedProg]

@[simp] private theorem clientState_calcLogDerivedProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (calcLogDerivedProg x) = s :=
  runClient_state_calcLogDerivedProg x s

private theorem clientResult_calcLogDerivedProg_bounds {w k nDst : ℕ} (s : Memory.State)
    (hw6 : 6 ≤ w) (hk_lt : k < w) :
    ((Memory.spec 0).clientResult s (calcLogDerivedProg (k, nDst))).1 ≤ k + 1 ∧
    Fits w ((Memory.spec 0).clientResult s (calcLogDerivedProg (k, nDst))).2 := by
  have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
  have hw_lt := add_two_lt_two_pow_of_six hw6
  have hcc := clientResult_calcClogPairProg_le k nDst ((1 : ℕ) <<< k) s
  unfold calcLogDerivedProg; dsimp only [Fits]
  simp only [StateTransitionSpec.clientResult, prog_clientResult_bind,
    runClient_state_calcClogPairProg, runClient_state_max2Prog, prog_clientResult_pure]
  repeat rw [runClient0_res]
  rw [clientResult_max2Prog]
  simp only [Nat.max_def]
  split_ifs <;> omega

private theorem validHistory_calcLogDerivedProg (w : ℕ) (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (calcLogDerivedProg x)) := by
  rcases x with ⟨k, nDst⟩; unfold calcLogDerivedProg; dsimp only
  refine vh_seq (validHistory_calcClogPairProg w _ s) fun s1 hs1 _ _ => ?_
  rw [hs1, clientState_calcClogPairProg]
  exact vh_seq (validHistory_max2Prog w _ s) fun _ _ _ _ => trivial

private theorem realizesBounded_calcLogDerived :
    RealizesBounded .exact calcLogDerivedProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (k, _) _ => 6 ≤ w ∧ k < w)
      (fun _ _ => 0) := by
  have hcc := realizesBounded_calcClogPair
  have hm := realizesBounded_max2
  realize
  all_goals (
    rcases d with ⟨k, nDst⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hw6, hk_lt⟩ := h
    have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hw_lt := add_two_lt_two_pow_of_six hw6
    have hpow_k : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by decide) hk_lt
    have hsh : (1 : ℕ) <<< k = 2 ^ k := shift_one_eq k
    try rw [hsh] at *
    dsimp only [Fits] at *
    omega)

attribute [local irreducible] calcLogDerivedProg

/-- Write helper for `sub = 0` completion in `tickLogShiftProg` (`7` writes, `0` branches). -/
private def writeLogSub0Prog : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((base, k), (clogN, pgB)), acc1) => do
    Memory.write (base + hdrLogN) k
    Memory.write (base + hdrClogN) clogN
    Memory.write (base + hdrPtrB) (k + 1)
    Memory.write (base + hdrPgB) pgB
    Memory.write (base + hdrLogSub) 1
    Memory.write (base + hdrLogAcc) acc1
    Memory.write (base + hdrLogK) 0

private theorem validHistory_writeLogSub0Prog {w base k clogN pgB acc1 : ℕ} {s : Memory.State}
    (hw6 : 6 ≤ w) (hb : base + 48 ≤ s.frontier) (hk_lt : k < w)
    (hcl : clogN ≤ k + 1) (hpg : Fits w pgB) (hacc1 : Fits w acc1) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (writeLogSub0Prog (((base, k), (clogN, pgB)), acc1))) := by
  have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
  have hw_lt := add_two_lt_two_pow_of_six hw6
  rcases s with ⟨m, fr⟩
  unfold writeLogSub0Prog hdrLogN hdrClogN hdrPtrB hdrPgB hdrLogSub hdrLogAcc hdrLogK
  dsimp only [Fits] at *
  exact vh_wr (by omega) (by dsimp only [Fits]; omega) <|
    vh_wr (by omega) (by dsimp only [Fits]; omega) <|
    vh_wr (by omega) (by dsimp only [Fits]; omega) <|
    vh_wr (by omega) hpg <|
    vh_wr (by omega) (by dsimp only [Fits]; omega) <|
    vh_wr (by omega) hacc1 <|
    vh_wr_only (by omega) (by dsimp only [Fits]; omega)

private theorem realizesBounded_writeLogSub0 :
    RealizesBounded .exact writeLogSub0Prog
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((base, k), _), _) s => 6 ≤ w ∧ base + 48 ≤ s.frontier ∧ k < w)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨base, k⟩, ⟨clogN, pgB⟩⟩, acc1⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hw6, hb, hk_lt⟩ := h
    have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hw_lt := add_two_lt_two_pow_of_six hw6
    have hfr_w := hmem.1
    try simp only [hdrLogN, hdrClogN, hdrPtrB, hdrPgB, hdrLogSub, hdrLogAcc, hdrLogK, Fits] at *
    omega)

attribute [local irreducible] writeLogSub0Prog

/-- Phase `1` (`log2Calc`) sub-stages `0` & `1`: 1-step `Nat.log 2` shift-right loop plus derived
`clog`, `ptrB`, `pgB`, and `ell`. -/
def tickLogShiftProg (base : ℕ) : Memory.Prog Unit := do
  let sub ← Memory.read (base + hdrLogSub)
  let acc ← Memory.read (base + hdrLogAcc)
  let k ← Memory.read (base + hdrLogK)
  let nDst ← Memory.read (base + hdrNDst)
  if 1 < acc then do
    Memory.write (base + hdrLogAcc) (acc / 2)
    Memory.write (base + hdrLogK) (k + 1)
  else if sub = 0 then do
    let cp ← calcLogDerivedProg (k, nDst)
    let acc1 ← clampSubProg (cp.1, 1)
    writeLogSub0Prog (((base, k), cp), acc1)
  else do
    Memory.write (base + hdrEll) (k + 1)
    Memory.write (base + hdrLogSub) 2

/-- Precondition for `tickLogShiftProg`. -/
@[expose] def TickLogShiftPre (w base : ℕ) (s : Memory.State) : Prop :=
  6 ≤ w ∧ base + 48 ≤ s.frontier ∧ s.mem (base + hdrLogK) < w

theorem validHistory_tickLogShiftProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : TickLogShiftPre w base s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (tickLogShiftProg base)) := by
  obtain ⟨hw6, hb, hk_lt⟩ := hpre
  have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
  have hw_lt := add_two_lt_two_pow_of_six hw6
  have hacc_w := hwf.2 (base + hdrLogAcc)
  rcases s with ⟨m, fr⟩
  unfold tickLogShiftProg hdrLogSub hdrLogAcc hdrLogK hdrNDst hdrEll at *
  dsimp only [Fits] at *
  refine vh_rd (by dsimp only; omega) <| vh_rd (by dsimp only; omega) <|
    vh_rd (by dsimp only; omega) <| vh_rd (by dsimp only; omega) ?_
  refine vh_ite (1 < m (base + 30)) (fun _ => ?_) (fun _ => ?_)
  · exact vh_wr (by omega) (by dsimp only [Fits]; omega) <|
      vh_wr_only (by omega) (by dsimp only [Fits]; omega)
  · refine vh_ite (m (base + 36) = 0) (fun _ => ?_) (fun _ => ?_)
    · refine vh_seq (validHistory_calcLogDerivedProg w _ _) fun s1 hs1 cp hcp => ?_
      rw [hs1, clientState_calcLogDerivedProg]
      refine vh_seq (validHistory_clampSubProg w _ _) fun s2 hs2 acc1 hacc1 => ?_
      rw [hs2, clientState_clampSubProg]
      obtain ⟨hcl_le, hpg_f⟩ :=
        clientResult_calcLogDerivedProg_bounds (k := m (base + 31)) (nDst := m (base + 14))
          ⟨m, fr⟩ hw6 hk_lt
      rw [← hcp] at hcl_le hpg_f
      have hacc1_f : Fits w acc1 := by
        rw [hacc1, clientResult_clampSubProg]; dsimp only [Fits]; omega
      exact validHistory_writeLogSub0Prog hw6 hb hk_lt hcl_le hpg_f hacc1_f
    · exact vh_wr (by omega) (by dsimp only [Fits]; omega) <|
        vh_wr_only (by omega) (by dsimp only [Fits]; omega)

theorem realizesBounded_tickLogShift :
    RealizesBounded .exact tickLogShiftProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      TickLogShiftPre (fun _ _ => 0) := by
  have hcl := realizesBounded_calcLogDerived
  have hcs := realizesBounded_clampSub
  have hw0 := realizesBounded_writeLogSub0
  realize
  all_goals (
    obtain ⟨hw6, hb, hk_lt⟩ := h
    have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hw_lt := add_two_lt_two_pow_of_six hw6
    have hfr_w := hmem.1
    have hacc_w := hmem.2 (d + hdrLogAcc)
    repeat rw [clientState_calcLogDerivedProg] at *
    repeat rw [clientState_clampSubProg] at *
    try simp only [hdrLogSub, hdrLogAcc, hdrLogK, hdrNDst, hdrEll, Fits] at *
    omega)

attribute [local irreducible] tickLogShiftProg

/-- Write helper for `tickLogFinishProg` (`13` scalar writes, `0` branches). -/
private def writeLogFinishHdrProg :
    ((ℕ × ℕ) × (ℕ × ℕ)) × (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) → Memory.Prog Unit
  | (((base, mDst), (pad, qHi)), (((od, ot), (ptrB, pgB)), (mp, offFp))) => do
    let p1 := base + hdrPBase1
    let meta1 := base + 192 + pad
    let ibHi := meta1 + mDst + 4
    Memory.write (p1 + 1) meta1
    Memory.write (p1 + 61) (meta1 + 32)
    Memory.write (p1 + 62) (meta1 + offFp)
    Memory.write (base + hdrMDst) mDst
    Memory.write (base + hdrPad) pad
    Memory.write (base + hdrItemHi) ibHi
    Memory.write (base + hdrQHi) qHi
    Memory.write (base + hdrDstOd) od
    Memory.write (base + hdrDstOt) ot
    Memory.write (base + hdrDstPb) ptrB
    Memory.write (base + hdrDstPg) pgB
    Memory.write (base + hdrDstMp) mp
    Memory.write (base + hdrPhase) 2

private theorem validHistory_writeLogFinishHdrProg {w : ℕ}
    {x : ((ℕ × ℕ) × (ℕ × ℕ)) × (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ))} {s : Memory.State}
    (h : let (((base, mDst), (pad, qHi)), (((od, ot), (ptrB, pgB)), (mp, offFp))) := x
         base + 192 ≤ s.frontier ∧ 4 ≤ w ∧ 32 ≤ mDst ∧
         Fits w (base + 192 + pad + mDst + 4) ∧
         offFp ≤ mDst ∧ Fits w mDst ∧ Fits w pad ∧ Fits w qHi ∧ Fits w od ∧ Fits w ot ∧
         Fits w ptrB ∧ Fits w pgB ∧ Fits w mp) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writeLogFinishHdrProg x)) := by
  rcases x with ⟨⟨⟨base, mDst⟩, ⟨pad, qHi⟩⟩, ⟨⟨⟨od, ot⟩, ⟨ptrB, pgB⟩⟩, ⟨mp, offFp⟩⟩⟩
  rcases s with ⟨m, fr⟩
  obtain ⟨hb, hw4, hm32, htop, hfp_le, hm_f, hp_f, hq_f, hod_f, hot_f, hpb_f, hpg_f, hmp_f⟩ := h
  have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) hw4
  dsimp only [Fits] at *
  unfold writeLogFinishHdrProg hdrPBase1 hdrMDst hdrPad hdrItemHi hdrQHi hdrDstOd hdrDstOt
    hdrDstPb hdrDstPg hdrDstMp hdrPhase
  dsimp only
  exact vh_wr (by omega) (by dsimp only [Fits]; omega) <|
    vh_wr (by omega) (by dsimp only [Fits]; omega) <|
    vh_wr (by omega) (by dsimp only [Fits]; omega) <|
    vh_wr (by omega) hm_f <| vh_wr (by omega) hp_f <|
    vh_wr (by omega) htop <| vh_wr (by omega) hq_f <|
    vh_wr (by omega) hod_f <| vh_wr (by omega) hot_f <|
    vh_wr (by omega) hpb_f <| vh_wr (by omega) hpg_f <|
    vh_wr (by omega) hmp_f <| vh_wr_only (by omega) (by dsimp only [Fits]; omega)

private theorem realizesBounded_writeLogFinishHdr :
    RealizesBounded .exact writeLogFinishHdrProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w (((base, mDst), (pad, _)), (_, (_, offFp))) s =>
        4 ≤ w ∧ base + 192 ≤ s.frontier ∧ 32 ≤ mDst ∧
        Fits w (base + 192 + pad + mDst + 4) ∧ offFp ≤ mDst)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨base, mDst⟩, ⟨pad, qHi⟩⟩, ⟨⟨⟨od, ot⟩, ⟨ptrB, pgB⟩⟩, ⟨mp, offFp⟩⟩⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hw4, hb, hm32, htop, hfp_le⟩ := h
    have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) hw4
    have hfr_w := hmem.1
    try simp only [hdrPBase1, hdrMDst, hdrPad, hdrItemHi, hdrQHi, hdrDstOd, hdrDstOt, hdrDstPb,
      hdrDstPg, hdrDstMp, hdrPhase, Fits] at *
    omega)

attribute [local irreducible] writeLogFinishHdrProg

/-- Read helper loading the `8` header words for `tickLogFinishProg` (`0` writes). -/
private def loadLogFinishArgsProg (base : ℕ) :
    Memory.Prog (((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) := do
  let nDst ← Memory.read (base + hdrNDst)
  let logN ← Memory.read (base + hdrLogN)
  let ell ← Memory.read (base + hdrEll)
  let ptrB ← Memory.read (base + hdrPtrB)
  let pgB ← Memory.read (base + hdrPgB)
  let mSrc ← Memory.read (base + hdrMSrc)
  let kb ← Memory.read (base + hdrKeyBits)
  let qLo ← Memory.read (base + hdrQLo)
  pure (((nDst, logN), (ell, ptrB)), ((pgB, mSrc), (kb, qLo)))

@[simp] private theorem runClient_state_loadLogFinishArgsProg (base : ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (loadLogFinishArgsProg base)).2.1 = s := by
  simp [loadLogFinishArgsProg]

@[simp] private theorem clientState_loadLogFinishArgsProg (base : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (loadLogFinishArgsProg base) = s :=
  runClient_state_loadLogFinishArgsProg base s

@[simp] private theorem clientResult_loadLogFinishArgsProg (base : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (loadLogFinishArgsProg base) =
      (((s.mem (base + hdrNDst), s.mem (base + hdrLogN)),
        (s.mem (base + hdrEll), s.mem (base + hdrPtrB))),
       ((s.mem (base + hdrPgB), s.mem (base + hdrMSrc)),
        (s.mem (base + hdrKeyBits), s.mem (base + hdrQLo)))) := by
  unfold loadLogFinishArgsProg
  simp

private theorem validHistory_loadLogFinishArgsProg {w base : ℕ} {s : Memory.State}
    (hb : base + 48 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (loadLogFinishArgsProg base)) := by
  unfold loadLogFinishArgsProg hdrNDst hdrLogN hdrEll hdrPtrB hdrPgB hdrMSrc hdrKeyBits hdrQLo
  exact vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <|
    vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) trivial

private theorem realizesBounded_loadLogFinishArgs :
    RealizesBounded .exact loadLogFinishArgsProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (fun _ base s => base + 48 ≤ s.frontier)
      (fun _ _ => 0) := by
  realize
  all_goals (
    have hfr_w := hmem.1
    try simp only [hdrNDst, hdrLogN, hdrEll, hdrPtrB, hdrPgB, hdrMSrc, hdrKeyBits, hdrQLo,
      Fits] at *
    omega)

attribute [local irreducible] loadLogFinishArgsProg

private abbrev logArgNDst (a : ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) : ℕ := a.1.1.1
private abbrev logArgLogN (a : ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) : ℕ := a.1.1.2
private abbrev logArgEll (a : ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) : ℕ := a.1.2.1
private abbrev logArgPtrB (a : ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) : ℕ := a.1.2.2
private abbrev logArgPgB (a : ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) : ℕ := a.2.1.1
private abbrev logArgMSrc (a : ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) : ℕ := a.2.1.2
private abbrev logArgKb (a : ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) : ℕ := a.2.2.1
private abbrev logArgQLo (a : ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) : ℕ := a.2.2.2

/-- Page-directory offset `res.1.1` returned by `writeLargeParamTableProg`. -/
abbrev paramTableOd (res : (ℕ × ℕ) × ℕ) : ℕ := res.1.1

/-- Page-tail offset `res.1.2` returned by `writeLargeParamTableProg`. -/
abbrev paramTableOt (res : (ℕ × ℕ) × ℕ) : ℕ := res.1.2

private abbrev pageScPgB (sc : ℕ × (ℕ × ℕ)) : ℕ := sc.2.1
private abbrev pageScMaxPages (sc : ℕ × (ℕ × ℕ)) : ℕ := sc.2.2

/-- Phase `1` (`log2Calc`) sub-stage `2`: populates `pBase1`, caches `43..47`, sets `pad`,
`itemBaseHi`, `qHi`, relocates `pBase1`'s 3 `metaBase`-dependent words to `meta1`, and enters
`growPre` (`phase = 2`). -/
def tickLogFinishProg (base : ℕ) : Memory.Prog Unit := do
  let a ← loadLogFinishArgsProg base
  let p1 := base + hdrPBase1
  let res ← writeLargeParamTableProg
    ((base, p1), ((logArgNDst a, base + 192), ((logArgLogN a, logArgEll a), logArgPgB a)))
  let pad ← max2Prog (logArgMSrc a, res.2)
  let sub1 ← clampSubProg (logArgLogN a, 12 * logArgEll a)
  let qDst ← clampSubProg (logArgKb a, sub1)
  let qHi ← max2Prog (logArgQLo a, qDst)
  let offFp ← Memory.read (p1 + 30)
  writeLogFinishHdrProg
    (((base, res.2), (pad, qHi)),
     (((paramTableOd res, paramTableOt res), (logArgPtrB a, logArgPgB a)),
      (logArgNDst a / logArgPgB a + 4, offFp)))

/-- Precondition for `tickLogFinishProg`. -/
@[expose] def TickLogFinishPre (w base : ℕ) (s : Memory.State) : Prop :=
  let nDst := s.mem (base + hdrNDst)
  let logN := s.mem (base + hdrLogN)
  let ell := s.mem (base + hdrEll)
  let pgB := s.mem (base + hdrPgB)
  11 ≤ w ∧ base + 192 ≤ s.frontier ∧ 0 < pgB ∧
  Fits w (12 * ell) ∧
  WriteLargeParamPre w ((base, base + hdrPBase1), ((nDst, base + 192), ((logN, ell), pgB))) s ∧
  (∀ c U V, RootStaticHeader c U V w base s.mem → whpThreshold c ≤ nDst → nDst ≤ U →
    Fits w (base + 192 + max (s.mem (base + hdrMSrc)) (epochMetaWordsWhp c w nDst) +
      epochMetaWordsWhp c w nDst + 4))

theorem validHistory_tickLogFinishProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : TickLogFinishPre w base s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (tickLogFinishProg base)) := by
  obtain ⟨hw11, hb, _, _, hwlp, hfit_all⟩ := hpre
  have hwlp' := hwlp
  obtain ⟨c, U, V, hdisj, hth, hNU, _, _, _, hlog_eq, hell_eq, hpg_eq, _, _, _, _, hhdr⟩ := hwlp'
  have hw_pos : 0 < w := by omega
  set nDst := s.mem (base + hdrNDst)
  let fl0 : FastEpochLayout := ⟨c, U, V, w, nDst, base + 192, base + hdrPBase1,
    ⟨0, 0, ⟨0, 0, 0, 0, w, 32, 4, 0, 0, 0, 0⟩⟩⟩
  have hspec := writeLargeParamTableProg_spec (fl := fl0) (s := s) hdisj hth hNU hw_pos hhdr
  unfold tickLogFinishProg
  refine vh_seq (validHistory_loadLogFinishArgsProg (by omega)) fun s0 hs0 a ha => ?_
  rw [hs0, clientState_loadLogFinishArgsProg, ha, clientResult_loadLogFinishArgsProg]
  dsimp only [nDst] at hwlp hlog_eq hell_eq hpg_eq ⊢
  rw [hlog_eq, hell_eq, hpg_eq] at hwlp ⊢
  have vhw := validHistory_writeLargeParamTableProg (s := s) hwlp
  refine vh_seq vhw fun s1 hs1 res hres => ?_
  have hfr1 : s1.frontier = s.frontier := hs1 ▸ hspec.2.1
  have hmDst : res.2 = epochMetaWordsWhp c w nDst := by rw [hres, hspec.1]
  have hod : res.1.1 = offPageDir c w nDst := by rw [hres, hspec.1]
  have hot : res.1.2 = offPageTail c w nDst := by rw [hres, hspec.1]
  have hoffFp : s1.mem (base + hdrPBase1 + 30) = offFpHash c w nDst := by
    rw [hs1]; exact hspec.2.2.2.1 30 (by decide)
  have he_end := offEpochEnd_eq_epochMetaWordsWhp (c := c) (w := w) hth
  have hm32 : 32 ≤ epochMetaWordsWhp c w nDst := by
    rw [← he_end]
    unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild
      offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
      offBktMeta offFpHash offBktHash
    omega
  have hfp_le_M : offFpHash c w nDst ≤ epochMetaWordsWhp c w nDst := by
    rw [← he_end]
    unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild
      offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
      offBktMeta offFpHash offBktHash
    omega
  have hod_le : res.1.1 ≤ epochMetaWordsWhp c w nDst := by
    rw [hod, ← he_end]; unfold offEpochEnd offPageTail; omega
  have hot_le : res.1.2 ≤ epochMetaWordsWhp c w nDst := by
    rw [hot, ← he_end]; unfold offEpochEnd; omega
  have htop := hfit_all c U V hhdr hth hNU
  have hnDst_w := hwf.2 (base + hdrNDst)
  have hqLo_w := hwf.2 (base + hdrQLo)
  have hkb_w := hwf.2 (base + hdrKeyBits)
  have hpB_w := hwf.2 (base + hdrPtrB)
  have hpg_w := hwf.2 (base + hdrPgB)
  rw [hpg_eq] at hpg_w
  have hms_w := hwf.2 (base + hdrMSrc)
  have hnd_pg : Fits w (s.mem (base + hdrNDst) / pageSizeWhp (s.mem (base + hdrNDst)) + 4) := by
    have hpg32 : 32 ≤ pageSizeWhp (s.mem (base + hdrNDst)) := le_max_left 32 _
    have hd_le : s.mem (base + hdrNDst) / pageSizeWhp (s.mem (base + hdrNDst)) ≤
        s.mem (base + hdrNDst) / 32 := Nat.div_le_div_left hpg32 (by decide)
    have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) (by omega)
    dsimp only [Fits] at hnDst_w ⊢; omega
  refine vh_seq (validHistory_max2Prog w _ s1) fun sa hsa pad hpad => ?_
  rw [hsa, clientState_max2Prog, hpad, clientResult_max2Prog]
  refine vh_seq (validHistory_clampSubProg w _ s1) fun sb hsb sub1 hsub1 => ?_
  rw [hsb, clientState_clampSubProg, hsub1, clientResult_clampSubProg]
  refine vh_seq (validHistory_clampSubProg w _ s1) fun sc hsc qDst hqDst => ?_
  rw [hsc, clientState_clampSubProg, hqDst, clientResult_clampSubProg]
  refine vh_seq (validHistory_max2Prog w _ s1) fun sd hsd qHi hqHi => ?_
  rw [hsd, clientState_max2Prog, hqHi, clientResult_max2Prog]
  refine vh_rd (by rw [hfr1]; unfold hdrPBase1; omega) ?_
  rw [hoffFp]
  refine validHistory_writeLogFinishHdrProg ?_
  dsimp only [Fits] at htop hqLo_w hkb_w hpB_w hpg_w hms_w ⊢
  rw [hfr1, hmDst]
  refine ⟨hb, by omega, hm32, htop, hfp_le_M, by omega, by simp [Nat.max_def]; split_ifs <;> omega,
    by simp [Nat.max_def]; split_ifs <;> omega, by omega, by omega, hpB_w, hpg_w, hnd_pg⟩

theorem realizesBounded_tickLogFinish :
    RealizesBounded .exact tickLogFinishProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      TickLogFinishPre (fun _ _ => 0) := by
  have hla := realizesBounded_loadLogFinishArgs
  have hwl := realizesBounded_writeLargeParamTable
  have hmx := realizesBounded_max2
  have hcs := realizesBounded_clampSub
  have hwh := realizesBounded_writeLogFinishHdr
  realize
  all_goals (
    obtain ⟨hw11, hb, hpg_pos, hell12, hwlp, hfit_all⟩ := h
    have hwlp' := hwlp
    obtain ⟨c, U, V, hdisj, hth, hNU, _, _, _, hlog_eq, hell_eq, hpg_eq, _, _, _, _, hhdr⟩ :=
      hwlp'
    have hw_pos : 0 < w := by omega
    have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) (by omega)
    have hfr_w := hmem.1
    set nDst := s.mem (d + hdrNDst)
    let fl0 : FastEpochLayout := ⟨c, U, V, w, nDst, d + 192, d + hdrPBase1,
      ⟨0, 0, ⟨0, 0, 0, 0, w, 32, 4, 0, 0, 0, 0⟩⟩⟩
    have hspec := writeLargeParamTableProg_spec (fl := fl0) (s := s) hdisj hth hNU hw_pos hhdr
    rw [← hlog_eq, ← hell_eq, ← hpg_eq] at hspec
    have hfr1 := hspec.2.1
    have hoffFp : ((Memory.spec 0).clientState s
        (writeLargeParamTableProg ((d, d + hdrPBase1),
          ((nDst, d + 192), ((s.mem (d + hdrLogN), s.mem (d + hdrEll)),
            s.mem (d + hdrPgB)))))).mem (d + hdrPBase1 + 30) = offFpHash c w nDst :=
      hspec.2.2.2.1 30 (by decide)
    have hm32 : 32 ≤ epochMetaWordsWhp c w nDst := by
      have he := offEpochEnd_eq_epochMetaWordsWhp (c := c) (w := w) hth
      rw [← he]
      unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild
        offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
        offBktMeta offFpHash offBktHash
      omega
    have hfp_le_M : offFpHash c w nDst ≤ epochMetaWordsWhp c w nDst := by
      have he := offEpochEnd_eq_epochMetaWordsWhp (c := c) (w := w) hth
      rw [← he]
      unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild
        offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
        offBktMeta offFpHash offBktHash
      omega
    have htop := hfit_all c U V hhdr hth hNU
    have hnDst_w : nDst < 2 ^ w := hmem.2 (d + hdrNDst)
    have hpg32 : 32 ≤ s.mem (d + hdrPgB) := hpg_eq.symm ▸ le_max_left 32 _
    have hd_le : nDst / s.mem (d + hdrPgB) ≤ nDst / 32 := Nat.div_le_div_left hpg32 (by decide)
    repeat rw [clientState_loadLogFinishArgsProg] at *
    repeat rw [clientResult_loadLogFinishArgsProg] at *
    dsimp only [Prod.fst, Prod.snd] at *
    first
    | exact hwlp
    | (repeat rw [clientState_max2Prog] at *
       repeat rw [clientResult_max2Prog] at *
       repeat rw [clientState_clampSubProg] at *
       dsimp only [fl0, nDst] at *
       try rw [hspec.1]
       try rw [hfr1]
       try rw [hoffFp]
       dsimp only [Prod.fst, Prod.snd, Nat.max_def] at *
       try simp only [hdrNDst, hdrLogN, hdrEll, hdrPgB, hdrMSrc, hdrPBase1, Fits] at *
       (try split_ifs) <;> omega))

attribute [local irreducible] tickLogFinishProg

/-- Phase `1` (`log2Calc`) dispatcher. -/
def tickLogProg (base : ℕ) : Memory.Prog Unit := do
  let sub ← Memory.read (base + hdrLogSub)
  if sub < 2 then tickLogShiftProg base else tickLogFinishProg base

/-- Precondition for `tickLogProg`. -/
@[expose] def TickLogPre (w base : ℕ) (s : Memory.State) : Prop :=
  1 ≤ w ∧ base + 48 ≤ s.frontier ∧
  if s.mem (base + hdrLogSub) < 2 then TickLogShiftPre w base s
  else TickLogFinishPre w base s

theorem validHistory_tickLogProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : TickLogPre w base s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (tickLogProg base)) := by
  obtain ⟨_, hb, hdisp⟩ := hpre
  unfold tickLogProg
  unfold hdrLogSub at hdisp ⊢
  refine vh_rd (by omega) ?_
  by_cases hlt : s.mem (base + 36) < 2
  · rw [ite_eq_left hlt] at hdisp ⊢; exact validHistory_tickLogShiftProg hwf hdisp
  · rw [ite_eq_right hlt] at hdisp ⊢; exact validHistory_tickLogFinishProg hwf hdisp

theorem realizesBounded_tickLog :
    RealizesBounded .exact tickLogProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      TickLogPre (fun _ _ => 0) := by
  have hs := realizesBounded_tickLogShift
  have hf := realizesBounded_tickLogFinish
  realize
  all_goals (
    obtain ⟨hw1, hb, hdisp⟩ := h
    have hw6 := six_le_of_frontier48 hmem hb
    have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    unfold hdrLogSub at *
    dsimp only [Fits] at *
    by_cases hsub : s.mem (d + 36) < 2
    · rw [ite_eq_left hsub] at hdisp; first | exact hdisp | omega
    · rw [ite_eq_right hsub] at hdisp; first | exact hdisp | omega)

attribute [local irreducible] tickLogProg

/-- Phase `2` (`growPre`) tick: checks whether `newFr` covers `itemBaseHi + pairStreamWords nLive`
and transitions `pBase0` into `SplitPair` mode (`phase = 3`). -/
def tickGrowPreProg : ℕ × ℕ → Memory.Prog Unit
  | (base, newFr) => do
    let wv ← Memory.read (base + hdrW)
    let vb ← Memory.read (base + hdrValBits)
    let nLive ← Memory.read (base + hdrLive)
    let ibHi ← Memory.read (base + hdrItemHi)
    let qHi ← Memory.read (base + hdrQHi)
    let pw ← pairStreamWordsSafeProg (((nLive, qHi), vb), wv)
    if newFr < ibHi + pw then
      pure ()
    else do
      Memory.write (base + hdrSplit) nLive
      setSplitSlotIoProg ((base, base + hdrPBase0), nLive)
      Memory.write (base + hdrPhase) 3

/-- Precondition for `tickGrowPreProg`. -/
@[expose] def TickGrowPrePre (w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (base, _), s =>
    11 ≤ w ∧ s.mem (base + hdrW) = w ∧ base + 192 ≤ s.frontier ∧
    s.mem (base + hdrQHi) ≤ w ∧ s.mem (base + hdrValBits) ≤ w ∧
    Fits w (s.mem (base + hdrItemHi) +
      pairStreamWords (s.mem (base + hdrLive)) (s.mem (base + hdrQHi))
        (s.mem (base + hdrValBits)) w)

theorem validHistory_tickGrowPreProg {w : ℕ} {x : ℕ × ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : TickGrowPrePre w x s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (tickGrowPreProg x)) := by
  rcases x with ⟨base, newFr⟩
  obtain ⟨hw11, _, hb, _, _, _⟩ := hpre
  have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) (by omega)
  unfold tickGrowPreProg hdrW hdrValBits hdrLive hdrItemHi hdrQHi hdrSplit hdrPBase0 hdrPhase at *
  refine vh_rd (by omega) <| vh_rd (by omega) <| vh_rd (by omega) <|
    vh_rd (by omega) <| vh_rd (by omega) ?_
  refine vh_seq (validHistory_pairStreamWordsSafeProg w _ s) fun s1 hs1 _ _ => ?_
  rw [hs1, clientState_pairStreamWordsSafeProg]
  refine vh_ite _ (fun _ => trivial) fun _ => ?_
  have hnl_f := hwf.2 (base + 10)
  have hwf2 : Memory.WellFormed w
      ⟨Function.update s.mem (base + 16) (s.mem (base + 10)), s.frontier⟩ := by
    change Memory.WellFormed w (Memory.step s (.write (base + 16) (s.mem (base + 10)))).1
    exact hwf.step ⟨by omega, hnl_f⟩
  rcases s with ⟨m, fr⟩; dsimp only at hb hwf2 ⊢
  refine vh_wr (by omega) hnl_f ?_
  have vhs := validHistory_setSplitSlotIoProg
    (s := ⟨Function.update m (base + 16) (m (base + 10)), fr⟩)
    (pBase := base + 64) hwf2 (by dsimp only; omega) (by dsimp only; omega) (by omega) hnl_f
  exact vh_seq vhs fun s3 hs3 _ _ => by
    have hfr3 : s3.frontier = fr := hs3 ▸ setSplitSlotIoProg_fr _ _
    rcases s3 with ⟨_, fr3⟩; dsimp only at hfr3
    exact vh_wr_only (by omega) (by dsimp only [Fits]; omega)

theorem realizesBounded_tickGrowPre :
    RealizesBounded .exact tickGrowPreProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      TickGrowPrePre (fun _ _ => 0) := by
  have hps := realizesBounded_pairStreamWordsSafe
  have hss := realizesBounded_setSplitSlotIo
  realize
  all_goals (
    rcases d with ⟨base, newFr⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hw11, hwv, hb, hqH, hvb, hfit⟩ := h
    have hw_pos : 0 < w := by omega
    have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) (by omega)
    have hfr_w := hmem.1
    subst hwv
    repeat rw [clientState_pairStreamWordsSafeProg] at *
    repeat rw [pairStreamWordsSafeProg_res hw_pos] at *
    try simp only [hdrW, hdrValBits, hdrLive, hdrItemHi, hdrQHi, hdrSplit, hdrPBase0,
      hdrPhase, Fits] at *
    try omega)

attribute [local irreducible] tickGrowPreProg

/-- Phase `3` (`slideUp`) tick: slides up to `itemBatchWhp` pairs from `(itemBaseLo, qLo)` to
`(itemBaseHi, qHi)`; when `s_new = 0`, switches `pBase0` to direct mode at `itemBaseHi` and enters
`zeroMeta` (`phase = 4`, if `nDst > 0`) or `initDir` (`phase = 6`, if `nDst = 0`). -/
def tickSlideUpProg (base : ℕ) : Memory.Prog Unit := do
  let sp ← Memory.read (base + hdrSplit)
  let nLive ← Memory.read (base + hdrLive)
  let nDst ← Memory.read (base + hdrNDst)
  let ibHi ← Memory.read (base + hdrItemHi)
  let qHi ← Memory.read (base + hdrQHi)
  let ctx ← loadSplitPairCtxProg base
  let sp' ← slideUpBatchProg ((ctx, sp), itemBatchWhp)
  Memory.write (base + hdrSplit) sp'
  if sp' = 0 then do
    setDirectSlotIoProg ((base, base + hdrPBase0), ((ibHi, qHi), nLive))
    Memory.write (base + hdrCur) 0
    if nDst = 0 then do
      Memory.write (base + hdrSmallMeta1) 0
      Memory.write (base + hdrSmallMeta1 + 1) 0
      Memory.write (base + hdrPhase) 6
    else
      Memory.write (base + hdrPhase) 4
  else
    pure ()

/-- Precondition for `tickSlideUpProg`. -/
@[expose] def TickSlideUpPre (w base : ℕ) (s : Memory.State) : Prop :=
  11 ≤ w ∧ base + 192 ≤ s.frontier ∧
  let ctx := (Memory.spec 0).clientResult s (loadSplitPairCtxProg base)
  let sp := s.mem (base + hdrSplit)
  SlideUpStepPre w (ctx, sp) s ∧
  iterationSafe slideUpStepProg SlideUpStepPre w ctx itemBatchWhp sp s

theorem validHistory_tickSlideUpProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : TickSlideUpPre w base s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (tickSlideUpProg base)) := by
  obtain ⟨hw11, hb, hstep_pre, _⟩ := hpre
  have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) (by omega)
  have hz : Fits w 0 := Nat.two_pow_pos w
  unfold tickSlideUpProg
  refine vh_rd (by unfold hdrSplit; omega) <| vh_rd (by unfold hdrLive; omega) <|
    vh_rd (by unfold hdrNDst; omega) <| vh_rd (by unfold hdrItemHi; omega) <|
    vh_rd (by unfold hdrQHi; omega) ?_
  refine vh_seq (validHistory_loadSplitPairCtxProg (by omega)) fun s1 hs1 ctx hctx => ?_
  rw [hs1, clientState_loadSplitPairCtxProg, hctx]
  have vhb := validHistory_slideUpBatchProg (fuel := itemBatchWhp) hwf hstep_pre
  refine vh_seq vhb fun s2 hs2 sp' hsp' => ?_
  have hwf2 := wf_step hwf vhb
  obtain ⟨hfr_b, hle_b⟩ := slideUpBatchProg_fr_and_le
    ((Memory.spec 0).clientResult s (loadSplitPairCtxProg base)) itemBatchWhp
    (s.mem (base + hdrSplit)) s
  have hfr2 : s2.frontier = s.frontier := hs2 ▸ hfr_b
  have hsp'_f : Fits w sp' := by
    have hsp_w := hwf.2 (base + hdrSplit)
    have hle_sp : sp' ≤ s.mem (base + hdrSplit) := hsp' ▸ hle_b
    dsimp only [Fits] at hsp_w ⊢; omega
  have hwf3 : Memory.WellFormed w ⟨Function.update s2.mem (base + hdrSplit) sp', s2.frontier⟩ := by
    change Memory.WellFormed w (Memory.step s2 (.write (base + hdrSplit) sp')).1
    rw [hs2]
    exact hwf2.step ⟨by rw [hfr_b]; unfold hdrSplit; omega, hsp'_f⟩
  rcases s2 with ⟨m2, fr2⟩
  dsimp only at hfr2 hwf3
  refine vh_wr (by unfold hdrSplit; omega) hsp'_f ?_
  refine vh_ite (sp' = 0) (fun _ => ?_) (fun _ => trivial)
  have vhd := validHistory_setDirectSlotIoProg
    (s := ⟨Function.update m2 (base + hdrSplit) sp', fr2⟩)
    (base := base) (pBase := base + hdrPBase0)
    (ib := s.mem (base + hdrItemHi)) (qb := s.mem (base + hdrQHi)) (nc := s.mem (base + hdrLive))
    hwf3 (by dsimp only; omega) (by dsimp only; unfold hdrPBase0; omega) (by omega)
    (hwf.2 _) (hwf.2 _) (hwf.2 _)
  refine vh_seq vhd fun s4 hs4 _ _ => ?_
  have hfr4 : s4.frontier = s.frontier := (hs4 ▸ setDirectSlotIoProg_fr _ _).trans hfr2
  rcases s4 with ⟨_, fr4⟩
  dsimp only at hfr4
  refine vh_wr (by unfold hdrCur; omega) hz ?_
  refine vh_ite _ (fun _ => ?_) (fun _ => ?_)
  · unfold hdrSmallMeta1 hdrPhase
    exact vh_wr (by omega) hz <|
      vh_wr (by omega) hz <|
      vh_wr_only (by omega) (by dsimp only [Fits]; omega)
  · unfold hdrPhase
    exact vh_wr_only (by omega) (by dsimp only [Fits]; omega)

theorem realizesBounded_tickSlideUp :
    RealizesBounded .exact tickSlideUpProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      TickSlideUpPre (fun _ _ => 0) := by
  have hl := realizesBounded_loadSplitPairCtx
  have hb := realizesBounded_slideUpBatch
  have hd := realizesBounded_setDirectSlotIo
  realize
  all_goals (
    obtain ⟨hw11, hb_fr, hstep_pre, hsafe⟩ := h
    have h2048 : 2048 ≤ 2 ^ w :=
      (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
    have hfr_w := hmem.1
    have hfr2 : ((Memory.spec 0).clientState s
        (slideUpBatchProg (((Memory.spec 0).clientResult s (loadSplitPairCtxProg d),
          s.mem (d + hdrSplit)), itemBatchWhp))).frontier = s.frontier :=
      (slideUpBatchProg_fr_and_le _ _ _ s).1
    repeat rw [clientState_loadSplitPairCtxProg] at *
    try rw [hfr2]
    try simp only [hdrSplit, hdrLive, hdrNDst, hdrItemHi, hdrQHi, hdrPBase0, hdrCur,
      hdrSmallMeta1, hdrPhase, itemBatchWhp, Fits] at *
    first | exact hsafe | omega)

attribute [local irreducible] tickSlideUpProg

/-- Optional Stage-B (`stg ≠ 0`) parameter-table write at the end of `zeroMeta`. -/
private def optWriteStageBTableProg :
    ℕ × ((ℕ × ℕ) × ((ℕ × ℕ) × ((ℕ × ℕ) × ℕ))) → Memory.Prog Unit
  | (stg, args) =>
    if stg = 0 then
      pure ()
    else do
      let _ ← writeLargeParamTableProg args
      pure ()

private theorem validHistory_optWriteStageBTableProg {w stg : ℕ}
    {args : (ℕ × ℕ) × ((ℕ × ℕ) × ((ℕ × ℕ) × ℕ))} {s : Memory.State}
    (hpre : stg ≠ 0 → WriteLargeParamPre w args s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (optWriteStageBTableProg (stg, args))) := by
  rcases args with ⟨⟨base, pBase⟩, ⟨⟨nDst, mb⟩, ⟨⟨logN, ell⟩, pgB⟩⟩⟩
  unfold optWriteStageBTableProg; dsimp only
  refine vh_ite (stg = 0) (fun _ => trivial) fun hne => ?_
  have hp' := hpre hne
  obtain ⟨_, _, _, _, _, _, _, _, _, hlog, hell, hpg, _⟩ := hpre hne
  rw [hlog, hell, hpg] at hp' ⊢
  exact vh_seq (validHistory_writeLargeParamTableProg hp') fun _ _ _ _ => trivial

private theorem optWriteStageBTableProg_fr {w stg base nDst logN ell pgB : ℕ} {s : Memory.State}
    (hw_pos : 0 < w)
    (hpre : stg ≠ 0 → WriteLargeParamPre w
      ((base, base + hdrPBase0), ((nDst, base + 192), ((logN, ell), pgB))) s) :
    ((Memory.spec 0).clientState s (optWriteStageBTableProg
      (stg, ((base, base + hdrPBase0), ((nDst, base + 192), ((logN, ell), pgB)))))).frontier =
      s.frontier := by
  unfold optWriteStageBTableProg; dsimp only
  by_cases h0 : stg = 0
  · rw [ite_eq_left h0]; rfl
  · rw [ite_eq_right h0]
    obtain ⟨c, U, V, hdisj, hth, hNU, _, _, _, hlog, hell, hpg, _, _, _, _, hhdr⟩ := hpre h0
    let fl0 : FastEpochLayout := ⟨c, U, V, w, nDst, base + 192, base + hdrPBase0,
      ⟨0, 0, ⟨0, 0, 0, 0, w, 32, 4, 0, 0, 0, 0⟩⟩⟩
    have hsp := writeLargeParamTableProg_spec (fl := fl0) (s := s) hdisj hth hNU hw_pos hhdr
    rw [← hlog, ← hell, ← hpg] at hsp
    rw [StateTransitionSpec.clientState_bind]
    exact hsp.2.1

private theorem realizesBounded_optWriteStageBTable :
    RealizesBounded .exact optWriteStageBTableProg
      (WordEncoding.encode (α := ℕ × ((ℕ × ℕ) × ((ℕ × ℕ) × ((ℕ × ℕ) × ℕ)))))
      (WordEncoding.encode (α := Unit))
      (fun w (stg, args) s => 1 ≤ w ∧ (stg ≠ 0 → WriteLargeParamPre w args s))
      (fun _ _ => 0) := by
  have hwl := realizesBounded_writeLargeParamTable
  realize
  all_goals (
    rcases d with ⟨stg, args⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨_, hpre⟩ := h
    exact hpre ‹_›)

attribute [local irreducible] optWriteStageBTableProg

/-- Phase `4` (`zeroMeta`) tick: zeroes up to `bulkBatchWhp` words of `metaDst`; when
`cur' = M_dst`, populates `pBase0` (if `stage = 1`) and transitions to `randFill` (`phase = 5`,
`cur := 32`). -/
def tickZeroMetaProg (base : ℕ) : Memory.Prog Unit := do
  let stg ← Memory.read (base + hdrStage)
  let cur ← Memory.read (base + hdrCur)
  let mDst ← Memory.read (base + hdrMDst)
  let pad ← Memory.read (base + hdrPad)
  let nDst ← Memory.read (base + hdrNDst)
  let logN ← Memory.read (base + hdrLogN)
  let ell ← Memory.read (base + hdrEll)
  let pgB ← Memory.read (base + hdrPgB)
  let metaDst ← metaDstAddrProg (stg, (base, pad))
  let cur' ← zeroWordsBatchProg (((metaDst, mDst), cur), bulkBatchWhp)
  if cur' < mDst then
    Memory.write (base + hdrCur) cur'
  else do
    optWriteStageBTableProg
      (stg, ((base, base + hdrPBase0), ((nDst, base + 192), ((logN, ell), pgB))))
    Memory.write (base + hdrCur) 32
    Memory.write (base + hdrPhase) 5

/-- Precondition for `tickZeroMetaProg`. -/
@[expose] def TickZeroMetaPre (w base : ℕ) (s : Memory.State) : Prop :=
  11 ≤ w ∧ base + 192 ≤ s.frontier ∧
  let stg := s.mem (base + hdrStage)
  let cur := s.mem (base + hdrCur)
  let mDst := s.mem (base + hdrMDst)
  let pad := s.mem (base + hdrPad)
  let metaDst := if stg = 0 then base + 192 + pad else base + 192
  cur ≤ mDst ∧ metaDst < s.frontier ∧ metaDst + mDst ≤ s.frontier ∧
  (stg ≠ 0 →
    WriteLargeParamPre w ((base, base + hdrPBase0), ((s.mem (base + hdrNDst), base + 192),
      ((s.mem (base + hdrLogN), s.mem (base + hdrEll)), s.mem (base + hdrPgB))))
      ((Memory.spec 0).clientState s (zeroWordsBatchProg (((metaDst, mDst), cur), bulkBatchWhp))))

theorem validHistory_tickZeroMetaProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : TickZeroMetaPre w base s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (tickZeroMetaProg base)) := by
  obtain ⟨hw11, hb, hcur_le, hmd_lt, hmd_fr, hwlp⟩ := hpre
  have h2048 : 2048 ≤ 2 ^ w :=
    (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
  have hw_pos : 0 < w := by omega
  unfold tickZeroMetaProg
  refine vh_rd (by unfold hdrStage; omega) <| vh_rd (by unfold hdrCur; omega) <|
    vh_rd (by unfold hdrMDst; omega) <| vh_rd (by unfold hdrPad; omega) <|
    vh_rd (by unfold hdrNDst; omega) <| vh_rd (by unfold hdrLogN; omega) <|
    vh_rd (by unfold hdrEll; omega) <| vh_rd (by unfold hdrPgB; omega) ?_
  refine vh_seq (validHistory_metaDstAddrProg w _ s) fun s0 hs0 metaDst hmd => ?_
  rw [hs0, clientState_metaDstAddrProg, hmd, clientResult_metaDstAddrProg]
  have vhz := validHistory_zeroWordsBatchProg (w := w) (fuel := bulkBatchWhp)
    ⟨hw_pos, hcur_le, hmd_lt, hmd_fr⟩
  have hzb := zeroWordsBatchProg_spec hw_pos hcur_le hmd_lt hmd_fr bulkBatchWhp
  refine vh_seq vhz fun s1 hs1 cur' _ => ?_
  have hfr1 : s1.frontier = s.frontier := hs1 ▸ hzb.2.2.1
  have hmDst_w := hwf.2 (base + hdrMDst)
  refine vh_ite (cur' < s.mem (base + hdrMDst))
    (fun hlt => by
      rcases s1 with ⟨_, fr1⟩; dsimp only at hfr1
      exact vh_wr_only (by unfold hdrCur; omega) (lt_trans hlt hmDst_w))
    fun _ => ?_
  refine vh_seq (validHistory_optWriteStageBTableProg (fun hne => hs1 ▸ hwlp hne))
    fun s2 hs2 _ _ => ?_
  have hfr2 : s2.frontier = s.frontier := by
    rw [hs2]
    exact (optWriteStageBTableProg_fr hw_pos (fun hne => hs1 ▸ hwlp hne)).trans hfr1
  rcases s2 with ⟨_, fr2⟩; dsimp only at hfr2
  unfold hdrCur hdrPhase
  exact vh_wr (by omega) (by dsimp only [Fits]; omega) <|
    vh_wr_only (by omega) (by dsimp only [Fits]; omega)

theorem realizesBounded_tickZeroMeta :
    RealizesBounded .exact tickZeroMetaProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      TickZeroMetaPre (fun _ _ => 0) := by
  have hmd := realizesBounded_metaDstAddr
  have hzb := realizesBounded_zeroWordsBatch
  have howl := realizesBounded_optWriteStageBTable
  realize
  all_goals (
    obtain ⟨hw11, hb, hcur_le, hmd_lt, hmd_fr, hwlp⟩ := h
    have hw_pos : 0 < w := by omega
    have h2048 : 2048 ≤ 2 ^ w :=
      (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
    have hfr_w := hmem.1
    have hzb0 := zeroWordsBatchProg_spec hw_pos hcur_le hmd_lt hmd_fr bulkBatchWhp
    have hmDst_w : s.mem (d + hdrMDst) < 2 ^ w := hmem.2 (d + hdrMDst)
    repeat rw [clientState_metaDstAddrProg] at *
    repeat rw [clientResult_metaDstAddrProg] at *
    first
    | exact hzb0.1
    | exact hwlp
    | (try simp only [hdrStage, hdrCur, hdrMDst, hdrPad, hdrNDst, hdrLogN, hdrEll, hdrPgB,
         hdrPBase0, hdrPhase, bulkBatchWhp, Fits] at *
       by_cases hstg : s.mem (d + 12) = 0 <;> (simp only [hstg, ↓reduceIte] at *; omega)))

attribute [local irreducible] tickZeroMetaProg

/-- Phase `5` (`randFill`) prep tick: advances `hdrCur` by up to `bulkBatchWhp` toward `offBktMeta`
and returns `(rCur, (rEnd, rMask))` with overflow-free `rMask = 2 ^ w - 1`. -/
def tickRandPrepProg (base : ℕ) : Memory.Prog (ℕ × (ℕ × ℕ)) := do
  let wv ← Memory.read (base + hdrW)
  let stg ← Memory.read (base + hdrStage)
  let cur ← Memory.read (base + hdrCur)
  let pad ← Memory.read (base + hdrPad)
  let slots ← slotPairProg (stg, base)
  let offBM ← Memory.read (slots.2 + 31)
  let metaDst ← metaDstAddrProg (stg, (base, pad))
  let rem ← clampSubProg (offBM, cur)
  let step ← min2Prog (bulkBatchWhp, rem)
  let endOff ← pure (cur + step)
  Memory.write (base + hdrCur) endOff
  let half ← pure ((1 : ℕ) <<< (wv - 1))
  let rMask ← pure ((half - 1) * 2 + 1)
  pure (metaDst + cur, (metaDst + endOff, rMask))

/-- Precondition for `tickRandPrepProg`. -/
@[expose] def TickRandPrepPre (w base : ℕ) (s : Memory.State) : Prop :=
  11 ≤ w ∧ s.mem (base + hdrW) = w ∧ base + 192 ≤ s.frontier ∧
  let stg := s.mem (base + hdrStage)
  let pDst := if stg = 0 then base + hdrPBase1 else base + hdrPBase0
  let metaDst := if stg = 0 then base + 192 + s.mem (base + hdrPad) else base + 192
  s.mem (base + hdrCur) ≤ s.mem (pDst + 31) ∧
  metaDst + s.mem (pDst + 31) ≤ s.frontier

theorem validHistory_tickRandPrepProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : TickRandPrepPre w base s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (tickRandPrepProg base)) := by
  obtain ⟨_, _, hb, hcur_le, hfr_end⟩ := hpre
  have hfr_w := hwf.1
  unfold tickRandPrepProg
  refine vh_rd (by unfold hdrW; omega) <| vh_rd (by unfold hdrStage; omega) <|
    vh_rd (by unfold hdrCur; omega) <| vh_rd (by unfold hdrPad; omega) ?_
  refine vh_seq (validHistory_slotPairProg w _ s) fun s0 hs0 slots hsl => ?_
  rw [hs0, clientState_slotPairProg, hsl, clientResult_slotPairProg]
  dsimp only
  refine vh_rd (by unfold hdrPBase0 hdrPBase1; split_ifs <;> omega) ?_
  refine vh_seq (validHistory_metaDstAddrProg w _ s) fun s1 hs1 metaDst hmd => ?_
  rw [hs1, clientState_metaDstAddrProg, hmd, clientResult_metaDstAddrProg]
  refine vh_seq (validHistory_clampSubProg w _ s) fun s2 hs2 rem hrem => ?_
  rw [hs2, clientState_clampSubProg, hrem, clientResult_clampSubProg]
  refine vh_seq (validHistory_min2Prog w _ s) fun s3 hs3 step hstep => ?_
  rw [hs3, clientState_min2Prog, hstep, clientResult_min2Prog]
  simp only [pure_bind]
  refine vh_wr (by unfold hdrCur; omega) ?_ trivial
  dsimp only [Fits, Nat.min_def] at *; (try split_ifs at *) <;> omega

theorem realizesBounded_tickRandPrep :
    RealizesBounded .exact tickRandPrepProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      TickRandPrepPre (fun _ _ => 0) := by
  have hsl := realizesBounded_slotPair
  have hmd := realizesBounded_metaDstAddr
  have hcs := realizesBounded_clampSub
  have hmn := realizesBounded_min2
  realize
  all_goals (
    obtain ⟨hw11, hwv, hb, hcur_le, hfr_end⟩ := h
    have h2048 : 2048 ≤ 2 ^ w :=
      (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hfr_w := hmem.1
    have hpow_lt : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
    have hsh : (1 : ℕ) <<< (w - 1) = 2 ^ (w - 1) := shift_one_eq _
    have hpow : 2 ^ (w - 1) * 2 = 2 ^ w := by
      rw [← Nat.pow_succ, show (w - 1).succ = w by omega]
    have hp1 : 1 ≤ 2 ^ (w - 1) := Nat.one_le_two_pow
    subst hwv
    repeat rw [clientState_slotPairProg] at *
    repeat rw [clientResult_slotPairProg] at *
    repeat rw [clientState_metaDstAddrProg] at *
    repeat rw [clientResult_metaDstAddrProg] at *
    repeat rw [clientState_clampSubProg] at *
    repeat rw [clientResult_clampSubProg] at *
    repeat rw [clientResult_min2Prog] at *
    dsimp only [Prod.fst, Prod.snd] at *
    try rw [hsh] at *
    try simp only [hdrW, hdrStage, hdrCur, hdrPad, hdrPBase0, hdrPBase1, bulkBatchWhp, Fits,
      Nat.min_def] at *
    by_cases hstg : s.mem (d + 12) = 0 <;> simp only [hstg, ↓reduceIte] at * <;>
      (try split_ifs) <;> omega)

attribute [local irreducible] tickRandPrepProg

/-- Snapshot quotient `if nLive < pg + (pg + pg / 2) then 0 else (nLive - (pg + pg / 2)) / pg`. -/
private def calcQSnapProg : ℕ × ℕ → Memory.Prog ℕ
  | (nLive, pg) =>
    let base_r := pg + pg / 2
    if nLive < pg + base_r then pure 0 else pure ((nLive - base_r) / pg)

@[simp] private theorem runClient_state_calcQSnapProg (x : ℕ × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (calcQSnapProg x)).2.1 = s := by
  rcases x with ⟨nLive, pg⟩; unfold calcQSnapProg; dsimp only; split_ifs <;> rfl

@[simp] private theorem clientState_calcQSnapProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (calcQSnapProg x) = s :=
  runClient_state_calcQSnapProg x s

private theorem clientResult_calcQSnapProg_le (nLive pg : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (calcQSnapProg (nLive, pg)) ≤ nLive := by
  unfold calcQSnapProg; dsimp only
  have hd := Nat.div_le_self (nLive - (pg + pg / 2)) pg
  split_ifs <;> (simp only [StateTransitionSpec.clientResult, prog_clientResult_pure]; omega)

private theorem validHistory_calcQSnapProg (w : ℕ) (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (calcQSnapProg x)) := by
  rcases x with ⟨nLive, pg⟩; unfold calcQSnapProg; dsimp only; split_ifs <;> exact trivial

private theorem realizesBounded_calcQSnap :
    RealizesBounded .exact calcQSnapProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (_, pg) _ => 0 < pg ∧ Fits w (3 * pg))
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨nLive, pg⟩
    dsimp only [Fits] at *
    obtain ⟨hpg_pos, h3pg⟩ := h
    have hd := Nat.div_le_self (nLive - (pg + pg / 2)) pg
    omega)

attribute [local irreducible] calcQSnapProg

/-- Phase `6` (`initDir`) tick: initializes up to `bulkBatchWhp` directory entries of `pgHost`;
when `cur' = maxPages`, snapshots `(nSnap, qSnap)` and enters `initTail` (`phase = 7`). -/
def tickInitDirProg (base : ℕ) : Memory.Prog Unit := do
  let cur ← Memory.read (base + hdrCur)
  let nLive ← Memory.read (base + hdrLive)
  let ctx ← loadHostCtxProg (base, 1)
  let sc ← pageCtxScalarsProg ctx
  let cur' ← pageInitDirBatchProg ((ctx, cur), bulkBatchWhp)
  if cur' < pageScMaxPages sc then
    Memory.write (base + hdrCur) cur'
  else do
    let qSnap ← calcQSnapProg (nLive, pageScPgB sc)
    Memory.write (base + hdrNSnap) nLive
    Memory.write (base + hdrQSnap) qSnap
    Memory.write (base + hdrCur) 0
    Memory.write (base + hdrPhase) 7

/-- Precondition for `tickInitDirProg`. -/
@[expose] def TickInitDirPre (w base : ℕ) (s : Memory.State) : Prop :=
  11 ≤ w ∧ base + 192 ≤ s.frontier ∧ Fits w (base + 192 + s.mem (base + hdrPad)) ∧
  (PageArenaLayout.ofCtx ((Memory.spec 0).clientResult s (loadHostCtxProg (base, 1)))).Valid
    w s.frontier

theorem validHistory_tickInitDirProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : TickInitDirPre w base s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (tickInitDirProg base)) := by
  obtain ⟨hw11, hb, _, hv_ctx⟩ := hpre
  have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) (by omega)
  have hz : Fits w 0 := Nat.two_pow_pos w
  unfold tickInitDirProg
  refine vh_rd (by unfold hdrCur; omega) <| vh_rd (by unfold hdrLive; omega) ?_
  refine vh_seq (validHistory_loadHostCtxProg (by omega)) fun s1 hs1 ctx hctx => ?_
  rw [hs1, clientState_loadHostCtxProg] at *
  rw [← hctx] at hv_ctx
  refine vh_seq (validHistory_pageCtxScalarsProg w ctx s) fun sa hsa sc hsc => ?_
  rw [hsa, clientState_pageCtxScalarsProg, hsc, clientResult_pageCtxScalarsProg]
  dsimp only
  have vhb := validHistory_pageInitDirBatchProg (cur := s.mem (base + hdrCur))
    (fuel := bulkBatchWhp) hwf hv_ctx
  refine vh_seq vhb fun s2 hs2 cur' _ => ?_
  have hfr2 : s2.frontier = s.frontier := by
    have hce : (PageArenaLayout.ofCtx ctx).toCtx = ctx := by
      rcases ctx with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩; rfl
    have hw_c : 0 < (PageArenaLayout.ofCtx ctx).w := by rw [← hv_ctx.2.1]; exact hv_ctx.1
    have hfrm := pageInitDirBatchProg_frame (L := PageArenaLayout.ofCtx ctx)
      hw_c (s.mem (base + hdrCur)) bulkBatchWhp
    rw [hce] at hfrm
    exact hs2 ▸ hfrm.frontier_eq s
  have hmp_w : (PageArenaLayout.ofCtx ctx).maxPages < 2 ^ w := by
    have hmp4 := pageArenaValid_mp4_lt hv_ctx; omega
  rcases s2 with ⟨m2, fr2⟩; dsimp only at hfr2
  refine vh_ite (cur' < (PageArenaLayout.ofCtx ctx).maxPages)
    (fun hlt => vh_wr_only (by unfold hdrCur; omega) (lt_trans hlt hmp_w)) fun _ => ?_
  refine vh_seq (validHistory_calcQSnapProg w _ _) fun sb hsb qSnap hqSnap => ?_
  rw [hsb, clientState_calcQSnapProg]
  have hnl_w := hwf.2 (base + hdrLive)
  have hqs_w : Fits w qSnap :=
    lt_of_le_of_lt (hqSnap ▸ clientResult_calcQSnapProg_le _ _ _) hnl_w
  unfold hdrNSnap hdrQSnap hdrCur hdrPhase
  exact vh_wr (by omega) hnl_w <|
    vh_wr (by omega) hqs_w <|
    vh_wr (by omega) hz <|
    vh_wr_only (by omega) (by dsimp only [Fits]; omega)

theorem realizesBounded_tickInitDir :
    RealizesBounded .exact tickInitDirProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      TickInitDirPre (fun _ _ => 0) := by
  have hl := realizesBounded_loadHostCtx
  have hsc := realizesBounded_pageCtxScalars
  have hb := realizesBounded_pageInitDirBatch
  have hcq := realizesBounded_calcQSnap
  realize
  all_goals (
    obtain ⟨hw11, hb_fr, hpad, hv_ctx⟩ := h
    have h2048 : 2048 ≤ 2 ^ w :=
      (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
    have hfr_w := hmem.1
    set ctx := (Memory.spec 0).clientResult s (loadHostCtxProg (d, 1))
    have hsafe : ∀ fuel c0 (st : Memory.State),
        (PageArenaLayout.ofCtx ctx).Valid w st.frontier →
        iterationSafe pageInitDirStepProg
          (fun w' (c', _) s' => (PageArenaLayout.ofCtx c').Valid w' s'.frontier)
          w ctx fuel c0 st := by
      intro fuel
      induction fuel with
      | zero => intro _ _ _; exact trivial
      | succ k ih =>
        intro c0 st hv_st
        have hfr_s1 := pageInitDirStepProg_fr ctx c0 w st hv_st
        unfold iterationSafe
        rw [clientResult_width, clientState_width]
        exact ⟨hv_st, ih _ _ (hfr_s1.symm ▸ hv_st)⟩
    have hpg32 : 32 ≤ (PageArenaLayout.ofCtx ctx).pgB := hv_ctx.2.2.2.2.2.1
    have hpg16 := pageArenaValid_pg16_lt hv_ctx
    have hmp4 := pageArenaValid_mp4_lt hv_ctx
    have hnl_w : s.mem (d + hdrLive) < 2 ^ w := hmem.2 (d + hdrLive)
    repeat rw [clientState_loadHostCtxProg] at *
    repeat rw [clientState_pageCtxScalarsProg] at *
    repeat rw [clientResult_pageCtxScalarsProg] at *
    dsimp only [Prod.fst, Prod.snd] at *
    try simp only [hdrCur, hdrLive, hdrNSnap, hdrQSnap, hdrPhase, bulkBatchWhp, Fits] at *
    first | exact hsafe bulkBatchWhp _ s hv_ctx | omega)

attribute [local irreducible] tickInitDirProg

/-- Initializes `pDst`'s `SlotIoCtx` on `pgHost` (`sideBit = 1`), writing small-table words if
`nDst = 0`. -/
private def initDstSlotIoProg : (ℕ × (ℕ × ℕ)) × PageArenaCtx → Memory.Prog Unit
  | ((nDst, (pDst, smallMeta1)), pgCtx) =>
    if nDst = 0 then
      writeSmallParamTableProg ((pDst, smallMeta1), ((1, 1), pgCtx))
    else
      setSlotIoProg (pDst, ((1, 1), pgCtx))

private theorem initDstSlotIoProg_fr (x : (ℕ × (ℕ × ℕ)) × PageArenaCtx) (s : Memory.State) :
    ((Memory.spec 0).clientState s (initDstSlotIoProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨nDst, ⟨pDst, sm1⟩⟩, pgCtx⟩
  unfold initDstSlotIoProg; dsimp only
  split_ifs
  · exact writeSmallParamTableProg_fr _ s
  · exact runClient_frontier_setSlotIoProg _ _

private theorem validHistory_initDstSlotIoProg {w nDst pDst sm1 : ℕ} {pgL : PageArenaLayout}
    {s : Memory.State} (h1 : Fits w 1) (hpDst : pDst + 61 ≤ s.frontier) (hsm1 : Fits w sm1)
    (hpg_fits : Fits w pgL.metaBase ∧ Fits w pgL.offDir ∧ Fits w pgL.offTail ∧
      Fits w pgL.ptrB ∧ Fits w pgL.w ∧ Fits w pgL.pgB ∧ Fits w pgL.maxPages ∧
      Fits w pgL.itemBase ∧ Fits w pgL.qBits ∧ Fits w pgL.vBits ∧ Fits w pgL.nCap) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (initDstSlotIoProg ((nDst, (pDst, sm1)), pgL.toCtx))) := by
  unfold initDstSlotIoProg; dsimp only
  refine vh_ite _ (fun _ => ?_) (fun _ => ?_)
  · exact validHistory_writeSmallParamTableProg
      (L := ⟨sm1, 0, 0, ⟨1, 1, pgL⟩⟩) hpDst hsm1 ⟨h1, h1, hpg_fits⟩
  · exact validHistory_setSlotIoProg (io := ⟨1, 1, pgL⟩) hpDst ⟨h1, h1, hpg_fits⟩

private theorem realizesBounded_initDstSlotIo :
    RealizesBounded .exact initDstSlotIoProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × PageArenaCtx))
      (WordEncoding.encode (α := Unit))
      (fun w ((_, (pDst, _)), _) s => 1 ≤ w ∧ pDst + 61 ≤ s.frontier)
      (fun _ _ => 0) := by
  have hsio := realizesBounded_setSlotIo
  have hwsm := realizesBounded_writeSmallParamTable
  realize
  all_goals (
    rcases d with ⟨⟨nDst, ⟨pDst, sm1⟩⟩, pgCtx⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hw1, hpDst⟩ := h
    have h2 : 2 ≤ 2 ^ w := (by decide : 2 = 2 ^ 1) ▸ Nat.pow_le_pow_right (by decide) hw1
    dsimp only [Fits] at *
    omega)

attribute [local irreducible] initDstSlotIoProg

/-- Phase `7` (`initTail`) completion helper: writes `pageInitScalarsBandProg`, switches both
`pSrc` (`sideBit = 0`) and `pDst` (`sideBit = 1`) onto `pgHost`, and enters `migrate` (`phase = 8`).
-/
def finishInitTailProg (base : ℕ) : Memory.Prog Unit := do
  let stg ← Memory.read (base + hdrStage)
  let nDst ← Memory.read (base + hdrNDst)
  let nLive ← Memory.read (base + hdrLive)
  let qSnap ← Memory.read (base + hdrQSnap)
  let pgCtx ← loadHostCtxProg (base, 0)
  let sc ← pageCtxScalarsProg pgCtx
  let r_cur ← pure (nLive - qSnap * pageScPgB sc)
  pageInitScalarsBandProg ((sc.1, pageScPgB sc), (qSnap, r_cur))
  let slots ← slotPairProg (stg, base)
  setSlotIoProg (slots.1, ((1, 0), pgCtx))
  initDstSlotIoProg ((nDst, (slots.2, base + hdrSmallMeta1)), pgCtx)
  Memory.write (base + hdrRem) (nLive / itemBatchWhp + 1)
  Memory.write (base + hdrPhase) 8

/-- Precondition for `finishInitTailProg`. -/
@[expose] def FinishInitTailPre (w base : ℕ) (s : Memory.State) : Prop :=
  11 ≤ w ∧ base + 192 ≤ s.frontier ∧ Fits w (base + 192 + s.mem (base + hdrPad)) ∧
  let pgCtx := (Memory.spec 0).clientResult s (loadHostCtxProg (base, 0))
  (PageArenaLayout.ofCtx pgCtx).Valid w s.frontier ∧
  s.mem (base + hdrQSnap) * (PageArenaLayout.ofCtx pgCtx).pgB ≤ s.mem (base + hdrLive)

theorem validHistory_finishInitTailProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FinishInitTailPre w base s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (finishInitTailProg base)) := by
  obtain ⟨hw11, hb, _, hv_pg, hq_mul⟩ := hpre
  have h2048 : 2048 ≤ 2 ^ w :=
    (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
  have hz : Fits w 0 := Nat.two_pow_pos w
  have h1 : Fits w 1 := by dsimp only [Fits]; omega
  unfold finishInitTailProg
  refine vh_rd (by unfold hdrStage; omega) <| vh_rd (by unfold hdrNDst; omega) <|
    vh_rd (by unfold hdrLive; omega) <| vh_rd (by unfold hdrQSnap; omega) ?_
  refine vh_seq (validHistory_loadHostCtxProg (by omega)) fun s1 hs1 pgCtx hpg => ?_
  rw [hs1, clientState_loadHostCtxProg] at *
  rw [← hpg] at hv_pg hq_mul
  set pgL := PageArenaLayout.ofCtx pgCtx
  refine vh_seq (validHistory_pageCtxScalarsProg w pgCtx s) fun s1a hs1a sc hsc => ?_
  rw [hs1a, clientState_pageCtxScalarsProg, hsc, clientResult_pageCtxScalarsProg]
  dsimp only
  have hm32 : pgL.metaBase + 32 ≤ s.frontier := pageArenaValid_meta32 hv_pg
  have hpg_w : Fits w pgL.pgB := by
    have := pageArenaValid_pg16_lt hv_pg; dsimp only [Fits]; omega
  have hqs_w := hwf.2 (base + hdrQSnap)
  have hnl_w := hwf.2 (base + hdrLive)
  have hrc_w : Fits w (s.mem (base + hdrLive) - s.mem (base + hdrQSnap) * pgL.pgB) := by
    dsimp only [Fits] at hnl_w ⊢; omega
  simp only [pure_bind]
  have vhsb := validHistory_pageInitScalarsBandProg (w := w) hm32 hpg_w hqs_w hrc_w
  refine vh_seq vhsb fun s2 hs2 _ _ => ?_
  have hfr2 : s2.frontier = s.frontier :=
    hs2 ▸ (pageInitScalarsBandProg_spec _ _ _ _ s).1
  have hfr_w := hwf.1
  have hpg_fits : Fits w pgL.metaBase ∧ Fits w pgL.offDir ∧ Fits w pgL.offTail ∧
      Fits w pgL.ptrB ∧ Fits w pgL.w ∧ Fits w pgL.pgB ∧ Fits w pgL.maxPages ∧
      Fits w pgL.itemBase ∧ Fits w pgL.qBits ∧ Fits w pgL.vBits ∧ Fits w pgL.nCap := by
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hpg16 := pageArenaValid_pg16_lt hv_pg
    have hmp4 := pageArenaValid_mp4_lt hv_pg
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hnc_w, _, ho2, hm_ib, hib_fr⟩ := hv_pg
    have h2 := pairStreamWords_ge_two pgL.nCap pgL.qBits pgL.vBits pgL.w
    dsimp only [Fits] at hfr_w ⊢
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, hnc_w⟩
  have hce : pgL.toCtx = pgCtx := by
    rcases pgCtx with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩; rfl
  refine vh_seq (validHistory_slotPairProg w _ s2) fun sa hsa slots hsl => ?_
  rw [hsa, clientState_slotPairProg, hsl, clientResult_slotPairProg]
  dsimp only
  have hpSrc_fr :
      (if s.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1) + 61 ≤
        s2.frontier := by
    rw [hfr2]; unfold hdrPBase0 hdrPBase1; split_ifs <;> omega
  have vhs1 : (Memory.spec w).ValidHistory s2
      ((Memory.spec w).clientHistory s2
        (setSlotIoProg
          (if s.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1,
           ((1, 0), pgCtx)))) := by
    rw [← hce]
    exact validHistory_setSlotIoProg (io := ⟨1, 0, pgL⟩) hpSrc_fr ⟨h1, hz, hpg_fits⟩
  refine vh_seq vhs1 fun s3 hs3 _ _ => ?_
  have hfr3 : s3.frontier = s.frontier := (hs3 ▸ runClient_frontier_setSlotIoProg _ _).trans hfr2
  have hpDst_fr :
      (if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) + 61 ≤
        s3.frontier := by
    rw [hfr3]; unfold hdrPBase0 hdrPBase1; split_ifs <;> omega
  have hsm1_f : Fits w (base + hdrSmallMeta1) := by
    unfold hdrSmallMeta1; dsimp only [Fits] at hfr_w ⊢; omega
  have vhd : (Memory.spec w).ValidHistory s3
      ((Memory.spec w).clientHistory s3
        (initDstSlotIoProg
          ((s.mem (base + hdrNDst),
            (if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0,
             base + hdrSmallMeta1)), pgCtx))) := by
    rw [← hce]
    exact validHistory_initDstSlotIoProg h1 hpDst_fr hsm1_f hpg_fits
  refine vh_seq vhd fun s4 hs4 _ _ => ?_
  have hfr4 : s4.frontier = s.frontier := (hs4 ▸ initDstSlotIoProg_fr _ _).trans hfr3
  rcases s4 with ⟨_, fr4⟩; dsimp only at hfr4
  have hrem_f : Fits w (s.mem (base + hdrLive) / itemBatchWhp + 1) := by
    unfold itemBatchWhp
    dsimp only [Fits] at hnl_w ⊢; omega
  unfold hdrRem hdrPhase
  exact vh_wr (by omega) hrem_f <|
    vh_wr_only (by omega) (by dsimp only [Fits]; omega)

theorem realizesBounded_finishInitTail :
    RealizesBounded .exact finishInitTailProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      FinishInitTailPre (fun _ _ => 0) := by
  have hl := realizesBounded_loadHostCtx
  have hsc := realizesBounded_pageCtxScalars
  have hsb := realizesBounded_pageInitScalarsBand
  have hsl := realizesBounded_slotPair
  have hsio := realizesBounded_setSlotIo
  have hid := realizesBounded_initDstSlotIo
  realize
  all_goals (
    obtain ⟨hw11, hb, hpad, hv_pg, hq_mul⟩ := h
    have h2048 : 2048 ≤ 2 ^ w :=
      (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
    have hfr_w := hmem.1
    have hnl_w : s.mem (d + hdrLive) < 2 ^ w := hmem.2 (d + hdrLive)
    set pgCtx := (Memory.spec 0).clientResult s (loadHostCtxProg (d, 0))
    have hm32 : (PageArenaLayout.ofCtx pgCtx).metaBase + 32 ≤ s.frontier :=
      pageArenaValid_meta32 hv_pg
    dsimp only [PageArenaLayout.ofCtx] at hm32
    repeat rw [clientState_loadHostCtxProg] at *
    repeat rw [clientState_pageCtxScalarsProg] at *
    repeat rw [clientResult_pageCtxScalarsProg] at *
    repeat rw [clientState_slotPairProg] at *
    repeat rw [clientResult_slotPairProg] at *
    repeat rw [setSlotIoProg_fr] at *
    repeat rw [pageInitScalarsBandProg_fr] at *
    dsimp only [Prod.fst, Prod.snd, PageArenaLayout.ofCtx] at *
    try simp only [hdrStage, hdrNDst, hdrLive, hdrQSnap, hdrPBase0, hdrPBase1, hdrSmallMeta1,
      hdrRem, hdrPhase, itemBatchWhp, Fits] at *
    by_cases hstg : s.mem (d + 12) = 0 <;> (simp only [hstg, ↓reduceIte] at *; omega))

attribute [local irreducible] finishInitTailProg

/-- Phase `7` (`initTail`) tick: initializes up to `tailBatchWhp` (`128`) tail entries of `pgHost`;
when `cur' = 8 * pgB`, runs `finishInitTailProg`. -/
def tickInitTailProg (base : ℕ) : Memory.Prog Unit := do
  let cur ← Memory.read (base + hdrCur)
  let nSnap ← Memory.read (base + hdrNSnap)
  let ctx ← loadHostCtxProg (base, 1)
  let sc ← pageCtxScalarsProg ctx
  let cur' ← pageInitTailBatchProg (((ctx, nSnap), cur), tailBatchWhp)
  if cur' < 8 * pageScPgB sc then
    Memory.write (base + hdrCur) cur'
  else
    finishInitTailProg base

/-- Precondition for `tickInitTailProg`. -/
@[expose] def TickInitTailPre (w base : ℕ) (s : Memory.State) : Prop :=
  11 ≤ w ∧ base + 192 ≤ s.frontier ∧ Fits w (base + 192 + s.mem (base + hdrPad)) ∧
  let ctx := (Memory.spec 0).clientResult s (loadHostCtxProg (base, 1))
  (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
  (¬((Memory.spec 0).clientResult s
      (pageInitTailBatchProg (((ctx, s.mem (base + hdrNSnap)), s.mem (base + hdrCur)),
        tailBatchWhp)) < 8 * (PageArenaLayout.ofCtx ctx).pgB) →
    FinishInitTailPre w base ((Memory.spec 0).clientState s
      (pageInitTailBatchProg (((ctx, s.mem (base + hdrNSnap)), s.mem (base + hdrCur)),
        tailBatchWhp))))

theorem validHistory_tickInitTailProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : TickInitTailPre w base s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (tickInitTailProg base)) := by
  obtain ⟨_, hb, _, hv_ctx, hfin⟩ := hpre
  unfold tickInitTailProg
  refine vh_rd (by unfold hdrCur; omega) <| vh_rd (by unfold hdrNSnap; omega) ?_
  refine vh_seq (validHistory_loadHostCtxProg (by omega)) fun s1 hs1 ctx hctx => ?_
  rw [hs1, clientState_loadHostCtxProg] at *
  rw [← hctx] at hv_ctx hfin
  refine vh_seq (validHistory_pageCtxScalarsProg w ctx s) fun sa hsa sc hsc => ?_
  rw [hsa, clientState_pageCtxScalarsProg, hsc, clientResult_pageCtxScalarsProg]
  dsimp only
  have vhb := validHistory_pageInitTailBatchProg (n_0 := s.mem (base + hdrNSnap))
    (cur := s.mem (base + hdrCur)) (fuel := tailBatchWhp) hwf hv_ctx
  refine vh_seq vhb fun s2 hs2 cur' hcur' => ?_
  have hwf2 := wf_step hwf vhb
  have hfr2 : s2.frontier = s.frontier := by
    have hce : (PageArenaLayout.ofCtx ctx).toCtx = ctx := by
      rcases ctx with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩; rfl
    have hw_c : 0 < (PageArenaLayout.ofCtx ctx).w := by rw [← hv_ctx.2.1]; exact hv_ctx.1
    have hfrm := pageInitTailBatchProg_frame (L := PageArenaLayout.ofCtx ctx)
      hw_c (s.mem (base + hdrNSnap)) (s.mem (base + hdrCur)) tailBatchWhp
    rw [hce] at hfrm; exact hs2 ▸ hfrm.frontier_eq s
  have hpg8_w : 8 * (PageArenaLayout.ofCtx ctx).pgB < 2 ^ w := by
    have h16 := pageArenaValid_pg16_lt hv_ctx; omega
  refine vh_ite (cur' < 8 * (PageArenaLayout.ofCtx ctx).pgB)
    (fun hlt => by
      rcases s2 with ⟨_, fr2⟩; dsimp only at hfr2
      exact vh_wr_only (by unfold hdrCur; omega) (lt_trans hlt hpg8_w))
    fun hnlt => ?_
  rw [hs2]
  exact validHistory_finishInitTailProg (hs2 ▸ hwf2) (hfin (hcur' ▸ hnlt))

theorem realizesBounded_tickInitTail :
    RealizesBounded .exact tickInitTailProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      TickInitTailPre (fun _ _ => 0) := by
  have hl := realizesBounded_loadHostCtx
  have hsc := realizesBounded_pageCtxScalars
  have hb := realizesBounded_pageInitTailBatch
  have hf := realizesBounded_finishInitTail
  realize
  all_goals (
    obtain ⟨hw11, hb_fr, hpad, hv_ctx, hfin⟩ := h
    have h2048 : 2048 ≤ 2 ^ w :=
      (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
    have hfr_w := hmem.1
    set ctx := (Memory.spec 0).clientResult s (loadHostCtxProg (d, 1))
    have hsafe : ∀ fuel c0 (st : Memory.State),
        (PageArenaLayout.ofCtx ctx).Valid w st.frontier →
        iterationSafe pageInitTailStepProg
          (fun w' ((c', _), _) s' => (PageArenaLayout.ofCtx c').Valid w' s'.frontier)
          w (ctx, s.mem (d + hdrNSnap)) fuel c0 st := by
      intro fuel
      induction fuel with
      | zero => intro _ _ _; exact trivial
      | succ k ih =>
        intro c0 st hv_st
        have hfr_s1 := pageInitTailStepProg_fr ctx (s.mem (d + hdrNSnap)) c0 w st hv_st
        unfold iterationSafe
        rw [clientResult_width, clientState_width]
        exact ⟨hv_st, ih _ _ (hfr_s1.symm ▸ hv_st)⟩
    have hpg16 := pageArenaValid_pg16_lt hv_ctx
    repeat rw [clientState_loadHostCtxProg] at *
    repeat rw [clientState_pageCtxScalarsProg] at *
    repeat rw [clientResult_pageCtxScalarsProg] at *
    dsimp only [Prod.fst, Prod.snd] at *
    first
    | exact hsafe tailBatchWhp _ s hv_ctx
    | exact hfin (by omega)
    | (try simp only [hdrCur, hdrNSnap, tailBatchWhp, Fits] at *; omega))

attribute [local irreducible] tickInitTailProg

/-- Phase `8` (`migrate`) tick: migrates up to `itemBatchWhp` items from `pSrc` to `pDst`; when
`rem ≤ 1`, calls `pageBeginUnpermBoundedProg` and enters `unperm` (`phase = 9`). -/
def tickMigrateProg (base : ℕ) : Memory.Prog Unit := do
  let stg ← Memory.read (base + hdrStage)
  let rem ← Memory.read (base + hdrRem)
  let th ← Memory.read (base + hdrThresh)
  let nSrc ← Memory.read (base + hdrNSrc)
  let slots ← slotPairProg (stg, base)
  let _ ← migrateBatchProg (((slots.1, slots.2), 0), itemBatchWhp)
  if 1 < rem then
    Memory.write (base + hdrRem) (rem - 1)
  else do
    let pgCtx ← loadHostCtxProg (base, 0)
    let sc ← pageCtxScalarsProg pgCtx
    pageBeginUnpermBoundedProg pgCtx
    let nRef ← max2Prog (th, nSrc)
    let uTicks ← pure (nRef / 240 + pageScPgB sc / 8 + 4)
    Memory.write (base + hdrUnpermDone) 0
    Memory.write (base + hdrRem) uTicks
    Memory.write (base + hdrPhase) 9

/-- Precondition for `tickMigrateProg`. -/
@[expose] def TickMigratePre (w base : ℕ) (s : Memory.State) : Prop :=
  11 ≤ w ∧ base + 192 ≤ s.frontier ∧ Fits w (base + 192 + s.mem (base + hdrPad)) ∧
  let stg := s.mem (base + hdrStage)
  let pSrc := if stg = 0 then base + hdrPBase0 else base + hdrPBase1
  let pDst := if stg = 0 then base + hdrPBase1 else base + hdrPBase0
  iterationSafe migrateStepProg MigrateStepPre w (pSrc, pDst) itemBatchWhp 0 s ∧
  (¬(1 < s.mem (base + hdrRem)) →
    let s1 := (Memory.spec 0).clientState s (migrateBatchProg (((pSrc, pDst), 0), itemBatchWhp))
    let pgCtx := (Memory.spec 0).clientResult s1 (loadHostCtxProg (base, 0))
    base + 192 ≤ s1.frontier ∧ Fits w (base + 192 + s1.mem (base + hdrPad)) ∧
    (PageArenaLayout.ofCtx pgCtx).Valid w s1.frontier)

theorem validHistory_tickMigrateProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : TickMigratePre w base s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (tickMigrateProg base)) := by
  obtain ⟨hw11, hb, _, hsafe, hend⟩ := hpre
  have h2048 : 2048 ≤ 2 ^ w :=
    (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
  have hz : Fits w 0 := Nat.two_pow_pos w
  unfold tickMigrateProg
  refine vh_rd (by unfold hdrStage; omega) <| vh_rd (by unfold hdrRem; omega) <|
    vh_rd (by unfold hdrThresh; omega) <| vh_rd (by unfold hdrNSrc; omega) ?_
  refine vh_seq (validHistory_slotPairProg w _ s) fun sa hsa slots hsl => ?_
  rw [hsa, clientState_slotPairProg, hsl, clientResult_slotPairProg]
  dsimp only
  have vhm := validHistory_migrateBatchProg hwf hsafe
  refine vh_seq vhm fun s1 hs1 _ _ => ?_
  have hfr_le : s.frontier ≤ s1.frontier := by
    rw [hs1, ← (Memory.spec 0).run_runClient _ s]; exact Memory.frontier_le_run s _
  have hrem_w := hwf.2 (base + hdrRem)
  refine vh_ite (1 < s.mem (base + hdrRem))
    (fun _ => by
      rcases s1 with ⟨_, fr1⟩; dsimp only at hfr_le
      exact vh_wr_only (by unfold hdrRem; omega) (by dsimp only [Fits] at hrem_w ⊢; omega))
    fun hn1 => ?_
  obtain ⟨hb1, _, hv_pg⟩ := hend hn1
  rw [← hs1] at hb1 hv_pg
  have hpg16 := pageArenaValid_pg16_lt hv_pg
  refine vh_seq (validHistory_loadHostCtxProg (by omega)) fun s2 hs2 pgCtx hpg => ?_
  rw [hs2, clientState_loadHostCtxProg] at *
  rw [← hpg] at hv_pg hpg16
  refine vh_seq (validHistory_pageCtxScalarsProg w pgCtx s1) fun s2a hs2a sc hsc => ?_
  rw [hs2a, clientState_pageCtxScalarsProg, hsc, clientResult_pageCtxScalarsProg]
  dsimp only
  have vhb := validHistory_pageBeginUnpermBoundedProg hv_pg
  refine vh_seq vhb fun s3 hs3 _ _ => ?_
  have hfr3 : s3.frontier = s1.frontier := hs3 ▸ pageBeginUnpermBoundedProg_fr pgCtx s1
  refine vh_seq (validHistory_max2Prog w _ s3) fun sc' hsc' nRef hnRef => ?_
  rw [hsc', clientState_max2Prog, hnRef, clientResult_max2Prog]
  simp only [pure_bind]
  have hth_w := hwf.2 (base + hdrThresh)
  have hns_w := hwf.2 (base + hdrNSrc)
  have hut_f : Fits w
      (max (s.mem (base + hdrThresh)) (s.mem (base + hdrNSrc)) / 240 +
        (PageArenaLayout.ofCtx pgCtx).pgB / 8 + 4) := by
    dsimp only [Fits, Nat.max_def] at hth_w hns_w hpg16 ⊢
    split_ifs <;> omega
  rcases s3 with ⟨_, fr3⟩; dsimp only at hfr3
  unfold hdrUnpermDone hdrRem hdrPhase
  exact vh_wr (by omega) hz <|
    vh_wr (by omega) hut_f <|
    vh_wr_only (by omega) (by dsimp only [Fits]; omega)

theorem realizesBounded_tickMigrate :
    RealizesBounded .exact tickMigrateProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      TickMigratePre (fun _ _ => 0) := by
  have hsl := realizesBounded_slotPair
  have hm := realizesBounded_migrateBatch
  have hl := realizesBounded_loadHostCtx
  have hsc := realizesBounded_pageCtxScalars
  have hbu := realizesBounded_pageBeginUnperm
  have hmx := realizesBounded_max2
  realize
  all_goals (
    obtain ⟨hw11, hb, hpad, hsafe, hend⟩ := h
    have h2048 : 2048 ≤ 2 ^ w :=
      (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
    have hfr_w := hmem.1
    have hth_w : s.mem (d + hdrThresh) < 2 ^ w := hmem.2 (d + hdrThresh)
    have hns_w : s.mem (d + hdrNSrc) < 2 ^ w := hmem.2 (d + hdrNSrc)
    have hfr_m : ∀ x, s.frontier ≤ ((Memory.spec 0).clientState s (migrateBatchProg x)).frontier :=
      fun x => by rw [← (Memory.spec 0).run_runClient _ s]; exact Memory.frontier_le_run s _
    repeat rw [clientState_slotPairProg] at *
    repeat rw [clientResult_slotPairProg] at *
    repeat rw [clientState_loadHostCtxProg] at *
    repeat rw [clientState_pageCtxScalarsProg] at *
    repeat rw [clientResult_pageCtxScalarsProg] at *
    repeat rw [clientResult_max2Prog] at *
    dsimp only [Prod.fst, Prod.snd] at *
    first
    | exact hsafe
    | (by_cases hn1 : ¬1 < s.mem (d + hdrRem)
       · obtain ⟨hb1, hp1, hv_pg⟩ := hend hn1
         have hpg16 := pageArenaValid_pg16_lt hv_pg
         have hnr_w : max (s.mem (d + hdrThresh)) (s.mem (d + hdrNSrc)) < 2 ^ w :=
           max_lt hth_w hns_w
         first
         | exact hv_pg
         | (dsimp only [Fits, PageArenaLayout.ofCtx, StateTransitionSpec.clientResult,
              StateTransitionSpec.clientState] at hp1 hpg16 hnr_w ⊢
            try simp only [hdrStage, hdrRem, hdrThresh, hdrNSrc, hdrPBase0, hdrPBase1,
              hdrUnpermDone, hdrPhase, hdrPad, itemBatchWhp, Fits] at *
            (try split_ifs) <;> omega)
       · have hfr_le := hfr_m
           (((if s.mem (d + hdrStage) = 0 then d + hdrPBase0 else d + hdrPBase1,
              if s.mem (d + hdrStage) = 0 then d + hdrPBase1 else d + hdrPBase0), 0), itemBatchWhp)
         have hrem_w : s.mem (d + hdrRem) < 2 ^ w := hmem.2 (d + hdrRem)
         try simp only [hdrStage, hdrRem, hdrThresh, hdrNSrc, hdrPBase0, hdrPBase1,
           hdrUnpermDone, hdrPhase, hdrPad, itemBatchWhp, Fits] at *
         (try split_ifs) <;> omega))

attribute [local irreducible] tickMigrateProg

/-- Returns `1` iff `stg = 0` and `0 < nDst` (Stage A finished with a large destination). -/
private def isStageBNextProg : ℕ × ℕ → Memory.Prog ℕ
  | (stg, nDst) =>
    if stg = 0 then
      if 0 < nDst then pure 1 else pure 0
    else
      pure 0

@[simp] private theorem runClient_state_isStageBNextProg (x : ℕ × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (isStageBNextProg x)).2.1 = s := by
  rcases x with ⟨stg, nDst⟩; unfold isStageBNextProg; dsimp only; split_ifs <;> rfl

@[simp] private theorem clientState_isStageBNextProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (isStageBNextProg x) = s :=
  runClient_state_isStageBNextProg x s

private theorem validHistory_isStageBNextProg (w : ℕ) (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (isStageBNextProg x)) := by
  rcases x with ⟨stg, nDst⟩; unfold isStageBNextProg; dsimp only; split_ifs <;> exact trivial

private theorem realizesBounded_isStageBNext :
    RealizesBounded .exact isStageBNextProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w _ _ => 1 ≤ w)
      (fun _ _ => 0) := by
  realize
  all_goals (
    have h2 : 2 ≤ 2 ^ w := (by decide : 2 = 2 ^ 1) ▸ Nat.pow_le_pow_right (by decide) h
    dsimp only [Fits] at *; omega)

attribute [local irreducible] isStageBNextProg

/-- Initializes `slot 0`'s 2-word small metadata and parameter header when `stg = 0`. -/
private def optInitSmallSlot0Prog : ℕ × (ℕ × ℕ) → Memory.Prog Unit
  | (stg, (base, nLive)) =>
    if stg = 0 then do
      Memory.write (base + hdrSmallMeta0) 0
      Memory.write (base + hdrSmallMeta0 + 1) nLive
      Memory.write (base + hdrPBase0) 0
      Memory.write (base + hdrPBase0 + 1) (base + hdrSmallMeta0)
    else
      pure ()

private theorem optInitSmallSlot0Prog_fr (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientState s (optInitSmallSlot0Prog x)).frontier = s.frontier := by
  rcases x with ⟨stg, ⟨base, nLive⟩⟩
  unfold optInitSmallSlot0Prog StateTransitionSpec.clientState; dsimp only
  split_ifs <;> simp

private theorem validHistory_optInitSmallSlot0Prog {w stg base nLive : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hb : base + 192 ≤ s.frontier) (hnl : Fits w nLive) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (optInitSmallSlot0Prog (stg, (base, nLive)))) := by
  have hz : Fits w 0 := Nat.two_pow_pos w
  have hfr_w := hwf.1
  unfold optInitSmallSlot0Prog; dsimp only
  refine vh_ite _ (fun _ => ?_) (fun _ => trivial)
  unfold hdrSmallMeta0 hdrPBase0
  exact vh_wr (by omega) hz <| vh_wr (by omega) hnl <|
    vh_wr (by omega) hz <| vh_wr_only (by omega) (by dsimp only [Fits] at hfr_w ⊢; omega)

private theorem realizesBounded_optInitSmallSlot0 :
    RealizesBounded .exact optInitSmallSlot0Prog
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (_, (base, _)) s => 1 ≤ w ∧ base + 192 ≤ s.frontier)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨stg, ⟨base, nLive⟩⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hw1, hb⟩ := h
    have hz : 0 < 2 ^ w := Nat.two_pow_pos w
    have hfr_w := hmem.1
    try simp only [hdrSmallMeta0, hdrPBase0, Fits] at *
    omega)

attribute [local irreducible] optInitSmallSlot0Prog

/-- Slide-down entry branch of `finishUnpermProg`: configures `slot 0` in `SplitPair` mode at
`s_split = 0` and enters `slideDown` (`phase = 10`). -/
private def finishUnpermSlideProg (base : ℕ) : Memory.Prog Unit := do
  let stg ← Memory.read (base + hdrStage)
  let nDst ← Memory.read (base + hdrNDst)
  let mDst ← Memory.read (base + hdrMDst)
  let nLive ← Memory.read (base + hdrLive)
  let kb ← Memory.read (base + hdrKeyBits)
  let logN ← Memory.read (base + hdrLogN)
  let ell ← Memory.read (base + hdrEll)
  optInitSmallSlot0Prog (stg, (base, nLive))
  let ellSafe ← selectEq0Prog (nDst, (0, ell))
  let sub1 ← clampSubProg (logN, 12 * ellSafe)
  let qSub ← clampSubProg (kb, sub1)
  let qLo ← selectEq0Prog (nDst, (kb, qSub))
  Memory.write (base + hdrItemLo) (base + 192 + mDst)
  Memory.write (base + hdrQLo) qLo
  Memory.write (base + hdrSplit) 0
  setSplitSlotIoProg ((base, base + hdrPBase0), nLive)
  Memory.write (base + hdrPhase) 10

/-- Precondition for `finishUnpermProg`. -/
@[expose] def FinishUnpermPre (w base : ℕ) (s : Memory.State) : Prop :=
  6 ≤ w ∧ base + 192 ≤ s.frontier ∧ Fits w (base + 192 + s.mem (base + hdrMDst)) ∧
  (0 < s.mem (base + hdrNDst) → Fits w (12 * s.mem (base + hdrEll)))

private theorem validHistory_finishUnpermSlideProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FinishUnpermPre w base s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (finishUnpermSlideProg base)) := by
  obtain ⟨hw6, hb, hmd_f, _⟩ := hpre
  have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
  have hz : Fits w 0 := Nat.two_pow_pos w
  have hnl_w := hwf.2 (base + hdrLive)
  have hkb_w := hwf.2 (base + hdrKeyBits)
  unfold finishUnpermSlideProg
  refine vh_rd (by unfold hdrStage; omega) <| vh_rd (by unfold hdrNDst; omega) <|
    vh_rd (by unfold hdrMDst; omega) <| vh_rd (by unfold hdrLive; omega) <|
    vh_rd (by unfold hdrKeyBits; omega) <| vh_rd (by unfold hdrLogN; omega) <|
    vh_rd (by unfold hdrEll; omega) ?_
  have vhs0 := validHistory_optInitSmallSlot0Prog (stg := s.mem (base + hdrStage)) hwf hb hnl_w
  refine vh_seq vhs0 fun s1 hs1 _ _ => ?_
  have hwf1 := wf_step hwf vhs0
  have hfr1 : s1.frontier = s.frontier := hs1 ▸ optInitSmallSlot0Prog_fr _ s
  refine vh_seq (validHistory_selectEq0Prog w _ s1) fun s1e hs1e ellS hellS => ?_
  rw [hs1e, clientState_selectEq0Prog, hellS, clientResult_selectEq0Prog]
  refine vh_seq (validHistory_clampSubProg w _ s1) fun sa hsa sub1 hsub1 => ?_
  rw [hsa, clientState_clampSubProg, hsub1, clientResult_clampSubProg]
  refine vh_seq (validHistory_clampSubProg w _ s1) fun sb hsb qSub hqSub => ?_
  rw [hsb, clientState_clampSubProg, hqSub, clientResult_clampSubProg]
  refine vh_seq (validHistory_selectEq0Prog w _ s1) fun sc hsc qLo hqLo => ?_
  rw [hsc, clientState_selectEq0Prog, hqLo, clientResult_selectEq0Prog]
  set qLoVal := if s.mem (base + hdrNDst) = 0 then s.mem (base + hdrKeyBits)
    else s.mem (base + hdrKeyBits) -
      (s.mem (base + hdrLogN) -
        12 * (if s.mem (base + hdrNDst) = 0 then 0 else s.mem (base + hdrEll)))
  have hqL_f : Fits w qLoVal := by
    dsimp only [qLoVal, Fits] at hkb_w ⊢; split_ifs <;> omega
  rw [← hs1] at hwf1
  have hwf2 : Memory.WellFormed w
      ⟨Function.update (Function.update (Function.update s1.mem
        (base + hdrItemLo) (base + 192 + s.mem (base + hdrMDst)))
        (base + hdrQLo) qLoVal) (base + hdrSplit) 0, s1.frontier⟩ := by
    have hw1 : Memory.WellFormed w
        ⟨Function.update s1.mem (base + hdrItemLo) (base + 192 + s.mem (base + hdrMDst)),
          s1.frontier⟩ :=
      hwf1.step (o := .write _ _) ⟨by rw [hfr1]; unfold hdrItemLo; omega, hmd_f⟩
    have hw2 : Memory.WellFormed w
        ⟨Function.update (Function.update s1.mem (base + hdrItemLo) _) (base + hdrQLo) qLoVal,
          s1.frontier⟩ :=
      hw1.step (o := .write _ _) ⟨by dsimp only; rw [hfr1]; unfold hdrQLo; omega, hqL_f⟩
    exact hw2.step (o := .write _ _) ⟨by dsimp only; rw [hfr1]; unfold hdrSplit; omega, hz⟩
  rcases s1 with ⟨m1, fr1⟩; dsimp only at hfr1 hwf2
  refine vh_wr (by unfold hdrItemLo; omega) hmd_f <|
    vh_wr (by unfold hdrQLo; omega) hqL_f <|
    vh_wr (by unfold hdrSplit; omega) hz ?_
  have vhs := validHistory_setSplitSlotIoProg
    (s := ⟨Function.update (Function.update (Function.update m1 _ _) _ qLoVal) _ 0, fr1⟩)
    (base := base) (pBase := base + hdrPBase0) (nc := s.mem (base + hdrLive)) hwf2
    (by dsimp only; omega) (by dsimp only; unfold hdrPBase0; omega) hw6 hnl_w
  exact vh_seq vhs fun s3 hs3 _ _ => by
    have hfr3 : s3.frontier = s.frontier := (hs3 ▸ setSplitSlotIoProg_fr _ _).trans hfr1
    rcases s3 with ⟨_, fr3⟩; dsimp only at hfr3
    unfold hdrPhase
    exact vh_wr_only (by omega) (by dsimp only [Fits]; omega)

private theorem realizesBounded_finishUnpermSlide :
    RealizesBounded .exact finishUnpermSlideProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      FinishUnpermPre (fun _ _ => 0) := by
  have hos := realizesBounded_optInitSmallSlot0
  have hcs := realizesBounded_clampSub
  have hsel := realizesBounded_selectEq0
  have hss := realizesBounded_setSplitSlotIo
  realize
  all_goals (
    obtain ⟨hw6, hb, hmd_f, hell12⟩ := h
    have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    have hkb_w : s.mem (d + hdrKeyBits) < 2 ^ w := hmem.2 (d + hdrKeyBits)
    repeat rw [clientState_selectEq0Prog] at *
    repeat rw [clientResult_selectEq0Prog] at *
    repeat rw [clientState_clampSubProg] at *
    repeat rw [optInitSmallSlot0Prog_fr] at *
    try simp only [hdrStage, hdrNDst, hdrMDst, hdrLive, hdrKeyBits, hdrLogN, hdrEll,
      hdrPhase, hdrPBase0, hdrItemLo, hdrQLo, hdrSplit, Fits] at *
    by_cases hd0 : s.mem (d + 14) = 0
    · simp only [hd0, ↓reduceIte] at *; omega
    · have h12 := hell12 (Nat.pos_of_ne_zero hd0)
      simp only [hd0, ↓reduceIte] at *; omega)

attribute [local irreducible] finishUnpermSlideProg

/-- Phase `9` (`unperm`) completion helper (`rem ≤ 1`): either starts Stage B (`stage := 1`,
`phase := 4`) when `stage = 0 ∧ nDst > 0`, or runs `finishUnpermSlideProg`. -/
def finishUnpermProg (base : ℕ) : Memory.Prog Unit := do
  let stg ← Memory.read (base + hdrStage)
  let nDst ← Memory.read (base + hdrNDst)
  let goB ← isStageBNextProg (stg, nDst)
  if goB = 1 then do
    Memory.write (base + hdrStage) 1
    Memory.write (base + hdrCur) 0
    Memory.write (base + hdrPhase) 4
  else
    finishUnpermSlideProg base

theorem validHistory_finishUnpermProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FinishUnpermPre w base s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (finishUnpermProg base)) := by
  have hpre0 := hpre
  obtain ⟨hw6, hb, _, _⟩ := hpre
  have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
  have hz : Fits w 0 := Nat.two_pow_pos w
  have h1 : Fits w 1 := by dsimp only [Fits]; omega
  unfold finishUnpermProg
  refine vh_rd (by unfold hdrStage; omega) <| vh_rd (by unfold hdrNDst; omega) ?_
  refine vh_seq (validHistory_isStageBNextProg w _ s) fun s0 hs0 goB _ => ?_
  rw [hs0, clientState_isStageBNextProg]
  refine vh_ite (goB = 1) (fun _ => ?_) (fun _ => validHistory_finishUnpermSlideProg hwf hpre0)
  unfold hdrStage hdrCur hdrPhase
  exact vh_wr (by omega) h1 <| vh_wr (by omega) hz <|
    vh_wr_only (by omega) (by dsimp only [Fits]; omega)

theorem realizesBounded_finishUnperm :
    RealizesBounded .exact finishUnpermProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      FinishUnpermPre (fun _ _ => 0) := by
  have hib := realizesBounded_isStageBNext
  have hus := realizesBounded_finishUnpermSlide
  realize
  all_goals (
    have h_pre := h
    obtain ⟨hw6, hb, _, _⟩ := h
    have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    repeat rw [clientState_isStageBNextProg] at *
    first
    | exact h_pre
    | (try simp only [hdrStage, hdrNDst, hdrCur, hdrPhase, Fits] at *; omega))

attribute [local irreducible] finishUnpermProg

/-- Phase `9` (`unperm`) active batch helper (`done = 0`): runs `pageRunUnpermBatchProg`
(`itemBatchWhp` steps), and if `cleanPhase = 4`, switches `pDst` to direct mode at
`(itemBaseHi, qHi)` and sets `hdrUnpermDone := 1`. -/
def stepUnpermBatchProg (base : ℕ) : Memory.Prog Unit := do
  let stg ← Memory.read (base + hdrStage)
  let nLive ← Memory.read (base + hdrLive)
  let ibHi ← Memory.read (base + hdrItemHi)
  let qHi ← Memory.read (base + hdrQHi)
  let pgCtx ← loadHostCtxProg (base, 0)
  let sc ← pageCtxScalarsProg pgCtx
  pageRunUnpermBatchProg (pgCtx, itemBatchWhp)
  let cph ← Memory.read (sc.1 + 18)
  if cph = 4 then do
    let slots ← slotPairProg (stg, base)
    setDirectSlotIoProg ((base, slots.2), ((ibHi, qHi), nLive))
    Memory.write (base + hdrUnpermDone) 1
  else
    pure ()

/-- Precondition for `stepUnpermBatchProg`. -/
@[expose] def StepUnpermBatchPre (w base : ℕ) (s : Memory.State) : Prop :=
  11 ≤ w ∧ base + 192 ≤ s.frontier ∧ Fits w (base + 192 + s.mem (base + hdrPad)) ∧
  (PageArenaLayout.ofCtx ((Memory.spec 0).clientResult s (loadHostCtxProg (base, 0)))).Valid
    w s.frontier

theorem validHistory_stepUnpermBatchProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : StepUnpermBatchPre w base s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (stepUnpermBatchProg base)) := by
  obtain ⟨hw11, hb, _, hv_pg⟩ := hpre
  have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) (by omega)
  unfold stepUnpermBatchProg
  refine vh_rd (by unfold hdrStage; omega) <| vh_rd (by unfold hdrLive; omega) <|
    vh_rd (by unfold hdrItemHi; omega) <| vh_rd (by unfold hdrQHi; omega) ?_
  refine vh_seq (validHistory_loadHostCtxProg (by omega)) fun s1 hs1 pgCtx hpg => ?_
  rw [hs1, clientState_loadHostCtxProg] at *
  rw [← hpg] at hv_pg
  refine vh_seq (validHistory_pageCtxScalarsProg w pgCtx s) fun s1a hs1a sc hsc => ?_
  rw [hs1a, clientState_pageCtxScalarsProg, hsc, clientResult_pageCtxScalarsProg]
  dsimp only
  have vhu := validHistory_pageRunUnpermBatchProg (fuel := itemBatchWhp) hwf hv_pg
  refine vh_seq vhu fun s2 hs2 _ _ => ?_
  have hwf2 := wf_step hwf vhu
  rw [← hs2] at hwf2
  have hfr2 : s2.frontier = s.frontier := hs2 ▸ pageRunUnpermBatchProg_fr pgCtx itemBatchWhp s
  have hm32 := pageArenaValid_meta32 hv_pg
  dsimp only [PageArenaLayout.ofCtx] at hm32
  refine vh_rd (by rw [hfr2]; omega) ?_
  refine vh_ite _ (fun _ => ?_) (fun _ => trivial)
  refine vh_seq (validHistory_slotPairProg w _ s2) fun sa hsa slots hsl => ?_
  rw [hsa, clientState_slotPairProg, hsl, clientResult_slotPairProg]
  dsimp only
  have hpDst_fr :
      (if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) + 61 ≤
        s2.frontier := by
    rw [hfr2]; unfold hdrPBase0 hdrPBase1; split_ifs <;> omega
  have vhd := validHistory_setDirectSlotIoProg (s := s2) (base := base)
    (pBase := if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0)
    (ib := s.mem (base + hdrItemHi)) (qb := s.mem (base + hdrQHi)) (nc := s.mem (base + hdrLive))
    hwf2 (by rw [hfr2]; omega) hpDst_fr (by omega) (hwf.2 _) (hwf.2 _) (hwf.2 _)
  exact vh_seq vhd fun s3 hs3 _ _ => by
    have hfr3 : s3.frontier = s.frontier := (hs3 ▸ setDirectSlotIoProg_fr _ _).trans hfr2
    rcases s3 with ⟨_, fr3⟩; dsimp only at hfr3
    unfold hdrUnpermDone
    exact vh_wr_only (by omega) (by dsimp only [Fits]; omega)

theorem realizesBounded_stepUnpermBatch :
    RealizesBounded .exact stepUnpermBatchProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      StepUnpermBatchPre (fun _ _ => 0) := by
  have hl := realizesBounded_loadHostCtx
  have hsc := realizesBounded_pageCtxScalars
  have hu := realizesBounded_pageRunUnpermBatch
  have hsl := realizesBounded_slotPair
  have hd := realizesBounded_setDirectSlotIo
  realize
  all_goals (
    obtain ⟨hw11, hb, hpad, hv_pg⟩ := h
    have h2048 : 2048 ≤ 2 ^ w :=
      (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
    have hfr_w := hmem.1
    set pgCtx := (Memory.spec 0).clientResult s (loadHostCtxProg (d, 0))
    have hm32 := pageArenaValid_meta32 hv_pg
    dsimp only [PageArenaLayout.ofCtx] at hm32
    repeat rw [clientState_loadHostCtxProg] at *
    repeat rw [clientState_pageCtxScalarsProg] at *
    repeat rw [clientResult_pageCtxScalarsProg] at *
    repeat rw [clientState_slotPairProg] at *
    repeat rw [clientResult_slotPairProg] at *
    repeat rw [pageRunUnpermBatchProg_fr] at *
    dsimp only [Prod.fst, Prod.snd] at *
    first
    | exact hv_pg
    | (dsimp only [PageArenaLayout.ofCtx] at *
       try simp only [hdrStage, hdrLive, hdrItemHi, hdrQHi, hdrPBase0, hdrPBase1, hdrUnpermDone,
         itemBatchWhp, Fits] at *
       by_cases hstg : s.mem (d + 12) = 0 <;> (simp only [hstg, ↓reduceIte] at *; omega)))

attribute [local irreducible] stepUnpermBatchProg

/-- Runs `stepUnpermBatchProg base` when `done = 0`. -/
private def optStepUnpermProg : ℕ × ℕ → Memory.Prog Unit
  | (done, base) => if done = 0 then stepUnpermBatchProg base else pure ()

private theorem validHistory_optStepUnpermProg {w done base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : done = 0 → StepUnpermBatchPre w base s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (optStepUnpermProg (done, base))) :=
  vh_ite _ (fun h0 => validHistory_stepUnpermBatchProg hwf (hpre h0)) (fun _ => trivial)

private theorem realizesBounded_optStepUnperm :
    RealizesBounded .exact optStepUnpermProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (done, base) s => 1 ≤ w ∧ (done = 0 → StepUnpermBatchPre w base s))
      (fun _ _ => 0) := by
  have hs := realizesBounded_stepUnpermBatch
  realize
  all_goals (
    rcases d with ⟨done, base⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨_, hpre⟩ := h
    exact hpre ‹_›)

/-- Phase `9` (`unperm`) tick: runs `stepUnpermBatchProg` if `done = 0`, then counts down `hdrRem`
or runs `finishUnpermProg`. -/
def tickUnpermProg (base : ℕ) : Memory.Prog Unit := do
  let done ← Memory.read (base + hdrUnpermDone)
  let rem ← Memory.read (base + hdrRem)
  optStepUnpermProg (done, base)
  if 1 < rem then
    Memory.write (base + hdrRem) (rem - 1)
  else
    finishUnpermProg base

/-- Precondition for `tickUnpermProg`. -/
@[expose] def TickUnpermPre (w base : ℕ) (s : Memory.State) : Prop :=
  1 ≤ w ∧ base + 48 ≤ s.frontier ∧
  (s.mem (base + hdrUnpermDone) = 0 → StepUnpermBatchPre w base s) ∧
  (¬(1 < s.mem (base + hdrRem)) →
    FinishUnpermPre w base ((Memory.spec 0).clientState s
      (if s.mem (base + hdrUnpermDone) = 0 then stepUnpermBatchProg base else pure ())))

theorem validHistory_tickUnpermProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : TickUnpermPre w base s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (tickUnpermProg base)) := by
  obtain ⟨_, hb, hstep, hfin⟩ := hpre
  unfold tickUnpermProg
  refine vh_rd (by unfold hdrUnpermDone; omega) <| vh_rd (by unfold hdrRem; omega) ?_
  have vh1 := validHistory_optStepUnpermProg hwf hstep
  refine vh_seq vh1 fun s1 hs1 _ _ => ?_
  have hwf1 := wf_step hwf vh1
  have hfr_le : s.frontier ≤ s1.frontier := by
    rw [hs1, ← (Memory.spec 0).run_runClient _ s]; exact Memory.frontier_le_run s _
  have hrem_w := hwf.2 (base + hdrRem)
  refine vh_ite (1 < s.mem (base + hdrRem))
    (fun _ => by
      rcases s1 with ⟨_, fr1⟩; dsimp only at hfr_le
      exact vh_wr_only (by unfold hdrRem; omega) (by dsimp only [Fits] at hrem_w ⊢; omega))
    fun hn1 => ?_
  rw [hs1]; unfold optStepUnpermProg; dsimp only
  exact validHistory_finishUnpermProg (hs1 ▸ hwf1) (hfin hn1)

theorem realizesBounded_tickUnperm :
    RealizesBounded .exact tickUnpermProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      TickUnpermPre (fun _ _ => 0) := by
  have hos := realizesBounded_optStepUnperm
  have hf := realizesBounded_finishUnperm
  realize
  all_goals (
    obtain ⟨hw1, hb, hstep, hfin⟩ := h
    have h2 : 2 ≤ 2 ^ w := (by decide : 2 = 2 ^ 1) ▸ Nat.pow_le_pow_right (by decide) hw1
    have hfr_w := hmem.1
    have hrem_w : s.mem (d + hdrRem) < 2 ^ w := hmem.2 (d + hdrRem)
    first
    | exact hstep
    | (unfold optStepUnpermProg; dsimp only; exact hfin ‹_›)
    | (have hfr_le : s.frontier ≤
           ((Memory.spec 0).clientState s
             (optStepUnpermProg (s.mem (d + hdrUnpermDone), d))).frontier := by
         rw [← (Memory.spec 0).run_runClient _ s]; exact Memory.frontier_le_run s _
       try simp only [hdrUnpermDone, hdrRem, Fits] at *; omega))

attribute [local irreducible] optStepUnpermProg tickUnpermProg

/-- Phase `10` (`slideDown`) tick: slides up to `itemBatchWhp` pairs downward from `(itemBaseHi,
qHi)` to `(itemBaseLo, qLo)`; when `nLive ≤ sp'`, switches `pBase0` to direct mode at
`(itemBaseLo, qLo)` and enters `shrinkPost` (`phase = 11`). -/
def tickSlideDownProg (base : ℕ) : Memory.Prog Unit := do
  let sp ← Memory.read (base + hdrSplit)
  let nLive ← Memory.read (base + hdrLive)
  let ibLo ← Memory.read (base + hdrItemLo)
  let qLo ← Memory.read (base + hdrQLo)
  let ctx ← loadSplitPairCtxProg base
  let sp' ← slideDownBatchProg (((ctx, nLive), sp), itemBatchWhp)
  Memory.write (base + hdrSplit) sp'
  if nLive ≤ sp' then do
    setDirectSlotIoProg ((base, base + hdrPBase0), ((ibLo, qLo), nLive))
    Memory.write (base + hdrPhase) 11
  else
    pure ()

/-- Precondition for `tickSlideDownProg`. -/
@[expose] def TickSlideDownPre (w base : ℕ) (s : Memory.State) : Prop :=
  11 ≤ w ∧ base + 192 ≤ s.frontier ∧
  let ctx := (Memory.spec 0).clientResult s (loadSplitPairCtxProg base)
  let nLive := s.mem (base + hdrLive)
  let sp := s.mem (base + hdrSplit)
  SlideDownStepPre w ((ctx, nLive), sp) s ∧
  iterationSafe slideDownStepProg SlideDownStepPre w (ctx, nLive) itemBatchWhp sp s ∧
  Fits w ((Memory.spec 0).clientResult s
    (slideDownBatchProg (((ctx, nLive), sp), itemBatchWhp)))

theorem validHistory_tickSlideDownProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : TickSlideDownPre w base s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (tickSlideDownProg base)) := by
  obtain ⟨hw11, hb, hstep_pre, _, hsp'_f⟩ := hpre
  have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) (by omega)
  unfold tickSlideDownProg
  refine vh_rd (by unfold hdrSplit; omega) <| vh_rd (by unfold hdrLive; omega) <|
    vh_rd (by unfold hdrItemLo; omega) <| vh_rd (by unfold hdrQLo; omega) ?_
  refine vh_seq (validHistory_loadSplitPairCtxProg (by omega)) fun s1 hs1 ctx hctx => ?_
  rw [hs1, clientState_loadSplitPairCtxProg] at *
  rw [← hctx] at hstep_pre hsp'_f
  have vhb := validHistory_slideDownBatchProg (fuel := itemBatchWhp) hwf hstep_pre
  refine vh_seq vhb fun s2 hs2 sp' hsp' => ?_
  have hwf2 := wf_step hwf vhb
  have hfr_b := slideDownBatchProg_fr ctx (s.mem (base + hdrLive)) (s.mem (base + hdrSplit))
    itemBatchWhp s
  have hfr2 : s2.frontier = s.frontier := hs2 ▸ hfr_b
  rw [← hsp'] at hsp'_f
  rw [← hs2] at hwf2
  have hwf3 : Memory.WellFormed w ⟨Function.update s2.mem (base + hdrSplit) sp', s2.frontier⟩ :=
    hwf2.step (o := .write _ _) ⟨by rw [hfr2]; unfold hdrSplit; omega, hsp'_f⟩
  rcases s2 with ⟨m2, fr2⟩; dsimp only at hfr2 hwf3
  refine vh_wr (by unfold hdrSplit; omega) hsp'_f ?_
  refine vh_ite _ (fun _ => ?_) (fun _ => trivial)
  have vhd := validHistory_setDirectSlotIoProg
    (s := ⟨Function.update m2 (base + hdrSplit) sp', fr2⟩) (base := base)
    (pBase := base + hdrPBase0)
    (ib := s.mem (base + hdrItemLo)) (qb := s.mem (base + hdrQLo)) (nc := s.mem (base + hdrLive))
    hwf3 (by dsimp only; omega) (by dsimp only; unfold hdrPBase0; omega) (by omega)
    (hwf.2 _) (hwf.2 _) (hwf.2 _)
  exact vh_seq vhd fun s4 hs4 _ _ => by
    have hfr4 : s4.frontier = s.frontier := (hs4 ▸ setDirectSlotIoProg_fr _ _).trans hfr2
    rcases s4 with ⟨_, fr4⟩; dsimp only at hfr4
    unfold hdrPhase
    exact vh_wr_only (by omega) (by dsimp only [Fits]; omega)

theorem realizesBounded_tickSlideDown :
    RealizesBounded .exact tickSlideDownProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      TickSlideDownPre (fun _ _ => 0) := by
  have hl := realizesBounded_loadSplitPairCtx
  have hb := realizesBounded_slideDownBatch
  have hd := realizesBounded_setDirectSlotIo
  realize
  all_goals (
    obtain ⟨hw11, hb_fr, hstep_pre, hsafe, hsp'_f⟩ := h
    have h2048 : 2048 ≤ 2 ^ w :=
      (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
    have hfr_w := hmem.1
    set ctx := (Memory.spec 0).clientResult s (loadSplitPairCtxProg d)
    have hfr2 : ((Memory.spec 0).clientState s
        (slideDownBatchProg (((ctx, s.mem (d + hdrLive)), s.mem (d + hdrSplit)),
          itemBatchWhp))).frontier = s.frontier :=
      slideDownBatchProg_fr _ _ _ _ s
    repeat rw [clientState_loadSplitPairCtxProg] at *
    try rw [hfr2]
    try simp only [hdrSplit, hdrLive, hdrItemLo, hdrQLo, hdrPBase0, hdrPhase, itemBatchWhp,
      Fits] at *
    first | exact hsafe | omega)

attribute [local irreducible] tickSlideDownProg

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
