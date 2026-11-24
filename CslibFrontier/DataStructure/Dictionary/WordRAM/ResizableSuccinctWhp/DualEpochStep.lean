/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochCtrl
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unified Dual-Epoch Step & Post-Randomization Programs (`DualEpochStep`)

This module combines the 12-phase (`0..11`) background tick programs from `DualEpochCtrl` with
`userQueryProg` and `userMutateProg` from `DualEpochCtrlBase` into the top-level deterministic
`Memory.Prog` stages of each dictionary operation (`bgTickProg`, `stepOpProg`, `finishRandFillProg`,
`finishShrinkPostProg`, and `postRandShrinkProg`) for the resizable succinct worst-case WHP
dictionary ([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.bgTickProg`: unified 1-tick
  background dispatcher across phases `0..11`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.stepOpProg`: read-only `query` or
  `userMutateProg` followed by `1` deterministic `bgTickProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.postRandShrinkProg`: finalizes
  `randFill` (`phase = 5`) and computes bounded frontier reclamation `k_shrink ≤ bulkBatchWhp`.

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

/-- Unified 1-tick background dispatcher across phases `0..11`, returning `(rCur, (rEnd, rMask))`
for `randFillBatchCode` (`(0, (0, 0))` outside `phase = 5`). -/
def bgTickProg : ℕ × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | (base, newFr) => do
    let ph ← Memory.read (base + hdrPhase)
    if ph = 0 then do tickIdleProg base; pure (0, (0, 0))
    else if ph = 1 then do tickLogProg base; pure (0, (0, 0))
    else if ph = 2 then do tickGrowPreProg (base, newFr); pure (0, (0, 0))
    else if ph = 3 then do tickSlideUpProg base; pure (0, (0, 0))
    else if ph = 4 then do tickZeroMetaProg base; pure (0, (0, 0))
    else if ph = 5 then tickRandPrepProg base
    else if ph = 6 then do tickInitDirProg base; pure (0, (0, 0))
    else if ph = 7 then do tickInitTailProg base; pure (0, (0, 0))
    else if ph = 8 then do tickMigrateProg base; pure (0, (0, 0))
    else if ph = 9 then do tickUnpermProg base; pure (0, (0, 0))
    else if ph = 10 then do tickSlideDownProg base; pure (0, (0, 0))
    else pure (0, (0, 0))

/-- Precondition for `bgTickProg`. -/
@[expose] def BgTickPre (w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (base, newFr), s =>
    4 ≤ w ∧ base + 48 ≤ s.frontier ∧
    let ph := s.mem (base + hdrPhase)
    if ph = 0 then TickIdlePre w base s
    else if ph = 1 then TickLogPre w base s
    else if ph = 2 then TickGrowPrePre w (base, newFr) s
    else if ph = 3 then TickSlideUpPre w base s
    else if ph = 4 then TickZeroMetaPre w base s
    else if ph = 5 then TickRandPrepPre w base s
    else if ph = 6 then TickInitDirPre w base s
    else if ph = 7 then TickInitTailPre w base s
    else if ph = 8 then TickMigratePre w base s
    else if ph = 9 then TickUnpermPre w base s
    else if ph = 10 then TickSlideDownPre w base s
    else True

theorem validHistory_bgTickProg {w : ℕ} {x : ℕ × ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : BgTickPre w x s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bgTickProg x)) := by
  rcases x with ⟨base, newFr⟩
  obtain ⟨_, hb, hdisp⟩ := hpre
  dsimp only at hdisp
  unfold bgTickProg
  unfold hdrPhase at hdisp ⊢
  refine vh_rd (by omega) ?_
  by_cases h0 : s.mem (base + 11) = 0
  · rw [ite_eq_left h0] at hdisp ⊢
    exact vh_seq (validHistory_tickIdleProg hwf hdisp) fun _ _ _ _ => trivial
  · rw [ite_eq_right h0] at hdisp ⊢
    by_cases h1 : s.mem (base + 11) = 1
    · rw [ite_eq_left h1] at hdisp ⊢
      exact vh_seq (validHistory_tickLogProg hwf hdisp) fun _ _ _ _ => trivial
    · rw [ite_eq_right h1] at hdisp ⊢
      by_cases h2 : s.mem (base + 11) = 2
      · rw [ite_eq_left h2] at hdisp ⊢
        exact vh_seq (validHistory_tickGrowPreProg hwf hdisp) fun _ _ _ _ => trivial
      · rw [ite_eq_right h2] at hdisp ⊢
        by_cases h3 : s.mem (base + 11) = 3
        · rw [ite_eq_left h3] at hdisp ⊢
          exact vh_seq (validHistory_tickSlideUpProg hwf hdisp) fun _ _ _ _ => trivial
        · rw [ite_eq_right h3] at hdisp ⊢
          by_cases h4 : s.mem (base + 11) = 4
          · rw [ite_eq_left h4] at hdisp ⊢
            exact vh_seq (validHistory_tickZeroMetaProg hwf hdisp) fun _ _ _ _ => trivial
          · rw [ite_eq_right h4] at hdisp ⊢
            by_cases h5 : s.mem (base + 11) = 5
            · rw [ite_eq_left h5] at hdisp ⊢
              exact validHistory_tickRandPrepProg hwf hdisp
            · rw [ite_eq_right h5] at hdisp ⊢
              by_cases h6 : s.mem (base + 11) = 6
              · rw [ite_eq_left h6] at hdisp ⊢
                exact vh_seq (validHistory_tickInitDirProg hwf hdisp) fun _ _ _ _ => trivial
              · rw [ite_eq_right h6] at hdisp ⊢
                by_cases h7 : s.mem (base + 11) = 7
                · rw [ite_eq_left h7] at hdisp ⊢
                  exact vh_seq (validHistory_tickInitTailProg hwf hdisp) fun _ _ _ _ => trivial
                · rw [ite_eq_right h7] at hdisp ⊢
                  by_cases h8 : s.mem (base + 11) = 8
                  · rw [ite_eq_left h8] at hdisp ⊢
                    exact vh_seq (validHistory_tickMigrateProg hwf hdisp) fun _ _ _ _ => trivial
                  · rw [ite_eq_right h8] at hdisp ⊢
                    by_cases h9 : s.mem (base + 11) = 9
                    · rw [ite_eq_left h9] at hdisp ⊢
                      exact vh_seq (validHistory_tickUnpermProg hwf hdisp) fun _ _ _ _ => trivial
                    · rw [ite_eq_right h9] at hdisp ⊢
                      by_cases h10 : s.mem (base + 11) = 10
                      · rw [ite_eq_left h10] at hdisp ⊢
                        exact vh_seq (validHistory_tickSlideDownProg hwf hdisp)
                          fun _ _ _ _ => trivial
                      · rw [ite_eq_right h10]; exact trivial

theorem realizesBounded_bgTick :
    RealizesBounded .exact bgTickProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      BgTickPre (fun _ _ => 0) := by
  have t0 := realizesBounded_tickIdle
  have t1 := realizesBounded_tickLog
  have t2 := realizesBounded_tickGrowPre
  have t3 := realizesBounded_tickSlideUp
  have t4 := realizesBounded_tickZeroMeta
  have t5 := realizesBounded_tickRandPrep
  have t6 := realizesBounded_tickInitDir
  have t7 := realizesBounded_tickInitTail
  have t8 := realizesBounded_tickMigrate
  have t9 := realizesBounded_tickUnperm
  have t10 := realizesBounded_tickSlideDown
  realize
  all_goals (
    rcases d with ⟨base, newFr⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hw4, hb, hdisp⟩ := h
    dsimp (config := { proj := false, iota := false }) only [Prod.fst, Prod.snd] at hdisp
    have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) hw4
    have hfr_w := hmem.1
    unfold hdrPhase at *
    dsimp only [Fits] at *
    by_cases h0 : s.mem (base + 11) = 0
    · rw [ite_eq_left h0] at hdisp; first | exact hdisp | omega
    · rw [ite_eq_right h0] at hdisp
      by_cases h1 : s.mem (base + 11) = 1
      · rw [ite_eq_left h1] at hdisp; first | exact hdisp | omega
      · rw [ite_eq_right h1] at hdisp
        by_cases h2 : s.mem (base + 11) = 2
        · rw [ite_eq_left h2] at hdisp; first | exact hdisp | omega
        · rw [ite_eq_right h2] at hdisp
          by_cases h3 : s.mem (base + 11) = 3
          · rw [ite_eq_left h3] at hdisp; first | exact hdisp | omega
          · rw [ite_eq_right h3] at hdisp
            by_cases h4 : s.mem (base + 11) = 4
            · rw [ite_eq_left h4] at hdisp; first | exact hdisp | omega
            · rw [ite_eq_right h4] at hdisp
              by_cases h5 : s.mem (base + 11) = 5
              · rw [ite_eq_left h5] at hdisp; first | exact hdisp | omega
              · rw [ite_eq_right h5] at hdisp
                by_cases h6 : s.mem (base + 11) = 6
                · rw [ite_eq_left h6] at hdisp; first | exact hdisp | omega
                · rw [ite_eq_right h6] at hdisp
                  by_cases h7 : s.mem (base + 11) = 7
                  · rw [ite_eq_left h7] at hdisp; first | exact hdisp | omega
                  · rw [ite_eq_right h7] at hdisp
                    by_cases h8 : s.mem (base + 11) = 8
                    · rw [ite_eq_left h8] at hdisp; first | exact hdisp | omega
                    · rw [ite_eq_right h8] at hdisp
                      by_cases h9 : s.mem (base + 11) = 9
                      · rw [ite_eq_left h9] at hdisp; first | exact hdisp | omega
                      · rw [ite_eq_right h9] at hdisp
                        by_cases h10 : s.mem (base + 11) = 10
                        · rw [ite_eq_left h10] at hdisp; first | exact hdisp | omega
                        · rw [ite_eq_right h10] at hdisp; omega)

attribute [local irreducible] bgTickProg

/-- Main operational step program (`opTag = 0` = read-only `query`; `opTag ≠ 0` = `userMutateProg`
followed by `1` deterministic `bgTickProg`). -/
def stepOpProg : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))
  | (((base, newFr), opTag), (u_val, v_val)) =>
    if opTag = 0 then do
      let qv ← userQueryProg (base, u_val)
      pure (qv, (0, (0, 0)))
    else do
      let _ ← userMutateProg ((base, opTag), (u_val, v_val))
      let rArgs ← bgTickProg (base, newFr)
      pure ((0, 0), rArgs)

/-- Precondition for `stepOpProg`. -/
@[expose] def StepOpPre (w : ℕ) : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((base, newFr), opTag), (u_val, v_val)), s =>
    1 ≤ w ∧
    if opTag = 0 then
      UserQueryPre w (base, u_val) s
    else
      UserMutatePre w ((base, opTag), (u_val, v_val)) s ∧
      BgTickPre w (base, newFr)
        ((Memory.spec 0).clientState s (userMutateProg ((base, opTag), (u_val, v_val))))

theorem validHistory_stepOpProg {w : ℕ} {x : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : StepOpPre w x s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (stepOpProg x)) := by
  rcases x with ⟨⟨⟨base, newFr⟩, opTag⟩, ⟨u_val, v_val⟩⟩
  obtain ⟨_, hdisp⟩ := hpre
  unfold stepOpProg; dsimp only at hdisp ⊢
  by_cases h0 : opTag = 0
  · rw [ite_eq_left h0] at hdisp ⊢
    exact vh_seq (validHistory_userQueryProg hdisp) fun _ _ _ _ => trivial
  · rw [ite_eq_right h0] at hdisp ⊢
    have vhm := validHistory_userMutateProg hwf hdisp.1
    refine vh_seq vhm fun s1 hs1 _ _ => ?_
    rw [hs1]
    exact vh_seq (validHistory_bgTickProg (wf_step hwf vhm) hdisp.2) fun _ _ _ _ => trivial

theorem realizesBounded_stepOp :
    RealizesBounded .exact stepOpProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      StepOpPre (fun _ _ => 0) := by
  have hq := realizesBounded_userQuery
  have hm := realizesBounded_userMutate
  have hb := realizesBounded_bgTick
  realize
  all_goals (
    rcases d with ⟨⟨⟨base, newFr⟩, opTag⟩, ⟨u_val, v_val⟩⟩
    dsimp only [Prod.fst, Prod.snd, Fits] at *
    obtain ⟨hw1, hdisp⟩ := h
    have hz : 0 < 2 ^ w := Nat.two_pow_pos w
    by_cases h0 : opTag = 0
    · rw [ite_eq_left h0] at hdisp; first | exact hdisp | omega
    · rw [ite_eq_right h0] at hdisp
      first | exact hdisp.1 | exact hdisp.2 | omega)

/-- First half of `finishRandFillProg`: masks `aB` & `aF` at `metaDst + 32` and `metaDst + offFp`
modulo `2 ^ (redW - 1)`. -/
def maskRandMultsProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((redW, metaDst), (pDst, _unused)) => do
    let offFp ← Memory.read (pDst + 30)
    let mask ← pure (((1 : ℕ) <<< (redW - 1)) - 1)
    let vB ← Memory.read (metaDst + 32)
    Memory.write (metaDst + 32) (vB &&& mask)
    let vF ← Memory.read (metaDst + offFp)
    Memory.write (metaDst + offFp) (vF &&& mask)

theorem maskRandMultsProg_state (redW metaDst pDst : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (maskRandMultsProg ((redW, metaDst), (pDst, 0))) =
      { mem := Function.update
          (Function.update s.mem (metaDst + 32)
            (s.mem (metaDst + 32) &&& (((1 : ℕ) <<< (redW - 1)) - 1)))
          (metaDst + s.mem (pDst + 30))
          (s.mem (metaDst + s.mem (pDst + 30)) &&& (((1 : ℕ) <<< (redW - 1)) - 1)),
        frontier := s.frontier } := by
  unfold maskRandMultsProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd, pure_bind,
    StateTransitionSpec.clientState_bind, cstate_rd, cres_rd,
    StateTransitionSpec.clientState_bind, cstate_wr,
    StateTransitionSpec.clientState_bind, cstate_rd, cres_rd, cstate_wr]
  dsimp only
  congr 2
  by_cases hsame : metaDst + s.mem (pDst + 30) = metaDst + 32
  · rw [hsame, Function.update_self, Nat.and_assoc, Nat.and_self]
  · rw [Function.update_of_ne hsame]

private theorem validHistory_maskRandMultsProg {w redW metaDst pDst : ℕ} {s : Memory.State}
    (h1_rw : 1 ≤ redW) (hrw_w : redW ≤ w) (hp : pDst + 31 ≤ s.frontier)
    (hm32 : metaDst + 32 < s.frontier) (hmfp : metaDst + s.mem (pDst + 30) < s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (maskRandMultsProg ((redW, metaDst), (pDst, 0)))) := by
  have hpow_rw : 2 ^ (redW - 1) < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
  have hsh : (1 : ℕ) <<< (redW - 1) = 2 ^ (redW - 1) := shift_one_eq _
  have hand_f : ∀ x : ℕ, Fits w (x &&& (((1 : ℕ) <<< (redW - 1)) - 1)) := fun x => by
    rw [hsh, Nat.and_two_pow_sub_one_eq_mod]
    exact lt_trans (Nat.mod_lt _ (by positivity)) hpow_rw
  unfold maskRandMultsProg; dsimp only
  refine vh_rd (by omega) ?_
  simp only [pure_bind]
  refine vh_rd hm32 <| vh_wr hm32 (hand_f _) ?_
  exact vh_rd hmfp <| vh_wr_only hmfp (hand_f _)

private theorem realizesBounded_maskRandMults :
    RealizesBounded .exact maskRandMultsProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((redW, metaDst), (pDst, _)) s =>
        6 ≤ w ∧ 1 ≤ redW ∧ redW ≤ w ∧ pDst + 31 ≤ s.frontier ∧
        metaDst + 32 < s.frontier ∧ metaDst + s.mem (pDst + 30) < s.frontier)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨redW, metaDst⟩, ⟨pDst, unused⟩⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hw6, h1_rw, hrw_w, hp, hm32, hmfp⟩ := h
    have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hfr_w := hmem.1
    have hpow_rw : 2 ^ (redW - 1) < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
    have hsh : (1 : ℕ) <<< (redW - 1) = 2 ^ (redW - 1) := shift_one_eq _
    have hp1 : 1 ≤ 2 ^ (redW - 1) := Nat.one_le_two_pow
    have ha1 : s.mem (metaDst + 32) &&& (2 ^ (redW - 1) - 1) < 2 ^ w := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact lt_trans (Nat.mod_lt _ (by positivity)) hpow_rw
    have ha2 : ∀ m' : ℕ → ℕ, m' (metaDst + s.mem (pDst + 30)) &&& (2 ^ (redW - 1) - 1) < 2 ^ w :=
      fun m' => by
        rw [Nat.and_two_pow_sub_one_eq_mod]
        exact lt_trans (Nat.mod_lt _ (by positivity)) hpow_rw
    have ha2' := ha2 (Function.update s.mem (metaDst + 32)
      (s.mem (metaDst + 32) &&& (2 ^ (redW - 1) - 1)))
    try rw [hsh] at *
    dsimp only [Fits] at *
    omega)

attribute [local irreducible] maskRandMultsProg

/-- Post-`randFill` completion helper (`phase = 5` and `cur = offBktMeta`): masks `aB` & `aF` mod
`2 ^ (redW - 1)`, sets `pDst` direct `SlotIoCtx` at `(itemBaseHi, qHi)`, calls
`epochInitZeroedProg pDst`, and transitions to `initDir` (`phase = 6`). -/
def finishRandFillProg (base : ℕ) : Memory.Prog Unit := do
  let redW ← Memory.read (base + hdrRedW)
  let stg ← Memory.read (base + hdrStage)
  let pad ← Memory.read (base + hdrPad)
  let nLive ← Memory.read (base + hdrLive)
  let ibHi ← Memory.read (base + hdrItemHi)
  let qHi ← Memory.read (base + hdrQHi)
  let slots ← slotPairProg (stg, base)
  let metaDst ← metaDstAddrProg (stg, (base, pad))
  maskRandMultsProg ((redW, metaDst), (slots.2, 0))
  setDirectSlotIoProg ((base, slots.2), ((ibHi, qHi), nLive))
  epochInitZeroedProg slots.2
  Memory.write (base + hdrCur) 0
  Memory.write (base + hdrPhase) 6

/-- Precondition for `finishRandFillProg`. -/
@[expose] def FinishRandFillPre (w base : ℕ) (s : Memory.State) : Prop :=
  6 ≤ w ∧ base + 192 ≤ s.frontier ∧ 1 ≤ s.mem (base + hdrRedW) ∧ s.mem (base + hdrRedW) ≤ w ∧
  let stg := s.mem (base + hdrStage)
  let pDst := if stg = 0 then base + hdrPBase1 else base + hdrPBase0
  let metaDst := if stg = 0 then base + 192 + s.mem (base + hdrPad) else base + 192
  metaDst + 32 < s.frontier ∧ metaDst + s.mem (pDst + 30) < s.frontier ∧
  let mask := ((1 : ℕ) <<< (s.mem (base + hdrRedW) - 1)) - 1
  let s1 : Memory.State :=
    { mem := Function.update (Function.update s.mem (metaDst + 32) (s.mem (metaDst + 32) &&& mask))
        (metaDst + s.mem (pDst + 30)) (s.mem (metaDst + s.mem (pDst + 30)) &&& mask),
      frontier := s.frontier }
  EpochProgPre w pDst ((Memory.spec 0).clientState s1
    (setDirectSlotIoProg ((base, pDst),
      ((s.mem (base + hdrItemHi), s.mem (base + hdrQHi)), s.mem (base + hdrLive)))))

theorem validHistory_finishRandFillProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FinishRandFillPre w base s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (finishRandFillProg base)) := by
  obtain ⟨hw6, hb, h1_rw, hrw_w, hm32, hmfp, hepre⟩ := hpre
  have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
  have hz : Fits w 0 := Nat.two_pow_pos w
  unfold finishRandFillProg
  refine vh_rd (by unfold hdrRedW; omega) <| vh_rd (by unfold hdrStage; omega) <|
    vh_rd (by unfold hdrPad; omega) <| vh_rd (by unfold hdrLive; omega) <|
    vh_rd (by unfold hdrItemHi; omega) <| vh_rd (by unfold hdrQHi; omega) ?_
  refine vh_seq (validHistory_slotPairProg w _ s) fun sa hsa slots hsl => ?_
  rw [hsa, clientState_slotPairProg, hsl, clientResult_slotPairProg]
  dsimp only
  refine vh_seq (validHistory_metaDstAddrProg w _ s) fun sb hsb metaDst hmd => ?_
  rw [hsb, clientState_metaDstAddrProg, hmd, clientResult_metaDstAddrProg]
  set pD := if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0
  have hpD_fr : pD + 31 ≤ s.frontier := by
    dsimp only [pD]; unfold hdrPBase0 hdrPBase1; split_ifs <;> omega
  have vhm := validHistory_maskRandMultsProg h1_rw hrw_w hpD_fr hm32 hmfp
  refine vh_seq vhm fun s1 hs1 _ _ => ?_
  have hwf1 := wf_step hwf vhm
  rw [← hs1] at hwf1
  have hs1_eq := hs1.trans (maskRandMultsProg_state _ _ _ s)
  have hfr1 : s1.frontier = s.frontier := by rw [hs1_eq]
  have vhd := validHistory_setDirectSlotIoProg (s := s1) (base := base) (pBase := pD)
    (ib := s.mem (base + hdrItemHi)) (qb := s.mem (base + hdrQHi)) (nc := s.mem (base + hdrLive))
    hwf1 (by rw [hfr1]; omega)
    (by rw [hfr1]; dsimp only [pD]; unfold hdrPBase0 hdrPBase1; split_ifs <;> omega)
    hw6 (hwf.2 _) (hwf.2 _) (hwf.2 _)
  refine vh_seq vhd fun s2 hs2 _ _ => ?_
  have hwf2 := wf_step hwf1 vhd
  rw [← hs2] at hwf2
  have hepre2 : EpochProgPre w pD s2 := by rw [hs2, hs1_eq]; exact hepre
  have vhi := validHistory_epochInitZeroedProg hwf2 hepre2
  refine vh_seq vhi fun s3 hs3 _ _ => ?_
  have hfr_le : s.frontier ≤ s3.frontier := by
    have h2 : s1.frontier ≤ s2.frontier := by
      rw [hs2, setDirectSlotIoProg_fr]
    have h3 : s2.frontier ≤ s3.frontier := by
      rw [hs3, ← (Memory.spec 0).run_runClient _ s2]; exact Memory.frontier_le_run s2 _
    omega
  rcases s3 with ⟨_, fr3⟩; dsimp only at hfr_le
  unfold hdrCur hdrPhase
  exact vh_wr (by omega) hz <| vh_wr_only (by omega) (by dsimp only [Fits]; omega)

theorem realizesBounded_finishRandFill :
    RealizesBounded .exact finishRandFillProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      FinishRandFillPre (fun _ _ => 0) := by
  have hsl := realizesBounded_slotPair
  have hmd := realizesBounded_metaDstAddr
  have hmm := realizesBounded_maskRandMults
  have hd := realizesBounded_setDirectSlotIo
  have hi := realizesBounded_epochInitZeroed
  realize
  all_goals (
    obtain ⟨hw6, hb, h1_rw, hrw_w, hm32, hmfp, hepre⟩ := h
    have h64 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    repeat rw [clientState_slotPairProg] at *
    repeat rw [clientResult_slotPairProg] at *
    repeat rw [clientState_metaDstAddrProg] at *
    repeat rw [clientResult_metaDstAddrProg] at *
    repeat rw [maskRandMultsProg_state] at *
    dsimp only [Prod.fst, Prod.snd] at *
    first
    | exact hepre
    | (try simp only [hdrRedW, hdrStage, hdrPad, hdrLive, hdrItemHi, hdrQHi, hdrPBase0,
         hdrPBase1, hdrCur, hdrPhase, Fits] at *
       by_cases hstg : s.mem (d + 12) = 0 <;> (simp only [hstg, ↓reduceIte] at *; omega)))

attribute [local irreducible] finishRandFillProg

/-- Copies destination host cache `43..47 → 38..42` when `0 < nDst`. -/
def optCopyDstToSrcProg : ℕ × ℕ → Memory.Prog Unit
  | (nDst, base) => if 0 < nDst then copyDstToSrcHostProg base else pure ()

theorem optCopyDstToSrcProg_fr (x : ℕ × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (optCopyDstToSrcProg x)).frontier = s.frontier := by
  rcases x with ⟨nDst, base⟩; unfold optCopyDstToSrcProg; dsimp only
  split_ifs
  · exact (copyDstToSrcHostProg_spec base s).1
  · rfl

private theorem validHistory_optCopyDstToSrcProg {w nDst base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hb : base + 48 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (optCopyDstToSrcProg (nDst, base))) :=
  vh_ite _ (fun _ => validHistory_copyDstToSrcHostProg hwf hb) (fun _ => trivial)

private theorem realizesBounded_optCopyDstToSrc :
    RealizesBounded .exact optCopyDstToSrcProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (_, base) s => 1 ≤ w ∧ base + 48 ≤ s.frontier)
      (fun _ _ => 0) := by
  have hc := realizesBounded_copyDstToSrcHost
  realize
  all_goals (
    rcases d with ⟨nDst, base⟩
    dsimp only [Fits] at *
    obtain ⟨_, hb⟩ := h
    have hz : 0 < 2 ^ w := Nat.two_pow_pos w
    omega)

attribute [local irreducible] optCopyDstToSrcProg

/-- Phase `11` (`shrinkPost`) completion helper: promotes `N_dst` to `N_src`, copies `43..47 →
38..42` when `N_dst > 0`, syncs `(hdrItemHi, hdrQHi) := (hdrItemLo, hdrQLo)`, and enters `idle`
(`phase = 0`). -/
def finishShrinkPostProg (base : ℕ) : Memory.Prog Unit := do
  let nDst ← Memory.read (base + hdrNDst)
  let mDst ← Memory.read (base + hdrMDst)
  let ibLo ← Memory.read (base + hdrItemLo)
  let qLo ← Memory.read (base + hdrQLo)
  optCopyDstToSrcProg (nDst, base)
  Memory.write (base + hdrNSrc) nDst
  Memory.write (base + hdrMSrc) mDst
  Memory.write (base + hdrNDst) 0
  Memory.write (base + hdrMDst) 0
  Memory.write (base + hdrStage) 0
  Memory.write (base + hdrEpochOps) 0
  Memory.write (base + hdrItemHi) ibLo
  Memory.write (base + hdrQHi) qLo
  Memory.write (base + hdrPhase) 0

theorem validHistory_finishShrinkPostProg {w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hb : base + 48 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (finishShrinkPostProg base)) := by
  have hz : Fits w 0 := Nat.two_pow_pos w
  unfold finishShrinkPostProg
  refine vh_rd (by unfold hdrNDst; omega) <| vh_rd (by unfold hdrMDst; omega) <|
    vh_rd (by unfold hdrItemLo; omega) <| vh_rd (by unfold hdrQLo; omega) ?_
  have vhc := validHistory_optCopyDstToSrcProg (nDst := s.mem (base + hdrNDst)) hwf hb
  refine vh_seq vhc fun s1 hs1 _ _ => ?_
  have hfr1 : s1.frontier = s.frontier := hs1 ▸ optCopyDstToSrcProg_fr _ s
  rcases s1 with ⟨_, fr1⟩; dsimp only at hfr1
  unfold hdrNSrc hdrMSrc hdrNDst hdrMDst hdrStage hdrEpochOps hdrItemHi hdrQHi hdrPhase
  exact vh_wr (by omega) (hwf.2 _) <|
    vh_wr (by omega) (hwf.2 _) <|
    vh_wr (by omega) hz <|
    vh_wr (by omega) hz <|
    vh_wr (by omega) hz <|
    vh_wr (by omega) hz <|
    vh_wr (by omega) (hwf.2 _) <|
    vh_wr (by omega) (hwf.2 _) <|
    vh_wr_only (by omega) hz

theorem realizesBounded_finishShrinkPost :
    RealizesBounded .exact finishShrinkPostProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w base s => 1 ≤ w ∧ base + 48 ≤ s.frontier)
      (fun _ _ => 0) := by
  have hc := realizesBounded_optCopyDstToSrc
  realize
  all_goals (
    obtain ⟨hw1, hb⟩ := h
    have hz : 0 < 2 ^ w := Nat.two_pow_pos w
    have hfr_w := hmem.1
    try simp only [hdrNDst, hdrMDst, hdrItemLo, hdrQLo, hdrNSrc, hdrMSrc, hdrStage, hdrEpochOps,
      hdrItemHi, hdrQHi, hdrPhase, Fits] at *
    omega)

attribute [local irreducible] finishShrinkPostProg

/-- Runs `finishRandFillProg base` when `ph0 = 5` and `offBM ≤ cur0`. -/
def optFinishRandFillProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((ph0, stg0), (cur0, base)) =>
    if ph0 = 5 then do
      let slots0 ← slotPairProg (stg0, base)
      let offBM ← Memory.read (slots0.2 + 31)
      if offBM ≤ cur0 then finishRandFillProg base else pure ()
    else
      pure ()

theorem clientState_optFinishRandFillProg (base : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
      (optFinishRandFillProg
        ((s.mem (base + hdrPhase), s.mem (base + hdrStage)),
         (s.mem (base + hdrCur), base))) =
    if s.mem (base + hdrPhase) = 5 then
      let pDst0 := if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0
      if s.mem (pDst0 + 31) ≤ s.mem (base + hdrCur) then
        (Memory.spec 0).clientState s (finishRandFillProg base)
      else s
    else s := by
  unfold optFinishRandFillProg; dsimp only
  by_cases hp5 : s.mem (base + hdrPhase) = 5
  · rw [ite_eq_left hp5, StateTransitionSpec.clientState_bind, clientState_slotPairProg,
      clientResult_slotPairProg]
    dsimp only
    rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd]
    split_ifs <;> rfl
  · simp only [hp5, ↓reduceIte]; rfl

private theorem validHistory_optFinishRandFillProg {w ph0 stg0 cur0 base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hb : base + 192 ≤ s.frontier)
    (hrf : ph0 = 5 →
      s.mem ((if stg0 = 0 then base + hdrPBase1 else base + hdrPBase0) + 31) ≤ cur0 →
      FinishRandFillPre w base s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (optFinishRandFillProg ((ph0, stg0), (cur0, base)))) := by
  unfold optFinishRandFillProg; dsimp only
  refine vh_ite _ (fun hp5 => ?_) (fun _ => trivial)
  refine vh_seq (validHistory_slotPairProg w _ s) fun sa hsa slots0 hsl => ?_
  rw [hsa, clientState_slotPairProg, hsl, clientResult_slotPairProg]
  dsimp only
  refine vh_rd (by unfold hdrPBase0 hdrPBase1; split_ifs <;> omega) ?_
  exact vh_ite _ (fun hle => validHistory_finishRandFillProg hwf (hrf hp5 hle))
    (fun _ => trivial)

private theorem realizesBounded_optFinishRandFill :
    RealizesBounded .exact optFinishRandFillProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((ph0, stg0), (cur0, base)) s =>
        4 ≤ w ∧ base + 192 ≤ s.frontier ∧
        (ph0 = 5 →
          s.mem ((if stg0 = 0 then base + hdrPBase1 else base + hdrPBase0) + 31) ≤ cur0 →
          FinishRandFillPre w base s))
      (fun _ _ => 0) := by
  have hsl := realizesBounded_slotPair
  have hrf := realizesBounded_finishRandFill
  realize
  all_goals (
    rcases d with ⟨⟨ph0, stg0⟩, ⟨cur0, base⟩⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hw4, hb, hpre⟩ := h
    have h16 : 16 ≤ 2 ^ w := (by decide : 16 = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) hw4
    have hfr_w := hmem.1
    repeat rw [clientState_slotPairProg] at *
    repeat rw [clientResult_slotPairProg] at *
    try dsimp only [Prod.fst, Prod.snd] at *
    first
    | exact hpre ‹_› (by omega)
    | (try simp only [hdrPBase0, hdrPBase1, Fits] at *
       by_cases hstg : stg0 = 0 <;> (simp only [hstg, ↓reduceIte] at *; omega)))

attribute [local irreducible] optFinishRandFillProg

/-- Second half of `postRandShrinkProg`: computes `k_shrink ≤ bulkBatchWhp` and runs
`finishShrinkPostProg` when `phase = 11` and `diff ≤ bulkBatchWhp`. -/
def calcPostShrinkProg : ℕ × ℕ → Memory.Prog ℕ
  | (base, curFr) => do
    let ph ← Memory.read (base + hdrPhase)
    let wv ← Memory.read (base + hdrW)
    let vb ← Memory.read (base + hdrValBits)
    let nLive ← Memory.read (base + hdrLive)
    let ibLo ← Memory.read (base + hdrItemLo)
    let ibHi ← Memory.read (base + hdrItemHi)
    let qLo ← Memory.read (base + hdrQLo)
    let qHi ← Memory.read (base + hdrQHi)
    if ph < 2 then do
      let pw ← pairStreamWordsSafeProg (((nLive, qLo), vb), wv)
      clampSubProg (curFr, ibLo + pw)
    else if ph = 11 then do
      let pw ← pairStreamWordsSafeProg (((nLive, qLo), vb), wv)
      let diff ← clampSubProg (curFr, ibLo + pw)
      if diff ≤ bulkBatchWhp then do
        finishShrinkPostProg base
        pure diff
      else
        pure bulkBatchWhp
    else do
      let pw ← pairStreamWordsSafeProg (((nLive, qHi), vb), wv)
      clampSubProg (curFr, ibHi + pw)

private theorem validHistory_calcPostShrinkProg {w base curFr : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hb : base + 48 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (calcPostShrinkProg (base, curFr))) := by
  unfold calcPostShrinkProg
  refine vh_rd (by unfold hdrPhase; omega) <| vh_rd (by unfold hdrW; omega) <|
    vh_rd (by unfold hdrValBits; omega) <| vh_rd (by unfold hdrLive; omega) <|
    vh_rd (by unfold hdrItemLo; omega) <| vh_rd (by unfold hdrItemHi; omega) <|
    vh_rd (by unfold hdrQLo; omega) <| vh_rd (by unfold hdrQHi; omega) ?_
  refine vh_ite _
    (fun _ => vh_seq (validHistory_pairStreamWordsSafeProg w _ _) fun sa hsa _ _ => by
      rw [hsa]; exact validHistory_clampSubProg w _ _)
    fun _ => ?_
  refine vh_ite _ (fun _ => ?_)
    (fun _ => vh_seq (validHistory_pairStreamWordsSafeProg w _ _) fun sa hsa _ _ => by
      rw [hsa]; exact validHistory_clampSubProg w _ _)
  refine vh_seq (validHistory_pairStreamWordsSafeProg w _ _) fun s2 hs2 _ _ => ?_
  rw [hs2, clientState_pairStreamWordsSafeProg]
  refine vh_seq (validHistory_clampSubProg w _ _) fun s3 hs3 _ _ => ?_
  rw [hs3, clientState_clampSubProg]
  refine vh_ite _ (fun _ => ?_) (fun _ => trivial)
  exact vh_seq (validHistory_finishShrinkPostProg hwf hb) fun _ _ _ _ => trivial

private theorem realizesBounded_calcPostShrink :
    RealizesBounded .exact calcPostShrinkProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (base, _) s =>
        11 ≤ w ∧ base + 48 ≤ s.frontier ∧ s.mem (base + hdrW) = w ∧
        s.mem (base + hdrValBits) ≤ w ∧ s.mem (base + hdrQLo) ≤ w ∧ s.mem (base + hdrQHi) ≤ w ∧
        Fits w (s.mem (base + hdrItemLo) +
          pairStreamWords (s.mem (base + hdrLive)) (s.mem (base + hdrQLo))
            (s.mem (base + hdrValBits)) w) ∧
        Fits w (s.mem (base + hdrItemHi) +
          pairStreamWords (s.mem (base + hdrLive)) (s.mem (base + hdrQHi))
            (s.mem (base + hdrValBits)) w))
      (fun _ _ => 0) := by
  have hps := realizesBounded_pairStreamWordsSafe
  have hcs := realizesBounded_clampSub
  have hsp := realizesBounded_finishShrinkPost
  realize
  all_goals (
    rcases d with ⟨base, curFr⟩
    dsimp only [Prod.fst, Prod.snd] at *
    obtain ⟨hw11, hb, hwv, hvb, hqL, hqH, hfL, hfH⟩ := h
    have hw_pos : 0 < w := by omega
    have h2048 : 2048 ≤ 2 ^ w :=
      (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
    have hfr_w := hmem.1
    subst hwv
    repeat rw [clientState_pairStreamWordsSafeProg] at *
    repeat rw [pairStreamWordsSafeProg_res hw_pos] at *
    repeat rw [clientState_clampSubProg] at *
    repeat rw [clientResult_clampSubProg] at *
    try simp only [hdrPhase, hdrW, hdrValBits, hdrLive, hdrItemLo, hdrItemHi, hdrQLo, hdrQHi,
      bulkBatchWhp, Fits] at *
    try omega)

attribute [local irreducible] calcPostShrinkProg

/-- Post-`randFill` finalization and bounded `k_shrink ≤ bulkBatchWhp` computation (`0` on `query`).
-/
def postRandShrinkProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((base, curFr), opTag) =>
    if opTag = 0 then
      pure 0
    else do
      let ph0 ← Memory.read (base + hdrPhase)
      let stg0 ← Memory.read (base + hdrStage)
      let cur0 ← Memory.read (base + hdrCur)
      optFinishRandFillProg ((ph0, stg0), (cur0, base))
      calcPostShrinkProg (base, curFr)

/-- Precondition for `postRandShrinkProg`. -/
@[expose] def PostRandShrinkPre (w : ℕ) : (ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((base, curFr), opTag), s =>
    opTag = 0 ∨
    (11 ≤ w ∧ base + 192 ≤ s.frontier ∧ Fits w curFr ∧
      (let stg0 := s.mem (base + hdrStage)
       let pDst0 := if stg0 = 0 then base + hdrPBase1 else base + hdrPBase0
       s.mem (base + hdrPhase) = 5 → s.mem (pDst0 + 31) ≤ s.mem (base + hdrCur) →
         FinishRandFillPre w base s) ∧
      (let s1 :=
        if s.mem (base + hdrPhase) = 5 then
          let pDst0 := if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0
          if s.mem (pDst0 + 31) ≤ s.mem (base + hdrCur) then
            (Memory.spec 0).clientState s (finishRandFillProg base)
          else s
        else s
       s1.mem (base + hdrW) = w ∧ s1.mem (base + hdrValBits) ≤ w ∧
       s1.mem (base + hdrQLo) ≤ w ∧ s1.mem (base + hdrQHi) ≤ w ∧
       Fits w (s1.mem (base + hdrItemLo) +
         pairStreamWords (s1.mem (base + hdrLive)) (s1.mem (base + hdrQLo))
           (s1.mem (base + hdrValBits)) w) ∧
       Fits w (s1.mem (base + hdrItemHi) +
         pairStreamWords (s1.mem (base + hdrLive)) (s1.mem (base + hdrQHi))
           (s1.mem (base + hdrValBits)) w)))

theorem validHistory_postRandShrinkProg {w : ℕ} {x : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : PostRandShrinkPre w x s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (postRandShrinkProg x)) := by
  rcases x with ⟨⟨base, curFr⟩, opTag⟩
  unfold postRandShrinkProg; dsimp only
  refine vh_ite (opTag = 0) (fun _ => trivial) fun hne => ?_
  rcases hpre with h0 | ⟨_, hb, _, hrf, _⟩
  · exact absurd h0 hne
  refine vh_rd (by unfold hdrPhase; omega) <| vh_rd (by unfold hdrStage; omega) <|
    vh_rd (by unfold hdrCur; omega) ?_
  have vhr := validHistory_optFinishRandFillProg hwf hb hrf
  refine vh_seq vhr fun s1 hs1 _ _ => ?_
  have hwf1 := wf_step hwf vhr
  have hfr_le : s.frontier ≤ s1.frontier := by
    rw [hs1, ← (Memory.spec 0).run_runClient _ s]; exact Memory.frontier_le_run s _
  exact validHistory_calcPostShrinkProg (hs1 ▸ hwf1) (by omega)

theorem realizesBounded_postRandShrink :
    RealizesBounded .exact postRandShrinkProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      PostRandShrinkPre (fun _ _ => 0) := by
  have horf := realizesBounded_optFinishRandFill
  have hcps := realizesBounded_calcPostShrink
  realize
  all_goals (
    rcases d with ⟨⟨base, curFr⟩, opTag⟩
    dsimp only [Prod.fst, Prod.snd] at *
    rcases h with h0 | ⟨hw11, hb, hcf, hrf_pre, hs1_pre⟩
    · exfalso; exact ‹¬opTag = 0› h0
    have hfr_w := hmem.1
    have hfr_orf : s.frontier ≤
        ((Memory.spec 0).clientState s
          (optFinishRandFillProg
            ((s.mem (base + hdrPhase), s.mem (base + hdrStage)),
             (s.mem (base + hdrCur), base)))).frontier := by
      rw [← (Memory.spec 0).run_runClient _ s]; exact Memory.frontier_le_run s _
    dsimp only [Prod.fst, Prod.snd] at hrf_pre hs1_pre
    obtain ⟨hwv1, hvb1, hqL1, hqH1, hfL1, hfH1⟩ := hs1_pre
    try rw [clientState_optFinishRandFillProg base s] at hfr_orf ⊢
    first
    | exact hrf_pre
    | exact hwv1
    | exact hvb1
    | exact hqL1
    | exact hqH1
    | exact hfL1
    | exact hfH1
    | (try simp only [hdrPhase, hdrStage, hdrCur, Fits] at *; omega))

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
