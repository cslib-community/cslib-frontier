/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochDrain
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sub-Epoch Drain Ticks, Rollover (`advanceSubEpochProg`), and Good-Seed Potential

This module wraps the elementary `drainTryStepProg` and `drainOldSlotProg` routines of
`LargeEpochDrain` into the background draining schedules and rollover controller for the large
hashed epoch of [Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]:

* `drainTryTickProg` / `drainTrySteps5Prog`: runs `5` candidate-salt ticks before bucket insertion
  to maintain `4 * tryIns + 5 * (cnt - tryPos) + 5 ≤ 20 * L ^ 12` unconditionally while preserving
  `drainPotential`.
* `drainTickProg` / `drainTicks16Prog`: runs `16` deamortized draining ticks per update operation
  during the first half of each sub-epoch (`subStep < Q / 2`).
* `advanceSubEpochProg`: steps `subStep` through both halves of the sub-epoch (`BufOld` drain in
  `[0, Q / 2)`, incremental node clearing in `[Q / 2, Q)`, invoking `fastEnterFallbackProg` from
  `LargeEpochSubEpoch` if any drain work remains at `Q / 2`), flipping `curBufRole` at `Q`.
* `drainPotential`: strict `ℕ`-valued potential showing that under `GoodEpochSeeds win seeds`,
  `drainTicks16Prog` drains every `BufOld` slot and resolves every fingerprint collision strictly
  before `subStep + 1 = Q / 2`, so `advanceSubEpochProg` never enters fallback on good seeds.

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
open Finset

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: Single Drain Ticks (`drainTryTickProg`, `drainTickProg`) & Compositions -/

/-- Advance candidate salt search by 1 step when `tryAct = 1`; if the step commits (`tryAct' = 0`),
immediately run `drainOldSlotProg` to advance `drainPos` past the cleared slot in the same tick.
No-op when `tryAct = 0` (`¬ReadsWidth`). -/
def drainTryTickProg (pBase : ℕ) : Memory.Prog Unit := do
  let ta ← fastReadMetaProg (pBase, 6)
  if ta = 1 then do
    drainTryStepProg pBase
    let ta' ← fastReadMetaProg (pBase, 6)
    if ta' = 0 then
      drainOldSlotProg pBase
    else
      pure ()
  else
    pure ()

theorem drainTryTickProg_pre {w pBase : ℕ} {s : Memory.State} (h : FastProgPre w pBase s) :
    FastProgPre w pBase ((Memory.spec 0).clientState s (drainTryTickProg pBase)) := by
  unfold drainTryTickProg
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind]
    have h1 := drainTryStepProg_pre h
    rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
    split_ifs
    · exact drainOldSlotProg_pre h1
    · exact h1
  · exact h

theorem realizesBounded_drainTryTick :
    RealizesBounded .exact drainTryTickProg
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hts := realizesBounded_drainTryStep
  have hos := realizesBounded_drainOldSlot
  realize
  all_goals (
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg] at *
    first
    | exact ⟨fl, rfl, hr⟩
    | exact drainTryStepProg_pre ⟨fl, rfl, hr⟩
    | omega)

/-- Cost bound for a single `drainTryTickProg` / `drainTickProg` step (`O_c(1)`). -/
@[expose] def drainTickCost (c : ℕ) : ℕ :=
  4220 + 42 * dTabWhp c * (cTabWhp c + 2) + 2 * cTabWhp c + 864 * hMaxBTree

private theorem drainTryStepProg_cost_le (c : ℕ) :
    600 + 6 * dTabWhp c * (cTabWhp c + 2) + 84 * hMaxBTree +
      (3600 + 36 * dTabWhp c * (cTabWhp c + 2) + 2 * cTabWhp c + 780 * hMaxBTree) + 10 ≤
      drainTickCost c := by
  unfold drainTickCost
  have hd : 6 * dTabWhp c * (cTabWhp c + 2) + 36 * dTabWhp c * (cTabWhp c + 2) =
      42 * dTabWhp c * (cTabWhp c + 2) := by ring
  omega

/-- Unconditional single-step specification for `drainTryTickProg`: preserves `FastEpochInvGen`
on **100%** of hash seeds, leaves `BlockPool`, `BufCur`, `curBufRole`, `subStep`, `fl.io.OwnsAddr`,
and `¬fl.OwnsFastAddr` intact, and raises bucket `b`'s `try` slack by `+1` whenever
`bp.bktCount b < capMaxWhp fl.N` and `k ≤ 4`. -/
theorem drainTryTickProg_spec {slackCur : ℕ} {fl : FastEpochLayout} {w slack b k : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hb : b < numBucketsWhp fl.N)
    (hcnt_lt : (extractBlockPool fl.mp s.mem).bktCount b < capMaxWhp fl.N)
    (hk_le : k ≤ 4)
    (hslack_in : let fm := extractFastMeta fl s.mem
      fm.tryAct = 1 → fm.tryBkt = b →
        4 * fm.tryIns + 5 * ((extractBlockPool fl.mp s.mem).bktCount b - fm.tryPos) + k ≤
          20 * slabScale fl.N ^ 12) :
    let s' := (Memory.spec 0).clientState s (drainTryTickProg fl.pBase)
    let fm := extractFastMeta fl s.mem
    let fm' := extractFastMeta fl s'.mem
    s'.frontier = s.frontier ∧
    memoryCost (drainTryTickProg fl.pBase) s ≤ drainTickCost fl.c ∧
    FastEpochInvGen slackCur fl slack seeds s'.mem s_abs ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    extractBufTrie (fl.trieL fm.curBufRole) s'.mem =
      extractBufTrie (fl.trieL fm.curBufRole) s.mem ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    fm'.curBufRole = fm.curBufRole ∧
    fm'.subStep = fm.subStep ∧
    (fm.tryAct = 0 → s' = s) ∧
    (fm'.tryAct = 1 → fm'.tryBkt = b →
      4 * fm'.tryIns + 5 * ((extractBlockPool fl.mp s.mem).bktCount b - fm'.tryPos) + (k + 1) ≤
        20 * slabScale fl.N ^ 12) := by
  dsimp only
  have hpt := hinv.param_table
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  have hm6_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 6)) = fm.tryAct :=
    clientResult_fastReadMetaProg hpt (by decide)
  have cm6 := memoryCost_fastReadMetaProg (fl.pBase, 6) s
  have hcnt5 : 5 * bp.bktCount b + 5 ≤ 20 * slabScale fl.N ^ 12 := by
    have hlt : bp.bktCount b + 1 ≤ 4 * slabScale fl.N ^ 12 := hcnt_lt
    omega
  have _ := hb
  unfold drainTryTickProg
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hm6_r]
  by_cases hta : fm.tryAct = 1
  · rw [ite_eq_left hta]
    obtain ⟨hfr1, hc1, hinv1, hbp1, htr1, hoi1, hof1, hcr1, hss1, _, _, _, _, htri1⟩ :=
      drainTryStepProg_spec hv hinv
    set s1 := (Memory.spec 0).clientState s (drainTryStepProg fl.pBase)
    set fm1 := extractFastMeta fl s1.mem
    have hpt1 := hinv1.param_table
    have hm6_r1 : (Memory.spec 0).clientResult s1 (fastReadMetaProg (fl.pBase, 6)) =
        fm1.tryAct := clientResult_fastReadMetaProg hpt1 (by decide)
    have cm6_1 := memoryCost_fastReadMetaProg (fl.pBase, 6) s1
    have hsub : fm.subStep < qEpochWhp fl.N / 2 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, htry⟩ := hinv.tiers
      exact (htry hta).1
    have hsub1 : fm1.subStep < qEpochWhp fl.N / 2 := hss1.symm ▸ hsub
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadMetaProg, hm6_r1]
    rcases htri1 hta with ⟨htp_lt, hta1, htb1, _, htp1, hti1, _⟩ |
        ⟨hta1, htb1, htp0, hti0, _, _, _⟩ |
        ⟨_, hta0, _, _, _, _, _⟩
    · -- Case A: `tryPos + 1`, `tryAct = 1`
      have hne0 : fm1.tryAct ≠ 0 := by rw [hta1]; exact Nat.one_ne_zero
      rw [ite_eq_right hne0, StateTransitionSpec.clientState_pure, memoryCost_pure]
      have hcost := drainTryStepProg_cost_le fl.c
      change memoryCost (fastReadMetaProg (fl.pBase, 6)) s1 ≤ 2 at cm6_1
      dsimp only [s1] at cm6_1 hc1 hfr1 hinv1 hbp1 htr1 hoi1 hof1 hcr1 hss1
      refine ⟨hfr1, by omega, hinv1, hbp1, htr1 fm.curBufRole hinv.role_lt, hoi1, hof1,
        hcr1, hss1, fun h0 => absurd (h0.symm.trans hta) Nat.zero_ne_one, fun _ htb_eq => ?_⟩
      have htb_orig : fm.tryBkt = b := htb1.symm.trans htb_eq
      have hin := hslack_in hta htb_orig
      have hlt_b : fm.tryPos < bp.bktCount b := by rw [← htb_orig]; exact htp_lt
      change fm1.tryPos = fm.tryPos + 1 at htp1
      have hti_le : fm1.tryIns ≤ fm.tryIns + 1 := ‹_›
      have hsub_eq : bp.bktCount b - fm.tryPos = (bp.bktCount b - (fm.tryPos + 1)) + 1 := by
        omega
      change 4 * fm1.tryIns + 5 * (bp.bktCount b - fm1.tryPos) + (k + 1) ≤ _
      rw [htp1]
      change 4 * fm.tryIns + 5 * (bp.bktCount b - fm.tryPos) + k ≤ _ at hin
      linarith only [hin, hti_le, hsub_eq]
    · -- Case B: salt reset (`tryPos = 0, tryIns = 0`)
      have hne0 : fm1.tryAct ≠ 0 := by rw [hta1]; exact Nat.one_ne_zero
      rw [ite_eq_right hne0, StateTransitionSpec.clientState_pure, memoryCost_pure]
      have hcost := drainTryStepProg_cost_le fl.c
      dsimp only [s1] at cm6_1
      refine ⟨hfr1, by omega, hinv1, hbp1, htr1 fm.curBufRole hinv.role_lt, hoi1, hof1,
        hcr1, hss1, fun h0 => absurd (h0.symm.trans hta) Nat.zero_ne_one, fun _ _ => ?_⟩
      rw [htp0, hti0]; omega
    · -- Case C: committed (`tryAct' = 0`), immediately run `drainOldSlotProg`
      rw [ite_eq_left hta0]
      obtain ⟨hfr2, hc2, hinv2, hbp2, htr2_c, hoi2, hof2, hcr2, hss2, _, hnoop2, hact2⟩ :=
        drainOldSlotProg_spec (hfr1.symm ▸ hv) hinv1 hsub1 hta0
      have hcost := drainTryStepProg_cost_le fl.c
      dsimp only [s1] at cm6_1 hc2
      have htr_eq : extractBufTrie (fl.trieL fm.curBufRole)
          ((Memory.spec 0).clientState s1 (drainOldSlotProg fl.pBase)).mem =
          extractBufTrie (fl.trieL fm.curBufRole) s.mem := by
        have h1 : extractBufTrie (fl.trieL fm.curBufRole)
            ((Memory.spec 0).clientState s1 (drainOldSlotProg fl.pBase)).mem =
            extractBufTrie (fl.trieL fm1.curBufRole)
              ((Memory.spec 0).clientState s1 (drainOldSlotProg fl.pBase)).mem := by rw [hcr1]
        rw [h1, htr2_c, hcr1]
        exact htr1 fm.curBufRole hinv.role_lt
      refine ⟨hfr2.trans hfr1, by omega, hinv2, hbp2.trans hbp1, htr_eq,
        fun a ha => (hoi2 a ha).trans (hoi1 a ha),
        fun a ha => (hof2 a ha).trans (hof1 a ha),
        hcr2.trans hcr1, hss2.trans hss1,
        fun h0 => absurd (h0.symm.trans hta) Nat.zero_ne_one, fun hta2 _ => ?_⟩
      set oldTr1 := extractBufTrie (fl.trieL (1 - fm1.curBufRole)) s1.mem
      by_cases hdp_lt : fm1.drainPos < oldTr1.itemAlloc
      · rcases hact2 hdp_lt with ⟨_, _, h0, _⟩ | ⟨_, _, _, _, _, _, _, _, h0, _⟩ |
            ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h0, _⟩ |
            ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htp0, hti0, _, _⟩
        · exact absurd (hta2.symm.trans h0) Nat.one_ne_zero
        · exact absurd (hta2.symm.trans h0) Nat.one_ne_zero
        · exact absurd (hta2.symm.trans h0) Nat.one_ne_zero
        · rw [htp0, hti0]; omega
      · have hst2 := hnoop2 (Nat.le_of_not_lt hdp_lt)
        change (Memory.spec 0).clientState s1 (drainOldSlotProg fl.pBase) = s1 at hst2
        rw [hst2] at hta2
        exact absurd (hta2.symm.trans hta0) Nat.one_ne_zero
  · rw [ite_eq_right hta, StateTransitionSpec.clientState_pure, memoryCost_pure]
    have hcost := drainTryStepProg_cost_le fl.c
    refine ⟨rfl, by omega, hinv, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl,
      fun _ => rfl, fun hta' => absurd hta' hta⟩

/-- Run `5` `drainTryTickProg` steps before inserting into a bucket so that
`4 * tryIns + 5 * (cnt - tryPos) + 5 ≤ 20 * L ^ 12` holds when `cnt < capMaxWhp fl.N`. -/
def drainTrySteps5Prog (pBase : ℕ) : Memory.Prog Unit := do
  drainTryTickProg pBase
  drainTryTickProg pBase
  drainTryTickProg pBase
  drainTryTickProg pBase
  drainTryTickProg pBase

theorem drainTrySteps5Prog_pre {w pBase : ℕ} {s : Memory.State} (h : FastProgPre w pBase s) :
    FastProgPre w pBase ((Memory.spec 0).clientState s (drainTrySteps5Prog pBase)) := by
  unfold drainTrySteps5Prog
  iterate 4 rw [StateTransitionSpec.clientState_bind]
  exact drainTryTickProg_pre (drainTryTickProg_pre (drainTryTickProg_pre
    (drainTryTickProg_pre (drainTryTickProg_pre h))))

theorem realizesBounded_drainTrySteps5 :
    RealizesBounded .exact drainTrySteps5Prog
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have ht := realizesBounded_drainTryTick
  realize
  all_goals first
    | exact h
    | exact drainTryTickProg_pre h
    | exact drainTryTickProg_pre (drainTryTickProg_pre h)
    | exact drainTryTickProg_pre (drainTryTickProg_pre (drainTryTickProg_pre h))
    | exact drainTryTickProg_pre (drainTryTickProg_pre
        (drainTryTickProg_pre (drainTryTickProg_pre h)))

theorem drainTrySteps5Prog_spec {slackCur : ℕ} {fl : FastEpochLayout} {w slack b : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hb : b < numBucketsWhp fl.N)
    (hcnt_lt : (extractBlockPool fl.mp s.mem).bktCount b < capMaxWhp fl.N) :
    let s' := (Memory.spec 0).clientState s (drainTrySteps5Prog fl.pBase)
    let fm := extractFastMeta fl s.mem
    let fm' := extractFastMeta fl s'.mem
    s'.frontier = s.frontier ∧
    memoryCost (drainTrySteps5Prog fl.pBase) s ≤ 5 * drainTickCost fl.c ∧
    FastEpochInvGen slackCur fl slack seeds s'.mem s_abs ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    extractBufTrie (fl.trieL fm.curBufRole) s'.mem =
      extractBufTrie (fl.trieL fm.curBufRole) s.mem ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    fm'.curBufRole = fm.curBufRole ∧
    fm'.subStep = fm.subStep ∧
    (fm'.tryAct = 1 → fm'.tryBkt = b →
      4 * fm'.tryIns + 5 * ((extractBlockPool fl.mp s.mem).bktCount b - fm'.tryPos) + 5 ≤
        20 * slabScale fl.N ^ 12) := by
  dsimp only
  have h0_sl : (extractFastMeta fl s.mem).tryAct = 1 → (extractFastMeta fl s.mem).tryBkt = b →
      4 * (extractFastMeta fl s.mem).tryIns +
        5 * ((extractBlockPool fl.mp s.mem).bktCount b - (extractFastMeta fl s.mem).tryPos) + 0 ≤
        20 * slabScale fl.N ^ 12 := fun hta htb => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, htry⟩ := hinv.tiers
    have h := (htry hta).2.choose_spec.choose_spec.2.2.1
    rw [htb] at h; simpa only [Nat.add_zero] using h
  obtain ⟨f1, c1, i1, bp1, tr1, io1, of1, cr1, ss1, _, sl1⟩ :=
    drainTryTickProg_spec (k := 0) hv hinv hb hcnt_lt (by decide) h0_sl
  set s1 := (Memory.spec 0).clientState s (drainTryTickProg fl.pBase)
  obtain ⟨f2, c2, i2, bp2, tr2, io2, of2, cr2, ss2, _, sl2⟩ :=
    drainTryTickProg_spec (k := 1) (f1.symm ▸ hv) i1 hb (bp1.symm ▸ hcnt_lt) (by decide)
      (by rwa [bp1])
  set s2 := (Memory.spec 0).clientState s1 (drainTryTickProg fl.pBase)
  obtain ⟨f3, c3, i3, bp3, tr3, io3, of3, cr3, ss3, _, sl3⟩ :=
    drainTryTickProg_spec (k := 2) ((f2.trans f1).symm ▸ hv) i2 hb
      ((bp2.trans bp1).symm ▸ hcnt_lt) (by decide) (by rwa [bp2])
  set s3 := (Memory.spec 0).clientState s2 (drainTryTickProg fl.pBase)
  obtain ⟨f4, c4, i4, bp4, tr4, io4, of4, cr4, ss4, _, sl4⟩ :=
    drainTryTickProg_spec (k := 3) ((f3.trans (f2.trans f1)).symm ▸ hv) i3 hb
      ((bp3.trans (bp2.trans bp1)).symm ▸ hcnt_lt) (by decide) (by rwa [bp3])
  set s4 := (Memory.spec 0).clientState s3 (drainTryTickProg fl.pBase)
  obtain ⟨f5, c5, i5, bp5, tr5, io5, of5, cr5, ss5, _, sl5⟩ :=
    drainTryTickProg_spec (k := 4) ((f4.trans (f3.trans (f2.trans f1))).symm ▸ hv) i4 hb
      ((bp4.trans (bp3.trans (bp2.trans bp1))).symm ▸ hcnt_lt) (by decide) (by rwa [bp4])
  unfold drainTrySteps5Prog
  iterate 4 rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  dsimp only [s1, s2, s3, s4] at c2 c3 c4 c5
  refine ⟨f5.trans (f4.trans (f3.trans (f2.trans f1))), by omega, i5,
    bp5.trans (bp4.trans (bp3.trans (bp2.trans bp1))), ?_,
    fun a ha => (io5 a ha).trans ((io4 a ha).trans ((io3 a ha).trans
      ((io2 a ha).trans (io1 a ha)))),
    fun a ha => (of5 a ha).trans ((of4 a ha).trans ((of3 a ha).trans
      ((of2 a ha).trans (of1 a ha)))),
    cr5.trans (cr4.trans (cr3.trans (cr2.trans cr1))),
    ss5.trans (ss4.trans (ss3.trans (ss2.trans ss1))),
    fun hta htb => by have h := sl5 hta htb; rwa [bp4, bp3, bp2, bp1] at h⟩
  have e4 := cr4.trans (cr3.trans (cr2.trans cr1))
  have e3 := cr3.trans (cr2.trans cr1)
  have e2 := cr2.trans cr1
  have t5 : extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole)
      ((Memory.spec 0).clientState s4 (drainTryTickProg fl.pBase)).mem =
      extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s4.mem := by
    rw [← e4]; exact tr5
  have t4 : extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s4.mem =
      extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s3.mem := by
    rw [← e3]; exact tr4
  have t3 : extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s3.mem =
      extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s2.mem := by
    rw [← e2]; exact tr3
  have t2 : extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s2.mem =
      extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s1.mem := by
    rw [← cr1]; exact tr2
  exact t5.trans (t4.trans (t3.trans (t2.trans tr1)))

/-- One background `BufOld` draining tick (`subStep < Q / 2`): if `tryAct = 1`, step the
candidate salt search (and immediately drain `drainPos` if it commits to `tryAct = 0`); else drain
`drainPos` via `drainOldSlotProg` (`¬ReadsWidth`). -/
def drainTickProg (pBase : ℕ) : Memory.Prog Unit := do
  let ta ← fastReadMetaProg (pBase, 6)
  if ta = 1 then do
    drainTryStepProg pBase
    let ta' ← fastReadMetaProg (pBase, 6)
    if ta' = 0 then
      drainOldSlotProg pBase
    else
      pure ()
  else
    drainOldSlotProg pBase

theorem drainTickProg_pre {w pBase : ℕ} {s : Memory.State} (h : FastProgPre w pBase s) :
    FastProgPre w pBase ((Memory.spec 0).clientState s (drainTickProg pBase)) := by
  unfold drainTickProg
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind]
    have h1 := drainTryStepProg_pre h
    rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
    split_ifs
    · exact drainOldSlotProg_pre h1
    · exact h1
  · exact drainOldSlotProg_pre h

theorem realizesBounded_drainTick :
    RealizesBounded .exact drainTickProg
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hts := realizesBounded_drainTryStep
  have hos := realizesBounded_drainOldSlot
  realize
  all_goals (
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg] at *
    first
    | exact ⟨fl, rfl, hr⟩
    | exact drainTryStepProg_pre ⟨fl, rfl, hr⟩
    | omega)

theorem drainTickProg_spec {slackCur : ℕ} {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hsub : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2) :
    let s' := (Memory.spec 0).clientState s (drainTickProg fl.pBase)
    let fm := extractFastMeta fl s.mem
    let fm' := extractFastMeta fl s'.mem
    s'.frontier = s.frontier ∧
    memoryCost (drainTickProg fl.pBase) s ≤ drainTickCost fl.c ∧
    FastEpochInvGen slackCur fl slack seeds s'.mem s_abs ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    extractBufTrie (fl.trieL fm.curBufRole) s'.mem =
      extractBufTrie (fl.trieL fm.curBufRole) s.mem ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    fm'.curBufRole = fm.curBufRole ∧
    fm'.subStep = fm.subStep := by
  dsimp only
  have hpt := hinv.param_table
  set fm := extractFastMeta fl s.mem
  have hm6_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 6)) = fm.tryAct :=
    clientResult_fastReadMetaProg hpt (by decide)
  have cm6 := memoryCost_fastReadMetaProg (fl.pBase, 6) s
  have hta_le : fm.tryAct ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hle, _⟩ := hinv.tiers; exact hle
  have hcost := drainTryStepProg_cost_le fl.c
  unfold drainTickProg
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hm6_r]
  by_cases hta : fm.tryAct = 1
  · rw [ite_eq_left hta]
    obtain ⟨hfr1, hc1, hinv1, hbp1, htr1, hoi1, hof1, hcr1, hss1, _, _, _, _, _⟩ :=
      drainTryStepProg_spec hv hinv
    set s1 := (Memory.spec 0).clientState s (drainTryStepProg fl.pBase)
    have hm6_r1 : (Memory.spec 0).clientResult s1 (fastReadMetaProg (fl.pBase, 6)) =
        (extractFastMeta fl s1.mem).tryAct :=
      clientResult_fastReadMetaProg hinv1.param_table (by decide)
    have cm6_1 := memoryCost_fastReadMetaProg (fl.pBase, 6) s1
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadMetaProg, hm6_r1]
    by_cases hta0 : (extractFastMeta fl s1.mem).tryAct = 0
    · rw [ite_eq_left hta0]
      obtain ⟨hfr2, hc2, hinv2, hbp2, htr2_c, hoi2, hof2, hcr2, hss2, _⟩ :=
        drainOldSlotProg_spec (hfr1.symm ▸ hv) hinv1 (hss1.symm ▸ hsub) hta0
      dsimp only [s1] at cm6_1 hc2
      refine ⟨hfr2.trans hfr1, by omega, hinv2, hbp2.trans hbp1,
        by have h1 : extractBufTrie (fl.trieL fm.curBufRole)
              ((Memory.spec 0).clientState s1 (drainOldSlotProg fl.pBase)).mem =
              extractBufTrie (fl.trieL (extractFastMeta fl s1.mem).curBufRole)
              ((Memory.spec 0).clientState s1 (drainOldSlotProg fl.pBase)).mem := by rw [hcr1]
           rw [h1, htr2_c, hcr1]; exact htr1 fm.curBufRole hinv.role_lt,
        fun a ha => (hoi2 a ha).trans (hoi1 a ha),
        fun a ha => (hof2 a ha).trans (hof1 a ha),
        hcr2.trans hcr1, hss2.trans hss1⟩
    · rw [ite_eq_right hta0, StateTransitionSpec.clientState_pure, memoryCost_pure]
      dsimp only [s1] at cm6_1
      exact ⟨hfr1, by omega, hinv1, hbp1, htr1 fm.curBufRole hinv.role_lt, hoi1, hof1,
        hcr1, hss1⟩
  · have hta0 : fm.tryAct = 0 := by omega
    rw [ite_eq_right hta]
    obtain ⟨hfr1, hc1, hinv1, hbp1, htr1_c, hoi1, hof1, hcr1, hss1, _⟩ :=
      drainOldSlotProg_spec hv hinv hsub hta0
    exact ⟨hfr1, by omega, hinv1, hbp1, htr1_c, hoi1, hof1, hcr1, hss1⟩

private def drainTicks2Prog (pBase : ℕ) : Memory.Prog Unit := do
  drainTickProg pBase; drainTickProg pBase

private def drainTicks4Prog (pBase : ℕ) : Memory.Prog Unit := do
  drainTicks2Prog pBase; drainTicks2Prog pBase

private def drainTicks8Prog (pBase : ℕ) : Memory.Prog Unit := do
  drainTicks4Prog pBase; drainTicks4Prog pBase

/-- Run `16` consecutive `drainTickProg` ticks per operation in the first half of each sub-epoch
(`¬ReadsWidth`). -/
def drainTicks16Prog (pBase : ℕ) : Memory.Prog Unit := do
  drainTicks8Prog pBase; drainTicks8Prog pBase

private theorem drainTicks2Prog_pre {w pBase : ℕ} {s : Memory.State} (h : FastProgPre w pBase s) :
    FastProgPre w pBase ((Memory.spec 0).clientState s (drainTicks2Prog pBase)) := by
  unfold drainTicks2Prog; rw [StateTransitionSpec.clientState_bind]
  exact drainTickProg_pre (drainTickProg_pre h)

private theorem drainTicks4Prog_pre {w pBase : ℕ} {s : Memory.State} (h : FastProgPre w pBase s) :
    FastProgPre w pBase ((Memory.spec 0).clientState s (drainTicks4Prog pBase)) := by
  unfold drainTicks4Prog; rw [StateTransitionSpec.clientState_bind]
  exact drainTicks2Prog_pre (drainTicks2Prog_pre h)

private theorem drainTicks8Prog_pre {w pBase : ℕ} {s : Memory.State} (h : FastProgPre w pBase s) :
    FastProgPre w pBase ((Memory.spec 0).clientState s (drainTicks8Prog pBase)) := by
  unfold drainTicks8Prog; rw [StateTransitionSpec.clientState_bind]
  exact drainTicks4Prog_pre (drainTicks4Prog_pre h)

theorem drainTicks16Prog_pre {w pBase : ℕ} {s : Memory.State} (h : FastProgPre w pBase s) :
    FastProgPre w pBase ((Memory.spec 0).clientState s (drainTicks16Prog pBase)) := by
  unfold drainTicks16Prog; rw [StateTransitionSpec.clientState_bind]
  exact drainTicks8Prog_pre (drainTicks8Prog_pre h)

private theorem realizesBounded_drainTicks2 :
    RealizesBounded .exact drainTicks2Prog
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have h1 := realizesBounded_drainTick
  realize
  all_goals first | exact h | exact drainTickProg_pre h

private theorem realizesBounded_drainTicks4 :
    RealizesBounded .exact drainTicks4Prog
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have h2 := realizesBounded_drainTicks2
  realize
  all_goals first | exact h | exact drainTicks2Prog_pre h

private theorem realizesBounded_drainTicks8 :
    RealizesBounded .exact drainTicks8Prog
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have h4 := realizesBounded_drainTicks4
  realize
  all_goals first | exact h | exact drainTicks4Prog_pre h

theorem realizesBounded_drainTicks16 :
    RealizesBounded .exact drainTicks16Prog
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have h8 := realizesBounded_drainTicks8
  realize
  all_goals first | exact h | exact drainTicks8Prog_pre h

theorem drainTicks16Prog_spec {slackCur : ℕ} {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hsub : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2) :
    let s' := (Memory.spec 0).clientState s (drainTicks16Prog fl.pBase)
    let fm := extractFastMeta fl s.mem
    let fm' := extractFastMeta fl s'.mem
    s'.frontier = s.frontier ∧
    memoryCost (drainTicks16Prog fl.pBase) s ≤ 16 * drainTickCost fl.c ∧
    FastEpochInvGen slackCur fl slack seeds s'.mem s_abs ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    extractBufTrie (fl.trieL fm.curBufRole) s'.mem =
      extractBufTrie (fl.trieL fm.curBufRole) s.mem ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    fm'.curBufRole = fm.curBufRole ∧
    fm'.subStep = fm.subStep := by
  have dbl : ∀ (p : ℕ → Memory.Prog Unit) (m : ℕ),
      (∀ (st : Memory.State), fl.Valid w st.frontier →
        FastEpochInvGen slackCur fl slack seeds st.mem s_abs →
        (extractFastMeta fl st.mem).subStep < qEpochWhp fl.N / 2 →
        let st' := (Memory.spec 0).clientState st (p fl.pBase)
        let fm0 := extractFastMeta fl st.mem
        let fm1 := extractFastMeta fl st'.mem
        st'.frontier = st.frontier ∧
        memoryCost (p fl.pBase) st ≤ m * drainTickCost fl.c ∧
        FastEpochInvGen slackCur fl slack seeds st'.mem s_abs ∧
        extractBlockPool fl.mp st'.mem = extractBlockPool fl.mp st.mem ∧
        extractBufTrie (fl.trieL fm0.curBufRole) st'.mem =
          extractBufTrie (fl.trieL fm0.curBufRole) st.mem ∧
        (∀ addr, fl.io.OwnsAddr addr → st'.mem addr = st.mem addr) ∧
        (∀ addr, ¬fl.OwnsFastAddr addr → st'.mem addr = st.mem addr) ∧
        fm1.curBufRole = fm0.curBufRole ∧
        fm1.subStep = fm0.subStep) →
      ∀ (st : Memory.State), fl.Valid w st.frontier →
        FastEpochInvGen slackCur fl slack seeds st.mem s_abs →
        (extractFastMeta fl st.mem).subStep < qEpochWhp fl.N / 2 →
        let st' := (Memory.spec 0).clientState st (do p fl.pBase; p fl.pBase)
        let fm0 := extractFastMeta fl st.mem
        let fm1 := extractFastMeta fl st'.mem
        st'.frontier = st.frontier ∧
        memoryCost (do p fl.pBase; p fl.pBase) st ≤ (2 * m) * drainTickCost fl.c ∧
        FastEpochInvGen slackCur fl slack seeds st'.mem s_abs ∧
        extractBlockPool fl.mp st'.mem = extractBlockPool fl.mp st.mem ∧
        extractBufTrie (fl.trieL fm0.curBufRole) st'.mem =
          extractBufTrie (fl.trieL fm0.curBufRole) st.mem ∧
        (∀ addr, fl.io.OwnsAddr addr → st'.mem addr = st.mem addr) ∧
        (∀ addr, ¬fl.OwnsFastAddr addr → st'.mem addr = st.mem addr) ∧
        fm1.curBufRole = fm0.curBufRole ∧
        fm1.subStep = fm0.subStep := by
    intro p m hp st hvs his hss
    obtain ⟨f1, c1, i1, bp1, tr1, io1, of1, cr1, ss1⟩ := hp st hvs his hss
    set st1 := (Memory.spec 0).clientState st (p fl.pBase)
    obtain ⟨f2, c2, i2, bp2, tr2, io2, of2, cr2, ss2⟩ :=
      hp st1 (f1.symm ▸ hvs) i1 (ss1.symm ▸ hss)
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
    have hmul : (2 * m) * drainTickCost fl.c = m * drainTickCost fl.c + m * drainTickCost fl.c := by
      ring
    refine ⟨f2.trans f1, by rw [hmul]; exact Nat.add_le_add c1 c2, i2, bp2.trans bp1, ?_,
      fun a ha => (io2 a ha).trans (io1 a ha), fun a ha => (of2 a ha).trans (of1 a ha),
      cr2.trans cr1, ss2.trans ss1⟩
    have htr : extractBufTrie (fl.trieL (extractFastMeta fl st.mem).curBufRole)
        ((Memory.spec 0).clientState st1 (p fl.pBase)).mem =
        extractBufTrie (fl.trieL (extractFastMeta fl st1.mem).curBufRole)
          ((Memory.spec 0).clientState st1 (p fl.pBase)).mem := by rw [cr1]
    exact htr.trans (tr2.trans (by rw [cr1]; exact tr1))
  have h2 := dbl drainTickProg 1 fun st hvs his hss => by
    have h := drainTickProg_spec hvs his hss
    simpa only [one_mul] using h
  have h4 := dbl drainTicks2Prog 2 h2
  have h8 := dbl drainTicks4Prog 4 h4
  have h16 := dbl drainTicks8Prog 8 h8
  exact h16 s hv hinv hsub

/-! ## Section 3: Sub-Epoch Advance & Rollover (`advanceSubEpochProg`) -/

/-- Advance the deamortized sub-epoch controller at the end of any update operation
(`FastEpochInvGen 1` → `FastEpochInv` or `FallbackLayout.StateInv`, `¬ReadsWidth`). -/
def advanceSubEpochProg (pBase : ℕ) : Memory.Prog Unit := do
  let ss ← fastReadMetaProg (pBase, 4)
  let qMax ← Memory.read (pBase + 23)
  let halfQ ← pure (qMax / 2)
  if ss < halfQ then do
    drainTicks16Prog pBase
    if ss + 1 < halfQ then
      fastWriteMetaProg ((pBase, 4), ss + 1)
    else do
      let curR ← fastReadMetaProg (pBase, 3)
      if curR < 2 then do
        let ia ← fastBufItemAllocProg (pBase, 1 - curR)
        let dp ← fastReadMetaProg (pBase, 5)
        let ta ← fastReadMetaProg (pBase, 6)
        if ia ≤ dp ∧ ta = 0 then
          fastWriteMetaProg ((pBase, 4), ss + 1)
        else
          fastEnterFallbackProg pBase
      else
        pure ()
  else do
    let curR ← fastReadMetaProg (pBase, 3)
    if curR < 2 then do
      let oldR ← pure (1 - curR)
      fastBufClearStepsProg (pBase, oldR)
      if 0 < qMax ∧ ss < qMax - 1 then
        fastWriteMetaProg ((pBase, 4), ss + 1)
      else do
        fastWriteMetaProg ((pBase, 3), oldR)
        fastWriteMetaProg ((pBase, 4), 0)
        fastWriteMetaProg ((pBase, 5), 0)
    else
      pure ()

theorem realizesBounded_advanceSubEpoch :
    RealizesBounded .exact advanceSubEpochProg
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hwm := realizesBounded_fastWriteMeta
  have hd16 := realizesBounded_drainTicks16
  have hia := realizesBounded_fastBufItemAlloc
  have hef := realizesBounded_fastEnterFallback
  have hbc := realizesBounded_fastBufClearSteps
  realize
  all_goals (
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hm23 : s.mem (fl.pBase + 23) = qEpochWhp fl.N := hr.2.1 23 (by decide)
    have hq_N : qEpochWhp fl.N ≤ fl.N := hr.1.bounds_le_N.2.2.2
    have hn_w : fl.N < 2 ^ w := hr.1.mp_valid.nCap_lt_two_pow_w
    have h1_w : 1 < 2 ^ w := by omega
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    dsimp only at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg,
      runClient_state_fastBufItemAllocProg, hm23] at *
    have h16 := drainTicks16Prog_pre ⟨fl, rfl, hr⟩
    have hbc_pre := fastBufClearStepsProg_pre (x := (fl.pBase,
      1 - ((Memory.spec 0).runClient s (fastReadMetaProg (fl.pBase, 3))).1)) ⟨fl, rfl, hr⟩
    have hwm_r := fastWriteMetaProg_pre (x := ((fl.pBase, 3),
      1 - ((Memory.spec 0).runClient s (fastReadMetaProg (fl.pBase, 3))).1)) hbc_pre
    have hwm_s := fastWriteMetaProg_pre (x := ((fl.pBase, 4), 0)) hwm_r
    first
    | exact ⟨fl, rfl, hr⟩
    | exact h16
    | exact hbc_pre
    | exact hwm_r
    | exact hwm_s
    | omega)

private theorem qEpochWhp_even_and_ge (N : ℕ) :
    2 ∣ qEpochWhp N ∧ 4 ≤ qEpochWhp N := by
  have hL : 2 ≤ slabScale N := by
    have := Dynamic.one_le_logLogFactor N
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ Dynamic.logLogFactor N := Nat.pow_le_pow_right (by decide) this
  have h2dvd : 2 ∣ slabScale N := by
    have h1 := Dynamic.one_le_logLogFactor N
    rw [show slabScale N = 2 ^ Dynamic.logLogFactor N from rfl]
    exact dvd_pow_self 2 (by omega)
  have hq_eq : qEpochWhp N = slabScale N ^ 18 := rfl
  refine ⟨by rw [hq_eq]; exact dvd_pow h2dvd (by decide), ?_⟩
  rw [hq_eq]
  calc 4 = 2 ^ 2 := by decide
    _ ≤ 2 ^ 18 := Nat.pow_le_pow_right (by decide) (by decide)
    _ ≤ slabScale N ^ 18 := Nat.pow_le_pow_left hL 18

private theorem rawClearableBounds_clearSteps_exact :
    ∀ (k : ℕ) {tr : BufTrie}, RawClearableBounds tr →
      RawClearableBounds (bufClearSteps k tr) ∧
      (bufClearSteps k tr).nodeAlloc = max 1 (tr.nodeAlloc - k) := by
  intro k
  induction k with
  | zero =>
    intro tr hc
    have h1 := hc.1
    exact ⟨hc, by dsimp only [bufClearSteps]; omega⟩
  | succ k ih =>
    intro tr hc
    obtain ⟨hc1, hna1⟩ := hc.clearOne_step
    obtain ⟨hck, hnak⟩ := ih hc1
    exact ⟨hck, by dsimp only [bufClearSteps]; rw [hnak, hna1]; omega⟩

/-- Shared rollover helper for `advanceSubEpochProg` in the first half (`ss < Q / 2`), keeping
`FastEpochInvGen 0` after bumping `subStep := ss + 1`. -/
private theorem advanceSubEpoch_writeSub_half1 {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen 1 fl slack seeds s.mem s_abs)
    (hsub : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2)
    (hbd : (extractFastMeta fl s.mem).subStep + 1 < qEpochWhp fl.N / 2 ∨
      ((extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem).itemAlloc ≤
        (extractFastMeta fl s.mem).drainPos ∧ (extractFastMeta fl s.mem).tryAct = 0)) :
    let fm := extractFastMeta fl s.mem
    let s' := (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, 4), fm.subStep + 1))
    s'.frontier = s.frontier ∧
    FastEpochInv fl slack seeds s'.mem s_abs ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    extractFastMeta fl s'.mem = { fm with subStep := fm.subStep + 1 } := by
  dsimp only
  have hr₀ := hinv.ready hv rfl
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  obtain ⟨mapCur, mapOld, mapBTree, hv_cur, hrb_cur, hrc_cur, hia_cur, hna_cur, hcur_snd,
    hold_half, hbt_all, hcomp, hsh_all, hta_le, htry_all⟩ := hinv.tiers
  rw [ite_eq_left hsub] at hold_half
  obtain ⟨hv_o, hrb_o, hrc_o, hia_o, hna_o, hdp_le, hscan_o, hold_snd⟩ := hold_half
  obtain ⟨hfr', hr', hbp', hbt', htr', hoi', hof', hm2', hfm'⟩ :=
    extractFastMeta_writeMeta (off := 4) (val := fm.subStep + 1) hr₀
      (Or.inl ⟨by decide, by decide⟩)
  generalize hs'_def :
    (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, 4), fm.subStep + 1)) = s'
  rw [hs'_def] at hfr' hr' hbp' hbt' htr' hoi' hof' hm2' hfm'
  rw [ite_eq_right (by decide), ite_eq_left rfl] at hfm'
  have hkey_eq : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
      fastKeyAt fl seeds.bkt s'.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
    fun b' loc' hb' hl' => fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp' hoi' hb' hl'
  have hsub'_lt : fm.subStep + 1 < qEpochWhp fl.N := by
    have ⟨_, hq4⟩ := qEpochWhp_even_and_ge fl.N; omega
  have hbm' : ∀ b' < numBucketsWhp fl.N,
      let fm2 := extractFastMeta fl s'.mem
      fm2.bktSalt b' < sMaxWhp fl.c fl.N ∧ fm2.curRole b' < 3 ∧
      fm2.curIns b' ≤ 8 * slabScale fl.N ^ 12 ∧
      (fm2.shadowCode b' = 0 → ¬(fm2.tryAct = 1 ∧ fm2.tryBkt = b') →
        fm2.curIns b' < 6 * slabScale fl.N ^ 12) := fun b' hb' => by
    dsimp only; rw [hfm']; exact hinv.bkt_meta_bounds b' hb'
  obtain ⟨hc_N, hc_sb, hc_sf, hc_bp, hc_cap, hc_ref⟩ :=
    FastEpochInvGen.fixed_pool_core hv hinv hbp' hoi' hof'
  have hgen : FastEpochInvGen 0 fl slack seeds s'.mem s_abs := by
    refine
      { param_table := hr'.2.1
        hdr_N := hc_N
        mode_zero := hm2'.trans hinv.mode_zero
        seed_bkt := hc_sb
        seed_fp := hc_sf
        bp_inv := hc_bp
        bkt_le_capMax := hc_cap
        refines := hc_ref
        role_lt := by rw [hfm']; exact hinv.role_lt
        subStep_lt := by rw [hfm']; exact hsub'_lt
        bkt_meta_bounds := hbm'
        tiers := ?_ }
    dsimp only
    have hcr' : (extractFastMeta fl s'.mem).curBufRole = fm.curBufRole := by rw [hfm']
    have hss' : (extractFastMeta fl s'.mem).subStep = fm.subStep + 1 := by rw [hfm']
    have hdp' : (extractFastMeta fl s'.mem).drainPos = fm.drainPos := by rw [hfm']
    have hta' : (extractFastMeta fl s'.mem).tryAct = fm.tryAct := by rw [hfm']
    have htb' : (extractFastMeta fl s'.mem).tryBkt = fm.tryBkt := by rw [hfm']
    have hts' : (extractFastMeta fl s'.mem).trySalt = fm.trySalt := by rw [hfm']
    have htp' : (extractFastMeta fl s'.mem).tryPos = fm.tryPos := by rw [hfm']
    have hti' : (extractFastMeta fl s'.mem).tryIns = fm.tryIns := by rw [hfm']
    have hbs' : (extractFastMeta fl s'.mem).bktSalt = fm.bktSalt := by rw [hfm']
    have hrl' : (extractFastMeta fl s'.mem).curRole = fm.curRole := by rw [hfm']
    have hci' : (extractFastMeta fl s'.mem).curIns = fm.curIns := by rw [hfm']
    have hsi' : (extractFastMeta fl s'.mem).shadowIns = fm.shadowIns := by rw [hfm']
    have hsc' : (extractFastMeta fl s'.mem).shadowCode = fm.shadowCode := by rw [hfm']
    have htr_c := htr' fm.curBufRole hinv.role_lt
    have htr_o := htr' (1 - fm.curBufRole) (by have := hinv.role_lt; omega)
    have hmap_old_empty :
        ((extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem).itemAlloc ≤ fm.drainPos) →
        mapOld = (fun _ => none) := fun hia_dp => by
      funext rk
      cases hm : mapOld rk with
      | none => rfl
      | some bl =>
        rcases bl with ⟨b0, l0⟩
        obtain ⟨id, hid_lt, hid_chk⟩ := hv_o.exists_checkSlot_of_map_some hm
        have hnone := hscan_o id (lt_min (lt_of_lt_of_le hid_lt hia_dp) hid_lt)
        rw [hnone] at hid_chk; cases hid_chk
    rcases hbd with hlt | ⟨hia_dp, hta0⟩
    · refine ⟨mapCur, mapOld, mapBTree,
        by rw [hcr', htr_c]; exact hv_cur,
        by rw [hcr', htr_c]; exact hrb_cur,
        by rw [hcr', htr_c]; exact hrc_cur,
        by rw [hcr', htr_c, hss']; simpa only [Nat.add_zero] using hia_cur,
        by rw [hcr', htr_c]; exact hna_cur,
        fun rk b' loc' hm => by
          obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk b' loc' hm
          exact ⟨hb', by rw [hbp']; exact hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩,
        ?_, ?_, ?_, ?_, by rw [hta']; exact hta_le, ?_⟩
      · rw [hss', hcr', htr_o, hdp', hbp', ite_eq_left hlt]
        exact ⟨hv_o, hrb_o, hrc_o, hia_o, hna_o, hdp_le, hscan_o, fun rk b' loc' hm => by
          obtain ⟨hn', hb', hl', u', hrk', hk'⟩ := hold_snd rk b' loc' hm
          exact ⟨hn', hb', hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩⟩
      · intro b' hb'
        rw [hbp']
        refine ⟨?_, fun fp' loc' hm => ?_⟩
        · rw [congrFun hci' b', congrFun hrl' b',
            hbt' b' hb' _ (hinv.bkt_meta_bounds b' hb').2.1]
          exact (hbt_all b' hb').1
        · obtain ⟨hl', u', hfp', hk', hd1, hd2⟩ := (hbt_all b' hb').2 fp' loc' hm
          exact ⟨hl', u',
            (congrArg Fin.val (fpHash_congr_salt (congrFun hbs' b') u')).trans hfp',
            (hkey_eq b' loc' hb' hl').trans hk',
            fun b₁ l₁ hm₁ => by
              obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
              rw [hkey_eq b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁,
            fun b₂ l₂ hm₂ => by
              obtain ⟨_, hb₂, hl₂, _⟩ := hold_snd _ b₂ l₂ hm₂
              rw [hkey_eq b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂⟩
      · intro b' hb' loc' hloc'
        rw [hbp'] at hloc'
        obtain ⟨u', hk', ht'⟩ := hcomp b' hb' loc' hloc'
        refine ⟨u', (hkey_eq b' loc' hb' hloc').trans hk', ?_⟩
        rw [fpHash_congr_salt (congrFun hbs' b') u']; exact ht'
      · intro b' hb' hsc_nz
        rw [congrFun hsc' b'] at hsc_nz ⊢
        rw [hta', htb', congrFun hsi' b', congrFun hci' b', congrFun hrl' b', hbp']
        obtain ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩ := hsh_all b' hb' hsc_nz
        rw [hbt' b' hb' _ (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1]
        exact ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩
      · intro hta1
        rw [hta'] at hta1
        obtain ⟨_, hb_t, hs_t, htp_le, hsc_t, hti_le, tm, hv_tm, ht_s, ht_c⟩ := htry_all hta1
        have hbs_lt := (hinv.bkt_meta_bounds fm.tryBkt hb_t).1
        have hbs_tb : (extractFastMeta fl s'.mem).bktSalt (extractFastMeta fl s'.mem).tryBkt =
            fm.bktSalt fm.tryBkt := by rw [htb', congrFun hbs' fm.tryBkt]
        rw [hss', htp', hti', hbp']
        refine ⟨hlt, htb'.symm ▸ hb_t, hts'.symm ▸ hs_t,
          by rw [htb']; exact htp_le,
          by rw [htb', congrFun hsc' fm.tryBkt]; exact hsc_t,
          by rw [htb']; exact hti_le, tm, ?_, ?_, ?_⟩
        · rw [htb', congrFun hrl' fm.tryBkt,
            hbt' _ hb_t _ (tryRoleOf_lt_and_ne (hinv.bkt_meta_bounds _ hb_t).2.1).1]
          exact hv_tm
        · intro fp' loc' htm'
          obtain ⟨hl', u', hk', hmb', hfp'⟩ := ht_s fp' loc' htm'
          exact ⟨hl', u',
            by rw [htb']; exact (hkey_eq _ loc' hb_t (hl'.trans_le htp_le)).trans hk',
            by rw [mapBTree_fpHash_congr mapBTree (h₂ := hbs_lt) htb' hbs_tb u']; exact hmb',
            (congrArg Fin.val (fpHash_congr_salt hts' u')).trans hfp'⟩
        · intro loc' hl' u' hk' hmb'
          rw [htb'] at hk'
          rw [mapBTree_fpHash_congr mapBTree (h₂ := hbs_lt) htb' hbs_tb u'] at hmb'
          rw [fpHash_congr_salt hts' u']
          exact ht_c loc' hl' u' ((hkey_eq _ loc' hb_t (hl'.trans_le htp_le)).symm.trans hk') hmb'
    · by_cases hlt : fm.subStep + 1 < qEpochWhp fl.N / 2
      · refine ⟨mapCur, mapOld, mapBTree,
          by rw [hcr', htr_c]; exact hv_cur,
          by rw [hcr', htr_c]; exact hrb_cur,
          by rw [hcr', htr_c]; exact hrc_cur,
          by rw [hcr', htr_c, hss']; simpa only [Nat.add_zero] using hia_cur,
          by rw [hcr', htr_c]; exact hna_cur,
          fun rk b' loc' hm => by
            obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk b' loc' hm
            exact ⟨hb', by rw [hbp']; exact hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩,
          ?_, ?_, ?_, ?_, by rw [hta', hta0]; decide,
          fun h01 => absurd (hta'.symm.trans h01) (by rw [hta0]; decide)⟩
        · rw [hss', hcr', htr_o, hdp', hbp', ite_eq_left hlt]
          exact ⟨hv_o, hrb_o, hrc_o, hia_o, hna_o, hdp_le, hscan_o, fun rk b' loc' hm => by
            obtain ⟨hn', hb', hl', u', hrk', hk'⟩ := hold_snd rk b' loc' hm
            exact ⟨hn', hb', hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩⟩
        · intro b' hb'
          rw [hbp']
          refine ⟨?_, fun fp' loc' hm => ?_⟩
          · rw [congrFun hci' b', congrFun hrl' b',
              hbt' b' hb' _ (hinv.bkt_meta_bounds b' hb').2.1]
            exact (hbt_all b' hb').1
          · obtain ⟨hl', u', hfp', hk', hd1, hd2⟩ := (hbt_all b' hb').2 fp' loc' hm
            exact ⟨hl', u',
              (congrArg Fin.val (fpHash_congr_salt (congrFun hbs' b') u')).trans hfp',
              (hkey_eq b' loc' hb' hl').trans hk',
              fun b₁ l₁ hm₁ => by
                obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
                rw [hkey_eq b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁,
              fun b₂ l₂ hm₂ => by
                obtain ⟨_, hb₂, hl₂, _⟩ := hold_snd _ b₂ l₂ hm₂
                rw [hkey_eq b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂⟩
        · intro b' hb' loc' hloc'
          rw [hbp'] at hloc'
          obtain ⟨u', hk', ht'⟩ := hcomp b' hb' loc' hloc'
          refine ⟨u', (hkey_eq b' loc' hb' hloc').trans hk', ?_⟩
          rw [fpHash_congr_salt (congrFun hbs' b') u']; exact ht'
        · intro b' hb' hsc_nz
          rw [congrFun hsc' b'] at hsc_nz ⊢
          rw [hta', htb', congrFun hsi' b', congrFun hci' b', congrFun hrl' b', hbp']
          obtain ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩ := hsh_all b' hb' hsc_nz
          rw [hbt' b' hb' _ (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1]
          exact ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩
      · have hmo_none : mapOld = (fun _ => none) := hmap_old_empty hia_dp
        have heq_half : fm.subStep + 1 = qEpochWhp fl.N / 2 := by omega
        refine ⟨mapCur, (fun _ => none), mapBTree,
          by rw [hcr', htr_c]; exact hv_cur,
          by rw [hcr', htr_c]; exact hrb_cur,
          by rw [hcr', htr_c]; exact hrc_cur,
          by rw [hcr', htr_c, hss']; simpa only [Nat.add_zero] using hia_cur,
          by rw [hcr', htr_c]; exact hna_cur,
          fun rk b' loc' hm => by
            obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk b' loc' hm
            exact ⟨hb', by rw [hbp']; exact hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩,
          ?_, ?_, ?_, ?_, by rw [hta', hta0]; decide,
          fun h01 => absurd (hta'.symm.trans h01) (by rw [hta0]; decide)⟩
        · rw [hss', hcr', htr_o, hta', ite_eq_right hlt, heq_half, Nat.sub_self, Nat.mul_zero,
            Nat.sub_zero]
          refine ⟨rfl, hta0, hv_o.toClearable, hrc_o, hna_o.trans (le_max_right _ _)⟩
        · intro b' hb'
          rw [hbp']
          refine ⟨?_, fun fp' loc' hm => ?_⟩
          · rw [congrFun hci' b', congrFun hrl' b',
              hbt' b' hb' _ (hinv.bkt_meta_bounds b' hb').2.1]
            exact (hbt_all b' hb').1
          · obtain ⟨hl', u', hfp', hk', hd1, _⟩ := (hbt_all b' hb').2 fp' loc' hm
            exact ⟨hl', u',
              (congrArg Fin.val (fpHash_congr_salt (congrFun hbs' b') u')).trans hfp',
              (hkey_eq b' loc' hb' hl').trans hk',
              fun b₁ l₁ hm₁ => by
                obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
                rw [hkey_eq b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁,
              fun _ _ h => (Option.some_ne_none _ h.symm).elim⟩
        · intro b' hb' loc' hloc'
          rw [hbp'] at hloc'
          obtain ⟨u', hk', ht'⟩ := hcomp b' hb' loc' hloc'
          refine ⟨u', (hkey_eq b' loc' hb' hloc').trans hk', ?_⟩
          rw [hmo_none] at ht'
          rcases ht' with h1 | h2 | h3
          · exact Or.inl h1
          · cases h2
          · exact Or.inr (Or.inr (by rw [fpHash_congr_salt (congrFun hbs' b') u']; exact h3))
        · intro b' hb' hsc_nz
          rw [congrFun hsc' b'] at hsc_nz ⊢
          rw [hta', htb', congrFun hsi' b', congrFun hci' b', congrFun hrl' b', hbp']
          obtain ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩ := hsh_all b' hb' hsc_nz
          rw [hbt' b' hb' _ (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1]
          exact ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩
  exact ⟨hfr', hgen.toInv, hbp', htr', hoi', hof', hfm'⟩

/-- Second half of `advanceSubEpochProg` (`Q / 2 ≤ ss`): incremental `BufOld` node clearing and
sub-epoch rollover at `ss + 1 = Q`. Always stays fast (`fallbackMode = 0`). -/
private theorem advanceSubEpochProg_half2 {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen 1 fl slack seeds s.mem s_abs)
    (hsub : ¬(extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2) :
    let s' := (Memory.spec 0).clientState s (advanceSubEpochProg fl.pBase)
    let fm := extractFastMeta fl s.mem
    let fm' := extractFastMeta fl s'.mem
    s'.frontier = s.frontier ∧
    memoryCost (advanceSubEpochProg fl.pBase) s ≤ 96 * (cTabWhp fl.c + 2) + 40 ∧
    FastEpochInv fl slack seeds s'.mem s_abs ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fm.subStep + 1 < qEpochWhp fl.N →
      fm'.curBufRole = fm.curBufRole ∧ fm'.subStep = fm.subStep + 1 ∧ fm'.tryAct = 0) ∧
    (fm.subStep + 1 = qEpochWhp fl.N →
      fm'.curBufRole = 1 - fm.curBufRole ∧ fm'.subStep = 0 ∧
      fm'.drainPos = 0 ∧ fm'.tryAct = 0 ∧
      extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem =
        extractBufTrie (fl.trieL fm.curBufRole) s.mem ∧
      (extractBufTrie (fl.trieL fm'.curBufRole) s'.mem).itemAlloc = 0 ∧
      fm'.shadowCode = fm.shadowCode ∧ fm'.shadowIns = fm.shadowIns ∧
      fm'.curIns = fm.curIns ∧ fm'.curRole = fm.curRole ∧ fm'.bktSalt = fm.bktSalt) := by
  dsimp only
  have hr₀ := hinv.ready hv rfl
  have hpt := hinv.param_table
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  set Q := qEpochWhp fl.N
  set cTab := cTabWhp fl.c
  set kStep := 4 * (cTab + 2)
  have hrole_lt : fm.curBufRole < 2 := hinv.role_lt
  have hold_lt : 1 - fm.curBufRole < 2 := by omega
  have hrole_swap : 1 - (1 - fm.curBufRole) = fm.curBufRole := by omega
  have hss_lt_Q : fm.subStep < Q := hinv.subStep_lt
  obtain ⟨h2dvd, hQ4⟩ := qEpochWhp_even_and_ge fl.N
  have hQ_eq : Q = 2 * (Q / 2) := by
    have : 2 ∣ Q := h2dvd; exact (Nat.mul_div_cancel' this).symm
  obtain ⟨mapCur, mapOld, mapBTree, hv_cur, hrb_cur, hrc_cur, hia_cur, hna_cur, hcur_snd,
    hold_half, hbt_all, hcomp, hsh_all, _, _⟩ := hinv.tiers
  rw [ite_eq_right hsub] at hold_half
  obtain ⟨hmo_none, hta0, hcl_o, hrc_o, hna_o⟩ := hold_half
  have hna_max : (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem).nodeAlloc ≤
      maxTrieNodesWhp fl.c fl.N := by
    have h1 : 1 + cTab * Q ≤ maxTrieNodesWhp fl.c fl.N := by
      have hm : maxTrieNodesWhp fl.c fl.N = (cTab + 1) * Q + 2 := rfl
      have hmul : (cTab + 1) * Q = cTab * Q + Q := by ring
      omega
    exact hna_o.trans (max_le (by unfold maxTrieNodesWhp; omega) ((Nat.sub_le _ _).trans h1))
  obtain ⟨hfr1, hr1, hc1, htr1_old, hcl1, hbp1, hfm1, hm2_1, _, hbt1, htr1_cur, hoi1, hof1⟩ :=
    fastBufClearStepsProg_spec hr₀ hold_lt hcl_o hna_max
  generalize hs1_def :
    (Memory.spec 0).clientState s (fastBufClearStepsProg (fl.pBase, 1 - fm.curBufRole)) = s1
  rw [hs1_def] at hfr1 hr1 htr1_old hcl1 hbp1 hfm1 hm2_1 hbt1 htr1_cur hoi1 hof1
  have htr1_cur' : extractBufTrie (fl.trieL fm.curBufRole) s1.mem =
      extractBufTrie (fl.trieL fm.curBufRole) s.mem := by
    rw [← hrole_swap]; exact htr1_cur
  have hrm4_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 4)) = fm.subStep :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hrm3_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 3)) = fm.curBufRole :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hr23_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 23)) = s := rfl
  have hr23_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 23)) = Q :=
    hpt 23 (by decide)
  have cm4 := memoryCost_fastReadMetaProg (fl.pBase, 4) s
  have cm3 := memoryCost_fastReadMetaProg (fl.pBase, 3) s
  have hsplit_out : ∀ (p : Memory.Prog Unit),
      (Memory.spec 0).clientState s (do
        let ss ← fastReadMetaProg (fl.pBase, 4)
        let qMax ← Memory.read (fl.pBase + 23)
        let halfQ ← pure (qMax / 2)
        if ss < halfQ then pure ()
        else do
          let curR ← fastReadMetaProg (fl.pBase, 3)
          if curR < 2 then do
            let oldR ← pure (1 - curR)
            fastBufClearStepsProg (fl.pBase, oldR)
            p
          else pure ()) = (Memory.spec 0).clientState s1 p := fun p => by
    rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hrm4_r,
      StateTransitionSpec.clientState_bind, hr23_st, hr23_r, pure_bind, ite_eq_right hsub,
      StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hrm3_r,
      ite_eq_left hinv.role_lt, pure_bind, StateTransitionSpec.clientState_bind, hs1_def]
  have _ := hsplit_out
  unfold advanceSubEpochProg
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hrm4_r,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    hr23_st, hr23_r, prog_memoryCost_read, pure_bind, ite_eq_right hsub,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hrm3_r, ite_eq_left hinv.role_lt, pure_bind,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs1_def]
  by_cases hlt_Q : fm.subStep + 1 < Q
  · have hq_cond : 0 < Q ∧ fm.subStep < Q - 1 := by omega
    rw [ite_eq_left hq_cond]
    obtain ⟨hfr2, hr2, hbp2, hbt2, htr2, hoi2, hof2, hm2_2, hfm2⟩ :=
      extractFastMeta_writeMeta (off := 4) (val := fm.subStep + 1) hr1
        (Or.inl ⟨by decide, by decide⟩)
    have cw4 := memoryCost_fastWriteMetaProg ((fl.pBase, 4), fm.subStep + 1) s1
    generalize hs2_def :
      (Memory.spec 0).clientState s1 (fastWriteMetaProg ((fl.pBase, 4), fm.subStep + 1)) = s2
    rw [hs2_def] at hfr2 hr2 hbp2 hbt2 htr2 hoi2 hof2 hm2_2 hfm2
    rw [ite_eq_right (by decide), ite_eq_left rfl, hfm1] at hfm2
    have hbp_tot : extractBlockPool fl.mp s2.mem = bp := hbp2.trans hbp1
    have hoi_tot : ∀ a, fl.io.OwnsAddr a → s2.mem a = s.mem a :=
      fun a ha => (hoi2 a ha).trans (hoi1 a ha)
    have hof_tot : ∀ a, ¬fl.OwnsFastAddr a → s2.mem a = s.mem a :=
      fun a ha => (hof2 a ha).trans (hof1 a ha)
    have hkey_eq : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
        fastKeyAt fl seeds.bkt s2.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
      fun b' loc' hb' hl' => fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp_tot hoi_tot hb' hl'
    obtain ⟨hrc1, hna1_eq⟩ := rawClearableBounds_clearSteps_exact kStep hrc_o
    have hna_s2 : (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s1.mem).nodeAlloc ≤
        max 1 ((1 + cTab * Q) - kStep * (fm.subStep + 1 - Q / 2)) := by
      have hmul : kStep * (fm.subStep + 1 - Q / 2) = kStep * (fm.subStep - Q / 2) + kStep := by
        have hsub1 : fm.subStep + 1 - Q / 2 = (fm.subStep - Q / 2) + 1 := by omega
        rw [hsub1, Nat.mul_add, Nat.mul_one]
      rw [htr1_old, hna1_eq, hmul]
      change max 1 ((extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem).nodeAlloc - kStep) ≤ _
      change (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem).nodeAlloc ≤
        max 1 (1 + cTab * Q - kStep * (fm.subStep - Q / 2)) at hna_o
      omega
    have hbm2 : ∀ b' < numBucketsWhp fl.N,
        let fm2 := extractFastMeta fl s2.mem
        fm2.bktSalt b' < sMaxWhp fl.c fl.N ∧ fm2.curRole b' < 3 ∧
        fm2.curIns b' ≤ 8 * slabScale fl.N ^ 12 ∧
        (fm2.shadowCode b' = 0 → ¬(fm2.tryAct = 1 ∧ fm2.tryBkt = b') →
          fm2.curIns b' < 6 * slabScale fl.N ^ 12) := fun b' hb' => by
      dsimp only; rw [hfm2]; exact hinv.bkt_meta_bounds b' hb'
    obtain ⟨hc_N, hc_sb, hc_sf, hc_bp, hc_cap, hc_ref⟩ :=
      FastEpochInvGen.fixed_pool_core hv hinv hbp_tot hoi_tot hof_tot
    have hgen : FastEpochInvGen 0 fl slack seeds s2.mem s_abs := by
      refine
        { param_table := hr2.2.1
          hdr_N := hc_N
          mode_zero := hm2_2.trans (hm2_1.trans hinv.mode_zero)
          seed_bkt := hc_sb
          seed_fp := hc_sf
          bp_inv := hc_bp
          bkt_le_capMax := hc_cap
          refines := hc_ref
          role_lt := by rw [hfm2]; exact hinv.role_lt
          subStep_lt := by rw [hfm2]; exact hlt_Q
          bkt_meta_bounds := hbm2
          tiers := ?_ }
      dsimp only
      have hcr2 : (extractFastMeta fl s2.mem).curBufRole = fm.curBufRole := by rw [hfm2]
      have hss2 : (extractFastMeta fl s2.mem).subStep = fm.subStep + 1 := by rw [hfm2]
      have hta2 : (extractFastMeta fl s2.mem).tryAct = fm.tryAct := by rw [hfm2]
      have htb2 : (extractFastMeta fl s2.mem).tryBkt = fm.tryBkt := by rw [hfm2]
      have hbs2 : (extractFastMeta fl s2.mem).bktSalt = fm.bktSalt := by rw [hfm2]
      have hrl2 : (extractFastMeta fl s2.mem).curRole = fm.curRole := by rw [hfm2]
      have hci2 : (extractFastMeta fl s2.mem).curIns = fm.curIns := by rw [hfm2]
      have hsi2 : (extractFastMeta fl s2.mem).shadowIns = fm.shadowIns := by rw [hfm2]
      have hsc2 : (extractFastMeta fl s2.mem).shadowCode = fm.shadowCode := by rw [hfm2]
      have htc_eq : extractBufTrie (fl.trieL (extractFastMeta fl s2.mem).curBufRole) s2.mem =
          extractBufTrie (fl.trieL fm.curBufRole) s.mem := by
        rw [hcr2, htr2 fm.curBufRole hinv.role_lt, htr1_cur']
      have hto_eq : extractBufTrie (fl.trieL (1 - (extractFastMeta fl s2.mem).curBufRole)) s2.mem =
          extractBufTrie (fl.trieL (1 - fm.curBufRole)) s1.mem := by
        rw [hcr2, htr2 (1 - fm.curBufRole) hold_lt]
      have hge_half : ¬fm.subStep + 1 < Q / 2 := by omega
      refine ⟨mapCur, fun _ => none, mapBTree,
        by rw [htc_eq]; exact hv_cur,
        by rw [htc_eq]; exact hrb_cur,
        by rw [htc_eq]; exact hrc_cur,
        by rw [htc_eq, hss2]; simpa only [Nat.add_zero] using hia_cur,
        by rw [htc_eq]; exact hna_cur,
        fun rk b' loc' hm => by
          obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk b' loc' hm
          exact ⟨hb', by rw [hbp_tot]; exact hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩,
        ?_, ?_, ?_, ?_, by rw [hta2, hta0]; decide,
        fun h01 => absurd (hta2.symm.trans h01) (by rw [hta0]; decide)⟩
      · rw [hss2, ite_eq_right hge_half, hto_eq, hta2]
        refine ⟨rfl, hta0, hcl1, by rw [htr1_old]; exact hrc1, hna_s2⟩
      · intro b' hb'
        rw [hbp_tot]
        refine ⟨?_, fun fp' loc' hm => ?_⟩
        · rw [congrFun hci2 b', congrFun hrl2 b',
            hbt2 b' hb' _ (hinv.bkt_meta_bounds b' hb').2.1,
            hbt1 b' hb' _ (hinv.bkt_meta_bounds b' hb').2.1]
          exact (hbt_all b' hb').1
        · obtain ⟨hl', u', hfp', hk', hd1, _⟩ := (hbt_all b' hb').2 fp' loc' hm
          exact ⟨hl', u',
            (congrArg Fin.val (fpHash_congr_salt (congrFun hbs2 b') u')).trans hfp',
            (hkey_eq b' loc' hb' hl').trans hk',
            fun b₁ l₁ hm₁ => by
              obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
              rw [hkey_eq b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁,
            fun _ _ h => (Option.some_ne_none _ h.symm).elim⟩
      · intro b' hb' loc' hloc'
        rw [hbp_tot] at hloc'
        obtain ⟨u', hk', ht'⟩ := hcomp b' hb' loc' hloc'
        refine ⟨u', (hkey_eq b' loc' hb' hloc').trans hk', ?_⟩
        rw [hmo_none] at ht'
        rcases ht' with h1 | h2 | h3
        · exact Or.inl h1
        · cases h2
        · exact Or.inr (Or.inr (by rw [fpHash_congr_salt (congrFun hbs2 b') u']; exact h3))
      · intro b' hb' hsc_nz
        rw [congrFun hsc2 b'] at hsc_nz ⊢
        rw [hta2, htb2, congrFun hsi2 b', congrFun hci2 b', congrFun hrl2 b', hbp_tot]
        obtain ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩ := hsh_all b' hb' hsc_nz
        have hsr := (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1
        rw [hbt2 b' hb' _ hsr, hbt1 b' hb' _ hsr]
        exact ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩
    refine ⟨hfr2.trans hfr1, by linarith only [cm4, cm3, hc1, cw4],
      hgen.toInv, hbp_tot, hoi_tot, hof_tot,
      fun _ => ⟨by rw [hfm2], by rw [hfm2], by rw [hfm2]; exact hta0⟩,
      fun heq => by omega⟩
  · -- Rollover branch: `fm.subStep + 1 = Q`
    have hq_not : ¬(0 < Q ∧ fm.subStep < Q - 1) := by omega
    rw [ite_eq_right hq_not]
    have hss_eq : fm.subStep + 1 = Q := by omega
    have hna_le_k : (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem).nodeAlloc ≤ kStep := by
      have h1 : kStep * (fm.subStep - Q / 2) + kStep = 2 * (cTab + 2) * Q := by
        have hsub_eq : (fm.subStep - Q / 2) + 1 = Q / 2 := by omega
        calc kStep * (fm.subStep - Q / 2) + kStep
            = kStep * ((fm.subStep - Q / 2) + 1) := by ring
          _ = 4 * (cTab + 2) * (Q / 2) := by rw [hsub_eq]
          _ = 2 * (cTab + 2) * (2 * (Q / 2)) := by ring
          _ = 2 * (cTab + 2) * Q := by rw [← hQ_eq]
      have h2 : 1 + cTab * Q ≤ 2 * (cTab + 2) * Q := by
        have hle : 2 * (cTab + 2) * Q = 2 * cTab * Q + 4 * Q := by ring
        have hcz : 0 ≤ cTab * Q := Nat.zero_le _
        have hq4' : 4 ≤ Q := hQ4
        linarith only [hle, hcz, hq4']
      have hsub_le : 1 + cTab * Q - kStep * (fm.subStep - Q / 2) ≤ kStep :=
        Nat.sub_le_of_le_add (h2.trans_eq (h1.symm.trans (Nat.add_comm _ _)))
      have hk1 : 1 ≤ kStep := by dsimp only [kStep]; omega
      exact hna_o.trans (max_le hk1 hsub_le)
    obtain ⟨hv_new_cur, hna_new_cur, hia_new_cur⟩ :=
      ClearableBufTrie.clearSteps_spec cTab (bCharWhp fl.N) kStep hcl_o hna_le_k
    obtain ⟨hrb_new_cur, hrc_new_cur⟩ :=
      RawClearableBounds.clearSteps_bounds kStep hrc_o hna_le_k
    obtain ⟨hfr2, hr2, hbp2, hbt2, htr2, hoi2, hof2, hm2_2, hfm2⟩ :=
      extractFastMeta_writeMeta (off := 3) (val := 1 - fm.curBufRole) hr1
        (Or.inl ⟨by decide, by decide⟩)
    have cw3 := memoryCost_fastWriteMetaProg ((fl.pBase, 3), 1 - fm.curBufRole) s1
    generalize hs2_def :
      (Memory.spec 0).clientState s1 (fastWriteMetaProg ((fl.pBase, 3), 1 - fm.curBufRole)) = s2
    rw [hs2_def] at hfr2 hr2 hbp2 hbt2 htr2 hoi2 hof2 hm2_2 hfm2
    obtain ⟨hfr3, hr3, hbp3, hbt3, htr3, hoi3, hof3, hm2_3, hfm3⟩ :=
      extractFastMeta_writeMeta (off := 4) (val := 0) hr2 (Or.inl ⟨by decide, by decide⟩)
    have cw4 := memoryCost_fastWriteMetaProg ((fl.pBase, 4), 0) s2
    generalize hs3_def :
      (Memory.spec 0).clientState s2 (fastWriteMetaProg ((fl.pBase, 4), 0)) = s3
    rw [hs3_def] at hfr3 hr3 hbp3 hbt3 htr3 hoi3 hof3 hm2_3 hfm3
    obtain ⟨hfr4, hr4, hbp4, hbt4, htr4, hoi4, hof4, hm2_4, hfm4⟩ :=
      extractFastMeta_writeMeta (off := 5) (val := 0) hr3 (Or.inl ⟨by decide, by decide⟩)
    have cw5 := memoryCost_fastWriteMetaProg ((fl.pBase, 5), 0) s3
    generalize hs4_def :
      (Memory.spec 0).clientState s3 (fastWriteMetaProg ((fl.pBase, 5), 0)) = s4
    rw [hs4_def] at hfr4 hr4 hbp4 hbt4 htr4 hoi4 hof4 hm2_4 hfm4
    rw [ite_eq_left rfl, hfm1] at hfm2
    rw [ite_eq_right (by decide), ite_eq_left rfl, hfm2] at hfm3
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl, hfm3] at hfm4
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs2_def,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs3_def, hs4_def]
    have hbp_tot : extractBlockPool fl.mp s4.mem = bp := hbp4.trans (hbp3.trans (hbp2.trans hbp1))
    have hoi_tot : ∀ a, fl.io.OwnsAddr a → s4.mem a = s.mem a := fun a ha =>
      (hoi4 a ha).trans ((hoi3 a ha).trans ((hoi2 a ha).trans (hoi1 a ha)))
    have hof_tot : ∀ a, ¬fl.OwnsFastAddr a → s4.mem a = s.mem a := fun a ha =>
      (hof4 a ha).trans ((hof3 a ha).trans ((hof2 a ha).trans (hof1 a ha)))
    have hbt_tot : ∀ b' < numBucketsWhp fl.N, ∀ r < 3,
        extractBTreeSlice fl.btL b' r s4.mem = extractBTreeSlice fl.btL b' r s.mem :=
      fun b' hb' r hr => (hbt4 b' hb' r hr).trans ((hbt3 b' hb' r hr).trans
        ((hbt2 b' hb' r hr).trans (hbt1 b' hb' r hr)))
    have htr_tot : ∀ r < 2,
        extractBufTrie (fl.trieL r) s4.mem = extractBufTrie (fl.trieL r) s1.mem :=
      fun r hr => (htr4 r hr).trans ((htr3 r hr).trans (htr2 r hr))
    have hnew_cur : extractBufTrie (fl.trieL (1 - fm.curBufRole)) s4.mem =
        bufClearSteps kStep (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem) := by
      rw [htr_tot (1 - fm.curBufRole) hold_lt, htr1_old]
    have hnew_old : extractBufTrie (fl.trieL fm.curBufRole) s4.mem =
        extractBufTrie (fl.trieL fm.curBufRole) s.mem := by
      rw [htr_tot fm.curBufRole hinv.role_lt, htr1_cur']
    have hkey_eq : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
        fastKeyAt fl seeds.bkt s4.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
      fun b' loc' hb' hl' => fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp_tot hoi_tot hb' hl'
    have hbm4 : ∀ b' < numBucketsWhp fl.N,
        let fm4 := extractFastMeta fl s4.mem
        fm4.bktSalt b' < sMaxWhp fl.c fl.N ∧ fm4.curRole b' < 3 ∧
        fm4.curIns b' ≤ 8 * slabScale fl.N ^ 12 ∧
        (fm4.shadowCode b' = 0 → ¬(fm4.tryAct = 1 ∧ fm4.tryBkt = b') →
          fm4.curIns b' < 6 * slabScale fl.N ^ 12) := fun b' hb' => by
      dsimp only; rw [hfm4]; exact hinv.bkt_meta_bounds b' hb'
    obtain ⟨hc_N, hc_sb, hc_sf, hc_bp, hc_cap, hc_ref⟩ :=
      FastEpochInvGen.fixed_pool_core hv hinv hbp_tot hoi_tot hof_tot
    have hgen : FastEpochInvGen 0 fl slack seeds s4.mem s_abs := by
      refine
        { param_table := hr4.2.1
          hdr_N := hc_N
          mode_zero := hm2_4.trans (hm2_3.trans (hm2_2.trans (hm2_1.trans hinv.mode_zero)))
          seed_bkt := hc_sb
          seed_fp := hc_sf
          bp_inv := hc_bp
          bkt_le_capMax := hc_cap
          refines := hc_ref
          role_lt := by rw [hfm4]; exact hold_lt
          subStep_lt := by rw [hfm4]; dsimp only; omega
          bkt_meta_bounds := hbm4
          tiers := ?_ }
      dsimp only
      have hcr4 : (extractFastMeta fl s4.mem).curBufRole = 1 - fm.curBufRole := by rw [hfm4]
      have hss4 : (extractFastMeta fl s4.mem).subStep = 0 := by rw [hfm4]
      have hdp4 : (extractFastMeta fl s4.mem).drainPos = 0 := by rw [hfm4]
      have hta4 : (extractFastMeta fl s4.mem).tryAct = fm.tryAct := by rw [hfm4]
      have htb4 : (extractFastMeta fl s4.mem).tryBkt = fm.tryBkt := by rw [hfm4]
      have hbs4 : (extractFastMeta fl s4.mem).bktSalt = fm.bktSalt := by rw [hfm4]
      have hrl4 : (extractFastMeta fl s4.mem).curRole = fm.curRole := by rw [hfm4]
      have hci4 : (extractFastMeta fl s4.mem).curIns = fm.curIns := by rw [hfm4]
      have hsi4 : (extractFastMeta fl s4.mem).shadowIns = fm.shadowIns := by rw [hfm4]
      have hsc4 : (extractFastMeta fl s4.mem).shadowCode = fm.shadowCode := by rw [hfm4]
      have hcur_ia_le : (extractBufTrie (fl.trieL fm.curBufRole) s.mem).itemAlloc ≤ Q := by
        have hq_ss : fm.subStep + 1 = Q := hss_eq
        exact hia_cur.trans (by rw [← hq_ss])
      have hcur_na_le : (extractBufTrie (fl.trieL fm.curBufRole) s.mem).nodeAlloc ≤
          1 + cTab * Q :=
        hna_cur.trans (Nat.add_le_add_left (Nat.mul_le_mul_left cTab hcur_ia_le) 1)
      refine ⟨fun _ => none, mapCur, mapBTree,
        by rw [hcr4, hnew_cur]; exact hv_new_cur,
        by rw [hcr4, hnew_cur]; exact hrb_new_cur,
        by rw [hcr4, hnew_cur]; exact hrc_new_cur,
        by rw [hcr4, hnew_cur, hia_new_cur]; exact Nat.zero_le _,
        by rw [hcr4, hnew_cur, hna_new_cur, hia_new_cur]; omega,
        fun _ _ _ h => (Option.some_ne_none _ h.symm).elim,
        ?_, ?_, ?_, ?_, by rw [hta4, hta0]; decide,
        fun h01 => absurd (hta4.symm.trans h01) (by rw [hta0]; decide)⟩
      · rw [hss4, hcr4, hrole_swap, hnew_old, hdp4, hbp_tot, ite_eq_left (by omega : 0 < Q / 2)]
        refine ⟨hv_cur, hrb_cur, hrc_cur, hcur_ia_le, hcur_na_le, Nat.zero_le _,
          fun id hid => by simp at hid, fun rk b' loc' hm => ?_⟩
        obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk b' loc' hm
        exact ⟨rfl, hb', hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩
      · intro b' hb'
        rw [hbp_tot]
        refine ⟨?_, fun fp' loc' hm => ?_⟩
        · rw [congrFun hci4 b', congrFun hrl4 b',
            hbt_tot b' hb' _ (hinv.bkt_meta_bounds b' hb').2.1]
          exact (hbt_all b' hb').1
        · obtain ⟨hl', u', hfp', hk', hd1, _⟩ := (hbt_all b' hb').2 fp' loc' hm
          exact ⟨hl', u',
            (congrArg Fin.val (fpHash_congr_salt (congrFun hbs4 b') u')).trans hfp',
            (hkey_eq b' loc' hb' hl').trans hk',
            fun _ _ h => (Option.some_ne_none _ h.symm).elim,
            fun b₂ l₂ hm₂ => by
              obtain ⟨hb₂, hl₂, _⟩ := hcur_snd _ b₂ l₂ hm₂
              rw [hkey_eq b₂ l₂ hb₂ hl₂]; exact hd1 b₂ l₂ hm₂⟩
      · intro b' hb' loc' hloc'
        rw [hbp_tot] at hloc'
        obtain ⟨u', hk', ht'⟩ := hcomp b' hb' loc' hloc'
        refine ⟨u', (hkey_eq b' loc' hb' hloc').trans hk', ?_⟩
        rw [hmo_none] at ht'
        rcases ht' with h1 | h2 | h3
        · exact Or.inr (Or.inl h1)
        · cases h2
        · exact Or.inr (Or.inr (by rw [fpHash_congr_salt (congrFun hbs4 b') u']; exact h3))
      · intro b' hb' hsc_nz
        rw [congrFun hsc4 b'] at hsc_nz ⊢
        rw [hta4, htb4, congrFun hsi4 b', congrFun hci4 b', congrFun hrl4 b', hbp_tot]
        obtain ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩ := hsh_all b' hb' hsc_nz
        rw [hbt_tot b' hb' _ (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1]
        exact ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩
    refine ⟨hfr4.trans (hfr3.trans (hfr2.trans hfr1)),
      by linarith only [cm4, cm3, hc1, cw3, cw4, cw5],
      hgen.toInv, hbp_tot, hoi_tot, hof_tot, fun h => absurd h hlt_Q, fun _ => ?_⟩
    exact ⟨by rw [hfm4], by rw [hfm4], by rw [hfm4], by rw [hfm4]; exact hta0,
      by rw [show (extractFastMeta fl s4.mem).curBufRole = 1 - fm.curBufRole by rw [hfm4],
        hrole_swap]; exact hnew_old,
      by rw [show (extractFastMeta fl s4.mem).curBufRole = 1 - fm.curBufRole by rw [hfm4],
        hnew_cur]; exact hia_new_cur,
      by rw [hfm4], by rw [hfm4], by rw [hfm4], by rw [hfm4], by rw [hfm4]⟩

/-- Cost bound for `advanceSubEpochProg` (`O_c(1)` in the fast-path branch). -/
@[expose] def advanceSubEpochCost (c : ℕ) : ℕ :=
  16 * drainTickCost c + 96 * (cTabWhp c + 2) + 80

/-- Unconditional specification of `advanceSubEpochProg` from `FastEpochInvGen 1`: on every seed
in `EpochHashSeeds`, either preserves `FastEpochInv` (`fallbackMode = 0`) in `≤ advanceSubEpochCost`
memory steps, or triggers the in-place `1 · OPT` transition `fastEnterFallbackProg`
(`fallbackMode = 1`, `fl.fbL.StateInv`). Specifically, stays fast whenever:
* `subStep + 1 < Q / 2`,
* `Q / 2 ≤ subStep` (clearing & rollover half), or
* `oldTr_mid.itemAlloc ≤ fm_mid.drainPos ∧ fm_mid.tryAct = 0` right after `drainTicks16Prog`. -/
theorem advanceSubEpochProg_spec {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen 1 fl slack seeds s.mem s_abs) :
    let s' := (Memory.spec 0).clientState s (advanceSubEpochProg fl.pBase)
    let fm := extractFastMeta fl s.mem
    let sMid := (Memory.spec 0).clientState s (drainTicks16Prog fl.pBase)
    let fmMid := extractFastMeta fl sMid.mem
    let oldTrMid := extractBufTrie (fl.trieL (1 - fm.curBufRole)) sMid.mem
    s'.frontier = s.frontier ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    fl.ParamTable s'.mem ∧
    (fl.io.usePaged ≠ 0 →
      extractPageUnperm fl.io.pgL s'.mem = extractPageUnperm fl.io.pgL s.mem ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) ∧
    (if fm.subStep < qEpochWhp fl.N / 2 then
      if fm.subStep + 1 < qEpochWhp fl.N / 2 ∨
          (oldTrMid.itemAlloc ≤ fmMid.drainPos ∧ fmMid.tryAct = 0) then
        memoryCost (advanceSubEpochProg fl.pBase) s ≤ advanceSubEpochCost fl.c ∧
        FastEpochInv fl slack seeds s'.mem s_abs ∧
        extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
        (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
        (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) sMid.mem) ∧
        extractFastMeta fl s'.mem = { fmMid with subStep := fm.subStep + 1 }
      else
        (extractFallback fl.mp s'.mem).nSide = (extractBlockPool fl.mp s.mem).nSide ∧
        fl.fbL.StateInv slack seeds.bkt s'.mem s_abs
    else
      memoryCost (advanceSubEpochProg fl.pBase) s ≤ advanceSubEpochCost fl.c ∧
      FastEpochInv fl slack seeds s'.mem s_abs ∧
      extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
      (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
      (fm.subStep + 1 < qEpochWhp fl.N →
        (extractFastMeta fl s'.mem).curBufRole = fm.curBufRole ∧
        (extractFastMeta fl s'.mem).subStep = fm.subStep + 1 ∧
        (extractFastMeta fl s'.mem).tryAct = 0) ∧
      (fm.subStep + 1 = qEpochWhp fl.N →
        (extractFastMeta fl s'.mem).curBufRole = 1 - fm.curBufRole ∧
        (extractFastMeta fl s'.mem).subStep = 0 ∧
        (extractFastMeta fl s'.mem).drainPos = 0 ∧
        (extractFastMeta fl s'.mem).tryAct = 0 ∧
        extractBufTrie (fl.trieL (1 - (extractFastMeta fl s'.mem).curBufRole)) s'.mem =
          extractBufTrie (fl.trieL fm.curBufRole) s.mem ∧
        (extractBufTrie (fl.trieL (extractFastMeta fl s'.mem).curBufRole) s'.mem).itemAlloc = 0 ∧
        (extractFastMeta fl s'.mem).shadowCode = fm.shadowCode ∧
        (extractFastMeta fl s'.mem).shadowIns = fm.shadowIns ∧
        (extractFastMeta fl s'.mem).curIns = fm.curIns ∧
        (extractFastMeta fl s'.mem).curRole = fm.curRole ∧
        (extractFastMeta fl s'.mem).bktSalt = fm.bktSalt)) := by
  dsimp only
  have hpt := hinv.param_table
  have hw_pos : 0 < fl.io.pgL.w := by
    by_cases hup : fl.io.usePaged = 0
    · have hi := hv.io_valid; unfold SlotIoLayout.Valid at hi; rw [ite_eq_left hup] at hi
      exact hi.2.1 ▸ hv.w_pos
    · have hi := hv.io_valid; unfold SlotIoLayout.Valid at hi; rw [ite_eq_right hup] at hi
      exact hi.2.1 ▸ hv.w_pos
  set fm := extractFastMeta fl s.mem
  set Q := qEpochWhp fl.N
  by_cases hsub : fm.subStep < Q / 2
  · have hrm4_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 4)) = fm.subStep :=
      clientResult_fastReadMetaProg hpt (by decide)
    have hr23_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 23)) = s := rfl
    have hr23_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 23)) = Q :=
      hpt 23 (by decide)
    have cm4 := memoryCost_fastReadMetaProg (fl.pBase, 4) s
    obtain ⟨hfr1, hc1, hinv1, hbp1, _, hoi1, hof1, hcr1, hss1⟩ :=
      drainTicks16Prog_spec hv hinv hsub
    set sMid := (Memory.spec 0).clientState s (drainTicks16Prog fl.pBase)
    set fmMid := extractFastMeta fl sMid.mem
    have hpt1 := hinv1.param_table
    have hsub1 : fmMid.subStep < Q / 2 := hss1.symm ▸ hsub
    have hv1 : fl.Valid w sMid.frontier := hfr1.symm ▸ hv
    have hadv_eq : advanceSubEpochCost fl.c =
        16 * drainTickCost fl.c + 96 * (cTabWhp fl.c + 2) + 80 := rfl
    by_cases hlt1 : fm.subStep + 1 < Q / 2
    · have hst_rw : (Memory.spec 0).clientState s (advanceSubEpochProg fl.pBase) =
          (Memory.spec 0).clientState sMid (fastWriteMetaProg ((fl.pBase, 4), fm.subStep + 1)) ∧
          memoryCost (advanceSubEpochProg fl.pBase) s ≤ advanceSubEpochCost fl.c := by
        have cw4 := memoryCost_fastWriteMetaProg ((fl.pBase, 4), fm.subStep + 1) sMid
        unfold advanceSubEpochProg
        rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadMetaProg, hrm4_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          hr23_st, hr23_r, prog_memoryCost_read, pure_bind, ite_eq_left hsub,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          ite_eq_left hlt1]
        dsimp only [sMid] at cw4
        exact ⟨rfl, by rw [hadv_eq]; omega⟩
      have hss_eq : fm.subStep + 1 = fmMid.subStep + 1 := congrArg (· + 1) hss1.symm
      obtain ⟨hfr2, hinv2, hbp2, htr2, hoi2, hof2, hfm2⟩ :=
        advanceSubEpoch_writeSub_half1 hv1 hinv1 hsub1 (Or.inl (hss_eq ▸ hlt1))
      rw [← hss_eq] at hfr2 hinv2 hbp2 htr2 hoi2 hof2 hfm2
      rw [hst_rw.1, ite_eq_left hsub, ite_eq_left (Or.inl hlt1)]
      have hoi_tot : ∀ a, fl.io.OwnsAddr a →
          ((Memory.spec 0).clientState sMid
            (fastWriteMetaProg ((fl.pBase, 4), fm.subStep + 1))).mem a = s.mem a :=
        fun a ha => (hoi2 a ha).trans (hoi1 a ha)
      refine ⟨hfr2.trans hfr1, fun a ha => (hof2 a ha).trans (hof1 a ha), hinv2.param_table,
        fun hnz => SlotIoLayout.partner_congr_of_outside hw_pos hinv.bp_inv.2.2 hoi_tot hnz,
        hst_rw.2, hinv2, hbp2.trans hbp1, hoi_tot, htr2, hfm2⟩
    · have hcur_r : (Memory.spec 0).clientResult sMid (fastReadMetaProg (fl.pBase, 3)) =
          fmMid.curBufRole := clientResult_fastReadMetaProg hpt1 (by decide)
      have hia_old_lt : 1 - fmMid.curBufRole < 2 := by rw [hcr1]; have := hinv.role_lt; omega
      have hia_spec := fastBufItemAllocProg_spec (role := 1 - fmMid.curBufRole)
        (hinv1.ready hv1 rfl) hia_old_lt
      have hia_r : (Memory.spec 0).clientResult sMid
          (fastBufItemAllocProg (fl.pBase, 1 - fmMid.curBufRole)) =
          (extractBufTrie (fl.trieL (1 - fmMid.curBufRole)) sMid.mem).itemAlloc := hia_spec.1
      have hia_c := hia_spec.2
      have hdp_r : (Memory.spec 0).clientResult sMid (fastReadMetaProg (fl.pBase, 5)) =
          fmMid.drainPos := clientResult_fastReadMetaProg hpt1 (by decide)
      have hta_r : (Memory.spec 0).clientResult sMid (fastReadMetaProg (fl.pBase, 6)) =
          fmMid.tryAct := clientResult_fastReadMetaProg hpt1 (by decide)
      have cm3 := memoryCost_fastReadMetaProg (fl.pBase, 3) sMid
      have cm5 := memoryCost_fastReadMetaProg (fl.pBase, 5) sMid
      have cm6 := memoryCost_fastReadMetaProg (fl.pBase, 6) sMid
      have hcr_old : 1 - fmMid.curBufRole = 1 - fm.curBufRole := by rw [hcr1]
      have hpre_mid : (Memory.spec 0).clientState s (advanceSubEpochProg fl.pBase) =
          (Memory.spec 0).clientState sMid
            (if (extractBufTrie (fl.trieL (1 - fm.curBufRole)) sMid.mem).itemAlloc ≤
                fmMid.drainPos ∧ fmMid.tryAct = 0
              then fastWriteMetaProg ((fl.pBase, 4), fm.subStep + 1)
              else fastEnterFallbackProg fl.pBase) ∧
          memoryCost (advanceSubEpochProg fl.pBase) s ≤
            16 * drainTickCost fl.c + 50 + memoryCost
              (if (extractBufTrie (fl.trieL (1 - fm.curBufRole)) sMid.mem).itemAlloc ≤
                  fmMid.drainPos ∧ fmMid.tryAct = 0
                then fastWriteMetaProg ((fl.pBase, 4), fm.subStep + 1)
                else fastEnterFallbackProg fl.pBase) sMid := by
        unfold advanceSubEpochProg
        rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadMetaProg, hrm4_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          hr23_st, hr23_r, prog_memoryCost_read, pure_bind, ite_eq_left hsub,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          ite_eq_right hlt1,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadMetaProg, hcur_r, ite_eq_left hinv1.role_lt,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastBufItemAllocProg, hia_r, hcr_old,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadMetaProg, hdp_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadMetaProg, hta_r]
        have hia_c' : memoryCost (fastBufItemAllocProg (fl.pBase, 1 - fm.curBufRole)) sMid ≤ 12 :=
          hcr_old ▸ hia_c
        refine ⟨rfl, ?_⟩
        change memoryCost (fastReadMetaProg (fl.pBase, 4)) s +
          (1 + (memoryCost (drainTicks16Prog fl.pBase) s +
            (memoryCost (fastReadMetaProg (fl.pBase, 3)) sMid +
              (memoryCost (fastBufItemAllocProg (fl.pBase, 1 - fm.curBufRole)) sMid +
                (memoryCost (fastReadMetaProg (fl.pBase, 5)) sMid +
                  (memoryCost (fastReadMetaProg (fl.pBase, 6)) sMid +
                    memoryCost (if (extractBufTrie (fl.trieL (1 - fm.curBufRole))
                        sMid.mem).itemAlloc ≤ fmMid.drainPos ∧ fmMid.tryAct = 0
                      then fastWriteMetaProg ((fl.pBase, 4), fm.subStep + 1)
                      else fastEnterFallbackProg fl.pBase) sMid)))))) ≤ _
        linarith only [cm4, hc1, cm3, hia_c', cm5, cm6]
      by_cases hdone : (extractBufTrie (fl.trieL (1 - fm.curBufRole)) sMid.mem).itemAlloc ≤
          fmMid.drainPos ∧ fmMid.tryAct = 0
      · have hss_eq : fm.subStep + 1 = fmMid.subStep + 1 := congrArg (· + 1) hss1.symm
        obtain ⟨hfr2, hinv2, hbp2, htr2, hoi2, hof2, hfm2⟩ :=
          advanceSubEpoch_writeSub_half1 hv1 hinv1 hsub1
            (Or.inr ⟨by rw [hcr_old]; exact hdone.1, hdone.2⟩)
        rw [← hss_eq] at hfr2 hinv2 hbp2 htr2 hoi2 hof2 hfm2
        have cw4 := memoryCost_fastWriteMetaProg ((fl.pBase, 4), fm.subStep + 1) sMid
        have hst_eq := hpre_mid.1; rw [ite_eq_left hdone] at hst_eq
        have hc_eq := hpre_mid.2; rw [ite_eq_left hdone] at hc_eq
        rw [hst_eq, ite_eq_left hsub, ite_eq_left (Or.inr hdone)]
        have hoi_tot : ∀ a, fl.io.OwnsAddr a →
            ((Memory.spec 0).clientState sMid
              (fastWriteMetaProg ((fl.pBase, 4), fm.subStep + 1))).mem a = s.mem a :=
          fun a ha => (hoi2 a ha).trans (hoi1 a ha)
        refine ⟨hfr2.trans hfr1, fun a ha => (hof2 a ha).trans (hof1 a ha), hinv2.param_table,
          fun hnz => SlotIoLayout.partner_congr_of_outside hw_pos hinv.bp_inv.2.2 hoi_tot hnz,
          by rw [hadv_eq]; omega, hinv2, hbp2.trans hbp1, hoi_tot, htr2, hfm2⟩
      · have hnot_cond : ¬(fm.subStep + 1 < Q / 2 ∨
            ((extractBufTrie (fl.trieL (1 - fm.curBufRole)) sMid.mem).itemAlloc ≤
              fmMid.drainPos ∧ fmMid.tryAct = 0)) := fun h => h.elim hlt1 hdone
        have hst_eq := hpre_mid.1; rw [ite_eq_right hdone] at hst_eq
        obtain ⟨hfr2, hpt2, hns2, hfb2, hof2, hpg2⟩ :=
          fastEnterFallbackProg_spec (hinv1.ready hv1 rfl) hinv1.hdr_N hinv1.seed_bkt
            hinv1.bp_inv.1.core hinv1.bp_inv.2.1 hinv1.bp_inv.2.2 hinv1.refines
        rw [hst_eq, ite_eq_left hsub, ite_eq_right hnot_cond]
        refine ⟨hfr2.trans hfr1, fun a ha => (hof2 a ha).trans (hof1 a ha), hpt2,
          fun hnz => ?_, by rw [hns2, hbp1], hfb2⟩
        obtain ⟨hpu1, hps1⟩ := SlotIoLayout.partner_congr_of_outside hw_pos hinv.bp_inv.2.2
          hoi1 hnz
        obtain ⟨hpu2, hps2⟩ := hpg2 hnz
        refine ⟨hpu2.trans hpu1, fun idx hidx => ?_⟩
        have hvl_eq : (extractPagePair fl.io.pgL sMid.mem).virtLen fl.io.partner.side =
            (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side :=
          congrArg (fun u => u.st.virtLen fl.io.partner.side) hpu1
        exact (hps2 idx (hvl_eq.symm ▸ hidx)).trans (hps1 idx hidx)
  · obtain ⟨hfr, hc, hinv', hbp', hoi', hof', hlt', heq'⟩ :=
      advanceSubEpochProg_half2 hv hinv hsub
    rw [ite_eq_right hsub]
    have hadv : 96 * (cTabWhp fl.c + 2) + 40 ≤ advanceSubEpochCost fl.c := by
      unfold advanceSubEpochCost; omega
    exact ⟨hfr, hof', hinv'.param_table,
      fun hnz => SlotIoLayout.partner_congr_of_outside hw_pos hinv.bp_inv.2.2 hoi' hnz,
      hc.trans hadv, hinv', hbp', hoi', hlt', heq'⟩

/-! ## Section 4: Strict Draining Potential (`drainPotential`) & Good-Seed Preservation -/

private theorem mul_cEff_le_slabScale_adv {c N : ℕ} (hth : whpThreshold c ≤ N) :
    16 * (cEff c + 4) ≤ slabScale N := by
  have hm : bMinWhp c ≤ Nat.log 2 N := bMinWhp_le_log hth
  have h1 : Nat.log 2 N ≤ Nat.clog 2 (max N 4) :=
    (Nat.log_mono_right (le_max_left N 4)).trans (Nat.log_le_clog 2 _)
  have hbm : bMinWhp c ≤ slabScale N :=
    hm.trans (h1.trans (Nat.le_pow_clog Nat.one_lt_two _))
  have hce : cEff c + 4 ≤ codeExpWhp c := by
    rw [codeExpWhp_eq]
    unfold cTabWhp
    nlinarith [one_le_cEff c, le_qTabWhp c]
  have h16 : 16 * (cEff c + 4) ≤ bMinWhp c := by rw [bMinWhp_eq]; nlinarith
  exact h16.trans hbm

private theorem sMax_drain_bound {c N : ℕ} (hth : whpThreshold c ≤ N) :
    2 * sMaxWhp c N *
      ((sMaxWhp c N * (capMaxWhp N + 2) + 1) + 4 * slabScale N ^ 12) ≤ qEpochWhp N := by
  set L := slabScale N
  set S := sMaxWhp c N
  have h16 : 16 * (cEff c + 4) ≤ L := mul_cEff_le_slabScale_adv hth
  have hc1 : 1 ≤ cEff c := one_le_cEff c
  have hL80 : 80 ≤ L := by omega
  have hSL : S ≤ L ^ 2 := by
    have hS : S = (cEff c + 4) * L := rfl
    rw [hS, sq]
    exact Nat.mul_le_mul_right L (by omega)
  have hL12_pos : 1 ≤ L ^ 12 := Nat.one_le_pow 12 L (by omega)
  have hcap : capMaxWhp N + 2 ≤ 6 * L ^ 12 := by
    have : capMaxWhp N = 4 * L ^ 12 := rfl; omega
  have hW_try : S * (capMaxWhp N + 2) + 1 ≤ 7 * L ^ 14 := by
    have h1 : S * (capMaxWhp N + 2) ≤ L ^ 2 * (6 * L ^ 12) := Nat.mul_le_mul hSL hcap
    have h2 : L ^ 2 * (6 * L ^ 12) = 6 * L ^ 14 := by ring
    have h3 : 1 ≤ L ^ 14 := Nat.one_le_pow 14 L (by omega)
    omega
  have hW_sh : 4 * L ^ 12 ≤ L ^ 14 := by
    have hmul : L ^ 14 = L ^ 2 * L ^ 12 := by ring
    have hL2 : 4 ≤ L ^ 2 := by nlinarith
    rw [hmul]; exact Nat.mul_le_mul_right (L ^ 12) hL2
  have hsum : (S * (capMaxWhp N + 2) + 1) + 4 * L ^ 12 ≤ 8 * L ^ 14 := by omega
  calc 2 * S * ((S * (capMaxWhp N + 2) + 1) + 4 * L ^ 12)
      ≤ 2 * L ^ 2 * (8 * L ^ 14) := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hSL) hsum
    _ = 16 * L ^ 16 := by ring
    _ ≤ L ^ 2 * L ^ 16 := Nat.mul_le_mul_right _ (by nlinarith)
    _ = qEpochWhp N := by change L ^ 2 * L ^ 16 = L ^ 18; ring

/-- Key `u : Fin fl.U` collides under some salt `s : Fin (sMaxWhp fl.c fl.N)` with a distinct
key `v ∈ win.subUnions e` in the same Feistel bucket. -/
@[expose] def isSubCollidingKey {fl : FastEpochLayout} (win : EpochWindowSpec fl.c fl.U fl.N)
    (e : Fin win.numSubs) (seeds : EpochHashSeeds fl.c fl.U fl.N) (u : Fin fl.U) : Prop :=
  ∃ v ∈ (win.subUnions e).filter
      (fun v' => epochBucket fl.c fl.U fl.N seeds.bkt v' = epochBucket fl.c fl.U fl.N seeds.bkt u),
    u ≠ v ∧ ∃ s : Fin (sMaxWhp fl.c fl.N),
      fpHash fl.c fl.U fl.N seeds.fp s u = fpHash fl.c fl.U fl.N seeds.fp s v

/-- Item slot `id` in `BufOld` is active and holds a key `u` satisfying `isSubCollidingKey`. -/
@[expose] def isBadOldSlot {fl : FastEpochLayout} (win : EpochWindowSpec fl.c fl.U fl.N)
    (e : Fin win.numSubs) (seeds : EpochHashSeeds fl.c fl.U fl.N) (mem : ℕ → ℕ)
    (id : ℕ) : Prop :=
  let fm := extractFastMeta fl mem
  let oldTr := extractBufTrie (fl.trieL (1 - fm.curBufRole)) mem
  ∃ (b loc : ℕ) (u : Fin fl.U),
    bufCheckSlot oldTr id = some (b, loc) ∧
    b < numBucketsWhp fl.N ∧
    loc < (extractBlockPool fl.mp mem).bktCount b ∧
    fastKeyAt fl seeds.bkt mem b loc = u.val ∧
    isSubCollidingKey win e seeds u

/-- Available shadow-compaction slack `shSlack fl mem b ≤ 4 * L ^ 12` for bucket `b`. -/
@[expose] def shSlack (fl : FastEpochLayout) (mem : ℕ → ℕ) (b : ℕ) : ℕ :=
  let fm := extractFastMeta fl mem
  let cnt := (extractBlockPool fl.mp mem).bktCount b
  min (20 * slabScale fl.N ^ 12 - (4 * fm.shadowIns b + 5 * (cnt - (fm.shadowCode b - 1))))
      (4 * slabScale fl.N ^ 12 - (8 * (fm.curIns b - 6 * slabScale fl.N ^ 12) +
        (cnt - (fm.shadowCode b - 1))))

/-- Remaining shadow-compaction work `shCost fl mem b ≤ 4 * L ^ 12` (zero when inactive). -/
@[expose] def shCost (fl : FastEpochLayout) (mem : ℕ → ℕ) (b : ℕ) : ℕ :=
  if (extractFastMeta fl mem).shadowCode b = 0 then 0
  else 4 * slabScale fl.N ^ 12 - shSlack fl mem b

theorem shCost_le (fl : FastEpochLayout) (mem : ℕ → ℕ) (b : ℕ) :
    shCost fl mem b ≤ 4 * slabScale fl.N ^ 12 := by
  unfold shCost; split_ifs <;> omega

/-- Shadow-compaction term at the current `BufOld` scan slot `fm.drainPos`. -/
@[expose] noncomputable def shTerm (fl : FastEpochLayout) (win : EpochWindowSpec fl.c fl.U fl.N)
    (e : Fin win.numSubs) (seeds : EpochHashSeeds fl.c fl.U fl.N) (mem : ℕ → ℕ) : ℕ := by
  classical
  exact
    let fm := extractFastMeta fl mem
    let oldTr := extractBufTrie (fl.trieL (1 - fm.curBufRole)) mem
    if isBadOldSlot win e seeds mem fm.drainPos then
      match bufCheckSlot oldTr fm.drainPos with
      | some (b, _) => shCost fl mem b
      | none => 0
    else 0

theorem shTerm_le (fl : FastEpochLayout) (win : EpochWindowSpec fl.c fl.U fl.N)
    (e : Fin win.numSubs) (seeds : EpochHashSeeds fl.c fl.U fl.N) (mem : ℕ → ℕ) :
    shTerm fl win e seeds mem ≤ 4 * slabScale fl.N ^ 12 := by
  classical
  unfold shTerm
  dsimp only
  split_ifs
  · cases bufCheckSlot (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem)
        (extractFastMeta fl mem).drainPos with
    | none => exact Nat.zero_le _
    | some p => exact shCost_le fl mem p.1
  · exact Nat.zero_le _

/-- Number of active bad slots `id ∈ [k, oldTr.itemAlloc)` in `BufOld`. -/
@[expose] noncomputable def nBadFrom {fl : FastEpochLayout} (win : EpochWindowSpec fl.c fl.U fl.N)
    (e : Fin win.numSubs) (seeds : EpochHashSeeds fl.c fl.U fl.N) (mem : ℕ → ℕ)
    (k : ℕ) : ℕ := by
  classical
  exact
    let fm := extractFastMeta fl mem
    let oldTr := extractBufTrie (fl.trieL (1 - fm.curBufRole)) mem
    ((Finset.range oldTr.itemAlloc).filter fun id => k ≤ id ∧ isBadOldSlot win e seeds mem id).card

/-- Collision-free salt witness chosen from `GoodEpochSeeds` for sub-epoch `e`, bucket `b`. -/
@[expose] noncomputable def goodSaltVal {c U N : ℕ} {win : EpochWindowSpec c U N}
    {seeds : EpochHashSeeds c U N} (hgood : GoodEpochSeeds win seeds)
    (e : Fin win.numSubs) (b : ℕ) : ℕ :=
  if hb : b < numBucketsWhp N then
    (by exact hgood.2.2.1 e b hb :
      ∃ s : Fin (sMaxWhp c N), ∀ u ∈ win.subUnions e, ∀ v ∈ win.subUnions e,
        epochBucket c U N seeds.bkt u = b → epochBucket c U N seeds.bkt v = b → u ≠ v →
          fpHash c U N seeds.fp s u ≠ fpHash c U N seeds.fp s v).choose.val
  else 0

theorem goodSaltVal_spec {c U N : ℕ} {win : EpochWindowSpec c U N}
    {seeds : EpochHashSeeds c U N} (hgood : GoodEpochSeeds win seeds)
    (e : Fin win.numSubs) {b : ℕ} (hb : b < numBucketsWhp N) :
    ∃ (hs : goodSaltVal hgood e b < sMaxWhp c N),
      ∀ u ∈ win.subUnions e, ∀ v ∈ win.subUnions e,
        epochBucket c U N seeds.bkt u = b → epochBucket c U N seeds.bkt v = b → u ≠ v →
          fpHash c U N seeds.fp ⟨goodSaltVal hgood e b, hs⟩ u ≠
            fpHash c U N seeds.fp ⟨goodSaltVal hgood e b, hs⟩ v := by
  unfold goodSaltVal
  rw [dite_eq_left hb]
  exact ⟨(hgood.2.2.1 e b hb).choose.isLt, (hgood.2.2.1 e b hb).choose_spec⟩

/-- Strict `ℕ`-valued draining potential `Φ` for the first half (`subStep < Q / 2`) of sub-epoch
`e` under `GoodEpochSeeds win seeds`. Every `drainTickProg` reduces `Φ` by `≥ 1` when `Φ > 0`;
`Φ = 0 ↔ oldTr.itemAlloc ≤ fm.drainPos ∧ fm.tryAct = 0`. -/
@[expose] noncomputable def drainPotential {fl : FastEpochLayout}
    (win : EpochWindowSpec fl.c fl.U fl.N) (e : Fin win.numSubs)
    (seeds : EpochHashSeeds fl.c fl.U fl.N) (hgood : GoodEpochSeeds win seeds)
    (mem : ℕ → ℕ) : ℕ :=
  let fm := extractFastMeta fl mem
  let bp := extractBlockPool fl.mp mem
  let oldTr := extractBufTrie (fl.trieL (1 - fm.curBufRole)) mem
  let W_try := sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1
  let W_sh := 4 * slabScale fl.N ^ 12
  if fm.tryAct = 1 then
    let b := fm.tryBkt
    let sStar := goodSaltVal hgood e b
    (oldTr.itemAlloc - fm.drainPos) +
      W_try * nBadFrom win e seeds mem (fm.drainPos + 1) +
      W_sh * nBadFrom win e seeds mem (fm.drainPos + 1) +
      ((sStar - fm.trySalt) * (capMaxWhp fl.N + 2) + (bp.bktCount b - fm.tryPos) + 1)
  else
    (oldTr.itemAlloc - fm.drainPos) +
      W_try * nBadFrom win e seeds mem fm.drainPos +
      W_sh * nBadFrom win e seeds mem (fm.drainPos + 1) +
      shTerm fl win e seeds mem

private theorem nBadFrom_zero_of_ge {fl : FastEpochLayout}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ} {k : ℕ}
    (hk : (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem).itemAlloc ≤ k) :
    nBadFrom win e seeds mem k = 0 := by
  classical
  unfold nBadFrom
  refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun id hid => ?_)
  rw [Finset.mem_range] at hid
  omega

private theorem nBadFrom_succ {fl : FastEpochLayout}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ} {k : ℕ}
    (hk : k < (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem).itemAlloc) :
    (isBadOldSlot win e seeds mem k →
      nBadFrom win e seeds mem k = nBadFrom win e seeds mem (k + 1) + 1) ∧
    (¬isBadOldSlot win e seeds mem k →
      nBadFrom win e seeds mem k = nBadFrom win e seeds mem (k + 1)) := by
  classical
  set tr := extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem
  set sK := (Finset.range tr.itemAlloc).filter fun id => k ≤ id ∧ isBadOldSlot win e seeds mem id
  set sK1 := (Finset.range tr.itemAlloc).filter fun id =>
    k + 1 ≤ id ∧ isBadOldSlot win e seeds mem id
  constructor
  · intro hbad
    unfold nBadFrom
    have hnot : k ∉ sK1 := by simp [sK1]
    have heq : sK = insert k sK1 := by
      ext id
      simp only [sK, sK1, Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hlt, hge, hb⟩
        rcases Nat.eq_or_lt_of_le hge with rfl | hgt
        · exact Or.inl rfl
        · exact Or.inr ⟨hlt, hgt, hb⟩
      · rintro (rfl | ⟨hlt, hge, hb⟩)
        · exact ⟨hk, le_rfl, hbad⟩
        · exact ⟨hlt, by omega, hb⟩
    change sK.card = sK1.card + 1
    rw [heq, Finset.card_insert_of_notMem hnot, Nat.add_comm]
  · intro hbad
    unfold nBadFrom
    change sK.card = sK1.card
    congr 1
    ext id
    simp only [sK, sK1, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hlt, hge, hb⟩
      refine ⟨hlt, ?_, hb⟩
      rcases Nat.eq_or_lt_of_le hge with rfl | hgt
      · exact absurd hb hbad
      · exact hgt
    · rintro ⟨hlt, hge, hb⟩; exact ⟨hlt, by omega, hb⟩

theorem nBadFrom_mono_of_imp {fl : FastEpochLayout}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem₁ mem₂ : ℕ → ℕ} {k : ℕ}
    (hia : (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem₂).curBufRole)) mem₂).itemAlloc =
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem₁).curBufRole)) mem₁).itemAlloc)
    (himp : ∀ id, k ≤ id → isBadOldSlot win e seeds mem₂ id → isBadOldSlot win e seeds mem₁ id) :
    nBadFrom win e seeds mem₂ k ≤ nBadFrom win e seeds mem₁ k := by
  classical
  unfold nBadFrom
  dsimp only
  rw [hia]
  refine Finset.card_le_card fun id hid => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hid ⊢
  exact ⟨hid.1, hid.2.1, himp id hid.2.1 hid.2.2⟩

private theorem bufCheckSlot_bufDelete_imp {cTab bChar rk id b loc : ℕ} {tr : BufTrie}
    (h : bufCheckSlot (bufDelete cTab bChar tr rk) id = some (b, loc)) :
    bufCheckSlot tr id = some (b, loc) := by
  unfold bufDelete at h
  cases hwk : bufWalk bChar tr.trieChild rk cTab 0 0 with
  | none => rwa [hwk] at h
  | some leaf =>
    rw [hwk] at h; dsimp only at h
    split_ifs at h with hc
    · exact h
    · unfold bufCheckSlot at h ⊢
      dsimp only at h
      by_cases hid : id < tr.itemAlloc
      · rw [ite_eq_left hid] at h ⊢
        by_cases hcond : tr.nodeLeafItem (tr.itemLeaf id) = id + 1 ∧
            Function.update tr.nodeActive leaf 0 (tr.itemLeaf id) ≠ 0
        · rw [ite_eq_left hcond] at h
          have hne : tr.itemLeaf id ≠ leaf := by
            intro heq; rw [heq, Function.update_self] at hcond; exact hcond.2 rfl
          have hact : tr.nodeActive (tr.itemLeaf id) ≠ 0 := by
            simpa only [Function.update_of_ne hne] using hcond.2
          rwa [ite_eq_left ⟨hcond.1, hact⟩]
        · rw [ite_eq_right hcond] at h; cases h
      · rw [ite_eq_right hid] at h; cases h

private theorem bufDelete_itemAlloc_eq (cTab bChar rk : ℕ) (tr : BufTrie) :
    (bufDelete cTab bChar tr rk).itemAlloc = tr.itemAlloc := by
  unfold bufDelete
  cases bufWalk bChar tr.trieChild rk cTab 0 0 with
  | none => rfl
  | some leaf => dsimp only; split_ifs <;> rfl

theorem drainPotential_eq_zero_iff {fl : FastEpochLayout}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {hgood : GoodEpochSeeds win seeds}
    {mem : ℕ → ℕ} (hle : (extractFastMeta fl mem).tryAct ≤ 1) :
    drainPotential win e seeds hgood mem = 0 ↔
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem).itemAlloc ≤
        (extractFastMeta fl mem).drainPos ∧ (extractFastMeta fl mem).tryAct = 0 := by
  unfold drainPotential
  dsimp only
  by_cases hta : (extractFastMeta fl mem).tryAct = 1
  · rw [ite_eq_left hta]
    constructor
    · intro h; omega
    · rintro ⟨_, h0⟩; omega
  · rw [ite_eq_right hta]
    have hta0 : (extractFastMeta fl mem).tryAct = 0 := by omega
    constructor
    · intro h; exact ⟨by omega, hta0⟩
    · rintro ⟨hia, _⟩
      have hnb1 := nBadFrom_zero_of_ge (win := win) (e := e) (seeds := seeds) hia
      have hnb2 := nBadFrom_zero_of_ge (win := win) (e := e) (seeds := seeds)
        (hia.trans (Nat.le_succ _))
      have hsh0 : shTerm fl win e seeds mem = 0 := by
        classical
        unfold shTerm; dsimp only
        have hnot : ¬isBadOldSlot win e seeds mem (extractFastMeta fl mem).drainPos := by
          rintro ⟨b, loc, u, hchk, _⟩
          unfold bufCheckSlot at hchk
          rw [ite_eq_right (Nat.not_lt.mpr hia)] at hchk; cases hchk
        rw [ite_eq_right hnot]
      rw [Nat.sub_eq_zero_of_le hia, hnb1, hnb2, hsh0]; simp

private theorem nBadFrom_lt_two_mul_sMax {slackCur : ℕ} {fl : FastEpochLayout} {slack : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ}
    {s_abs : Fin fl.U → Option (Fin fl.V)}
    (hinv : FastEpochInvGen slackCur fl slack seeds mem s_abs)
    (hgood : GoodEpochSeeds win seeds)
    (hsub : (extractFastMeta fl mem).subStep < qEpochWhp fl.N / 2)
    (hold_sub : ∀ id b loc (u : Fin fl.U),
      bufCheckSlot (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem) id =
        some (b, loc) →
      b < numBucketsWhp fl.N →
      loc < (extractBlockPool fl.mp mem).bktCount b →
      fastKeyAt fl seeds.bkt mem b loc = u.val →
      u ∈ win.subBatches e) :
    nBadFrom win e seeds mem 0 < 2 * sMaxWhp fl.c fl.N := by
  classical
  set fm := extractFastMeta fl mem
  set oldTr := extractBufTrie (fl.trieL (1 - fm.curBufRole)) mem
  obtain ⟨_, mapOld, _, _, _, _, _, _, _, hold_half, _⟩ := hinv.tiers
  rw [ite_eq_left hsub] at hold_half
  obtain ⟨hv_o, _, _, _, _, _, _, hold_snd⟩ := hold_half
  set dom := (Finset.range oldTr.itemAlloc).filter fun id =>
    0 ≤ id ∧ isBadOldSlot win e seeds mem id
  set cod := (win.subBatches e).filter fun u => isSubCollidingKey win e seeds u
  have hcod_lt : cod.card < 2 * sMaxWhp fl.c fl.N := by
    have h := hgood.2.2.2 e
    convert h using 2
    ext u; simp [cod, isSubCollidingKey]
  change dom.card < 2 * sMaxWhp fl.c fl.N
  rcases dom.eq_empty_or_nonempty with hem | ⟨id0, hid0⟩
  · rw [hem, Finset.card_empty]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hcod_lt
  · have hu0_ex : ∃ u : Fin fl.U, True := by
      simp only [dom, Finset.mem_filter] at hid0
      obtain ⟨_, _, u, _⟩ := hid0.2.2; exact ⟨u, trivial⟩
    obtain ⟨u0, _⟩ := hu0_ex
    have hex : ∀ id ∈ dom, ∃ u ∈ cod,
        ∃ (b loc : ℕ), bufCheckSlot oldTr id = some (b, loc) ∧
          b < numBucketsWhp fl.N ∧ loc < (extractBlockPool fl.mp mem).bktCount b ∧
          fastKeyAt fl seeds.bkt mem b loc = u.val := by
      intro id hid
      simp only [dom, Finset.mem_filter, Finset.mem_range] at hid
      obtain ⟨b, loc, u, hchk, hb, hl, hk, hcol⟩ := hid.2.2
      exact ⟨u, Finset.mem_filter.mpr ⟨hold_sub id b loc u hchk hb hl hk, hcol⟩,
        b, loc, hchk, hb, hl, hk⟩
    have hinj : ∀ id₁ id₂, ∀ (h₁ : id₁ ∈ dom) (h₂ : id₂ ∈ dom),
        (hex id₁ h₁).choose = (hex id₂ h₂).choose → id₁ = id₂ := by
      intro id₁ id₂ h₁ h₂ heq_u
      obtain ⟨_, b₁, loc₁, hchk₁, hb₁, hl₁, hk₁⟩ := (hex id₁ h₁).choose_spec
      obtain ⟨_, b₂, loc₂, hchk₂, hb₂, hl₂, hk₂⟩ := (hex id₂ h₂).choose_spec
      have hu_val : fastKeyAt fl seeds.bkt mem b₁ loc₁ =
          fastKeyAt fl seeds.bkt mem b₂ loc₂ := by
        rw [hk₁, hk₂, heq_u]
      obtain ⟨hid₁_lt, k₁, _, hwk₁, hmk₁⟩ := hv_o.checkSlot_some hchk₁
      obtain ⟨hid₂_lt, k₂, _, hwk₂, hmk₂⟩ := hv_o.checkSlot_some hchk₂
      obtain ⟨_, _, _, u₁', hrk₁, hk₁'⟩ := hold_snd k₁ b₁ loc₁ hmk₁
      obtain ⟨_, _, _, u₂', hrk₂, hk₂'⟩ := hold_snd k₂ b₂ loc₂ hmk₂
      have heq_u' : u₁' = u₂' := Fin.ext (hk₁'.symm.trans (hu_val.trans hk₂'))
      have hk_eq : k₁ = k₂ := by rw [← hrk₁, ← hrk₂, heq_u']
      have hleaf_eq : oldTr.itemLeaf id₁ = oldTr.itemLeaf id₂ := by
        have : some (oldTr.itemLeaf id₁) = some (oldTr.itemLeaf id₂) := by
          rw [← hwk₁, hk_eq, hwk₂]
        exact Option.some.inj this
      have hli₁ : oldTr.nodeLeafItem (oldTr.itemLeaf id₁) = id₁ + 1 := by
        unfold bufCheckSlot at hchk₁; rw [ite_eq_left hid₁_lt] at hchk₁
        by_cases hc : oldTr.nodeLeafItem (oldTr.itemLeaf id₁) = id₁ + 1 ∧
            oldTr.nodeActive (oldTr.itemLeaf id₁) ≠ 0
        · exact hc.1
        · dsimp only at hchk₁; rw [ite_eq_right hc] at hchk₁; cases hchk₁
      have hli₂ : oldTr.nodeLeafItem (oldTr.itemLeaf id₂) = id₂ + 1 := by
        unfold bufCheckSlot at hchk₂; rw [ite_eq_left hid₂_lt] at hchk₂
        by_cases hc : oldTr.nodeLeafItem (oldTr.itemLeaf id₂) = id₂ + 1 ∧
            oldTr.nodeActive (oldTr.itemLeaf id₂) ≠ 0
        · exact hc.1
        · dsimp only at hchk₂; rw [ite_eq_right hc] at hchk₂; cases hchk₂
      have heq1 : id₁ + 1 = id₂ + 1 := by rw [← hli₁, hleaf_eq, hli₂]
      omega
    have hle : dom.card ≤ cod.card := by
      refine Finset.card_le_card_of_injOn
        (fun id => if h : id ∈ dom then (hex id h).choose else u0) ?_ ?_
      · intro id hid
        simp only [Finset.mem_coe] at hid ⊢
        rw [dite_eq_left hid]
        exact (hex id hid).choose_spec.1
      · intro id₁ h₁ id₂ h₂ heq
        simp only [Finset.mem_coe] at h₁ h₂
        simp only [dite_eq_left h₁, dite_eq_left h₂] at heq
        exact hinj id₁ id₂ h₁ h₂ heq
    exact hle.trans_lt hcod_lt

private theorem shCost_fastShadowSteps8_sub {slackCur : ℕ} {fl : FastEpochLayout} {w slack b : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hb : b < numBucketsWhp fl.N)
    (hsc' : (extractFastMeta fl
      ((Memory.spec 0).clientState s (fastShadowSteps8Prog (fl.pBase, b))).mem).shadowCode b ≠ 0) :
    shCost fl ((Memory.spec 0).clientState s (fastShadowSteps8Prog (fl.pBase, b))).mem b + 8 ≤
      shCost fl s.mem b := by
  have hsc0 : (extractFastMeta fl s.mem).shadowCode b ≠ 0 := by
    intro hz
    have hst := fastShadowSteps8Prog_eq_of_shadowZero hinv.param_table hb hz
    rw [hst] at hsc'
    exact hsc' hz
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsh_all, _, _⟩ := hinv.tiers
  obtain ⟨_, _, hle1, hle2, _⟩ := hsh_all b hb hsc0
  set k := shSlack fl s.mem b
  have hk_in : b < numBucketsWhp fl.N → (extractFastMeta fl s.mem).shadowCode b ≠ 0 →
      let fm := extractFastMeta fl s.mem
      let cnt := (extractBlockPool fl.mp s.mem).bktCount b
      4 * fm.shadowIns b + 5 * (cnt - (fm.shadowCode b - 1)) + k ≤ 20 * slabScale fl.N ^ 12 ∧
      8 * (fm.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm.shadowCode b - 1)) + k ≤
        4 * slabScale fl.N ^ 12 := fun _ _ => by
    have hk1 : k ≤ 20 * slabScale fl.N ^ 12 -
        (4 * (extractFastMeta fl s.mem).shadowIns b +
          5 * ((extractBlockPool fl.mp s.mem).bktCount b -
            ((extractFastMeta fl s.mem).shadowCode b - 1))) := min_le_left _ _
    have hk2 : k ≤ 4 * slabScale fl.N ^ 12 -
        (8 * ((extractFastMeta fl s.mem).curIns b - 6 * slabScale fl.N ^ 12) +
          ((extractBlockPool fl.mp s.mem).bktCount b -
            ((extractFastMeta fl s.mem).shadowCode b - 1))) := min_le_right _ _
    exact ⟨by omega, by omega⟩
  obtain ⟨hbp_eq, hsl1, hsl2⟩ :
      extractBlockPool fl.mp ((Memory.spec 0).clientState s
        (fastShadowSteps8Prog (fl.pBase, b))).mem = extractBlockPool fl.mp s.mem ∧
      4 * (extractFastMeta fl ((Memory.spec 0).clientState s
        (fastShadowSteps8Prog (fl.pBase, b))).mem).shadowIns b +
        5 * ((extractBlockPool fl.mp s.mem).bktCount b -
          ((extractFastMeta fl ((Memory.spec 0).clientState s
            (fastShadowSteps8Prog (fl.pBase, b))).mem).shadowCode b - 1)) + (k + 8) ≤
        20 * slabScale fl.N ^ 12 ∧
      8 * ((extractFastMeta fl ((Memory.spec 0).clientState s
        (fastShadowSteps8Prog (fl.pBase, b))).mem).curIns b - 6 * slabScale fl.N ^ 12) +
        ((extractBlockPool fl.mp s.mem).bktCount b -
          ((extractFastMeta fl ((Memory.spec 0).clientState s
            (fastShadowSteps8Prog (fl.pBase, b))).mem).shadowCode b - 1)) + (k + 8) ≤
        4 * slabScale fl.N ^ 12 := by
    have hspec := fastShadowSteps8Prog_spec hv hinv (b := b)
    have hsl := fastShadowSteps8Prog_spec_slack hv hinv (b := b) (k := k) hk_in hb hsc'
    exact ⟨hspec.2.2.2.1, hsl.1, hsl.2⟩
  set s' := (Memory.spec 0).clientState s (fastShadowSteps8Prog (fl.pBase, b))
  have hk_le : k + 8 ≤ shSlack fl s'.mem b := by
    unfold shSlack; rw [hbp_eq]; exact le_min (by omega) (by omega)
  have hsh_le : shSlack fl s'.mem b ≤ 4 * slabScale fl.N ^ 12 :=
    (min_le_right _ _).trans (Nat.sub_le _ _)
  unfold shCost
  rw [ite_eq_right hsc', ite_eq_right hsc0]
  omega

/-- Initial rollover bound: at `subStep = 0`, `drainPos = 0`, `tryAct = 0`, under
`GoodEpochSeeds win seeds`, `drainPotential ≤ 2 * qEpochWhp fl.N`. -/
theorem drainPotential_rollover_le {slackCur : ℕ} {fl : FastEpochLayout} {slack : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ}
    {s_abs : Fin fl.U → Option (Fin fl.V)}
    (hth : whpThreshold fl.c ≤ fl.N)
    (hinv : FastEpochInvGen slackCur fl slack seeds mem s_abs)
    (hgood : GoodEpochSeeds win seeds)
    (hss0 : (extractFastMeta fl mem).subStep = 0)
    (hdp0 : (extractFastMeta fl mem).drainPos = 0)
    (hta0 : (extractFastMeta fl mem).tryAct = 0)
    (hold_sub : ∀ id b loc (u : Fin fl.U),
      bufCheckSlot (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem) id =
        some (b, loc) →
      b < numBucketsWhp fl.N →
      loc < (extractBlockPool fl.mp mem).bktCount b →
      fastKeyAt fl seeds.bkt mem b loc = u.val →
      u ∈ win.subBatches e) :
    drainPotential win e seeds hgood mem ≤ 2 * qEpochWhp fl.N := by
  have hq4 : 4 ≤ qEpochWhp fl.N := (qEpochWhp_even_and_ge fl.N).2
  have hsub_lt : (extractFastMeta fl mem).subStep < qEpochWhp fl.N / 2 := by omega
  obtain ⟨_, _, _, _, _, _, _, _, _, hold_half, _⟩ := hinv.tiers
  rw [ite_eq_left hsub_lt] at hold_half
  obtain ⟨_, _, _, hia_le, _⟩ := hold_half
  have hnb0_lt : nBadFrom win e seeds mem 0 < 2 * sMaxWhp fl.c fl.N :=
    nBadFrom_lt_two_mul_sMax hinv hgood hsub_lt hold_sub
  set W_try := sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1
  set W_sh := 4 * slabScale fl.N ^ 12
  have hbound : 2 * sMaxWhp fl.c fl.N * (W_try + W_sh) ≤ qEpochWhp fl.N := sMax_drain_bound hth
  have hsh_pair : W_sh * nBadFrom win e seeds mem 1 + shTerm fl win e seeds mem ≤
      W_sh * nBadFrom win e seeds mem 0 := by
    by_cases hia_pos : 0 <
        (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem).itemAlloc
    · have hrec := nBadFrom_succ (win := win) (e := e) (seeds := seeds) (mem := mem) (k := 0)
        hia_pos
      by_cases hbad0 : isBadOldSlot win e seeds mem 0
      · have hst_le : shTerm fl win e seeds mem ≤ W_sh := shTerm_le ..
        rw [hrec.1 hbad0, Nat.mul_add, Nat.mul_one]
        exact Nat.add_le_add_left hst_le _
      · have hst0 : shTerm fl win e seeds mem = 0 := by
          classical
          unfold shTerm; dsimp only; rw [hdp0, ite_eq_right hbad0]
        rw [hrec.2 hbad0, hst0, Nat.add_zero]
    · have hia0 : (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole))
          mem).itemAlloc = 0 := by omega
      have hnb1 := nBadFrom_zero_of_ge (win := win) (e := e) (seeds := seeds) (mem := mem)
        (k := 1) (by omega)
      have hst0 : shTerm fl win e seeds mem = 0 := by
        classical
        unfold shTerm; dsimp only; rw [hdp0]
        have hnot : ¬isBadOldSlot win e seeds mem 0 := by
          rintro ⟨b, loc, u, hchk, _⟩
          unfold bufCheckSlot at hchk; rw [hia0, ite_eq_right (Nat.not_lt_zero _)] at hchk
          cases hchk
        rw [ite_eq_right hnot]
      rw [hnb1, hst0]; simp
  unfold drainPotential; dsimp only
  rw [ite_eq_right (by omega : (extractFastMeta fl mem).tryAct ≠ 1), hdp0, Nat.sub_zero,
    Nat.zero_add]
  have hia_le' : (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole))
      mem).itemAlloc ≤ qEpochWhp fl.N := hia_le
  have hmul_le : W_try * nBadFrom win e seeds mem 0 + W_sh * nBadFrom win e seeds mem 0 ≤
      2 * sMaxWhp fl.c fl.N * (W_try + W_sh) := by
    have h1 : W_try * nBadFrom win e seeds mem 0 + W_sh * nBadFrom win e seeds mem 0 =
        nBadFrom win e seeds mem 0 * (W_try + W_sh) := by ring
    rw [h1]
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt hnb0_lt)
  change (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem).itemAlloc +
    W_try * nBadFrom win e seeds mem 0 +
    W_sh * nBadFrom win e seeds mem 1 + shTerm fl win e seeds mem ≤ 2 * qEpochWhp fl.N
  linarith only [hia_le', hsh_pair, hmul_le, hbound]

/-- Good-seed sub-epoch invariant tying `FastEpochInvGen slackCur` to `EpochWindowSpec` sub-epoch
`e` with budget slack `slackPot` on `drainPotential ≤ (2 * Q - 11 * subStep) + slackPot`. -/
structure FastSubEpochGood (slackCur slackPot : ℕ) {fl : FastEpochLayout} (slack : ℕ)
    (win : EpochWindowSpec fl.c fl.U fl.N) (e : Fin win.numSubs)
    (seeds : EpochHashSeeds fl.c fl.U fl.N) (hgood : GoodEpochSeeds win seeds)
    (mem : ℕ → ℕ) (s_abs : Fin fl.U → Option (Fin fl.V)) : Prop where
  inv : FastEpochInvGen slackCur fl slack seeds mem s_abs
  live_sub : ∀ u : Fin fl.U, s_abs u ≠ none → u ∈ win.subUnions e
  old_sub : (extractFastMeta fl mem).subStep < qEpochWhp fl.N / 2 →
    ∀ id b loc (u : Fin fl.U),
      bufCheckSlot (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem) id =
        some (b, loc) →
      b < numBucketsWhp fl.N →
      loc < (extractBlockPool fl.mp mem).bktCount b →
      fastKeyAt fl seeds.bkt mem b loc = u.val →
      u ∈ win.subBatches e
  try_match : (extractFastMeta fl mem).tryAct = 1 →
    (extractFastMeta fl mem).drainPos <
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem).itemAlloc →
    ∀ b' loc',
      bufCheckSlot (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem)
        (extractFastMeta fl mem).drainPos = some (b', loc') →
      b' = (extractFastMeta fl mem).tryBkt
  trySalt_le : (extractFastMeta fl mem).tryAct = 1 →
    (extractFastMeta fl mem).trySalt ≤
      goodSaltVal hgood e (extractFastMeta fl mem).tryBkt
  pot_le : (extractFastMeta fl mem).subStep < qEpochWhp fl.N / 2 →
    drainPotential win e seeds hgood mem ≤
      (2 * qEpochWhp fl.N - 11 * (extractFastMeta fl mem).subStep) + slackPot

private theorem drainOldSlotProg_dp_step_pot {fl : FastEpochLayout}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {hgood : GoodEpochSeeds win seeds}
    {m₁ m₂ : ℕ → ℕ}
    (hcr : (extractFastMeta fl m₂).curBufRole = (extractFastMeta fl m₁).curBufRole)
    (hta₂ : (extractFastMeta fl m₂).tryAct = 0)
    (hdp_lt : (extractFastMeta fl m₁).drainPos <
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl m₁).curBufRole)) m₁).itemAlloc)
    (hdp₂ : (extractFastMeta fl m₂).drainPos = (extractFastMeta fl m₁).drainPos + 1)
    (hia_eq : (extractBufTrie (fl.trieL (1 - (extractFastMeta fl m₂).curBufRole)) m₂).itemAlloc =
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl m₁).curBufRole)) m₁).itemAlloc)
    (hbad_imp : ∀ id, (extractFastMeta fl m₁).drainPos + 1 ≤ id →
      isBadOldSlot win e seeds m₂ id → isBadOldSlot win e seeds m₁ id) :
    drainPotential win e seeds hgood m₂ + 1 ≤
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl m₁).curBufRole)) m₁).itemAlloc -
        (extractFastMeta fl m₁).drainPos +
      (sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1) *
        nBadFrom win e seeds m₁ ((extractFastMeta fl m₁).drainPos + 1) +
      4 * slabScale fl.N ^ 12 *
        nBadFrom win e seeds m₁ ((extractFastMeta fl m₁).drainPos + 1) := by
  have _ := hcr
  set dp := (extractFastMeta fl m₁).drainPos
  set ia := (extractBufTrie (fl.trieL (1 - (extractFastMeta fl m₁).curBufRole)) m₁).itemAlloc
  set W_try := sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1
  set W_sh := 4 * slabScale fl.N ^ 12
  have hnb_mono : nBadFrom win e seeds m₂ (dp + 1) ≤ nBadFrom win e seeds m₁ (dp + 1) :=
    nBadFrom_mono_of_imp hia_eq hbad_imp
  have hsh_pair : W_sh * nBadFrom win e seeds m₂ (dp + 2) + shTerm fl win e seeds m₂ ≤
      W_sh * nBadFrom win e seeds m₂ (dp + 1) := by
    by_cases hlt : dp + 1 < ia
    · have hrec := nBadFrom_succ (win := win) (e := e) (seeds := seeds) (mem := m₂) (k := dp + 1)
        (hia_eq.symm ▸ hlt)
      by_cases hbad : isBadOldSlot win e seeds m₂ (dp + 1)
      · rw [hrec.1 hbad, Nat.mul_add, Nat.mul_one]
        exact Nat.add_le_add_left (shTerm_le fl win e seeds m₂) _
      · have hst0 : shTerm fl win e seeds m₂ = 0 := by
          classical
          unfold shTerm; dsimp only; rw [hdp₂, ite_eq_right hbad]
        rw [hrec.2 hbad, hst0, Nat.add_zero]
    · have hge : (extractBufTrie (fl.trieL (1 - (extractFastMeta fl m₂).curBufRole))
          m₂).itemAlloc ≤ dp + 1 := by omega
      have hnb2 := nBadFrom_zero_of_ge (win := win) (e := e) (seeds := seeds) (mem := m₂)
        (k := dp + 2) (hge.trans (Nat.le_succ _))
      have hst0 : shTerm fl win e seeds m₂ = 0 := by
        classical
        unfold shTerm; dsimp only; rw [hdp₂]
        have hnot : ¬isBadOldSlot win e seeds m₂ (dp + 1) := by
          rintro ⟨b, loc, u, hchk, _⟩
          unfold bufCheckSlot at hchk; rw [ite_eq_right (Nat.not_lt.mpr hge)] at hchk; cases hchk
        rw [ite_eq_right hnot]
      rw [hnb2, hst0]; simp
  unfold drainPotential; dsimp only
  rw [ite_eq_right (by omega : (extractFastMeta fl m₂).tryAct ≠ 1), hdp₂, hia_eq]
  have htry_le : W_try * nBadFrom win e seeds m₂ (dp + 1) ≤
      W_try * nBadFrom win e seeds m₁ (dp + 1) := Nat.mul_le_mul_left W_try hnb_mono
  have hsh_le : W_sh * nBadFrom win e seeds m₂ (dp + 1) ≤
      W_sh * nBadFrom win e seeds m₁ (dp + 1) := Nat.mul_le_mul_left W_sh hnb_mono
  have hia_drop : (ia - (dp + 1)) + 1 = ia - dp := by omega
  change (ia - (dp + 1)) + W_try * nBadFrom win e seeds m₂ (dp + 1) +
    W_sh * nBadFrom win e seeds m₂ (dp + 2) + shTerm fl win e seeds m₂ + 1 ≤
    ia - dp + W_try * nBadFrom win e seeds m₁ (dp + 1) +
    W_sh * nBadFrom win e seeds m₁ (dp + 1)
  linarith only [hia_drop, htry_le, hsh_pair, hsh_le]

private theorem isBadOldSlot_fixed_pool {fl : FastEpochLayout} {w slack slackCur : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s s' : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hbp : extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem)
    (hoi : ∀ a, fl.io.OwnsAddr a → s'.mem a = s.mem a)
    (hcr : (extractFastMeta fl s'.mem).curBufRole = (extractFastMeta fl s.mem).curBufRole)
    (hchk_imp : ∀ id b loc,
      bufCheckSlot (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s'.mem)
        id = some (b, loc) →
      bufCheckSlot (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem)
        id = some (b, loc))
    (id : ℕ) :
    isBadOldSlot win e seeds s'.mem id → isBadOldSlot win e seeds s.mem id := by
  rintro ⟨b, loc, u, hchk, hb, hl, hk, hcol⟩
  rw [hcr] at hchk
  rw [hbp] at hl
  have hkey : fastKeyAt fl seeds.bkt s'.mem b loc = fastKeyAt fl seeds.bkt s.mem b loc :=
    fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp hoi hb hl
  exact ⟨b, loc, u, hchk_imp id b loc hchk, hb, hl, hkey.symm.trans hk, hcol⟩

private theorem drainOldSlotProg_step_good {slackCur : ℕ} {fl : FastEpochLayout} {w slack : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {hgood : GoodEpochSeeds win seeds}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hsub : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2)
    (hta0 : (extractFastMeta fl s.mem).tryAct = 0)
    (hlive : ∀ u : Fin fl.U, s_abs u ≠ none → u ∈ win.subUnions e)
    (hold_sub : ∀ id b loc (u : Fin fl.U),
      bufCheckSlot (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem)
        id = some (b, loc) →
      b < numBucketsWhp fl.N →
      loc < (extractBlockPool fl.mp s.mem).bktCount b →
      fastKeyAt fl seeds.bkt s.mem b loc = u.val →
      u ∈ win.subBatches e) :
    let s' := (Memory.spec 0).clientState s (drainOldSlotProg fl.pBase)
    let fm' := extractFastMeta fl s'.mem
    (∀ id b loc (u : Fin fl.U),
      bufCheckSlot (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem) id = some (b, loc) →
      b < numBucketsWhp fl.N →
      loc < (extractBlockPool fl.mp s'.mem).bktCount b →
      fastKeyAt fl seeds.bkt s'.mem b loc = u.val →
      u ∈ win.subBatches e) ∧
    (fm'.tryAct = 1 → fm'.drainPos <
        (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem).itemAlloc →
      ∀ b' loc', bufCheckSlot (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem)
        fm'.drainPos = some (b', loc') → b' = fm'.tryBkt) ∧
    (fm'.tryAct = 1 → fm'.trySalt ≤ goodSaltVal hgood e fm'.tryBkt) ∧
    drainPotential win e seeds hgood s'.mem ≤ drainPotential win e seeds hgood s.mem - 1 := by
  dsimp only
  set fm := extractFastMeta fl s.mem
  set oldRole := 1 - fm.curBufRole
  set oldTr := extractBufTrie (fl.trieL oldRole) s.mem
  set s' := (Memory.spec 0).clientState s (drainOldSlotProg fl.pBase)
  set fm' := extractFastMeta fl s'.mem
  obtain ⟨_, _, hinv', hbp', _, hoi', _, hcr', _, _, hnoop, hact⟩ :=
    drainOldSlotProg_spec hv hinv hsub hta0
  by_cases hdp_lt : fm.drainPos < oldTr.itemAlloc
  · have hchk_sub : ∀ (himp : ∀ id b loc,
        bufCheckSlot (extractBufTrie (fl.trieL oldRole) s'.mem) id = some (b, loc) →
          bufCheckSlot oldTr id = some (b, loc)),
        ∀ id b loc (u : Fin fl.U),
          bufCheckSlot (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem) id =
            some (b, loc) →
          b < numBucketsWhp fl.N →
          loc < (extractBlockPool fl.mp s'.mem).bktCount b →
          fastKeyAt fl seeds.bkt s'.mem b loc = u.val →
          u ∈ win.subBatches e := fun himp id b loc u hchk hb hl hk => by
      rw [hcr'] at hchk
      rw [hbp'] at hl
      have hkey : fastKeyAt fl seeds.bkt s'.mem b loc = fastKeyAt fl seeds.bkt s.mem b loc :=
        fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp' hoi' hb hl
      exact hold_sub id b loc u (himp id b loc hchk) hb hl (hkey.symm.trans hk)
    rcases hact hdp_lt with ⟨_, hdp', hta', htr', _⟩ |
        ⟨b, loc, u, _, _, _, _, hdp', hta', htr', _⟩ |
        ⟨b, loc, hb, u, v, hchk, hk_u, huv, _, hsv, hbu, hbv, hfp, hs'_eq, hsc', hta', hdp', htr',
          _⟩ |
        ⟨b, loc, hb, u, v, hchk, hk_u, huv, _, hsv, hbu, hbv, hfp, hta', htb', hts', htp', _,
          hdp', _, htr', _⟩
    · -- Case 1: inactive slot `none`
      have hold_ok := hchk_sub (fun _ _ _ h => by rw [htr'] at h; exact h)
      have hnb_mono_rec : nBadFrom win e seeds s.mem (fm.drainPos + 1) ≤
          nBadFrom win e seeds s.mem fm.drainPos := by
        by_cases hb : isBadOldSlot win e seeds s.mem fm.drainPos
        · rw [(nBadFrom_succ hdp_lt).1 hb]; exact Nat.le_succ _
        · rw [(nBadFrom_succ hdp_lt).2 hb]
      have hstep := drainOldSlotProg_dp_step_pot (win := win) (e := e) (seeds := seeds)
        (hgood := hgood) hcr' hta' hdp_lt hdp'
        (by rw [hcr', htr'])
        (fun id _ => isBadOldSlot_fixed_pool hv hinv hbp' hoi' hcr'
          (fun _ _ _ h => by rw [htr'] at h; exact h) id)
      have hpot_old : (oldTr.itemAlloc - fm.drainPos) +
          (sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1) *
            nBadFrom win e seeds s.mem (fm.drainPos + 1) +
          4 * slabScale fl.N ^ 12 * nBadFrom win e seeds s.mem (fm.drainPos + 1) ≤
          drainPotential win e seeds hgood s.mem := by
        unfold drainPotential; dsimp only
        rw [ite_eq_right (by omega : fm.tryAct ≠ 1)]
        have hm := Nat.mul_le_mul_left (sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1) hnb_mono_rec
        linarith only [hm, Nat.zero_le (shTerm fl win e seeds s.mem)]
      refine ⟨hold_ok, fun h1 => absurd (hta'.symm.trans h1) Nat.zero_ne_one,
        fun h1 => absurd (hta'.symm.trans h1) Nat.zero_ne_one,
        Nat.le_sub_of_add_le (hstep.trans hpot_old)⟩
    · -- Case 2: active non-colliding slot drained cleanly (`bufDelete`)
      have himp : ∀ id b' loc',
          bufCheckSlot (extractBufTrie (fl.trieL oldRole) s'.mem) id = some (b', loc') →
            bufCheckSlot oldTr id = some (b', loc') := fun id b' loc' h => by
        rw [htr'] at h; exact bufCheckSlot_bufDelete_imp h
      have hia_eq : (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem).itemAlloc =
          oldTr.itemAlloc := by
        rw [hcr', htr', bufDelete_itemAlloc_eq]
      have hnb_mono_rec : nBadFrom win e seeds s.mem (fm.drainPos + 1) ≤
          nBadFrom win e seeds s.mem fm.drainPos := by
        by_cases hb : isBadOldSlot win e seeds s.mem fm.drainPos
        · rw [(nBadFrom_succ hdp_lt).1 hb]; exact Nat.le_succ _
        · rw [(nBadFrom_succ hdp_lt).2 hb]
      have hstep := drainOldSlotProg_dp_step_pot (win := win) (e := e) (seeds := seeds)
        (hgood := hgood) hcr' hta' hdp_lt hdp' hia_eq
        (fun id _ => isBadOldSlot_fixed_pool hv hinv hbp' hoi' hcr' himp id)
      have hpot_old : (oldTr.itemAlloc - fm.drainPos) +
          (sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1) *
            nBadFrom win e seeds s.mem (fm.drainPos + 1) +
          4 * slabScale fl.N ^ 12 * nBadFrom win e seeds s.mem (fm.drainPos + 1) ≤
          drainPotential win e seeds hgood s.mem := by
        unfold drainPotential; dsimp only
        rw [ite_eq_right (by omega : fm.tryAct ≠ 1)]
        have hm := Nat.mul_le_mul_left (sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1) hnb_mono_rec
        linarith only [hm, Nat.zero_le (shTerm fl win e seeds s.mem)]
      refine ⟨hchk_sub himp, fun h1 => absurd (hta'.symm.trans h1) Nat.zero_ne_one,
        fun h1 => absurd (hta'.symm.trans h1) Nat.zero_ne_one,
        Nat.le_sub_of_add_le (hstep.trans hpot_old)⟩
    · -- Case 3: colliding slot stalled on `shadowCode b ≠ 0` after `fastShadowSteps8Prog`
      have hcol : isSubCollidingKey win e seeds u :=
        ⟨v, Finset.mem_filter.mpr ⟨hlive v hsv, hbv.trans hbu.symm⟩, huv,
          ⟨fm.bktSalt b, (hinv.bkt_meta_bounds b hb).1⟩, hfp⟩
      have hl_lt : loc < (extractBlockPool fl.mp s.mem).bktCount b := by
        obtain ⟨_, mapOld, _, _, _, _, _, _, _, hold_half, _⟩ := hinv.tiers
        rw [ite_eq_left hsub] at hold_half
        obtain ⟨hv_o, _, _, _, _, _, _, hold_snd⟩ := hold_half
        obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
        exact (hold_snd k b loc hmk).2.2.1
      have hbad_s : isBadOldSlot win e seeds s.mem fm.drainPos :=
        ⟨b, loc, u, hchk, hb, hl_lt, hk_u, hcol⟩
      have hbad_s' : isBadOldSlot win e seeds s'.mem fm.drainPos := by
        have hkey : fastKeyAt fl seeds.bkt s'.mem b loc = fastKeyAt fl seeds.bkt s.mem b loc :=
        fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp' hoi' hb hl_lt
        exact ⟨b, loc, u, by rw [hcr', htr']; exact hchk, hb, hbp' ▸ hl_lt,
          hkey.trans hk_u, hcol⟩
      have hnb_eq : ∀ k, nBadFrom win e seeds s'.mem k = nBadFrom win e seeds s.mem k := fun k => by
        refine le_antisymm
          (nBadFrom_mono_of_imp (by rw [hcr', htr'])
            fun id _ => isBadOldSlot_fixed_pool hv hinv hbp' hoi' hcr'
              (fun _ _ _ h => htr' ▸ h) id)
          (nBadFrom_mono_of_imp (by rw [hcr', htr']) fun id _ h => ?_)
        obtain ⟨b0, l0, u0, hc0, hb0, hl0, hk0, hcol0⟩ := h
        have hkey0 : fastKeyAt fl seeds.bkt s'.mem b0 l0 = fastKeyAt fl seeds.bkt s.mem b0 l0 :=
          fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp' hoi' hb0 hl0
        exact ⟨b0, l0, u0, by rw [hcr', htr']; exact hc0, hb0, hbp' ▸ hl0,
          hkey0.trans hk0, hcol0⟩
      have hsh_drop : shCost fl s'.mem b + 8 ≤ shCost fl s.mem b := by
        have h := shCost_fastShadowSteps8_sub hv hinv hb (hs'_eq ▸ hsc')
        rwa [← hs'_eq] at h
      have hst_s : shTerm fl win e seeds s.mem = shCost fl s.mem b := by
        classical
        unfold shTerm; dsimp only; rw [ite_eq_left hbad_s, hchk]
      have hst_s' : shTerm fl win e seeds s'.mem = shCost fl s'.mem b := by
        classical
        unfold shTerm; dsimp only; rw [hdp', ite_eq_left hbad_s', hcr', htr', hchk]
      refine ⟨hchk_sub (fun _ _ _ h => by rw [htr'] at h; exact h),
        fun h1 => absurd (hta'.symm.trans h1) Nat.zero_ne_one,
        fun h1 => absurd (hta'.symm.trans h1) Nat.zero_ne_one, ?_⟩
      unfold drainPotential; dsimp only
      have hne' : fm'.tryAct ≠ 1 := by rw [hta']; exact Nat.zero_ne_one
      have hne0 : fm.tryAct ≠ 1 := by rw [hta0]; exact Nat.zero_ne_one
      rw [ite_eq_right hne', ite_eq_right hne0,
        hcr', htr', hdp', hnb_eq fm.drainPos, hnb_eq (fm.drainPos + 1), hst_s, hst_s']
      apply Nat.le_sub_of_add_le
      linarith only [hsh_drop]
    · -- Case 4: colliding slot started salt search (`tryAct := 1, tryBkt := b, trySalt := 0`)
      have hcol : isSubCollidingKey win e seeds u :=
        ⟨v, Finset.mem_filter.mpr ⟨hlive v hsv, hbv.trans hbu.symm⟩, huv,
          ⟨fm.bktSalt b, (hinv.bkt_meta_bounds b hb).1⟩, hfp⟩
      have hl_lt : loc < (extractBlockPool fl.mp s.mem).bktCount b := by
        obtain ⟨_, mapOld, _, _, _, _, _, _, _, hold_half, _⟩ := hinv.tiers
        rw [ite_eq_left hsub] at hold_half
        obtain ⟨hv_o, _, _, _, _, _, _, hold_snd⟩ := hold_half
        obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
        exact (hold_snd k b loc hmk).2.2.1
      have hbad_s : isBadOldSlot win e seeds s.mem fm.drainPos :=
        ⟨b, loc, u, hchk, hb, hl_lt, hk_u, hcol⟩
      have hrec : nBadFrom win e seeds s.mem fm.drainPos =
          nBadFrom win e seeds s.mem (fm.drainPos + 1) + 1 :=
        (nBadFrom_succ (win := win) (e := e) (seeds := seeds) (mem := s.mem) hdp_lt).1 hbad_s
      have hnb_le : nBadFrom win e seeds s'.mem (fm.drainPos + 1) ≤
          nBadFrom win e seeds s.mem (fm.drainPos + 1) :=
        nBadFrom_mono_of_imp (by rw [hcr', htr'])
          fun id _ => isBadOldSlot_fixed_pool hv hinv hbp' hoi' hcr'
            (fun _ _ _ h => htr' ▸ h) id
      obtain ⟨hs_star, _⟩ := goodSaltVal_spec hgood e hb
      have hcnt_le : (extractBlockPool fl.mp s.mem).bktCount b ≤ capMaxWhp fl.N :=
        hinv.bkt_le_capMax b hb
      have htry_lt : goodSaltVal hgood e b * (capMaxWhp fl.N + 2) +
          (extractBlockPool fl.mp s.mem).bktCount b + 1 + 1 ≤
          sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1 := by
        have h1 : goodSaltVal hgood e b + 1 ≤ sMaxWhp fl.c fl.N := hs_star
        have h2 : (goodSaltVal hgood e b + 1) * (capMaxWhp fl.N + 2) ≤
            sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) := Nat.mul_le_mul_right _ h1
        have h3 : (goodSaltVal hgood e b + 1) * (capMaxWhp fl.N + 2) =
            goodSaltVal hgood e b * (capMaxWhp fl.N + 2) + capMaxWhp fl.N + 2 := by ring
        omega
      refine ⟨hchk_sub (fun _ _ _ h => by rw [htr'] at h; exact h), fun _ _ b' loc' hc => ?_,
        fun _ => by rw [hts']; exact Nat.zero_le _, ?_⟩
      · rw [hcr', htr', hdp', hchk] at hc
        cases hc; exact htb'.symm
      · set W_try := sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1
        set W_sh := 4 * slabScale fl.N ^ 12
        unfold drainPotential; dsimp only
        have hne0 : fm.tryAct ≠ 1 := by rw [hta0]; exact Nat.zero_ne_one
        rw [ite_eq_left hta', ite_eq_right hne0,
          hcr', htr', hdp', htb', hts', htp', hbp', Nat.sub_zero, Nat.sub_zero, hrec]
        have h1 : W_try * nBadFrom win e seeds s'.mem (fm.drainPos + 1) ≤
            W_try * nBadFrom win e seeds s.mem (fm.drainPos + 1) :=
          Nat.mul_le_mul_left W_try hnb_le
        have h2 : W_sh * nBadFrom win e seeds s'.mem (fm.drainPos + 1) ≤
            W_sh * nBadFrom win e seeds s.mem (fm.drainPos + 1) :=
          Nat.mul_le_mul_left W_sh hnb_le
        have hmul : W_try * (nBadFrom win e seeds s.mem (fm.drainPos + 1) + 1) =
            W_try * nBadFrom win e seeds s.mem (fm.drainPos + 1) + W_try := by ring
        have hs0 : 0 ≤ shTerm fl win e seeds s.mem := Nat.zero_le _
        have hW_eq : W_try = sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1 := rfl
        apply Nat.le_sub_of_add_le
        change (oldTr.itemAlloc - fm.drainPos) +
          W_try * nBadFrom win e seeds s'.mem (fm.drainPos + 1) +
          W_sh * nBadFrom win e seeds s'.mem (fm.drainPos + 1) +
          (goodSaltVal hgood e b * (capMaxWhp fl.N + 2) +
            (extractBlockPool fl.mp s.mem).bktCount b + 1) + 1 ≤
          (oldTr.itemAlloc - fm.drainPos) +
          W_try * (nBadFrom win e seeds s.mem (fm.drainPos + 1) + 1) +
          W_sh * nBadFrom win e seeds s.mem (fm.drainPos + 1) +
          shTerm fl win e seeds s.mem
        linarith only [h1, h2, hmul, hs0, htry_lt, hW_eq]
  · have hst : s' = s := hnoop (Nat.le_of_not_lt hdp_lt)
    have hpot0 : drainPotential win e seeds hgood s.mem = 0 :=
      (drainPotential_eq_zero_iff (by rw [hta0]; exact Nat.zero_le 1)).mpr
        ⟨Nat.le_of_not_lt hdp_lt, hta0⟩
    refine ⟨fun id b loc u hchk hb hl hk => by
        rw [hcr'] at hchk
        change bufCheckSlot (extractBufTrie (fl.trieL oldRole) s'.mem) id = some (b, loc) at hchk
        change loc < (extractBlockPool fl.mp s'.mem).bktCount b at hl
        change fastKeyAt fl seeds.bkt s'.mem b loc = u.val at hk
        rw [hst] at hchk hl hk
        exact hold_sub id b loc u hchk hb hl hk,
      fun h1 => absurd (hta0.symm.trans (by dsimp only [fm'] at h1; rwa [hst] at h1))
        Nat.zero_ne_one,
      fun h1 => absurd (hta0.symm.trans (by dsimp only [fm'] at h1; rwa [hst] at h1))
        Nat.zero_ne_one,
      by rw [hst, hpot0]⟩

private theorem drainTryStep_commit_good {slackCur : ℕ} {fl : FastEpochLayout} {w slack : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {hgood : GoodEpochSeeds win seeds}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hta1 : (extractFastMeta fl s.mem).tryAct = 1)
    (hlive : ∀ u : Fin fl.U, s_abs u ≠ none → u ∈ win.subUnions e)
    (hold_sub : ∀ id b loc (u : Fin fl.U),
      bufCheckSlot (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem)
        id = some (b, loc) →
      b < numBucketsWhp fl.N →
      loc < (extractBlockPool fl.mp s.mem).bktCount b →
      fastKeyAt fl seeds.bkt s.mem b loc = u.val →
      u ∈ win.subBatches e)
    (hmatch : (extractFastMeta fl s.mem).drainPos <
        (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem).itemAlloc →
      ∀ b' loc', bufCheckSlot
          (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem)
          (extractFastMeta fl s.mem).drainPos = some (b', loc') →
        b' = (extractFastMeta fl s.mem).tryBkt)
    (hsalt_le : (extractFastMeta fl s.mem).trySalt ≤
      goodSaltVal hgood e (extractFastMeta fl s.mem).tryBkt) :
    let s1 := (Memory.spec 0).clientState s (drainTryStepProg fl.pBase)
    let s' := if (extractFastMeta fl s1.mem).tryAct = 0 then
        (Memory.spec 0).clientState s1 (drainOldSlotProg fl.pBase)
      else s1
    let fm' := extractFastMeta fl s'.mem
    (∀ id b loc (u : Fin fl.U),
      bufCheckSlot (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem) id = some (b, loc) →
      b < numBucketsWhp fl.N →
      loc < (extractBlockPool fl.mp s'.mem).bktCount b →
      fastKeyAt fl seeds.bkt s'.mem b loc = u.val →
      u ∈ win.subBatches e) ∧
    (fm'.tryAct = 1 → fm'.drainPos <
        (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem).itemAlloc →
      ∀ b' loc', bufCheckSlot (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem)
        fm'.drainPos = some (b', loc') → b' = fm'.tryBkt) ∧
    (fm'.tryAct = 1 → fm'.trySalt ≤ goodSaltVal hgood e fm'.tryBkt) ∧
    drainPotential win e seeds hgood s'.mem + 1 ≤ drainPotential win e seeds hgood s.mem := by
  dsimp only
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  set oldRole := 1 - fm.curBufRole
  have hold_lt : oldRole < 2 := by have := hinv.role_lt; omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, htry⟩ := hinv.tiers
  obtain ⟨hsub, hb_t, hs_t, htp_le, hsc_t, hti_le_m, tm, hv_tm, _, _⟩ := htry hta1
  have hcnt_le : bp.bktCount fm.tryBkt ≤ capMaxWhp fl.N := hinv.bkt_le_capMax _ hb_t
  obtain ⟨hfr1, _, hinv1, hbp1, htr1, hoi1, _, hcr1, hss1, hdp1, hsc1, _, _, hcases⟩ :=
    drainTryStepProg_spec hv hinv
  set s1 := (Memory.spec 0).clientState s (drainTryStepProg fl.pBase)
  set fm1 := extractFastMeta fl s1.mem
  have htr1_o : extractBufTrie (fl.trieL oldRole) s1.mem =
      extractBufTrie (fl.trieL oldRole) s.mem := htr1 oldRole hold_lt
  have hnb1_eq : ∀ k, nBadFrom win e seeds s1.mem k = nBadFrom win e seeds s.mem k := fun k => by
    refine le_antisymm
      (nBadFrom_mono_of_imp (by rw [hcr1, htr1_o])
        fun id _ => isBadOldSlot_fixed_pool hv hinv hbp1 hoi1 hcr1
          (fun _ _ _ h => htr1_o ▸ h) id)
      (nBadFrom_mono_of_imp (by rw [hcr1, htr1_o]) fun id _ h => ?_)
    obtain ⟨b0, l0, u0, hc0, hb0, hl0, hk0, hcol0⟩ := h
    have hkey0 : fastKeyAt fl seeds.bkt s1.mem b0 l0 = fastKeyAt fl seeds.bkt s.mem b0 l0 :=
      fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp1 hoi1 hb0 hl0
    exact ⟨b0, l0, u0, by rw [hcr1, htr1_o]; exact hc0, hb0, hbp1 ▸ hl0,
      hkey0.trans hk0, hcol0⟩
  have hold_s1 : ∀ id b loc (u : Fin fl.U),
      bufCheckSlot (extractBufTrie (fl.trieL (1 - fm1.curBufRole)) s1.mem) id = some (b, loc) →
      b < numBucketsWhp fl.N → loc < (extractBlockPool fl.mp s1.mem).bktCount b →
      fastKeyAt fl seeds.bkt s1.mem b loc = u.val → u ∈ win.subBatches e :=
    fun id b loc u hchk hb hl hk => by
      rw [hcr1, htr1_o] at hchk; rw [hbp1] at hl
      have hkey : fastKeyAt fl seeds.bkt s1.mem b loc = fastKeyAt fl seeds.bkt s.mem b loc :=
        fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp1 hoi1 hb hl
      exact hold_sub id b loc u hchk hb hl (hkey.symm.trans hk)
  rcases hcases hta1 with ⟨htp_lt, hta1', htb1, hts1, htp1, _, _⟩ |
      ⟨hta1', htb1, htp0, _, hts_nxt, _, hs_try, u, v, huv, hsu, hsv, hbu, hbv, hfp⟩ |
      ⟨_, hta0, hdp_lk, hbt_eq, hbs_upd, hrl_upd, _⟩
  · -- Case A: `tryPos' = tryPos + 1`
    have hne0 : fm1.tryAct ≠ 0 := by rw [hta1']; exact Nat.one_ne_zero
    rw [ite_eq_right hne0]
    refine ⟨hold_s1,
      fun _ hdp b' l' hc => by
        rw [hcr1, htr1_o, hdp1] at hdp hc
        exact (hmatch hdp b' l' hc).trans htb1.symm,
      fun _ => by rw [htb1, hts1]; exact hsalt_le, ?_⟩
    unfold drainPotential; dsimp only
    rw [ite_eq_left hta1', ite_eq_left hta1, hcr1, htr1_o, hdp1, htb1, hts1, htp1, hbp1,
      hnb1_eq (fm.drainPos + 1)]
    have hlt_cnt : fm.tryPos < bp.bktCount fm.tryBkt := htp_lt
    have hsub_p : bp.bktCount fm.tryBkt - fm.tryPos =
        (bp.bktCount fm.tryBkt - (fm.tryPos + 1)) + 1 := by omega
    linarith only [hsub_p]
  · -- Case B: salt collision `(u, v)` under `fm.trySalt` → `trySalt' = trySalt + 1`
    have hne0 : fm1.tryAct ≠ 0 := by rw [hta1']; exact Nat.one_ne_zero
    rw [ite_eq_right hne0]
    obtain ⟨hs_star, hinj_star⟩ := goodSaltVal_spec hgood e hb_t
    have hne_salt : fm.trySalt ≠ goodSaltVal hgood e fm.tryBkt := by
      intro heq
      have hfp' : fpHash fl.c fl.U fl.N seeds.fp ⟨goodSaltVal hgood e fm.tryBkt, hs_star⟩ u =
          fpHash fl.c fl.U fl.N seeds.fp ⟨goodSaltVal hgood e fm.tryBkt, hs_star⟩ v := by
        rw [fpHash_congr_salt (h₂ := hs_try) heq.symm u,
          fpHash_congr_salt (h₂ := hs_try) heq.symm v]
        exact hfp
      exact hinj_star u (hlive u hsu) v (hlive v hsv) hbu hbv huv hfp'
    have hts_lt : fm.trySalt + 1 ≤ goodSaltVal hgood e fm.tryBkt := by omega
    have hts_lt_S : fm.trySalt + 1 < sMaxWhp fl.c fl.N := lt_of_le_of_lt hts_lt hs_star
    have hts_eq : fm1.trySalt = fm.trySalt + 1 := by
      have h := hts_nxt
      change fm1.trySalt = (if fm.trySalt + 1 < sMaxWhp fl.c fl.N then fm.trySalt + 1 else 0) at h
      rwa [ite_eq_left hts_lt_S] at h
    refine ⟨hold_s1,
      fun _ hdp b' l' hc => by
        rw [hcr1, htr1_o, hdp1] at hdp hc
        exact (hmatch hdp b' l' hc).trans htb1.symm,
      fun _ => by rw [htb1, hts_eq]; exact hts_lt, ?_⟩
    unfold drainPotential; dsimp only
    rw [ite_eq_left hta1', ite_eq_left hta1, hcr1, htr1_o, hdp1, htb1, hts_eq, htp0, hbp1,
      Nat.sub_zero, hnb1_eq (fm.drainPos + 1)]
    have hsub_s : goodSaltVal hgood e fm.tryBkt - fm.trySalt =
        (goodSaltVal hgood e fm.tryBkt - (fm.trySalt + 1)) + 1 := by omega
    have hmul_eq : (goodSaltVal hgood e fm.tryBkt - fm.trySalt) * (capMaxWhp fl.N + 2) =
        (goodSaltVal hgood e fm.tryBkt - (fm.trySalt + 1)) * (capMaxWhp fl.N + 2) +
          (capMaxWhp fl.N + 2) := by rw [hsub_s, Nat.add_mul, Nat.one_mul]
    have hcnt_le' : bp.bktCount fm.tryBkt ≤ capMaxWhp fl.N := hcnt_le
    linarith only [hmul_eq, hcnt_le', Nat.zero_le (bp.bktCount fm.tryBkt - fm.tryPos)]
  · -- Case C: committed (`tryAct' = 0`), immediately run `drainOldSlotProg` on `s1`
    rw [ite_eq_left hta0]
    have hv1 : fl.Valid w s1.frontier := hfr1.symm ▸ hv
    have hsub1 : fm1.subStep < qEpochWhp fl.N / 2 := hss1.symm ▸ hsub
    obtain ⟨_, _, hinv2, hbp2, _, hoi2, _, hcr2, _, _, hnoop2, hact2⟩ :=
      drainOldSlotProg_spec hv1 hinv1 hsub1 hta0
    set s2 := (Memory.spec 0).clientState s1 (drainOldSlotProg fl.pBase)
    set fm2 := extractFastMeta fl s2.mem
    have hbp12 : extractBlockPool fl.mp s2.mem = bp := hbp2.trans hbp1
    have hoi12 : ∀ a, fl.io.OwnsAddr a → s2.mem a = s.mem a :=
      fun a ha => (hoi2 a ha).trans (hoi1 a ha)
    have hcr12 : fm2.curBufRole = fm.curBufRole := hcr2.trans hcr1
    by_cases hdp_lt : fm.drainPos < (extractBufTrie (fl.trieL oldRole) s.mem).itemAlloc
    · have hdp_lt1 : fm1.drainPos <
          (extractBufTrie (fl.trieL (1 - fm1.curBufRole)) s1.mem).itemAlloc := by
        rw [hdp1, hcr1, htr1_o]; exact hdp_lt
      rcases hact2 hdp_lt1 with ⟨_, hdp2, hta2, htr2, _⟩ |
          ⟨b, loc, u, _, _, _, _, hdp2, hta2, htr2, _⟩ |
          ⟨b, loc, hb, u, _, hchk, _, _, _, _, _, _, _, hs2_eq, hsc2, _⟩ |
          ⟨b, loc, hb, u, _, hchk, hku, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnot0⟩
      · -- Subcase 1: `none`
        have htr2_o : extractBufTrie (fl.trieL oldRole) s2.mem =
            extractBufTrie (fl.trieL oldRole) s.mem := by
          have : extractBufTrie (fl.trieL (1 - fm1.curBufRole)) s2.mem =
              extractBufTrie (fl.trieL (1 - fm1.curBufRole)) s1.mem := htr2
          rwa [hcr1, htr1_o] at this
        have hstep := drainOldSlotProg_dp_step_pot (win := win) (e := e) (seeds := seeds)
          (hgood := hgood) hcr12 hta2 hdp_lt (hdp2.trans (congrArg (· + 1) hdp1))
          (by rw [hcr12, htr2_o])
          (fun id _ => isBadOldSlot_fixed_pool hv hinv hbp12 hoi12 hcr12
            (fun _ _ _ h => htr2_o ▸ h) id)
        refine ⟨fun id b' l' u' hc hb' hl' hk' => ?_,
          fun h1 => absurd (hta2.symm.trans h1) Nat.zero_ne_one,
          fun h1 => absurd (hta2.symm.trans h1) Nat.zero_ne_one, ?_⟩
        · rw [hcr12, htr2_o] at hc; rw [hbp12] at hl'
          exact hold_sub id b' l' u' hc hb' hl'
            ((fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp12 hoi12 hb' hl').symm.trans hk')
        · unfold drainPotential; dsimp only; rw [ite_eq_left hta1]
          exact hstep.trans (Nat.le_add_right _ _)
      · -- Subcase 2: drained cleanly (`bufDelete`)
        have himp : ∀ id b' l',
            bufCheckSlot (extractBufTrie (fl.trieL oldRole) s2.mem) id = some (b', l') →
              bufCheckSlot (extractBufTrie (fl.trieL oldRole) s.mem) id = some (b', l') := by
          intro id b' l' hc
          have htr2' : extractBufTrie (fl.trieL oldRole) s2.mem =
              bufDelete (cTabWhp fl.c) (bCharWhp fl.N)
                (extractBufTrie (fl.trieL oldRole) s.mem)
                (rKeyOf fl.c fl.U fl.N seeds.fp u) := by
            have h := htr2; rwa [hcr1, htr1_o] at h
          rw [htr2'] at hc; exact bufCheckSlot_bufDelete_imp hc
        have hia_eq : (extractBufTrie (fl.trieL (1 - fm2.curBufRole)) s2.mem).itemAlloc =
            (extractBufTrie (fl.trieL oldRole) s.mem).itemAlloc := by
          rw [hcr12]
          have h := htr2; rw [hcr1, htr1_o] at h; rw [h, bufDelete_itemAlloc_eq]
        have hstep := drainOldSlotProg_dp_step_pot (win := win) (e := e) (seeds := seeds)
          (hgood := hgood) hcr12 hta2 hdp_lt (hdp2.trans (congrArg (· + 1) hdp1)) hia_eq
          (fun id _ => isBadOldSlot_fixed_pool hv hinv hbp12 hoi12 hcr12 himp id)
        refine ⟨fun id b' l' u' hc hb' hl' hk' => ?_,
          fun h1 => absurd (hta2.symm.trans h1) Nat.zero_ne_one,
          fun h1 => absurd (hta2.symm.trans h1) Nat.zero_ne_one, ?_⟩
        · rw [hcr12] at hc; rw [hbp12] at hl'
          exact hold_sub id b' l' u' (himp id b' l' hc) hb' hl'
            ((fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp12 hoi12 hb' hl').symm.trans hk')
        · unfold drainPotential; dsimp only; rw [ite_eq_left hta1]
          exact hstep.trans (Nat.le_add_right _ _)
      · -- Subcase 3 impossible: `fm1.shadowCode b = 0`!
        rw [hcr1, htr1_o, hdp1] at hchk
        have hbe : b = fm.tryBkt := hmatch hdp_lt b loc hchk
        have hsc0 : fm1.shadowCode b = 0 := by rw [hbe, congrFun hsc1 fm.tryBkt]; exact hsc_t
        have hs2_noop : s2 = s1 :=
          hs2_eq.trans (fastShadowSteps8Prog_eq_of_shadowZero hinv1.param_table hb hsc0)
        exact absurd
          (by change (extractFastMeta fl s2.mem).shadowCode b = 0; rw [hs2_noop]; exact hsc0) hsc2
      · -- Subcase 4 impossible: `fastBTreeLookupProg` returned `(0, 0)`!
        rw [hcr1, htr1_o, hdp1] at hchk
        have hbe : b = fm.tryBkt := hmatch hdp_lt b loc hchk
        subst hbe
        have hsc0 : fm1.shadowCode fm.tryBkt = 0 := by
          rw [congrFun hsc1 fm.tryBkt]; exact hsc_t
        have hl_s : loc < bp.bktCount fm.tryBkt := by
          obtain ⟨_, mapOld, _, _, _, _, _, _, _, hold_half, _⟩ := hinv.tiers
          rw [ite_eq_left hsub] at hold_half
          obtain ⟨hv_o, _, _, _, _, _, _, hold_snd⟩ := hold_half
          obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
          exact (hold_snd k fm.tryBkt loc hmk).2.2.1
        have hkey_s : fastKeyAt fl seeds.bkt s.mem fm.tryBkt loc = u.val :=
          (fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp1 hoi1 hb hl_s).symm.trans hku
        obtain ⟨hs_t', hlk_s⟩ := hdp_lk loc u hchk hkey_s
        have hrole1 : fm1.curRole fm.tryBkt = tryRoleOf (fm.curRole fm.tryBkt) := by
          rw [hrl_upd, Function.update_self]
        have hsalt1 : fm1.bktSalt fm.tryBkt = fm.trySalt := by
          rw [hbs_upd, Function.update_self]
        have hti_8 : fm.tryIns ≤ 8 * slabScale fl.N ^ 12 := by
          have : 4 * fm.tryIns ≤ 20 * slabScale fl.N ^ 12 := by
            have := hti_le_m; exact (Nat.le_add_right _ _).trans this
          omega
        have htRole_lt : tryRoleOf (fm.curRole fm.tryBkt) < 3 :=
          (tryRoleOf_lt_and_ne (hinv.bkt_meta_bounds fm.tryBkt hb_t).2.1).1
        set fp := (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t'⟩ u).val
        have hfp_lt : fp < 2 ^ fpBitsWhp fl.N :=
          (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t'⟩ u).isLt
        have hfp_eq : (fpHash fl.c fl.U fl.N seeds.fp
              ⟨fm1.bktSalt fm.tryBkt, (hinv1.bkt_meta_bounds fm.tryBkt hb).1⟩ u).val = fp :=
          congrArg Fin.val (fpHash_congr_salt hsalt1 u)
        have hspec_s := (fastBTreeLookupProg_spec (hinv.ready hv rfl) hb_t htRole_lt hti_8 hv_tm
          hfp_lt).1
        have hspec_s1 := (fastBTreeLookupProg_spec (hinv1.ready hv1 rfl) hb_t htRole_lt hti_8
          (by rw [hbt_eq fm.tryBkt hb_t _ htRole_lt]; exact hv_tm) hfp_lt).1
        have hlk_s1 : (Memory.spec 0).clientResult s1 (fastBTreeLookupProg
            ((fl.pBase, (fm.tryBkt, fm1.curRole fm.tryBkt)),
              (fpHash fl.c fl.U fl.N seeds.fp
                ⟨fm1.bktSalt fm.tryBkt, (hinv1.bkt_meta_bounds fm.tryBkt hb).1⟩ u).val)) =
              (0, 0) := by
          have hgoal : (fl.pBase, (fm.tryBkt, fm1.curRole fm.tryBkt)) =
              (fl.pBase, (fm.tryBkt, tryRoleOf (fm.curRole fm.tryBkt))) := by rw [hrole1]
          rw [hgoal, hfp_eq, hspec_s1, ← hspec_s, hlk_s]
        exact (hnot0 hsc0 hlk_s1).elim
    · have hst : s2 = s1 :=
        hnoop2 (by rw [hcr1, htr1_o, hdp1]; exact Nat.le_of_not_lt hdp_lt)
      change (∀ id b loc (u : Fin fl.U), _ → _ → _ → _ → _) ∧ _
      have hpot0 : drainPotential win e seeds hgood s1.mem = 0 :=
        (drainPotential_eq_zero_iff (by rw [hta0]; exact Nat.zero_le 1)).mpr
          ⟨by rw [hcr1, htr1_o, hdp1]; exact Nat.le_of_not_lt hdp_lt, hta0⟩
      have hfst_ge : 1 ≤ drainPotential win e seeds hgood s.mem := by
        unfold drainPotential; dsimp only; rw [ite_eq_left hta1]; omega
      refine ⟨fun id b loc u hchk hb hl hk => by
          change bufCheckSlot
            (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s2.mem).curBufRole)) s2.mem) id =
              some (b, loc) at hchk
          change loc < (extractBlockPool fl.mp s2.mem).bktCount b at hl
          change fastKeyAt fl seeds.bkt s2.mem b loc = u.val at hk
          rw [hst] at hchk hl hk
          exact hold_s1 id b loc u hchk hb hl hk,
        fun h1 => absurd (hta0.symm.trans (by
          change (extractFastMeta fl s2.mem).tryAct = 1 at h1; rwa [hst] at h1)) Nat.zero_ne_one,
        fun h1 => absurd (hta0.symm.trans (by
          change (extractFastMeta fl s2.mem).tryAct = 1 at h1; rwa [hst] at h1)) Nat.zero_ne_one,
        by rw [hst, hpot0]; exact hfst_ge⟩

/-- Single-step good-seed specification of `drainTryTickProg` (monotone potential: `Φ' ≤ Φ`). -/
theorem drainTryTickProg_good {slackCur : ℕ} {fl : FastEpochLayout} {w slack : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {hgood : GoodEpochSeeds win seeds}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hlive : ∀ u : Fin fl.U, s_abs u ≠ none → u ∈ win.subUnions e)
    (hold_sub : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2 →
      ∀ id b loc (u : Fin fl.U),
        bufCheckSlot (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem)
          id = some (b, loc) →
        b < numBucketsWhp fl.N →
        loc < (extractBlockPool fl.mp s.mem).bktCount b →
        fastKeyAt fl seeds.bkt s.mem b loc = u.val →
        u ∈ win.subBatches e)
    (hmatch : (extractFastMeta fl s.mem).tryAct = 1 →
      (extractFastMeta fl s.mem).drainPos <
        (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem).itemAlloc →
      ∀ b' loc', bufCheckSlot
          (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem)
          (extractFastMeta fl s.mem).drainPos = some (b', loc') →
        b' = (extractFastMeta fl s.mem).tryBkt)
    (hsalt_le : (extractFastMeta fl s.mem).tryAct = 1 →
      (extractFastMeta fl s.mem).trySalt ≤
        goodSaltVal hgood e (extractFastMeta fl s.mem).tryBkt) :
    let s' := (Memory.spec 0).clientState s (drainTryTickProg fl.pBase)
    let fm' := extractFastMeta fl s'.mem
    ((extractFastMeta fl s'.mem).subStep < qEpochWhp fl.N / 2 →
      ∀ id b loc (u : Fin fl.U),
        bufCheckSlot (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem) id = some (b, loc) →
        b < numBucketsWhp fl.N →
        loc < (extractBlockPool fl.mp s'.mem).bktCount b →
        fastKeyAt fl seeds.bkt s'.mem b loc = u.val →
        u ∈ win.subBatches e) ∧
    (fm'.tryAct = 1 → fm'.drainPos <
        (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem).itemAlloc →
      ∀ b' loc', bufCheckSlot (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem)
        fm'.drainPos = some (b', loc') → b' = fm'.tryBkt) ∧
    (fm'.tryAct = 1 → fm'.trySalt ≤ goodSaltVal hgood e fm'.tryBkt) ∧
    ((extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2 →
      drainPotential win e seeds hgood s'.mem ≤ drainPotential win e seeds hgood s.mem) := by
  dsimp only
  set fm := extractFastMeta fl s.mem
  have hm6_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 6)) = fm.tryAct :=
    clientResult_fastReadMetaProg hinv.param_table (by decide)
  unfold drainTryTickProg
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm6_r]
  by_cases hta : fm.tryAct = 1
  · rw [ite_eq_left hta, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      clientState_fastReadMetaProg]
    have hsub : fm.subStep < qEpochWhp fl.N / 2 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, htry⟩ := hinv.tiers
      exact (htry hta).1
    obtain ⟨_, _, hinv1, _⟩ := drainTryStepProg_spec hv hinv
    set s1 := (Memory.spec 0).clientState s (drainTryStepProg fl.pBase)
    have hm6_r1 : (Memory.spec 0).clientResult s1 (fastReadMetaProg (fl.pBase, 6)) =
        (extractFastMeta fl s1.mem).tryAct :=
      clientResult_fastReadMetaProg hinv1.param_table (by decide)
    rw [hm6_r1]
    obtain ⟨ho, hm, hs, hp⟩ :=
      drainTryStep_commit_good hv hinv hta hlive (hold_sub hsub) (hmatch hta) (hsalt_le hta)
    by_cases hta0 : (extractFastMeta fl s1.mem).tryAct = 0
    · rw [ite_eq_left hta0] at ho hm hs hp ⊢
      exact ⟨fun _ => ho, hm, hs, fun _ => Nat.le_of_lt (Nat.lt_of_succ_le hp)⟩
    · rw [ite_eq_right hta0] at ho hm hs hp ⊢
      rw [StateTransitionSpec.clientState_pure]
      exact ⟨fun _ => ho, hm, hs, fun _ => Nat.le_of_lt (Nat.lt_of_succ_le hp)⟩
  · rw [ite_eq_right hta, StateTransitionSpec.clientState_pure]
    exact ⟨hold_sub, hmatch, hsalt_le, fun _ => le_rfl⟩

/-- `drainTrySteps5Prog` preserves `FastSubEpochGood` (`drainPotential` non-increasing). -/
theorem drainTrySteps5Prog_good {slackCur slackPot : ℕ} {fl : FastEpochLayout} {w slack b : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {hgood : GoodEpochSeeds win seeds}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hg : FastSubEpochGood slackCur slackPot slack win e seeds hgood s.mem s_abs)
    (hb : b < numBucketsWhp fl.N)
    (hcnt_lt : (extractBlockPool fl.mp s.mem).bktCount b < capMaxWhp fl.N) :
    FastSubEpochGood slackCur slackPot slack win e seeds hgood
      ((Memory.spec 0).clientState s (drainTrySteps5Prog fl.pBase)).mem s_abs := by
  have h1 : ∀ (st : Memory.State), fl.Valid w st.frontier →
      (extractBlockPool fl.mp st.mem).bktCount b < capMaxWhp fl.N →
      FastSubEpochGood slackCur slackPot slack win e seeds hgood st.mem s_abs →
      fl.Valid w ((Memory.spec 0).clientState st (drainTryTickProg fl.pBase)).frontier ∧
      (extractBlockPool fl.mp
        ((Memory.spec 0).clientState st (drainTryTickProg fl.pBase)).mem).bktCount b <
          capMaxWhp fl.N ∧
      FastSubEpochGood slackCur slackPot slack win e seeds hgood
        ((Memory.spec 0).clientState st (drainTryTickProg fl.pBase)).mem s_abs := by
    intro st hvs hcl hgs
    have h0_sl : (extractFastMeta fl st.mem).tryAct = 1 →
        (extractFastMeta fl st.mem).tryBkt = b →
        4 * (extractFastMeta fl st.mem).tryIns +
          5 * ((extractBlockPool fl.mp st.mem).bktCount b -
            (extractFastMeta fl st.mem).tryPos) + 0 ≤ 20 * slabScale fl.N ^ 12 := fun hta htb => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, htry⟩ := hgs.inv.tiers
      have h := (htry hta).2.choose_spec.choose_spec.2.2.1
      rw [htb] at h; simpa only [Nat.add_zero] using h
    obtain ⟨hfr', _, hi', hbp', _, _, _, _, hss', _, _⟩ :=
      drainTryTickProg_spec (k := 0) hvs hgs.inv hb hcl (by decide) h0_sl
    obtain ⟨ho', hm', hs', hp'⟩ :=
      drainTryTickProg_good hvs hgs.inv hgs.live_sub hgs.old_sub hgs.try_match hgs.trySalt_le
    refine ⟨hfr'.symm ▸ hvs, by rw [hbp']; exact hcl,
      { inv := hi'
        live_sub := hgs.live_sub
        old_sub := ho'
        try_match := hm'
        trySalt_le := hs'
        pot_le := fun hsub' => by
          have hsub : (extractFastMeta fl st.mem).subStep < qEpochWhp fl.N / 2 := hss' ▸ hsub'
          exact (hp' hsub).trans (by rw [hss']; exact hgs.pot_le hsub) }⟩
  obtain ⟨v1, c1, g1⟩ := h1 s hv hcnt_lt hg
  obtain ⟨v2, c2, g2⟩ := h1 _ v1 c1 g1
  obtain ⟨v3, c3, g3⟩ := h1 _ v2 c2 g2
  obtain ⟨v4, c4, g4⟩ := h1 _ v3 c3 g3
  obtain ⟨_, _, g5⟩ := h1 _ v4 c4 g4
  unfold drainTrySteps5Prog
  iterate 4 rw [StateTransitionSpec.clientState_bind]
  exact g5

/-- Single `drainTickProg` step strictly decreases `drainPotential` by `≥ 1` when `Φ > 0`. -/
theorem drainTickProg_good {slackCur : ℕ} {fl : FastEpochLayout} {w slack : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {hgood : GoodEpochSeeds win seeds}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hsub : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2)
    (hlive : ∀ u : Fin fl.U, s_abs u ≠ none → u ∈ win.subUnions e)
    (hold_sub : ∀ id b loc (u : Fin fl.U),
      bufCheckSlot (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem)
        id = some (b, loc) →
      b < numBucketsWhp fl.N →
      loc < (extractBlockPool fl.mp s.mem).bktCount b →
      fastKeyAt fl seeds.bkt s.mem b loc = u.val →
      u ∈ win.subBatches e)
    (hmatch : (extractFastMeta fl s.mem).tryAct = 1 →
      (extractFastMeta fl s.mem).drainPos <
        (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem).itemAlloc →
      ∀ b' loc', bufCheckSlot
          (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem)
          (extractFastMeta fl s.mem).drainPos = some (b', loc') →
        b' = (extractFastMeta fl s.mem).tryBkt)
    (hsalt_le : (extractFastMeta fl s.mem).tryAct = 1 →
      (extractFastMeta fl s.mem).trySalt ≤
        goodSaltVal hgood e (extractFastMeta fl s.mem).tryBkt) :
    let s' := (Memory.spec 0).clientState s (drainTickProg fl.pBase)
    let fm' := extractFastMeta fl s'.mem
    (∀ id b loc (u : Fin fl.U),
      bufCheckSlot (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem) id = some (b, loc) →
      b < numBucketsWhp fl.N →
      loc < (extractBlockPool fl.mp s'.mem).bktCount b →
      fastKeyAt fl seeds.bkt s'.mem b loc = u.val →
      u ∈ win.subBatches e) ∧
    (fm'.tryAct = 1 → fm'.drainPos <
        (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem).itemAlloc →
      ∀ b' loc', bufCheckSlot (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem)
        fm'.drainPos = some (b', loc') → b' = fm'.tryBkt) ∧
    (fm'.tryAct = 1 → fm'.trySalt ≤ goodSaltVal hgood e fm'.tryBkt) ∧
    drainPotential win e seeds hgood s'.mem ≤ drainPotential win e seeds hgood s.mem - 1 := by
  dsimp only
  set fm := extractFastMeta fl s.mem
  have hm6_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 6)) = fm.tryAct :=
    clientResult_fastReadMetaProg hinv.param_table (by decide)
  have hta_le : fm.tryAct ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hle, _⟩ := hinv.tiers; exact hle
  unfold drainTickProg
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm6_r]
  by_cases hta : fm.tryAct = 1
  · rw [ite_eq_left hta, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      clientState_fastReadMetaProg]
    obtain ⟨_, _, hinv1, _⟩ := drainTryStepProg_spec hv hinv
    set s1 := (Memory.spec 0).clientState s (drainTryStepProg fl.pBase)
    have hm6_r1 : (Memory.spec 0).clientResult s1 (fastReadMetaProg (fl.pBase, 6)) =
        (extractFastMeta fl s1.mem).tryAct :=
      clientResult_fastReadMetaProg hinv1.param_table (by decide)
    rw [hm6_r1]
    obtain ⟨ho, hm, hs, hp⟩ :=
      drainTryStep_commit_good hv hinv hta hlive hold_sub (hmatch hta) (hsalt_le hta)
    by_cases hta0 : (extractFastMeta fl s1.mem).tryAct = 0
    · rw [ite_eq_left hta0] at ho hm hs hp ⊢
      exact ⟨ho, hm, hs, Nat.le_sub_of_add_le hp⟩
    · rw [ite_eq_right hta0] at ho hm hs hp ⊢
      rw [StateTransitionSpec.clientState_pure]
      exact ⟨ho, hm, hs, Nat.le_sub_of_add_le hp⟩
  · have hta0 : fm.tryAct = 0 := by omega
    rw [ite_eq_right hta]
    exact drainOldSlotProg_step_good hv hinv hsub hta0 hlive hold_sub

/-- `drainTicks16Prog` drops `drainPotential` by `16` (floored at `0`). -/
theorem drainTicks16Prog_good {slackCur : ℕ} {fl : FastEpochLayout} {w slack : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {hgood : GoodEpochSeeds win seeds}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hsub : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2)
    (hlive : ∀ u : Fin fl.U, s_abs u ≠ none → u ∈ win.subUnions e)
    (hold_sub : ∀ id b loc (u : Fin fl.U),
      bufCheckSlot (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem)
        id = some (b, loc) →
      b < numBucketsWhp fl.N →
      loc < (extractBlockPool fl.mp s.mem).bktCount b →
      fastKeyAt fl seeds.bkt s.mem b loc = u.val →
      u ∈ win.subBatches e)
    (hmatch : (extractFastMeta fl s.mem).tryAct = 1 →
      (extractFastMeta fl s.mem).drainPos <
        (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem).itemAlloc →
      ∀ b' loc', bufCheckSlot
          (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem)
          (extractFastMeta fl s.mem).drainPos = some (b', loc') →
        b' = (extractFastMeta fl s.mem).tryBkt)
    (hsalt_le : (extractFastMeta fl s.mem).tryAct = 1 →
      (extractFastMeta fl s.mem).trySalt ≤
        goodSaltVal hgood e (extractFastMeta fl s.mem).tryBkt) :
    let s' := (Memory.spec 0).clientState s (drainTicks16Prog fl.pBase)
    let fm' := extractFastMeta fl s'.mem
    (∀ id b loc (u : Fin fl.U),
      bufCheckSlot (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem) id = some (b, loc) →
      b < numBucketsWhp fl.N →
      loc < (extractBlockPool fl.mp s'.mem).bktCount b →
      fastKeyAt fl seeds.bkt s'.mem b loc = u.val →
      u ∈ win.subBatches e) ∧
    (fm'.tryAct = 1 → fm'.drainPos <
        (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem).itemAlloc →
      ∀ b' loc', bufCheckSlot (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem)
        fm'.drainPos = some (b', loc') → b' = fm'.tryBkt) ∧
    (fm'.tryAct = 1 → fm'.trySalt ≤ goodSaltVal hgood e fm'.tryBkt) ∧
    drainPotential win e seeds hgood s'.mem ≤ drainPotential win e seeds hgood s.mem - 16 := by
  let P (st : Memory.State) : Prop :=
    fl.Valid w st.frontier ∧
    FastEpochInvGen slackCur fl slack seeds st.mem s_abs ∧
    (extractFastMeta fl st.mem).subStep < qEpochWhp fl.N / 2 ∧
    (∀ id b loc (u : Fin fl.U),
      bufCheckSlot (extractBufTrie (fl.trieL (1 - (extractFastMeta fl st.mem).curBufRole)) st.mem)
        id = some (b, loc) →
      b < numBucketsWhp fl.N → loc < (extractBlockPool fl.mp st.mem).bktCount b →
      fastKeyAt fl seeds.bkt st.mem b loc = u.val → u ∈ win.subBatches e) ∧
    ((extractFastMeta fl st.mem).tryAct = 1 →
      (extractFastMeta fl st.mem).drainPos <
        (extractBufTrie (fl.trieL (1 - (extractFastMeta fl st.mem).curBufRole))
          st.mem).itemAlloc →
      ∀ b' loc', bufCheckSlot
          (extractBufTrie (fl.trieL (1 - (extractFastMeta fl st.mem).curBufRole)) st.mem)
          (extractFastMeta fl st.mem).drainPos = some (b', loc') →
        b' = (extractFastMeta fl st.mem).tryBkt) ∧
    ((extractFastMeta fl st.mem).tryAct = 1 →
      (extractFastMeta fl st.mem).trySalt ≤
        goodSaltVal hgood e (extractFastMeta fl st.mem).tryBkt)
  have dbl : ∀ (p : ℕ → Memory.Prog Unit) (m : ℕ),
      (∀ st, P st → P ((Memory.spec 0).clientState st (p fl.pBase)) ∧
        drainPotential win e seeds hgood
          ((Memory.spec 0).clientState st (p fl.pBase)).mem ≤
          drainPotential win e seeds hgood st.mem - m) →
      ∀ st, P st →
        P ((Memory.spec 0).clientState st (do p fl.pBase; p fl.pBase)) ∧
        drainPotential win e seeds hgood
          ((Memory.spec 0).clientState st (do p fl.pBase; p fl.pBase)).mem ≤
          drainPotential win e seeds hgood st.mem - 2 * m := by
    intro p m hp st hst
    rw [StateTransitionSpec.clientState_bind]
    obtain ⟨hp1, hd1⟩ := hp st hst
    obtain ⟨hp2, hd2⟩ := hp _ hp1
    exact ⟨hp2, hd2.trans (by omega)⟩
  have h1 : ∀ st, P st → P ((Memory.spec 0).clientState st (drainTickProg fl.pBase)) ∧
      drainPotential win e seeds hgood
        ((Memory.spec 0).clientState st (drainTickProg fl.pBase)).mem ≤
        drainPotential win e seeds hgood st.mem - 1 := by
    intro st ⟨hvs, his, hss, ho, hm, hs⟩
    obtain ⟨hfr', _, hi', _, _, _, _, _, hss'⟩ := drainTickProg_spec hvs his hss
    obtain ⟨ho', hm', hs', hd'⟩ := drainTickProg_good hvs his hss hlive ho hm hs
    exact ⟨⟨hfr'.symm ▸ hvs, hi', hss'.symm ▸ hss, ho', hm', hs'⟩, hd'⟩
  have h16 := dbl drainTicks8Prog 8 (dbl drainTicks4Prog 4 (dbl drainTicks2Prog 2
    (dbl drainTickProg 1 h1)))
  obtain ⟨⟨_, _, _, ho, hm, hs⟩, hd⟩ := h16 s ⟨hv, hinv, hsub, hold_sub, hmatch, hsalt_le⟩
  exact ⟨ho, hm, hs, hd⟩

/-- Under `GoodEpochSeeds win seeds` (`FastSubEpochGood 1 5`), `advanceSubEpochProg` **NEVER**
enters fallback (`fallbackMode = 0`, `FastEpochInv`, `memoryCost ≤ advanceSubEpochCost fl.c`),
advancing `subStep` through both halves of the sub-epoch and seamlessly rolling over to any
sub-epoch `eNext` covering the promoted `BufCur` batch and live keys. -/
theorem advanceSubEpochProg_good {fl : FastEpochLayout} {w slack : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {hgood : GoodEpochSeeds win seeds}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hg : FastSubEpochGood 1 5 slack win e seeds hgood s.mem s_abs) :
    let s' := (Memory.spec 0).clientState s (advanceSubEpochProg fl.pBase)
    let fm := extractFastMeta fl s.mem
    s'.frontier = s.frontier ∧
    memoryCost (advanceSubEpochProg fl.pBase) s ≤ advanceSubEpochCost fl.c ∧
    FastEpochInv fl slack seeds s'.mem s_abs ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fm.subStep + 1 < qEpochWhp fl.N →
      FastSubEpochGood 0 0 slack win e seeds hgood s'.mem s_abs ∧
      (extractFastMeta fl s'.mem).subStep = fm.subStep + 1 ∧
      (extractFastMeta fl s'.mem).curBufRole = fm.curBufRole) ∧
    (fm.subStep + 1 = qEpochWhp fl.N →
      (extractFastMeta fl s'.mem).curBufRole = 1 - fm.curBufRole ∧
      (extractFastMeta fl s'.mem).subStep = 0 ∧
      (extractFastMeta fl s'.mem).drainPos = 0 ∧
      (extractFastMeta fl s'.mem).tryAct = 0 ∧
      (∀ eNext : Fin win.numSubs,
        (∀ u : Fin fl.U, s_abs u ≠ none → u ∈ win.subUnions eNext) →
        (∀ id b loc (u : Fin fl.U),
          bufCheckSlot (extractBufTrie (fl.trieL fm.curBufRole) s.mem) id = some (b, loc) →
          b < numBucketsWhp fl.N →
          loc < (extractBlockPool fl.mp s.mem).bktCount b →
          fastKeyAt fl seeds.bkt s.mem b loc = u.val →
          u ∈ win.subBatches eNext) →
        FastSubEpochGood 0 0 slack win eNext seeds hgood s'.mem s_abs)) := by
  dsimp only
  set fm := extractFastMeta fl s.mem
  set Q := qEpochWhp fl.N
  have ⟨h2dvd, hQ4⟩ := qEpochWhp_even_and_ge fl.N
  have hQ_eq : Q = 2 * (Q / 2) := (Nat.mul_div_cancel' h2dvd).symm
  obtain ⟨hfr, hof, _, _, hbranch⟩ := advanceSubEpochProg_spec hv hg.inv
  by_cases hsub : fm.subStep < Q / 2
  · rw [ite_eq_left hsub] at hbranch
    set sMid := (Memory.spec 0).clientState s (drainTicks16Prog fl.pBase)
    set fmMid := extractFastMeta fl sMid.mem
    obtain ⟨hfr_m, _, hinv_m, hbp_m, _, hoi_m, _, hcr_m, hss_m⟩ :=
      drainTicks16Prog_spec hv hg.inv hsub
    obtain ⟨ho_m, hm_m, hs_m, hd_m⟩ :=
      drainTicks16Prog_good hv hg.inv hsub hg.live_sub (hg.old_sub hsub) hg.try_match hg.trySalt_le
    have hpot_in : drainPotential win e seeds hgood s.mem ≤ 2 * Q - 11 * fm.subStep + 5 :=
      hg.pot_le hsub
    have hpot_m : drainPotential win e seeds hgood sMid.mem ≤
        2 * Q - 11 * (fm.subStep + 1) := by
      have hd_m' : drainPotential win e seeds hgood sMid.mem ≤
          drainPotential win e seeds hgood s.mem - 16 := hd_m
      omega
    have hcond : fm.subStep + 1 < Q / 2 ∨
        ((extractBufTrie (fl.trieL (1 - fm.curBufRole)) sMid.mem).itemAlloc ≤
          fmMid.drainPos ∧ fmMid.tryAct = 0) := by
      by_cases hlt1 : fm.subStep + 1 < Q / 2
      · exact Or.inl hlt1
      · refine Or.inr ?_
        have heq_half : fm.subStep + 1 = Q / 2 := by omega
        have hpot0 : drainPotential win e seeds hgood sMid.mem = 0 := by
          rw [heq_half] at hpot_m; omega
        have hta_le : fmMid.tryAct ≤ 1 := by
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hle, _⟩ := hinv_m.tiers; exact hle
        have hd := (drainPotential_eq_zero_iff hta_le).mp hpot0
        exact ⟨by have h := hd.1; rwa [hcr_m] at h, hd.2⟩
    rw [ite_eq_left hcond] at hbranch
    obtain ⟨hc', hinv', hbp', hoi', htr', hfm'⟩ := hbranch
    set s' := (Memory.spec 0).clientState s (advanceSubEpochProg fl.pBase)
    have hcr' : (extractFastMeta fl s'.mem).curBufRole = fmMid.curBufRole := by rw [hfm']
    have hss' : (extractFastMeta fl s'.mem).subStep = fm.subStep + 1 := by rw [hfm']
    have hdp' : (extractFastMeta fl s'.mem).drainPos = fmMid.drainPos := by rw [hfm']
    have hta' : (extractFastMeta fl s'.mem).tryAct = fmMid.tryAct := by rw [hfm']
    have htb' : (extractFastMeta fl s'.mem).tryBkt = fmMid.tryBkt := by rw [hfm']
    have hts' : (extractFastMeta fl s'.mem).trySalt = fmMid.trySalt := by rw [hfm']
    have htp' : (extractFastMeta fl s'.mem).tryPos = fmMid.tryPos := by rw [hfm']
    have hsc' : (extractFastMeta fl s'.mem).shadowCode = fmMid.shadowCode := by rw [hfm']
    have hsi' : (extractFastMeta fl s'.mem).shadowIns = fmMid.shadowIns := by rw [hfm']
    have hci' : (extractFastMeta fl s'.mem).curIns = fmMid.curIns := by rw [hfm']
    have hbp_m' : extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp sMid.mem := by
      rw [hbp', hbp_m]
    have hoi_m' : ∀ a, fl.io.OwnsAddr a → s'.mem a = sMid.mem a := fun a ha =>
      (hoi' a ha).trans (hoi_m a ha).symm
    have hv_m : fl.Valid w sMid.frontier := hfr_m.symm ▸ hv
    have hold_lt_m : 1 - fmMid.curBufRole < 2 := by have := hinv_m.role_lt; omega
    have htr_o' : extractBufTrie (fl.trieL (1 - (extractFastMeta fl s'.mem).curBufRole)) s'.mem =
        extractBufTrie (fl.trieL (1 - fmMid.curBufRole)) sMid.mem := by
      rw [hcr']; exact htr' (1 - fmMid.curBufRole) hold_lt_m
    have hbad_iff : ∀ id, isBadOldSlot win e seeds s'.mem id ↔
        isBadOldSlot win e seeds sMid.mem id := fun id => by
      constructor
      · intro h; rcases h with ⟨b, loc, u, hchk, hb, hl, hk, hcol⟩
        rw [htr_o'] at hchk; rw [hbp_m'] at hl
        have hkey : fastKeyAt fl seeds.bkt s'.mem b loc = fastKeyAt fl seeds.bkt sMid.mem b loc :=
          fastKeyAt_eq_of_fixed_pool hv_m hinv_m.bp_inv hbp_m' hoi_m' hb hl
        exact ⟨b, loc, u, hchk, hb, hl, hkey.symm.trans hk, hcol⟩
      · intro h; rcases h with ⟨b, loc, u, hchk, hb, hl, hk, hcol⟩
        have hkey : fastKeyAt fl seeds.bkt s'.mem b loc = fastKeyAt fl seeds.bkt sMid.mem b loc :=
          fastKeyAt_eq_of_fixed_pool hv_m hinv_m.bp_inv hbp_m' hoi_m' hb hl
        exact ⟨b, loc, u, by rw [htr_o']; exact hchk, hb, hbp_m'.symm ▸ hl,
          hkey.trans hk, hcol⟩
    have hpot_eq : drainPotential win e seeds hgood s'.mem =
        drainPotential win e seeds hgood sMid.mem := by
      have hnb_eq : ∀ k, nBadFrom win e seeds s'.mem k = nBadFrom win e seeds sMid.mem k :=
        fun k => by
          classical
          unfold nBadFrom; dsimp only; rw [htr_o']
          congr 1; ext id
          simp only [Finset.mem_filter, Finset.mem_range, hbad_iff]
          rfl
      have hsh_eq : shTerm fl win e seeds s'.mem = shTerm fl win e seeds sMid.mem := by
        classical
        unfold shTerm; dsimp only; rw [hdp', htr_o']
        by_cases hb : isBadOldSlot win e seeds sMid.mem fmMid.drainPos
        · rw [ite_eq_left ((hbad_iff _).mpr hb), ite_eq_left hb]
          cases bufCheckSlot (extractBufTrie (fl.trieL (1 - fmMid.curBufRole)) sMid.mem)
              fmMid.drainPos with
          | none => rfl
          | some bl =>
            dsimp only; unfold shCost shSlack; dsimp only
            rw [congrFun hsc' bl.1, congrFun hsi' bl.1, congrFun hci' bl.1, hbp_m']
        · rw [ite_eq_right (fun h => hb ((hbad_iff _).mp h)), ite_eq_right hb]
      unfold drainPotential; dsimp only
      rw [hta', htb', hts', htp', hdp', hbp_m', htr_o', hnb_eq fmMid.drainPos,
        hnb_eq (fmMid.drainPos + 1), hsh_eq]
    refine ⟨hfr, hc', hinv', hbp', hoi', hof, fun _ => ⟨?_, hss', hcr'.trans hcr_m⟩,
      fun heq => by omega⟩
    refine
      { inv := hinv'.toGen 0
        live_sub := hg.live_sub
        old_sub := fun _ id b loc u hchk hb hl hk => by
          rw [htr_o'] at hchk; rw [hbp_m'] at hl
          have hkey : fastKeyAt fl seeds.bkt s'.mem b loc =
              fastKeyAt fl seeds.bkt sMid.mem b loc :=
            fastKeyAt_eq_of_fixed_pool hv_m hinv_m.bp_inv hbp_m' hoi_m' hb hl
          exact ho_m id b loc u hchk hb hl (hkey.symm.trans hk)
        try_match := fun h1 hdp b' l' hchk => by
          rw [hta'] at h1; rw [hdp', htr_o'] at hdp hchk; rw [htb']
          exact hm_m h1 hdp b' l' hchk
        trySalt_le := fun h1 => by rw [hta'] at h1; rw [htb', hts']; exact hs_m h1
        pot_le := fun _ => by rw [hpot_eq, hss', Nat.add_zero]; exact hpot_m }
  · rw [ite_eq_right hsub] at hbranch
    obtain ⟨hc', hinv', hbp', hoi', hlt_br, heq_br⟩ := hbranch
    refine ⟨hfr, hc', hinv', hbp', hoi', hof, fun hlt => ?_, fun heq => ?_⟩
    · obtain ⟨hcr', hss', hta0'⟩ := hlt_br hlt
      refine ⟨?_, hss', hcr'⟩
      refine
        { inv := hinv'.toGen 0
          live_sub := hg.live_sub
          old_sub := fun h => absurd (hss' ▸ h) (by dsimp only [fm] at hsub; omega)
          try_match := fun h1 => by rw [hta0'] at h1; cases h1
          trySalt_le := fun h1 => by rw [hta0'] at h1; cases h1
          pot_le := fun h => absurd (hss' ▸ h) (by dsimp only [fm] at hsub; omega) }
    · obtain ⟨hcr', hss', hdp', hta', hold_eq, _⟩ := heq_br heq
      refine ⟨hcr', hss', hdp', hta', fun eNext hlive_n hbatch_n => ?_⟩
      have hold_ok : ∀ id b loc (u : Fin fl.U),
          bufCheckSlot (extractBufTrie (fl.trieL (1 - (extractFastMeta fl
            ((Memory.spec 0).clientState s (advanceSubEpochProg fl.pBase)).mem).curBufRole))
              ((Memory.spec 0).clientState s (advanceSubEpochProg fl.pBase)).mem) id =
            some (b, loc) →
          b < numBucketsWhp fl.N →
          loc < (extractBlockPool fl.mp ((Memory.spec 0).clientState s
            (advanceSubEpochProg fl.pBase)).mem).bktCount b →
          fastKeyAt fl seeds.bkt ((Memory.spec 0).clientState s
            (advanceSubEpochProg fl.pBase)).mem b loc = u.val →
          u ∈ win.subBatches eNext := by
        intro id b loc u hchk hb hl hk
        rw [hold_eq] at hchk; rw [hbp'] at hl
        have hkey : fastKeyAt fl seeds.bkt ((Memory.spec 0).clientState s
            (advanceSubEpochProg fl.pBase)).mem b loc = fastKeyAt fl seeds.bkt s.mem b loc :=
          fastKeyAt_eq_of_fixed_pool hv hg.inv.bp_inv hbp' hoi' hb hl
        exact hbatch_n id b loc u hchk hb hl (hkey.symm.trans hk)
      refine
        { inv := hinv'.toGen 0
          live_sub := hlive_n
          old_sub := fun _ => hold_ok
          try_match := fun h1 => by rw [hta'] at h1; cases h1
          trySalt_le := fun h1 => by rw [hta'] at h1; cases h1
          pot_le := fun _ => by
            rw [hss', Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
            exact drainPotential_rollover_le hv.thresh_le (hinv'.toGen 0) hgood hss' hdp' hta'
              hold_ok }

/-- In the clearing half (`Q / 2 ≤ subStep`, `subStep + 1 < Q`), `advanceSubEpochProg` leaves the
active `BufCur` trie (`fl.trieL fm.curBufRole`) untouched. -/
theorem advanceSubEpochProg_curTrie_half2 {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen 1 fl slack seeds s.mem s_abs)
    (hge : ¬(extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2)
    (hlt : (extractFastMeta fl s.mem).subStep + 1 < qEpochWhp fl.N) :
    extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole)
      ((Memory.spec 0).clientState s (advanceSubEpochProg fl.pBase)).mem =
      extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s.mem := by
  have hr := hinv.ready hv rfl
  have hpt := hinv.param_table
  set fm := extractFastMeta fl s.mem
  have hrole_lt : fm.curBufRole < 2 := hinv.role_lt
  have hold_lt : 1 - fm.curBufRole < 2 := by omega
  have hQ_pos : 0 < qEpochWhp fl.N := by omega
  have hlt_sub : fm.subStep < qEpochWhp fl.N - 1 := by omega
  have hm4 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 4)) = fm.subStep :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hm3 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 3)) = fm.curBufRole :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hq23 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 23)) = qEpochWhp fl.N :=
    hpt 23 (by decide)
  unfold advanceSubEpochProg
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm4,
    StateTransitionSpec.clientState_bind,
    show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 23)) = s from rfl, hq23,
    pure_bind, ite_eq_right hge,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm3,
    ite_eq_left hrole_lt, pure_bind, StateTransitionSpec.clientState_bind,
    ite_eq_left ⟨hQ_pos, hlt_sub⟩]
  have hclr := fastBufClearStepsProg_ready (role := 1 - fm.curBufRole) hr
  have hout := hclr.2.2.2 hold_lt
  have htr_c : extractBufTrie (fl.trieL fm.curBufRole)
      ((Memory.spec 0).clientState s
        (fastBufClearStepsProg (fl.pBase, 1 - fm.curBufRole))).mem =
      extractBufTrie (fl.trieL fm.curBufRole) s.mem := by
    have hfr := (fastTrieMod_frame hv hold_lt hout).2.2.2.2.2.1
    have hrr : 1 - (1 - fm.curBufRole) = fm.curBufRole := by omega
    rwa [hrr] at hfr
  set sc := (Memory.spec 0).clientState s (fastBufClearStepsProg (fl.pBase, 1 - fm.curBufRole))
  have hwm := clientState_fastWriteMetaProg hclr.2.1.2.1 (off := 4) (val := fm.subStep + 1)
    (Or.inl ⟨by decide, by decide⟩)
  rw [hwm]
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have htri_eq : extractBufTrie (fl.trieL fm.curBufRole)
      (Function.update sc.mem (fl.metaBase + 4) (fm.subStep + 1)) =
      extractBufTrie (fl.trieL fm.curBufRole) sc.mem := by
    have h32 : 32 ≤ offBktMeta fl.c fl.w fl.N := hv.mp_valid.offBktMeta_ge
    have hle : offBktMeta fl.c fl.w fl.N ≤ offTrieChild fl.c fl.w fl.N 0 := by
      unfold offTrieChild offBTreeVals offBTreeKeys offBTreeMeta offTailOwner
        offSlabOwner offTailDir offSlabDir; omega
    exact extractBufTrie_congr (show 0 < (fl.trieL fm.curBufRole).w from hw_pos) fun a ha =>
      Function.update_of_ne (fun heq => fl.disj_trie_bpAndMeta hv hrole_lt ha
        (Or.inl ⟨by rw [heq]; omega, by rw [heq]; omega⟩)) _ _
  exact htri_eq.trans htr_c

private theorem bufLookup_bufDelete_none {cTab bChar rKey k : ℕ} {tr : BufTrie}
    (hnone : bufLookup cTab bChar tr k = none) :
    bufLookup cTab bChar (bufDelete cTab bChar tr rKey) k = none := by
  unfold bufDelete
  cases hwk : bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => exact hnone
  | some nd =>
    dsimp only
    by_cases hcond : tr.nodeLeafItem nd = 0 ∨ tr.nodeActive nd = 0
    · rw [ite_eq_left hcond]; exact hnone
    · rw [ite_eq_right hcond]
      unfold bufLookup at hnone ⊢
      cases hwk2 : bufWalk bChar tr.trieChild k cTab 0 0 with
      | none => rfl
      | some leaf =>
        dsimp only at hnone ⊢
        by_cases hleaf : leaf = nd
        · subst hleaf; simp only [Function.update_self, or_true, ↓reduceIte]
        · rw [hwk2] at hnone; dsimp only at hnone ⊢
          simp only [Function.update_of_ne hleaf]
          exact hnone

private theorem drainTryTickProg_oldLookup_none {slackCur : ℕ} {fl : FastEpochLayout}
    {w slack : ℕ} {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State} {rk : ℕ}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hsub : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2)
    (hnone : bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem) rk = none) :
    let s' := (Memory.spec 0).clientState s (drainTryTickProg fl.pBase)
    s'.frontier = s.frontier ∧
    FastEpochInvGen slackCur fl slack seeds s'.mem s_abs ∧
    (extractFastMeta fl s'.mem).curBufRole = (extractFastMeta fl s.mem).curBufRole ∧
    (extractFastMeta fl s'.mem).subStep = (extractFastMeta fl s.mem).subStep ∧
    bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s'.mem).curBufRole)) s'.mem)
      rk = none := by
  dsimp only
  have hpt := hinv.param_table
  set fm := extractFastMeta fl s.mem
  have hm6_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 6)) = fm.tryAct :=
    clientResult_fastReadMetaProg hpt (by decide)
  unfold drainTryTickProg
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm6_r]
  by_cases hta : fm.tryAct = 1
  · rw [ite_eq_left hta, StateTransitionSpec.clientState_bind]
    obtain ⟨hfr1, _, hinv1, _, htr1, _, _, hcr1, hss1, _, _, _, _, _⟩ :=
      drainTryStepProg_spec hv hinv
    set s1 := (Memory.spec 0).clientState s (drainTryStepProg fl.pBase)
    have hrole_lt : fm.curBufRole < 2 := hinv.role_lt
    have hold_lt : 1 - fm.curBufRole < 2 := by omega
    have hnone1 : bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
        (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s1.mem).curBufRole)) s1.mem) rk =
        none := by
      rw [hcr1, htr1 (1 - fm.curBufRole) hold_lt]; exact hnone
    have hm6_1 : (Memory.spec 0).clientResult s1 (fastReadMetaProg (fl.pBase, 6)) =
        (extractFastMeta fl s1.mem).tryAct :=
      clientResult_fastReadMetaProg hinv1.param_table (by decide)
    rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm6_1]
    by_cases hta0 : (extractFastMeta fl s1.mem).tryAct = 0
    · rw [ite_eq_left hta0]
      have hsub1 : (extractFastMeta fl s1.mem).subStep < qEpochWhp fl.N / 2 := by
        rw [hss1]; exact hsub
      obtain ⟨hfr2, _, hinv2, _, _, _, _, hcr2, hss2, _, hnoop, hact⟩ :=
        drainOldSlotProg_spec (hfr1.symm ▸ hv) hinv1 hsub1 hta0
      refine ⟨hfr2.trans hfr1, hinv2, hcr2.trans hcr1, hss2.trans hss1, ?_⟩
      rw [hcr2]
      by_cases hdp : (extractFastMeta fl s1.mem).drainPos <
          (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s1.mem).curBufRole)) s1.mem).itemAlloc
      · rcases hact hdp with ⟨_, _, _, heq, _⟩ | ⟨_, _, _, _, _, _, _, _, _, heq, _⟩ |
            ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heq, _⟩ |
            ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heq, _⟩
        · rw [heq]; exact hnone1
        · rw [heq]; exact bufLookup_bufDelete_none hnone1
        · rw [heq]; exact hnone1
        · rw [heq]; exact hnone1
      · have hs2 := hnoop (Nat.le_of_not_lt hdp)
        dsimp only at hs2; rw [hs2]; exact hnone1
    · rw [ite_eq_right hta0, StateTransitionSpec.clientState_pure]
      exact ⟨hfr1, hinv1, hcr1, hss1, hnone1⟩
  · rw [ite_eq_right hta, StateTransitionSpec.clientState_pure]
    exact ⟨rfl, hinv, rfl, rfl, hnone⟩

/-- Five drain-try ticks preserve absence of an `rKey` from `BufOld` in the drain half. -/
theorem drainTrySteps5Prog_oldLookup_none {slackCur : ℕ} {fl : FastEpochLayout}
    {w slack : ℕ} {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State} {rk : ℕ}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hsub : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2)
    (hnone : bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem) rk = none) :
    let s' := (Memory.spec 0).clientState s (drainTrySteps5Prog fl.pBase)
    bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s'.mem).curBufRole)) s'.mem)
      rk = none := by
  obtain ⟨f1, i1, _, ss1, n1⟩ := drainTryTickProg_oldLookup_none hv hinv hsub hnone
  obtain ⟨f2, i2, _, ss2, n2⟩ :=
    drainTryTickProg_oldLookup_none (f1.symm ▸ hv) i1 (ss1.symm ▸ hsub) n1
  obtain ⟨f3, i3, _, ss3, n3⟩ :=
    drainTryTickProg_oldLookup_none ((f2.trans f1).symm ▸ hv) i2 ((ss2.trans ss1).symm ▸ hsub) n2
  obtain ⟨f4, i4, _, ss4, n4⟩ :=
    drainTryTickProg_oldLookup_none ((f3.trans (f2.trans f1)).symm ▸ hv) i3
      ((ss3.trans (ss2.trans ss1)).symm ▸ hsub) n3
  obtain ⟨_, _, _, _, n5⟩ :=
    drainTryTickProg_oldLookup_none ((f4.trans (f3.trans (f2.trans f1))).symm ▸ hv) i4
      ((ss4.trans (ss3.trans (ss2.trans ss1))).symm ▸ hsub) n4
  unfold drainTrySteps5Prog
  iterate 4 rw [StateTransitionSpec.clientState_bind]
  exact n5

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
