/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.ValidHistoryPool
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpoch
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochSubEpoch
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochDrain
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochAdvance
-- Private deletion/pop helpers shared across the LargeEpochRemBase/LargeEpochRemove split.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochRemBase
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochRemove
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochFast
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpoch

/-!
# Memory History Admissibility (`ValidHistory`) for the Unified Epoch Stack

This module proves `(Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)` for every
public `Memory.Prog` operation exported by `LargeEpochSubEpoch`, `LargeEpochDrain`,
`LargeEpochAdvance`, `LargeEpochRemBase`, `LargeEpochRemove`, `LargeEpochFast`, and `LargeEpoch`.

It uses private `import all` solely to unfold the unexposed `Memory.Prog` bodies of those seven
modules without modifying any existing module.

## Main results

* `validHistory_fastBpInitProg`, `validHistory_fastBpOwnerOfZeroProg`,
  `validHistory_fastBpWriteAtProg`, `validHistory_fastBpAppendProg`,
  `validHistory_fastBpPopBktBackProg`, `validHistory_fastEnterFallbackProg`,
  `validHistory_fastBufInitEmptyProg`, `validHistory_fastBufLookupProg`,
  `validHistory_fastBufInsertProg`, `validHistory_fastBufDeleteProg`,
  `validHistory_fastBufCheckSlotProg`, `validHistory_fastBufClearStepsProg`,
  `validHistory_fastBTreeResetProg`, `validHistory_fastBTreeLookupProg`,
  `validHistory_fastBTreeDeleteProg`, `validHistory_fastBTreeUpdateProg`,
  `validHistory_fastBTreeInsertProg`, `validHistory_fastInitZeroedProg`,
  `validHistory_fastReadBktCntProg`, `validHistory_shadowRoleProg`,
  `validHistory_tryRoleProg`, `validHistory_fastCommitShadowProg`,
  `validHistory_fastShadowStepProg`, `validHistory_fastShadowSteps8Prog`:
  admissibility for `LargeEpochSubEpoch` (`24` operations).
* `validHistory_fastBufItemAllocProg`, `validHistory_advanceTrySaltProg`,
  `validHistory_commitTrySaltProg`, `validHistory_startTrySaltProg`,
  `validHistory_drainTryStepProg`, `validHistory_drainOldSlotProg`:
  admissibility for `LargeEpochDrain` (`6` operations).
* `validHistory_drainTryTickProg`, `validHistory_drainTrySteps5Prog`,
  `validHistory_drainTickProg`, `validHistory_drainTicks16Prog`,
  `validHistory_advanceSubEpochProg`:
  admissibility for `LargeEpochAdvance` (`5` operations).
* `validHistory_fastRemoveAtProg`, `validHistory_fastPopAnyProg`:
  admissibility for `LargeEpochRemBase` (`2` operations).
* `validHistory_fastFallbackQueryProg`, `validHistory_fastFallbackInsertProg`,
  `validHistory_fastFallbackDeleteProg`, `validHistory_fastFallbackPopAnyProg`,
  `validHistory_fastDeleteProg`, `validHistory_fastInsertProg`,
  `validHistory_largeEpochQueryProg`, `validHistory_largeEpochInsertProg`,
  `validHistory_largeEpochDeleteProg`, `validHistory_largeEpochPopAnyProg`:
  admissibility for `LargeEpochFast` (`10` operations).
* `validHistory_epochReadNSideProg`, `validHistory_epochInitZeroedProg`,
  `validHistory_epochQueryProg`, `validHistory_epochInsertProg`,
  `validHistory_epochDeleteProg`, `validHistory_epochPopAnyProg`:
  admissibility for `LargeEpoch` (`6` top-level operations).
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

/-! ## Section 1: Generic `ValidHistory` Combinators -/

private theorem wellFormed_clientState {α : Type} {w : ℕ} {s : Memory.State} {p : Memory.Prog α}
    (hwf : Memory.WellFormed w s)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)) :
    Memory.WellFormed w ((Memory.spec 0).clientState s p) := by
  rw [← clientState_width w, ← (Memory.spec w).run_runClient p s]
  exact hwf.run hp

private theorem validHistory_bind_eq {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : (Memory.spec w).ValidHistory ((Memory.spec 0).clientState s p)
      ((Memory.spec w).clientHistory ((Memory.spec 0).clientState s p)
        (q ((Memory.spec 0).clientResult s p)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) := by
  change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p.bind q))
  rw [validHistory_bind, clientResult_width, clientState_width]
  exact ⟨hp, hq⟩

private theorem validHistory_bind_same {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hst : (Memory.spec 0).clientState s p = s)
    (hq : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (q ((Memory.spec 0).clientResult s p)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) := by
  refine validHistory_bind_eq hp ?_
  rwa [hst]

private theorem validHistory_step {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hwf : Memory.WellFormed w s)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : Memory.WellFormed w ((Memory.spec 0).clientState s p) →
      (Memory.spec w).ValidHistory ((Memory.spec 0).clientState s p)
        ((Memory.spec w).clientHistory ((Memory.spec 0).clientState s p)
          (q ((Memory.spec 0).clientResult s p)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_eq hp (hq (wellFormed_clientState hwf hp))

private theorem validHistory_step_pre {α β : Type} {w pBase : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hwf : Memory.WellFormed w s)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hpre' : FastProgPre w pBase ((Memory.spec 0).clientState s p))
    (hq : Memory.WellFormed w ((Memory.spec 0).clientState s p) →
      FastProgPre w pBase ((Memory.spec 0).clientState s p) →
      (Memory.spec w).ValidHistory ((Memory.spec 0).clientState s p)
        ((Memory.spec w).clientHistory ((Memory.spec 0).clientState s p)
          (q ((Memory.spec 0).clientResult s p)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_eq hp (hq (wellFormed_clientState hwf hp) hpre')

private theorem validHistory_bind_pre {α β : Type} {w pBase : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hpre' : FastProgPre w pBase ((Memory.spec 0).clientState s p))
    (hq : FastProgPre w pBase ((Memory.spec 0).clientState s p) →
      (Memory.spec w).ValidHistory ((Memory.spec 0).clientState s p)
        ((Memory.spec w).clientHistory ((Memory.spec 0).clientState s p)
          (q ((Memory.spec 0).clientResult s p)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_eq hp (hq hpre')

private theorem validHistory_read_bind {α : Type} {w a : ℕ} {s : Memory.State}
    {q : ℕ → Memory.Prog α} (ha : a < s.frontier)
    (hq : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (q (s.mem a)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (Memory.read a >>= q)) :=
  validHistory_bind_eq ⟨ha, trivial⟩ hq

private theorem validHistory_ite {α : Type} {w : ℕ} {s : Memory.State} {c : Prop} [Decidable c]
    {p₁ p₂ : Memory.Prog α}
    (h₁ : c → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p₁))
    (h₂ : ¬c → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p₂)) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (if c then p₁ else p₂)) := by
  by_cases hc : c
  · rw [ite_eq_left hc]; exact h₁ hc
  · rw [ite_eq_right hc]; exact h₂ hc

private theorem epochMetaWords_ge_32 {c w N : ℕ} (ht : whpThreshold c ≤ N) :
    32 ≤ epochMetaWordsWhp c w N := by
  have hend := offEpochEnd_eq_epochMetaWordsWhp (c := c) (w := w) ht
  rw [← hend]
  unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild
    offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
    offBktMeta offFpHash offBktHash
  omega

private theorem bktMeta_frontier_le {fl : FastEpochLayout} {w fr : ℕ}
    (hv : fl.Valid w fr) :
    fl.metaBase + offBktMeta fl.c fl.w fl.N +
      packedWords (16 * numBucketsWhp fl.N) (globalPtrBits fl.N) fl.w ≤ fr := by
  have hmv := hv.mp_valid
  have hd1 := hmv.offSlabDir_ge
  have hd2 := hmv.offTailDir_ge
  have hd3 := hmv.offSlabOwner_ge
  have hd4 := hmv.offTailOwner_ge
  have hfr := hmv.frontier_ge
  dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hd1 hd2 hd3 hd4 hfr
  omega

private theorem validHistory_readParam2Prog {w pBase i j : ℕ} {s : Memory.State}
    (hp : pBase + 64 ≤ s.frontier) (hi : i < 64) (hj : j < 64) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (readParam2Prog (pBase, (i, j)))) := by
  unfold readParam2Prog
  exact validHistory_read_bind (by omega) (validHistory_read_bind (by omega) trivial)

private theorem validHistory_readParam4Prog {w pBase i j k l : ℕ} {s : Memory.State}
    (hp : pBase + 64 ≤ s.frontier) (hi : i < 64) (hj : j < 64) (hk : k < 64) (hl : l < 64) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (readParam4Prog ((pBase, (i, j)), (k, l)))) := by
  unfold readParam4Prog
  refine validHistory_bind_same (validHistory_readParam2Prog hp hi hj)
    (clientState_readParam2Prog _ s) ?_
  exact validHistory_bind_same (validHistory_readParam2Prog hp hk hl)
    (clientState_readParam2Prog _ s) trivial

private theorem two_lt_pow_w {fl : FastEpochLayout} {w fr : ℕ} (hv : fl.Valid w fr) :
    2 < 2 ^ w := by
  have hw6 : 6 ≤ w := hv.w_ge_six
  have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
  omega

private theorem fast_N_lt_pow_w {fl : FastEpochLayout} {w fr : ℕ} (hv : fl.Valid w fr) :
    fl.N < 2 ^ w :=
  lt_of_le_of_lt hv.N_le_U hv.fits_U

private theorem bkt_num_le_N {fl : FastEpochLayout} {w fr : ℕ} (hv : fl.Valid w fr) :
    numBucketsWhp fl.N ≤ fl.N := by
  have hN0 : fl.N ≠ 0 := (lt_of_lt_of_le (whpThreshold_pos fl.c) hv.thresh_le).ne'
  unfold numBucketsWhp bWhp
  exact (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)).trans (Nat.pow_log_le_self 2 hN0)

private theorem fastReadMeta_lt_pow_w {w pBase off : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) (hoff : off < 18) :
    (Memory.spec 0).clientResult s (fastReadMetaProg (pBase, off)) < 2 ^ w := by
  obtain ⟨fl, rfl, _, hpt, _, _⟩ := hpre
  rw [clientResult_fastReadMetaProg hpt hoff]
  exact hwf.2 (fl.metaBase + off)

/-! ## Section 2: `LargeEpochSubEpoch` `ValidHistory` Proofs -/

/-- Memory history admissibility for `fastBpInitProg`. -/
theorem validHistory_fastBpInitProg {w pBase : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBpInitProg pBase)) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  unfold fastBpInitProg
  refine validHistory_bind_same (validHistory_loadBpMetaCtxProg hp)
    (clientState_loadBpMetaCtxProg fl.pBase s) ?_
  rw [clientResult_loadBpMetaCtxProg hpt]
  refine validHistory_bpInitZeroedProg ?_
  rw [BpMetaLayout.ofCtx_toCtx]
  exact hv.mp_valid

/-- Memory history admissibility for `fastBpOwnerOfZeroProg` (read-only). -/
theorem validHistory_fastBpOwnerOfZeroProg {w pBase : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBpOwnerOfZeroProg pBase)) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  unfold fastBpOwnerOfZeroProg
  refine validHistory_bind_same (validHistory_loadBpMetaCtxProg hp)
    (clientState_loadBpMetaCtxProg fl.pBase s) ?_
  rw [clientResult_loadBpMetaCtxProg hpt]
  refine validHistory_bpOwnerOfProg ?_
  rw [BpMetaLayout.ofCtx_toCtx]
  exact hv.mp_valid

/-- Memory history admissibility for `fastBpWriteAtProg`. -/
theorem validHistory_fastBpWriteAtProg {w pBase b loc : ℕ} {qv : ℕ × ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBpWriteAtProg ((pBase, (b, loc)), qv))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  unfold fastBpWriteAtProg
  refine validHistory_bind_same (validHistory_loadBlockPoolCtxProg hp)
    (clientState_loadBlockPoolCtxProg fl.pBase s) ?_
  rw [clientResult_loadBlockPoolCtxProg hpt]
  dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
  exact validHistory_bpWriteAtRawProg hwf
    (by rw [BpMetaLayout.ofCtx_toCtx]; exact hv.mp_valid)
    (by rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid)

/-- Memory history admissibility for `fastBpAppendProg`. -/
theorem validHistory_fastBpAppendProg {w pBase b : ℕ} {qv : ℕ × ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBpAppendProg ((pBase, b), qv))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  unfold fastBpAppendProg
  refine validHistory_bind_same (validHistory_loadBlockPoolCtxProg hp)
    (clientState_loadBlockPoolCtxProg fl.pBase s) ?_
  rw [clientResult_loadBlockPoolCtxProg hpt]
  dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
  exact validHistory_bpAppendRawProg hwf
    (by rw [BpMetaLayout.ofCtx_toCtx]; exact hv.mp_valid)
    (by rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid)

/-- Memory history admissibility for `fastBpPopBktBackProg`. -/
theorem validHistory_fastBpPopBktBackProg {w pBase b : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBpPopBktBackProg (pBase, b))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  unfold fastBpPopBktBackProg
  refine validHistory_bind_same (validHistory_loadBlockPoolCtxProg hp)
    (clientState_loadBlockPoolCtxProg fl.pBase s) ?_
  rw [clientResult_loadBlockPoolCtxProg hpt]
  dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
  exact validHistory_bpPopBktBackRawProg hwf
    (by rw [BpMetaLayout.ofCtx_toCtx]; exact hv.mp_valid)
    (by rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid)

/-- Memory history admissibility for `fastEnterFallbackProg`. -/
theorem validHistory_fastEnterFallbackProg {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastEnterFallbackProg pBase)) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  unfold fastEnterFallbackProg
  refine validHistory_bind_same (validHistory_loadBlockPoolCtxProg hp)
    (clientState_loadBlockPoolCtxProg fl.pBase s) ?_
  rw [clientResult_loadBlockPoolCtxProg hpt]
  dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
  exact validHistory_enterFallbackProg hwf
    (by rw [BpMetaLayout.ofCtx_toCtx]; exact hv.mp_valid)
    (by rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid)

/-- Memory history admissibility for `fastBufInitEmptyProg`. -/
theorem validHistory_fastBufInitEmptyProg {w pBase role : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBufInitEmptyProg (pBase, role))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  unfold fastBufInitEmptyProg
  refine validHistory_ite (fun hrole => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_bind_same
    (validHistory_readParam2Prog hp (by decide) (by split_ifs <;> decide))
    (clientState_readParam2Prog _ s) ?_
  refine validHistory_bind_same
    (validHistory_readParam2Prog hp (by decide) (by decide))
    (clientState_readParam2Prog _ s) ?_
  refine validHistory_read_bind (by omega) ?_
  have hmb : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
  have hpb : s.mem (fl.pBase + 10) = globalPtrBits fl.N := hpt 10 (by decide)
  have hwv : s.mem (fl.pBase + 2) = fl.w := hpt 2 (by decide)
  have hqm : s.mem (fl.pBase + 23) = qEpochWhp fl.N := hpt 23 (by decide)
  have hoi : s.mem (fl.pBase + if role = 0 then 43 else 44) = (fl.trieL role).offItem := by
    by_cases hr0 : role = 0
    · subst hr0; rw [ite_eq_left rfl]; exact hpt 43 (by decide)
    · have hr1 : role = 1 := by omega
      subst hr1; rw [ite_eq_right (by decide)]; exact hpt 44 (by decide)
  have hmbOi : (Memory.spec 0).clientResult s
      (readParam2Prog (fl.pBase, (1, if role = 0 then 43 else 44))) =
      (fl.metaBase, (fl.trieL role).offItem) := Prod.ext hmb hoi
  have hpbw : (Memory.spec 0).clientResult s (readParam2Prog (fl.pBase, (10, 2))) =
      (globalPtrBits fl.N, fl.w) := Prod.ext hpb hwv
  rw [hmbOi, hpbw, hqm]
  have htv := hv.trie_valid hrole
  obtain ⟨hw_pos, _, hpb_le, _, _, _, _, _, _, _, _, _, _, _, _, hfr_i⟩ := htv
  dsimp only [FastEpochLayout.trieL, epochTrieLayout] at hpb_le hfr_i
  have hw_eq := hv.w_eq
  exact validHistory_writePackedCompGen hwf
    ⟨6 * qEpochWhp fl.N + 6, hv.w_pos, hw_eq, by rwa [hw_eq], by omega,
      by dsimp only [FastEpochLayout.trieL, epochTrieLayout]; rw [hw_eq]; exact hfr_i⟩

/-- Memory history admissibility for `fastBufLookupProg` (read-only). -/
theorem validHistory_fastBufLookupProg {w pBase role rk : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBufLookupProg ((pBase, role), rk))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  unfold fastBufLookupProg
  refine validHistory_ite (fun hrole => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_loadTrieCtxProg hp)
    (clientState_loadTrieCtxProg _ s) ?_
  rw [clientResult_loadTrieCtxProg hpt hrole]
  refine validHistory_bufLookupBoundedProg ?_
  rw [TrieLayout.ofCtx_toCtx, hv.w_eq]
  exact hv.trie_valid hrole

/-- Memory history admissibility for `fastBufInsertProg`. -/
theorem validHistory_fastBufInsertProg {w pBase role : ℕ} {rbl : ℕ × (ℕ × ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBufInsertProg ((pBase, role), rbl))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  unfold fastBufInsertProg
  refine validHistory_ite (fun hrole => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_loadTrieCtxProg hp)
    (clientState_loadTrieCtxProg _ s) ?_
  rw [clientResult_loadTrieCtxProg hpt hrole]
  rcases rbl with ⟨rk, ⟨b, loc⟩⟩
  refine validHistory_bufInsertBoundedProg hwf ?_
  rw [TrieLayout.ofCtx_toCtx, hv.w_eq]
  exact hv.trie_valid hrole

/-- Memory history admissibility for `fastBufDeleteProg`. -/
theorem validHistory_fastBufDeleteProg {w pBase role rk : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBufDeleteProg ((pBase, role), rk))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  unfold fastBufDeleteProg
  refine validHistory_ite (fun hrole => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_loadTrieCtxProg hp)
    (clientState_loadTrieCtxProg _ s) ?_
  rw [clientResult_loadTrieCtxProg hpt hrole]
  refine validHistory_bufDeleteBoundedProg hwf ?_
  rw [TrieLayout.ofCtx_toCtx, hv.w_eq]
  exact hv.trie_valid hrole

/-- Memory history admissibility for `fastBufCheckSlotProg` (read-only). -/
theorem validHistory_fastBufCheckSlotProg {w pBase role id : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBufCheckSlotProg ((pBase, role), id))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  unfold fastBufCheckSlotProg
  refine validHistory_ite (fun hrole => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_loadTrieCtxProg hp)
    (clientState_loadTrieCtxProg _ s) ?_
  rw [clientResult_loadTrieCtxProg hpt hrole]
  refine validHistory_bufCheckSlotBoundedProg ?_
  rw [TrieLayout.ofCtx_toCtx, hv.w_eq]
  exact hv.trie_valid hrole

/-- Memory history admissibility for `fastBufClearStepsProg`. -/
theorem validHistory_fastBufClearStepsProg {w pBase role : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBufClearStepsProg (pBase, role))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  unfold fastBufClearStepsProg
  refine validHistory_ite (fun hrole => ?_) (fun _ => trivial)
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_same (validHistory_loadTrieCtxProg hp)
    (clientState_loadTrieCtxProg _ s) ?_
  rw [clientResult_loadTrieCtxProg hpt hrole]
  refine validHistory_bufClearStepsBoundedProg hwf ?_
  rw [TrieLayout.ofCtx_toCtx, hv.w_eq]
  exact hv.trie_valid hrole

/-- Memory history admissibility for `fastBTreeResetProg`. -/
theorem validHistory_fastBTreeResetProg {w pBase b role : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBTreeResetProg (pBase, (b, role)))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  have hm1 : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
  have hm31 : s.mem (fl.pBase + 31) = offBktMeta fl.c fl.w fl.N := hpt 31 (by decide)
  have hm10 : s.mem (fl.pBase + 10) = globalPtrBits fl.N := hpt 10 (by decide)
  have hm2 : s.mem (fl.pBase + 2) = fl.w := hpt 2 (by decide)
  have hpb_le := hv.mp_valid.ptrB_le
  dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hpb_le
  have hfr_bm := bktMeta_frontier_le hv
  have hw_eq := hv.w_eq
  unfold fastBTreeResetProg
  refine validHistory_read_bind (by omega) ?_
  rw [hm11]
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  obtain ⟨hb, hrole⟩ := hcond
  refine validHistory_bind_same (validHistory_readParam2Prog hp (by decide) (by decide))
    (clientState_readParam2Prog _ s) ?_
  refine validHistory_bind_same (validHistory_readParam2Prog hp (by decide) (by decide))
    (clientState_readParam2Prog _ s) ?_
  have hmbObm : (Memory.spec 0).clientResult s (readParam2Prog (fl.pBase, (1, 31))) =
      (fl.metaBase, offBktMeta fl.c fl.w fl.N) := Prod.ext hm1 hm31
  have hpbw : (Memory.spec 0).clientResult s (readParam2Prog (fl.pBase, (10, 2))) =
      (globalPtrBits fl.N, fl.w) := Prod.ext hm10 hm2
  rw [hmbObm, hpbw]
  refine validHistory_step hwf (validHistory_writePackedCompGen hwf
    ⟨16 * numBucketsWhp fl.N, hv.w_pos, hw_eq, by omega, by omega, by rwa [hw_eq]⟩)
    fun hwf₁ => ?_
  have hfr_le : s.frontier ≤ ((Memory.spec 0).clientState s
      (writePackedCompGenProg ((((fl.metaBase, offBktMeta fl.c fl.w fl.N),
        (globalPtrBits fl.N, fl.w)), 16 * b + 6 + 2 * role), 0))).frontier := by
    rw [← (Memory.spec 0).run_runClient _ s]
    exact Memory.frontier_le_run s _
  exact validHistory_writePackedCompGen hwf₁
    ⟨16 * numBucketsWhp fl.N, hv.w_pos, hw_eq, by omega, by omega,
      by rw [hw_eq]; exact hfr_bm.trans hfr_le⟩

/-- Memory history admissibility for `fastBTreeLookupProg` (read-only). -/
theorem validHistory_fastBTreeLookupProg {w pBase b role q : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBTreeLookupProg ((pBase, (b, role)), q))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  unfold fastBTreeLookupProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_same (validHistory_readParam2Prog hp (by decide) (by decide))
    (clientState_readParam2Prog _ s) ?_
  rw [hm11]
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  obtain ⟨hb, hrole, _⟩ := hcond
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_loadBTreeSliceCtxProg hp)
    (clientState_loadBTreeSliceCtxProg _ s) ?_
  rw [clientResult_loadBTreeSliceCtxProg hpt]
  have hbtv := hv.bt_valid
  rw [← hv.w_eq] at hbtv
  exact validHistory_btreeLookupBoundedProg ⟨hbtv, hb, hrole⟩

/-- Memory history admissibility for `fastBTreeDeleteProg`. -/
theorem validHistory_fastBTreeDeleteProg {w pBase b role q : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBTreeDeleteProg ((pBase, (b, role)), q))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  unfold fastBTreeDeleteProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_same (validHistory_readParam2Prog hp (by decide) (by decide))
    (clientState_readParam2Prog _ s) ?_
  rw [hm11]
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  obtain ⟨hb, hrole, _⟩ := hcond
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_loadBTreeSliceCtxProg hp)
    (clientState_loadBTreeSliceCtxProg _ s) ?_
  rw [clientResult_loadBTreeSliceCtxProg hpt]
  have hbtv := hv.bt_valid
  rw [← hv.w_eq] at hbtv
  exact validHistory_btreeDeleteBoundedProg hwf ⟨hbtv, hb, hrole⟩

/-- Memory history admissibility for `fastBTreeUpdateProg`. -/
theorem validHistory_fastBTreeUpdateProg {w pBase b role q newVal : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastBTreeUpdateProg ((pBase, (b, role)), (q, newVal)))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  unfold fastBTreeUpdateProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_same
    (validHistory_readParam4Prog hp (by decide) (by decide) (by decide) (by decide))
    (clientState_readParam4Prog _ s) ?_
  dsimp only; rw [hm11]
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  obtain ⟨hb, hrole, _⟩ := hcond
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_loadBTreeSliceCtxProg hp)
    (clientState_loadBTreeSliceCtxProg _ s) ?_
  rw [clientResult_loadBTreeSliceCtxProg hpt]
  have hbtv := hv.bt_valid
  rw [← hv.w_eq] at hbtv
  exact validHistory_btreeUpdateBoundedProg hwf ⟨hbtv, hb, hrole⟩

/-- Memory history admissibility for `fastBTreeInsertProg`. -/
theorem validHistory_fastBTreeInsertProg {w pBase b role q val : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastBTreeInsertProg ((pBase, (b, role)), (q, val)))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  unfold fastBTreeInsertProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_same
    (validHistory_readParam4Prog hp (by decide) (by decide) (by decide) (by decide))
    (clientState_readParam4Prog _ s) ?_
  dsimp only; rw [hm11]
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  obtain ⟨hb, hrole, _⟩ := hcond
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_loadBTreeSliceCtxProg hp)
    (clientState_loadBTreeSliceCtxProg _ s) ?_
  rw [clientResult_loadBTreeSliceCtxProg hpt]
  have hbtv := hv.bt_valid
  rw [← hv.w_eq] at hbtv
  exact validHistory_btreeInsertBoundedProg hwf ⟨hbtv, hb, hrole⟩

/-- Memory history admissibility for `fastInitZeroedProg`. -/
theorem validHistory_fastInitZeroedProg {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastInitZeroedProg pBase)) := by
  unfold fastInitZeroedProg
  refine validHistory_step hwf (validHistory_fastBpInitProg hpre) fun hwf₁ => ?_
  have hpre₁ := fastBpInitProg_pre hpre
  refine validHistory_step hwf₁ (validHistory_fastBufInitEmptyProg hwf₁ hpre₁) fun hwf₂ => ?_
  have hpre₂ := fastBufInitEmptyProg_pre (x := (pBase, 0)) hpre₁
  exact validHistory_fastBufInitEmptyProg hwf₂ hpre₂

/-- Memory history admissibility for `fastReadBktCntProg` (read-only). -/
theorem validHistory_fastReadBktCntProg {w pBase b : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastReadBktCntProg (pBase, b))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  unfold fastReadBktCntProg
  refine validHistory_bind_same (validHistory_loadBpMetaCtxProg hp)
    (clientState_loadBpMetaCtxProg fl.pBase s) ?_
  rw [clientResult_loadBpMetaCtxProg hpt]
  refine validHistory_bpReadBktCountProg ?_
  rw [BpMetaLayout.ofCtx_toCtx]
  exact hv.mp_valid

/-- Unconditional memory history admissibility for `shadowRoleProg` (pure arithmetic). -/
theorem validHistory_shadowRoleProg (w r : ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (shadowRoleProg r)) := by
  unfold shadowRoleProg
  exact validHistory_ite (fun _ => trivial) fun _ =>
    validHistory_ite (fun _ => trivial) (fun _ => trivial)

/-- Unconditional memory history admissibility for `tryRoleProg` (pure arithmetic). -/
theorem validHistory_tryRoleProg (w r : ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (tryRoleProg r)) := by
  unfold tryRoleProg
  exact validHistory_ite (fun _ => trivial) fun _ =>
    validHistory_ite (fun _ => trivial) (fun _ => trivial)

/-- Memory history admissibility for `fastCommitShadowProg`. -/
theorem validHistory_fastCommitShadowProg {w pBase b shRole shIns : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastCommitShadowProg (pBase, (b, (shRole, shIns))))) := by
  unfold fastCommitShadowProg
  refine validHistory_step hwf (validHistory_fastWriteBktLaneProg hwf hpre) fun hwf₁ => ?_
  have hpre₁ := fastWriteBktLaneProg_pre (x := ((pBase, (b, 12)), shRole)) hpre
  refine validHistory_step hwf₁ (validHistory_fastWriteBktLaneProg hwf₁ hpre₁) fun hwf₂ => ?_
  have hpre₂ := fastWriteBktLaneProg_pre (x := ((pBase, (b, 13)), shIns)) hpre₁
  refine validHistory_step hwf₂ (validHistory_fastWriteBktLaneProg hwf₂ hpre₂) fun hwf₃ => ?_
  have hpre₃ := fastWriteBktLaneProg_pre (x := ((pBase, (b, 14)), 0)) hpre₂
  exact validHistory_fastWriteBktLaneProg hwf₃ hpre₃

private theorem validHistory_fastShadowAdvanceProg {w pBase b shPos cnt shRole shIns' : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastShadowAdvanceProg ((pBase, b), ((shPos, cnt), (shRole, shIns'))))) := by
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre
  unfold fastShadowAdvanceProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_fastCommitShadowProg hwf hpre)
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_fastCommitShadowProg hwf hpre)
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_fastCommitShadowProg hwf hpre)
  refine validHistory_step hwf (validHistory_fastWriteBktLaneProg hwf hpre) fun hwf₁ => ?_
  have hpre₁ := fastWriteBktLaneProg_pre (x := ((pBase, (b, 14)), shIns')) hpre
  exact validHistory_fastWriteBktLaneProg hwf₁ hpre₁

private theorem validHistory_fastShadowBodyTailProg {w pBase b shPos cnt fp : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastShadowBodyTailProg (((pBase, b), (shPos, cnt)), fp))) := by
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre
  unfold fastShadowBodyTailProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastBTreeLookupProg hpre)
    (clientState_fastBTreeLookupProg _ s) ?_
  refine validHistory_bind_same (validHistory_shadowRoleProg w _ s)
    (clientState_shadowRoleProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_ite (fun _ => ?_)
    (fun _ => validHistory_fastShadowAdvanceProg hwf hpre)
  refine validHistory_step_pre hwf (validHistory_fastBTreeInsertProg hwf hpre)
    (fastBTreeInsertProg_pre hpre) fun hwf₁ hpre₁ => ?_
  exact validHistory_fastShadowAdvanceProg hwf₁ hpre₁

private theorem validHistory_fastShadowBodyProg {w pBase b shPos cnt : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastShadowBodyProg ((pBase, b), (shPos, cnt)))) := by
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre
  unfold fastShadowBodyProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastBpReadAtProg hpre)
    (clientState_fastBpReadAtProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastFeistelReconProg hpre)
    (clientState_fastFeistelReconProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastFpHashProg hpre)
    (clientState_fastFpHashProg _ s) ?_
  exact validHistory_fastShadowBodyTailProg hwf hpre

/-- Memory history admissibility for `fastShadowStepProg`. -/
theorem validHistory_fastShadowStepProg {w pBase b : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastShadowStepProg (pBase, b))) := by
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre
  unfold fastShadowStepProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastReadBktCntProg hpre)
    (clientState_fastReadBktCntProg _ s) ?_
  exact validHistory_fastShadowBodyProg hwf hpre

private theorem validHistory_fastShadowSteps2Prog {w pBase b : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastShadowSteps2Prog (pBase, b))) := by
  unfold fastShadowSteps2Prog
  refine validHistory_step hwf (validHistory_fastShadowStepProg hwf hpre) fun hwf₁ => ?_
  exact validHistory_fastShadowStepProg hwf₁ (fastShadowStepProg_pre (x := (pBase, b)) hpre)

private theorem validHistory_fastShadowSteps4Prog {w pBase b : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastShadowSteps4Prog (pBase, b))) := by
  unfold fastShadowSteps4Prog
  refine validHistory_step hwf (validHistory_fastShadowSteps2Prog hwf hpre) fun hwf₁ => ?_
  exact validHistory_fastShadowSteps2Prog hwf₁ (fastShadowSteps2Prog_pre (x := (pBase, b)) hpre)

/-- Memory history admissibility for `fastShadowSteps8Prog`. -/
theorem validHistory_fastShadowSteps8Prog {w pBase b : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastShadowSteps8Prog (pBase, b))) := by
  unfold fastShadowSteps8Prog
  refine validHistory_step hwf (validHistory_fastShadowSteps4Prog hwf hpre) fun hwf₁ => ?_
  exact validHistory_fastShadowSteps4Prog hwf₁ (fastShadowSteps4Prog_pre (x := (pBase, b)) hpre)

/-! ## Section 3: `LargeEpochDrain` `ValidHistory` Proofs -/

private theorem validHistory_readTrieItemAllocCtxProg {w : ℕ} {tctx : TrieCtx}
    {s : Memory.State} (htv : (TrieLayout.ofCtx tctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (readTrieItemAllocCtxProg tctx)) := by
  rcases tctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  unfold readTrieItemAllocCtxProg
  dsimp only [TrieLayout.ofCtx] at htv
  obtain ⟨hw_pos, hwv, hpb, _, _, _, _, _, _, _, _, _, _, _, _, hfr⟩ := htv
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  exact validHistory_readPackedCompGen
    ⟨6 * qm + 6, hw_pos, hwv, hpb, by omega, by rwa [hwv]⟩

/-- Memory history admissibility for `fastBufItemAllocProg` (read-only). -/
theorem validHistory_fastBufItemAllocProg {w pBase role : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBufItemAllocProg (pBase, role))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  unfold fastBufItemAllocProg
  refine validHistory_ite (fun hrole => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_loadTrieCtxProg hp)
    (clientState_loadTrieCtxProg _ s) ?_
  rw [clientResult_loadTrieCtxProg hpt hrole]
  refine validHistory_readTrieItemAllocCtxProg ?_
  rw [TrieLayout.ofCtx_toCtx, hv.w_eq]
  exact hv.trie_valid hrole

private theorem validHistory_writeTryResetMetaProg {w pBase nextSalt : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) (hns : nextSalt < 2 ^ w) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writeTryResetMetaProg (pBase, nextSalt))) := by
  have h0 : 0 < 2 ^ w := Nat.two_pow_pos w
  unfold writeTryResetMetaProg
  refine validHistory_bind_eq (validHistory_fastWriteMetaProg hpre hns) ?_
  have hpre₁ := fastWriteMetaProg_pre (x := ((pBase, 8), nextSalt)) hpre
  refine validHistory_bind_eq (validHistory_fastWriteMetaProg hpre₁ h0) ?_
  have hpre₂ := fastWriteMetaProg_pre (x := ((pBase, 9), 0)) hpre₁
  exact validHistory_fastWriteMetaProg hpre₂ h0

private theorem validHistory_nextSaltProg (w ts sMax : ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (nextSaltProg (ts, sMax))) := by
  unfold nextSaltProg
  exact validHistory_ite
    (fun _ => validHistory_ite (fun _ => trivial) (fun _ => trivial))
    (fun _ => trivial)

/-- Memory history admissibility for `advanceTrySaltProg`. -/
theorem validHistory_advanceTrySaltProg {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (advanceTrySaltProg pBase)) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  have hpre0 : FastProgPre w fl.pBase s := ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre0
  have hm24 : s.mem (fl.pBase + 24) = sMaxWhp fl.c fl.N := hpt 24 (by decide)
  obtain ⟨_, _, hsMax_le, _⟩ := hv.bounds_le_N
  have hN_lt : fl.N < 2 ^ w := fast_N_lt_pow_w hv
  unfold advanceTrySaltProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre0)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre0)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_read_bind (by omega) ?_
  rw [hm24]
  refine validHistory_bind_same (validHistory_nextSaltProg w _ _ s)
    (clientState_nextSaltProg _ s) ?_
  have hns_lt : (Memory.spec 0).clientResult s
      (nextSaltProg ((Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 8)),
        sMaxWhp fl.c fl.N)) < 2 ^ w := by
    rw [clientResult_nextSaltProg]
    split_ifs <;> omega
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre0)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_tryRoleProg w _ s)
    (clientState_tryRoleProg _ s) ?_
  refine validHistory_bind_pre (validHistory_fastBTreeResetProg hwf hpre0)
    (fastBTreeResetProg_pre hpre0) fun hpre₁ => ?_
  exact validHistory_writeTryResetMetaProg hpre₁ hns_lt

private theorem validHistory_clearTryMetaProg {w pBase : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (clearTryMetaProg pBase)) := by
  have h0 : 0 < 2 ^ w := Nat.two_pow_pos w
  unfold clearTryMetaProg
  refine validHistory_bind_eq (validHistory_fastWriteMetaProg hpre h0) ?_
  have hpre₁ := fastWriteMetaProg_pre (x := ((pBase, 6), 0)) hpre
  refine validHistory_bind_eq (validHistory_fastWriteMetaProg hpre₁ h0) ?_
  have hpre₂ := fastWriteMetaProg_pre (x := ((pBase, 9), 0)) hpre₁
  exact validHistory_fastWriteMetaProg hpre₂ h0

/-- Memory history admissibility for `commitTrySaltProg`. -/
theorem validHistory_commitTrySaltProg {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (commitTrySaltProg pBase)) := by
  unfold commitTrySaltProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_tryRoleProg w _ s)
    (clientState_tryRoleProg _ s) ?_
  refine validHistory_step_pre hwf (validHistory_fastWriteBktLaneProg hwf hpre)
    (fastWriteBktLaneProg_pre hpre) fun hwf₁ hpre₁ => ?_
  refine validHistory_step_pre hwf₁ (validHistory_fastWriteBktLaneProg hwf₁ hpre₁)
    (fastWriteBktLaneProg_pre hpre₁) fun hwf₂ hpre₂ => ?_
  refine validHistory_bind_pre (validHistory_fastWriteBktLaneProg hwf₂ hpre₂)
    (fastWriteBktLaneProg_pre hpre₂) fun hpre₃ => ?_
  exact validHistory_clearTryMetaProg hpre₃

private theorem validHistory_writeStartTryMetaProg {w pBase b : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) (hb : b < 2 ^ w) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writeStartTryMetaProg (pBase, b))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  have hpre0 : FastProgPre w fl.pBase s := ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  have h2 := two_lt_pow_w hv
  unfold writeStartTryMetaProg
  refine validHistory_bind_eq (validHistory_fastWriteMetaProg hpre0 (by omega)) ?_
  have hpre₁ := fastWriteMetaProg_pre (x := ((fl.pBase, 6), 1)) hpre0
  refine validHistory_bind_eq (validHistory_fastWriteMetaProg hpre₁ hb) ?_
  have hpre₂ := fastWriteMetaProg_pre (x := ((fl.pBase, 7), b)) hpre₁
  exact validHistory_writeTryResetMetaProg hpre₂ (by omega)

/-- Memory history admissibility for `startTrySaltProg` (requires `b < 2 ^ w`). -/
theorem validHistory_startTrySaltProg {w pBase b : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) (hb : b < 2 ^ w) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (startTrySaltProg (pBase, b))) := by
  unfold startTrySaltProg
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_tryRoleProg w _ s)
    (clientState_tryRoleProg _ s) ?_
  refine validHistory_bind_pre (validHistory_fastBTreeResetProg hwf hpre)
    (fastBTreeResetProg_pre hpre) fun hpre₁ => ?_
  exact validHistory_writeStartTryMetaProg hpre₁ hb

private theorem validHistory_drainTryCheckDpInnerProg {w pBase b loc ts : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (drainTryCheckDpInnerProg ((pBase, b), (loc, ts)))) := by
  unfold drainTryCheckDpInnerProg
  refine validHistory_bind_same (validHistory_fastReadBktCntProg hpre)
    (clientState_fastReadBktCntProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastBpReadAtProg hpre)
    (clientState_fastBpReadAtProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastFeistelReconProg hpre)
    (clientState_fastFeistelReconProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastFpHashProg hpre)
    (clientState_fastFpHashProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_tryRoleProg w _ s)
    (clientState_tryRoleProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastBTreeLookupProg hpre)
    (clientState_fastBTreeLookupProg _ s) trivial

private theorem validHistory_drainTryCheckDpProg {w pBase : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (drainTryCheckDpProg pBase)) := by
  unfold drainTryCheckDpProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastBufCheckSlotProg hpre)
    (clientState_fastBufCheckSlotProg _ s) ?_
  exact validHistory_ite (fun _ => validHistory_drainTryCheckDpInnerProg hpre)
    (fun _ => trivial)

private theorem validHistory_drainTryInsertOrAdvProg {w pBase b tp cRole u_val : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (drainTryInsertOrAdvProg (((pBase, b), (tp, cRole)), u_val))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  have hpre0 : FastProgPre w fl.pBase s := ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre0
  have hm0 : s.mem (fl.pBase + 0) = fl.N := hpt 0 (by decide)
  have hN_lt : fl.N < 2 ^ w := fast_N_lt_pow_w hv
  unfold drainTryInsertOrAdvProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre0)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastFpHashProg hpre0)
    (clientState_fastFpHashProg _ s) ?_
  refine validHistory_bind_same (validHistory_tryRoleProg w _ s)
    (clientState_tryRoleProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastBTreeLookupProg hpre0)
    (clientState_fastBTreeLookupProg _ s) ?_
  refine validHistory_ite (fun _ => validHistory_advanceTrySaltProg hwf hpre0) fun _ => ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre0)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_read_bind (by omega) ?_
  rw [hm0]
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  obtain ⟨hti, htp⟩ := hcond
  refine validHistory_bind_pre (validHistory_fastBTreeInsertProg hwf hpre0)
    (fastBTreeInsertProg_pre hpre0) fun hpre₁ => ?_
  refine validHistory_bind_pre (validHistory_fastWriteMetaProg hpre₁ (by omega))
    (fastWriteMetaProg_pre hpre₁) fun hpre₂ => ?_
  exact validHistory_fastWriteMetaProg hpre₂ (by omega)

private theorem validHistory_drainTryScanSlotProg {w pBase b tp : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (drainTryScanSlotProg ((pBase, b), tp))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  have hpre0 : FastProgPre w fl.pBase s := ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre0
  have hm0 : s.mem (fl.pBase + 0) = fl.N := hpt 0 (by decide)
  have hN_lt : fl.N < 2 ^ w := fast_N_lt_pow_w hv
  unfold drainTryScanSlotProg
  refine validHistory_bind_same (validHistory_fastBpReadAtProg hpre0)
    (clientState_fastBpReadAtProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastFeistelReconProg hpre0)
    (clientState_fastFeistelReconProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre0)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre0)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastFpHashProg hpre0)
    (clientState_fastFpHashProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastBTreeLookupProg hpre0)
    (clientState_fastBTreeLookupProg _ s) ?_
  refine validHistory_ite (fun _ => validHistory_drainTryInsertOrAdvProg hwf hpre0) fun _ => ?_
  refine validHistory_read_bind (by omega) ?_
  rw [hm0]
  exact validHistory_ite (fun htp => validHistory_fastWriteMetaProg hpre0 (by omega))
    (fun _ => trivial)

/-- Memory history admissibility for `drainTryStepProg`. -/
theorem validHistory_drainTryStepProg {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (drainTryStepProg pBase)) := by
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre
  unfold drainTryStepProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastReadBktCntProg hpre)
    (clientState_fastReadBktCntProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_ite (fun _ => validHistory_drainTryScanSlotProg hwf hpre) fun _ => ?_
  refine validHistory_bind_same (validHistory_drainTryCheckDpProg hpre)
    (runClient_state_drainTryCheckDpProg pBase s) ?_
  exact validHistory_ite
    (fun _ => validHistory_commitTrySaltProg hwf hpre)
    (fun _ => validHistory_advanceTrySaltProg hwf hpre)

private theorem validHistory_drainOldShadowMaintProg {w pBase b fp loc cIns' : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (drainOldShadowMaintProg (((pBase, b), (fp, loc)), cIns'))) := by
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre
  unfold drainOldShadowMaintProg
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_shadowRoleProg w _ s)
    (clientState_shadowRoleProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
  · refine validHistory_read_bind (by omega) ?_
    refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
    refine validHistory_step_pre hwf (validHistory_fastBTreeResetProg hwf hpre)
      (fastBTreeResetProg_pre hpre) fun hwf₁ hpre₁ => ?_
    refine validHistory_step_pre hwf₁ (validHistory_fastWriteBktLaneProg hwf₁ hpre₁)
      (fastWriteBktLaneProg_pre hpre₁) fun hwf₂ hpre₂ => ?_
    exact validHistory_fastWriteBktLaneProg hwf₂ hpre₂
  · refine validHistory_read_bind (by omega) ?_
    refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
    refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
    refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
      (clientState_fastReadBktLaneProg _ s) ?_
    refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
    refine validHistory_step_pre hwf (validHistory_fastBTreeInsertProg hwf hpre)
      (fastBTreeInsertProg_pre hpre) fun hwf₁ hpre₁ => ?_
    exact validHistory_fastWriteBktLaneProg hwf₁ hpre₁

private theorem validHistory_drainOldInsertNoCollProg {w pBase oldRole dp rk b fp loc : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (drainOldInsertNoCollProg (((pBase, oldRole), (dp, rk)), (b, (fp, loc))))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  have hpre0 : FastProgPre w fl.pBase s := ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre0
  have hm23 : s.mem (fl.pBase + 23) = qEpochWhp fl.N := hpt 23 (by decide)
  obtain ⟨_, _, _, hq_le⟩ := hv.bounds_le_N
  have hN_lt : fl.N < 2 ^ w := fast_N_lt_pow_w hv
  unfold drainOldInsertNoCollProg
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre0)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre0)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_read_bind (by omega) ?_
  rw [hm23]
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  obtain ⟨_, hdp⟩ := hcond
  refine validHistory_step_pre hwf (validHistory_fastBTreeInsertProg hwf hpre0)
    (fastBTreeInsertProg_pre hpre0) fun hwf₁ hpre₁ => ?_
  refine validHistory_step_pre hwf₁ (validHistory_fastWriteBktLaneProg hwf₁ hpre₁)
    (fastWriteBktLaneProg_pre hpre₁) fun hwf₂ hpre₂ => ?_
  refine validHistory_step_pre hwf₂ (validHistory_drainOldShadowMaintProg hwf₂ hpre₂)
    (drainOldShadowMaintProg_pre hpre₂) fun hwf₃ hpre₃ => ?_
  refine validHistory_bind_pre (validHistory_fastBufDeleteProg hwf₃ hpre₃)
    (fastBufDeleteProg_pre hpre₃) fun hpre₄ => ?_
  exact validHistory_fastWriteMetaProg hpre₄ (by omega)

private theorem validHistory_drainOldActiveBodyProg {w pBase oldRole dp b loc : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (drainOldActiveBodyProg ((pBase, oldRole), (dp, (b, loc))))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  have hpre0 : FastProgPre w fl.pBase s := ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre0
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  have hM_le : numBucketsWhp fl.N ≤ fl.N := bkt_num_le_N hv
  have hN_lt : fl.N < 2 ^ w := fast_N_lt_pow_w hv
  unfold drainOldActiveBodyProg
  refine validHistory_bind_same (validHistory_fastReadBktCntProg hpre0)
    (clientState_fastReadBktCntProg _ s) ?_
  refine validHistory_read_bind (by omega) ?_
  rw [hm11]
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  obtain ⟨hb, _⟩ := hcond
  refine validHistory_bind_same (validHistory_fastBpReadAtProg hpre0)
    (clientState_fastBpReadAtProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastFeistelReconProg hpre0)
    (clientState_fastFeistelReconProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastRKeyProg hpre0)
    (clientState_fastRKeyProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre0)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre0)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastFpHashProg hpre0)
    (clientState_fastFpHashProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastBTreeLookupProg hpre0)
    (clientState_fastBTreeLookupProg _ s) ?_
  refine validHistory_ite
    (fun _ => validHistory_drainOldInsertNoCollProg hwf hpre0) fun _ => ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre0)
    (clientState_fastReadBktLaneProg _ s) ?_
  exact validHistory_ite
    (fun _ => validHistory_startTrySaltProg hwf hpre0 (by omega))
    (fun _ => trivial)

/-- Memory history admissibility for `drainOldSlotProg`. -/
theorem validHistory_drainOldSlotProg {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (drainOldSlotProg pBase)) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  have hpre0 : FastProgPre w fl.pBase s := ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre0
  have hm23 : s.mem (fl.pBase + 23) = qEpochWhp fl.N := hpt 23 (by decide)
  obtain ⟨_, _, _, hq_le⟩ := hv.bounds_le_N
  have hN_lt : fl.N < 2 ^ w := fast_N_lt_pow_w hv
  unfold drainOldSlotProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre0)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre0)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_read_bind (by omega) ?_
  rw [hm23]
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_bind_same (validHistory_fastBufItemAllocProg hpre0)
    (clientState_fastBufItemAllocProg _ s) ?_
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  obtain ⟨hia_le, hdp_lt⟩ := hcond
  refine validHistory_bind_same (validHistory_fastBufCheckSlotProg hpre0)
    (clientState_fastBufCheckSlotProg _ s) ?_
  refine validHistory_ite
    (fun _ => validHistory_fastWriteMetaProg hpre0 (by omega)) fun _ => ?_
  refine validHistory_step_pre hwf (validHistory_fastShadowSteps8Prog hwf hpre0)
    (fastShadowSteps8Prog_pre hpre0) fun hwf₁ hpre₁ => ?_
  exact validHistory_drainOldActiveBodyProg hwf₁ hpre₁

/-! ## Section 4: `LargeEpochAdvance` `ValidHistory` Proofs -/

/-- Memory history admissibility for `drainTryTickProg`. -/
theorem validHistory_drainTryTickProg {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (drainTryTickProg pBase)) := by
  unfold drainTryTickProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_step hwf (validHistory_drainTryStepProg hwf hpre) fun hwf₁ => ?_
  have hpre₁ := drainTryStepProg_pre hpre
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre₁)
    (clientState_fastReadMetaProg _ _) ?_
  exact validHistory_ite
    (fun _ => validHistory_drainOldSlotProg hwf₁ hpre₁) (fun _ => trivial)

/-- Memory history admissibility for `drainTrySteps5Prog`. -/
theorem validHistory_drainTrySteps5Prog {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (drainTrySteps5Prog pBase)) := by
  unfold drainTrySteps5Prog
  refine validHistory_step hwf (validHistory_drainTryTickProg hwf hpre) fun hwf₁ => ?_
  have hpre₁ := drainTryTickProg_pre hpre
  refine validHistory_step hwf₁ (validHistory_drainTryTickProg hwf₁ hpre₁) fun hwf₂ => ?_
  have hpre₂ := drainTryTickProg_pre hpre₁
  refine validHistory_step hwf₂ (validHistory_drainTryTickProg hwf₂ hpre₂) fun hwf₃ => ?_
  have hpre₃ := drainTryTickProg_pre hpre₂
  refine validHistory_step hwf₃ (validHistory_drainTryTickProg hwf₃ hpre₃) fun hwf₄ => ?_
  exact validHistory_drainTryTickProg hwf₄ (drainTryTickProg_pre hpre₃)

/-- Memory history admissibility for `drainTickProg`. -/
theorem validHistory_drainTickProg {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (drainTickProg pBase)) := by
  unfold drainTickProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_drainOldSlotProg hwf hpre)
  refine validHistory_step hwf (validHistory_drainTryStepProg hwf hpre) fun hwf₁ => ?_
  have hpre₁ := drainTryStepProg_pre hpre
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre₁)
    (clientState_fastReadMetaProg _ _) ?_
  exact validHistory_ite
    (fun _ => validHistory_drainOldSlotProg hwf₁ hpre₁) (fun _ => trivial)

private theorem validHistory_drainTicks2Prog {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (drainTicks2Prog pBase)) := by
  unfold drainTicks2Prog
  refine validHistory_step hwf (validHistory_drainTickProg hwf hpre) fun hwf₁ => ?_
  exact validHistory_drainTickProg hwf₁ (drainTickProg_pre hpre)

private theorem validHistory_drainTicks4Prog {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (drainTicks4Prog pBase)) := by
  unfold drainTicks4Prog
  refine validHistory_step hwf (validHistory_drainTicks2Prog hwf hpre) fun hwf₁ => ?_
  exact validHistory_drainTicks2Prog hwf₁ (drainTicks2Prog_pre hpre)

private theorem validHistory_drainTicks8Prog {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (drainTicks8Prog pBase)) := by
  unfold drainTicks8Prog
  refine validHistory_step hwf (validHistory_drainTicks4Prog hwf hpre) fun hwf₁ => ?_
  exact validHistory_drainTicks4Prog hwf₁ (drainTicks4Prog_pre hpre)

/-- Memory history admissibility for `drainTicks16Prog`. -/
theorem validHistory_drainTicks16Prog {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (drainTicks16Prog pBase)) := by
  unfold drainTicks16Prog
  refine validHistory_step hwf (validHistory_drainTicks8Prog hwf hpre) fun hwf₁ => ?_
  exact validHistory_drainTicks8Prog hwf₁ (drainTicks8Prog_pre hpre)

/-- Memory history admissibility for `advanceSubEpochProg`. -/
theorem validHistory_advanceSubEpochProg {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (advanceSubEpochProg pBase)) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  have hpre0 : FastProgPre w fl.pBase s := ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre0
  have hm23 : s.mem (fl.pBase + 23) = qEpochWhp fl.N := hpt 23 (by decide)
  obtain ⟨_, _, _, hq_le⟩ := hv.bounds_le_N
  have hN_lt : fl.N < 2 ^ w := fast_N_lt_pow_w hv
  have h2 := two_lt_pow_w hv
  unfold advanceSubEpochProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre0)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_read_bind (by omega) ?_
  rw [hm23]
  simp only [pure_bind]
  refine validHistory_ite (fun hss_lt => ?_) fun _ => ?_
  · refine validHistory_step hwf (validHistory_drainTicks16Prog hwf hpre0) fun hwf₁ => ?_
    have hpre₁ := drainTicks16Prog_pre hpre0
    refine validHistory_ite
      (fun _ => validHistory_fastWriteMetaProg hpre₁ (by omega)) fun _ => ?_
    refine validHistory_bind_same (validHistory_fastReadMetaProg hpre₁)
      (clientState_fastReadMetaProg _ _) ?_
    refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
    refine validHistory_bind_same (validHistory_fastBufItemAllocProg hpre₁)
      (clientState_fastBufItemAllocProg _ _) ?_
    refine validHistory_bind_same (validHistory_fastReadMetaProg hpre₁)
      (clientState_fastReadMetaProg _ _) ?_
    refine validHistory_bind_same (validHistory_fastReadMetaProg hpre₁)
      (clientState_fastReadMetaProg _ _) ?_
    exact validHistory_ite
      (fun _ => validHistory_fastWriteMetaProg hpre₁ (by omega))
      (fun _ => validHistory_fastEnterFallbackProg hwf₁ hpre₁)
  · refine validHistory_bind_same (validHistory_fastReadMetaProg hpre0)
      (clientState_fastReadMetaProg _ s) ?_
    refine validHistory_ite (fun hcur => ?_) (fun _ => trivial)
    refine validHistory_bind_pre (validHistory_fastBufClearStepsProg hwf hpre0)
      (fastBufClearStepsProg_pre hpre0) fun hpre₁ => ?_
    refine validHistory_ite
      (fun hcond => validHistory_fastWriteMetaProg hpre₁ (by omega)) fun _ => ?_
    refine validHistory_bind_pre (validHistory_fastWriteMetaProg hpre₁ (by omega))
      (fastWriteMetaProg_pre hpre₁) fun hpre₂ => ?_
    refine validHistory_bind_pre (validHistory_fastWriteMetaProg hpre₂ (by omega))
      (fastWriteMetaProg_pre hpre₂) fun hpre₃ => ?_
    exact validHistory_fastWriteMetaProg hpre₃ (by omega)

/-! ## Section 5: `LargeEpochRemove` `ValidHistory` Proofs -/

private theorem validHistory_fastDelShadowTryStepProg {w pBase b role fp delLoc : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastDelShadowTryStepProg ((pBase, (b, role)), (fp, delLoc)))) := by
  unfold fastDelShadowTryStepProg
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_shadowRoleProg w _ s)
    (clientState_shadowRoleProg _ s) ?_
  exact validHistory_fastBTreeDeleteProg hwf hpre

private theorem validHistory_fastDelTryStepProg {w pBase b role delLoc u_val : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastDelTryStepProg ((pBase, (b, role)), (delLoc, u_val)))) := by
  unfold fastDelTryStepProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastFpHashProg hpre)
    (clientState_fastFpHashProg _ s) ?_
  refine validHistory_bind_same (validHistory_tryRoleProg w _ s)
    (clientState_tryRoleProg _ s) ?_
  exact validHistory_fastBTreeDeleteProg hwf hpre

private theorem validHistory_fastDeleteFromBTreesProg {w pBase b delLoc u_val : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastDeleteFromBTreesProg ((pBase, (b, delLoc)), u_val))) := by
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre
  unfold fastDeleteFromBTreesProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastFpHashProg hpre)
    (clientState_fastFpHashProg _ s) ?_
  refine validHistory_step_pre hwf (validHistory_fastBTreeDeleteProg hwf hpre)
    (fastBTreeDeleteProg_pre hpre) fun hwf₁ hpre₁ => ?_
  refine validHistory_step_pre hwf₁ (validHistory_fastDelShadowTryStepProg hwf₁ hpre₁)
    (fastDelShadowTryStepProg_pre hpre₁) fun hwf₂ hpre₂ => ?_
  exact validHistory_fastDelTryStepProg hwf₂ hpre₂

private theorem validHistory_fastUnindexAtProg {w pBase b delLoc u_val : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastUnindexAtProg ((pBase, (b, delLoc)), u_val))) := by
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre
  unfold fastUnindexAtProg
  refine validHistory_bind_same (validHistory_fastRKeyProg hpre)
    (clientState_fastRKeyProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastBufLookupProg hpre)
    (clientState_fastBufLookupProg _ s) ?_
  refine validHistory_ite (fun _ => validHistory_fastBufDeleteProg hwf hpre) fun _ => ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun _ => ?_)
    (fun _ => validHistory_fastDeleteFromBTreesProg hwf hpre)
  simp only [pure_bind]
  refine validHistory_bind_same (validHistory_fastBufLookupProg hpre)
    (clientState_fastBufLookupProg _ s) ?_
  exact validHistory_ite
    (fun _ => validHistory_fastBufDeleteProg hwf hpre)
    (fun _ => validHistory_fastDeleteFromBTreesProg hwf hpre)

private theorem validHistory_fastRelocShadowStepProg {w pBase b role fp delLoc : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastRelocShadowStepProg ((pBase, (b, role)), (fp, delLoc)))) := by
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre
  unfold fastRelocShadowStepProg
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_shadowRoleProg w _ s)
    (clientState_shadowRoleProg _ s) ?_
  refine validHistory_step_pre hwf (validHistory_fastBTreeInsertProg hwf hpre)
    (fastBTreeInsertProg_pre hpre) fun hwf₁ hpre₁ => ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre₁)
    (clientState_fastReadBktLaneProg _ _) ?_
  exact validHistory_ite
    (fun _ => validHistory_fastWriteBktLaneProg hwf₁ hpre₁) (fun _ => trivial)

private theorem validHistory_fastRelocTryInsProg {w pBase b tRole fpT delLoc : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastRelocTryInsProg ((pBase, (b, tRole)), (fpT, delLoc)))) := by
  obtain ⟨fl, rfl, hv, hpt, hbkt, hfp⟩ := hpre
  have hpre0 : FastProgPre w fl.pBase s := ⟨fl, rfl, hv, hpt, hbkt, hfp⟩
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre0
  have hm0 : s.mem (fl.pBase + 0) = fl.N := hpt 0 (by decide)
  have hN_lt : fl.N < 2 ^ w := fast_N_lt_pow_w hv
  unfold fastRelocTryInsProg
  refine validHistory_bind_same (validHistory_fastBTreeLookupProg hpre0)
    (clientState_fastBTreeLookupProg _ s) ?_
  refine validHistory_ite (fun _ => validHistory_advanceTrySaltProg hwf hpre0) fun _ => ?_
  refine validHistory_read_bind (by omega) ?_
  rw [hm0]
  refine validHistory_step hwf (validHistory_fastBTreeInsertProg hwf hpre0) fun _ => ?_
  have hpre₁ := fastBTreeInsertProg_pre (x := ((fl.pBase, (b, tRole)), (fpT, delLoc))) hpre0
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre₁)
    (clientState_fastReadMetaProg _ _) ?_
  exact validHistory_ite
    (fun hti => validHistory_fastWriteMetaProg hpre₁ (by omega)) (fun _ => trivial)

private theorem validHistory_fastRelocTryStepProg {w pBase b role delLoc lastLoc u_last : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastRelocTryStepProg ((pBase, (b, role)), ((delLoc, lastLoc), u_last)))) := by
  unfold fastRelocTryStepProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastFpHashProg hpre)
    (clientState_fastFpHashProg _ s) ?_
  refine validHistory_bind_same (validHistory_tryRoleProg w _ s)
    (clientState_tryRoleProg _ s) ?_
  refine validHistory_ite
    (fun _ => validHistory_fastBTreeUpdateProg hwf hpre) fun _ => ?_
  exact validHistory_ite
    (fun _ => validHistory_fastRelocTryInsProg hwf hpre) (fun _ => trivial)

private theorem validHistory_fastRelocBTreeProg {w pBase b delLoc lastLoc u_last : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastRelocBTreeProg ((pBase, (b, delLoc)), (lastLoc, u_last)))) := by
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre
  unfold fastRelocBTreeProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastFpHashProg hpre)
    (clientState_fastFpHashProg _ s) ?_
  refine validHistory_step_pre hwf (validHistory_fastBTreeUpdateProg hwf hpre)
    (fastBTreeUpdateProg_pre hpre) fun hwf₁ hpre₁ => ?_
  refine validHistory_step_pre hwf₁ (validHistory_fastRelocShadowStepProg hwf₁ hpre₁)
    (fastRelocShadowStepProg_pre hpre₁) fun hwf₂ hpre₂ => ?_
  exact validHistory_fastRelocTryStepProg hwf₂ hpre₂

private theorem validHistory_fastRelocLastProg {w pBase b delLoc lastLoc u_last : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastRelocLastProg ((pBase, (b, delLoc)), (lastLoc, u_last)))) := by
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre
  unfold fastRelocLastProg
  refine validHistory_bind_same (validHistory_fastRKeyProg hpre)
    (clientState_fastRKeyProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastBufLookupProg hpre)
    (clientState_fastBufLookupProg _ s) ?_
  refine validHistory_ite (fun _ => validHistory_fastBufInsertProg hwf hpre) fun _ => ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun _ => ?_)
    (fun _ => validHistory_fastRelocBTreeProg hwf hpre)
  simp only [pure_bind]
  refine validHistory_bind_same (validHistory_fastBufLookupProg hpre)
    (clientState_fastBufLookupProg _ s) ?_
  exact validHistory_ite
    (fun _ => validHistory_fastBufInsertProg hwf hpre)
    (fun _ => validHistory_fastRelocBTreeProg hwf hpre)

private theorem validHistory_fastSwapLastDownProg {w pBase b delLoc lastLoc : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastSwapLastDownProg ((pBase, b), (delLoc, lastLoc)))) := by
  unfold fastSwapLastDownProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastBpReadAtProg hpre)
    (clientState_fastBpReadAtProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastFeistelReconProg hpre)
    (clientState_fastFeistelReconProg _ s) ?_
  refine validHistory_step_pre hwf (validHistory_fastBpWriteAtProg hwf hpre)
    (fastBpWriteAtProg_pre hpre) fun hwf₁ hpre₁ => ?_
  exact validHistory_fastRelocLastProg hwf₁ hpre₁

private theorem validHistory_fastPromoteShadowIfDoneProg {w pBase b cnt : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastPromoteShadowIfDoneProg ((pBase, b), cnt))) := by
  unfold fastPromoteShadowIfDoneProg
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_shadowRoleProg w _ s)
    (clientState_shadowRoleProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg hpre)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_step_pre hwf (validHistory_fastWriteBktLaneProg hwf hpre)
    (fastWriteBktLaneProg_pre hpre) fun hwf₁ hpre₁ => ?_
  refine validHistory_step_pre hwf₁ (validHistory_fastWriteBktLaneProg hwf₁ hpre₁)
    (fastWriteBktLaneProg_pre hpre₁) fun hwf₂ hpre₂ => ?_
  exact validHistory_fastWriteBktLaneProg hwf₂ hpre₂

private theorem validHistory_fastClampTryPosProg {w pBase b cnt lastLoc : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s)
    (hle : lastLoc ≤ cnt) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastClampTryPosProg ((pBase, b), (cnt, lastLoc)))) := by
  have htp_lt := fastReadMeta_lt_pow_w (off := 9) hwf hpre (by decide)
  unfold fastClampTryPosProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  obtain ⟨_, _, htp_eq⟩ := hcond
  exact validHistory_fastWriteMetaProg hpre (by omega)

/-- Memory history admissibility for `fastRemoveAtProg`. -/
theorem validHistory_fastRemoveAtProg {w pBase b delLoc u_val : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastRemoveAtProg ((pBase, b), (delLoc, u_val)))) := by
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre
  unfold fastRemoveAtProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastReadBktCntProg hpre)
    (clientState_fastReadBktCntProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_step_pre hwf (validHistory_fastUnindexAtProg hwf hpre)
    (fastUnindexAtProg_pre hpre) fun hwf₁ hpre₁ => ?_
  refine validHistory_step_pre hwf₁ (validHistory_fastSwapLastDownProg hwf₁ hpre₁)
    (fastSwapLastDownProg_pre hpre₁) fun hwf₂ hpre₂ => ?_
  refine validHistory_step_pre hwf₂ (validHistory_fastBpPopBktBackProg hwf₂ hpre₂)
    (fastBpPopBktBackProg_pre hpre₂) fun hwf₃ hpre₃ => ?_
  refine validHistory_step_pre hwf₃ (validHistory_fastPromoteShadowIfDoneProg hwf₃ hpre₃)
    (fastPromoteShadowIfDoneProg_pre hpre₃) fun hwf₄ hpre₄ => ?_
  exact validHistory_fastClampTryPosProg hwf₄ hpre₄ (Nat.sub_le _ 1)

/-- Memory history admissibility for `fastPopAnyProg`. -/
theorem validHistory_fastPopAnyProg {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastPopAnyProg pBase)) := by
  unfold fastPopAnyProg
  refine validHistory_bind_same (validHistory_fastBpOwnerOfZeroProg hpre)
    (clientState_fastBpOwnerOfZeroProg _ s) ?_
  simp only [pure_bind]
  refine validHistory_bind_same (validHistory_fastReadBktCntProg hpre)
    (clientState_fastReadBktCntProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastBpReadAtProg hpre)
    (clientState_fastBpReadAtProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastFeistelReconProg hpre)
    (clientState_fastFeistelReconProg _ s) ?_
  exact validHistory_bind_eq (validHistory_fastRemoveAtProg hwf hpre) trivial

/-! ## Section 6: `LargeEpochFast` `ValidHistory` Proofs -/

/-- Memory history admissibility for `fastFallbackQueryProg` (read-only). -/
theorem validHistory_fastFallbackQueryProg {w pBase u_val : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastFallbackQueryProg (pBase, u_val))) := by
  obtain ⟨fl, rfl, hr⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  have ⟨hv, hpt, _, _⟩ := hr
  have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hpt 46 (by decide)
  unfold fastFallbackQueryProg
  refine validHistory_read_bind (by omega) ?_
  rw [hum]
  refine validHistory_ite (fun hle => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_loadHashStaticCtxProg hp)
    (clientState_loadHashStaticCtxProg _ s) ?_
  rw [clientResult_loadFeistelCtx hpt]
  refine validHistory_bind_same (validHistory_loadBlockPoolCtxProg hp)
    (clientState_loadBlockPoolCtxProg _ s) ?_
  rw [clientResult_loadBlockPoolCtxProg hpt]
  dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
  exact validHistory_fallbackQueryProg (feistelSplitPre_of_fastReady hr hle)
    (by rw [BpMetaLayout.ofCtx_toCtx]; exact hv.mp_valid)
    (by rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid)

/-- Memory history admissibility for `fastFallbackInsertProg`. -/
theorem validHistory_fastFallbackInsertProg {w pBase u_val v_val : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastFallbackInsertProg ((pBase, u_val), v_val))) := by
  obtain ⟨fl, rfl, hr⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  have ⟨hv, hpt, _, _⟩ := hr
  have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hpt 46 (by decide)
  unfold fastFallbackInsertProg
  refine validHistory_read_bind (by omega) ?_
  rw [hum]
  refine validHistory_ite (fun hle => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_loadHashStaticCtxProg hp)
    (clientState_loadHashStaticCtxProg _ s) ?_
  rw [clientResult_loadFeistelCtx hpt]
  refine validHistory_bind_same (validHistory_loadBlockPoolCtxProg hp)
    (clientState_loadBlockPoolCtxProg _ s) ?_
  rw [clientResult_loadBlockPoolCtxProg hpt]
  dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
  exact validHistory_fallbackInsertProg hwf (feistelSplitPre_of_fastReady hr hle)
    (by rw [BpMetaLayout.ofCtx_toCtx]; exact hv.mp_valid)
    (by rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid)

/-- Memory history admissibility for `fastFallbackDeleteProg`. -/
theorem validHistory_fastFallbackDeleteProg {w pBase u_val : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastFallbackDeleteProg (pBase, u_val))) := by
  obtain ⟨fl, rfl, hr⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  have ⟨hv, hpt, _, _⟩ := hr
  have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hpt 46 (by decide)
  unfold fastFallbackDeleteProg
  refine validHistory_read_bind (by omega) ?_
  rw [hum]
  refine validHistory_ite (fun hle => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_loadHashStaticCtxProg hp)
    (clientState_loadHashStaticCtxProg _ s) ?_
  rw [clientResult_loadFeistelCtx hpt]
  refine validHistory_bind_same (validHistory_loadBlockPoolCtxProg hp)
    (clientState_loadBlockPoolCtxProg _ s) ?_
  rw [clientResult_loadBlockPoolCtxProg hpt]
  dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
  exact validHistory_fallbackDeleteProg hwf (feistelSplitPre_of_fastReady hr hle)
    (by rw [BpMetaLayout.ofCtx_toCtx]; exact hv.mp_valid)
    (by rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid)

/-- Memory history admissibility for `fastFallbackPopAnyProg`. -/
theorem validHistory_fastFallbackPopAnyProg {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastFallbackPopAnyProg pBase)) := by
  obtain ⟨fl, rfl, hr⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  have ⟨hv, hpt, _, _⟩ := hr
  unfold fastFallbackPopAnyProg
  refine validHistory_bind_same (validHistory_loadHashStaticCtxProg hp)
    (clientState_loadHashStaticCtxProg _ s) ?_
  rw [clientResult_loadFeistelCtx hpt]
  refine validHistory_bind_same (validHistory_loadBlockPoolCtxProg hp)
    (clientState_loadBlockPoolCtxProg _ s) ?_
  rw [clientResult_loadBlockPoolCtxProg hpt]
  dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
  exact validHistory_fallbackPopAnyProg hwf
    (by rw [BpMetaLayout.ofCtx_toCtx]; exact hv.mp_valid)
    (by rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid)
    (fun bkt q_val hq => feistelReconPre_of_fastReady hr hq)

/-- Memory history admissibility for `fastDeleteProg`. -/
theorem validHistory_fastDeleteProg {w pBase u_val : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastDeleteProg (pBase, u_val))) := by
  unfold fastDeleteProg
  refine validHistory_bind_same (validHistory_fastProbeProg hpre)
    (clientState_fastProbeProg _ s) ?_
  exact validHistory_ite (fun _ => trivial)
    (fun _ => validHistory_fastRemoveAtProg hwf hpre)

private theorem validHistory_fastInsertNewStepProg {w pBase u_val b cnt v_val : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastInsertNewStepProg ((pBase, u_val), ((b, cnt), v_val)))) := by
  unfold fastInsertNewStepProg
  refine validHistory_step hwf (validHistory_drainTrySteps5Prog hwf hpre) fun hwf₁ => ?_
  have hpre₁ := drainTrySteps5Prog_pre hpre
  refine validHistory_step hwf₁ (validHistory_fastShadowSteps8Prog hwf₁ hpre₁) fun hwf₂ => ?_
  have hpre₂ := fastShadowSteps8Prog_pre (x := (pBase, b)) hpre₁
  refine validHistory_bind_same (validHistory_fastFeistelSplitProg hpre₂)
    (clientState_fastFeistelSplitProg _ _) ?_
  refine validHistory_step_pre hwf₂ (validHistory_fastBpAppendProg hwf₂ hpre₂)
    (fastBpAppendProg_pre hpre₂) fun hwf₃ hpre₃ => ?_
  refine validHistory_bind_same (validHistory_fastRKeyProg hpre₃)
    (clientState_fastRKeyProg _ _) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre₃)
    (clientState_fastReadMetaProg _ _) ?_
  exact validHistory_fastBufInsertProg hwf₃ hpre₃

private theorem validHistory_fastCheckRKeyFreeProg {w pBase u_val : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastCheckRKeyFreeProg (pBase, u_val))) := by
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre
  unfold fastCheckRKeyFreeProg
  refine validHistory_bind_same (validHistory_fastRKeyProg hpre)
    (clientState_fastRKeyProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastBufLookupProg hpre)
    (clientState_fastBufLookupProg _ s) ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastBufLookupProg hpre)
    (clientState_fastBufLookupProg _ s) ?_
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

/-- Memory history admissibility for `fastInsertProg` (matching the precondition of
`realizesBounded_fastInsert`). -/
theorem validHistory_fastInsertProg {w pBase u_val v_val : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hpre : ∃ fl : FastEpochLayout, fl.pBase = pBase ∧ FastLayoutReady w fl s ∧
      FastLayoutReady w fl ((Memory.spec 0).clientState s (fastEnterFallbackProg pBase))) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastInsertProg ((pBase, u_val), v_val))) := by
  obtain ⟨fl, rfl, hfl, hfl_fb⟩ := hpre
  have hpre0 : FastProgPre w fl.pBase s := ⟨fl, rfl, hfl⟩
  have hpre_fb : FastProgPre w fl.pBase
      ((Memory.spec 0).clientState s (fastEnterFallbackProg fl.pBase)) := ⟨fl, rfl, hfl_fb⟩
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre0
  unfold fastInsertProg
  refine validHistory_bind_same (validHistory_fastProbeProg hpre0)
    (clientState_fastProbeProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) fun _ => ?_
  · refine validHistory_bind_same (validHistory_fastFeistelSplitProg hpre0)
      (clientState_fastFeistelSplitProg _ s) ?_
    exact validHistory_fastBpWriteAtProg hwf hpre0
  · refine validHistory_bind_same (validHistory_fastCheckRKeyFreeProg hpre0)
      (clientState_fastCheckRKeyFreeProg _ s) ?_
    refine validHistory_ite (fun _ => ?_) fun _ => ?_
    · refine validHistory_step hwf (validHistory_fastEnterFallbackProg hwf hpre0) fun hwf₁ => ?_
      exact validHistory_fastFallbackInsertProg hwf₁ hpre_fb
    · refine validHistory_bind_same (validHistory_fastReadBktCntProg hpre0)
        (clientState_fastReadBktCntProg _ s) ?_
      refine validHistory_read_bind (by omega) ?_
      refine validHistory_ite (fun _ => ?_) fun _ => ?_
      · refine validHistory_step hwf (validHistory_fastEnterFallbackProg hwf hpre0) fun hwf₁ => ?_
        exact validHistory_fastFallbackInsertProg hwf₁ hpre_fb
      · refine validHistory_step_pre hwf (validHistory_fastInsertNewStepProg hwf hpre0)
          (fastInsertNewStepProg_pre hpre0) fun hwf₁ hpre₁ => ?_
        exact validHistory_advanceSubEpochProg hwf₁ hpre₁

/-- Memory history admissibility for `largeEpochQueryProg` (read-only). -/
theorem validHistory_largeEpochQueryProg {w pBase u_val : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (largeEpochQueryProg (pBase, u_val))) := by
  unfold largeEpochQueryProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  exact validHistory_ite
    (fun _ => validHistory_fastQueryProg hpre)
    (fun _ => validHistory_fastFallbackQueryProg hpre)

/-- Memory history admissibility for `largeEpochInsertProg` under `FastInsertProgPre`. -/
theorem validHistory_largeEpochInsertProg {w pBase u_val v_val : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastInsertProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (largeEpochInsertProg ((pBase, u_val), v_val))) := by
  obtain ⟨fl, rfl, hr, hfb⟩ := hpre
  have hpre0 : FastProgPre w fl.pBase s := ⟨fl, rfl, hr⟩
  have ⟨_, hpt, _, _⟩ := hr
  unfold largeEpochInsertProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre0)
    (clientState_fastReadMetaProg _ s) ?_
  exact validHistory_ite
    (fun hm => by
      have hm2 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 2)) =
          s.mem (fl.metaBase + 2) := clientResult_fastReadMetaProg hpt (by decide)
      exact validHistory_fastInsertProg hwf ⟨fl, rfl, hr, hfb (by rwa [← hm2])⟩)
    (fun _ => validHistory_fastFallbackInsertProg hwf hpre0)

/-- Memory history admissibility for `largeEpochDeleteProg`. -/
theorem validHistory_largeEpochDeleteProg {w pBase u_val : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (largeEpochDeleteProg (pBase, u_val))) := by
  unfold largeEpochDeleteProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  exact validHistory_ite
    (fun _ => validHistory_fastDeleteProg hwf hpre)
    (fun _ => validHistory_fastFallbackDeleteProg hwf hpre)

/-- Memory history admissibility for `largeEpochPopAnyProg`. -/
theorem validHistory_largeEpochPopAnyProg {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (largeEpochPopAnyProg pBase)) := by
  unfold largeEpochPopAnyProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  exact validHistory_ite
    (fun _ => validHistory_fastPopAnyProg hwf hpre)
    (fun _ => validHistory_fastFallbackPopAnyProg hwf hpre)

/-! ## Section 7: Top-Level `LargeEpoch` `ValidHistory` Proofs -/

private theorem validHistory_loadSmallIoCtxProg {w pBase : ℕ} {s : Memory.State}
    (hp : pBase + 64 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (loadSmallIoCtxProg pBase)) := by
  unfold loadSmallIoCtxProg
  iterate 13 (refine validHistory_read_bind (by omega) ?_)
  exact trivial

/-- Memory history admissibility for `epochReadNSideProg` (read-only) under `EpochProgPre`. -/
theorem validHistory_epochReadNSideProg {w pBase : ℕ} {s : Memory.State}
    (hpre : EpochProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (epochReadNSideProg pBase)) := by
  unfold epochReadNSideProg
  rcases hpre with ⟨_, L, _, hp, hv, hpt⟩ | ⟨_, fl, rfl, hr⟩
  · obtain ⟨_, hmb, _⟩ := hpt
    refine validHistory_read_bind (by omega) ?_
    rw [hmb]
    have hfr := hv.hdr_frontier
    have hlt : L.metaBase + 1 < s.frontier := by omega
    exact ⟨hlt, trivial⟩
  · obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    obtain ⟨hv, hpt, _, _⟩ := hr
    have hmb : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
    have h32 := epochMetaWords_ge_32 (w := fl.w) hv.thresh_le
    have hmf := hv.meta_frontier
    refine validHistory_read_bind (by omega) ?_
    rw [hmb]
    have hlt : fl.metaBase + 1 < s.frontier := by omega
    exact ⟨hlt, trivial⟩

/-- Memory history admissibility for `epochInitZeroedProg` under `EpochProgPre`. -/
theorem validHistory_epochInitZeroedProg {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : EpochProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (epochInitZeroedProg pBase)) := by
  unfold epochInitZeroedProg
  rcases hpre with ⟨hm0, L, _, hp, hv, hpt⟩ | ⟨hmne, fl, rfl, hr⟩
  · obtain ⟨_, hmb, _⟩ := hpt
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    rw [hm0, hmb, ite_eq_left rfl]
    exact validHistory_smallEpochInitProg hv.hdr_frontier
  · obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    obtain ⟨hv, hpt, hbkt_α, hfp_α⟩ := hr
    have hcN : s.mem fl.pBase = fl.N := hpt 0 (by decide)
    have hmb : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
    have h32 := epochMetaWords_ge_32 (w := fl.w) hv.thresh_le
    have hmf := hv.meta_frontier
    have hN_lt : fl.N < 2 ^ w := fast_N_lt_pow_w hv
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    rw [ite_eq_right hmne]
    have hw_vh : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
        (Memory.write (s.mem (fl.pBase + 1)) (s.mem fl.pBase))) := by
      rw [hmb, hcN]
      exact ⟨⟨by omega, hN_lt⟩, trivial⟩
    refine validHistory_step hwf hw_vh fun hwf₁ => ?_
    have hpre₁ : FastProgPre w fl.pBase
        ((Memory.spec 0).clientState s
          (Memory.write (s.mem (fl.pBase + 1)) (s.mem fl.pBase))) := by
      refine ⟨fl, rfl, hv, ?_, ?_, ?_⟩
      · exact hpt.congr fun a ha1 ha2 =>
          Function.update_of_ne (fun he => by
            have hpl := hv.pBase_lt_meta; rw [hmb] at he; omega) _ _
      · change Function.update s.mem (s.mem (fl.pBase + 1)) (s.mem fl.pBase)
            fl.bktHashBase < 2 ^ (redWidthWhp fl.U - 1)
        rw [Function.update_of_ne (by
          rw [hmb]; dsimp only [FastEpochLayout.bktHashBase]; unfold offBktHash; omega)]
        exact hbkt_α
      · change Function.update s.mem (s.mem (fl.pBase + 1)) (s.mem fl.pBase)
            fl.fpHashBase < 2 ^ (redWidthWhp fl.U - 1)
        have hne : fl.fpHashBase ≠ s.mem (fl.pBase + 1) := by
          rw [hmb]; dsimp only [FastEpochLayout.fpHashBase]
          unfold offFpHash offBktHash; omega
        rw [Function.update_of_ne hne]
        exact hfp_α
    exact validHistory_fastInitZeroedProg hwf₁ hpre₁

/-- Memory history admissibility for `epochQueryProg` (read-only) under `EpochProgPre`. -/
theorem validHistory_epochQueryProg {w pBase u_val : ℕ} {s : Memory.State}
    (hpre : EpochProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (epochQueryProg (pBase, u_val))) := by
  unfold epochQueryProg
  rcases hpre with ⟨hm0, L, _, hp, hv, hpt⟩ | ⟨hmne, fl, rfl, hr⟩
  · have hmb : s.mem (pBase + 1) = L.metaBase := by obtain ⟨_, h, _⟩ := hpt; exact h
    refine validHistory_read_bind (by omega) ?_
    rw [hm0, ite_eq_left rfl]
    refine validHistory_read_bind (by omega) ?_
    rw [hmb]
    refine validHistory_bind_same (validHistory_loadSmallIoCtxProg hp)
      (clientState_loadSmallIoCtxProg pBase s) ?_
    rw [clientResult_loadSmallIoCtxProg hpt]
    exact validHistory_smallEpochQueryRawProg hv.hdr_frontier
      (by rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid)
  · obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    refine validHistory_read_bind (by omega) ?_
    rw [ite_eq_right hmne]
    exact validHistory_largeEpochQueryProg ⟨fl, rfl, hr⟩

/-- Memory history admissibility for `epochInsertProg` under `EpochInsertProgPre`. -/
theorem validHistory_epochInsertProg {w pBase u_val v_val : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : EpochInsertProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (epochInsertProg ((pBase, u_val), v_val))) := by
  unfold epochInsertProg
  rcases hpre with ⟨hm0, L, _, hp, hv, hpt⟩ | ⟨hmne, hfi⟩
  · have hmb : s.mem (pBase + 1) = L.metaBase := by obtain ⟨_, h, _⟩ := hpt; exact h
    refine validHistory_read_bind (by omega) ?_
    rw [hm0, ite_eq_left rfl]
    refine validHistory_read_bind (by omega) ?_
    rw [hmb]
    refine validHistory_bind_same (validHistory_loadSmallIoCtxProg hp)
      (clientState_loadSmallIoCtxProg pBase s) ?_
    rw [clientResult_loadSmallIoCtxProg hpt]
    exact validHistory_smallEpochInsertRawProg hwf hv.hdr_frontier
      (by rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid)
  · obtain ⟨fl, rfl, hr, hfb⟩ := hfi
    obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    refine validHistory_read_bind (by omega) ?_
    rw [ite_eq_right hmne]
    exact validHistory_largeEpochInsertProg hwf ⟨fl, rfl, hr, hfb⟩

/-- Memory history admissibility for `epochDeleteProg` under `EpochProgPre`. -/
theorem validHistory_epochDeleteProg {w pBase u_val : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : EpochProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (epochDeleteProg (pBase, u_val))) := by
  unfold epochDeleteProg
  rcases hpre with ⟨hm0, L, _, hp, hv, hpt⟩ | ⟨hmne, fl, rfl, hr⟩
  · have hmb : s.mem (pBase + 1) = L.metaBase := by obtain ⟨_, h, _⟩ := hpt; exact h
    refine validHistory_read_bind (by omega) ?_
    rw [hm0, ite_eq_left rfl]
    refine validHistory_read_bind (by omega) ?_
    rw [hmb]
    refine validHistory_bind_same (validHistory_loadSmallIoCtxProg hp)
      (clientState_loadSmallIoCtxProg pBase s) ?_
    rw [clientResult_loadSmallIoCtxProg hpt]
    exact validHistory_smallEpochDeleteRawProg hwf hv.hdr_frontier
      (by rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid)
  · obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    refine validHistory_read_bind (by omega) ?_
    rw [ite_eq_right hmne]
    exact validHistory_largeEpochDeleteProg hwf ⟨fl, rfl, hr⟩

/-- Memory history admissibility for `epochPopAnyProg` under `EpochProgPre`. -/
theorem validHistory_epochPopAnyProg {w pBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : EpochProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (epochPopAnyProg pBase)) := by
  unfold epochPopAnyProg
  rcases hpre with ⟨hm0, L, _, hp, hv, hpt⟩ | ⟨hmne, fl, rfl, hr⟩
  · have hmb : s.mem (pBase + 1) = L.metaBase := by obtain ⟨_, h, _⟩ := hpt; exact h
    refine validHistory_read_bind (by omega) ?_
    rw [hm0, ite_eq_left rfl]
    refine validHistory_read_bind (by omega) ?_
    rw [hmb]
    refine validHistory_bind_same (validHistory_loadSmallIoCtxProg hp)
      (clientState_loadSmallIoCtxProg pBase s) ?_
    rw [clientResult_loadSmallIoCtxProg hpt]
    exact validHistory_smallEpochPopAnyRawProg hwf hv.hdr_frontier
      (by rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid)
  · obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    refine validHistory_read_bind (by omega) ?_
    rw [ite_eq_right hmne]
    exact validHistory_largeEpochPopAnyProg hwf ⟨fl, rfl, hr⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
