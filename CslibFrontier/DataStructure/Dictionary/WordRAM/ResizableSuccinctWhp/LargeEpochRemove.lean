/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochRemBase
-- Private deletion/pop helpers shared across the LargeEpochRemBase/LargeEpochRemove split.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochRemBase
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Large Fast-Epoch Slot-Removal (`fastRemoveAtProg`) and Migration-Pop (`fastPopAnyProg`) Specs

This module proves the unconditional invariant-preservation, good-seed potential-preservation, and
`BufCur` key-preservation specifications for `fastRemoveAtProg` and `fastPopAnyProg` (defined in
`LargeEpochRemBase`) for the deamortized worst-case WHP resizable succinct dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]).

## Main results

* `fastRemoveAtProg_spec`, `fastRemoveAtProg_good`: unconditional `FastEpochInvGen` preservation
  on all hash seeds and `FastSubEpochGood` potential preservation under `GoodEpochSeeds` for
  `fastRemoveAtProg`.
* `fastPopAnyProg_spec`, `fastPopAnyProg_good`: unconditional `FastEpochInvGen` and
  `FastSubEpochGood` preservation for `fastPopAnyProg`.
* `fastRemoveAtProg_curSlot_keys`, `fastPopAnyProg_curSlot_keys`: active `BufCur` key-set
  monotonicity across slot removal and migration pop.

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

/-- Relocate `uLast` in `BTree(b, curRole b)` from `lastLoc = cnt - 1` to `delLoc < lastLoc`
(also inserting into `shadow` if `delLoc < sc - 1`, updating/inserting/advancing `tryMap` when
`tryAct = 1 ∧ tryBkt = b`). Assumes `(b, delLoc)` already holds `uLast`'s `(q, v)` pair. -/
private theorem fastRelocBTreeProg_spec {slackCur : ℕ} {fl : FastEpochLayout}
    {w b delLoc lastLoc : ℕ} {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s : Memory.State} (uLast : Fin fl.U)
    {mapCur mapOld : ℕ → Option (ℕ × ℕ)} {mapBTree : ℕ → ℕ → Option ℕ}
    (hr : FastLayoutReady w fl s)
    (hbp_inv : fl.bpL.StateInv 0 s.mem)
    (hfp_rep : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp s.mem)
    (hb : b < numBucketsWhp fl.N)
    (hcnt_le : (extractBlockPool fl.mp s.mem).bktCount b ≤ capMaxWhp fl.N)
    (hlast_eq : (extractBlockPool fl.mp s.mem).bktCount b = lastLoc + 1)
    (hdel_lt : delLoc < lastLoc)
    (hkey_del : fastKeyAt fl seeds.bkt s.mem b delLoc = uLast.val)
    (hkey_last : fastKeyAt fl seeds.bkt s.mem b lastLoc = uLast.val)
    (ht : TierInvHoleWith slackCur fl seeds s.mem b delLoc false mapCur mapOld mapBTree)
    (hcur_ne : mapCur (rKeyOf fl.c fl.U fl.N seeds.fp uLast) ≠ some (b, lastLoc))
    (hold_ne : mapOld (rKeyOf fl.c fl.U fl.N seeds.fp uLast) ≠ some (b, lastLoc))
    (hkey_ne_other : ∀ loc' < lastLoc, loc' ≠ delLoc →
      fastKeyAt fl seeds.bkt s.mem b loc' ≠ uLast.val) :
    let fm := extractFastMeta fl s.mem
    let bp := extractBlockPool fl.mp s.mem
    let s' := (Memory.spec 0).clientState s
      (fastRelocBTreeProg ((fl.pBase, (b, delLoc)), (lastLoc, uLast.val)))
    let fm' := extractFastMeta fl s'.mem
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastRelocBTreeProg ((fl.pBase, (b, delLoc)), (lastLoc, uLast.val))) s ≤
      4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 156 * hMaxBTree + 450 ∧
    extractBlockPool fl.mp s'.mem = bp ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    fm'.curBufRole = fm.curBufRole ∧
    fm'.subStep = fm.subStep ∧
    fm'.drainPos = fm.drainPos ∧
    fm'.tryAct = fm.tryAct ∧
    fm'.tryBkt = fm.tryBkt ∧
    fm'.bktSalt = fm.bktSalt ∧
    fm'.curRole = fm.curRole ∧
    fm'.curIns = fm.curIns ∧
    fm'.shadowCode = fm.shadowCode ∧
    (∀ b' ≠ b, fm'.shadowIns b' = fm.shadowIns b') ∧
    fm'.shadowIns b ≤ fm.shadowIns b + 1 ∧
    (fm'.shadowCode b = 0 ∨ ¬(delLoc < fm.shadowCode b - 1) → fm'.shadowIns b = fm.shadowIns b) ∧
    ((fm'.trySalt = fm.trySalt ∧ fm'.tryPos = fm.tryPos) ∨
      (fm.tryAct = 1 ∧ fm.tryBkt = b ∧ delLoc < fm.tryPos ∧ fm.tryPos ≤ lastLoc ∧
        fm'.trySalt = (if fm.trySalt + 1 < sMaxWhp fl.c fl.N then fm.trySalt + 1 else 0) ∧
        fm'.tryPos = 0 ∧ fm'.tryIns = 0 ∧
        ∃ (hs_t : fm.trySalt < sMaxWhp fl.c fl.N) (wLoc : ℕ) (wKey : Fin fl.U),
          wLoc < lastLoc ∧ wLoc ≠ delLoc ∧ wKey ≠ uLast ∧
          fastKeyAt fl seeds.bkt s.mem b wLoc = wKey.val ∧
          fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ wKey =
            fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ uLast)) ∧
    TierInvHole slackCur fl seeds s'.mem b lastLoc true := by
  dsimp only
  have hv := hr.1
  have hpt := hr.2.1
  let fm := extractFastMeta fl s.mem
  let bp := extractBlockPool fl.mp s.mem
  have hlast_lt : lastLoc < bp.bktCount b := by
    change lastLoc < (extractBlockPool fl.mp s.mem).bktCount b; omega
  have hdel_val : delLoc < 2 ^ valLaneBitsWhp fl.N := by
    rw [two_pow_valLaneBitsWhp]; unfold capMaxWhp at hcnt_le; omega
  obtain ⟨hs_b, hrl_b, hci_b, _⟩ := ht.bkt_meta_bounds b hb
  let fp_L := (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_b⟩ uLast).val
  have hfpL_lt : fp_L < 2 ^ fpBitsWhp fl.N :=
    (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_b⟩ uLast).isLt
  have hmb_L : mapBTree b fp_L = some lastLoc := by
    obtain ⟨u₀, hk₀, htier⟩ := ht.complete b hb lastLoc hlast_lt (fun h => by omega)
    have hu₀ : u₀ = uLast := Fin.ext (hk₀.symm.trans hkey_last)
    subst hu₀
    rcases htier with h1 | h2 | h3
    · exact absurd h1 hcur_ne
    · exact absurd h2 hold_ne
    · exact h3
  have hm11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := hpt 11 (by decide)
  have hs5_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 5))) =
      fm.bktSalt b := by
    have := bktLane_val_eq hpt hb (Or.inl rfl) (lane := 5); simpa using this
  have hs12_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 12))) =
      fm.curRole b := by
    have := bktLane_val_eq hpt hb (Or.inr ⟨by decide, by decide⟩) (lane := 12)
    simpa only [show (12 = 5) = False from by decide, ite_true, ite_false] using this
  obtain ⟨hfp_r, hfp_c⟩ := fastFpHashProg_spec hr hfp_rep ⟨fm.bktSalt b, hs_b⟩ uLast
  dsimp only at hfp_r hfp_c
  have hc5 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 5)) s
  have hc12 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 12)) s
  unfold fastRelocBTreeProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s from rfl,
    hm11_r, prog_memoryCost_read, ite_eq_left ⟨hb, hdel_lt⟩,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadBktLaneProg, hs5_r,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadBktLaneProg, hs12_r,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastFpHashProg, hfp_r,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  -- Step 1: update `BTree(b, curRole b)` at `fp_L` from `lastLoc` to `delLoc`
  obtain ⟨hfr1, hr1, hc1, hv1, hoth1, hbp1, hfm1, hm2_1, hm0_1, htr1, hoi1, hof1⟩ :=
    fastBTreeUpdateProg_spec hr hb hrl_b hci_b (ht.bt_valid b hb) hfpL_lt hdel_val
  have hsome_L : (mapBTree b fp_L).isSome = true := by rw [hmb_L]; rfl
  rw [hsome_L, ite_eq_left rfl] at hv1
  generalize hs1_def : (Memory.spec 0).clientState s
    (fastBTreeUpdateProg ((fl.pBase, (b, fm.curRole b)), (fp_L, delLoc))) = s1
  rw [hs1_def] at hfr1 hr1 hv1 hoth1 hbp1 hfm1 hm2_1 hm0_1 htr1 hoi1 hof1
  have hsr_p := shadowRoleOf_lt_and_ne hrl_b
  have htr_p := tryRoleOf_lt_and_ne hrl_b
  have htr_ne_sh : tryRoleOf (fm.curRole b) ≠ shadowRoleOf (fm.curRole b) := htr_p.2.2
  -- Step 2: `fastRelocShadowStepProg`
  have hsh_ex : fm.shadowCode b ≠ 0 →
      ∃ sm : ℕ → Option ℕ,
        fm.shadowIns b < 5 * slabScale fl.N ^ 12 ∧
        ValidWhpSlice fl.N (fm.shadowIns b)
          (extractBTreeSlice fl.btL b (shadowRoleOf (fm.curRole b)) s.mem) sm ∧
        (∀ fp, sm fp = match mapBTree b fp with
          | some loc' => if loc' < fm.shadowCode b - 1 then some loc' else none
          | none => none) := fun hsc => by
    obtain ⟨hsh_lt, _, hbd, _, sm, hvs, heq⟩ := ht.shadow b hb hsc
    have h1 : (extractFastMeta fl s.mem).shadowCode b - 1 <
        (extractBlockPool fl.mp s.mem).bktCount b := by simpa using hsh_lt
    have h2 : 4 * (extractFastMeta fl s.mem).shadowIns b +
        5 * ((extractBlockPool fl.mp s.mem).bktCount b -
          ((extractFastMeta fl s.mem).shadowCode b - 1)) ≤
        20 * slabScale fl.N ^ 12 := by simpa using hbd
    have hlt5 : fm.shadowIns b < 5 * slabScale fl.N ^ 12 := by
      change (extractFastMeta fl s.mem).shadowIns b < 5 * slabScale fl.N ^ 12; omega
    exact ⟨sm, hlt5, hvs, heq⟩
  classical
  let shMap₀ : ℕ → Option ℕ :=
    if h : fm.shadowCode b ≠ 0 then (hsh_ex h).choose else fun _ => none
  have hsh1_ok : (extractFastMeta fl s1.mem).shadowCode b ≠ 0 →
      (extractFastMeta fl s1.mem).shadowIns b < 5 * slabScale fl.N ^ 12 ∧
      ValidWhpSlice fl.N ((extractFastMeta fl s1.mem).shadowIns b)
        (extractBTreeSlice fl.btL b (shadowRoleOf (fm.curRole b)) s1.mem) shMap₀ := fun hsc => by
    rw [hfm1] at hsc ⊢
    obtain ⟨hlt5, hvs, _⟩ := (hsh_ex hsc).choose_spec
    refine ⟨hlt5, ?_⟩
    rw [hoth1 b hb (shadowRoleOf (fm.curRole b)) hsr_p.1 (Or.inr hsr_p.2)]
    dsimp only [shMap₀]; rw [dite_eq_left hsc]; exact hvs
  obtain ⟨hfr2, hr2, hc2, hbp2, hm0_2, hm2_2, htr2, hoi2, hof2, hoth2, hact2, hnoop2⟩ :=
    fastRelocShadowStepProg_spec hr1 hb hrl_b hfpL_lt hdel_val hsh1_ok
  generalize hs2_def : (Memory.spec 0).clientState s1
    (fastRelocShadowStepProg ((fl.pBase, (b, fm.curRole b)), (fp_L, delLoc))) = s2
  rw [hs2_def] at hfr2 hr2 hbp2 hm0_2 hm2_2 htr2 hoi2 hof2 hoth2 hact2 hnoop2
  have hfm2_core :
      (extractFastMeta fl s2.mem).curBufRole = fm.curBufRole ∧
      (extractFastMeta fl s2.mem).subStep = fm.subStep ∧
      (extractFastMeta fl s2.mem).drainPos = fm.drainPos ∧
      (extractFastMeta fl s2.mem).tryAct = fm.tryAct ∧
      (extractFastMeta fl s2.mem).tryBkt = fm.tryBkt ∧
      (extractFastMeta fl s2.mem).trySalt = fm.trySalt ∧
      (extractFastMeta fl s2.mem).tryPos = fm.tryPos ∧
      (extractFastMeta fl s2.mem).tryIns = fm.tryIns ∧
      (extractFastMeta fl s2.mem).bktSalt = fm.bktSalt ∧
      (extractFastMeta fl s2.mem).curRole = fm.curRole ∧
      (extractFastMeta fl s2.mem).curIns = fm.curIns ∧
      (extractFastMeta fl s2.mem).shadowCode = fm.shadowCode ∧
      (∀ b' ≠ b, (extractFastMeta fl s2.mem).shadowIns b' = fm.shadowIns b') ∧
      (extractFastMeta fl s2.mem).shadowIns b =
        (if fm.shadowCode b ≠ 0 ∧ delLoc < fm.shadowCode b - 1 then
          fm.shadowIns b + 1 else fm.shadowIns b) := by
    by_cases hcond : fm.shadowCode b ≠ 0 ∧ delLoc < fm.shadowCode b - 1
    · have hc1' : (extractFastMeta fl s1.mem).shadowCode b ≠ 0 ∧
          delLoc < (extractFastMeta fl s1.mem).shadowCode b - 1 := by rwa [hfm1]
      have hfm2 := (hact2 hc1').1
      rw [hfm1] at hfm2
      rw [hfm2, ite_eq_left hcond]
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fun b' hne => Function.update_of_ne hne _ _, Function.update_self _ _ _⟩
    · have hs2_eq : s2 = s1 := hnoop2 (by rwa [hfm1])
      rw [hs2_eq, hfm1, ite_eq_right hcond]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl⟩
  have hof12 : ∀ a, ¬fl.OwnsFastAddr a → s2.mem a = s.mem a :=
    fun a ha => (hof2 a ha).trans (hof1 a ha)
  have hfp_rep2 : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp s2.mem :=
    hfp_rep.congr_on (hv.w_eq ▸ hv.w_pos) fun a h1 h2 =>
      hof12 a (hv.not_ownsFast_seeds
        (by unfold FastEpochLayout.fpHashBase at h1; unfold offFpHash at h1
            have : offBktHash ≤ offFpHash fl.c fl.w fl.U := by
              unfold offFpHash; exact Nat.le_add_right _ _
            omega)
        (by unfold FastEpochLayout.fpHashBase at h2; unfold offBktMeta; omega))
  -- Step 3: `fastRelocTryStepProg`
  have htry_ex : fm.tryAct = 1 ∧ fm.tryBkt = b →
      ∃ (hs : fm.trySalt < sMaxWhp fl.c fl.N) (tm : ℕ → Option ℕ),
        fm.tryIns ≤ 5 * slabScale fl.N ^ 12 ∧
        (¬(lastLoc < fm.tryPos) → fm.tryIns < 5 * slabScale fl.N ^ 12) ∧
        (lastLoc < fm.tryPos → tm (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs⟩ uLast).val =
          some lastLoc) ∧
        ValidWhpSlice fl.N fm.tryIns
          (extractBTreeSlice fl.btL b (tryRoleOf (fm.curRole b)) s.mem) tm ∧
        (∀ fp loc', tm fp = some loc' →
          loc' < fm.tryPos ∧ loc' ≠ delLoc ∧ ∃ u' : Fin fl.U,
            fastKeyAt fl seeds.bkt s.mem b loc' = u'.val ∧
            mapBTree b (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_b⟩ u').val =
              some loc' ∧
            (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs⟩ u').val = fp) ∧
        (∀ loc' < fm.tryPos, loc' ≠ delLoc → ∀ u' : Fin fl.U,
          fastKeyAt fl seeds.bkt s.mem b loc' = u'.val →
          mapBTree b (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_b⟩ u').val =
            some loc' →
          tm (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs⟩ u').val = some loc') := fun hc => by
    obtain ⟨_, hb_t, hs_t, htp, _, hbd, tm, hvt, h1, h2⟩ := ht.try_ok hc.1
    have hbe : (extractFastMeta fl s.mem).tryBkt = b := hc.2
    have hbd' : 4 * (extractFastMeta fl s.mem).tryIns +
        5 * ((extractBlockPool fl.mp s.mem).bktCount b - (extractFastMeta fl s.mem).tryPos) ≤
        20 * slabScale fl.N ^ 12 := by simpa [hbe] using hbd
    have hti_le : fm.tryIns ≤ 5 * slabScale fl.N ^ 12 := by
      change (extractFastMeta fl s.mem).tryIns ≤ 5 * slabScale fl.N ^ 12; omega
    have hti_lt : ¬(lastLoc < fm.tryPos) → fm.tryIns < 5 * slabScale fl.N ^ 12 := by
      intro hnl
      change ¬(lastLoc < (extractFastMeta fl s.mem).tryPos) at hnl
      change (extractFastMeta fl s.mem).tryIns < 5 * slabScale fl.N ^ 12
      omega
    refine ⟨hs_t, tm, hti_le, hti_lt, fun hlt => ?_,
      by rw [hbe] at hvt; exact hvt, fun fp loc' hm => ?_, fun loc' hlt hne u' hk' hmb' => ?_⟩
    · exact h2 lastLoc hlt (fun h => by omega) uLast (by rw [hbe]; exact hkey_last)
        ((mapBTree_fpHash_congr mapBTree hbe (congrArg fm.bktSalt hbe) uLast).trans hmb_L)
    · obtain ⟨hlt, hne, u', hk', hmb', hf'⟩ := h1 fp loc' hm
      exact ⟨hlt, fun h => hne ⟨hbe, h⟩, u', hbe ▸ hk',
        (mapBTree_fpHash_congr mapBTree hbe (congrArg fm.bktSalt hbe) u').symm.trans hmb', hf'⟩
    · exact h2 loc' hlt (fun h => hne h.2) u' (by rw [hbe]; exact hk')
        ((mapBTree_fpHash_congr mapBTree hbe (congrArg fm.bktSalt hbe) u').trans hmb')
  let tryMap₀ : ℕ → Option ℕ :=
    if h : fm.tryAct = 1 ∧ fm.tryBkt = b then (htry_ex h).choose_spec.choose else fun _ => none
  have htry2_ok : (extractFastMeta fl s2.mem).tryAct = 1 →
      (extractFastMeta fl s2.mem).tryBkt = b →
      ∃ hs : (extractFastMeta fl s2.mem).trySalt < sMaxWhp fl.c fl.N,
        (extractFastMeta fl s2.mem).tryIns ≤ 5 * slabScale fl.N ^ 12 ∧
        (¬(lastLoc < (extractFastMeta fl s2.mem).tryPos) →
          delLoc < (extractFastMeta fl s2.mem).tryPos →
          (extractFastMeta fl s2.mem).tryIns < 5 * slabScale fl.N ^ 12) ∧
        (lastLoc < (extractFastMeta fl s2.mem).tryPos →
          tryMap₀ (fpHash fl.c fl.U fl.N seeds.fp
            ⟨(extractFastMeta fl s2.mem).trySalt, hs⟩ uLast).val = some lastLoc) ∧
        ValidWhpSlice fl.N (extractFastMeta fl s2.mem).tryIns
          (extractBTreeSlice fl.btL b (tryRoleOf (fm.curRole b)) s2.mem) tryMap₀ := by
    intro h1 h2
    rw [hfm2_core.2.2.2.1] at h1; rw [hfm2_core.2.2.2.2.1] at h2
    have hc : fm.tryAct = 1 ∧ fm.tryBkt = b := ⟨h1, h2⟩
    have hsp := (htry_ex hc).choose_spec.choose_spec
    rw [hfm2_core.2.2.2.2.2.1, hfm2_core.2.2.2.2.2.2.1, hfm2_core.2.2.2.2.2.2.2.1]
    refine ⟨(htry_ex hc).choose, hsp.1, fun hnl _ => hsp.2.1 hnl, fun hlt => ?_, ?_⟩
    · dsimp only [tryMap₀]; rw [dite_eq_left hc]; exact hsp.2.2.1 hlt
    · rw [hoth2 b hb _ htr_p.1 (Or.inr htr_ne_sh), hoth1 b hb _ htr_p.1 (Or.inr htr_p.2.1)]
      dsimp only [tryMap₀]; rw [dite_eq_left hc]; exact hsp.2.2.2.1
  have hcr2 : (extractFastMeta fl s2.mem).curRole b = fm.curRole b :=
    congrFun hfm2_core.2.2.2.2.2.2.2.2.2.1 b
  obtain ⟨hfr3, hr3, hc3, hbp3, hm0_3, hm2_3, htr3, hoi3, hof3, hoth3, hnoop3, hact3⟩ :=
    fastRelocTryStepProg_spec uLast hr2 hfp_rep2 hb hrl_b hcr2 hdel_val htry2_ok
  generalize hs3_def : (Memory.spec 0).clientState s2
    (fastRelocTryStepProg ((fl.pBase, (b, fm.curRole b)), ((delLoc, lastLoc), uLast.val))) = s3
  rw [hs3_def] at hfr3 hr3 hbp3 hm0_3 hm2_3 htr3 hoi3 hof3 hoth3 hnoop3 hact3
  have hbp_tot : extractBlockPool fl.mp s3.mem = bp := hbp3.trans (hbp2.trans hbp1)
  have hoi_tot : ∀ a, fl.io.OwnsAddr a → s3.mem a = s.mem a :=
    fun a ha => (hoi3 a ha).trans ((hoi2 a ha).trans (hoi1 a ha))
  have hof_tot : ∀ a, ¬fl.OwnsFastAddr a → s3.mem a = s.mem a :=
    fun a ha => (hof3 a ha).trans (hof12 a ha)
  have htr_tot : ∀ r < 2, extractBufTrie (fl.trieL r) s3.mem =
      extractBufTrie (fl.trieL r) s.mem := fun r hrr =>
    (htr3 r hrr).trans ((htr2 r hrr).trans (htr1 r hrr))
  have hke : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
      fastKeyAt fl seeds.bkt s3.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
    fun b' loc' hb' hl' => fastKeyAt_eq_of_fixed_pool hv hbp_inv hbp_tot hoi_tot hb' hl'
  have hcost_tot : memoryCost (fastReadBktLaneProg (fl.pBase, (b, 5))) s +
      memoryCost (fastReadBktLaneProg (fl.pBase, (b, 12))) s +
      memoryCost (fastFpHashProg (fl.pBase, (fm.bktSalt b, uLast.val))) s +
      memoryCost (fastBTreeUpdateProg ((fl.pBase, (b, fm.curRole b)), (fp_L, delLoc))) s +
      memoryCost (fastRelocShadowStepProg ((fl.pBase, (b, fm.curRole b)),
        (fp_L, delLoc))) s1 +
      memoryCost (fastRelocTryStepProg ((fl.pBase, (b, fm.curRole b)),
        ((delLoc, lastLoc), uLast.val))) s2 + 1 ≤
      4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 156 * hMaxBTree + 450 := by
    have hmul : 2 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 2 * dTabWhp fl.c * (cTabWhp fl.c + 2) =
        4 * dTabWhp fl.c * (cTabWhp fl.c + 2) := by ring
    change memoryCost (fastFpHashProg (fl.pBase, (fm.bktSalt b, uLast.val))) s ≤
      12 + 2 * dTabWhp fl.c * (cTabWhp fl.c + 2) at hfp_c
    change memoryCost (fastBTreeUpdateProg ((fl.pBase, (b, fm.curRole b)), (fp_L, delLoc))) s ≤
      6 * hMaxBTree + 50 at hc1
    change memoryCost (fastRelocShadowStepProg ((fl.pBase, (b, fm.curRole b)),
      (fp_L, delLoc))) s1 ≤ 72 * hMaxBTree + 150 at hc2
    change memoryCost (fastRelocTryStepProg ((fl.pBase, (b, fm.curRole b)),
      ((delLoc, lastLoc), uLast.val))) s2 ≤
      2 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 78 * hMaxBTree + 200 at hc3
    omega
  -- Common `extractFastMeta` fields between `s3` and `s2` (all except `trySalt`/`tryPos`/`tryIns`)
  have hfm3_other :
      (extractFastMeta fl s3.mem).curBufRole = fm.curBufRole ∧
      (extractFastMeta fl s3.mem).subStep = fm.subStep ∧
      (extractFastMeta fl s3.mem).drainPos = fm.drainPos ∧
      (extractFastMeta fl s3.mem).tryAct = fm.tryAct ∧
      (extractFastMeta fl s3.mem).tryBkt = fm.tryBkt ∧
      (extractFastMeta fl s3.mem).bktSalt = fm.bktSalt ∧
      (extractFastMeta fl s3.mem).curRole = fm.curRole ∧
      (extractFastMeta fl s3.mem).curIns = fm.curIns ∧
      (extractFastMeta fl s3.mem).shadowCode = fm.shadowCode ∧
      (extractFastMeta fl s3.mem).shadowIns = (extractFastMeta fl s2.mem).shadowIns := by
    by_cases hact : fm.tryAct = 1 ∧ fm.tryBkt = b
    · have hact2' : (extractFastMeta fl s2.mem).tryAct = 1 :=
        hfm2_core.2.2.2.1.trans hact.1
      have htb2' : (extractFastMeta fl s2.mem).tryBkt = b :=
        hfm2_core.2.2.2.2.1.trans hact.2
      have hs_t2 : (extractFastMeta fl s2.mem).trySalt < sMaxWhp fl.c fl.N := by
        rw [hfm2_core.2.2.2.2.2.1]; exact (htry_ex hact).choose
      obtain ⟨h_lt, h_ins⟩ := hact3 hact2' htb2' hs_t2
      by_cases hlt : lastLoc < fm.tryPos
      · have hfm3_eq := (h_lt (by rwa [hfm2_core.2.2.2.2.2.2.1])).1
        rw [hfm3_eq]
        exact ⟨hfm2_core.1, hfm2_core.2.1, hfm2_core.2.2.1, hfm2_core.2.2.2.1,
          hfm2_core.2.2.2.2.1, hfm2_core.2.2.2.2.2.2.2.2.1,
          hfm2_core.2.2.2.2.2.2.2.2.2.1, hfm2_core.2.2.2.2.2.2.2.2.2.2.1,
          hfm2_core.2.2.2.2.2.2.2.2.2.2.2.1, rfl⟩
      · by_cases hdl : delLoc < fm.tryPos
        · rcases h_ins (by rwa [hfm2_core.2.2.2.2.2.2.1])
            (by rwa [hfm2_core.2.2.2.2.2.2.1]) with ⟨_, hfm3_eq, _⟩ | ⟨_, _, hfm3_eq, _⟩
          all_goals (
            rw [hfm3_eq]
            exact ⟨hfm2_core.1, hfm2_core.2.1, hfm2_core.2.2.1, hfm2_core.2.2.2.1,
              hfm2_core.2.2.2.2.1, hfm2_core.2.2.2.2.2.2.2.2.1,
              hfm2_core.2.2.2.2.2.2.2.2.2.1, hfm2_core.2.2.2.2.2.2.2.2.2.2.1,
              hfm2_core.2.2.2.2.2.2.2.2.2.2.2.1, rfl⟩)
        · have hs3_eq : s3 = s2 := hnoop3
            ⟨Or.inr (by rwa [hfm2_core.2.2.2.2.2.2.1]),
              fun h => hlt (hfm2_core.2.2.2.2.2.2.1 ▸ h.2.2)⟩
          rw [hs3_eq]
          exact ⟨hfm2_core.1, hfm2_core.2.1, hfm2_core.2.2.1, hfm2_core.2.2.2.1,
            hfm2_core.2.2.2.2.1, hfm2_core.2.2.2.2.2.2.2.2.1,
            hfm2_core.2.2.2.2.2.2.2.2.2.1, hfm2_core.2.2.2.2.2.2.2.2.2.2.1,
            hfm2_core.2.2.2.2.2.2.2.2.2.2.2.1, rfl⟩
    · have hs3_eq : s3 = s2 := hnoop3
        ⟨Or.inl (fun h => hact ⟨hfm2_core.2.2.2.1 ▸ h.1, hfm2_core.2.2.2.2.1 ▸ h.2⟩),
          fun h => hact ⟨hfm2_core.2.2.2.1 ▸ h.1, hfm2_core.2.2.2.2.1 ▸ h.2.1⟩⟩
      rw [hs3_eq]
      exact ⟨hfm2_core.1, hfm2_core.2.1, hfm2_core.2.2.1, hfm2_core.2.2.2.1,
        hfm2_core.2.2.2.2.1, hfm2_core.2.2.2.2.2.2.2.2.1,
        hfm2_core.2.2.2.2.2.2.2.2.2.1, hfm2_core.2.2.2.2.2.2.2.2.2.2.1,
        hfm2_core.2.2.2.2.2.2.2.2.2.2.2.1, rfl⟩
  have hshi_b_eq : (extractFastMeta fl s3.mem).shadowIns b =
      if fm.shadowCode b ≠ 0 ∧ delLoc < fm.shadowCode b - 1 then
        fm.shadowIns b + 1 else fm.shadowIns b :=
    (congrFun hfm3_other.2.2.2.2.2.2.2.2.2 b).trans hfm2_core.2.2.2.2.2.2.2.2.2.2.2.2.2
  have htry_delta :
      ((extractFastMeta fl s3.mem).trySalt = fm.trySalt ∧
        (extractFastMeta fl s3.mem).tryPos = fm.tryPos) ∨
      (fm.tryAct = 1 ∧ fm.tryBkt = b ∧ delLoc < fm.tryPos ∧ fm.tryPos ≤ lastLoc ∧
        (extractFastMeta fl s3.mem).trySalt =
          (if fm.trySalt + 1 < sMaxWhp fl.c fl.N then fm.trySalt + 1 else 0) ∧
        (extractFastMeta fl s3.mem).tryPos = 0 ∧
        (extractFastMeta fl s3.mem).tryIns = 0 ∧
        ∃ (hs_t : fm.trySalt < sMaxWhp fl.c fl.N) (wLoc : ℕ) (wKey : Fin fl.U),
          wLoc < lastLoc ∧ wLoc ≠ delLoc ∧ wKey ≠ uLast ∧
          fastKeyAt fl seeds.bkt s.mem b wLoc = wKey.val ∧
          fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ wKey =
            fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ uLast) := by
    by_cases hact : fm.tryAct = 1 ∧ fm.tryBkt = b
    · have hact2' := hfm2_core.2.2.2.1.trans hact.1
      have htb2' := hfm2_core.2.2.2.2.1.trans hact.2
      have hs_t := (htry_ex hact).choose
      have hs_t2 : (extractFastMeta fl s2.mem).trySalt < sMaxWhp fl.c fl.N := by
        rw [hfm2_core.2.2.2.2.2.1]; exact hs_t
      obtain ⟨h_lt, h_ins⟩ := hact3 hact2' htb2' hs_t2
      by_cases hlt : lastLoc < fm.tryPos
      · have hfm3_eq := (h_lt (by rwa [hfm2_core.2.2.2.2.2.2.1])).1
        exact Or.inl ⟨(congrArg FastEpochMeta.trySalt hfm3_eq).trans hfm2_core.2.2.2.2.2.1,
          (congrArg FastEpochMeta.tryPos hfm3_eq).trans hfm2_core.2.2.2.2.2.2.1⟩
      · by_cases hdl : delLoc < fm.tryPos
        · rcases h_ins (by rwa [hfm2_core.2.2.2.2.2.2.1])
            (by rwa [hfm2_core.2.2.2.2.2.2.1]) with ⟨_, hfm3_eq, _⟩ |
              ⟨wLoc, hhit, hfm3_eq, _⟩
          · exact Or.inl ⟨(congrArg FastEpochMeta.trySalt hfm3_eq).trans hfm2_core.2.2.2.2.2.1,
              (congrArg FastEpochMeta.tryPos hfm3_eq).trans hfm2_core.2.2.2.2.2.2.1⟩
          · right
            refine ⟨hact.1, hact.2, hdl, by omega, ?_, ?_, ?_, hs_t, wLoc, ?_⟩
            · rw [congrArg FastEpochMeta.trySalt hfm3_eq, hfm2_core.2.2.2.2.2.1]
            · exact congrArg FastEpochMeta.tryPos hfm3_eq
            · exact congrArg FastEpochMeta.tryIns hfm3_eq
            · have hhit0 : (htry_ex hact).choose_spec.choose
                  (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ uLast).val = some wLoc := by
                dsimp only [tryMap₀] at hhit; rw [dite_eq_left hact] at hhit
                rwa [congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t)
                  hfm2_core.2.2.2.2.2.1 uLast)] at hhit
              obtain ⟨hwl_lt, hwl_ne, wKey, hwk, _, hwf⟩ :=
                (htry_ex hact).choose_spec.choose_spec.2.2.2.2.1 _ _ hhit0
              have hwl_lt_last : wLoc < lastLoc := by omega
              have hw_ne_u : wKey ≠ uLast := fun he =>
                hkey_ne_other wLoc hwl_lt_last hwl_ne (hwk.trans (congrArg Fin.val he))
              exact ⟨wKey, hwl_lt_last, hwl_ne, hw_ne_u, hwk, Fin.ext hwf⟩
        · have hs3_eq : s3 = s2 := hnoop3
            ⟨Or.inr (by rwa [hfm2_core.2.2.2.2.2.2.1]),
              fun h => hlt (hfm2_core.2.2.2.2.2.2.1 ▸ h.2.2)⟩
          exact Or.inl ⟨by rw [hs3_eq]; exact hfm2_core.2.2.2.2.2.1,
            by rw [hs3_eq]; exact hfm2_core.2.2.2.2.2.2.1⟩
    · have hs3_eq : s3 = s2 := hnoop3
        ⟨Or.inl (fun h => hact ⟨hfm2_core.2.2.2.1 ▸ h.1, hfm2_core.2.2.2.2.1 ▸ h.2⟩),
          fun h => hact ⟨hfm2_core.2.2.2.1 ▸ h.1, hfm2_core.2.2.2.2.1 ▸ h.2.1⟩⟩
      exact Or.inl ⟨by rw [hs3_eq]; exact hfm2_core.2.2.2.2.2.1,
        by rw [hs3_eq]; exact hfm2_core.2.2.2.2.2.2.1⟩
  refine ⟨hfr3.trans (hfr2.trans hfr1), hr3, ?_, hbp_tot,
    hm0_3.trans (hm0_2.trans hm0_1), hm2_3.trans (hm2_2.trans hm2_1), htr_tot, hoi_tot, hof_tot,
    hfm3_other.1, hfm3_other.2.1, hfm3_other.2.2.1, hfm3_other.2.2.2.1, hfm3_other.2.2.2.2.1,
    hfm3_other.2.2.2.2.2.1, hfm3_other.2.2.2.2.2.2.1, hfm3_other.2.2.2.2.2.2.2.1,
    hfm3_other.2.2.2.2.2.2.2.2.1,
    fun b' hne => (congrFun hfm3_other.2.2.2.2.2.2.2.2.2 b').trans
      (hfm2_core.2.2.2.2.2.2.2.2.2.2.2.2.1 b' hne),
    by rw [hshi_b_eq]; split_ifs
       · exact Nat.le_refl _
       · exact Nat.le_succ _,
    fun h => by
      rw [hshi_b_eq, ite_eq_right (fun hc => by
        rw [hfm3_other.2.2.2.2.2.2.2.2.1] at h
        exact h.elim (fun h0 => hc.1 h0) (fun hn => hn hc.2))],
    htry_delta,
    mapCur, mapOld, Function.update mapBTree b (Function.update (mapBTree b) fp_L (some delLoc)),
    ?_⟩
  · linarith only [hcost_tot]
  have hrole_lt : fm.curBufRole < 2 := ht.role_lt
  have hold_lt : 1 - fm.curBufRole < 2 := by omega
  have hmb3 : ∀ b' < numBucketsWhp fl.N,
      (extractFastMeta fl s3.mem).bktSalt b' = fm.bktSalt b' := fun b' _ =>
    congrFun hfm3_other.2.2.2.2.2.1 b'
  refine
    { role_lt := by rw [hfm3_other.1]; exact ht.role_lt
      subStep_lt := by rw [hfm3_other.2.1]; exact ht.subStep_lt
      bkt_meta_bounds := fun b' hb' => by
        rw [congrFun hfm3_other.2.2.2.2.2.1 b', congrFun hfm3_other.2.2.2.2.2.2.1 b',
          congrFun hfm3_other.2.2.2.2.2.2.2.1 b', congrFun hfm3_other.2.2.2.2.2.2.2.2.1 b',
          hfm3_other.2.2.2.1, hfm3_other.2.2.2.2.1]
        exact ht.bkt_meta_bounds b' hb'
      cur_valid := by rw [hfm3_other.1, htr_tot _ hrole_lt]; exact ht.cur_valid
      cur_raw := by rw [hfm3_other.1, htr_tot _ hrole_lt]; exact ht.cur_raw
      cur_clr := by rw [hfm3_other.1, htr_tot _ hrole_lt]; exact ht.cur_clr
      cur_ia := by rw [hfm3_other.1, hfm3_other.2.1, htr_tot _ hrole_lt]; exact ht.cur_ia
      cur_na := by rw [hfm3_other.1, htr_tot _ hrole_lt]; exact ht.cur_na
      cur_sound := fun rk b' loc' hm => by
        obtain ⟨hb', hl', hne_d, u', hrk', hk'⟩ := ht.cur_sound rk b' loc' hm
        refine ⟨hb', by rw [hbp_tot]; exact hl', ?_, u', hrk', (hke b' loc' hb' hl').trans hk'⟩
        rintro ⟨rfl, rfl⟩
        have hu' : u' = uLast := Fin.ext (hk'.symm.trans hkey_last)
        exact hcur_ne (by rw [← hu', hrk']; exact hm)
      old_valid_half := fun hsub => by
        rw [hfm3_other.2.1] at hsub
        rw [hfm3_other.1, hfm3_other.2.2.1, htr_tot _ hold_lt, hbp_tot]
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, hsnd⟩ := ht.old_valid_half hsub
        refine ⟨h1, h2, h3, h4, h5, h6, h7, fun rk b' loc' hm => ?_⟩
        obtain ⟨hcn, hb', hl', _, u', hrk', hk'⟩ := hsnd rk b' loc' hm
        refine ⟨hcn, hb', hl', ?_, u', hrk', (hke b' loc' hb' hl').trans hk'⟩
        rintro ⟨rfl, rfl⟩
        have hu' : u' = uLast := Fin.ext (hk'.symm.trans hkey_last)
        exact hold_ne (by rw [← hu', hrk']; exact hm)
      old_clear_half := fun hsub => by
        rw [hfm3_other.2.1] at hsub
        rw [hfm3_other.1, hfm3_other.2.1, hfm3_other.2.2.2.1, htr_tot _ hold_lt]
        exact ht.old_clear_half hsub
      bt_valid := fun b' hb' => by
        rw [congrFun hfm3_other.2.2.2.2.2.2.1 b', congrFun hfm3_other.2.2.2.2.2.2.2.1 b']
        by_cases hbb : b' = b
        · rw [hbb, Function.update_self, hoth3 b hb _ hrl_b (Or.inr htr_p.2.1.symm),
            hoth2 b hb _ hrl_b (Or.inr hsr_p.2.symm)]
          exact hv1
        · rw [Function.update_of_ne hbb]
          have hrl' := (ht.bkt_meta_bounds b' hb').2.1
          rw [hoth3 b' hb' _ hrl' (Or.inl hbb), hoth2 b' hb' _ hrl' (Or.inl hbb),
            hoth1 b' hb' _ hrl' (Or.inl hbb)]
          exact ht.bt_valid b' hb'
      bt_sound := fun b' hb' fp' loc' hm => by
        by_cases hbb : b' = b
        · rw [hbb, Function.update_self] at hm
          by_cases hfe : fp' = fp_L
          · rw [hfe, Function.update_self] at hm
            have hl_eq : loc' = delLoc := (Option.some.inj hm).symm
            have hdl_lt_cnt : delLoc < bp.bktCount b := by omega
            refine ⟨by rw [hbp_tot, hbb, hl_eq]; exact hdl_lt_cnt,
              fun h => by omega, uLast,
              by rw [congrArg Fin.val (fpHash_congr_salt (h₂ := hs_b)
                ((hmb3 b' hb').trans (congrArg fm.bktSalt hbb)) uLast)]; exact hfe.symm,
              by rw [hbb, hl_eq, hke b delLoc hb hdl_lt_cnt, hkey_del],
              fun b₁ l₁ hm₁ => ?_, fun b₂ l₂ hm₂ => ?_⟩
            · obtain ⟨hb₁, hl₁, hne₁, _⟩ := ht.cur_sound _ b₁ l₁ hm₁
              rw [hke b₁ l₁ hb₁ hl₁]
              obtain ⟨_, _, u₀, _, hk₀, hd1, _⟩ := ht.bt_sound b hb fp_L lastLoc hmb_L
              have hu₀ : u₀ = uLast := Fin.ext (hk₀.symm.trans hkey_last)
              have hne_c := hd1 b₁ l₁ (by rw [hu₀]; exact hm₁)
              rwa [hu₀] at hne_c
            · have hsub : fm.subStep < qEpochWhp fl.N / 2 := by
                by_contra hn; rw [(ht.old_clear_half hn).1] at hm₂; cases hm₂
              obtain ⟨_, hb₂, hl₂, _, _⟩ :=
                (ht.old_valid_half hsub).2.2.2.2.2.2.2 _ b₂ l₂ hm₂
              rw [hke b₂ l₂ hb₂ hl₂]
              obtain ⟨_, _, u₀, _, hk₀, _, hd2⟩ := ht.bt_sound b hb fp_L lastLoc hmb_L
              have hu₀ : u₀ = uLast := Fin.ext (hk₀.symm.trans hkey_last)
              have := hd2 b₂ l₂ (by rwa [hu₀]); rwa [hu₀] at this
          · rw [Function.update_of_ne hfe] at hm
            obtain ⟨hl', hne_d, u', hf', hk', hd1, hd2⟩ := ht.bt_sound b hb fp' loc' hm
            refine ⟨by rw [hbp_tot, hbb]; exact hl', ?_, u',
              (congrArg Fin.val (fpHash_congr_salt (h₂ := hs_b)
                ((hmb3 b' hb').trans (congrArg fm.bktSalt hbb)) u')).trans hf',
              by rw [hbb]; exact (hke b loc' hb hl').trans hk',
              fun b₁ l₁ hm₁ => ?_, fun b₂ l₂ hm₂ => ?_⟩
            · rintro ⟨_, hl_eq⟩
              have hu' : u' = uLast := Fin.ext ((hl_eq ▸ hk').symm.trans hkey_last)
              exact hfe (hf'.symm.trans (by rw [hu']))
            · obtain ⟨hb₁, hl₁, _, _⟩ := ht.cur_sound _ b₁ l₁ hm₁
              rw [hke b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁
            · have hsub : fm.subStep < qEpochWhp fl.N / 2 := by
                by_contra hn; rw [(ht.old_clear_half hn).1] at hm₂; cases hm₂
              obtain ⟨_, hb₂, hl₂, _, _⟩ :=
                (ht.old_valid_half hsub).2.2.2.2.2.2.2 _ b₂ l₂ hm₂
              rw [hke b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂
        · rw [Function.update_of_ne hbb] at hm
          obtain ⟨hl', _, u', hf', hk', hd1, hd2⟩ := ht.bt_sound b' hb' fp' loc' hm
          refine ⟨by rw [hbp_tot]; exact hl', fun h => hbb h.1, u',
            (congrArg Fin.val (fpHash_congr_salt
              (h₂ := (ht.bkt_meta_bounds b' hb').1) (hmb3 b' hb') u')).trans hf',
            (hke b' loc' hb' hl').trans hk',
            fun b₁ l₁ hm₁ => ?_, fun b₂ l₂ hm₂ => ?_⟩
          · obtain ⟨hb₁, hl₁, _, _⟩ := ht.cur_sound _ b₁ l₁ hm₁
            rw [hke b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁
          · have hsub : fm.subStep < qEpochWhp fl.N / 2 := by
              by_contra hn; rw [(ht.old_clear_half hn).1] at hm₂; cases hm₂
            obtain ⟨_, hb₂, hl₂, _, _⟩ :=
              (ht.old_valid_half hsub).2.2.2.2.2.2.2 _ b₂ l₂ hm₂
            rw [hke b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂
      complete := fun b' hb' loc' hl' hne => by
        rw [hbp_tot] at hl'
        by_cases hdel_eq : b' = b ∧ loc' = delLoc
        · rcases hdel_eq with ⟨rfl, rfl⟩
          refine ⟨uLast, by rw [hke b' loc' hb' hl', hkey_del],
            Or.inr (Or.inr ?_)⟩
          have hfp_eq : (fpHash fl.c fl.U fl.N seeds.fp
              ⟨(extractFastMeta fl s3.mem).bktSalt b',
                by rw [hmb3 b' hb']; exact hs_b⟩ uLast).val = fp_L :=
            congrArg Fin.val (fpHash_congr_salt (h₂ := hs_b) (hmb3 b' hb') uLast)
          rw [hfp_eq, Function.update_self, Function.update_self]
        · obtain ⟨u', hk', htier⟩ := ht.complete b' hb' loc' hl' hdel_eq
          refine ⟨u', (hke b' loc' hb' hl').trans hk', ?_⟩
          rcases htier with h1 | h2 | h3
          · exact Or.inl h1
          · exact Or.inr (Or.inl h2)
          · refine Or.inr (Or.inr ?_)
            rw [congrArg Fin.val (fpHash_congr_salt
              (h₂ := (ht.bkt_meta_bounds b' hb').1) (hmb3 b' hb') u')]
            by_cases hbb : b' = b
            · have h3b : mapBTree b (fpHash fl.c fl.U fl.N seeds.fp
                  ⟨fm.bktSalt b, hs_b⟩ u').val = some loc' :=
                (mapBTree_fpHash_congr mapBTree hbb (congrArg fm.bktSalt hbb) u').symm.trans h3
              have hne_fp : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_b⟩ u').val ≠
                  fp_L := fun hf => by
                exact hne ⟨hbb, Option.some.inj (h3b.symm.trans (by rw [hf]; exact hmb_L))⟩
              have hcongr : (fpHash fl.c fl.U fl.N seeds.fp
                  ⟨fm.bktSalt b', (ht.bkt_meta_bounds b' hb').1⟩ u').val =
                  (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_b⟩ u').val :=
                congrArg Fin.val (fpHash_congr_salt (h₂ := hs_b) (congrArg fm.bktSalt hbb) u')
              rw [hcongr, hbb, Function.update_self, Function.update_of_ne hne_fp]; exact h3b
            · rw [Function.update_of_ne hbb]; exact h3
      shadow := fun b' hb' hsc => by
        rw [congrFun hfm3_other.2.2.2.2.2.2.2.2.1 b'] at hsc
        obtain ⟨hsh_lt, hnt, hbd1, hbd2, sm, hvs, heq⟩ := ht.shadow b' hb' hsc
        have hsr' := (shadowRoleOf_lt_and_ne (ht.bkt_meta_bounds b' hb').2.1).1
        rw [hbp_tot, hfm3_other.2.2.2.1, hfm3_other.2.2.2.2.1,
          congrFun hfm3_other.2.2.2.2.2.2.1 b', congrFun hfm3_other.2.2.2.2.2.2.2.1 b',
          congrFun hfm3_other.2.2.2.2.2.2.2.2.1 b']
        by_cases hbb : b' = b
        · have hsc_b : fm.shadowCode b ≠ 0 := hbb ▸ hsc
          have hsi_eq' : (extractFastMeta fl s3.mem).shadowIns b =
              if fm.shadowCode b ≠ 0 ∧ delLoc < fm.shadowCode b - 1 then
                fm.shadowIns b + 1 else fm.shadowIns b := hshi_b_eq
          have heff : (if (true : Bool) ∧ b = b then bp.bktCount b - 1 else bp.bktCount b) =
              bp.bktCount b - 1 := by simp
          by_cases hdl_lt : delLoc < fm.shadowCode b - 1
          · have hc_b : fm.shadowCode b ≠ 0 ∧ delLoc < fm.shadowCode b - 1 := ⟨hsc_b, hdl_lt⟩
            rw [hbb, hsi_eq', ite_eq_left hc_b]
            have hsh_lt_b : fm.shadowCode b - 1 < bp.bktCount b := hbb ▸ hsh_lt
            have hbd1_b : 4 * fm.shadowIns b + 5 * (bp.bktCount b - (fm.shadowCode b - 1)) ≤
                20 * slabScale fl.N ^ 12 := by simpa [hbb] using hbd1
            have hbd2_b : 8 * (fm.curIns b - 6 * slabScale fl.N ^ 12) +
                (bp.bktCount b - (fm.shadowCode b - 1)) ≤ 4 * slabScale fl.N ^ 12 := by
              simpa [hbb] using hbd2
            refine ⟨hsh_lt_b, hbb ▸ hnt, by rw [heff]; omega, by rw [heff]; omega,
              Function.update shMap₀ fp_L (some delLoc), ?_, fun fp => ?_⟩
            · rw [hoth3 b hb _ hsr_p.1 (Or.inr htr_ne_sh.symm)]
              have hv2 := (hact2 (by rwa [hfm1])).2
              rwa [hfm1] at hv2
            · by_cases hfe : fp = fp_L
              · rw [hfe, Function.update_self, Function.update_self, Function.update_self]
                exact (ite_eq_left hdl_lt).symm
              · rw [Function.update_of_ne hfe, Function.update_self, Function.update_of_ne hfe]
                have hspec := (hsh_ex hsc_b).choose_spec.2.2 fp
                dsimp only [shMap₀]; rw [dite_eq_left hsc_b]; exact hspec
          · have hc_b : ¬(fm.shadowCode b ≠ 0 ∧ delLoc < fm.shadowCode b - 1) :=
              fun h => hdl_lt h.2
            rw [hbb, hsi_eq', ite_eq_right hc_b]
            have hsh_lt_b : fm.shadowCode b - 1 < bp.bktCount b := hbb ▸ hsh_lt
            have hbd1_b : 4 * fm.shadowIns b + 5 * (bp.bktCount b - (fm.shadowCode b - 1)) ≤
                20 * slabScale fl.N ^ 12 := by simpa [hbb] using hbd1
            have hbd2_b : 8 * (fm.curIns b - 6 * slabScale fl.N ^ 12) +
                (bp.bktCount b - (fm.shadowCode b - 1)) ≤ 4 * slabScale fl.N ^ 12 := by
              simpa [hbb] using hbd2
            refine ⟨hsh_lt_b, hbb ▸ hnt, by rw [heff]; omega, by rw [heff]; omega,
              sm, ?_, fun fp => ?_⟩
            · have hs2_eq : s2 = s1 := hnoop2 (by rwa [hfm1])
              rw [hoth3 b hb _ hsr_p.1 (Or.inr htr_ne_sh.symm), hs2_eq,
                hoth1 b hb _ hsr_p.1 (Or.inr hsr_p.2)]
              exact hbb ▸ hvs
            · by_cases hfe : fp = fp_L
              · have heq_b : sm fp_L = match mapBTree b fp_L with
                    | some loc' => if loc' < fm.shadowCode b - 1 then some loc' else none
                    | none => none := hbb ▸ heq fp_L
                rw [hfe, Function.update_self, Function.update_self, heq_b, hmb_L]
                dsimp only
                rw [ite_eq_right (by omega : ¬(lastLoc < fm.shadowCode b - 1)),
                  ite_eq_right hdl_lt]
              · rw [Function.update_self, Function.update_of_ne hfe]
                exact hbb ▸ heq fp
        · have heff : (if (true : Bool) ∧ b' = b then bp.bktCount b' - 1 else bp.bktCount b') =
              bp.bktCount b' := by simp [hbb]
          have hsi_eq' : (extractFastMeta fl s3.mem).shadowIns b' = fm.shadowIns b' :=
            (congrFun hfm3_other.2.2.2.2.2.2.2.2.2 b').trans
              (hfm2_core.2.2.2.2.2.2.2.2.2.2.2.2.1 b' hbb)
          dsimp only
          rw [hsi_eq', heff]
          refine ⟨hsh_lt, hnt, by simpa using hbd1, by simpa using hbd2, sm, ?_,
            fun fp => by rw [Function.update_of_ne hbb]; exact heq fp⟩
          rw [hoth3 b' hb' _ hsr' (Or.inl hbb), hoth2 b' hb' _ hsr' (Or.inl hbb),
            hoth1 b' hb' _ hsr' (Or.inl hbb)]
          exact hvs
      tryAct_le := by rw [hfm3_other.2.2.2.1]; exact ht.tryAct_le
      try_ok := fun hta1 => by
        have hta0 : fm.tryAct = 1 := by rwa [hfm3_other.2.2.2.1] at hta1
        obtain ⟨hsub, hb_t, hs_t, htp, hsc_t, hbd, tm, hvt, htm1, htm2⟩ := ht.try_ok hta0
        have htb_eq : (extractFastMeta fl s3.mem).tryBkt = fm.tryBkt := hfm3_other.2.2.2.2.1
        have hcr_eq : (extractFastMeta fl s3.mem).curRole fm.tryBkt = fm.curRole fm.tryBkt :=
          congrFun hfm3_other.2.2.2.2.2.2.1 fm.tryBkt
        have hbs_eq : (extractFastMeta fl s3.mem).bktSalt fm.tryBkt = fm.bktSalt fm.tryBkt :=
          congrFun hfm3_other.2.2.2.2.2.1 fm.tryBkt
        by_cases htb : fm.tryBkt = b
        · have hc : fm.tryAct = 1 ∧ fm.tryBkt = b := ⟨hta0, htb⟩
          have hact2' : (extractFastMeta fl s2.mem).tryAct = 1 :=
            hfm2_core.2.2.2.1.trans hta0
          have htb2' : (extractFastMeta fl s2.mem).tryBkt = b :=
            hfm2_core.2.2.2.2.1.trans htb
          have hs_t2 : (extractFastMeta fl s2.mem).trySalt < sMaxWhp fl.c fl.N := by
            rw [hfm2_core.2.2.2.2.2.1]; exact hs_t
          obtain ⟨h_lt, h_ins⟩ := hact3 hact2' htb2' hs_t2
          have hbd_b : 4 * fm.tryIns + 5 * (bp.bktCount b - fm.tryPos) ≤
              20 * slabScale fl.N ^ 12 := by
            have h : 4 * (extractFastMeta fl s.mem).tryIns +
                5 * ((extractBlockPool fl.mp s.mem).bktCount (extractFastMeta fl s.mem).tryBkt -
                  (extractFastMeta fl s.mem).tryPos) ≤ 20 * slabScale fl.N ^ 12 := by
              simpa using hbd
            have htb' : (extractFastMeta fl s.mem).tryBkt = b := htb
            rwa [htb'] at h
          have htp_b : fm.tryPos ≤ bp.bktCount b := by rwa [htb] at htp
          by_cases hlt : lastLoc < fm.tryPos
          · have ⟨hfm3_eq, hvt3⟩ := h_lt (by rwa [hfm2_core.2.2.2.2.2.2.1])
            have hts3 : (extractFastMeta fl s3.mem).trySalt = fm.trySalt :=
              (congrArg FastEpochMeta.trySalt hfm3_eq).trans hfm2_core.2.2.2.2.2.1
            have htp3 : (extractFastMeta fl s3.mem).tryPos = fm.tryPos :=
              (congrArg FastEpochMeta.tryPos hfm3_eq).trans hfm2_core.2.2.2.2.2.2.1
            have hti3 : (extractFastMeta fl s3.mem).tryIns = fm.tryIns :=
              (congrArg FastEpochMeta.tryIns hfm3_eq).trans hfm2_core.2.2.2.2.2.2.2.1
            have hbd_post : 4 * (extractFastMeta fl s3.mem).tryIns +
                5 * ((if (true : Bool) ∧ (extractFastMeta fl s3.mem).tryBkt = b then
                  (extractBlockPool fl.mp s3.mem).bktCount (extractFastMeta fl s3.mem).tryBkt - 1
                else (extractBlockPool fl.mp s3.mem).bktCount (extractFastMeta fl s3.mem).tryBkt) -
                  (extractFastMeta fl s3.mem).tryPos) ≤ 20 * slabScale fl.N ^ 12 := by
              rw [htb_eq, htb, hbp_tot, hti3, htp3]; simp only [true_and, ite_true]; omega
            refine ⟨by rw [hfm3_other.2.1]; exact hsub, by rw [htb_eq]; exact hb_t,
              by rw [hts3]; exact hs_t, by rw [hbp_tot, htb_eq, htp3]; exact htp,
              by rw [htb_eq, congrFun hfm3_other.2.2.2.2.2.2.2.2.1 _]; exact hsc_t,
              hbd_post, Function.update tryMap₀
                (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ uLast).val (some delLoc),
              ?_, ?_, ?_⟩
            · rw [htb_eq, hcr_eq, hti3, htb]
              rw [hfm2_core.2.2.2.2.2.2.2.1,
                congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t)
                  hfm2_core.2.2.2.2.2.1 uLast)] at hvt3
              exact hvt3
            · intro fp' loc' hm
              set fpT_L := (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ uLast).val
              by_cases hfe : fp' = fpT_L
              · rw [hfe, Function.update_self] at hm
                have hle : loc' = delLoc := (Option.some.inj hm).symm
                refine ⟨by rw [htp3, hle]; omega, fun h => by omega, uLast,
                  by rw [htb_eq, htb, hle, hke b delLoc hb (by omega), hkey_del], ?_,
                  by rw [congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts3 uLast), hfe]⟩
                exact (mapBTree_fpHash_congr
                  (Function.update mapBTree b (Function.update (mapBTree b) fp_L (some delLoc)))
                  (htb_eq.trans htb)
                  (by rw [htb_eq, hbs_eq, htb]) uLast).trans
                  (by rw [Function.update_self, Function.update_self, hle])
              · rw [Function.update_of_ne hfe] at hm
                dsimp only [tryMap₀] at hm; rw [dite_eq_left hc] at hm
                obtain ⟨hlt', hne_d, u', hk', hmb', hf'⟩ :=
                  (htry_ex hc).choose_spec.choose_spec.2.2.2.2.1 fp' loc' hm
                have hne_last : loc' ≠ lastLoc := fun h => by
                  have hk_eq : fastKeyAt fl seeds.bkt s.mem b lastLoc = u'.val := by rwa [h] at hk'
                  have hu' : u' = uLast := Fin.ext (hk_eq.symm.trans hkey_last)
                  exact hfe (hf'.symm.trans (by rw [hu']))
                have hfp_ne : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_b⟩ u').val ≠
                    fp_L := fun hf =>
                  hne_last (Option.some.inj (hmb'.symm.trans (by rw [hf]; exact hmb_L)))
                refine ⟨by rw [htp3]; exact hlt', fun h => hne_last h.2, u',
                  by rw [htb_eq, htb]; exact (hke b loc' hb (by omega)).trans hk', ?_,
                  (congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts3 u')).trans hf'⟩
                exact (mapBTree_fpHash_congr
                  (Function.update mapBTree b (Function.update (mapBTree b) fp_L (some delLoc)))
                  (htb_eq.trans htb) (by rw [htb_eq, hbs_eq, htb]) u').trans
                  (by rw [Function.update_self, Function.update_of_ne hfp_ne]; exact hmb')
            · intro loc' hlt' hne u' hk' hmb'
              have hlt0 : loc' < fm.tryPos := by rwa [htp3] at hlt'
              have hk_b : fastKeyAt fl seeds.bkt s.mem b loc' = u'.val := by
                have hk3 : fastKeyAt fl seeds.bkt s3.mem b loc' = u'.val := by
                  rwa [htb_eq, htb] at hk'
                exact (hke b loc' hb (by omega)).symm.trans hk3
              rw [congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts3 u')]
              by_cases hdl_eq : loc' = delLoc
              · have hu' : u' = uLast := Fin.ext ((hdl_eq ▸ hk_b).symm.trans hkey_del)
                rw [hu', hdl_eq, Function.update_self]
              · have hne_l : loc' ≠ lastLoc := fun h => hne ⟨htb_eq.trans htb, h⟩
                have hmb_b : Function.update (mapBTree b) fp_L (some delLoc)
                    (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_b⟩ u').val = some loc' := by
                  have h := (mapBTree_fpHash_congr
                    (Function.update mapBTree b (Function.update (mapBTree b) fp_L (some delLoc)))
                    (htb_eq.trans htb) (by rw [htb_eq, hbs_eq, htb])
                    u' (h₂ := hs_b)).symm.trans hmb'
                  simpa only [Function.update_self] using h
                have hfp_ne : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_b⟩ u').val ≠
                    fp_L := fun hf => by
                  rw [hf, Function.update_self] at hmb_b; exact hdl_eq (Option.some.inj hmb_b).symm
                rw [Function.update_of_ne hfp_ne] at hmb_b
                have hfpt_ne : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u').val ≠
                    (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ uLast).val := fun hf => by
                  have h1 := (htry_ex hc).choose_spec.choose_spec.2.2.2.2.2
                    loc' hlt0 hdl_eq u' hk_b hmb_b
                  have h2 := (htry_ex hc).choose_spec.choose_spec.2.2.1 hlt
                  exact hne_l (Option.some.inj (h1.symm.trans (by rw [hf]; exact h2)))
                rw [Function.update_of_ne hfpt_ne]
                dsimp only [tryMap₀]; rw [dite_eq_left hc]
                exact (htry_ex hc).choose_spec.choose_spec.2.2.2.2.2
                  loc' hlt0 hdl_eq u' hk_b hmb_b
          · by_cases hdl : delLoc < fm.tryPos
            · rcases h_ins (by rwa [hfm2_core.2.2.2.2.2.2.1])
                (by rwa [hfm2_core.2.2.2.2.2.2.1]) with ⟨hnone, hfm3_eq, hvt3⟩ |
                  ⟨_, _, hfm3_eq, hvz⟩
              · -- Inserted `fpT_L → delLoc` (`tryIns → tryIns + 1`, no collision)
                have hts3 : (extractFastMeta fl s3.mem).trySalt = fm.trySalt :=
                  (congrArg FastEpochMeta.trySalt hfm3_eq).trans hfm2_core.2.2.2.2.2.1
                have htp3 : (extractFastMeta fl s3.mem).tryPos = fm.tryPos :=
                  (congrArg FastEpochMeta.tryPos hfm3_eq).trans hfm2_core.2.2.2.2.2.2.1
                have hti3 : (extractFastMeta fl s3.mem).tryIns = fm.tryIns + 1 :=
                  (congrArg FastEpochMeta.tryIns hfm3_eq).trans
                    (by rw [hfm2_core.2.2.2.2.2.2.2.1])
                have hnone0 : tryMap₀
                    (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ uLast).val = none := by
                  rwa [congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t)
                    hfm2_core.2.2.2.2.2.1 uLast)] at hnone
                have hbd_post : 4 * (extractFastMeta fl s3.mem).tryIns +
                    5 * ((if (true : Bool) ∧ (extractFastMeta fl s3.mem).tryBkt = b then
                      (extractBlockPool fl.mp s3.mem).bktCount
                        (extractFastMeta fl s3.mem).tryBkt - 1
                    else (extractBlockPool fl.mp s3.mem).bktCount
                      (extractFastMeta fl s3.mem).tryBkt) -
                      (extractFastMeta fl s3.mem).tryPos) ≤ 20 * slabScale fl.N ^ 12 := by
                  rw [htb_eq, htb, hbp_tot, hti3, htp3]; simp only [true_and, ite_true]; omega
                refine ⟨by rw [hfm3_other.2.1]; exact hsub, by rw [htb_eq]; exact hb_t,
                  by rw [hts3]; exact hs_t, by rw [hbp_tot, htb_eq, htp3]; exact htp,
                  by rw [htb_eq, congrFun hfm3_other.2.2.2.2.2.2.2.2.1 _]; exact hsc_t,
                  hbd_post, Function.update tryMap₀
                    (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ uLast).val (some delLoc),
                  ?_, ?_, ?_⟩
                · rw [htb_eq, hcr_eq, hti3, htb]
                  rw [hfm2_core.2.2.2.2.2.2.2.1,
                    congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t)
                      hfm2_core.2.2.2.2.2.1 uLast)] at hvt3
                  exact hvt3
                · intro fp' loc' hm
                  set fpT_L := (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ uLast).val
                  by_cases hfe : fp' = fpT_L
                  · rw [hfe, Function.update_self] at hm
                    have hle : loc' = delLoc := (Option.some.inj hm).symm
                    refine ⟨by rw [htp3, hle]; exact hdl, fun h => by omega, uLast,
                      by rw [htb_eq, htb, hle, hke b delLoc hb (by omega), hkey_del], ?_,
                      by rw [congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts3 uLast), hfe]⟩
                    exact (mapBTree_fpHash_congr
                      (Function.update mapBTree b
                        (Function.update (mapBTree b) fp_L (some delLoc)))
                      (htb_eq.trans htb) (by rw [htb_eq, hbs_eq, htb]) uLast).trans
                      (by rw [Function.update_self, Function.update_self, hle])
                  · rw [Function.update_of_ne hfe] at hm
                    dsimp only [tryMap₀] at hm; rw [dite_eq_left hc] at hm
                    obtain ⟨hlt', hne_d, u', hk', hmb', hf'⟩ :=
                      (htry_ex hc).choose_spec.choose_spec.2.2.2.2.1 fp' loc' hm
                    have hne_last : loc' ≠ lastLoc := by omega
                    have hfp_ne : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_b⟩ u').val ≠
                        fp_L := fun hf =>
                      hne_last (Option.some.inj (hmb'.symm.trans (by rw [hf]; exact hmb_L)))
                    refine ⟨by rw [htp3]; exact hlt', fun h => hne_last h.2, u',
                      by rw [htb_eq, htb]; exact (hke b loc' hb (by omega)).trans hk', ?_,
                      (congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts3 u')).trans hf'⟩
                    exact (mapBTree_fpHash_congr
                      (Function.update mapBTree b
                        (Function.update (mapBTree b) fp_L (some delLoc)))
                      (htb_eq.trans htb) (by rw [htb_eq, hbs_eq, htb]) u').trans
                      (by rw [Function.update_self, Function.update_of_ne hfp_ne]; exact hmb')
                · intro loc' hlt' _ u' hk' hmb'
                  have hlt0 : loc' < fm.tryPos := by rwa [htp3] at hlt'
                  have hk_b : fastKeyAt fl seeds.bkt s.mem b loc' = u'.val :=
                    (hke b loc' hb (by omega)).symm.trans (by rwa [htb_eq, htb] at hk')
                  rw [congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts3 u')]
                  by_cases hdl_eq : loc' = delLoc
                  · have hu' : u' = uLast := Fin.ext ((hdl_eq ▸ hk_b).symm.trans hkey_del)
                    rw [hu', hdl_eq, Function.update_self]
                  · have hmb_b : Function.update (mapBTree b) fp_L (some delLoc)
                        (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_b⟩ u').val =
                        some loc' := by
                      have := (mapBTree_fpHash_congr
                        (Function.update mapBTree b
                          (Function.update (mapBTree b) fp_L (some delLoc)))
                        (htb_eq.trans htb) (by rw [htb_eq, hbs_eq, htb])
                        (h₂ := hs_b) u').symm.trans hmb'
                      simpa only [Function.update_self] using this
                    have hfp_ne : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_b⟩ u').val ≠
                        fp_L := fun hf => by
                      rw [hf, Function.update_self] at hmb_b
                      exact hdl_eq (Option.some.inj hmb_b).symm
                    rw [Function.update_of_ne hfp_ne] at hmb_b
                    have htm_u' : tryMap₀
                        (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u').val =
                        some loc' := by
                      dsimp only [tryMap₀]; rw [dite_eq_left hc]
                      exact (htry_ex hc).choose_spec.choose_spec.2.2.2.2.2
                        loc' hlt0 hdl_eq u' hk_b hmb_b
                    have hfpt_ne : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u').val ≠
                        (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ uLast).val :=
                      fun hf => by rw [hf, hnone0] at htm_u'; cases htm_u'
                    rw [Function.update_of_ne hfpt_ne]; exact htm_u'
              · -- Collision! `advanceTrySaltProg` reset `tryPos := 0, tryIns := 0`
                have hts3 : (extractFastMeta fl s3.mem).trySalt =
                    if fm.trySalt + 1 < sMaxWhp fl.c fl.N then fm.trySalt + 1 else 0 :=
                  (congrArg FastEpochMeta.trySalt hfm3_eq).trans
                    (by rw [hfm2_core.2.2.2.2.2.1])
                have htp3 : (extractFastMeta fl s3.mem).tryPos = 0 :=
                  congrArg FastEpochMeta.tryPos hfm3_eq
                have hti3 : (extractFastMeta fl s3.mem).tryIns = 0 :=
                  congrArg FastEpochMeta.tryIns hfm3_eq
                have hns_lt : (extractFastMeta fl s3.mem).trySalt < sMaxWhp fl.c fl.N := by
                  rw [hts3]; split_ifs with h <;> [exact h; exact Nat.zero_lt_of_lt hs_t]
                have hbd_post : 4 * (extractFastMeta fl s3.mem).tryIns +
                    5 * ((if (true : Bool) ∧ (extractFastMeta fl s3.mem).tryBkt = b then
                      (extractBlockPool fl.mp s3.mem).bktCount
                        (extractFastMeta fl s3.mem).tryBkt - 1
                    else (extractBlockPool fl.mp s3.mem).bktCount
                      (extractFastMeta fl s3.mem).tryBkt) -
                      (extractFastMeta fl s3.mem).tryPos) ≤ 20 * slabScale fl.N ^ 12 := by
                  rw [htb_eq, htb, hbp_tot, hti3, htp3]
                  have hcap_b : bp.bktCount b ≤ 4 * slabScale fl.N ^ 12 := hcnt_le
                  simp only [true_and, ite_true]
                  omega
                refine ⟨by rw [hfm3_other.2.1]; exact hsub, by rw [htb_eq]; exact hb_t,
                  hns_lt, by rw [htp3]; exact Nat.zero_le _,
                  by rw [htb_eq, congrFun hfm3_other.2.2.2.2.2.2.2.2.1 _]; exact hsc_t,
                  hbd_post, fun _ => none,
                  by rw [htb_eq, hcr_eq, hti3, htb]; exact hvz,
                  fun _ _ hm => by simp at hm,
                  fun loc' hlt' _ => False.elim
                    (Nat.not_lt_zero loc' (by rw [htp3] at hlt'; exact hlt'))⟩
            · -- `fm.tryPos ≤ delLoc < lastLoc`: no-op!
              have hs3_eq : s3 = s2 := hnoop3
                ⟨Or.inr (by rwa [hfm2_core.2.2.2.2.2.2.1]),
                  fun h => hlt (hfm2_core.2.2.2.2.2.2.1 ▸ h.2.2)⟩
              have hts3 : (extractFastMeta fl s3.mem).trySalt = fm.trySalt := by
                rw [hs3_eq]; exact hfm2_core.2.2.2.2.2.1
              have htp3 : (extractFastMeta fl s3.mem).tryPos = fm.tryPos := by
                rw [hs3_eq]; exact hfm2_core.2.2.2.2.2.2.1
              have hti3 : (extractFastMeta fl s3.mem).tryIns = fm.tryIns := by
                rw [hs3_eq]; exact hfm2_core.2.2.2.2.2.2.2.1
              have hbd_post : 4 * (extractFastMeta fl s3.mem).tryIns +
                  5 * ((if (true : Bool) ∧ (extractFastMeta fl s3.mem).tryBkt = b then
                    (extractBlockPool fl.mp s3.mem).bktCount (extractFastMeta fl s3.mem).tryBkt - 1
                  else (extractBlockPool fl.mp s3.mem).bktCount
                    (extractFastMeta fl s3.mem).tryBkt) -
                    (extractFastMeta fl s3.mem).tryPos) ≤ 20 * slabScale fl.N ^ 12 := by
                rw [htb_eq, htb, hbp_tot, hti3, htp3]; simp only [true_and, ite_true]; omega
              refine ⟨by rw [hfm3_other.2.1]; exact hsub, by rw [htb_eq]; exact hb_t,
                by rw [hts3]; exact hs_t, by rw [hbp_tot, htb_eq, htp3]; exact htp,
                by rw [htb_eq, congrFun hfm3_other.2.2.2.2.2.2.2.2.1 _]; exact hsc_t,
                hbd_post, tm, ?_, ?_, ?_⟩
              · rw [htb_eq, hcr_eq, hti3, hs3_eq, htb,
                  hoth2 b hb _ htr_p.1 (Or.inr htr_ne_sh),
                  hoth1 b hb _ htr_p.1 (Or.inr htr_p.2.1)]
                rwa [htb] at hvt
              · intro fp' loc' hm
                obtain ⟨hlt', hne_d, u', hk', hmb', hf'⟩ := htm1 fp' loc' hm
                have hne_l : loc' ≠ lastLoc :=
                  Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt' (Nat.not_lt.mp hlt))
                have hmb_b : mapBTree b (fpHash fl.c fl.U fl.N seeds.fp
                    ⟨fm.bktSalt b, hs_b⟩ u').val = some loc' :=
                  (mapBTree_fpHash_congr mapBTree htb (congrArg fm.bktSalt htb) u').symm.trans hmb'
                have hfp_ne : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_b⟩ u').val ≠
                    fp_L := fun hf =>
                  hne_l (Option.some.inj (hmb_b.symm.trans (by rw [hf]; exact hmb_L)))
                refine ⟨by rw [htp3]; exact hlt', fun h => hne_l h.2, u',
                  by rw [htb_eq]; exact (hke _ loc' hb_t (lt_of_lt_of_le hlt' htp)).trans hk', ?_,
                  (congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts3 u')).trans hf'⟩
                exact (mapBTree_fpHash_congr
                  (Function.update mapBTree b (Function.update (mapBTree b) fp_L (some delLoc)))
                  (htb_eq.trans htb) (by rw [htb_eq, hbs_eq, htb]) u').trans
                  (by rw [Function.update_self, Function.update_of_ne hfp_ne]; exact hmb_b)
              · intro loc' hlt' _ u' hk' hmb'
                have hlt0 : loc' < fm.tryPos := by rwa [htp3] at hlt'
                have hne_d : ¬(fm.tryBkt = b ∧ loc' = delLoc) := fun ⟨_, hle⟩ =>
                  hdl (hle ▸ hlt0)
                have hmb_u' : Function.update mapBTree b
                    (Function.update (mapBTree b) fp_L (some delLoc)) b
                    (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_b⟩ u').val = some loc' :=
                  (mapBTree_fpHash_congr
                    (Function.update mapBTree b (Function.update (mapBTree b) fp_L (some delLoc)))
                    (htb_eq.trans htb) (by rw [htb_eq, hbs_eq, htb]) u').symm.trans hmb'
                rw [Function.update_self] at hmb_u'
                have hfp_ne : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_b⟩ u').val ≠
                    fp_L := fun hf => by
                  rw [hf, Function.update_self] at hmb_u'
                  exact hdl (Option.some.inj hmb_u' ▸ hlt0)
                rw [Function.update_of_ne hfp_ne] at hmb_u'
                rw [congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts3 u')]
                exact htm2 loc' hlt0 hne_d u'
                  ((hke _ loc' hb_t (lt_of_lt_of_le hlt0 htp)).symm.trans (htb_eq ▸ hk'))
                  ((mapBTree_fpHash_congr mapBTree htb (congrArg fm.bktSalt htb) u').trans hmb_u')
        · -- `fm.tryBkt ≠ b`: `s3 = s2`
          have hs3_eq : s3 = s2 := hnoop3
            ⟨Or.inl (fun h => htb ((hfm2_core.2.2.2.2.1 ▸ h.2))),
              fun h => htb (hfm2_core.2.2.2.2.1 ▸ h.2.1)⟩
          have hts3 : (extractFastMeta fl s3.mem).trySalt = fm.trySalt := by
            rw [hs3_eq]; exact hfm2_core.2.2.2.2.2.1
          have htp3 : (extractFastMeta fl s3.mem).tryPos = fm.tryPos := by
            rw [hs3_eq]; exact hfm2_core.2.2.2.2.2.2.1
          have hti3 : (extractFastMeta fl s3.mem).tryIns = fm.tryIns := by
            rw [hs3_eq]; exact hfm2_core.2.2.2.2.2.2.2.1
          have htr' := (tryRoleOf_lt_and_ne (ht.bkt_meta_bounds _ hb_t).2.1).1
          have hbd_post : 4 * (extractFastMeta fl s3.mem).tryIns +
              5 * ((if (true : Bool) ∧ (extractFastMeta fl s3.mem).tryBkt = b then
                (extractBlockPool fl.mp s3.mem).bktCount (extractFastMeta fl s3.mem).tryBkt - 1
              else (extractBlockPool fl.mp s3.mem).bktCount (extractFastMeta fl s3.mem).tryBkt) -
                (extractFastMeta fl s3.mem).tryPos) ≤ 20 * slabScale fl.N ^ 12 := by
            rw [htb_eq, hbp_tot, hti3, htp3]; simp only [htb, and_false, ite_false]; exact hbd
          refine ⟨by rw [hfm3_other.2.1]; exact hsub, by rw [htb_eq]; exact hb_t,
            by rw [hts3]; exact hs_t, by rw [hbp_tot, htb_eq, htp3]; exact htp,
            by rw [htb_eq, congrFun hfm3_other.2.2.2.2.2.2.2.2.1 _]; exact hsc_t,
            hbd_post, tm, ?_, ?_, ?_⟩
          · rw [htb_eq, hcr_eq, hti3, hs3_eq, hoth2 _ hb_t _ htr' (Or.inl htb),
              hoth1 _ hb_t _ htr' (Or.inl htb)]
            exact hvt
          · intro fp' loc' hm
            obtain ⟨hlt', _, u', hk', hmb', hf'⟩ := htm1 fp' loc' hm
            have hlb := lt_of_lt_of_le hlt' htp
            refine ⟨by rw [htp3]; exact hlt', fun h => htb (htb_eq.symm.trans h.1), u',
              by rw [htb_eq]; exact (hke _ loc' hb_t hlb).trans hk', ?_,
              (congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts3 u')).trans hf'⟩
            exact (mapBTree_fpHash_congr
              (Function.update mapBTree b (Function.update (mapBTree b) fp_L (some delLoc)))
              htb_eq (by rw [htb_eq, hbs_eq]) u').trans
              (by rw [Function.update_of_ne htb]; exact hmb')
          · intro loc' hlt' _ u' hk' hmb'
            have hlt0 : loc' < fm.tryPos := by rwa [htp3] at hlt'
            have hlb := lt_of_lt_of_le hlt0 htp
            have hmb0 : Function.update mapBTree b
                (Function.update (mapBTree b) fp_L (some delLoc)) fm.tryBkt
                (fpHash fl.c fl.U fl.N seeds.fp
                  ⟨fm.bktSalt fm.tryBkt, (ht.bkt_meta_bounds _ hb_t).1⟩ u').val = some loc' :=
              (mapBTree_fpHash_congr
                (Function.update mapBTree b (Function.update (mapBTree b) fp_L (some delLoc)))
                htb_eq (by rw [htb_eq, hbs_eq]) u').symm.trans hmb'
            rw [Function.update_of_ne htb] at hmb0
            rw [congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts3 u')]
            exact htm2 loc' hlt0 (fun h => htb h.1) u'
              ((hke _ loc' hb_t hlb).symm.trans (htb_eq ▸ hk')) hmb0 }

private theorem fastRelocLastProg_spec {slackCur : ℕ} {fl : FastEpochLayout}
    {w b delLoc lastLoc : ℕ} {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s : Memory.State} (uLast : Fin fl.U)
    (hslack : slackCur ≤ 1)
    (hr : FastLayoutReady w fl s)
    (hbp_inv : fl.bpL.StateInv 0 s.mem)
    (hfp_rep : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp s.mem)
    (hb : b < numBucketsWhp fl.N)
    (hcnt_le : (extractBlockPool fl.mp s.mem).bktCount b ≤ capMaxWhp fl.N)
    (hlast_eq : (extractBlockPool fl.mp s.mem).bktCount b = lastLoc + 1)
    (hdel_lt : delLoc < lastLoc)
    (hkey_del : fastKeyAt fl seeds.bkt s.mem b delLoc = uLast.val)
    (hkey_last : fastKeyAt fl seeds.bkt s.mem b lastLoc = uLast.val)
    (ht : TierInvHole slackCur fl seeds s.mem b delLoc false)
    (hkey_ne_other : ∀ loc' < lastLoc, loc' ≠ delLoc →
      fastKeyAt fl seeds.bkt s.mem b loc' ≠ uLast.val) :
    let fm := extractFastMeta fl s.mem
    let bp := extractBlockPool fl.mp s.mem
    let oldRole := 1 - fm.curBufRole
    let oldTr := extractBufTrie (fl.trieL oldRole) s.mem
    let s' := (Memory.spec 0).clientState s
      (fastRelocLastProg ((fl.pBase, (b, delLoc)), (lastLoc, uLast.val)))
    let fm' := extractFastMeta fl s'.mem
    let oldTr' := extractBufTrie (fl.trieL oldRole) s'.mem
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastRelocLastProg ((fl.pBase, (b, delLoc)), (lastLoc, uLast.val))) s ≤
      30 * cTabWhp fl.c + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 156 * hMaxBTree + 560 ∧
    extractBlockPool fl.mp s'.mem = bp ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    oldTr'.itemAlloc = oldTr.itemAlloc ∧
    (∀ id b' loc', bufCheckSlot oldTr' id = some (b', loc') →
      bufCheckSlot oldTr id = some (b', loc') ∨
      (b' = b ∧ loc' = delLoc ∧ bufCheckSlot oldTr id = some (b, lastLoc))) ∧
    fm'.curBufRole = fm.curBufRole ∧
    fm'.subStep = fm.subStep ∧
    fm'.drainPos = fm.drainPos ∧
    fm'.tryAct = fm.tryAct ∧
    fm'.tryBkt = fm.tryBkt ∧
    fm'.bktSalt = fm.bktSalt ∧
    fm'.curRole = fm.curRole ∧
    fm'.curIns = fm.curIns ∧
    fm'.shadowCode = fm.shadowCode ∧
    (∀ b' ≠ b, fm'.shadowIns b' = fm.shadowIns b') ∧
    fm'.shadowIns b ≤ fm.shadowIns b + 1 ∧
    (fm'.shadowCode b = 0 ∨ ¬(delLoc < fm.shadowCode b - 1) → fm'.shadowIns b = fm.shadowIns b) ∧
    ((fm'.trySalt = fm.trySalt ∧ fm'.tryPos = fm.tryPos) ∨
      (fm.tryAct = 1 ∧ fm.tryBkt = b ∧ delLoc < fm.tryPos ∧ fm.tryPos ≤ lastLoc ∧
        fm'.trySalt = (if fm.trySalt + 1 < sMaxWhp fl.c fl.N then fm.trySalt + 1 else 0) ∧
        fm'.tryPos = 0 ∧ fm'.tryIns = 0 ∧
        ∃ (hs_t : fm.trySalt < sMaxWhp fl.c fl.N) (wLoc : ℕ) (wKey : Fin fl.U),
          wLoc < lastLoc ∧ wLoc ≠ delLoc ∧ wKey ≠ uLast ∧
          fastKeyAt fl seeds.bkt s.mem b wLoc = wKey.val ∧
          fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ wKey =
            fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ uLast)) ∧
    TierInvHole slackCur fl seeds s'.mem b lastLoc true := by
  dsimp only
  rcases ht with ⟨mapCur, mapOld, mapBTree, ht⟩
  have hv := hr.1
  have hpt := hr.2.1
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  set Q := qEpochWhp fl.N
  set rk := rKeyOf fl.c fl.U fl.N seeds.fp uLast
  have hlast_lt : lastLoc < bp.bktCount b := by omega
  have hrk_lt : rk < 2 ^ (cTabWhp fl.c * bCharWhp fl.N) :=
    rKeyOf_lt fl.c fl.U fl.N seeds.fp uLast
  have hrole_lt : fm.curBufRole < 2 := ht.role_lt
  have hold_lt : 1 - fm.curBufRole < 2 := by omega
  have hN_ptr : fl.N < 2 ^ globalPtrBits fl.N := hv.mp_valid.nCap_lt_ptrB
  have hb_ptr : b < 2 ^ globalPtrBits fl.N := by
    have hM_le : numBucketsWhp fl.N ≤ fl.N := by
      have hb_le : bWhp fl.N ≤ Nat.log 2 fl.N := by unfold bWhp; omega
      have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hv.thresh_le
      exact (Nat.pow_le_pow_right (by decide) hb_le).trans (Nat.pow_log_le_self 2 hN_pos.ne')
    exact lt_of_lt_of_le (lt_of_lt_of_le hb hM_le) (Nat.le_of_lt hN_ptr)
  have hdl_ptr : delLoc < 2 ^ globalPtrBits fl.N := by
    have hcap := hv.bounds_le_N.2.1
    omega
  have hmax_t := cTab_add_one_mul_le_maxTrieNodes hv.thresh_le
  obtain ⟨hrk_r, hrk_c⟩ := fastRKeyProg_spec hr hfp_rep uLast
  have hr3_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 3)) = fm.curBufRole :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hc3 := memoryCost_fastReadMetaProg (fl.pBase, 3) s
  have hcur_spec := fastBufLookupProg_spec hr hrole_lt ht.cur_valid hrk_lt
  have hc_cost_r : memoryCost (fastRKeyProg (fl.pBase, uLast.val)) s ≤
      2 * cTabWhp fl.c + 20 := by
    have := hrk_c; omega
  have hia_cur_b : (extractBufTrie (fl.trieL fm.curBufRole) s.mem).itemAlloc ≤
      qEpochWhp fl.N := by
    have h1 : (extractBufTrie (fl.trieL fm.curBufRole) s.mem).itemAlloc ≤
        fm.subStep + slackCur := ht.cur_ia
    have h2 : fm.subStep < qEpochWhp fl.N := ht.subStep_lt
    omega
  have hna_cur_le : (extractBufTrie (fl.trieL fm.curBufRole) s.mem).nodeAlloc + cTabWhp fl.c ≤
      maxTrieNodesWhp fl.c fl.N := by
    have hna : (extractBufTrie (fl.trieL fm.curBufRole) s.mem).nodeAlloc ≤
        1 + cTabWhp fl.c * qEpochWhp fl.N :=
      ht.cur_na.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hia_cur_b) 1)
    exact (Nat.add_le_add_right hna _).trans hmax_t
  unfold fastRelocLastProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastRKeyProg, hrk_r,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hr3_r, ite_eq_left hrole_lt,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastBufLookupProg]
  by_cases hcur_hit : mapCur rk = some (b, lastLoc)
  · rw [hcur_spec.1, hcur_hit]; dsimp only; rw [ite_eq_left ⟨rfl, rfl, rfl⟩]
    obtain ⟨hfr, hr', hci, hext, hv_c', hbp', hfm', hm2', hm0', hbt', htr_o, hoi, hof⟩ :=
      fastBufInsertProg_update_spec hr hrole_lt ht.cur_valid ht.cur_raw hna_cur_le hia_cur_b
        (by rw [hcur_hit]; exact Option.some_ne_none _) hrk_lt hb_ptr hdl_ptr
    generalize hs1_def : (Memory.spec 0).clientState s
      (fastBufInsertProg ((fl.pBase, fm.curBufRole), (rk, (b, delLoc)))) = s1
    rw [hs1_def] at hfr hr' hext hv_c' hbp' hfm' hm2' hm0' hbt' htr_o hoi hof
    obtain ⟨hna_eq, hia_eq, hrb_f, hrc_f, _, _⟩ :=
      bufInsert_active_props ht.cur_valid hrk_lt hcur_hit (b := b) (loc := delLoc)
    have hke : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
        fastKeyAt fl seeds.bkt s1.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
      fun b' loc' hb' hl' => fastKeyAt_eq_of_fixed_pool hv hbp_inv hbp' hoi hb' hl'
    have hcl_c : memoryCost (fastBufLookupProg ((fl.pBase, fm.curBufRole), rk)) s ≤
        2 * cTabWhp fl.c + 18 := hcur_spec.2
    have hci_c : memoryCost (fastBufInsertProg ((fl.pBase, fm.curBufRole), (rk, (b, delLoc)))) s ≤
        24 * cTabWhp fl.c + 42 := hci
    have hcost_eq : memoryCost (fastRKeyProg (fl.pBase, uLast.val)) s +
        memoryCost (fastReadMetaProg (fl.pBase, 3)) s +
        memoryCost (fastBufLookupProg ((fl.pBase, fm.curBufRole), rk)) s +
        memoryCost (fastBufInsertProg ((fl.pBase, fm.curBufRole), (rk, (b, delLoc)))) s ≤
        30 * cTabWhp fl.c + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 156 * hMaxBTree + 560 := by
      omega
    have hfm_sh : (extractFastMeta fl s1.mem).shadowIns b = fm.shadowIns b :=
      congrFun (congrArg FastEpochMeta.shadowIns hfm') b
    refine ⟨hfr, hr', by linarith only [hcost_eq], hbp', hm0', hm2', hoi, hof,
      by rw [htr_o], fun id b' l' h => Or.inl (by rwa [htr_o] at h),
      by rw [hfm'], by rw [hfm'], by rw [hfm'], by rw [hfm'], by rw [hfm'],
      by rw [hfm'], by rw [hfm'], by rw [hfm'], by rw [hfm'],
      fun b' _ => congrFun (congrArg FastEpochMeta.shadowIns hfm') b',
      by rw [hfm_sh]; exact Nat.le_succ _,
      fun _ => hfm_sh, Or.inl ⟨by rw [hfm'], by rw [hfm']⟩,
      Function.update mapCur rk (some (b, delLoc)), mapOld, mapBTree, ?_⟩
    exact
      { role_lt := by rw [hfm']; exact hrole_lt
        subStep_lt := by rw [hfm']; exact ht.subStep_lt
        bkt_meta_bounds := fun b' hb' => by rw [hfm']; exact ht.bkt_meta_bounds b' hb'
        cur_valid := by rw [hfm']; exact hv_c'
        cur_raw := by rw [hfm', hext]; exact hrb_f ht.cur_raw
        cur_clr := by rw [hfm', hext]; exact hrc_f ht.cur_clr
        cur_ia := by rw [hfm', hext, hia_eq]; exact ht.cur_ia
        cur_na := by rw [hfm', hext, hna_eq, hia_eq]; exact ht.cur_na
        cur_sound := fun rk' b' loc' hm => by
          by_cases hrke : rk' = rk
          · rw [hrke, Function.update_self] at hm
            have hp := Option.some.inj hm
            have hbe : b' = b := (congrArg Prod.fst hp).symm
            have hle : loc' = delLoc := (congrArg Prod.snd hp).symm
            rw [hbe, hle, hbp']
            have hdl_lt : delLoc < bp.bktCount b := lt_trans hdel_lt hlast_lt
            exact ⟨hb, hdl_lt, fun h => absurd h.2 (Nat.ne_of_lt hdel_lt), uLast, hrke.symm,
              (hke b delLoc hb hdl_lt).trans hkey_del⟩
          · rw [Function.update_of_ne hrke] at hm
            obtain ⟨hb', hl', _, u', hrk', hk'⟩ := ht.cur_sound rk' b' loc' hm
            refine ⟨hb', by rw [hbp']; exact hl', ?_, u', hrk', (hke b' loc' hb' hl').trans hk'⟩
            rintro ⟨hbe, hle⟩
            have hku : fastKeyAt fl seeds.bkt s.mem b lastLoc = u'.val := by rwa [hbe, hle] at hk'
            have hu' : u' = uLast := Fin.ext (hku.symm.trans hkey_last)
            exact hrke (hrk'.symm.trans (by rw [hu']))
        old_valid_half := fun hsub => by
          rw [hfm'] at hsub
          rw [hfm', htr_o, hbp']
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, hsnd⟩ := ht.old_valid_half hsub
          refine ⟨h1, h2, h3, h4, h5, h6, h7, fun rk' b' loc' hm => ?_⟩
          obtain ⟨hcn, hb', hl', _, u', hrk', hk'⟩ := hsnd rk' b' loc' hm
          have hrke : rk' ≠ rk := fun h => by subst h; rw [hcur_hit] at hcn; cases hcn
          refine ⟨by rw [Function.update_of_ne hrke]; exact hcn, hb', hl', ?_, u', hrk',
            (hke b' loc' hb' hl').trans hk'⟩
          rintro ⟨hbe, hle⟩
          have hku : fastKeyAt fl seeds.bkt s.mem b lastLoc = u'.val := by rwa [hbe, hle] at hk'
          have hu' : u' = uLast := Fin.ext (hku.symm.trans hkey_last)
          exact hrke (hrk'.symm.trans (by rw [hu']))
        old_clear_half := fun hsub => by
          rw [hfm'] at hsub ⊢; rw [htr_o]; exact ht.old_clear_half hsub
        bt_valid := fun b' hb' => by
          rw [hfm', hbt' b' hb' _ (ht.bkt_meta_bounds b' hb').2.1]; exact ht.bt_valid b' hb'
        bt_sound := fun b' hb' fp' loc' hm => by
          obtain ⟨hl', _, u', hfp', hk', hd1, hd2⟩ := ht.bt_sound b' hb' fp' loc' hm
          have hbs := congrArg (fun m => m.bktSalt b') hfm'
          refine ⟨by rw [hbp']; exact hl', ?_, u',
            (congrArg Fin.val
              (fpHash_congr_salt (h₂ := (ht.bkt_meta_bounds b' hb').1) hbs u')).trans
              hfp',
            (hke b' loc' hb' hl').trans hk', fun b₁ l₁ hm₁ => ?_, fun b₂ l₂ hm₂ => ?_⟩
          · rintro ⟨hbe, hle⟩
            have hku : fastKeyAt fl seeds.bkt s.mem b lastLoc = u'.val := by rwa [hbe, hle] at hk'
            have hu' : u' = uLast := Fin.ext (hku.symm.trans hkey_last)
            exact hd1 b lastLoc (by rw [hu']; exact hcur_hit) (by rw [hu']; exact hkey_last)
          · by_cases he : rKeyOf fl.c fl.U fl.N seeds.fp u' = rk
            · rw [he, Function.update_self] at hm₁
              have hp := Option.some.inj hm₁
              have hbe : b₁ = b := (congrArg Prod.fst hp).symm
              have hle : l₁ = delLoc := (congrArg Prod.snd hp).symm
              rw [hbe, hle]
              have hdl_lt : delLoc < bp.bktCount b := by omega
              rw [hke b delLoc hb hdl_lt, hkey_del]
              have := hd1 b lastLoc (by rw [he]; exact hcur_hit)
              rwa [hkey_last] at this
            · rw [Function.update_of_ne he] at hm₁
              obtain ⟨hb₁, hl₁, _⟩ := ht.cur_sound _ b₁ l₁ hm₁
              rw [hke b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁
          · have hsub : fm.subStep < Q / 2 := by
              by_contra hn; rw [(ht.old_clear_half hn).1] at hm₂; cases hm₂
            obtain ⟨_, hb₂, hl₂, _⟩ := (ht.old_valid_half hsub).2.2.2.2.2.2.2 _ b₂ l₂ hm₂
            rw [hke b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂
        complete := fun b' hb' loc' hl' hne => by
          rw [hbp'] at hl'
          by_cases hd : b' = b ∧ loc' = delLoc
          · obtain ⟨rfl, rfl⟩ := hd
            exact ⟨uLast, (hke b' loc' hb' hl').trans hkey_del,
              Or.inl (Function.update_self _ _ _)⟩
          · obtain ⟨u', hk', htier⟩ := ht.complete b' hb' loc' hl' hd
            refine ⟨u', (hke b' loc' hb' hl').trans hk', ?_⟩
            rcases htier with h1 | h2 | h3
            · by_cases he : rKeyOf fl.c fl.U fl.N seeds.fp u' = rk
              · rw [he, hcur_hit] at h1; cases h1; exact absurd ⟨rfl, rfl⟩ hne
              · exact Or.inl (by rw [Function.update_of_ne he]; exact h1)
            · exact Or.inr (Or.inl h2)
            · have hbs := congrArg (fun m => m.bktSalt b') hfm'
              exact Or.inr (Or.inr ((mapBTree_fpHash_congr mapBTree rfl hbs u').trans h3))
        shadow := fun b' hb' hsc => by
          have hsc0 : fm.shadowCode b' ≠ 0 := by rwa [hfm'] at hsc
          obtain ⟨h1, h2, h3, h4, sm, hvs, heq⟩ := ht.shadow b' hb' hsc0
          rw [hfm', hbp']
          have hsr := (shadowRoleOf_lt_and_ne (ht.bkt_meta_bounds b' hb').2.1).1
          have h3' : 4 * fm.shadowIns b' + 5 * ((if true = true ∧ b' = b then bp.bktCount b' - 1
              else bp.bktCount b') - (fm.shadowCode b' - 1)) ≤ 20 * slabScale fl.N ^ 12 := by
            have h3b : 4 * fm.shadowIns b' +
                5 * (bp.bktCount b' - (fm.shadowCode b' - 1)) ≤ 20 * slabScale fl.N ^ 12 := by
              simpa using h3
            split_ifs <;> omega
          have h4' : 8 * (fm.curIns b' - 6 * slabScale fl.N ^ 12) +
              ((if true = true ∧ b' = b then bp.bktCount b' - 1 else bp.bktCount b') -
                (fm.shadowCode b' - 1)) ≤ 4 * slabScale fl.N ^ 12 := by
            have h4b : 8 * (fm.curIns b' - 6 * slabScale fl.N ^ 12) +
                (bp.bktCount b' - (fm.shadowCode b' - 1)) ≤ 4 * slabScale fl.N ^ 12 := by
              simpa using h4
            split_ifs <;> omega
          exact ⟨h1, h2, h3', h4', sm, by rw [hbt' b' hb' _ hsr]; exact hvs, heq⟩
        tryAct_le := by rw [hfm']; exact ht.tryAct_le
        try_ok := fun hta1 => by
          have hta0 : fm.tryAct = 1 := by rwa [hfm'] at hta1
          obtain ⟨hsub, hb_t, hs_t, htp, hsc, hbd, tm, hvt, htm1, htm2⟩ := ht.try_ok hta0
          have htb_eq := congrArg FastEpochMeta.tryBkt hfm'
          have hts_eq := congrArg FastEpochMeta.trySalt hfm'
          have htp_eq := congrArg FastEpochMeta.tryPos hfm'
          have hti_eq := congrArg FastEpochMeta.tryIns hfm'
          have hcr_eq := congrArg (fun m => m.curRole fm.tryBkt) hfm'
          have hbs_eq := congrArg (fun m => m.bktSalt fm.tryBkt) hfm'
          have htr_lt := (tryRoleOf_lt_and_ne (ht.bkt_meta_bounds _ hb_t).2.1).1
          have hbd' : 4 * (extractFastMeta fl s1.mem).tryIns +
              5 * ((if true = true ∧ (extractFastMeta fl s1.mem).tryBkt = b then
                (extractBlockPool fl.mp s1.mem).bktCount (extractFastMeta fl s1.mem).tryBkt - 1
                else (extractBlockPool fl.mp s1.mem).bktCount (extractFastMeta fl s1.mem).tryBkt) -
                (extractFastMeta fl s1.mem).tryPos) ≤ 20 * slabScale fl.N ^ 12 := by
            rw [hfm', hbp']
            simp only [Bool.false_eq_true, false_and, ↓reduceIte] at hbd
            split_ifs <;> omega
          refine ⟨by rw [hfm']; exact hsub, by rw [htb_eq]; exact hb_t,
            by rw [hts_eq]; exact hs_t, by rw [hbp', htp_eq, htb_eq]; exact htp,
            by rw [hfm']; exact hsc, hbd', tm, ?_, ?_, ?_⟩
          · rw [htb_eq, hti_eq, hcr_eq, hbt' _ hb_t _ htr_lt]; exact hvt
          · intro fp' loc' hm
            obtain ⟨hlt, _, u', hk', hmb, hf'⟩ := htm1 fp' loc' hm
            have hlb := lt_of_lt_of_le hlt htp
            refine ⟨by rw [htp_eq]; exact hlt, ?_, u',
              by rw [htb_eq]; exact (hke _ loc' hb_t hlb).trans hk',
              (mapBTree_fpHash_congr mapBTree htb_eq (by rw [htb_eq, hbs_eq]) u').trans hmb,
              (congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts_eq u')).trans hf'⟩
            rintro ⟨hbt_eq, hle⟩
            have hbt0 : fm.tryBkt = b := htb_eq.symm.trans hbt_eq
            have hmb' : mapBTree b (fpHash fl.c fl.U fl.N seeds.fp
                ⟨fm.bktSalt b, (ht.bkt_meta_bounds b hb).1⟩ u').val = some lastLoc := by
              rw [← hle]
              exact (mapBTree_fpHash_congr mapBTree hbt0 (congrArg fm.bktSalt hbt0) u').symm.trans
                hmb
            obtain ⟨_, _, u'', _, hk'', hd1, _⟩ := ht.bt_sound b hb _ lastLoc hmb'
            have hu'' : u'' = uLast := Fin.ext (hk''.symm.trans hkey_last)
            exact hd1 b lastLoc (by rw [hu'']; exact hcur_hit) (by rw [hu'']; exact hkey_last)
          · intro loc' hlt _ u' hk' hmb
            have hlt' : loc' < fm.tryPos := by rwa [htp_eq] at hlt
            have hlb := lt_of_lt_of_le hlt' htp
            have hmb0 : mapBTree fm.tryBkt (fpHash fl.c fl.U fl.N seeds.fp
                ⟨fm.bktSalt fm.tryBkt, (ht.bkt_meta_bounds _ hb_t).1⟩ u').val = some loc' :=
              (mapBTree_fpHash_congr mapBTree htb_eq (by rw [htb_eq, hbs_eq]) u').symm.trans hmb
            have hne_del : ¬(fm.tryBkt = b ∧ loc' = delLoc) := fun ⟨hbe, hle⟩ => by
              have hmb_d : mapBTree fm.tryBkt (fpHash fl.c fl.U fl.N seeds.fp
                  ⟨fm.bktSalt fm.tryBkt, (ht.bkt_meta_bounds _ hb_t).1⟩ u').val = some loc' := hmb0
              obtain ⟨_, hne_d, _⟩ := ht.bt_sound fm.tryBkt hb_t _ loc' hmb_d
              exact hne_d ⟨hbe, hle⟩
            rw [congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts_eq u')]
            exact htm2 loc' hlt' hne_del u'
              ((hke _ loc' hb_t hlb).symm.trans (htb_eq ▸ hk')) hmb0 }
  · have hcur_ne_step : ¬(((Memory.spec 0).clientResult s
        (fastBufLookupProg ((fl.pBase, fm.curBufRole), rk))).1 = 1 ∧
        ((Memory.spec 0).clientResult s
          (fastBufLookupProg ((fl.pBase, fm.curBufRole), rk))).2.1 = b ∧
        ((Memory.spec 0).clientResult s
          (fastBufLookupProg ((fl.pBase, fm.curBufRole), rk))).2.2 = lastLoc) := by
      rw [hcur_spec.1]
      cases hc : mapCur rk with
      | none => exact fun h => absurd h.1 (by decide)
      | some p => exact fun h =>
          hcur_hit (hc.trans (congrArg some (Prod.ext h.2.1 h.2.2)))
    rw [ite_eq_right hcur_ne_step]
    have hr4_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 4)) = fm.subStep :=
      clientResult_fastReadMetaProg hpt (by decide)
    have hc4 := memoryCost_fastReadMetaProg (fl.pBase, 4) s
    have hr23_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 23)) = Q :=
      hpt 23 (by decide)
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadMetaProg, hr4_r,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 23)) = s from rfl,
      hr23_r, prog_memoryCost_read]
    by_cases hsub : fm.subStep < Q / 2
    · rw [ite_eq_left hsub, pure_bind]
      obtain ⟨hv_o, hrb_o, hrc_o, hia_o, hna_o, hdp_o, hclr_o, hold_snd⟩ := ht.old_valid_half hsub
      have hold_spec := fastBufLookupProg_spec hr hold_lt hv_o hrk_lt
      rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        clientState_fastBufLookupProg]
      by_cases ho_hit : mapOld rk = some (b, lastLoc)
      · rw [hold_spec.1, ho_hit]; dsimp only; rw [ite_eq_left ⟨rfl, rfl, rfl⟩]
        have hna_old_le : (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem).nodeAlloc +
            cTabWhp fl.c ≤ maxTrieNodesWhp fl.c fl.N :=
          (Nat.add_le_add_right hna_o _).trans hmax_t
        obtain ⟨hfr, hr', hci, hext, hv_o', hbp', hfm', hm2', hm0', hbt', htr_c, hoi, hof⟩ :=
          fastBufInsertProg_update_spec hr hold_lt hv_o hrb_o hna_old_le hia_o
            (by rw [ho_hit]; exact Option.some_ne_none _) hrk_lt hb_ptr hdl_ptr
        generalize hs1_def : (Memory.spec 0).clientState s
          (fastBufInsertProg ((fl.pBase, 1 - fm.curBufRole), (rk, (b, delLoc)))) = s1
        rw [hs1_def] at hfr hr' hext hv_o' hbp' hfm' hm2' hm0' hbt' htr_c hoi hof
        have hcc_role : 1 - (1 - fm.curBufRole) = fm.curBufRole := by omega
        rw [hcc_role] at htr_c
        obtain ⟨hna_eq, hia_eq, hrb_f, hrc_f, hnone_f, id₀, hid₀⟩ :=
          bufInsert_active_props hv_o hrk_lt ho_hit (b := b) (loc := delLoc)
        have hke : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
            fastKeyAt fl seeds.bkt s1.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
          fun b' loc' hb' hl' => fastKeyAt_eq_of_fixed_pool hv hbp_inv hbp' hoi hb' hl'
        have hcl_c : memoryCost (fastBufLookupProg ((fl.pBase, fm.curBufRole),
            rKeyOf fl.c fl.U fl.N seeds.fp uLast)) s ≤ 2 * cTabWhp fl.c + 18 := hcur_spec.2
        have hcl_o : memoryCost (fastBufLookupProg ((fl.pBase, 1 - fm.curBufRole),
            rKeyOf fl.c fl.U fl.N seeds.fp uLast)) s ≤ 2 * cTabWhp fl.c + 18 := hold_spec.2
        have hci_c : memoryCost (fastBufInsertProg ((fl.pBase, 1 - fm.curBufRole),
            (rKeyOf fl.c fl.U fl.N seeds.fp uLast, (b, delLoc)))) s ≤
            24 * cTabWhp fl.c + 42 := hci
        have hfm_sh : (extractFastMeta fl s1.mem).shadowIns b = fm.shadowIns b :=
          congrFun (congrArg FastEpochMeta.shadowIns hfm') b
        have hchk_rel : ∀ id b' loc',
            bufCheckSlot (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s1.mem) id =
              some (b', loc') →
            bufCheckSlot (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem) id =
              some (b', loc') ∨
            (b' = b ∧ loc' = delLoc ∧
              bufCheckSlot (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem) id =
                some (b, lastLoc)) := by
          intro id b' l' hchk
          rw [hext] at hchk
          by_cases he : id = id₀
          · subst he; exact Or.inr ((hid₀ id).2 b' l' hchk)
          · exact Or.inl ((hid₀ id).1 he ▸ hchk)
        refine ⟨hfr, hr', by omega, hbp', hm0', hm2', hoi, hof,
          by rw [hext, hia_eq], hchk_rel,
          by rw [hfm'], by rw [hfm'], by rw [hfm'], by rw [hfm'], by rw [hfm'],
          by rw [hfm'], by rw [hfm'], by rw [hfm'], by rw [hfm'],
          fun b' _ => congrFun (congrArg FastEpochMeta.shadowIns hfm') b',
          by rw [hfm_sh]; exact Nat.le_succ _,
          fun _ => hfm_sh, Or.inl ⟨by rw [hfm'], by rw [hfm']⟩,
          mapCur, Function.update mapOld rk (some (b, delLoc)), mapBTree, ?_⟩
        exact
          { role_lt := by rw [hfm']; exact hrole_lt
            subStep_lt := by rw [hfm']; exact ht.subStep_lt
            bkt_meta_bounds := fun b' hb' => by rw [hfm']; exact ht.bkt_meta_bounds b' hb'
            cur_valid := by rw [hfm', htr_c]; exact ht.cur_valid
            cur_raw := by rw [hfm', htr_c]; exact ht.cur_raw
            cur_clr := by rw [hfm', htr_c]; exact ht.cur_clr
            cur_ia := by rw [hfm', htr_c]; exact ht.cur_ia
            cur_na := by rw [hfm', htr_c]; exact ht.cur_na
            cur_sound := fun rk' b' loc' hm => by
              obtain ⟨hb', hl', _, u', hrk', hk'⟩ := ht.cur_sound rk' b' loc' hm
              refine ⟨hb', by rw [hbp']; exact hl', ?_, u', hrk', (hke b' loc' hb' hl').trans hk'⟩
              rintro ⟨hbe, hle⟩
              have hku : fastKeyAt fl seeds.bkt s.mem b lastLoc = u'.val := by
                rwa [hbe, hle] at hk'
              have hu' : u' = uLast := Fin.ext (hku.symm.trans hkey_last)
              have hcn := (hold_snd rk b lastLoc ho_hit).1
              rw [← hrk', hu'] at hm; rw [hm] at hcn; cases hcn
            old_valid_half := fun _ => by
              rw [hfm', hbp']
              refine ⟨hv_o', hext ▸ hrb_f hrb_o, hext ▸ hrc_f hrc_o,
                by rw [hext, hia_eq]; exact hia_o, by rw [hext, hna_eq]; exact hna_o, hdp_o,
                fun id hid => by
                  rw [hext, hia_eq] at hid; rw [hext]; exact hnone_f id (hclr_o id hid),
                fun rk' b' loc' hm => by
                  by_cases hrke : rk' = rk
                  · rw [hrke, Function.update_self] at hm
                    have hp := Option.some.inj hm
                    have hbe : b' = b := (congrArg Prod.fst hp).symm
                    have hle : loc' = delLoc := (congrArg Prod.snd hp).symm
                    have hdl_lt : delLoc < bp.bktCount b := lt_trans hdel_lt hlast_lt
                    rw [hrke, hbe, hle]
                    exact ⟨(hold_snd rk b lastLoc ho_hit).1, hb, hdl_lt, fun h => by omega,
                      uLast, rfl, (hke b delLoc hb hdl_lt).trans hkey_del⟩
                  · rw [Function.update_of_ne hrke] at hm
                    obtain ⟨hcn, hb', hl', _, u', hrk', hk'⟩ := hold_snd rk' b' loc' hm
                    refine ⟨hcn, hb', hl', ?_, u', hrk', (hke b' loc' hb' hl').trans hk'⟩
                    rintro ⟨hbe, hle⟩
                    have hku : fastKeyAt fl seeds.bkt s.mem b lastLoc = u'.val := by
                      rwa [hbe, hle] at hk'
                    have hu' : u' = uLast := Fin.ext (hku.symm.trans hkey_last)
                    exact hrke (hrk'.symm.trans (by rw [hu']))⟩
            old_clear_half := fun hn => absurd (by rw [hfm']; exact hsub) hn
            bt_valid := fun b' hb' => by
              rw [hfm', hbt' b' hb' _ (ht.bkt_meta_bounds b' hb').2.1]; exact ht.bt_valid b' hb'
            bt_sound := fun b' hb' fp' loc' hm => by
              obtain ⟨hl', _, u', hfp', hk', hd1, hd2⟩ := ht.bt_sound b' hb' fp' loc' hm
              have hbs := congrArg (fun m => m.bktSalt b') hfm'
              refine ⟨by rw [hbp']; exact hl', ?_, u',
                (congrArg Fin.val (fpHash_congr_salt (h₂ := (ht.bkt_meta_bounds b' hb').1) hbs
                  u')).trans hfp',
                (hke b' loc' hb' hl').trans hk', fun b₁ l₁ hm₁ => ?_, fun b₂ l₂ hm₂ => ?_⟩
              · rintro ⟨hbe, hle⟩
                have hku : fastKeyAt fl seeds.bkt s.mem b lastLoc = u'.val := by
                  rwa [hbe, hle] at hk'
                have hu' : u' = uLast := Fin.ext (hku.symm.trans hkey_last)
                exact hd2 b lastLoc (by rw [hu']; exact ho_hit) (by rw [hu']; exact hkey_last)
              · obtain ⟨hb₁, hl₁, _⟩ := ht.cur_sound _ b₁ l₁ hm₁
                rw [hke b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁
              · by_cases he : rKeyOf fl.c fl.U fl.N seeds.fp u' = rk
                · rw [he, Function.update_self] at hm₂
                  have hp := Option.some.inj hm₂
                  have hbe : b₂ = b := (congrArg Prod.fst hp).symm
                  have hle : l₂ = delLoc := (congrArg Prod.snd hp).symm
                  rw [hbe, hle]
                  have hdl_lt : delLoc < bp.bktCount b := by omega
                  rw [hke b delLoc hb hdl_lt, hkey_del]
                  have := hd2 b lastLoc (by rw [he]; exact ho_hit)
                  rwa [hkey_last] at this
                · rw [Function.update_of_ne he] at hm₂
                  obtain ⟨_, hb₂, hl₂, _⟩ := hold_snd _ b₂ l₂ hm₂
                  rw [hke b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂
            complete := fun b' hb' loc' hl' hne => by
              rw [hbp'] at hl'
              by_cases hd : b' = b ∧ loc' = delLoc
              · obtain ⟨rfl, rfl⟩ := hd
                exact ⟨uLast, (hke b' loc' hb' hl').trans hkey_del,
                  Or.inr (Or.inl (Function.update_self _ _ _))⟩
              · obtain ⟨u', hk', htier⟩ := ht.complete b' hb' loc' hl' hd
                refine ⟨u', (hke b' loc' hb' hl').trans hk', ?_⟩
                rcases htier with h1 | h2 | h3
                · exact Or.inl h1
                · by_cases he : rKeyOf fl.c fl.U fl.N seeds.fp u' = rk
                  · rw [he, ho_hit] at h2; cases h2; exact absurd ⟨rfl, rfl⟩ hne
                  · exact Or.inr (Or.inl (by rw [Function.update_of_ne he]; exact h2))
                · have hbs := congrArg (fun m => m.bktSalt b') hfm'
                  exact Or.inr (Or.inr ((mapBTree_fpHash_congr mapBTree rfl hbs u').trans h3))
            shadow := fun b' hb' hsc => by
              have hsc0 : fm.shadowCode b' ≠ 0 := by rwa [hfm'] at hsc
              obtain ⟨h1, h2, h3, h4, sm, hvs, heq⟩ := ht.shadow b' hb' hsc0
              rw [hfm', hbp']
              have hsr := (shadowRoleOf_lt_and_ne (ht.bkt_meta_bounds b' hb').2.1).1
              have h3' : 4 * fm.shadowIns b' + 5 * ((if true = true ∧ b' = b then bp.bktCount b' - 1
                  else bp.bktCount b') - (fm.shadowCode b' - 1)) ≤ 20 * slabScale fl.N ^ 12 := by
                have h3b : 4 * fm.shadowIns b' +
                    5 * (bp.bktCount b' - (fm.shadowCode b' - 1)) ≤ 20 * slabScale fl.N ^ 12 := by
                  simpa using h3
                split_ifs <;> omega
              have h4' : 8 * (fm.curIns b' - 6 * slabScale fl.N ^ 12) +
                  ((if true = true ∧ b' = b then bp.bktCount b' - 1 else bp.bktCount b') -
                    (fm.shadowCode b' - 1)) ≤ 4 * slabScale fl.N ^ 12 := by
                have h4b : 8 * (fm.curIns b' - 6 * slabScale fl.N ^ 12) +
                    (bp.bktCount b' - (fm.shadowCode b' - 1)) ≤ 4 * slabScale fl.N ^ 12 := by
                  simpa using h4
                split_ifs <;> omega
              exact ⟨h1, h2, h3', h4', sm, by rw [hbt' b' hb' _ hsr]; exact hvs, heq⟩
            tryAct_le := by rw [hfm']; exact ht.tryAct_le
            try_ok := fun hta1 => by
              have hta0 : fm.tryAct = 1 := by rwa [hfm'] at hta1
              obtain ⟨hsub', hb_t, hs_t, htp, hsc, hbd, tm, hvt, htm1, htm2⟩ := ht.try_ok hta0
              have htb_eq := congrArg FastEpochMeta.tryBkt hfm'
              have hts_eq := congrArg FastEpochMeta.trySalt hfm'
              have htp_eq := congrArg FastEpochMeta.tryPos hfm'
              have hti_eq := congrArg FastEpochMeta.tryIns hfm'
              have hcr_eq := congrArg (fun m => m.curRole fm.tryBkt) hfm'
              have hbs_eq := congrArg (fun m => m.bktSalt fm.tryBkt) hfm'
              have htr_lt := (tryRoleOf_lt_and_ne (ht.bkt_meta_bounds _ hb_t).2.1).1
              have hbd' : 4 * (extractFastMeta fl s1.mem).tryIns +
                  5 * ((if true = true ∧ (extractFastMeta fl s1.mem).tryBkt = b then
                    (extractBlockPool fl.mp s1.mem).bktCount (extractFastMeta fl s1.mem).tryBkt - 1
                    else (extractBlockPool fl.mp s1.mem).bktCount
                      (extractFastMeta fl s1.mem).tryBkt) -
                    (extractFastMeta fl s1.mem).tryPos) ≤ 20 * slabScale fl.N ^ 12 := by
                rw [hfm', hbp']
                simp only [Bool.false_eq_true, false_and, ↓reduceIte] at hbd
                split_ifs <;> omega
              refine ⟨by rw [hfm']; exact hsub', by rw [htb_eq]; exact hb_t,
                by rw [hts_eq]; exact hs_t, by rw [hbp', htp_eq, htb_eq]; exact htp,
                by rw [hfm']; exact hsc, hbd', tm, ?_, ?_, ?_⟩
              · rw [htb_eq, hti_eq, hcr_eq, hbt' _ hb_t _ htr_lt]; exact hvt
              · intro fp' loc' hm
                obtain ⟨hlt, _, u', hk', hmb, hf'⟩ := htm1 fp' loc' hm
                have hlb := lt_of_lt_of_le hlt htp
                refine ⟨by rw [htp_eq]; exact hlt, ?_, u',
                  by rw [htb_eq]; exact (hke _ loc' hb_t hlb).trans hk',
                  (mapBTree_fpHash_congr mapBTree htb_eq (by rw [htb_eq, hbs_eq]) u').trans hmb,
                  (congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts_eq u')).trans hf'⟩
                rintro ⟨hbt_eq, hle⟩
                have hbt0 : fm.tryBkt = b := htb_eq.symm.trans hbt_eq
                have hmb' : mapBTree b (fpHash fl.c fl.U fl.N seeds.fp
                    ⟨fm.bktSalt b, (ht.bkt_meta_bounds b hb).1⟩ u').val = some lastLoc := by
                  rw [← hle]
                  exact (mapBTree_fpHash_congr mapBTree hbt0
                    (congrArg fm.bktSalt hbt0) u').symm.trans hmb
                obtain ⟨_, _, u'', _, hk'', _, hd2⟩ := ht.bt_sound b hb _ lastLoc hmb'
                have hu'' : u'' = uLast := Fin.ext (hk''.symm.trans hkey_last)
                exact hd2 b lastLoc (by rw [hu'']; exact ho_hit) (by rw [hu'']; exact hkey_last)
              · intro loc' hlt _ u' hk' hmb
                have hlt' : loc' < fm.tryPos := by rwa [htp_eq] at hlt
                have hlb := lt_of_lt_of_le hlt' htp
                have hmb0 : mapBTree fm.tryBkt (fpHash fl.c fl.U fl.N seeds.fp
                    ⟨fm.bktSalt fm.tryBkt, (ht.bkt_meta_bounds _ hb_t).1⟩ u').val = some loc' :=
                  (mapBTree_fpHash_congr mapBTree htb_eq (by rw [htb_eq, hbs_eq]) u').symm.trans
                    hmb
                have hne_del : ¬(fm.tryBkt = b ∧ loc' = delLoc) := fun ⟨hbe, hle⟩ => by
                  obtain ⟨_, hne_d, _⟩ := ht.bt_sound fm.tryBkt hb_t _ loc' hmb0
                  exact hne_d ⟨hbe, hle⟩
                rw [congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts_eq u')]
                exact htm2 loc' hlt' hne_del u'
                  ((hke _ loc' hb_t hlb).symm.trans (htb_eq ▸ hk')) hmb0 }
      · have hold_ne_step : ¬(((Memory.spec 0).clientResult s
            (fastBufLookupProg ((fl.pBase, 1 - fm.curBufRole), rk))).1 = 1 ∧
            ((Memory.spec 0).clientResult s
              (fastBufLookupProg ((fl.pBase, 1 - fm.curBufRole), rk))).2.1 = b ∧
            ((Memory.spec 0).clientResult s
              (fastBufLookupProg ((fl.pBase, 1 - fm.curBufRole), rk))).2.2 = lastLoc) := by
          rw [hold_spec.1]
          cases ho : mapOld rk with
          | none => exact fun h => absurd h.1 (by decide)
          | some p => intro h; exact ho_hit (ho.trans (congrArg some (Prod.ext h.2.1 h.2.2)))
        rw [ite_eq_right hold_ne_step]
        obtain ⟨hfr, hr', hc_bt, hbp', hm0', hm2', htr', hoi, hof, h1, h2, h3, h4, h5, h6,
          h7, h8, h9, h10, h11, h12, htd, hth⟩ := fastRelocBTreeProg_spec uLast hr hbp_inv hfp_rep
            hb hcnt_le hlast_eq hdel_lt hkey_del hkey_last ht hcur_hit ho_hit hkey_ne_other
        have hcl_c : memoryCost (fastBufLookupProg ((fl.pBase, fm.curBufRole),
            rKeyOf fl.c fl.U fl.N seeds.fp uLast)) s ≤ 2 * cTabWhp fl.c + 18 := hcur_spec.2
        have hcl_o : memoryCost (fastBufLookupProg ((fl.pBase, 1 - fm.curBufRole),
            rKeyOf fl.c fl.U fl.N seeds.fp uLast)) s ≤ 2 * cTabWhp fl.c + 18 := hold_spec.2
        have hto := htr' (1 - fm.curBufRole) hold_lt
        exact ⟨hfr, hr', by omega, hbp', hm0', hm2', hoi, hof, by rw [hto],
          fun id b' l' h => Or.inl (by rwa [hto] at h),
          h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, htd, hth⟩
    · rw [ite_eq_right hsub]
      have ho_hit : mapOld rk ≠ some (b, lastLoc) := by
        rw [(ht.old_clear_half hsub).1]; exact fun h => by cases h
      obtain ⟨hfr, hr', hc_bt, hbp', hm0', hm2', htr', hoi, hof, h1, h2, h3, h4, h5, h6,
        h7, h8, h9, h10, h11, h12, htd, hth⟩ := fastRelocBTreeProg_spec uLast hr hbp_inv hfp_rep
          hb hcnt_le hlast_eq hdel_lt hkey_del hkey_last ht hcur_hit ho_hit hkey_ne_other
      have hcl_c : memoryCost (fastBufLookupProg ((fl.pBase, fm.curBufRole),
          rKeyOf fl.c fl.U fl.N seeds.fp uLast)) s ≤ 2 * cTabWhp fl.c + 18 := hcur_spec.2
      have hto := htr' (1 - fm.curBufRole) hold_lt
      exact ⟨hfr, hr', by omega, hbp', hm0', hm2', hoi, hof, by rw [hto],
        fun id b' l' h => Or.inl (by rwa [hto] at h),
        h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, htd, hth⟩

private theorem fastSwapLastDownProg_spec {slackCur : ℕ} {fl : FastEpochLayout}
    {w b delLoc lastLoc : ℕ} {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s : Memory.State}
    (hslack : slackCur ≤ 1)
    (hr : FastLayoutReady w fl s)
    (hbp_inv : fl.bpL.StateInv 0 s.mem)
    (hbkt_rep : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt s.mem)
    (hfp_rep : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp s.mem)
    (hb : b < numBucketsWhp fl.N)
    (hcnt_le : (extractBlockPool fl.mp s.mem).bktCount b ≤ capMaxWhp fl.N)
    (hlast_eq : (extractBlockPool fl.mp s.mem).bktCount b = lastLoc + 1)
    (hdel_le : delLoc ≤ lastLoc)
    (hlast_ref : ∃ (uLast : Fin fl.U) (vLast : Fin fl.V),
      uLast.val = fastKeyAt fl seeds.bkt s.mem b lastLoc ∧
      vLast.val = (bpPairAt fl.bpL s.mem b lastLoc).2 ∧
      keyQuotient (bWhp fl.N) uLast.val = (bpPairAt fl.bpL s.mem b lastLoc).1 ∧
      ∀ loc' < lastLoc, loc' ≠ delLoc → fastKeyAt fl seeds.bkt s.mem b loc' ≠ uLast.val)
    (ht : TierInvHole slackCur fl seeds s.mem b delLoc false) :
    let fm := extractFastMeta fl s.mem
    let bp := extractBlockPool fl.mp s.mem
    let oldRole := 1 - fm.curBufRole
    let oldTr := extractBufTrie (fl.trieL oldRole) s.mem
    let s' := (Memory.spec 0).clientState s
      (fastSwapLastDownProg ((fl.pBase, b), (delLoc, lastLoc)))
    let fm' := extractFastMeta fl s'.mem
    let oldTr' := extractBufTrie (fl.trieL oldRole) s'.mem
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastSwapLastDownProg ((fl.pBase, b), (delLoc, lastLoc))) s ≤
      30 * cTabWhp fl.c + 6 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 156 * hMaxBTree + 740 ∧
    extractBlockPool fl.mp s'.mem = bp ∧
    fl.bpL.StateInv 0 s'.mem ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ loc' < bp.bktCount b',
      bpPairAt fl.bpL s'.mem b' loc' =
        if b' = b ∧ loc' = delLoc ∧ delLoc < lastLoc then
          bpPairAt fl.bpL s.mem b lastLoc
        else bpPairAt fl.bpL s.mem b' loc') ∧
    (fl.io.usePaged ≠ 0 →
      extractPageUnperm fl.io.pgL s'.mem = extractPageUnperm fl.io.pgL s.mem ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) ∧
    oldTr'.itemAlloc = oldTr.itemAlloc ∧
    (∀ id b' loc', bufCheckSlot oldTr' id = some (b', loc') →
      bufCheckSlot oldTr id = some (b', loc') ∨
      (b' = b ∧ loc' = delLoc ∧ delLoc < lastLoc ∧
        bufCheckSlot oldTr id = some (b, lastLoc))) ∧
    fm'.curBufRole = fm.curBufRole ∧
    fm'.subStep = fm.subStep ∧
    fm'.drainPos = fm.drainPos ∧
    fm'.tryAct = fm.tryAct ∧
    fm'.tryBkt = fm.tryBkt ∧
    fm'.bktSalt = fm.bktSalt ∧
    fm'.curRole = fm.curRole ∧
    fm'.curIns = fm.curIns ∧
    fm'.shadowCode = fm.shadowCode ∧
    (∀ b' ≠ b, fm'.shadowIns b' = fm.shadowIns b') ∧
    fm'.shadowIns b ≤ fm.shadowIns b + 1 ∧
    (fm'.shadowCode b = 0 ∨ ¬(delLoc < fm.shadowCode b - 1) → fm'.shadowIns b = fm.shadowIns b) ∧
    ((fm'.trySalt = fm.trySalt ∧ fm'.tryPos = fm.tryPos) ∨
      (fm.tryAct = 1 ∧ fm.tryBkt = b ∧ delLoc < fm.tryPos ∧ fm.tryPos ≤ lastLoc ∧
        fm'.trySalt = (if fm.trySalt + 1 < sMaxWhp fl.c fl.N then fm.trySalt + 1 else 0) ∧
        fm'.tryPos = 0 ∧ fm'.tryIns = 0 ∧
        ∃ (hs_t : fm.trySalt < sMaxWhp fl.c fl.N) (wLoc : ℕ) (wKey uLast : Fin fl.U),
          wLoc < lastLoc ∧ wLoc ≠ delLoc ∧ wKey ≠ uLast ∧
          fastKeyAt fl seeds.bkt s.mem b wLoc = wKey.val ∧
          fastKeyAt fl seeds.bkt s.mem b lastLoc = uLast.val ∧
          fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ wKey =
            fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ uLast)) ∧
    TierInvHole slackCur fl seeds s'.mem b lastLoc true := by
  dsimp only
  have hv := hr.1
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  unfold fastSwapLastDownProg; dsimp only
  by_cases hlt : delLoc < lastLoc
  · rw [ite_eq_left hlt]
    have hlast_lt : lastLoc < bp.bktCount b := by omega
    have hdel_lt_cnt : delLoc < bp.bktCount b := lt_trans hlt hlast_lt
    obtain ⟨uLast, vLast, huL, hvL, hqL, hne_o⟩ := hlast_ref
    obtain ⟨_, hread_r, hread_c⟩ := fastBpReadAtProg_spec hr hbp_inv hb hlast_lt
    have hq_lt_q : (bpPairAt fl.bpL s.mem b lastLoc).1 < 2 ^ quotBitsWhp fl.U fl.N :=
      hqL ▸ keyQuotient_bWhp_lt hv.N_le_U uLast
    have hq_lt_pg : (bpPairAt fl.bpL s.mem b lastLoc).1 < 2 ^ fl.io.pgL.qBits :=
      hq_lt_q.trans_le (Nat.pow_le_pow_right Nat.one_lt_two.le hv.qBits_le)
    have hv_lt_pg : (bpPairAt fl.bpL s.mem b lastLoc).2 < 2 ^ fl.io.pgL.vBits := by
      rw [← hvL, hv.vBits_eq]
      exact vLast.isLt.trans_le (Nat.le_pow_clog (by decide) fl.V)
    obtain ⟨hrec_r, hrec_c⟩ := fastFeistelReconProg_spec hr hq_lt_q hbkt_rep (bkt := b)
    have hrec_val : (Memory.spec 0).clientResult s
        (fastFeistelReconProg (fl.pBase, (b, (bpPairAt fl.bpL s.mem b lastLoc).1))) =
        uLast.val := by
      rw [hrec_r]; exact huL.symm
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastBpReadAtProg, hread_r,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastFeistelReconProg, hrec_val,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
    obtain ⟨hfr1, hr1, hc_w, hbp1, hbp_inv1, hfm1, hm0_1, hm2_1, hbt1, htr1, hof1, hpair1,
      hpart1⟩ := fastBpWriteAtProg_spec hr hbp_inv hb hdel_lt_cnt hq_lt_pg hv_lt_pg
    generalize hs1_def : (Memory.spec 0).clientState s
      (fastBpWriteAtProg ((fl.pBase, (b, delLoc)), bpPairAt fl.bpL s.mem b lastLoc)) = s1
    rw [hs1_def] at hfr1 hr1 hbp1 hbp_inv1 hfm1 hm0_1 hm2_1 hbt1 htr1 hof1 hpair1 hpart1
    have hfp_rep1 : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
        (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp s1.mem :=
      hfp_rep.congr_on (hv.w_eq ▸ hv.w_pos) fun a h1 h2 =>
        hof1 a (hv.not_ownsFast_seeds
          (by unfold FastEpochLayout.fpHashBase at h1; unfold offFpHash at h1
              have : offBktHash ≤ offFpHash fl.c fl.w fl.U := by
                unfold offFpHash; exact Nat.le_add_right _ _
              omega)
          (by unfold FastEpochLayout.fpHashBase at h2; unfold offBktMeta; omega))
    have hkey_del1 : fastKeyAt fl seeds.bkt s1.mem b delLoc = uLast.val := by
      unfold fastKeyAt
      rw [hpair1 b hb delLoc hdel_lt_cnt, ite_eq_left ⟨rfl, rfl⟩]; exact huL.symm
    have hkey_last1 : fastKeyAt fl seeds.bkt s1.mem b lastLoc = uLast.val := by
      unfold fastKeyAt
      rw [hpair1 b hb lastLoc hlast_lt, ite_eq_right (fun h => by omega)]; exact huL.symm
    have hne_o1 : ∀ loc' < lastLoc, loc' ≠ delLoc →
        fastKeyAt fl seeds.bkt s1.mem b loc' ≠ uLast.val := fun loc' hl' hne => by
      have hloc_c : loc' < bp.bktCount b := lt_trans hl' hlast_lt
      unfold fastKeyAt
      rw [hpair1 b hb loc' hloc_c, ite_eq_right (fun h => hne h.2)]
      exact hne_o loc' hl' hne
    rcases ht with ⟨mc, mo, mb, ht⟩
    have ht1 : TierInvHole slackCur fl seeds s1.mem b delLoc false :=
      ⟨mc, mo, mb, tierInvHole_of_bpWriteAt hv hbp_inv hbp1 hfm1 hbt1 htr1 hpair1 ht⟩
    obtain ⟨hfr2, hr2, hc_rl, hbp2, hm0_2, hm2_2, hoi2, hof2, hia2, hchk2,
      h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, htd, hth⟩ :=
      fastRelocLastProg_spec uLast hslack hr1 hbp_inv1 hfp_rep1 hb
        (by rw [hbp1]; exact hcnt_le) (by rw [hbp1]; exact hlast_eq) hlt
        hkey_del1 hkey_last1 ht1 hne_o1
    generalize hs2_def : (Memory.spec 0).clientState s1
      (fastRelocLastProg ((fl.pBase, (b, delLoc)), (lastLoc, uLast.val))) = s2
    rw [hs2_def] at hfr2 hr2 hbp2 hm0_2 hm2_2 hoi2 hof2 hia2 hchk2
    rw [hs2_def] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 htd hth
    have hbp_tot : extractBlockPool fl.mp s2.mem = bp := hbp2.trans hbp1
    have hbp_inv2 : fl.bpL.StateInv 0 s2.mem :=
      bpStateInv_congr_io (hfr1.symm ▸ hv) hbp_inv1 hbp2 hoi2
    have hpair_tot : ∀ b' < numBucketsWhp fl.N, ∀ loc' < bp.bktCount b',
        bpPairAt fl.bpL s2.mem b' loc' =
          if b' = b ∧ loc' = delLoc ∧ delLoc < lastLoc then
            bpPairAt fl.bpL s.mem b lastLoc
          else bpPairAt fl.bpL s.mem b' loc' := by
      intro b' hb' loc' hl'
      have heq_p := bpPairAt_eq_of_fixed_pool (hfr1.symm ▸ hv) hbp_inv1 hbp2 hoi2 hb'
        (by rw [hbp1]; exact hl')
      rw [heq_p, hpair1 b' hb' loc' hl']
      by_cases hc : b' = b ∧ loc' = delLoc
      · simp [hc.1, hc.2, hlt]
      · rw [ite_eq_right hc, ite_eq_right (fun h : b' = b ∧ loc' = delLoc ∧ delLoc < lastLoc =>
          hc ⟨h.1, h.2.1⟩)]
    have hof_tot : ∀ a, ¬fl.OwnsFastAddr a → s2.mem a = s.mem a :=
      fun a ha => (hof2 a ha).trans (hof1 a ha)
    have hpart_tot : fl.io.usePaged ≠ 0 →
        extractPageUnperm fl.io.pgL s2.mem = extractPageUnperm fl.io.pgL s.mem ∧
        ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
          slotIoPairAt fl.io.partner s2.mem idx = slotIoPairAt fl.io.partner s.mem idx := by
      intro hup
      have hp1 := hpart1 hup
      have hp2 := pagePair_partner_eq_of_io (hfr1.symm ▸ hv) hup hbp_inv1 hoi2
      refine ⟨hp2.1.trans hp1.1, fun idx hidx => ?_⟩
      have hvl1 : (extractPagePair fl.io.pgL s1.mem).virtLen fl.io.partner.side =
          (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side :=
        congrArg (fun u => u.st.virtLen fl.io.partner.side) hp1.1
      exact (hp2.2.2 idx (hvl1.symm ▸ hidx)).trans (hp1.2 idx hidx)
    have hrole_lt : fm.curBufRole < 2 := ht.role_lt
    have hold_lt : 1 - fm.curBufRole < 2 := by omega
    have htr_o1 : extractBufTrie (fl.trieL (1 - fm.curBufRole)) s1.mem =
        extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem := htr1 _ hold_lt
    have hcr1 : (extractFastMeta fl s1.mem).curBufRole = fm.curBufRole :=
      congrArg FastEpochMeta.curBufRole hfm1
    have hcost_eq : memoryCost (fastBpReadAtProg (fl.pBase, (b, lastLoc))) s +
        memoryCost (fastFeistelReconProg
          (fl.pBase, (b, (bpPairAt fl.bpL s.mem b lastLoc).1))) s +
        memoryCost (fastBpWriteAtProg ((fl.pBase, (b, delLoc)),
          bpPairAt fl.bpL s.mem b lastLoc)) s +
        memoryCost (fastRelocLastProg ((fl.pBase, (b, delLoc)), (lastLoc, uLast.val))) s1 ≤
        30 * cTabWhp fl.c + 6 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 156 * hMaxBTree + 740 := by
      have hmul : 2 * dTabWhp fl.c * (cTabWhp fl.c + 2) +
          4 * dTabWhp fl.c * (cTabWhp fl.c + 2) =
          6 * dTabWhp fl.c * (cTabWhp fl.c + 2) := by ring
      linarith only [hread_c, hrec_c, hc_w, hc_rl, hmul]
    refine ⟨hfr2.trans hfr1, hr2, ?_, hbp_tot, hbp_inv2,
      hm0_2.trans hm0_1, hm2_2.trans hm2_1, hof_tot, hpair_tot, hpart_tot,
      by rw [hcr1, htr_o1] at hia2; exact hia2,
      fun id b' l' hchk => by
        rcases hchk2 id b' l' (by rwa [hcr1]) with h | ⟨hbe, hle, h0⟩
        · exact Or.inl (by rwa [hcr1, htr_o1] at h)
        · exact Or.inr ⟨hbe, hle, hlt, by rwa [hcr1, htr_o1] at h0⟩,
      by rw [h1, hfm1], by rw [h2, hfm1], by rw [h3, hfm1], by rw [h4, hfm1], by rw [h5, hfm1],
      by rw [h6, hfm1], by rw [h7, hfm1], by rw [h8, hfm1], by rw [h9, hfm1],
      fun b' hne => (h10 b' hne).trans (congrFun (congrArg FastEpochMeta.shadowIns hfm1) b'),
      by rw [hfm1] at h11; exact h11,
      fun h => by rw [hfm1] at h12; exact h12 h, ?_, hth⟩
    · linarith only [hcost_eq]
    rcases htd with ⟨hsa, hpo⟩ | ⟨hact, htb, hdl, hle, hts', htp', hti', hs_t, wLoc, wKey,
        hwl, hwn, hwk_ne, hwk, hfp_eq⟩
    · exact Or.inl ⟨hsa.trans (congrArg FastEpochMeta.trySalt hfm1),
        hpo.trans (congrArg FastEpochMeta.tryPos hfm1)⟩
    · right
      have hs_t0 : fm.trySalt < sMaxWhp fl.c fl.N := by rwa [hfm1] at hs_t
      rw [hfm1] at hact htb hdl hle hts'
      have hwk0 : fastKeyAt fl seeds.bkt s.mem b wLoc = wKey.val := by
        unfold fastKeyAt at hwk ⊢
        rw [hpair1 b hb wLoc (lt_trans hwl hlast_lt), ite_eq_right (fun h => hwn h.2)] at hwk
        exact hwk
      refine ⟨hact, htb, hdl, hle, hts', htp', hti', hs_t0, wLoc, wKey, uLast,
        hwl, hwn, hwk_ne, hwk0, huL.symm, ?_⟩
      exact (fpHash_congr_salt (congrArg FastEpochMeta.trySalt hfm1).symm wKey).trans
        (hfp_eq.trans (fpHash_congr_salt (congrArg FastEpochMeta.trySalt hfm1) uLast))
  · rw [ite_eq_right hlt]
    have hde : delLoc = lastLoc := by omega
    subst hde
    have hcp : memoryCost (pure () : Memory.Prog Unit) s = 0 := rfl
    rcases ht with ⟨mc, mo, mb, ht⟩
    have hth : TierInvHole slackCur fl seeds s.mem b delLoc true :=
      ⟨mc, mo, mb,
        { role_lt := ht.role_lt
          subStep_lt := ht.subStep_lt
          bkt_meta_bounds := ht.bkt_meta_bounds
          cur_valid := ht.cur_valid
          cur_raw := ht.cur_raw
          cur_clr := ht.cur_clr
          cur_ia := ht.cur_ia
          cur_na := ht.cur_na
          cur_sound := ht.cur_sound
          old_valid_half := ht.old_valid_half
          old_clear_half := ht.old_clear_half
          bt_valid := ht.bt_valid
          bt_sound := ht.bt_sound
          complete := ht.complete
          shadow := fun b' hb' hsc => by
            obtain ⟨h1, h2, h3, h4, sm, hvs, heq⟩ := ht.shadow b' hb' hsc
            have h3b : 4 * (extractFastMeta fl s.mem).shadowIns b' +
                5 * ((extractBlockPool fl.mp s.mem).bktCount b' -
                  ((extractFastMeta fl s.mem).shadowCode b' - 1)) ≤
                20 * slabScale fl.N ^ 12 := by simpa using h3
            have h4b : 8 * ((extractFastMeta fl s.mem).curIns b' - 6 * slabScale fl.N ^ 12) +
                ((extractBlockPool fl.mp s.mem).bktCount b' -
                  ((extractFastMeta fl s.mem).shadowCode b' - 1)) ≤
                4 * slabScale fl.N ^ 12 := by simpa using h4
            exact ⟨h1, h2, by split_ifs <;> omega, by split_ifs <;> omega, sm, hvs, heq⟩
          tryAct_le := ht.tryAct_le
          try_ok := fun hta1 => by
            obtain ⟨h1, hb_t, hs_t, htp, hsc, hbd, tm, hvt, htm1, htm2⟩ := ht.try_ok hta1
            have hbdb : 4 * (extractFastMeta fl s.mem).tryIns +
                5 * ((extractBlockPool fl.mp s.mem).bktCount (extractFastMeta fl s.mem).tryBkt -
                  (extractFastMeta fl s.mem).tryPos) ≤
                20 * slabScale fl.N ^ 12 := by simpa using hbd
            exact ⟨h1, hb_t, hs_t, htp, hsc, by split_ifs <;> omega, tm, hvt, htm1, htm2⟩ }⟩
    refine ⟨rfl, hr, by omega, rfl, hbp_inv, rfl, rfl, fun _ _ => rfl,
      fun b' _ loc' _ => by rw [ite_eq_right (fun h => hlt h.2.2)]; rfl,
      fun _ => ⟨rfl, fun _ _ => rfl⟩,
      rfl, fun _ _ _ h => Or.inl h,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ _ => rfl, Nat.le_succ _, fun _ => rfl, Or.inl ⟨rfl, rfl⟩, hth⟩

/-- Complete unconditional specification of `fastRemoveAtProg`: removes entry `(b, delLoc)` holding
`u : Fin fl.U` by swap-popping `(b, cnt - 1)` into `delLoc` when `delLoc < cnt - 1`, preserving
`FastEpochInvGen` (with `s_abs' = Function.update s_abs u none`) on **100%** of hash seeds in
`O_c(1)` worst-case memory operations (`≤ fastRemoveAtCost fl.c`). -/
theorem fastRemoveAtProg_spec {slackCur : ℕ} {fl : FastEpochLayout} {w b delLoc : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (u : Fin fl.U)
    (hslack : slackCur ≤ 1)
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl 0 seeds s.mem s_abs)
    (hb : b < numBucketsWhp fl.N)
    (hdel : delLoc < (extractBlockPool fl.mp s.mem).bktCount b)
    (hk_u : fastKeyAt fl seeds.bkt s.mem b delLoc = u.val) :
    let fm := extractFastMeta fl s.mem
    let bp := extractBlockPool fl.mp s.mem
    let oldRole := 1 - fm.curBufRole
    let oldTr := extractBufTrie (fl.trieL oldRole) s.mem
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    let s' := (Memory.spec 0).clientState s (fastRemoveAtProg ((fl.pBase, b), (delLoc, u.val)))
    let fm' := extractFastMeta fl s'.mem
    let bp' := extractBlockPool fl.mp s'.mem
    let oldTr' := extractBufTrie (fl.trieL oldRole) s'.mem
    s'.frontier = s.frontier ∧
    memoryCost (fastRemoveAtProg ((fl.pBase, b), (delLoc, u.val))) s ≤ fastRemoveAtCost fl.c ∧
    FastEpochInvGen slackCur fl slack' seeds s'.mem (Function.update s_abs u none) ∧
    bp'.nSide = bp.nSide - 1 ∧
    bp'.bktCount b = bp.bktCount b - 1 ∧
    (∀ b' ≠ b, bp'.bktCount b' = bp.bktCount b') ∧
    (∀ b' < numBucketsWhp fl.N, ∀ loc' < bp'.bktCount b',
      fastKeyAt fl seeds.bkt s'.mem b' loc' =
        if b' = b ∧ loc' = delLoc then fastKeyAt fl seeds.bkt s.mem b (bp.bktCount b - 1)
        else fastKeyAt fl seeds.bkt s.mem b' loc') ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      (extractPagePair fl.io.pgL s'.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
      (extractPagePair fl.io.pgL s'.mem).totalItems =
        (extractPagePair fl.io.pgL s.mem).totalItems - 1 ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) ∧
    oldTr'.itemAlloc = oldTr.itemAlloc ∧
    (∀ id b' loc', bufCheckSlot oldTr' id = some (b', loc') →
      (bufCheckSlot oldTr id = some (b', loc') ∧
        (fm.subStep < qEpochWhp fl.N / 2 → ¬(b' = b ∧ loc' = delLoc))) ∨
      (b' = b ∧ loc' = delLoc ∧ delLoc < bp.bktCount b - 1 ∧
        bufCheckSlot oldTr id = some (b, bp.bktCount b - 1))) ∧
    fm'.curBufRole = fm.curBufRole ∧
    fm'.subStep = fm.subStep ∧
    fm'.drainPos = fm.drainPos ∧
    fm'.tryAct = fm.tryAct ∧
    fm'.tryBkt = fm.tryBkt ∧
    fm'.bktSalt = fm.bktSalt ∧
    (∀ b' ≠ b, fm'.curRole b' = fm.curRole b' ∧ fm'.curIns b' = fm.curIns b' ∧
      fm'.shadowIns b' = fm.shadowIns b' ∧ fm'.shadowCode b' = fm.shadowCode b') ∧
    (fm.shadowCode b = bp.bktCount b → fm'.shadowCode b = 0) ∧
    (fm.shadowCode b ≠ bp.bktCount b →
      fm'.shadowCode b = fm.shadowCode b ∧ fm'.curIns b = fm.curIns b ∧
      fm'.shadowIns b ≤ fm.shadowIns b + 1 ∧
      (fm.shadowCode b = 0 ∨ ¬(delLoc < fm.shadowCode b - 1) →
        fm'.shadowIns b = fm.shadowIns b)) ∧
    ((fm'.trySalt = fm.trySalt ∧
      fm'.tryPos = (if fm.tryAct = 1 ∧ fm.tryBkt = b ∧ fm.tryPos = bp.bktCount b then
        bp.bktCount b - 1 else fm.tryPos)) ∨
      (fm.tryAct = 1 ∧ fm.tryBkt = b ∧ delLoc < fm.tryPos ∧ fm.tryPos ≤ bp.bktCount b - 1 ∧
        fm'.trySalt = (if fm.trySalt + 1 < sMaxWhp fl.c fl.N then fm.trySalt + 1 else 0) ∧
        fm'.tryPos = 0 ∧ fm'.tryIns = 0 ∧
        ∃ (hs_t : fm.trySalt < sMaxWhp fl.c fl.N) (wLoc : ℕ) (wKey uLast : Fin fl.U),
          wLoc < bp.bktCount b - 1 ∧ wLoc ≠ delLoc ∧ wKey ≠ uLast ∧
          fastKeyAt fl seeds.bkt s.mem b wLoc = wKey.val ∧
          fastKeyAt fl seeds.bkt s.mem b (bp.bktCount b - 1) = uLast.val ∧
          fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ wKey =
            fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ uLast)) := by
  dsimp only
  have hr0 := hinv.ready hv rfl
  have hpt := hinv.param_table
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  set cnt := bp.bktCount b
  set lastLoc := cnt - 1
  have hcnt_pos : 0 < cnt := Nat.zero_lt_of_lt hdel
  have hlast_eq : cnt = lastLoc + 1 := by omega
  have hdel_le : delLoc ≤ lastLoc := by omega
  have hlast_lt : lastLoc < cnt := by omega
  have hm11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := hpt 11 (by decide)
  obtain ⟨hcnt_r, hcnt_c⟩ := fastReadBktCntProg_spec hr0 hinv.bp_inv.1.core hb
  obtain ⟨u₀, _, hu₀, _, hb_u, hq_u, _⟩ := hinv.bktSlot_refines hb hdel
  have hu_eq : u₀ = u := Fin.ext (hu₀.trans hk_u)
  rw [hu_eq] at hb_u hq_u
  obtain ⟨uLast, vLast, huL, hvL, _, hqL, _⟩ := hinv.bktSlot_refines hb hlast_lt
  have hne_last : ∀ loc' < lastLoc, loc' ≠ delLoc →
      fastKeyAt fl seeds.bkt s.mem b loc' ≠ uLast.val := fun loc' hl' _ heq => by
    have hcv : bp.CoreValid := hinv.bp_inv.1.core
    have hloc'_lt : loc' < cnt := lt_trans hl' hlast_lt
    obtain ⟨u', _, hu', _, _, hq_u', _⟩ := hinv.bktSlot_refines hb hloc'_lt
    have hu_e : u' = uLast := Fin.ext (hu'.trans heq)
    have hq_e : (slotIoPairAt fl.io s.mem (bp.toPhys b loc')).1 =
        (slotIoPairAt fl.io s.mem (bp.toPhys b lastLoc)).1 := by
      change (bpPairAt fl.bpL s.mem b loc').1 = (bpPairAt fl.bpL s.mem b lastLoc).1
      rw [← hq_u', hu_e, hqL]
    have hp1 := hcv.toPhys_lt hb hloc'_lt
    have hp2 := hcv.toPhys_lt hb hlast_lt
    have how1 : (bp.ownerOf (bp.toPhys b loc')).1 = b := by rw [hcv.ownerOf_toPhys hb hloc'_lt]
    have how2 : (bp.ownerOf (bp.toPhys b lastLoc)).1 = b := by rw [hcv.ownerOf_toPhys hb hlast_lt]
    have hpe := hinv.refines.slot_inj _ hp1 _ hp2 (how1.trans how2.symm) hq_e
    have hle := congrArg (fun x => (bp.ownerOf x).2) hpe
    rw [hcv.ownerOf_toPhys hb hloc'_lt, hcv.ownerOf_toPhys hb hlast_lt] at hle
    exact (Nat.ne_of_lt hl') hle
  unfold fastRemoveAtProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s from rfl,
    hm11_r, prog_memoryCost_read, ite_eq_left hb,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadBktCntProg, hcnt_r, ite_eq_left hdel, pure_bind,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have seed_bkt_of : ∀ m : ℕ → ℕ, (∀ a, ¬fl.OwnsFastAddr a → m a = s.mem a) →
      BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w (redWidthWhp fl.U)
        (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt m := fun m hm =>
    hinv.seed_bkt.congr_on hw_pos fun a h1 h2 =>
      hm a (hv.not_ownsFast_seeds
        (by dsimp only [FastEpochLayout.bktHashBase] at h1; exact h1)
        (by dsimp only [FastEpochLayout.bktHashBase] at h2
            unfold offBktMeta offFpHash offBktHash at *; omega))
  have seed_fp_of : ∀ m : ℕ → ℕ, (∀ a, ¬fl.OwnsFastAddr a → m a = s.mem a) →
      BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
        (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp m := fun m hm =>
    hinv.seed_fp.congr_on hw_pos fun a h1 h2 =>
      hm a (hv.not_ownsFast_seeds
        (by dsimp only [FastEpochLayout.fpHashBase] at h1; unfold offFpHash at h1
            have : offBktHash ≤ offFpHash fl.c fl.w fl.U := by
              unfold offFpHash; exact Nat.le_add_right _ _
            omega)
        (by dsimp only [FastEpochLayout.fpHashBase] at h2; unfold offBktMeta; omega))
  -- Step 1: `fastUnindexAtProg`
  obtain ⟨hfr1, hr1, hc1, hbp1, hfm1, hm0_1, hm2_1, hoi1, hof1, hia1, hchk1, ht1⟩ :=
    fastUnindexAtProg_spec u hv hinv hb hdel hk_u
  generalize hs1_def : (Memory.spec 0).clientState s
    (fastUnindexAtProg ((fl.pBase, (b, delLoc)), u.val)) = s1
  rw [hs1_def] at hfr1 hr1 hbp1 hfm1 hm0_1 hm2_1 hoi1 hof1 hia1 hchk1 ht1
  have hbp_inv1 : fl.bpL.StateInv 0 s1.mem := bpStateInv_congr_io hv hinv.bp_inv hbp1 hoi1
  have hpair1_eq : ∀ b' < numBucketsWhp fl.N, ∀ loc' < bp.bktCount b',
      bpPairAt fl.bpL s1.mem b' loc' = bpPairAt fl.bpL s.mem b' loc' := fun b' hb' loc' hl' =>
    bpPairAt_eq_of_fixed_pool hv hinv.bp_inv hbp1 hoi1 hb' hl'
  have hkey1_eq : ∀ b' < numBucketsWhp fl.N, ∀ loc' < bp.bktCount b',
      fastKeyAt fl seeds.bkt s1.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
    fun b' hb' loc' hl' => fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp1 hoi1 hb' hl'
  have hlast_ref1 : ∃ (uLast' : Fin fl.U) (vLast' : Fin fl.V),
      uLast'.val = fastKeyAt fl seeds.bkt s1.mem b lastLoc ∧
      vLast'.val = (bpPairAt fl.bpL s1.mem b lastLoc).2 ∧
      keyQuotient (bWhp fl.N) uLast'.val = (bpPairAt fl.bpL s1.mem b lastLoc).1 ∧
      ∀ loc' < lastLoc, loc' ≠ delLoc → fastKeyAt fl seeds.bkt s1.mem b loc' ≠ uLast'.val := by
    refine ⟨uLast, vLast,
      huL.trans (hkey1_eq b hb lastLoc hlast_lt).symm,
      hvL.trans (congrArg Prod.snd (hpair1_eq b hb lastLoc hlast_lt)).symm,
      hqL.trans (congrArg Prod.fst (hpair1_eq b hb lastLoc hlast_lt)).symm,
      fun loc' hl' hne => by
        rw [hkey1_eq b hb loc' (lt_trans hl' hlast_lt)]; exact hne_last loc' hl' hne⟩
  -- Step 2: `fastSwapLastDownProg`
  obtain ⟨hfr2, hr2, hc2, hbp2, hbp_inv2, hm0_2, hm2_2, hof2, hpair2, hpart2,
    hia2, hchk2, hcr2, hss2, hdp2, hta2, htb2, hbs2, hrl2, hci2, hsc2, hsi_ne2, hsi_le2,
    hsi_noop2, htry_d2, ht2⟩ :=
    fastSwapLastDownProg_spec hslack hr1 hbp_inv1 (seed_bkt_of s1.mem hof1)
      (seed_fp_of s1.mem hof1) hb (by rw [hbp1]; exact hinv.bkt_le_capMax b hb)
      (by rw [hbp1]; exact hlast_eq) hdel_le hlast_ref1 ht1
  generalize hs2_def : (Memory.spec 0).clientState s1
    (fastSwapLastDownProg ((fl.pBase, b), (delLoc, lastLoc))) = s2
  rw [hs2_def] at hfr2 hr2 hbp2 hbp_inv2 hm0_2 hm2_2 hof2 hpair2 hpart2
  rw [hs2_def] at hia2 hchk2 hcr2 hss2 hdp2 hta2 htb2 hbs2 hrl2 hci2 hsc2 hsi_ne2 hsi_le2
  rw [hs2_def] at hsi_noop2 htry_d2 ht2
  have hbp12 : extractBlockPool fl.mp s2.mem = bp := hbp2.trans hbp1
  have hof12 : ∀ a, ¬fl.OwnsFastAddr a → s2.mem a = s.mem a :=
    fun a ha => (hof2 a ha).trans (hof1 a ha)
  have hpg_up1 : fl.io.usePaged ≠ 0 →
      extractPageUnperm fl.io.pgL s1.mem = extractPageUnperm fl.io.pgL s.mem ∧
      extractPagePair fl.io.pgL s1.mem = extractPagePair fl.io.pgL s.mem ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s1.mem idx = slotIoPairAt fl.io.partner s.mem idx := fun hup =>
    pagePair_partner_eq_of_io hv hup hinv.bp_inv hoi1
  have hclean2_eq : fl.io.usePaged ≠ 0 →
      (extractPageUnperm fl.io.pgL s2.mem).cleanPhase =
        (extractPageUnperm fl.io.pgL s.mem).cleanPhase := fun hup => by
    rw [(hpart2 hup).1, (hpg_up1 hup).1]
  have hslack_eq : (if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s2.mem).cleanPhase = 0
      then 0 else 24) =
      (if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0
        then 0 else 24) := by
    by_cases hup : fl.io.usePaged = 0
    · simp [hup]
    · simp [hup, hclean2_eq hup]
  -- Step 3: `fastBpPopBktBackProg`
  obtain ⟨hfr3, hr3, hc3, hbp_inv3, hns3, hbc_b3, hbc_ne3, hpair3, hfm3, hm0_3, hm2_3,
    hbt3, htr3, hof3, hpart3⟩ :=
    fastBpPopBktBackProg_spec hr2 hbp_inv2 hb (by rw [hbp12]; exact hcnt_pos)
  generalize hs3_def : (Memory.spec 0).clientState s2 (fastBpPopBktBackProg (fl.pBase, b)) = s3
  rw [hs3_def] at hfr3 hr3 hbp_inv3 hns3 hbc_b3 hbc_ne3 hpair3 hfm3 hm0_3 hm2_3
  rw [hs3_def] at hbt3 htr3 hof3 hpart3
  rw [hslack_eq] at hbp_inv3
  have hof123 : ∀ a, ¬fl.OwnsFastAddr a → s3.mem a = s.mem a :=
    fun a ha => (hof3 a ha).trans (hof12 a ha)
  have hbc_b3' : (extractBlockPool fl.mp s3.mem).bktCount b = lastLoc := by
    rw [hbc_b3, hbp12]
  have hbc_ne3' : ∀ b' ≠ b, (extractBlockPool fl.mp s3.mem).bktCount b' = bp.bktCount b' :=
    fun b' hne => (hbc_ne3 b' hne).trans (congrArg (fun x => x.bktCount b') hbp12)
  rcases ht2 with ⟨mapCur, mapOld, mapBTree, ht2⟩
  have hrl3_lt : (extractFastMeta fl s3.mem).curRole b < 3 := by
    rw [hfm3]; exact (ht2.bkt_meta_bounds b hb).2.1
  have hsh3_ins : (extractFastMeta fl s3.mem).shadowCode b = cnt →
      (extractFastMeta fl s3.mem).shadowIns b ≤ 5 * slabScale fl.N ^ 12 := fun heq => by
    rw [hfm3] at heq ⊢
    have hnz : (extractFastMeta fl s2.mem).shadowCode b ≠ 0 := by omega
    obtain ⟨_, _, hbd, _⟩ := ht2.shadow b hb hnz
    have hbd' : 4 * (extractFastMeta fl s2.mem).shadowIns b +
        5 * (bp.bktCount b - 1 - ((extractFastMeta fl s2.mem).shadowCode b - 1)) ≤
        20 * slabScale fl.N ^ 12 := by simpa [hbp12] using hbd
    omega
  -- Step 4: `fastPromoteShadowIfDoneProg`
  obtain ⟨hfr4, hr4, hc4, hbp4, hm0_4, hm2_4, hbt4, htr4, hoi4, hof4, hnoop4, hprom4⟩ :=
    fastPromoteShadowIfDoneProg_spec hr3 hb hcnt_pos hrl3_lt hsh3_ins
  generalize hs4_def : (Memory.spec 0).clientState s3
    (fastPromoteShadowIfDoneProg ((fl.pBase, b), cnt)) = s4
  rw [hs4_def] at hfr4 hr4 hbp4 hm0_4 hm2_4 hbt4 htr4 hoi4 hof4 hnoop4 hprom4
  have hof14 : ∀ a, ¬fl.OwnsFastAddr a → s4.mem a = s.mem a :=
    fun a ha => (hof4 a ha).trans (hof123 a ha)
  -- Step 5: `fastClampTryPosProg`
  obtain ⟨hfr5, hr5, hc5, hbp5, hm0_5, hm2_5, hbt5, htr5, hoi5, hof5, hfm5⟩ :=
    fastClampTryPosProg_spec (b := b) (cnt := cnt) (lastLoc := lastLoc) hr4
  generalize hs5_def : (Memory.spec 0).clientState s4
    (fastClampTryPosProg ((fl.pBase, b), (cnt, lastLoc))) = s5
  rw [hs5_def] at hfr5 hr5 hbp5 hm0_5 hm2_5 hbt5 htr5 hoi5 hof5 hfm5
  have hbp35 : extractBlockPool fl.mp s5.mem = extractBlockPool fl.mp s3.mem := hbp5.trans hbp4
  have hof_tot : ∀ a, ¬fl.OwnsFastAddr a → s5.mem a = s.mem a :=
    fun a ha => (hof5 a ha).trans (hof14 a ha)
  have hoi35 : ∀ a, fl.io.OwnsAddr a → s5.mem a = s3.mem a :=
    fun a ha => (hoi5 a ha).trans (hoi4 a ha)
  have hv3 : fl.Valid w s3.frontier := (hfr3.trans (hfr2.trans hfr1)).symm ▸ hv
  have hbp_inv5 : fl.bpL.StateInv
      (if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24)
      s5.mem := bpStateInv_congr_io hv3 hbp_inv3 hbp35 hoi35
  have hns5 : (extractBlockPool fl.mp s5.mem).nSide = bp.nSide - 1 := by
    rw [hbp35, hns3, hbp12]
  have hbc_b5 : (extractBlockPool fl.mp s5.mem).bktCount b = bp.bktCount b - 1 := by
    rw [hbp35, hbc_b3, hbp12]
  have hbc_ne5 : ∀ b' ≠ b, (extractBlockPool fl.mp s5.mem).bktCount b' = bp.bktCount b' :=
    fun b' hne => by rw [hbp35]; exact hbc_ne3' b' hne
  have hpair5_eq3 : ∀ b' < numBucketsWhp fl.N,
      ∀ loc' < (extractBlockPool fl.mp s5.mem).bktCount b',
      bpPairAt fl.bpL s5.mem b' loc' = bpPairAt fl.bpL s3.mem b' loc' := by
    intro b' hb' loc' hl'
    exact bpPairAt_eq_of_fixed_pool hv3 hbp_inv3 hbp35 hoi35 hb' (hbp35 ▸ hl')
  have hpair5_eq2 : ∀ b' < numBucketsWhp fl.N,
      ∀ loc' < (extractBlockPool fl.mp s5.mem).bktCount b',
      bpPairAt fl.bpL s5.mem b' loc' = bpPairAt fl.bpL s2.mem b' loc' := fun b' hb' loc' hl' =>
    (hpair5_eq3 b' hb' loc' hl').trans (hpair3 b' hb' loc' (hbp35 ▸ hl'))
  have hpair5_raw : ∀ b' < numBucketsWhp fl.N,
      ∀ loc' < (extractBlockPool fl.mp s5.mem).bktCount b',
      bpPairAt fl.bpL s5.mem b' loc' =
        if b' = b ∧ loc' = delLoc then bpPairAt fl.bpL s.mem b lastLoc
        else bpPairAt fl.bpL s.mem b' loc' := by
    intro b' hb' loc' hl'
    have hl_lt_bp : loc' < bp.bktCount b' := by
      by_cases hbb : b' = b
      · rw [hbb, hbc_b5] at hl'; rw [hbb]; omega
      · rwa [hbc_ne5 _ hbb] at hl'
    rw [hpair5_eq2 b' hb' loc' hl', hpair2 b' hb' loc' (hbp1.symm ▸ hl_lt_bp)]
    by_cases hbd : b' = b ∧ loc' = delLoc
    · have hdl_lt : delLoc < lastLoc := by
        rw [hbd.1, hbd.2, hbc_b5] at hl'; exact hl'
      rw [ite_eq_left ⟨hbd.1, hbd.2, hdl_lt⟩, ite_eq_left hbd]
      exact hpair1_eq b hb lastLoc hlast_lt
    · rw [ite_eq_right (fun h => hbd ⟨h.1, h.2.1⟩), ite_eq_right hbd]
      exact hpair1_eq b' hb' loc' hl_lt_bp
  have hkey5_eq2 : ∀ b' < numBucketsWhp fl.N,
      ∀ loc' < (extractBlockPool fl.mp s5.mem).bktCount b',
      fastKeyAt fl seeds.bkt s5.mem b' loc' = fastKeyAt fl seeds.bkt s2.mem b' loc' := by
    intro b' hb' loc' hl'
    unfold fastKeyAt; rw [hpair5_eq2 b' hb' loc' hl']
  have hkey5_raw : ∀ b' < numBucketsWhp fl.N,
      ∀ loc' < (extractBlockPool fl.mp s5.mem).bktCount b',
      fastKeyAt fl seeds.bkt s5.mem b' loc' =
        if b' = b ∧ loc' = delLoc then fastKeyAt fl seeds.bkt s.mem b lastLoc
        else fastKeyAt fl seeds.bkt s.mem b' loc' := by
    intro b' hb' loc' hl'
    unfold fastKeyAt; rw [hpair5_raw b' hb' loc' hl']
    split_ifs with h
    · rw [h.1]
    · rfl
  have href5 : PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt)
      (extractBlockPool fl.mp s5.mem).nSide
      (fun p => ((extractBlockPool fl.mp s5.mem).ownerOf p).1)
      (slotIoPairAt fl.io s5.mem) (Function.update s_abs u none) :=
    poolRefines_bpSwapPop hinv.bp_inv.1.core hbp_inv5.1.core hinv.refines hb hdel
      hb_u.symm hq_u.symm hbc_b5 hbc_ne5 hpair5_raw
  have htr35 : ∀ r < 2, extractBufTrie (fl.trieL r) s5.mem =
      extractBufTrie (fl.trieL r) s2.mem := fun r hrr =>
    (htr5 r hrr).trans ((htr4 r hrr).trans (htr3 r hrr))
  have hbt35 : ∀ b' < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b' r s5.mem = extractBTreeSlice fl.btL b' r s2.mem :=
    fun b' hb' r hrr => (hbt5 b' hb' r hrr).trans ((hbt4 b' hb' r hrr).trans (hbt3 b' hb' r hrr))
  have hfm4_core : (extractFastMeta fl s4.mem).curBufRole = (extractFastMeta fl s2.mem).curBufRole ∧
      (extractFastMeta fl s4.mem).subStep = (extractFastMeta fl s2.mem).subStep ∧
      (extractFastMeta fl s4.mem).drainPos = (extractFastMeta fl s2.mem).drainPos ∧
      (extractFastMeta fl s4.mem).tryAct = (extractFastMeta fl s2.mem).tryAct ∧
      (extractFastMeta fl s4.mem).tryBkt = (extractFastMeta fl s2.mem).tryBkt ∧
      (extractFastMeta fl s4.mem).trySalt = (extractFastMeta fl s2.mem).trySalt ∧
      (extractFastMeta fl s4.mem).tryPos = (extractFastMeta fl s2.mem).tryPos ∧
      (extractFastMeta fl s4.mem).tryIns = (extractFastMeta fl s2.mem).tryIns ∧
      (extractFastMeta fl s4.mem).bktSalt = (extractFastMeta fl s2.mem).bktSalt ∧
      (extractFastMeta fl s4.mem).shadowIns = (extractFastMeta fl s2.mem).shadowIns ∧
      (∀ b' ≠ b, (extractFastMeta fl s4.mem).curRole b' = (extractFastMeta fl s2.mem).curRole b' ∧
        (extractFastMeta fl s4.mem).curIns b' = (extractFastMeta fl s2.mem).curIns b' ∧
        (extractFastMeta fl s4.mem).shadowCode b' = (extractFastMeta fl s2.mem).shadowCode b') := by
    by_cases hdone : (extractFastMeta fl s3.mem).shadowCode b = cnt
    · rw [hprom4 hdone, hfm3]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun b' hne =>
        ⟨Function.update_of_ne hne _ _, Function.update_of_ne hne _ _,
          Function.update_of_ne hne _ _⟩⟩
    · rw [hnoop4 hdone, hfm3]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
  have hfm5_core : (extractFastMeta fl s5.mem).curBufRole = (extractFastMeta fl s4.mem).curBufRole ∧
      (extractFastMeta fl s5.mem).subStep = (extractFastMeta fl s4.mem).subStep ∧
      (extractFastMeta fl s5.mem).drainPos = (extractFastMeta fl s4.mem).drainPos ∧
      (extractFastMeta fl s5.mem).tryAct = (extractFastMeta fl s4.mem).tryAct ∧
      (extractFastMeta fl s5.mem).tryBkt = (extractFastMeta fl s4.mem).tryBkt ∧
      (extractFastMeta fl s5.mem).trySalt = (extractFastMeta fl s4.mem).trySalt ∧
      (extractFastMeta fl s5.mem).tryIns = (extractFastMeta fl s4.mem).tryIns ∧
      (extractFastMeta fl s5.mem).bktSalt = (extractFastMeta fl s4.mem).bktSalt ∧
      (extractFastMeta fl s5.mem).curRole = (extractFastMeta fl s4.mem).curRole ∧
      (extractFastMeta fl s5.mem).curIns = (extractFastMeta fl s4.mem).curIns ∧
      (extractFastMeta fl s5.mem).shadowIns = (extractFastMeta fl s4.mem).shadowIns ∧
      (extractFastMeta fl s5.mem).shadowCode = (extractFastMeta fl s4.mem).shadowCode ∧
      (extractFastMeta fl s5.mem).tryPos =
        if (extractFastMeta fl s4.mem).tryAct = 1 ∧ (extractFastMeta fl s4.mem).tryBkt = b ∧
            (extractFastMeta fl s4.mem).tryPos = cnt then
          lastLoc else (extractFastMeta fl s4.mem).tryPos := by
    rw [hfm5]; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsc3_eq : (extractFastMeta fl s3.mem).shadowCode b = fm.shadowCode b := by
    rw [hfm3, hsc2, hfm1]
  have hprom_res : (fm.shadowCode b = cnt →
      (extractFastMeta fl s5.mem).curRole b = shadowRoleOf (fm.curRole b) ∧
      (extractFastMeta fl s5.mem).curIns b = (extractFastMeta fl s2.mem).shadowIns b ∧
      (extractFastMeta fl s5.mem).shadowCode b = 0) ∧
      (fm.shadowCode b ≠ cnt →
        (extractFastMeta fl s5.mem).curRole b = fm.curRole b ∧
        (extractFastMeta fl s5.mem).curIns b = fm.curIns b ∧
        (extractFastMeta fl s5.mem).shadowCode b = fm.shadowCode b) := by
    constructor
    · intro hd
      have hpr := hprom4 (hsc3_eq.trans hd)
      rw [hfm5_core.2.2.2.2.2.2.2.2.1, hfm5_core.2.2.2.2.2.2.2.2.2.1,
        hfm5_core.2.2.2.2.2.2.2.2.2.2.2.1, hpr, hfm3]
      refine ⟨?_, ?_, ?_⟩
      · dsimp only; rw [Function.update_self, hrl2, hfm1]
      · dsimp only; rw [Function.update_self]
      · dsimp only; rw [Function.update_self]
    · intro hn
      have hnp := hnoop4 (fun h => hn (hsc3_eq.symm.trans h))
      rw [hfm5_core.2.2.2.2.2.2.2.2.1, hfm5_core.2.2.2.2.2.2.2.2.2.1,
        hfm5_core.2.2.2.2.2.2.2.2.2.2.2.1, hnp, hfm3, hrl2, hci2, hsc2, hfm1]
      exact ⟨rfl, rfl, rfl⟩
  have hrole_lt : fm.curBufRole < 2 := hinv.role_lt
  have hold_lt : 1 - fm.curBufRole < 2 := by omega
  have hcost_tot : 1 + (memoryCost (fastReadBktCntProg (fl.pBase, b)) s +
      (memoryCost (fastUnindexAtProg ((fl.pBase, (b, delLoc)), u.val)) s +
        (memoryCost (fastSwapLastDownProg ((fl.pBase, b), (delLoc, lastLoc))) s1 +
          (memoryCost (fastBpPopBktBackProg (fl.pBase, b)) s2 +
            (memoryCost (fastPromoteShadowIfDoneProg ((fl.pBase, b), cnt)) s3 +
              memoryCost (fastClampTryPosProg ((fl.pBase, b), (cnt, lastLoc))) s4))))) ≤
      fastRemoveAtCost fl.c := by
    unfold fastRemoveAtCost
    have hm1 : memoryCost (fastUnindexAtProg ((fl.pBase, (b, delLoc)), u.val)) s ≤
        6 * cTabWhp fl.c + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 18 * hMaxBTree + 280 := hc1
    have hm2 : memoryCost (fastSwapLastDownProg ((fl.pBase, b), (delLoc, lastLoc))) s1 ≤
        30 * cTabWhp fl.c + 6 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 156 * hMaxBTree + 740 := hc2
    have hm3 : memoryCost (fastBpPopBktBackProg (fl.pBase, b)) s2 ≤ 8527 := hc3
    have hm4 : memoryCost (fastPromoteShadowIfDoneProg ((fl.pBase, b), cnt)) s3 ≤ 65 := hc4
    have hm5 : memoryCost (fastClampTryPosProg ((fl.pBase, b), (cnt, lastLoc))) s4 ≤ 25 := hc5
    have hmul : 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 6 * dTabWhp fl.c * (cTabWhp fl.c + 2) ≤
        12 * dTabWhp fl.c * (cTabWhp fl.c + 2) := by
      have : 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 6 * dTabWhp fl.c * (cTabWhp fl.c + 2) =
          10 * dTabWhp fl.c * (cTabWhp fl.c + 2) := by ring
      rw [this]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
    linarith only [hcnt_c, hm1, hm2, hm3, hm4, hm5, hmul]
  have hpart_tot : fl.io.usePaged ≠ 0 →
      (extractPagePair fl.io.pgL s5.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
      (extractPagePair fl.io.pgL s5.mem).totalItems =
        (extractPagePair fl.io.pgL s.mem).totalItems - 1 ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s5.mem idx = slotIoPairAt fl.io.partner s.mem idx := by
    intro hup
    have hp1 := hpg_up1 hup
    have hp2 := hpart2 hup
    have hp3 := hpart3 hup
    have hp35 := pagePair_partner_eq_of_io hv3 hup hbp_inv3 hoi35
    have hvl12 : (extractPagePair fl.io.pgL s2.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side :=
      congrArg (fun u => u.st.virtLen fl.io.partner.side) (hp2.1.trans hp1.1)
    have hti12 : (extractPagePair fl.io.pgL s2.mem).totalItems =
        (extractPagePair fl.io.pgL s.mem).totalItems :=
      congrArg (fun u => u.st.totalItems) (hp2.1.trans hp1.1)
    refine ⟨by rw [hp35.2.1, hp3.1, hvl12], by rw [hp35.2.1, hp3.2.1, hti12], fun idx hidx => ?_⟩
    have hidx1 : idx < (extractPagePair fl.io.pgL s1.mem).virtLen fl.io.partner.side := by
      rw [hp1.2.1]; exact hidx
    have hidx2 : idx < (extractPagePair fl.io.pgL s2.mem).virtLen fl.io.partner.side := by
      rw [hvl12]; exact hidx
    have hidx3 : idx < (extractPagePair fl.io.pgL s3.mem).virtLen fl.io.partner.side := by
      rw [hp3.1, hvl12]; exact hidx
    exact (hp35.2.2 idx hidx3).trans
      ((hp3.2.2 idx hidx2).trans ((hp2.2 idx hidx1).trans (hp1.2.2 idx hidx)))
  have hcr5 : (extractFastMeta fl s5.mem).curBufRole = fm.curBufRole :=
    hfm5_core.1.trans (hfm4_core.1.trans (hcr2.trans (congrArg FastEpochMeta.curBufRole hfm1)))
  have hss5 : (extractFastMeta fl s5.mem).subStep = fm.subStep :=
    hfm5_core.2.1.trans (hfm4_core.2.1.trans (hss2.trans (congrArg FastEpochMeta.subStep hfm1)))
  have hdp5 : (extractFastMeta fl s5.mem).drainPos = fm.drainPos :=
    hfm5_core.2.2.1.trans (hfm4_core.2.2.1.trans
      (hdp2.trans (congrArg FastEpochMeta.drainPos hfm1)))
  have hta5 : (extractFastMeta fl s5.mem).tryAct = fm.tryAct :=
    hfm5_core.2.2.2.1.trans (hfm4_core.2.2.2.1.trans
      (hta2.trans (congrArg FastEpochMeta.tryAct hfm1)))
  have htb5 : (extractFastMeta fl s5.mem).tryBkt = fm.tryBkt :=
    hfm5_core.2.2.2.2.1.trans (hfm4_core.2.2.2.2.1.trans
      (htb2.trans (congrArg FastEpochMeta.tryBkt hfm1)))
  have hbs5 : (extractFastMeta fl s5.mem).bktSalt = fm.bktSalt :=
    hfm5_core.2.2.2.2.2.2.2.1.trans (hfm4_core.2.2.2.2.2.2.2.2.1.trans
      (hbs2.trans (congrArg FastEpochMeta.bktSalt hfm1)))
  have hinv5 : FastEpochInvGen slackCur fl
      (if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24)
      seeds s5.mem (Function.update s_abs u none) := by
    have hL12_pos : 1 ≤ slabScale fl.N ^ 12 := Nat.one_le_pow 12 _ (by
      have := hv.thresh_le; have := whpThreshold_ge_64 fl.c
      exact slabScale_pos fl.N)
    refine
      { param_table := hr5.2.1
        hdr_N := hm0_5.trans (hm0_4.trans (hm0_3.trans (hm0_2.trans hm0_1)))
        mode_zero := hm2_5.trans (hm2_4.trans (hm2_3.trans (hm2_2.trans hm2_1)))
        seed_bkt := seed_bkt_of s5.mem hof_tot
        seed_fp := seed_fp_of s5.mem hof_tot
        bp_inv := hbp_inv5
        bkt_le_capMax := fun b' hb' => by
          have := hinv.bkt_le_capMax b' hb'
          by_cases hbb : b' = b
          · subst b'; rw [hbc_b5]; exact (Nat.sub_le _ 1).trans this
          · rw [hbc_ne5 b' hbb]; exact this
        refines := href5
        role_lt := by rw [hcr5]; exact hrole_lt
        subStep_lt := by rw [hss5]; exact hinv.subStep_lt
        bkt_meta_bounds := fun b' hb' => by
          dsimp only
          rw [congrFun hbs5 b', hta5, htb5]
          have hbds2 := ht2.bkt_meta_bounds b' hb'
          by_cases hbb : b' = b
          · subst b'
            by_cases hd : fm.shadowCode b = cnt
            · obtain ⟨hcr_p, hci_p, hsc_p⟩ := hprom_res.1 hd
              rw [hcr_p, hci_p, hsc_p]
              have hsc2_nz : (extractFastMeta fl s2.mem).shadowCode b ≠ 0 := by
                have heq : (extractFastMeta fl s2.mem).shadowCode b = fm.shadowCode b := by
                  rw [hsc2, hfm1]
                rw [heq, hd]; exact hcnt_pos.ne'
              obtain ⟨_, _, hbd2, _⟩ := ht2.shadow b hb hsc2_nz
              have hsi_le5 : (extractFastMeta fl s2.mem).shadowIns b ≤ 5 * slabScale fl.N ^ 12 := by
                have hbd2' : 4 * (extractFastMeta fl s2.mem).shadowIns b ≤
                    20 * slabScale fl.N ^ 12 := le_trans (Nat.le_add_right _ _) hbd2
                omega
              have hsr_lt := (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b hb).2.1).1
              refine ⟨(hinv.bkt_meta_bounds b hb).1, hsr_lt, by omega, fun _ _ => by omega⟩
            · obtain ⟨hcr_n, hci_n, hsc_n⟩ := hprom_res.2 hd
              rw [hcr_n, hci_n, hsc_n]
              exact hinv.bkt_meta_bounds b hb
          · obtain ⟨hcr_e, hci_e, hsc_e⟩ := hfm4_core.2.2.2.2.2.2.2.2.2.2 b' hbb
            rw [congrFun hfm5_core.2.2.2.2.2.2.2.2.1 b', hcr_e,
              congrFun hfm5_core.2.2.2.2.2.2.2.2.2.1 b', hci_e,
              congrFun hfm5_core.2.2.2.2.2.2.2.2.2.2.2.1 b', hsc_e,
              congrFun hrl2 b', congrFun hci2 b', congrFun hsc2 b', hfm1]
            exact hinv.bkt_meta_bounds b' hb'
        tiers := ?_ }
    have hlt_old_5 : ∀ b' < numBucketsWhp fl.N, ∀ loc' < bp.bktCount b',
        ¬(b' = b ∧ loc' = lastLoc) →
        loc' < (extractBlockPool fl.mp s5.mem).bktCount b' := fun b' _ loc' hl' hne => by
      by_cases hbb : b' = b
      · rw [hbb, hbc_b5]; rw [hbb] at hl'
        have : loc' ≠ lastLoc := fun he => hne ⟨hbb, he⟩
        change loc' < cnt - 1; omega
      · rwa [hbc_ne5 b' hbb]
    have h2_role : (extractFastMeta fl s2.mem).curBufRole = fm.curBufRole :=
      hcr2.trans (congrArg FastEpochMeta.curBufRole hfm1)
    have h2_ss : (extractFastMeta fl s2.mem).subStep = fm.subStep :=
      hss2.trans (congrArg FastEpochMeta.subStep hfm1)
    have h2_dp : (extractFastMeta fl s2.mem).drainPos = fm.drainPos :=
      hdp2.trans (congrArg FastEpochMeta.drainPos hfm1)
    have h2_ta : (extractFastMeta fl s2.mem).tryAct = fm.tryAct :=
      hta2.trans (congrArg FastEpochMeta.tryAct hfm1)
    have h2_tb : (extractFastMeta fl s2.mem).tryBkt = fm.tryBkt :=
      htb2.trans (congrArg FastEpochMeta.tryBkt hfm1)
    have h2_bs : (extractFastMeta fl s2.mem).bktSalt = fm.bktSalt :=
      hbs2.trans (congrArg FastEpochMeta.bktSalt hfm1)
    have h2_sc : (extractFastMeta fl s2.mem).shadowCode = fm.shadowCode :=
      hsc2.trans (congrArg FastEpochMeta.shadowCode hfm1)
    have htr_c5 : extractBufTrie (fl.trieL fm.curBufRole) s5.mem =
        extractBufTrie (fl.trieL (extractFastMeta fl s2.mem).curBufRole) s2.mem := by
      rw [h2_role]; exact htr35 _ hrole_lt
    have htr_o5 : extractBufTrie (fl.trieL (1 - fm.curBufRole)) s5.mem =
        extractBufTrie (fl.trieL (1 - (extractFastMeta fl s2.mem).curBufRole)) s2.mem := by
      rw [h2_role]; exact htr35 _ hold_lt
    refine ⟨mapCur, mapOld, mapBTree, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcr5, htr_c5]; exact ht2.cur_valid
    · rw [hcr5, htr_c5]; exact ht2.cur_raw
    · rw [hcr5, htr_c5]; exact ht2.cur_clr
    · rw [hcr5, hss5, htr_c5, ← h2_ss]; exact ht2.cur_ia
    · rw [hcr5, htr_c5]; exact ht2.cur_na
    · intro rk b' loc' hm
      obtain ⟨hb', hl', hne, u', hrk', hk'⟩ := ht2.cur_sound rk b' loc' hm
      have hl5 := hlt_old_5 b' hb' loc' (hbp12 ▸ hl') hne
      exact ⟨hb', hl5, u', hrk', (hkey5_eq2 b' hb' loc' hl5).trans hk'⟩
    · rw [hcr5, hss5, hdp5, hta5, htr_o5]
      by_cases hsub : fm.subStep < qEpochWhp fl.N / 2
      · rw [ite_eq_left hsub]
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, hsnd⟩ := ht2.old_valid_half (h2_ss.symm ▸ hsub)
        refine ⟨h1, h2, h3, h4, h5, h2_dp ▸ h6, by rwa [← h2_dp], fun rk b' loc' hm => ?_⟩
        obtain ⟨hcn, hb', hl', hne, u', hrk', hk'⟩ := hsnd rk b' loc' hm
        have hl5 := hlt_old_5 b' hb' loc' (hbp12 ▸ hl') hne
        exact ⟨hcn, hb', hl5, u', hrk', (hkey5_eq2 b' hb' loc' hl5).trans hk'⟩
      · rw [ite_eq_right hsub]
        have ho := ht2.old_clear_half (h2_ss.symm ▸ hsub)
        rw [h2_ta, h2_ss] at ho
        exact ho
    · intro b' hb'
      refine ⟨?_, ?_⟩
      · by_cases hbb : b' = b
        · subst b'
          by_cases hd : fm.shadowCode b = cnt
          · obtain ⟨hcr_p, hci_p, _⟩ := hprom_res.1 hd
            rw [hcr_p, hci_p]
            have hsc2_nz : (extractFastMeta fl s2.mem).shadowCode b ≠ 0 := by rw [h2_sc]; omega
            obtain ⟨_, _, _, _, shMap, hvs_sh, heq_sh⟩ := ht2.shadow b hb hsc2_nz
            have hsr_lt := (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b hb).2.1).1
            rw [hbt35 b hb _ hsr_lt]
            have hsh_eq_mb : shMap = mapBTree b := by
              funext fp
              rw [heq_sh fp]
              cases hm : mapBTree b fp with
              | none => rfl
              | some loc' =>
                have hsp : (extractFastMeta fl s2.mem).shadowCode b - 1 = lastLoc := by
                  rw [h2_sc, hd]
                obtain ⟨hl2, hne2, _⟩ := ht2.bt_sound b hb fp loc' hm
                rw [hbp12] at hl2
                have hloc_lt_l : loc' < lastLoc := by
                  have hne_l : loc' ≠ lastLoc := fun he => hne2 ⟨rfl, he⟩
                  exact lt_of_le_of_ne (Nat.le_pred_of_lt hl2) hne_l
                dsimp only; rw [hsp, ite_eq_left hloc_lt_l]
            have hrl_eq : (extractFastMeta fl s2.mem).curRole b = fm.curRole b := by
              rw [hrl2, hfm1]
            rwa [← hsh_eq_mb, ← hrl_eq]
          · obtain ⟨hcr_n, hci_n, _⟩ := hprom_res.2 hd
            rw [hcr_n, hci_n, hbt35 b hb _ (hinv.bkt_meta_bounds b hb).2.1]
            have hrl_eq : (extractFastMeta fl s2.mem).curRole b = fm.curRole b := by
              rw [hrl2, hfm1]
            have hci_eq : (extractFastMeta fl s2.mem).curIns b = fm.curIns b := by
              rw [hci2, hfm1]
            rw [← hrl_eq, ← hci_eq]; exact ht2.bt_valid b hb
        · obtain ⟨hcr_e, hci_e, _⟩ := hfm4_core.2.2.2.2.2.2.2.2.2.2 b' hbb
          rw [congrFun hfm5_core.2.2.2.2.2.2.2.2.1 b', hcr_e,
            congrFun hfm5_core.2.2.2.2.2.2.2.2.2.1 b', hci_e,
            hbt35 b' hb' _ (ht2.bkt_meta_bounds b' hb').2.1]
          exact ht2.bt_valid b' hb'
      · intro fp loc' hm
        obtain ⟨hl', hne, u', hfp', hk', hd1, hd2⟩ := ht2.bt_sound b' hb' fp loc' hm
        have hl5 := hlt_old_5 b' hb' loc' (hbp12 ▸ hl') hne
        have hbs_e : (extractFastMeta fl s5.mem).bktSalt b' =
            (extractFastMeta fl s2.mem).bktSalt b' := by
          rw [congrFun hbs5 b', congrFun h2_bs b']
        refine ⟨hl5, u', (congrArg Fin.val (fpHash_congr_salt
          (h₂ := (ht2.bkt_meta_bounds b' hb').1) hbs_e u')).trans hfp',
          (hkey5_eq2 b' hb' loc' hl5).trans hk', fun b₁ l₁ hm₁ => ?_, fun b₂ l₂ hm₂ => ?_⟩
        · obtain ⟨hb₁, hl₁, hne₁, _⟩ := ht2.cur_sound _ b₁ l₁ hm₁
          rw [hkey5_eq2 b₁ hb₁ l₁ (hlt_old_5 b₁ hb₁ l₁ (hbp12 ▸ hl₁) hne₁)]
          exact hd1 b₁ l₁ hm₁
        · have hsub : (extractFastMeta fl s2.mem).subStep < qEpochWhp fl.N / 2 := by
            by_contra hn; rw [(ht2.old_clear_half hn).1] at hm₂; cases hm₂
          obtain ⟨_, hb₂, hl₂, hne₂, _⟩ := (ht2.old_valid_half hsub).2.2.2.2.2.2.2 _ b₂ l₂ hm₂
          rw [hkey5_eq2 b₂ hb₂ l₂ (hlt_old_5 b₂ hb₂ l₂ (hbp12 ▸ hl₂) hne₂)]
          exact hd2 b₂ l₂ hm₂
    · intro b' hb' loc' hl'
      have hne : ¬(b' = b ∧ loc' = lastLoc) := fun ⟨hbe, hle⟩ => by
        rw [hbe, hle, hbc_b5] at hl'; omega
      have hl2 : loc' < (extractBlockPool fl.mp s2.mem).bktCount b' := by
        rw [hbp12]
        by_cases hbb : b' = b
        · rw [hbb, hbc_b5] at hl'; rw [hbb]; omega
        · rwa [hbc_ne5 b' hbb] at hl'
      obtain ⟨u', hk', htier⟩ := ht2.complete b' hb' loc' hl2 hne
      refine ⟨u', (hkey5_eq2 b' hb' loc' hl').trans hk', ?_⟩
      rcases htier with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · have hbs_e : (extractFastMeta fl s5.mem).bktSalt b' =
            (extractFastMeta fl s2.mem).bktSalt b' := by
          rw [congrFun hbs5 b', congrFun h2_bs b']
        exact Or.inr (Or.inr ((mapBTree_fpHash_congr mapBTree rfl hbs_e u').trans h3))
    · intro b' hb' hsc_nz
      by_cases hbb : b' = b
      · subst b'
        by_cases hd : fm.shadowCode b = cnt
        · exact absurd (hprom_res.1 hd).2.2 hsc_nz
        · obtain ⟨hcr_n, hci_n, hsc_n⟩ := hprom_res.2 hd
          have hsc2_nz : (extractFastMeta fl s2.mem).shadowCode b ≠ 0 := by
            rw [h2_sc]; rwa [hsc_n] at hsc_nz
          obtain ⟨hsh_lt, hnt, hbd1, hbd2, sm, hvs, heq⟩ := ht2.shadow b hb hsc2_nz
          have hsc2_eq : (extractFastMeta fl s2.mem).shadowCode b = fm.shadowCode b :=
            congrFun h2_sc b
          have hcr2_eq : (extractFastMeta fl s2.mem).curRole b = fm.curRole b := by
            rw [hrl2, hfm1]
          have hci2_eq : (extractFastMeta fl s2.mem).curIns b = fm.curIns b := by
            rw [hci2, hfm1]
          have hsi5_eq : (extractFastMeta fl s5.mem).shadowIns b =
              (extractFastMeta fl s2.mem).shadowIns b :=
            congrFun (hfm5_core.2.2.2.2.2.2.2.2.2.2.1.trans hfm4_core.2.2.2.2.2.2.2.2.2.1) b
          have hsr_lt := (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b hb).2.1).1
          rw [hbp12, hsc2_eq] at hsh_lt hbd1 hbd2
          rw [ite_eq_left ⟨rfl, rfl⟩] at hbd1 hbd2
          have hsc_lt_cnt_sub : fm.shadowCode b - 1 < bp.bktCount b - 1 := by
            have hsc_pos : 0 < fm.shadowCode b := Nat.pos_of_ne_zero (by rwa [hsc_n] at hsc_nz)
            have hne_last : fm.shadowCode b - 1 ≠ bp.bktCount b - 1 := fun he =>
              hd (by have h1 := Nat.succ_pred_eq_of_pos hsc_pos
                     have h2 := Nat.succ_pred_eq_of_pos hcnt_pos
                     exact h1.symm.trans ((congrArg Nat.succ he).trans h2))
            exact lt_of_le_of_ne (Nat.le_pred_of_lt hsh_lt) hne_last
          refine ⟨by rw [hsc_n, hbc_b5]; exact hsc_lt_cnt_sub,
            by rw [hta5, htb5, ← h2_ta, ← h2_tb]; simp only [Bool.not_eq_true',
              decide_eq_false_iff_not]; exact hnt,
            by rw [hsi5_eq, hbc_b5, hsc_n]; exact hbd1,
            by rw [hci_n, hbc_b5, hsc_n, ← hci2_eq]; exact hbd2,
            sm, by rw [hcr_n, hsi5_eq, hbt35 b hb _ hsr_lt, ← hcr2_eq]; exact hvs,
            fun fp => by rw [hsc_n, ← hsc2_eq]; exact heq fp⟩
      · obtain ⟨hcr_e, hci_e, hsc_e⟩ := hfm4_core.2.2.2.2.2.2.2.2.2.2 b' hbb
        have hsc5_e : (extractFastMeta fl s5.mem).shadowCode b' =
            (extractFastMeta fl s2.mem).shadowCode b' :=
          (congrFun hfm5_core.2.2.2.2.2.2.2.2.2.2.2.1 b').trans hsc_e
        have hsc2_nz : (extractFastMeta fl s2.mem).shadowCode b' ≠ 0 := by rwa [← hsc5_e]
        obtain ⟨hsh_lt, hnt, hbd1, hbd2, sm, hvs, heq⟩ := ht2.shadow b' hb' hsc2_nz
        have hcr5_e : (extractFastMeta fl s5.mem).curRole b' =
            (extractFastMeta fl s2.mem).curRole b' :=
          (congrFun hfm5_core.2.2.2.2.2.2.2.2.1 b').trans hcr_e
        have hci5_e : (extractFastMeta fl s5.mem).curIns b' =
            (extractFastMeta fl s2.mem).curIns b' :=
          (congrFun hfm5_core.2.2.2.2.2.2.2.2.2.1 b').trans hci_e
        have hsi5_e : (extractFastMeta fl s5.mem).shadowIns b' =
            (extractFastMeta fl s2.mem).shadowIns b' :=
          congrFun (hfm5_core.2.2.2.2.2.2.2.2.2.2.1.trans hfm4_core.2.2.2.2.2.2.2.2.2.1) b'
        have hsr_lt := (shadowRoleOf_lt_and_ne (ht2.bkt_meta_bounds b' hb').2.1).1
        rw [ite_eq_right (fun h => hbb h.2), hbp12] at hbd1 hbd2
        rw [hbp12] at hsh_lt
        refine ⟨by rw [hsc5_e, hbc_ne5 b' hbb]; exact hsh_lt,
          by rw [hta5, htb5, ← h2_ta, ← h2_tb]; simp only [Bool.not_eq_true',
            decide_eq_false_iff_not]; exact hnt,
          by rw [hsi5_e, hbc_ne5 b' hbb, hsc5_e]; exact hbd1,
          by rw [hci5_e, hbc_ne5 b' hbb, hsc5_e]; exact hbd2,
          sm, by rw [hcr5_e, hsi5_e, hbt35 b' hb' _ hsr_lt]; exact hvs,
          fun fp => by rw [hsc5_e]; exact heq fp⟩
    · rw [hta5, ← h2_ta]; exact ht2.tryAct_le
    · intro hta1
      have hta2_1 : (extractFastMeta fl s2.mem).tryAct = 1 := by rwa [hta5, ← h2_ta] at hta1
      obtain ⟨hsub2, hb_t, hs_t, htp, hsc_t, hbd, tm, hvt, htm1, htm2⟩ := ht2.try_ok hta2_1
      have htb5_eq : (extractFastMeta fl s5.mem).tryBkt = (extractFastMeta fl s2.mem).tryBkt :=
        htb5.trans h2_tb.symm
      have hts5_eq : (extractFastMeta fl s5.mem).trySalt = (extractFastMeta fl s2.mem).trySalt :=
        hfm5_core.2.2.2.2.2.1.trans hfm4_core.2.2.2.2.2.1
      have hti5_eq : (extractFastMeta fl s5.mem).tryIns = (extractFastMeta fl s2.mem).tryIns :=
        hfm5_core.2.2.2.2.2.2.1.trans hfm4_core.2.2.2.2.2.2.2.1
      have htp4_eq : (extractFastMeta fl s4.mem).tryPos = (extractFastMeta fl s2.mem).tryPos :=
        hfm4_core.2.2.2.2.2.2.1
      have htp5_eq : (extractFastMeta fl s5.mem).tryPos =
          if (extractFastMeta fl s2.mem).tryBkt = b ∧
              (extractFastMeta fl s2.mem).tryPos = cnt then
            lastLoc else (extractFastMeta fl s2.mem).tryPos := by
        rw [hfm5_core.2.2.2.2.2.2.2.2.2.2.2.2, hfm4_core.2.2.2.1, hfm4_core.2.2.2.2.1, htp4_eq]
        by_cases hc : (extractFastMeta fl s2.mem).tryBkt = b ∧
            (extractFastMeta fl s2.mem).tryPos = cnt
        · rw [ite_eq_left ⟨hta2_1, hc.1, hc.2⟩, ite_eq_left hc]
        · rw [ite_eq_right (fun h => hc ⟨h.2.1, h.2.2⟩), ite_eq_right hc]
      have hsc_t_5 : (extractFastMeta fl s5.mem).shadowCode (extractFastMeta fl s2.mem).tryBkt =
          0 := by
        by_cases hbb : (extractFastMeta fl s2.mem).tryBkt = b
        · rw [hbb] at hsc_t ⊢
          have hne_c : fm.shadowCode b ≠ cnt := by
            have := congrFun h2_sc b; omega
          rw [(hprom_res.2 hne_c).2.2, ← congrFun h2_sc b]; exact hsc_t
        · exact (congrFun hfm5_core.2.2.2.2.2.2.2.2.2.2.2.1 _).trans
            ((hfm4_core.2.2.2.2.2.2.2.2.2.2 _ hbb).2.2.trans hsc_t)
      have hcr_t_5 : (extractFastMeta fl s5.mem).curRole (extractFastMeta fl s2.mem).tryBkt =
          (extractFastMeta fl s2.mem).curRole (extractFastMeta fl s2.mem).tryBkt := by
        by_cases hbb : (extractFastMeta fl s2.mem).tryBkt = b
        · rw [hbb] at hsc_t ⊢
          have hne_c : fm.shadowCode b ≠ cnt := by have := congrFun h2_sc b; omega
          rw [(hprom_res.2 hne_c).1, congrFun hrl2 b,
            congrFun (congrArg FastEpochMeta.curRole hfm1) b]
        · exact (congrFun hfm5_core.2.2.2.2.2.2.2.2.1 _).trans
            (hfm4_core.2.2.2.2.2.2.2.2.2.2 _ hbb).1
      have htp_le_5 : (extractFastMeta fl s5.mem).tryPos ≤
          (extractBlockPool fl.mp s5.mem).bktCount (extractFastMeta fl s2.mem).tryBkt := by
        rw [htp5_eq]
        by_cases hbb : (extractFastMeta fl s2.mem).tryBkt = b
        · rw [hbb, hbc_b5]; rw [hbb, hbp12] at htp
          split_ifs with hc
          · exact le_rfl
          · have hne_cnt : (extractFastMeta fl s2.mem).tryPos ≠ cnt := fun he => hc ⟨rfl, he⟩
            exact Nat.le_pred_of_lt (lt_of_le_of_ne htp hne_cnt)
        · rw [ite_eq_right (fun h => hbb h.1), hbc_ne5 _ hbb]
          rwa [hbp12] at htp
      have hbd_5 : 4 * (extractFastMeta fl s5.mem).tryIns +
          5 * ((extractBlockPool fl.mp s5.mem).bktCount (extractFastMeta fl s2.mem).tryBkt -
            (extractFastMeta fl s5.mem).tryPos) ≤ 20 * slabScale fl.N ^ 12 := by
        rw [hbp12] at hbd
        rw [hti5_eq, htp5_eq]
        by_cases hbb : (extractFastMeta fl s2.mem).tryBkt = b
        · rw [ite_eq_left ⟨rfl, hbb⟩, hbb] at hbd
          rw [hbb, hbc_b5]
          split_ifs with hc
          · rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
            exact le_trans (Nat.le_add_right _ _) hbd
          · exact hbd
        · rw [ite_eq_right (fun h => hbb h.2)] at hbd
          rw [ite_eq_right (fun h => hbb h.1), hbc_ne5 _ hbb]
          exact hbd
      have htr_lt := (tryRoleOf_lt_and_ne (ht2.bkt_meta_bounds _ hb_t).2.1).1
      have hbs_t_eq : (extractFastMeta fl s5.mem).bktSalt (extractFastMeta fl s2.mem).tryBkt =
          (extractFastMeta fl s2.mem).bktSalt (extractFastMeta fl s2.mem).tryBkt := by
        rw [congrFun hbs5 _, congrFun h2_bs _]
      refine ⟨by rw [hss5, ← h2_ss]; exact hsub2,
        by rw [htb5_eq]; exact hb_t,
        by rw [hts5_eq]; exact hs_t,
        by rw [htb5_eq]; exact htp_le_5,
        by rw [htb5_eq]; exact hsc_t_5,
        by rw [htb5_eq]; exact hbd_5,
        tm, ?_, ?_, ?_⟩
      · rw [htb5_eq, hti5_eq, hcr_t_5, hbt35 _ hb_t _ htr_lt]; exact hvt
      · intro fp' loc' hm
        obtain ⟨hlt, hne, u', hk', hmb', hf'⟩ := htm1 fp' loc' hm
        have hlt5 : loc' < (extractFastMeta fl s5.mem).tryPos := by
          rw [htp5_eq]; split_ifs with hc
          · have : loc' ≠ lastLoc := fun he => hne ⟨hc.1, he⟩
            rw [hc.2] at hlt; omega
          · exact hlt
        have hlb5 : loc' < (extractBlockPool fl.mp s5.mem).bktCount
            (extractFastMeta fl s2.mem).tryBkt := lt_of_lt_of_le hlt5 htp_le_5
        refine ⟨hlt5, u', by rw [htb5_eq]; exact (hkey5_eq2 _ hb_t loc' hlb5).trans hk',
          (mapBTree_fpHash_congr mapBTree htb5_eq (by rw [htb5_eq, hbs_t_eq]) u').trans hmb',
          (congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts5_eq u')).trans hf'⟩
      · intro loc' hlt' u' hk' hmb'
        have hlt2 : loc' < (extractFastMeta fl s2.mem).tryPos := by
          rw [htp5_eq] at hlt'; split_ifs at hlt' with hc
          · rw [hc.2]; omega
          · exact hlt'
        have hlb5 : loc' < (extractBlockPool fl.mp s5.mem).bktCount
            (extractFastMeta fl s2.mem).tryBkt := lt_of_lt_of_le hlt' htp_le_5
        have hne2 : ¬((extractFastMeta fl s2.mem).tryBkt = b ∧ loc' = lastLoc) := by
          rintro ⟨hbe, hle⟩; rw [hbe, hle, hbc_b5] at hlb5; exact Nat.lt_irrefl _ hlb5
        rw [congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts5_eq u')]
        exact htm2 loc' hlt2 hne2 u'
          ((hkey5_eq2 _ hb_t loc' hlb5).symm.trans (htb5_eq ▸ hk'))
          ((mapBTree_fpHash_congr mapBTree htb5_eq (by rw [htb5_eq, hbs_t_eq]) u').symm.trans
            hmb')
  have htr_o2_eq : extractBufTrie (fl.trieL (1 - fm.curBufRole)) s5.mem =
      extractBufTrie (fl.trieL (1 - fm.curBufRole)) s2.mem := htr35 _ hold_lt
  have hcr1 : (extractFastMeta fl s1.mem).curBufRole = fm.curBufRole :=
    congrArg FastEpochMeta.curBufRole hfm1
  have hsi_b5 : (extractFastMeta fl s5.mem).shadowIns b =
      (extractFastMeta fl s2.mem).shadowIns b :=
    congrFun (hfm5_core.2.2.2.2.2.2.2.2.2.2.1.trans hfm4_core.2.2.2.2.2.2.2.2.2.1) b
  refine ⟨hfr5.trans (hfr4.trans (hfr3.trans (hfr2.trans hfr1))),
    by linarith only [hcost_tot], hinv5,
    hns5, hbc_b5, hbc_ne5, hkey5_raw, hof_tot, hpart_tot,
    by rw [htr_o2_eq]; rw [hcr1] at hia2; exact hia2.trans hia1,
    fun id b' l' hchk => by
      rw [htr_o2_eq] at hchk
      rw [hcr1] at hchk2
      rcases hchk2 id b' l' hchk with h | ⟨hbe, hle, hlt, h0⟩
      · refine Or.inl ⟨hchk1 id b' l' h, fun hsub => ?_⟩
        rcases ht1 with ⟨_, mo1, _, ht1w⟩
        have hsub1 : (extractFastMeta fl s1.mem).subStep < qEpochWhp fl.N / 2 := by
          rw [hfm1]; exact hsub
        obtain ⟨hvo1, _, _, _, _, _, _, hsnd1⟩ := ht1w.old_valid_half hsub1
        obtain ⟨_, rk1, _, _, hmo1⟩ := hvo1.checkSlot_some (by rwa [hcr1])
        exact (hsnd1 rk1 b' l' hmo1).2.2.2.1
      · exact Or.inr ⟨hbe, hle, hlt, hchk1 id b lastLoc h0⟩,
    hcr5, hss5, hdp5, hta5, htb5, hbs5,
    fun b' hne => ?_,
    fun hd => (hprom_res.1 hd).2.2,
    fun hn => ?_,
    ?_⟩
  · obtain ⟨hcr_e, hci_e, hsc_e⟩ := hfm4_core.2.2.2.2.2.2.2.2.2.2 b' hne
    exact ⟨(congrFun hfm5_core.2.2.2.2.2.2.2.2.1 b').trans
      (hcr_e.trans ((congrFun hrl2 b').trans (congrFun (congrArg FastEpochMeta.curRole hfm1) b'))),
      (congrFun hfm5_core.2.2.2.2.2.2.2.2.2.1 b').trans
      (hci_e.trans ((congrFun hci2 b').trans (congrFun (congrArg FastEpochMeta.curIns hfm1) b'))),
      (congrFun (hfm5_core.2.2.2.2.2.2.2.2.2.2.1.trans
        hfm4_core.2.2.2.2.2.2.2.2.2.1) b').trans
      ((hsi_ne2 b' hne).trans (congrFun (congrArg FastEpochMeta.shadowIns hfm1) b')),
      (congrFun hfm5_core.2.2.2.2.2.2.2.2.2.2.2.1 b').trans
      (hsc_e.trans ((congrFun hsc2 b').trans
        (congrFun (congrArg FastEpochMeta.shadowCode hfm1) b')))⟩
  · obtain ⟨_, hci_n, hsc_n⟩ := hprom_res.2 hn
    refine ⟨hsc_n, hci_n, by rw [hsi_b5]; rw [hfm1] at hsi_le2; exact hsi_le2,
      fun h0 => by
        rw [hsi_b5]; rw [hfm1] at hsi_noop2
        apply hsi_noop2
        rw [hsc2, hfm1]; exact h0⟩
  · have htp4_eq : (extractFastMeta fl s4.mem).tryPos = (extractFastMeta fl s2.mem).tryPos :=
      hfm4_core.2.2.2.2.2.2.1
    have hts5_eq : (extractFastMeta fl s5.mem).trySalt = (extractFastMeta fl s2.mem).trySalt :=
      hfm5_core.2.2.2.2.2.1.trans hfm4_core.2.2.2.2.2.1
    have hti5_eq : (extractFastMeta fl s5.mem).tryIns = (extractFastMeta fl s2.mem).tryIns :=
      hfm5_core.2.2.2.2.2.2.1.trans hfm4_core.2.2.2.2.2.2.2.1
    have hta4_eq : (extractFastMeta fl s4.mem).tryAct = fm.tryAct :=
      hfm4_core.2.2.2.1.trans (hta2.trans (congrArg FastEpochMeta.tryAct hfm1))
    have htb4_eq : (extractFastMeta fl s4.mem).tryBkt = fm.tryBkt :=
      hfm4_core.2.2.2.2.1.trans (htb2.trans (congrArg FastEpochMeta.tryBkt hfm1))
    rcases htry_d2 with ⟨hsa, hpo⟩ | ⟨hact, htb, hdl, hle, hts', htp', hti', hs_t, wLoc, wKey,
        uL', hwl, hwn, hwk_ne, hwk, hul, hfp_eq⟩
    · left
      rw [hfm1] at hsa hpo
      refine ⟨hts5_eq.trans hsa, ?_⟩
      rw [hfm5_core.2.2.2.2.2.2.2.2.2.2.2.2, hta4_eq, htb4_eq, htp4_eq, hpo]
    · right
      rw [hfm1] at hact htb hdl hle hts'
      have hs_t0 : fm.trySalt < sMaxWhp fl.c fl.N := by rwa [hfm1] at hs_t
      have htp5_0 : (extractFastMeta fl s5.mem).tryPos = 0 := by
        rw [hfm5_core.2.2.2.2.2.2.2.2.2.2.2.2, htp4_eq, htp']
        rw [ite_eq_right (fun h => by omega)]
      refine ⟨hact, htb, hdl, hle, hts5_eq.trans hts', htp5_0, hti5_eq.trans hti',
        hs_t0, wLoc, wKey, uL', hwl, hwn, hwk_ne,
        (hkey1_eq b hb wLoc (lt_trans hwl hlast_lt)).symm.trans hwk,
        (hkey1_eq b hb lastLoc hlast_lt).symm.trans hul, ?_⟩
      exact (fpHash_congr_salt (congrArg FastEpochMeta.trySalt hfm1).symm wKey).trans
        (hfp_eq.trans (fpHash_congr_salt (congrArg FastEpochMeta.trySalt hfm1) uL'))

/-- Under `GoodEpochSeeds win seeds`, `fastRemoveAtProg` preserves `FastSubEpochGood` (without
increasing `drainPotential`, using `4 * (+1) - 5 = -1 ≤ 0` for `shadow` compaction and the
collision witness on `advanceTrySaltProg`). -/
theorem fastRemoveAtProg_good {slackCur slackPot : ℕ} {fl : FastEpochLayout} {w b delLoc : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {hgood : GoodEpochSeeds win seeds}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State} (u : Fin fl.U)
    (hslack : slackCur ≤ 1)
    (hv : fl.Valid w s.frontier)
    (hg : FastSubEpochGood slackCur slackPot 0 win e seeds hgood s.mem s_abs)
    (hb : b < numBucketsWhp fl.N)
    (hdel : delLoc < (extractBlockPool fl.mp s.mem).bktCount b)
    (hk_u : fastKeyAt fl seeds.bkt s.mem b delLoc = u.val) :
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    let s' := (Memory.spec 0).clientState s (fastRemoveAtProg ((fl.pBase, b), (delLoc, u.val)))
    FastSubEpochGood slackCur slackPot slack' win e seeds hgood s'.mem
      (Function.update s_abs u none) := by
  dsimp only
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  set s' := (Memory.spec 0).clientState s (fastRemoveAtProg ((fl.pBase, b), (delLoc, u.val)))
  set fm' := extractFastMeta fl s'.mem
  set bp' := extractBlockPool fl.mp s'.mem
  obtain ⟨_, _, hinv', _, hbc_b, hbc_ne, hkey', _, _, hia', hchk',
    hcr', hss', hdp', hta', htb', _, hoth', hsh_prom, hsh_stay, htry'⟩ :=
    fastRemoveAtProg_spec u hslack hv hg.inv hb hdel hk_u
  have hslot_map : fm.subStep < qEpochWhp fl.N / 2 →
      ∀ id b' loc',
        bufCheckSlot (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem) id = some (b', loc') →
        b' < numBucketsWhp fl.N → loc' < bp'.bktCount b' →
        ∃ loc0 < bp.bktCount b',
          bufCheckSlot (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem) id =
            some (b', loc0) ∧
          fastKeyAt fl seeds.bkt s'.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc0 := by
    intro hsub id b' loc' hchk hb' hl'
    rw [hcr'] at hchk
    rcases hchk' id b' loc' hchk with ⟨h0, hne⟩ | ⟨hbe, hle, hlt_last, h0⟩
    · have hl0 : loc' < bp.bktCount b' := by
        by_cases hbb : b' = b
        · rw [hbb, hbc_b] at hl'; rw [hbb]; exact lt_of_lt_of_le hl' (Nat.sub_le _ 1)
        · rwa [hbc_ne b' hbb] at hl'
      refine ⟨loc', hl0, h0, ?_⟩
      rw [hkey' b' hb' loc' hl', ite_eq_right (hne hsub)]
    · refine ⟨bp.bktCount b - 1, by rw [hbe]; exact Nat.sub_lt (Nat.zero_lt_of_lt hdel) Nat.one_pos,
        hbe ▸ h0, ?_⟩
      rw [hkey' b' hb' loc' hl', ite_eq_left ⟨hbe, hle⟩, hbe]
  have hia_eq : (extractBufTrie (fl.trieL (1 - fm'.curBufRole)) s'.mem).itemAlloc =
      (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem).itemAlloc := by
    rw [hcr']; exact hia'
  have hstar_ne_of_col : fm.tryAct = 1 → fm.tryBkt = b →
      ∀ (hs_t : fm.trySalt < sMaxWhp fl.c fl.N) (wLoc : ℕ) (wKey uLast : Fin fl.U),
        wLoc < bp.bktCount b - 1 → wKey ≠ uLast →
        fastKeyAt fl seeds.bkt s.mem b wLoc = wKey.val →
        fastKeyAt fl seeds.bkt s.mem b (bp.bktCount b - 1) = uLast.val →
        fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ wKey =
          fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ uLast →
        fm.trySalt < goodSaltVal hgood e b ∧
          fm.trySalt + 1 < sMaxWhp fl.c fl.N := by
    intro hta0 htb_b hs_t wLoc wKey uLast hwl hw_ne hwk hul hfp_eq
    have hstar_spec : ∃ (hs : goodSaltVal hgood e b < sMaxWhp fl.c fl.N),
        ∀ u₁ ∈ win.subUnions e, ∀ v₁ ∈ win.subUnions e,
          epochBucket fl.c fl.U fl.N seeds.bkt u₁ = b →
          epochBucket fl.c fl.U fl.N seeds.bkt v₁ = b → u₁ ≠ v₁ →
            fpHash fl.c fl.U fl.N seeds.fp ⟨goodSaltVal hgood e b, hs⟩ u₁ ≠
              fpHash fl.c fl.U fl.N seeds.fp ⟨goodSaltVal hgood e b, hs⟩ v₁ := by
      unfold goodSaltVal; rw [dite_eq_left hb]
      exact ⟨(hgood.2.2.1 e b hb).choose.isLt, (hgood.2.2.1 e b hb).choose_spec⟩
    obtain ⟨hs_star, hcol_free⟩ := hstar_spec
    have hcnt_pos : 0 < bp.bktCount b := Nat.zero_lt_of_lt hdel
    obtain ⟨w₀, v_w, hww, _, hb_w, _, hsw⟩ :=
      hg.inv.bktSlot_refines hb (lt_of_lt_of_le hwl (Nat.sub_le _ 1))
    have hw_e : w₀ = wKey := Fin.ext (hww.trans hwk)
    obtain ⟨u₀, v_u, huu, _, hb_u, _, hsu⟩ :=
      hg.inv.bktSlot_refines hb (Nat.sub_lt hcnt_pos Nat.one_pos)
    have hu_e : u₀ = uLast := Fin.ext (huu.trans hul)
    have hw_in : wKey ∈ win.subUnions e := hg.live_sub wKey (by
      rw [← hw_e, hsw]; exact Option.some_ne_none _)
    have hu_in : uLast ∈ win.subUnions e := hg.live_sub uLast (by
      rw [← hu_e, hsu]; exact Option.some_ne_none _)
    have hne_star : fm.trySalt ≠ goodSaltVal hgood e b := fun heq => by
      have h1 := hcol_free wKey hw_in uLast hu_in (hw_e ▸ hb_w) (hu_e ▸ hb_u) hw_ne
      have h2 : fpHash fl.c fl.U fl.N seeds.fp ⟨goodSaltVal hgood e b, hs_star⟩ wKey =
          fpHash fl.c fl.U fl.N seeds.fp ⟨goodSaltVal hgood e b, hs_star⟩ uLast :=
        (fpHash_congr_salt heq.symm wKey).trans
          (hfp_eq.trans (fpHash_congr_salt heq uLast))
      exact h1 h2
    have hle_b : fm.trySalt ≤ goodSaltVal hgood e b := htb_b ▸ hg.trySalt_le hta0
    have hlt_b : fm.trySalt < goodSaltVal hgood e b := lt_of_le_of_ne hle_b hne_star
    exact ⟨hlt_b, Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hlt_b) hs_star⟩
  have hts_le : fm'.tryAct = 1 → fm'.trySalt ≤ goodSaltVal hgood e fm'.tryBkt := by
    intro hta1
    have hta0 : fm.tryAct = 1 := hta'.symm.trans hta1
    rcases htry' with ⟨hsa, _⟩ | ⟨_, htb_b, _, _, hts_eq, _, _, hs_t, wLoc, wKey, uLast,
        hwl, _, hw_ne, hwk, hul, hfp_eq⟩
    · rw [htb', hsa]; exact hg.trySalt_le hta0
    · obtain ⟨hlt_b, hlt_smax⟩ :=
        hstar_ne_of_col hta0 htb_b hs_t wLoc wKey uLast hwl hw_ne hwk hul hfp_eq
      rw [htb', htb_b, hts_eq, ite_eq_left hlt_smax]
      exact Nat.succ_le_of_lt hlt_b
  refine
    { inv := hinv'
      live_sub := fun u' hu' => by
        by_cases he : u' = u
        · rw [he, Function.update_self] at hu'; exact absurd rfl hu'
        · rw [Function.update_of_ne he] at hu'; exact hg.live_sub u' hu'
      old_sub := fun hsub id b' loc' u' hchk hb' hl' hk' => by
        have hsub0 : fm.subStep < qEpochWhp fl.N / 2 := hss' ▸ hsub
        obtain ⟨loc0, hl0, hchk0, hkeq⟩ := hslot_map hsub0 id b' loc' hchk hb' hl'
        exact hg.old_sub hsub0 id b' loc0 u' hchk0 hb' hl0 (hkeq.symm.trans hk')
      try_match := fun hta1 hdp_lt b' loc' hchk => by
        have hta0 : fm.tryAct = 1 := hta'.symm.trans hta1
        have hdp0 : fm.drainPos <
            (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem).itemAlloc := by
          rwa [hdp', hia_eq] at hdp_lt
        rw [hdp', hcr'] at hchk
        rw [htb']
        rcases hchk' fm.drainPos b' loc' hchk with ⟨h0, _⟩ | ⟨hbe, _, _, h0⟩
        · exact hg.try_match hta0 hdp0 b' loc' h0
        · rw [hbe]; exact hg.try_match hta0 hdp0 b (bp.bktCount b - 1) h0
      trySalt_le := hts_le
      pot_le := fun hsub => ?_ }
  have hsub0 : fm.subStep < qEpochWhp fl.N / 2 := hss' ▸ hsub
  have hbad_imp : ∀ id, isBadOldSlot win e seeds s'.mem id → isBadOldSlot win e seeds s.mem id :=
    fun id ⟨b', loc', u', hchk, hb', hl', hk', hcol⟩ => by
      obtain ⟨loc0, hl0, hchk0, hkeq⟩ := hslot_map hsub0 id b' loc' hchk hb' hl'
      exact ⟨b', loc0, u', hchk0, hb', hl0, hkeq.symm.trans hk', hcol⟩
  have hnb_mono : ∀ k, nBadFrom win e seeds s'.mem k ≤ nBadFrom win e seeds s.mem k := fun k =>
    nBadFrom_mono_of_imp hia_eq fun id _ hb => hbad_imp id hb
  have hpot_le : drainPotential win e seeds hgood s'.mem ≤
      drainPotential win e seeds hgood s.mem := by
    unfold drainPotential; dsimp only
    rw [hia_eq, hdp', hta', htb']
    by_cases hta1 : fm.tryAct = 1
    · rw [ite_eq_left hta1, ite_eq_left hta1]
      have hnb := hnb_mono (fm.drainPos + 1)
      have hterm : (goodSaltVal hgood e fm.tryBkt - fm'.trySalt) * (capMaxWhp fl.N + 2) +
            (bp'.bktCount fm.tryBkt - fm'.tryPos) ≤
          (goodSaltVal hgood e fm.tryBkt - fm.trySalt) * (capMaxWhp fl.N + 2) +
            (bp.bktCount fm.tryBkt - fm.tryPos) := by
        rcases htry' with ⟨hsa, hpo⟩ | ⟨_, htb_b, _, _, hts_eq, htp_eq, _, hs_t, wLoc, wKey,
            uLast, hwl, _, hw_ne, hwk, hul, hfp_eq⟩
        · rw [hsa, hpo]
          by_cases hbb : fm.tryBkt = b
          · rw [hbb, hbc_b]
            by_cases hpc : fm.tryPos = bp.bktCount b
            · rw [ite_eq_left ⟨hta1, rfl, hpc⟩]
              have h0 : bp.bktCount b - 1 - (bp.bktCount b - 1) = 0 := Nat.sub_self _
              have hle : bp.bktCount b - 1 - (bp.bktCount b - 1) ≤ bp.bktCount b - fm.tryPos :=
                h0 ▸ Nat.zero_le _
              exact Nat.add_le_add_left hle _
            · rw [ite_eq_right (fun h => hpc h.2.2)]
              exact Nat.add_le_add_left
                (Nat.sub_le_sub_right (Nat.sub_le (bp.bktCount b) 1) fm.tryPos) _
          · rw [hbc_ne _ hbb, ite_eq_right (fun h => hbb h.2.1)]
        · have hcnt_le : bp.bktCount b ≤ capMaxWhp fl.N := hg.inv.bkt_le_capMax b hb
          obtain ⟨hlt_sm, hlt_sm1⟩ :=
            hstar_ne_of_col hta1 htb_b hs_t wLoc wKey uLast hwl hw_ne hwk hul hfp_eq
          rw [htb_b, hts_eq, ite_eq_left hlt_sm1, htp_eq, hbc_b, Nat.sub_zero]
          have hmul : (goodSaltVal hgood e b - ((extractFastMeta fl s.mem).trySalt + 1)) *
                (capMaxWhp fl.N + 2) + (capMaxWhp fl.N + 2) =
              (goodSaltVal hgood e b - (extractFastMeta fl s.mem).trySalt) *
                (capMaxWhp fl.N + 2) := by
            have hd : goodSaltVal hgood e b - (extractFastMeta fl s.mem).trySalt =
                (goodSaltVal hgood e b - ((extractFastMeta fl s.mem).trySalt + 1)) + 1 := by
              have hlt' : (extractFastMeta fl s.mem).trySalt < goodSaltVal hgood e b := hlt_sm
              omega
            rw [hd, Nat.add_mul, Nat.one_mul]
          have hsub_le : bp.bktCount b - 1 ≤ capMaxWhp fl.N + 2 :=
            (Nat.sub_le _ 1).trans (hcnt_le.trans (Nat.le_add_right _ 2))
          exact (Nat.add_le_add_left hsub_le _).trans
            (hmul ▸ Nat.le_add_right _ _)
      have hnb1 : (sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1) *
            nBadFrom win e seeds s'.mem (fm.drainPos + 1) ≤
          (sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1) *
            nBadFrom win e seeds s.mem (fm.drainPos + 1) := Nat.mul_le_mul_left _ hnb
      have hnb2 : 4 * slabScale fl.N ^ 12 * nBadFrom win e seeds s'.mem (fm.drainPos + 1) ≤
          4 * slabScale fl.N ^ 12 * nBadFrom win e seeds s.mem (fm.drainPos + 1) :=
        Nat.mul_le_mul_left _ hnb
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left hnb1 _) hnb2)
        (Nat.add_le_add_right hterm 1)
    · rw [ite_eq_right hta1, ite_eq_right hta1]
      have hnb0 := hnb_mono fm.drainPos
      have hnb1 := hnb_mono (fm.drainPos + 1)
      have hsh_le : shTerm fl win e seeds s'.mem ≤ shTerm fl win e seeds s.mem := by
        classical
        unfold shTerm; dsimp only; rw [hdp', hcr']
        by_cases hbd' : isBadOldSlot win e seeds s'.mem fm.drainPos
        · have hbd : isBadOldSlot win e seeds s.mem fm.drainPos := hbad_imp _ hbd'
          rw [ite_eq_left hbd', ite_eq_left hbd]
          cases hck' : bufCheckSlot (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s'.mem)
              fm.drainPos with
          | none => exact Nat.zero_le _
          | some p' =>
            rcases p' with ⟨b', loc'⟩
            have hck_b : ∃ loc0, bufCheckSlot (extractBufTrie (fl.trieL (1 - fm.curBufRole))
                s.mem) fm.drainPos = some (b', loc0) := by
              rcases hchk' fm.drainPos b' loc' hck' with ⟨h0, _⟩ | ⟨hbe, _, _, h0⟩
              · exact ⟨loc', h0⟩
              · exact ⟨bp.bktCount b - 1, hbe ▸ h0⟩
            obtain ⟨loc0, hck0⟩ := hck_b
            rw [hck0]; dsimp only
            by_cases hbb : b' = b
            · subst b'
              unfold shCost shSlack; dsimp only
              by_cases hsc0 : fm.shadowCode b = 0
              · have hne_c : fm.shadowCode b ≠ bp.bktCount b := by omega
                have hst := (hsh_stay hne_c).1
                rw [hst, ite_eq_left hsc0, ite_eq_left hsc0]
              · by_cases hdone : fm.shadowCode b = bp.bktCount b
                · rw [ite_eq_left (hsh_prom hdone)]; exact Nat.zero_le _
                · obtain ⟨hsc_eq, hci_eq, hsi_le, _⟩ := hsh_stay hdone
                  rw [hsc_eq, ite_eq_right hsc0, ite_eq_right hsc0, hci_eq, hbc_b]
                  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsh_all, _, _⟩ := hg.inv.tiers
                  have hsh_lt : fm.shadowCode b - 1 < bp.bktCount b :=
                    (hsh_all b hb hsc0).1
                  have hlt_sub : fm.shadowCode b - 1 < bp.bktCount b - 1 := by
                    have hpos_sc : 0 < fm.shadowCode b := Nat.pos_of_ne_zero hsc0
                    have hpos_bc : 0 < bp.bktCount b := Nat.zero_lt_of_lt hdel
                    have hne_p : fm.shadowCode b - 1 ≠ bp.bktCount b - 1 := fun he =>
                      hdone ((Nat.succ_pred_eq_of_pos hpos_sc).symm.trans
                        ((congrArg Nat.succ he).trans (Nat.succ_pred_eq_of_pos hpos_bc)))
                    exact lt_of_le_of_ne (Nat.le_pred_of_lt hsh_lt) hne_p
                  have h1_sub : bp.bktCount b - (fm.shadowCode b - 1) =
                      (bp.bktCount b - 1 - (fm.shadowCode b - 1)) + 1 := by
                    have h1 : fm.shadowCode b - 1 < bp.bktCount b := hsh_lt
                    have h2 : fm.shadowCode b - 1 ≤ bp.bktCount b - 1 := Nat.le_of_lt hlt_sub
                    omega
                  have ha : 4 * (extractFastMeta fl s'.mem).shadowIns b +
                        5 * (bp.bktCount b - 1 - (fm.shadowCode b - 1)) ≤
                      4 * (extractFastMeta fl s.mem).shadowIns b +
                        5 * (bp.bktCount b - (fm.shadowCode b - 1)) := by
                    have hsle : (extractFastMeta fl s'.mem).shadowIns b ≤
                        (extractFastMeta fl s.mem).shadowIns b + 1 := hsi_le
                    rw [h1_sub]; omega
                  have hb_i : 8 * ((extractFastMeta fl s.mem).curIns b - 6 * slabScale fl.N ^ 12) +
                        (bp.bktCount b - 1 - (fm.shadowCode b - 1)) ≤
                      8 * ((extractFastMeta fl s.mem).curIns b - 6 * slabScale fl.N ^ 12) +
                        (bp.bktCount b - (fm.shadowCode b - 1)) := by
                    rw [h1_sub]; omega
                  exact Nat.sub_le_sub_left (le_min
                    (min_le_of_left_le (Nat.sub_le_sub_left ha _))
                    (min_le_of_right_le (Nat.sub_le_sub_left hb_i _))) _
            · obtain ⟨_, hci_e, hsi_e, hsc_e⟩ := hoth' b' hbb
              unfold shCost shSlack; dsimp only
              rw [hsc_e, hci_e, hsi_e, hbc_ne b' hbb]
        · rw [ite_eq_right hbd']; exact Nat.zero_le _
      have hm1 : (sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1) *
            nBadFrom win e seeds s'.mem fm.drainPos ≤
          (sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1) *
            nBadFrom win e seeds s.mem fm.drainPos := Nat.mul_le_mul_left _ hnb0
      have hm2 : 4 * slabScale fl.N ^ 12 * nBadFrom win e seeds s'.mem (fm.drainPos + 1) ≤
          4 * slabScale fl.N ^ 12 * nBadFrom win e seeds s.mem (fm.drainPos + 1) :=
        Nat.mul_le_mul_left _ hnb1
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left hm1 _) hm2) hsh_le
  rw [hss']
  exact hpot_le.trans (hg.pot_le hsub0)

/-! ## Section 4: Migration `popAny` (`fastPopAnyProg`) Specification -/

/-- Unconditional specification of `fastPopAnyProg` on a non-empty large fast epoch
(`0 < (extractBlockPool fl.mp s.mem).nSide`): returns `(u.val, v.val)` with `s_abs u = some v`,
decrements `nSide` by `1`, and preserves `FastEpochInvGen` unconditionally on **100%** of hash seeds
without calling `advanceSubEpochProg` (`memoryCost ≤ fastPopAnyCost fl.c`). -/
theorem fastPopAnyProg_spec {slackCur : ℕ} {fl : FastEpochLayout} {w : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State}
    (hslack : slackCur ≤ 1)
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl 0 seeds s.mem s_abs)
    (hpos : 0 < (extractBlockPool fl.mp s.mem).nSide) :
    let res := (Memory.spec 0).clientResult s (fastPopAnyProg fl.pBase)
    let s' := (Memory.spec 0).clientState s (fastPopAnyProg fl.pBase)
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    ∃ (u : Fin fl.U) (v : Fin fl.V),
      res = (u.val, v.val) ∧
      s_abs u = some v ∧
      s'.frontier = s.frontier ∧
      memoryCost (fastPopAnyProg fl.pBase) s ≤ fastPopAnyCost fl.c ∧
      FastEpochInvGen slackCur fl slack' seeds s'.mem (Function.update s_abs u none) ∧
      (extractBlockPool fl.mp s'.mem).nSide = (extractBlockPool fl.mp s.mem).nSide - 1 ∧
      (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
      (fl.io.usePaged ≠ 0 →
        (extractPagePair fl.io.pgL s'.mem).virtLen fl.io.partner.side =
          (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
        (extractPagePair fl.io.pgL s'.mem).totalItems =
          (extractPagePair fl.io.pgL s.mem).totalItems - 1 ∧
        ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
          slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  dsimp only
  have hr := hinv.ready hv rfl
  set bp := extractBlockPool fl.mp s.mem
  obtain ⟨hco, hres_o, hb_lt, hl_lt⟩ := fastBpOwnerOfZeroProg_spec hr hinv.bp_inv.1.core hpos
  set b := ((Memory.spec 0).clientResult s (fastBpOwnerOfZeroProg fl.pBase)).1
  have hb : b < numBucketsWhp fl.N := hb_lt
  have hcnt_pos : 0 < bp.bktCount b := Nat.zero_lt_of_lt hl_lt
  set lastLoc := bp.bktCount b - 1
  have hlast_lt : lastLoc < bp.bktCount b := by omega
  obtain ⟨hcnt_r, hcnt_c⟩ := fastReadBktCntProg_spec hr hinv.bp_inv.1.core hb
  obtain ⟨_, hread_r, hread_c⟩ := fastBpReadAtProg_spec hr hinv.bp_inv hb hlast_lt
  obtain ⟨u, v, hu, hv_eq, _, hq_u, hs_u⟩ := hinv.bktSlot_refines hb hlast_lt
  have hq_lt : (bpPairAt fl.bpL s.mem b lastLoc).1 < 2 ^ quotBitsWhp fl.U fl.N :=
    hq_u ▸ keyQuotient_bWhp_lt hv.N_le_U u
  obtain ⟨hrec_r, hrec_c⟩ := fastFeistelReconProg_spec hr hq_lt hinv.seed_bkt (bkt := b)
  have hrec_val : (Memory.spec 0).clientResult s
      (fastFeistelReconProg (fl.pBase, (b, (bpPairAt fl.bpL s.mem b lastLoc).1))) = u.val := by
    rw [hrec_r]; exact hu.symm
  obtain ⟨hfr', hcost', hinv', hns', _, _, _, hof', hpart', _⟩ :=
    fastRemoveAtProg_spec u hslack hv hinv hb hlast_lt hu.symm
  have hres_eq : (Memory.spec 0).clientResult s (fastPopAnyProg fl.pBase) = (u.val, v.val) := by
    unfold fastPopAnyProg
    rw [prog_clientResult_bind, clientState_fastBpOwnerOfZeroProg, pure_bind,
      prog_clientResult_bind, clientState_fastReadBktCntProg, hcnt_r, ite_eq_left hcnt_pos,
      pure_bind, prog_clientResult_bind, clientState_fastBpReadAtProg, hread_r,
      prog_clientResult_bind, clientState_fastFeistelReconProg, hrec_val,
      prog_clientResult_bind, prog_clientResult_pure, hv_eq]
  have hst_eq : (Memory.spec 0).clientState s (fastPopAnyProg fl.pBase) =
      (Memory.spec 0).clientState s (fastRemoveAtProg ((fl.pBase, b), (lastLoc, u.val))) := by
    unfold fastPopAnyProg
    rw [StateTransitionSpec.clientState_bind, clientState_fastBpOwnerOfZeroProg, pure_bind,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktCntProg, hcnt_r,
      ite_eq_left hcnt_pos, pure_bind,
      StateTransitionSpec.clientState_bind, clientState_fastBpReadAtProg, hread_r,
      StateTransitionSpec.clientState_bind, clientState_fastFeistelReconProg, hrec_val,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  have hcost_tot : memoryCost (fastPopAnyProg fl.pBase) s ≤ fastPopAnyCost fl.c := by
    unfold fastPopAnyProg fastPopAnyCost
    rw [Realization.memoryCost_bind', clientState_fastBpOwnerOfZeroProg, pure_bind,
      Realization.memoryCost_bind', clientState_fastReadBktCntProg, hcnt_r,
      ite_eq_left hcnt_pos, pure_bind,
      Realization.memoryCost_bind', clientState_fastBpReadAtProg, hread_r,
      Realization.memoryCost_bind', clientState_fastFeistelReconProg, hrec_val,
      Realization.memoryCost_bind', memoryCost_pure]
    change memoryCost (fastBpOwnerOfZeroProg fl.pBase) s +
        (memoryCost (fastReadBktCntProg (fl.pBase, b)) s +
          (memoryCost (fastBpReadAtProg (fl.pBase, (b, lastLoc))) s +
            (memoryCost (fastFeistelReconProg
              (fl.pBase, (b, (bpPairAt fl.bpL s.mem b lastLoc).1))) s +
              (memoryCost (fastRemoveAtProg ((fl.pBase, b), (lastLoc, u.val))) s + 0)))) ≤ _
    linarith only [hco, hcnt_c, hread_c, hrec_c, hcost']
  refine ⟨u, v, hres_eq, hs_u, ?_, hcost_tot, ?_, ?_, ?_, ?_⟩
  all_goals (rw [hst_eq])
  · exact hfr'
  · exact hinv'
  · exact hns'
  · exact hof'
  · exact hpart'

/-- Good-seed wrapper for `fastPopAnyProg`: also preserves `FastSubEpochGood` under
`GoodEpochSeeds win seeds`. -/
theorem fastPopAnyProg_good {slackCur slackPot : ℕ} {fl : FastEpochLayout} {w : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {hgood : GoodEpochSeeds win seeds}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hslack : slackCur ≤ 1)
    (hv : fl.Valid w s.frontier)
    (hg : FastSubEpochGood slackCur slackPot 0 win e seeds hgood s.mem s_abs)
    (hpos : 0 < (extractBlockPool fl.mp s.mem).nSide) :
    let res := (Memory.spec 0).clientResult s (fastPopAnyProg fl.pBase)
    let s' := (Memory.spec 0).clientState s (fastPopAnyProg fl.pBase)
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    ∃ (u : Fin fl.U) (v : Fin fl.V),
      res = (u.val, v.val) ∧ s_abs u = some v ∧
      FastSubEpochGood slackCur slackPot slack' win e seeds hgood s'.mem
        (Function.update s_abs u none) := by
  dsimp only
  have hr := hg.inv.ready hv rfl
  set bp := extractBlockPool fl.mp s.mem
  obtain ⟨_, _, hb, hl_lt⟩ := fastBpOwnerOfZeroProg_spec hr hg.inv.bp_inv.1.core hpos
  set b := ((Memory.spec 0).clientResult s (fastBpOwnerOfZeroProg fl.pBase)).1
  have hcnt_pos : 0 < bp.bktCount b := Nat.zero_lt_of_lt hl_lt
  set lastLoc := bp.bktCount b - 1
  have hlast_lt : lastLoc < bp.bktCount b := by omega
  obtain ⟨hcnt_r, _⟩ := fastReadBktCntProg_spec hr hg.inv.bp_inv.1.core hb
  obtain ⟨_, hread_r, _⟩ := fastBpReadAtProg_spec hr hg.inv.bp_inv hb hlast_lt
  obtain ⟨u, v, hu, hv_eq, _, hq_u, hs_u⟩ := hg.inv.bktSlot_refines hb hlast_lt
  have hq_lt : (bpPairAt fl.bpL s.mem b lastLoc).1 < 2 ^ quotBitsWhp fl.U fl.N :=
    hq_u ▸ keyQuotient_bWhp_lt hv.N_le_U u
  obtain ⟨hrec_r, _⟩ := fastFeistelReconProg_spec hr hq_lt hg.inv.seed_bkt (bkt := b)
  have hrec_val : (Memory.spec 0).clientResult s
      (fastFeistelReconProg (fl.pBase, (b, (bpPairAt fl.bpL s.mem b lastLoc).1))) = u.val := by
    rw [hrec_r]; exact hu.symm
  have hst_eq : (Memory.spec 0).clientState s (fastPopAnyProg fl.pBase) =
      (Memory.spec 0).clientState s (fastRemoveAtProg ((fl.pBase, b), (lastLoc, u.val))) := by
    unfold fastPopAnyProg
    rw [StateTransitionSpec.clientState_bind, clientState_fastBpOwnerOfZeroProg, pure_bind,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktCntProg, hcnt_r,
      ite_eq_left hcnt_pos, pure_bind,
      StateTransitionSpec.clientState_bind, clientState_fastBpReadAtProg, hread_r,
      StateTransitionSpec.clientState_bind, clientState_fastFeistelReconProg, hrec_val,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  have hres_eq : (Memory.spec 0).clientResult s (fastPopAnyProg fl.pBase) = (u.val, v.val) := by
    unfold fastPopAnyProg
    rw [prog_clientResult_bind, clientState_fastBpOwnerOfZeroProg, pure_bind,
      prog_clientResult_bind, clientState_fastReadBktCntProg, hcnt_r, ite_eq_left hcnt_pos,
      pure_bind, prog_clientResult_bind, clientState_fastBpReadAtProg, hread_r,
      prog_clientResult_bind, clientState_fastFeistelReconProg, hrec_val,
      prog_clientResult_bind, prog_clientResult_pure, hv_eq]
  refine ⟨u, v, hres_eq, hs_u, ?_⟩
  rw [hst_eq]
  exact fastRemoveAtProg_good u hslack hv hg hb hlast_lt hu.symm

/-! ## Section 5: `BufCur` Key-Preservation Helpers for Sub-Epoch Rollover -/

private theorem fastRelocBTreeProg_trie_eq {fl : FastEpochLayout}
    {w b delLoc lastLoc u_last : ℕ} {s : Memory.State} (hr : FastLayoutReady w fl s) :
    ∀ r < 2,
      extractBufTrie (fl.trieL r)
        ((Memory.spec 0).clientState s
          (fastRelocBTreeProg ((fl.pBase, (b, delLoc)), (lastLoc, u_last)))).mem =
      extractBufTrie (fl.trieL r) s.mem := by
  intro r hrl
  unfold fastRelocBTreeProg; dsimp only
  rw [StateTransitionSpec.clientState_bind,
    show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s from rfl,
    prog_clientResult_read]
  by_cases hcond : b < s.mem (fl.pBase + 11) ∧ delLoc < lastLoc
  · rw [ite_eq_left hcond,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
      StateTransitionSpec.clientState_bind, clientState_fastFpHashProg,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
    set salt := (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 5)))
    set role := (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 12)))
    set fp := (Memory.spec 0).clientResult s (fastFpHashProg (fl.pBase, (salt, u_last)))
    obtain ⟨_, hr1, hout1⟩ := fastBTreeUpdateProg_ready (b := b) (role := role) (q := fp)
      (newVal := delLoc) hr
    have ht1 : extractBufTrie (fl.trieL r)
        ((Memory.spec 0).clientState s
          (fastBTreeUpdateProg ((fl.pBase, (b, role)), (fp, delLoc)))).mem =
        extractBufTrie (fl.trieL r) s.mem :=
      extractBufTrie_congr_of_not_bt hr.1 hrl hout1
    set s1 := (Memory.spec 0).clientState s
      (fastBTreeUpdateProg ((fl.pBase, (b, role)), (fp, delLoc)))
    have hsh : FastLayoutReady w fl
          ((Memory.spec 0).clientState s1
            (fastRelocShadowStepProg ((fl.pBase, (b, role)), (fp, delLoc)))) ∧
        extractBufTrie (fl.trieL r)
          ((Memory.spec 0).clientState s1
            (fastRelocShadowStepProg ((fl.pBase, (b, role)), (fp, delLoc)))).mem =
          extractBufTrie (fl.trieL r) s1.mem := by
      unfold fastRelocShadowStepProg; dsimp only
      rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
        StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState s1 (Memory.read (fl.pBase + 0)) = s1 from rfl,
        prog_clientResult_read]
      split_ifs with hs
      · rw [StateTransitionSpec.clientState_bind, clientState_shadowRoleProg,
          StateTransitionSpec.clientState_bind]
        set sr := (Memory.spec 0).clientResult s1 (shadowRoleProg role)
        obtain ⟨_, hra, houta⟩ := fastBTreeInsertProg_ready (b := b) (role := sr) (q := fp)
          (val := delLoc) hr1
        have hta := extractBufTrie_congr_of_not_bt hr1.1 hrl houta
        set sa := (Memory.spec 0).clientState s1
          (fastBTreeInsertProg ((fl.pBase, (b, sr)), (fp, delLoc)))
        rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg]
        split_ifs with hl
        · obtain ⟨_, hrb, _, _, htb, _, _⟩ :=
            fastWriteBktLaneProg_frame (b := b) (lane := 14) (val := _) hra
          exact ⟨hrb, (htb r hrl).trans hta⟩
        · exact ⟨hra, hta⟩
      · exact ⟨hr1, rfl⟩
    set s2 := (Memory.spec 0).clientState s1
      (fastRelocShadowStepProg ((fl.pBase, (b, role)), (fp, delLoc)))
    have ht3 : extractBufTrie (fl.trieL r)
        ((Memory.spec 0).clientState s2
          (fastRelocTryStepProg ((fl.pBase, (b, role)), ((delLoc, lastLoc), u_last)))).mem =
        extractBufTrie (fl.trieL r) s2.mem := by
      unfold fastRelocTryStepProg; dsimp only
      rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
        StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
        StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
      by_cases hta : (Memory.spec 0).clientResult s2 (fastReadMetaProg (fl.pBase, 6)) = 1 ∧
          (Memory.spec 0).clientResult s2 (fastReadMetaProg (fl.pBase, 7)) = b
      · rw [ite_eq_left hta, StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
          StateTransitionSpec.clientState_bind, clientState_fastFpHashProg,
          StateTransitionSpec.clientState_bind, clientState_tryRoleProg]
        set ts := (Memory.spec 0).clientResult s2 (fastReadMetaProg (fl.pBase, 8))
        set fpT := (Memory.spec 0).clientResult s2 (fastFpHashProg (fl.pBase, (ts, u_last)))
        set tR := (Memory.spec 0).clientResult s2 (tryRoleProg role)
        set tp := (Memory.spec 0).clientResult s2 (fastReadMetaProg (fl.pBase, 9))
        by_cases hlt : lastLoc < tp
        · rw [ite_eq_left hlt]
          obtain ⟨_, _, houtu⟩ := fastBTreeUpdateProg_ready (b := b) (role := tR) (q := fpT)
            (newVal := delLoc) hsh.1
          exact extractBufTrie_congr_of_not_bt hsh.1.1 hrl houtu
        · rw [ite_eq_right hlt]
          by_cases hdl : delLoc < tp
          · rw [ite_eq_left hdl]
            unfold fastRelocTryInsProg; dsimp only
            rw [StateTransitionSpec.clientState_bind, clientState_fastBTreeLookupProg]
            by_cases hlk : ((Memory.spec 0).clientResult s2
                (fastBTreeLookupProg ((fl.pBase, (b, tR)), fpT))).1 = 1
            · rw [ite_eq_left hlk]
              exact (advanceTrySaltProg_frame hsh.1).2.2.2.2.1 r hrl
            · rw [ite_eq_right hlk, StateTransitionSpec.clientState_bind,
                show (Memory.spec 0).clientState s2 (Memory.read (fl.pBase + 0)) = s2 from rfl,
                prog_clientResult_read, StateTransitionSpec.clientState_bind]
              obtain ⟨_, hri, houti⟩ := fastBTreeInsertProg_ready (b := b) (role := tR) (q := fpT)
                (val := delLoc) hsh.1
              have hti := extractBufTrie_congr_of_not_bt hsh.1.1 hrl houti
              set si := (Memory.spec 0).clientState s2
                (fastBTreeInsertProg ((fl.pBase, (b, tR)), (fpT, delLoc)))
              rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
              by_cases hti_lt : (Memory.spec 0).clientResult si
                  (fastReadMetaProg (fl.pBase, 17)) < s2.mem (fl.pBase + 0)
              · rw [ite_eq_left hti_lt, clientState_fastWriteMetaProg hri.2.1 (Or.inr rfl)]
                have hw_pos : 0 < fl.w := hri.1.w_eq ▸ hri.1.w_pos
                have hcon : extractBufTrie (fl.trieL r)
                    (Function.update si.mem (fl.metaBase + 17)
                      ((Memory.spec 0).clientResult si (fastReadMetaProg (fl.pBase, 17)) + 1)) =
                    extractBufTrie (fl.trieL r) si.mem := by
                  have ho32 : 32 ≤ offBktMeta fl.c fl.w fl.N := hri.1.mp_valid.offBktMeta_ge
                  have hbm : offBktMeta fl.c fl.w fl.N ≤ offTrieChild fl.c fl.w fl.N 0 := by
                    unfold offTrieChild offBTreeVals offBTreeKeys offBTreeMeta offTailOwner
                      offSlabOwner offTailDir offSlabDir
                    omega
                  exact extractBufTrie_congr (show 0 < (fl.trieL r).w from hw_pos) fun a ha =>
                    Function.update_of_ne (fun heq => fl.disj_trie_bpAndMeta hri.1 hrl ha
                      (Or.inl ⟨by rw [heq]; omega, by rw [heq]; omega⟩)) _ _
                exact hcon.trans hti
              · rw [ite_eq_right hti_lt]; exact hti
          · rw [ite_eq_right hdl]; rfl
      · rw [ite_eq_right hta]; rfl
    exact ht3.trans (hsh.2.trans ht1)
  · rw [ite_eq_right hcond]; rfl

private theorem fastUnindexAtProg_cur_slot {slackCur : ℕ} {fl : FastEpochLayout} {w b delLoc : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (u : Fin fl.U)
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl 0 seeds s.mem s_abs)
    (hb : b < numBucketsWhp fl.N)
    (hdel : delLoc < (extractBlockPool fl.mp s.mem).bktCount b)
    (hk_u : fastKeyAt fl seeds.bkt s.mem b delLoc = u.val) :
    let fm := extractFastMeta fl s.mem
    let s1 := (Memory.spec 0).clientState s (fastUnindexAtProg ((fl.pBase, (b, delLoc)), u.val))
    ∀ id b' loc',
      bufCheckSlot (extractBufTrie (fl.trieL fm.curBufRole) s1.mem) id = some (b', loc') →
      bufCheckSlot (extractBufTrie (fl.trieL fm.curBufRole) s.mem) id = some (b', loc') ∧
      ¬(b' = b ∧ loc' = delLoc) := by
  dsimp only
  intro id b' loc' hchk
  have hr0 := hinv.ready hv rfl
  have hpt := hinv.param_table
  set fm := extractFastMeta fl s.mem
  have hrole_lt : fm.curBufRole < 2 := hinv.role_lt
  have hold_lt : 1 - fm.curBufRole < 2 := by omega
  obtain ⟨_, _, _, _, hfm1, _, _, _, _, _, _, ht1⟩ :=
    fastUnindexAtProg_spec u hv hinv hb hdel hk_u
  obtain ⟨mapC1, _, _, ht1w⟩ := ht1
  have hv_c1 : ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N)
      (extractBufTrie (fl.trieL fm.curBufRole)
        ((Memory.spec 0).clientState s
          (fastUnindexAtProg ((fl.pBase, (b, delLoc)), u.val))).mem) mapC1 := by
    have := ht1w.cur_valid; rwa [hfm1] at this
  obtain ⟨_, rk', _, _, hmc1⟩ := hv_c1.checkSlot_some hchk
  refine ⟨?_, (ht1w.cur_sound rk' b' loc' hmc1).2.2.1⟩
  have hrk_lt : rKeyOf fl.c fl.U fl.N seeds.fp u < 2 ^ (cTabWhp fl.c * bCharWhp fl.N) :=
    rKeyOf_lt fl.c fl.U fl.N seeds.fp u
  obtain ⟨mapCur0, _, _, hv_cur0, _, _, _, _, _, _, _, _, _, _, _⟩ := hinv.tiers
  obtain ⟨hrk_r, _⟩ := fastRKeyProg_spec hr0 hinv.seed_fp u
  have hr3_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 3)) =
      fm.curBufRole := clientResult_fastReadMetaProg hpt (by decide)
  unfold fastUnindexAtProg at hchk; dsimp only at hchk
  rw [StateTransitionSpec.clientState_bind, clientState_fastRKeyProg, hrk_r,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hr3_r,
    ite_eq_left hrole_lt,
    StateTransitionSpec.clientState_bind, clientState_fastBufLookupProg] at hchk
  split_ifs at hchk with hh1
  · have hfd := (fastBufDeleteProg_spec hr0 hrole_lt hv_cur0 hrk_lt).2.2.2.1
    rw [hfd] at hchk
    exact bufDelete_props.2.2.2.2 id b' loc' hchk
  · rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
      StateTransitionSpec.clientState_bind,
      show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 23)) = s from rfl] at hchk
    split_ifs at hchk with hss
    · rw [pure_bind, StateTransitionSpec.clientState_bind, clientState_fastBufLookupProg] at hchk
      split_ifs at hchk with ho
      · have hfdo := (fastBufDeleteProg_ready (role := 1 - fm.curBufRole)
            (rk := rKeyOf fl.c fl.U fl.N seeds.fp u) hr0).2.2.2 hold_lt
        have htr_o := (fastTrieMod_frame hr0.1 hold_lt hfdo.2).2.2.2.2.2.1
        have hrr : 1 - (1 - fm.curBufRole) = fm.curBufRole := by omega
        rw [hrr] at htr_o; rwa [htr_o] at hchk
      · rwa [fastDeleteFromBTreesProg_trie_eq hr0 fm.curBufRole hrole_lt] at hchk
    · rwa [fastDeleteFromBTreesProg_trie_eq hr0 fm.curBufRole hrole_lt] at hchk

private theorem fastSwapLastDownProg_cur_slot {slackCur : ℕ} {fl : FastEpochLayout}
    {w b delLoc lastLoc : ℕ} {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s1 : Memory.State} (uLast : Fin fl.U)
    (hslack : slackCur ≤ 1)
    (hr1 : FastLayoutReady w fl s1)
    (hbp_inv1 : fl.bpL.StateInv 0 s1.mem)
    (hbkt1 : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt s1.mem)
    (hfp1 : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp s1.mem)
    (hb : b < numBucketsWhp fl.N)
    (hcnt_le : (extractBlockPool fl.mp s1.mem).bktCount b ≤ capMaxWhp fl.N)
    (hlast_lt : lastLoc < (extractBlockPool fl.mp s1.mem).bktCount b)
    (hqL : (bpPairAt fl.bpL s1.mem b lastLoc).1 < 2 ^ quotBitsWhp fl.U fl.N)
    (hvL : (bpPairAt fl.bpL s1.mem b lastLoc).2 < fl.V)
    (hkL : fastKeyAt fl seeds.bkt s1.mem b lastLoc = uLast.val)
    (ht1 : TierInvHole slackCur fl seeds s1.mem b delLoc false) :
    let fm1 := extractFastMeta fl s1.mem
    let s2 := (Memory.spec 0).clientState s1
      (fastSwapLastDownProg ((fl.pBase, b), (delLoc, lastLoc)))
    ∀ id b' loc',
      bufCheckSlot (extractBufTrie (fl.trieL fm1.curBufRole) s2.mem) id = some (b', loc') →
      bufCheckSlot (extractBufTrie (fl.trieL fm1.curBufRole) s1.mem) id = some (b', loc') ∨
      (b' = b ∧ loc' = delLoc ∧ delLoc < lastLoc ∧
        bufCheckSlot (extractBufTrie (fl.trieL fm1.curBufRole) s1.mem) id =
          some (b, lastLoc)) := by
  dsimp only
  intro id b' loc' hchk
  set fm1 := extractFastMeta fl s1.mem
  obtain ⟨mapC1, _, _, ht1w⟩ := ht1
  have hrole_lt : fm1.curBufRole < 2 := ht1w.role_lt
  have hold_lt : 1 - fm1.curBufRole < 2 := by omega
  by_cases hdl : delLoc < lastLoc
  · have hq_b : (bpPairAt fl.bpL s1.mem b lastLoc).1 < 2 ^ fl.io.pgL.qBits :=
      hqL.trans_le (Nat.pow_le_pow_right Nat.one_lt_two.le hr1.1.qBits_le)
    have hv_b : (bpPairAt fl.bpL s1.mem b lastLoc).2 < 2 ^ fl.io.pgL.vBits := by
      rw [hr1.1.vBits_eq]
      exact hvL.trans_le (Nat.le_pow_clog Nat.one_lt_two fl.V)
    obtain ⟨_, hrr, _⟩ := fastBpReadAtProg_spec hr1 hbp_inv1 hb hlast_lt
    obtain ⟨hrec, _⟩ := fastFeistelReconProg_spec hr1 hqL hbkt1 (bkt := b)
    have hrec_val : (Memory.spec 0).clientResult s1
        (fastFeistelReconProg (fl.pBase, (b, (bpPairAt fl.bpL s1.mem b lastLoc).1))) =
        uLast.val := hrec.trans hkL
    unfold fastSwapLastDownProg at hchk; dsimp only at hchk
    rw [ite_eq_left hdl, StateTransitionSpec.clientState_bind, clientState_fastBpReadAtProg, hrr,
      StateTransitionSpec.clientState_bind, clientState_fastFeistelReconProg, hrec_val,
      StateTransitionSpec.clientState_bind] at hchk
    obtain ⟨hfrw, hrw, _, _, _, hfmw, _, _, _, htrw, hofw, _, _⟩ :=
      fastBpWriteAtProg_spec hr1 hbp_inv1 hb (lt_trans hdl hlast_lt) hq_b hv_b
    generalize hsw_def : (Memory.spec 0).clientState s1
      (fastBpWriteAtProg ((fl.pBase, (b, delLoc)), bpPairAt fl.bpL s1.mem b lastLoc)) = sw
      at hchk hfrw hrw hfmw htrw hofw
    have hcur_w : extractBufTrie (fl.trieL fm1.curBufRole) sw.mem =
        extractBufTrie (fl.trieL fm1.curBufRole) s1.mem := htrw fm1.curBufRole hrole_lt
    have hfp_w : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
        (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp sw.mem :=
      hfp1.congr_on (hr1.1.w_eq ▸ hr1.1.w_pos) fun a h1 h2 =>
        hofw a (hr1.1.not_ownsFast_seeds
          (by dsimp only [FastEpochLayout.fpHashBase] at h1; unfold offFpHash at h1
              have : offBktHash ≤ offFpHash fl.c fl.w fl.U := by
                unfold offFpHash; exact Nat.le_add_right _ _
              omega)
          (by dsimp only [FastEpochLayout.fpHashBase] at h2; unfold offBktMeta; omega))
    have hvw : ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N)
        (extractBufTrie (fl.trieL fm1.curBufRole) sw.mem) mapC1 := by
      rw [hcur_w]; exact ht1w.cur_valid
    have hrk_w_lt : rKeyOf fl.c fl.U fl.N seeds.fp uLast <
        2 ^ (cTabWhp fl.c * bCharWhp fl.N) := rKeyOf_lt fl.c fl.U fl.N seeds.fp uLast
    have hrw_c : (Memory.spec 0).clientResult sw (fastReadMetaProg (fl.pBase, 3)) =
        fm1.curBufRole :=
      (clientResult_fastReadMetaProg hrw.2.1 (by decide)).trans
        (congrArg FastEpochMeta.curBufRole hfmw)
    have hrk_w_r : (Memory.spec 0).clientResult sw (fastRKeyProg (fl.pBase, uLast.val)) =
        rKeyOf fl.c fl.U fl.N seeds.fp uLast := (fastRKeyProg_spec hrw hfp_w uLast).1
    unfold fastRelocLastProg at hchk; dsimp only at hchk
    rw [StateTransitionSpec.clientState_bind, clientState_fastRKeyProg, hrk_w_r,
      StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hrw_c,
      ite_eq_left hrole_lt,
      StateTransitionSpec.clientState_bind, clientState_fastBufLookupProg] at hchk
    have hlk_c := (fastBufLookupProg_spec hrw hrole_lt hvw hrk_w_lt).1
    by_cases hc_hit : mapC1 (rKeyOf fl.c fl.U fl.N seeds.fp uLast) = some (b, lastLoc)
    · rw [hlk_c, hc_hit] at hchk; dsimp only at hchk
      rw [ite_eq_left ⟨rfl, rfl, rfl⟩] at hchk
      have hrb_w : RawBufTrieBounds (extractBufTrie (fl.trieL fm1.curBufRole) sw.mem) := by
        rw [hcur_w]; exact ht1w.cur_raw
      have hia_w : (extractBufTrie (fl.trieL fm1.curBufRole) sw.mem).itemAlloc ≤
          qEpochWhp fl.N := by
        rw [hcur_w]
        exact ht1w.cur_ia.trans (by have h2 := ht1w.subStep_lt; omega)
      have hna_w : (extractBufTrie (fl.trieL fm1.curBufRole) sw.mem).nodeAlloc +
          cTabWhp fl.c ≤ maxTrieNodesWhp fl.c fl.N := by
        have h1 : (extractBufTrie (fl.trieL fm1.curBufRole) sw.mem).nodeAlloc ≤
            1 + cTabWhp fl.c * qEpochWhp fl.N := by
          rw [hcur_w]
          exact ht1w.cur_na.trans
            (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by rwa [← hcur_w])) 1)
        exact (Nat.add_le_add_right h1 _).trans (cTab_add_one_mul_le_maxTrieNodes hr1.1.thresh_le)
      have hb_ptr : b < 2 ^ globalPtrBits fl.N := by
        have hM_le : numBucketsWhp fl.N ≤ fl.N := by
          have hb_le : bWhp fl.N ≤ Nat.log 2 fl.N := by unfold bWhp; omega
          have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hr1.1.thresh_le
          exact (Nat.pow_le_pow_right (by decide) hb_le).trans (Nat.pow_log_le_self 2 hN_pos.ne')
        exact lt_of_lt_of_le (lt_of_lt_of_le hb hM_le) (Nat.le_of_lt hr1.1.mp_valid.nCap_lt_ptrB)
      have hdl_ptr : delLoc < 2 ^ globalPtrBits fl.N := by
        have hlt_n := lt_of_lt_of_le (lt_trans hdl hlast_lt) hcnt_le
        exact lt_of_lt_of_le (lt_of_lt_of_le hlt_n hr1.1.bounds_le_N.2.1)
          (Nat.le_of_lt hr1.1.mp_valid.nCap_lt_ptrB)
      have hext := (fastBufInsertProg_update_spec hrw hrole_lt hvw hrb_w hna_w hia_w
        (by rw [hc_hit]; exact Option.some_ne_none _) hrk_w_lt hb_ptr hdl_ptr).2.2.2.1
      rw [hext] at hchk
      obtain ⟨_, _, _, _, _, id₀, hid₀⟩ :=
        bufInsert_active_props hvw hrk_w_lt hc_hit (b := b) (loc := delLoc)
      by_cases he : id = id₀
      · subst he; obtain ⟨hbe, hle, h0⟩ := (hid₀ id).2 b' loc' hchk
        exact Or.inr ⟨hbe, hle, hdl, by rwa [← hcur_w]⟩
      · exact Or.inl (by rw [← hcur_w]; exact (hid₀ id).1 he ▸ hchk)
    · have hne_if : ¬(((Memory.spec 0).clientResult sw
          (fastBufLookupProg ((fl.pBase, fm1.curBufRole),
            rKeyOf fl.c fl.U fl.N seeds.fp uLast))).1 = 1 ∧
          ((Memory.spec 0).clientResult sw
            (fastBufLookupProg ((fl.pBase, fm1.curBufRole),
              rKeyOf fl.c fl.U fl.N seeds.fp uLast))).2.1 = b ∧
          ((Memory.spec 0).clientResult sw
            (fastBufLookupProg ((fl.pBase, fm1.curBufRole),
              rKeyOf fl.c fl.U fl.N seeds.fp uLast))).2.2 = lastLoc) := by
        rw [hlk_c]
        cases hm : mapC1 (rKeyOf fl.c fl.U fl.N seeds.fp uLast) with
        | none => exact fun h => absurd h.1 (by decide)
        | some p => intro h; exact hc_hit (hm.trans (congrArg some (Prod.ext h.2.1 h.2.2)))
      rw [ite_eq_right hne_if,
        StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
        StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState sw (Memory.read (fl.pBase + 23)) = sw from rfl] at hchk
      split_ifs at hchk with hss
      · rw [pure_bind, StateTransitionSpec.clientState_bind,
          clientState_fastBufLookupProg] at hchk
        split_ifs at hchk with ho
        · have hfo := (fastBufInsertProg_ready (role := 1 - fm1.curBufRole)
            (rk := rKeyOf fl.c fl.U fl.N seeds.fp uLast) (b := b) (loc := delLoc) hrw).2.2.2
            hold_lt
          have htr_o := (fastTrieMod_frame hrw.1 hold_lt hfo).2.2.2.2.2.1
          have hrr : 1 - (1 - fm1.curBufRole) = fm1.curBufRole := by omega
          rw [hrr] at htr_o
          exact Or.inl (by rwa [htr_o, hcur_w] at hchk)
        · rw [fastRelocBTreeProg_trie_eq hrw fm1.curBufRole hrole_lt, hcur_w] at hchk
          exact Or.inl hchk
      · rw [fastRelocBTreeProg_trie_eq hrw fm1.curBufRole hrole_lt, hcur_w] at hchk
        exact Or.inl hchk
  · unfold fastSwapLastDownProg at hchk; dsimp only at hchk
    rw [ite_eq_right hdl] at hchk; exact Or.inl hchk

/-- Active `BufCur` slot-provenance lemma for `fastRemoveAtProg`: every surviving active key in
`BufCur` after `fastRemoveAtProg` already occupied the same bucket (and held the exact same key)
in `BufCur` before `fastRemoveAtProg` (either stationary at `(b', loc')` or relocated from
`(b, bktCount b - 1)` to `(b, delLoc)`). -/
theorem fastRemoveAtProg_curSlot_keys {slackCur : ℕ} {fl : FastEpochLayout} {w b delLoc : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (u : Fin fl.U)
    (hslack : slackCur ≤ 1)
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl 0 seeds s.mem s_abs)
    (hb : b < numBucketsWhp fl.N)
    (hdel : delLoc < (extractBlockPool fl.mp s.mem).bktCount b)
    (hk_u : fastKeyAt fl seeds.bkt s.mem b delLoc = u.val) :
    let fm := extractFastMeta fl s.mem
    let s' := (Memory.spec 0).clientState s (fastRemoveAtProg ((fl.pBase, b), (delLoc, u.val)))
    let fm' := extractFastMeta fl s'.mem
    ∀ id b' loc' (u' : Fin fl.U),
      bufCheckSlot (extractBufTrie (fl.trieL fm'.curBufRole) s'.mem) id = some (b', loc') →
      b' < numBucketsWhp fl.N →
      loc' < (extractBlockPool fl.mp s'.mem).bktCount b' →
      fastKeyAt fl seeds.bkt s'.mem b' loc' = u'.val →
      ∃ loc₀ < (extractBlockPool fl.mp s.mem).bktCount b',
        bufCheckSlot (extractBufTrie (fl.trieL fm.curBufRole) s.mem) id = some (b', loc₀) ∧
        fastKeyAt fl seeds.bkt s.mem b' loc₀ = u'.val := by
  dsimp only
  intro id b' loc' u' hchk hb' hloc' hk'
  have hr0 := hinv.ready hv rfl
  have hpt := hinv.param_table
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  set cnt := bp.bktCount b
  set lastLoc := cnt - 1
  have hrole_lt : fm.curBufRole < 2 := hinv.role_lt
  have hcnt_pos : 0 < cnt := Nat.zero_lt_of_lt hdel
  have hlast_lt : lastLoc < cnt := Nat.sub_lt hcnt_pos Nat.one_pos
  have hlast_eq : cnt = lastLoc + 1 := (Nat.sub_add_cancel hcnt_pos).symm
  have hdel_le : delLoc ≤ lastLoc := Nat.le_pred_of_lt hdel
  have hm11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := hpt 11 (by decide)
  obtain ⟨hcnt_r, _⟩ := fastReadBktCntProg_spec hr0 hinv.bp_inv.1.core hb
  obtain ⟨_, _, _, _, hbc_b, hbc_ne, hkey', _, _, _, _, hcr', _⟩ :=
    fastRemoveAtProg_spec u hslack hv hinv hb hdel hk_u
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have seed_bkt_of : ∀ m : ℕ → ℕ, (∀ a, ¬fl.OwnsFastAddr a → m a = s.mem a) →
      BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w (redWidthWhp fl.U)
        (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt m := fun m hm =>
    hinv.seed_bkt.congr_on hw_pos fun a h1 h2 =>
      hm a (hv.not_ownsFast_seeds
        (by dsimp only [FastEpochLayout.bktHashBase] at h1; exact h1)
        (by dsimp only [FastEpochLayout.bktHashBase] at h2
            unfold offBktMeta offFpHash offBktHash at *; omega))
  have seed_fp_of : ∀ m : ℕ → ℕ, (∀ a, ¬fl.OwnsFastAddr a → m a = s.mem a) →
      BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
        (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp m := fun m hm =>
    hinv.seed_fp.congr_on hw_pos fun a h1 h2 =>
      hm a (hv.not_ownsFast_seeds
        (by dsimp only [FastEpochLayout.fpHashBase] at h1; unfold offFpHash at h1
            have : offBktHash ≤ offFpHash fl.c fl.w fl.U := by
              unfold offFpHash; exact Nat.le_add_right _ _
            omega)
        (by dsimp only [FastEpochLayout.fpHashBase] at h2; unfold offBktMeta; omega))
  obtain ⟨uLast, vLast, huL, hvL, _, hqL, _⟩ := hinv.bktSlot_refines hb hlast_lt
  have hne_last : ∀ loc'' < lastLoc, loc'' ≠ delLoc →
      fastKeyAt fl seeds.bkt s.mem b loc'' ≠ uLast.val := fun loc'' hl'' _ heq => by
    have hcv : bp.CoreValid := hinv.bp_inv.1.core
    have hloc''_lt : loc'' < cnt := lt_trans hl'' hlast_lt
    obtain ⟨u'', _, hu'', _, _, hq_u'', _⟩ := hinv.bktSlot_refines hb hloc''_lt
    have hu_e : u'' = uLast := Fin.ext (hu''.trans heq)
    have hq_e : (slotIoPairAt fl.io s.mem (bp.toPhys b loc'')).1 =
        (slotIoPairAt fl.io s.mem (bp.toPhys b lastLoc)).1 := by
      change (bpPairAt fl.bpL s.mem b loc'').1 = (bpPairAt fl.bpL s.mem b lastLoc).1
      rw [← hq_u'', hu_e, hqL]
    have hp1 := hcv.toPhys_lt hb hloc''_lt
    have hp2 := hcv.toPhys_lt hb hlast_lt
    have how1 : (bp.ownerOf (bp.toPhys b loc'')).1 = b := by rw [hcv.ownerOf_toPhys hb hloc''_lt]
    have how2 : (bp.ownerOf (bp.toPhys b lastLoc)).1 = b := by rw [hcv.ownerOf_toPhys hb hlast_lt]
    have hpe := hinv.refines.slot_inj _ hp1 _ hp2 (how1.trans how2.symm) hq_e
    have hle := congrArg (fun x => (bp.ownerOf x).2) hpe
    rw [hcv.ownerOf_toPhys hb hloc''_lt, hcv.ownerOf_toPhys hb hlast_lt] at hle
    exact (Nat.ne_of_lt hl'') hle
  have hcur_s1 := fastUnindexAtProg_cur_slot u hv hinv hb hdel hk_u
  obtain ⟨_, hr1, _, hbp1, hfm1, _, _, hoi1, hof1, _, _, ht1⟩ :=
    fastUnindexAtProg_spec u hv hinv hb hdel hk_u
  generalize hs1_def : (Memory.spec 0).clientState s
    (fastUnindexAtProg ((fl.pBase, (b, delLoc)), u.val)) = s1 at hr1 hbp1 hfm1 hoi1 hof1 ht1 hcur_s1
  have hbp_inv1 : fl.bpL.StateInv 0 s1.mem := bpStateInv_congr_io hv hinv.bp_inv hbp1 hoi1
  have hke1 : ∀ b'' < numBucketsWhp fl.N, ∀ loc'' < bp.bktCount b'',
      fastKeyAt fl seeds.bkt s1.mem b'' loc'' = fastKeyAt fl seeds.bkt s.mem b'' loc'' :=
    fun b'' hb'' loc'' hl'' => fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp1 hoi1 hb'' hl''
  have hpair1 : ∀ b'' < numBucketsWhp fl.N, ∀ loc'' < bp.bktCount b'',
      bpPairAt fl.bpL s1.mem b'' loc'' = bpPairAt fl.bpL s.mem b'' loc'' :=
    fun b'' hb'' loc'' hl'' => bpPairAt_eq_of_fixed_pool hv hinv.bp_inv hbp1 hoi1 hb'' hl''
  have hqL1 : (bpPairAt fl.bpL s1.mem b lastLoc).1 < 2 ^ quotBitsWhp fl.U fl.N := by
    rw [hpair1 b hb lastLoc hlast_lt, ← hqL]; exact keyQuotient_bWhp_lt hv.N_le_U uLast
  have hlast_ref1 : ∃ (uLast' : Fin fl.U) (vLast' : Fin fl.V),
      uLast'.val = fastKeyAt fl seeds.bkt s1.mem b lastLoc ∧
      vLast'.val = (bpPairAt fl.bpL s1.mem b lastLoc).2 ∧
      keyQuotient (bWhp fl.N) uLast'.val = (bpPairAt fl.bpL s1.mem b lastLoc).1 ∧
      ∀ loc'' < lastLoc, loc'' ≠ delLoc → fastKeyAt fl seeds.bkt s1.mem b loc'' ≠ uLast'.val :=
    ⟨uLast, vLast,
      huL.trans (hke1 b hb lastLoc hlast_lt).symm,
      hvL.trans (congrArg Prod.snd (hpair1 b hb lastLoc hlast_lt)).symm,
      hqL.trans (congrArg Prod.fst (hpair1 b hb lastLoc hlast_lt)).symm,
      fun loc'' hl'' hne => by
        rw [hke1 b hb loc'' (lt_trans hl'' hlast_lt)]; exact hne_last loc'' hl'' hne⟩
  have hcur_s2 := fastSwapLastDownProg_cur_slot uLast hslack hr1 hbp_inv1
    (seed_bkt_of s1.mem hof1) (seed_fp_of s1.mem hof1) hb
    (by rw [hbp1]; exact hinv.bkt_le_capMax b hb) (by rw [hbp1]; exact hlast_lt) hqL1
    (by rw [hpair1 b hb lastLoc hlast_lt, ← hvL]; exact vLast.isLt)
    ((hke1 b hb lastLoc hlast_lt).trans huL.symm) ht1
  obtain ⟨_, hr2, _, hbp2, hbp_inv2, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, ht2⟩ :=
    fastSwapLastDownProg_spec hslack hr1 hbp_inv1 (seed_bkt_of s1.mem hof1)
      (seed_fp_of s1.mem hof1) hb (by rw [hbp1]; exact hinv.bkt_le_capMax b hb)
      (by rw [hbp1]; exact hlast_eq) hdel_le hlast_ref1 ht1
  generalize hs2_def : (Memory.spec 0).clientState s1
    (fastSwapLastDownProg ((fl.pBase, b), (delLoc, lastLoc))) = s2 at hr2 hbp2 hbp_inv2 ht2 hcur_s2
  have hbp12 : extractBlockPool fl.mp s2.mem = bp := hbp2.trans hbp1
  obtain ⟨_, hr3, _, _, _, _, _, _, hfm3, _, _, _, htr3, _, _⟩ :=
    fastBpPopBktBackProg_spec hr2 hbp_inv2 hb (by rw [hbp12]; exact hcnt_pos)
  generalize hs3_def : (Memory.spec 0).clientState s2 (fastBpPopBktBackProg (fl.pBase, b)) = s3
    at hr3 hfm3 htr3
  rcases ht2 with ⟨_, _, _, ht2w⟩
  have hrl3_lt : (extractFastMeta fl s3.mem).curRole b < 3 := by
    rw [hfm3]; exact (ht2w.bkt_meta_bounds b hb).2.1
  have hsh3_ins : (extractFastMeta fl s3.mem).shadowCode b = cnt →
      (extractFastMeta fl s3.mem).shadowIns b ≤ 5 * slabScale fl.N ^ 12 := fun heq => by
    have h2 : (extractFastMeta fl s2.mem).shadowCode b = cnt := by rwa [hfm3] at heq
    have hnz : (extractFastMeta fl s2.mem).shadowCode b ≠ 0 := by rw [h2]; exact hcnt_pos.ne'
    obtain ⟨_, _, hbd, _⟩ := ht2w.shadow b hb hnz
    have hmul : 4 * (extractFastMeta fl s2.mem).shadowIns b ≤ 4 * (5 * slabScale fl.N ^ 12) :=
      (Nat.le_add_right _ _).trans (hbd.trans (by rw [← Nat.mul_assoc]))
    have hres := Nat.le_of_mul_le_mul_left hmul (by decide : 0 < 4)
    rwa [hfm3]
  obtain ⟨_, hr4, _, _, _, _, _, htr4, _, _, _, _⟩ :=
    fastPromoteShadowIfDoneProg_spec hr3 hb hcnt_pos hrl3_lt hsh3_ins
  generalize hs4_def : (Memory.spec 0).clientState s3
    (fastPromoteShadowIfDoneProg ((fl.pBase, b), cnt)) = s4 at hr4 htr4
  obtain ⟨_, _, _, _, _, _, _, htr5, _, _, _⟩ :=
    fastClampTryPosProg_spec (b := b) (cnt := cnt) (lastLoc := lastLoc) hr4
  have hseq : (Memory.spec 0).clientState s (fastRemoveAtProg ((fl.pBase, b), (delLoc, u.val))) =
      (Memory.spec 0).clientState s4 (fastClampTryPosProg ((fl.pBase, b), (cnt, lastLoc))) := by
    unfold fastRemoveAtProg; dsimp only
    rw [StateTransitionSpec.clientState_bind,
      show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s from rfl,
      hm11_r, ite_eq_left hb,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktCntProg, hcnt_r,
      ite_eq_left hdel, pure_bind,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      hs1_def, hs2_def, hs3_def, hs4_def]
  have hchk2 : bufCheckSlot (extractBufTrie (fl.trieL fm.curBufRole) s2.mem) id =
      some (b', loc') := by
    rw [hcr', hseq, htr5 fm.curBufRole hrole_lt, htr4 fm.curBufRole hrole_lt,
      htr3 fm.curBufRole hrole_lt] at hchk
    exact hchk
  rw [hfm1] at hcur_s2
  rcases hcur_s2 id b' loc' hchk2 with h1 | ⟨hbe, hle, _, h1⟩
  · obtain ⟨h0, hne⟩ := hcur_s1 id b' loc' h1
    have hl0 : loc' < bp.bktCount b' := by
      by_cases hbb : b' = b
      · rw [hbb, hbc_b] at hloc'; rw [hbb]; exact lt_of_lt_of_le hloc' (Nat.sub_le _ 1)
      · rwa [hbc_ne b' hbb] at hloc'
    have hkf := hkey' b' hb' loc' hloc'
    rw [ite_eq_right hne] at hkf
    exact ⟨loc', hl0, h0, hkf.symm.trans hk'⟩
  · have h0 := (hcur_s1 id b lastLoc h1).1
    have hkf := hkey' b' hb' loc' hloc'
    rw [ite_eq_left ⟨hbe, hle⟩] at hkf
    refine ⟨lastLoc, by rw [hbe]; exact hlast_lt, hbe ▸ h0, ?_⟩
    rw [hbe]; exact hkf.symm.trans hk'

/-- Active `BufCur` slot-provenance lemma for `fastPopAnyProg`: every surviving active key in
`BufCur` after `fastPopAnyProg` already occupied `BufCur` before `fastPopAnyProg` with the same
exact key. -/
theorem fastPopAnyProg_curSlot_keys {slackCur : ℕ} {fl : FastEpochLayout} {w : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hslack : slackCur ≤ 1)
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl 0 seeds s.mem s_abs)
    (hpos : 0 < (extractBlockPool fl.mp s.mem).nSide) :
    let fm := extractFastMeta fl s.mem
    let s' := (Memory.spec 0).clientState s (fastPopAnyProg fl.pBase)
    let fm' := extractFastMeta fl s'.mem
    ∀ id b' loc' (u' : Fin fl.U),
      bufCheckSlot (extractBufTrie (fl.trieL fm'.curBufRole) s'.mem) id = some (b', loc') →
      b' < numBucketsWhp fl.N →
      loc' < (extractBlockPool fl.mp s'.mem).bktCount b' →
      fastKeyAt fl seeds.bkt s'.mem b' loc' = u'.val →
      ∃ loc₀ < (extractBlockPool fl.mp s.mem).bktCount b',
        bufCheckSlot (extractBufTrie (fl.trieL fm.curBufRole) s.mem) id = some (b', loc₀) ∧
        fastKeyAt fl seeds.bkt s.mem b' loc₀ = u'.val := by
  dsimp only
  have hr := hinv.ready hv rfl
  set bp := extractBlockPool fl.mp s.mem
  obtain ⟨_, _, hb, hl_lt⟩ := fastBpOwnerOfZeroProg_spec hr hinv.bp_inv.1.core hpos
  set b := ((Memory.spec 0).clientResult s (fastBpOwnerOfZeroProg fl.pBase)).1
  have hcnt_pos : 0 < bp.bktCount b := Nat.zero_lt_of_lt hl_lt
  set lastLoc := bp.bktCount b - 1
  have hlast_lt : lastLoc < bp.bktCount b := by omega
  obtain ⟨hcnt_r, _⟩ := fastReadBktCntProg_spec hr hinv.bp_inv.1.core hb
  obtain ⟨_, hread_r, _⟩ := fastBpReadAtProg_spec hr hinv.bp_inv hb hlast_lt
  obtain ⟨u, _, hu, _, _, hq_u, _⟩ := hinv.bktSlot_refines hb hlast_lt
  have hq_lt : (bpPairAt fl.bpL s.mem b lastLoc).1 < 2 ^ quotBitsWhp fl.U fl.N :=
    hq_u ▸ keyQuotient_bWhp_lt hv.N_le_U u
  obtain ⟨hrec_r, _⟩ := fastFeistelReconProg_spec hr hq_lt hinv.seed_bkt (bkt := b)
  have hrec_val : (Memory.spec 0).clientResult s
      (fastFeistelReconProg (fl.pBase, (b, (bpPairAt fl.bpL s.mem b lastLoc).1))) = u.val := by
    rw [hrec_r]; exact hu.symm
  have hst_eq : (Memory.spec 0).clientState s (fastPopAnyProg fl.pBase) =
      (Memory.spec 0).clientState s (fastRemoveAtProg ((fl.pBase, b), (lastLoc, u.val))) := by
    unfold fastPopAnyProg
    rw [StateTransitionSpec.clientState_bind, clientState_fastBpOwnerOfZeroProg, pure_bind,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktCntProg, hcnt_r,
      ite_eq_left hcnt_pos, pure_bind,
      StateTransitionSpec.clientState_bind, clientState_fastBpReadAtProg, hread_r,
      StateTransitionSpec.clientState_bind, clientState_fastFeistelReconProg, hrec_val,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  rw [hst_eq]
  exact fastRemoveAtProg_curSlot_keys u hslack hv hinv hb hlast_lt hu.symm

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
