/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvFGCore

/-!
# Foreground Mutation Setup (`DualEpochInvFGSetup`)

Establishes `fgSetup_of_dualStateInv`, discharging the `PrepGrowPre`, `growZero`, and
`UserMutatePre` preconditions from `DualStateInv` across all 12 phases (`0..11`) of the deamortized
dual-epoch resizable succinct worst-case WHP dictionary ([Bender, Farach-Colton, J. Kuszmaul, and
W. Kuszmaul, SOSA 2024, Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]).

## Main results

* `fgSetup_of_dualStateInv`

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
open EpochUpdate

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-- Pre-computed capacity, `prepGrowProg`, and layout facts extracted from `DualStateInv`. -/
structure FGSetup (c U V w base opTag : ℕ) (u : Fin U) (v : Fin V)
    (s_dict : Dictionary.State U) (L : DualLatent c U V) (s : Memory.State) : Prop where
  /-- Foreground setup invariant field `src_safe`. -/
  src_safe : EpochCapSafe (whpThreshold c) U (s.mem (base + hdrNSrc)) (Dictionary.dom s_dict).card
  /-- Foreground setup invariant field `dst_safe`. -/
  dst_safe :
    EpochCapSafe (whpThreshold c) U
      (if s.mem (base + hdrPhase) = 0 then s.mem (base + hdrNSrc) else s.mem (base + hdrNDst))
      (Dictionary.dom s_dict).card
  /-- Foreground setup invariant field `len_bounds`. -/
  len_bounds :
    (s.mem (base + hdrPhase) ≤ 8 →
      L.slotSrc.nCap ≠ 0 → L.slotSrc.evs.length ≤ 4 * L.slotSrc.nCap) ∧
    (8 ≤ s.mem (base + hdrPhase) →
      L.slotDst.nCap ≠ 0 → L.slotDst.evs.length ≤ 4 * L.slotDst.nCap)
  /-- Foreground setup invariant field `card_step`. -/
  card_step :
    let nLive := (Dictionary.dom s_dict).card
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val) else Function.update s_dict u none
    let nLive' := (Dictionary.dom s_dict').card
    let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
    (opTag = 1 → nLive' = if s_dict u = none then nLive + 1 else nLive) ∧
    (opTag ≠ 1 → nLive' = if s_dict u = none then nLive else nLive - 1) ∧
    nLive' ≤ nAlloc ∧ nLive ≤ nLive' + 1 ∧ nLive' ≤ nLive + 1 ∧
    nLive' ≤ U ∧ nAlloc ≤ U ∧ nAlloc ≤ nLive + 1
  /-- Foreground setup invariant field `pre_pg`. -/
  pre_pg : PrepGrowPre w (((base, s.frontier), opTag), u.val) s
  /-- Foreground setup invariant field `s_prep_fr`. -/
  s_prep_fr :
    ((Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))).frontier =
      s.frontier
  /-- Foreground setup invariant field `mc_pg`. -/
  mc_pg : memoryCost (prepGrowProg (((base, s.frontier), opTag), u.val)) s ≤ 40
  /-- Foreground setup invariant field `stg0_le3`. -/
  stg0_le3 : s.mem (base + hdrPhase) ≤ 3 → s.mem (base + hdrStage) = 0
  /-- Foreground setup invariant field `ibLo_ge`. -/
  ibLo_ge : base + 192 ≤ s.mem (base + hdrItemLo)
  /-- Foreground setup invariant field `ibHi_ge_ibLo`. -/
  ibHi_ge_ibLo :
    s.mem (base + hdrItemLo) ≤ s.mem (base + hdrItemHi) ∧
    (2 ≤ s.mem (base + hdrPhase) → s.mem (base + hdrItemLo) + 4 ≤ s.mem (base + hdrItemHi)) ∧
    s.mem (base + hdrQLo) ≤ s.mem (base + hdrQHi)
  /-- Foreground setup invariant field `nDst0_sched`. -/
  nDst0_sched :
    s.mem (base + hdrPhase) ≠ 0 → s.mem (base + hdrNDst) = 0 →
      0 < s.mem (base + hdrNSrc) ∧ s.mem (base + hdrStage) = 0 ∧
      s.mem (base + hdrPhase) ≠ 1 ∧ s.mem (base + hdrPhase) ≠ 4 ∧ s.mem (base + hdrPhase) ≠ 5
  /-- Foreground setup invariant field `ge2_sched`. -/
  ge2_sched :
    s.mem (base + hdrPhase) ≠ 0 → 2 ≤ s.mem (base + hdrPhase) →
      s.mem (base + hdrMDst) = epochMetaWordsWhp c w (s.mem (base + hdrNDst)) ∧
      s.mem (base + hdrPad) = max (s.mem (base + hdrMSrc)) (s.mem (base + hdrMDst)) ∧
      HostCacheValid c w (s.mem (base + hdrNDst)) hdrDstOd base s.mem ∧
      (0 < s.mem (base + hdrNDst) →
        s.mem (base + hdrLogN) = Nat.log 2 (s.mem (base + hdrNDst)) ∧
        s.mem (base + hdrEll) = Dynamic.logLogFactor (s.mem (base + hdrNDst)) ∧
        s.mem (base + hdrPgB) = pageSizeWhp (s.mem (base + hdrNDst))) ∧
      s.mem (base + hdrItemHi) =
        (if s.mem (base + hdrNDst) = 0 then base + 196 + s.mem (base + hdrMSrc)
         else base + 192 + s.mem (base + hdrPad) + s.mem (base + hdrMDst) + 4) ∧
      s.mem (base + hdrQHi) =
        max (if s.mem (base + hdrNSrc) = 0 then keyBits U
             else quotBitsWhp U (s.mem (base + hdrNSrc)))
          (if s.mem (base + hdrNDst) = 0 then keyBits U
           else quotBitsWhp U (s.mem (base + hdrNDst)))
  /-- Foreground setup invariant field `fr_bounds`. -/
  fr_bounds :
    let nLive := (Dictionary.dom s_dict).card
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val) else Function.update s_dict u none
    let nLive' := (Dictionary.dom s_dict').card
    let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
    let ph := s.mem (base + hdrPhase)
    let nSrc := s.mem (base + hdrNSrc)
    let nDst := s.mem (base + hdrNDst)
    let ibLo := s.mem (base + hdrItemLo)
    let ibHi := s.mem (base + hdrItemHi)
    let qLo := s.mem (base + hdrQLo)
    let qHi := s.mem (base + hdrQHi)
    let vB := valBits V
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    k_grow ≤ bulkBatchWhp ∧
    s_grow.frontier ≤ base + dualPaddedWords c U V w nSrc (if ph = 0 then nSrc else nDst) nLive ∧
    (ph ≤ 2 ∨ ph = 11 → ibLo + pairStreamWords nAlloc qLo vB w ≤ s_grow.frontier) ∧
    (3 ≤ ph ∧ ph ≤ 10 → ibHi + pairStreamWords nAlloc qHi vB w ≤ s_grow.frontier) ∧
    (ph ≤ 1 → s_grow.frontier ≤ ibLo + pairStreamWords (nLive' + 1) qLo vB w) ∧
    (2 ≤ ph → s_grow.frontier ≤ ibHi + pairStreamWords (nLive' + 1) qHi vB w) ∧
    (ph = 2 →
      ((ibHi + pairStreamWords nLive' qHi vB w) - s_grow.frontier) +
        (if s_grow.frontier < ibHi + pairStreamWords nLive' qHi vB w then 1022 else 0) ≤
      (ibHi + pairStreamWords nLive qHi vB w) - s.frontier) ∧
    (ph = 11 → s_grow.frontier - (ibLo + pairStreamWords nLive' qLo vB w) ≤
      (s.frontier - (ibLo + pairStreamWords nLive qLo vB w)) + 2)
  /-- Foreground setup invariant field `wf_grow`. -/
  wf_grow :
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
    Memory.WellFormed w { mem := s_prep.mem, frontier := s.frontier + k_grow }
  /-- Foreground setup invariant field `grow_below`. -/
  grow_below :
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    ∀ addr < base, s_prep.mem addr = s.mem addr
  /-- Foreground setup invariant field `grow_low`. -/
  grow_low :
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    ∀ off < 60, s_prep.mem (base + off) = s.mem (base + off)
  /-- Foreground setup invariant field `grow_ge192`. -/
  grow_ge192 :
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    ∀ addr, base + 192 ≤ addr → s_prep.mem addr = s.mem addr
  /-- Foreground setup invariant field `grow_p_rest`. -/
  grow_p_rest :
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    ∀ pB, (pB = base + hdrPBase0 ∨ pB = base + hdrPBase1) →
      ∀ a, pB ≤ a → a < pB + 64 → a ≠ pB + 60 → s_prep.mem a = s.mem a
  /-- Foreground setup invariant field `lift_grow_slot`. -/
  lift_grow_slot :
    let nLive := (Dictionary.dom s_dict).card
    let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    ∀ {pB mb slack : ℕ} {io0 : SlotIoLayout} {dr : Bool} {sl : SlotLatent c U V},
      EpochSlotInv c U V w s.frontier pB mb io0 slack dr sl s.mem →
      io0.pgL.nCap = nLive →
      (pB = base + hdrPBase0 ∨ pB = base + hdrPBase1) →
      ((sl.nCap = 0 ∧ (mb = base + hdrSmallMeta0 ∨ mb = base + hdrSmallMeta1)) ∨
        (sl.nCap ≠ 0 ∧ base + 192 ≤ mb)) →
      ((io0.usePaged = 0 → io0.sideBit ≠ 0 →
          io0.pgL.metaBase = base + hdrSplit ∧ base + 192 ≤ io0.pgL.offDir) ∧
        (io0.usePaged ≠ 0 → base + 192 ≤ io0.pgL.metaBase) ∧
        base + 192 ≤ io0.pgL.itemBase) →
      (io0.usePaged = 0 → io0.sideBit = 0 →
        io0.pgL.itemBase + pairStreamWords nAlloc io0.pgL.qBits io0.pgL.vBits io0.pgL.w ≤
          s_grow.frontier) →
      (io0.usePaged = 0 → io0.sideBit ≠ 0 →
        io0.pgL.itemBase + pairStreamWords nAlloc io0.pgL.offTail io0.pgL.vBits io0.pgL.w ≤
          s_grow.frontier) →
      (io0.usePaged ≠ 0 →
        nAlloc ≤ (io0.pgL.maxPages - 2) * io0.pgL.pgB ∧
        io0.pgL.itemBase + pairStreamWords nAlloc io0.pgL.qBits io0.pgL.vBits io0.pgL.w ≤
          s_grow.frontier) →
      (mb + (if sl.nCap = 0 then 2 else offPageDir c w sl.nCap) ≤ io0.pgL.itemBase ∧
        (io0.usePaged = 0 → io0.sideBit ≠ 0 →
          mb + (if sl.nCap = 0 then 2 else offPageDir c w sl.nCap) ≤ io0.pgL.offDir)) →
      EpochSlotInv c U V w s_grow.frontier pB mb (io0.withNCap nAlloc) slack dr sl s_grow.mem
  /-- Foreground setup invariant field `od_le_nSrc`. -/
  od_le_nSrc :
    s.mem (base + hdrNSrc) ≠ 0 →
      offPageDir c w (s.mem (base + hdrNSrc)) ≤ epochMetaWordsWhp c w (s.mem (base + hdrNSrc))
  /-- Foreground setup invariant field `od_le_nDst`. -/
  od_le_nDst :
    s.mem (base + hdrPhase) ≠ 0 → s.mem (base + hdrNDst) ≠ 0 →
      offPageDir c w (s.mem (base + hdrNDst)) ≤ epochMetaWordsWhp c w (s.mem (base + hdrNDst))
  /-- Foreground setup invariant field `pgHost_cap`. -/
  pgHost_cap :
    let nLive := (Dictionary.dom s_dict).card
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val) else Function.update s_dict u none
    let nLive' := (Dictionary.dom s_dict').card
    let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
    let stg := s.mem (base + hdrStage)
    let nSrc := s.mem (base + hdrNSrc)
    let nDst := s.mem (base + hdrNDst)
    let pad := s.mem (base + hdrPad)
    let ibHi := s.mem (base + hdrItemHi)
    let qHi := s.mem (base + hdrQHi)
    let nHost := if nDst = 0 then nSrc else nDst
    let mbHost := if nDst = 0 then base + 192
      else if stg = 0 then base + 192 + pad else base + 192
    let pgHost := hostPageLayout c w nHost mbHost ibHi qHi (valBits V) nLive
    8 ≤ s.mem (base + hdrPhase) → s.mem (base + hdrPhase) ≤ 9 →
      nAlloc ≤ (pgHost.maxPages - 2) * pgHost.pgB ∧
      nLive' ≤ (pgHost.maxPages - 2) * pgHost.pgB
  /-- Foreground setup invariant field `sm_src`. -/
  sm_src :
    s.mem (base + hdrPhase) ≤ 8 →
      L.slotSrc.nCap = 0 → (liveDom L.slotSrc.s_abs).card ≤ 2 * whpThreshold c
  /-- Foreground setup invariant field `sm_dst`. -/
  sm_dst :
    8 ≤ s.mem (base + hdrPhase) →
      L.slotDst.nCap = 0 → (liveDom L.slotDst.s_abs).card ≤ 2 * whpThreshold c
  /-- Foreground setup invariant field `mbSrc_info`. -/
  mbSrc_info :
    let ph := s.mem (base + hdrPhase)
    let stg := s.mem (base + hdrStage)
    let nSrc := s.mem (base + hdrNSrc)
    let nDst := s.mem (base + hdrNDst)
    let pad := s.mem (base + hdrPad)
    let ibLo := s.mem (base + hdrItemLo)
    let ibHi := s.mem (base + hdrItemHi)
    let capSrc := if stg = 0 then nSrc else nDst
    let mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
      else base + 192 + pad
    ph ≤ 8 →
      L.slotSrc.nCap = capSrc ∧
      ((L.slotSrc.nCap = 0 ∧ (mbSrc = base + hdrSmallMeta0 ∨ mbSrc = base + hdrSmallMeta1)) ∨
        (L.slotSrc.nCap ≠ 0 ∧ base + 192 ≤ mbSrc)) ∧
      (ph ≤ 3 → mbSrc + (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤ ibLo) ∧
      (3 ≤ ph → mbSrc + (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤ ibHi)
  /-- Foreground setup invariant field `mbDst_info`. -/
  mbDst_info :
    let ph := s.mem (base + hdrPhase)
    let stg := s.mem (base + hdrStage)
    let nDst := s.mem (base + hdrNDst)
    let pad := s.mem (base + hdrPad)
    let ibLo := s.mem (base + hdrItemLo)
    let ibHi := s.mem (base + hdrItemHi)
    let mbDst := if ph < 10 then
        (if nDst = 0 then base + hdrSmallMeta1
         else if stg = 0 then base + 192 + pad else base + 192)
      else
        (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
    8 ≤ ph →
      L.slotDst.nCap = nDst ∧
      ((L.slotDst.nCap = 0 ∧ (mbDst = base + hdrSmallMeta0 ∨ mbDst = base + hdrSmallMeta1)) ∨
        (L.slotDst.nCap ≠ 0 ∧ base + 192 ≤ mbDst)) ∧
      (ph ≤ 10 →
        mbDst + (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤ ibHi) ∧
      (10 ≤ ph →
        mbDst + (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤ ibLo)
  /-- Foreground setup invariant field `fr_n'`. -/
  fr_n' :
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val) else Function.update s_dict u none
    let nLive' := (Dictionary.dom s_dict').card
    let ph := s.mem (base + hdrPhase)
    let ibLo := s.mem (base + hdrItemLo)
    let ibHi := s.mem (base + hdrItemHi)
    let qLo := s.mem (base + hdrQLo)
    let qHi := s.mem (base + hdrQHi)
    let vB := valBits V
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    (ph ≤ 2 ∨ ph = 11 → ibLo + pairStreamWords nLive' qLo vB w ≤ s_grow.frontier) ∧
    (3 ≤ ph ∧ ph ≤ 10 → ibHi + pairStreamWords nLive' qHi vB w ≤ s_grow.frontier)


private theorem card_step_of_dualStateInv {c U V w base opTag : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s) (u : Fin U) (v : Fin V) :
    let nLive := (Dictionary.dom s_dict).card
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val) else Function.update s_dict u none
    let nLive' := (Dictionary.dom s_dict').card
    let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
    (opTag = 1 → nLive' = if s_dict u = none then nLive + 1 else nLive) ∧
    (opTag ≠ 1 → nLive' = if s_dict u = none then nLive else nLive - 1) ∧
    nLive' ≤ nAlloc ∧ nLive ≤ nLive' + 1 ∧ nLive' ≤ nLive + 1 ∧
    nLive' ≤ U ∧ nAlloc ≤ U ∧ nAlloc ≤ nLive + 1 := by
  dsimp only
  have hnL_U := h.live_le
  set nLive := (Dictionary.dom s_dict).card
  set s_dict' :=
    if opTag = 1 then Function.update s_dict u (some v.val)
    else Function.update s_dict u none
  set nLive' := (Dictionary.dom s_dict').card
  set nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
  classical
  have hdom_ins : (Dictionary.dom (Function.update s_dict u (some v.val))).card =
      if s_dict u = none then nLive + 1 else nLive := by
    have heq : Dictionary.dom (Function.update s_dict u (some v.val)) =
        insert u (Dictionary.dom s_dict) := by
      ext x; unfold Dictionary.dom
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hx : x = u <;> simp [hx]
    rw [heq]
    by_cases hn : s_dict u = none
    · rw [ite_eq_left hn, Finset.card_insert_of_notMem]
      unfold Dictionary.dom; simp [hn]
    · rw [ite_eq_right hn, Finset.insert_eq_of_mem]
      unfold Dictionary.dom; simp [Option.isSome_iff_ne_none, hn]
  have hdom_del : (Dictionary.dom (Function.update s_dict u none)).card =
      if s_dict u = none then nLive else nLive - 1 := by
    have heq : Dictionary.dom (Function.update s_dict u none) =
        (Dictionary.dom s_dict).erase u := by
      ext x; unfold Dictionary.dom
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      by_cases hx : x = u <;> simp [hx]
    rw [heq]
    by_cases hn : s_dict u = none
    · rw [ite_eq_left hn, Finset.erase_eq_of_notMem]
      unfold Dictionary.dom; simp [hn]
    · rw [ite_eq_right hn, Finset.card_erase_of_mem]
      unfold Dictionary.dom; simp [Option.isSome_iff_ne_none, hn]
  have hltU_none : s_dict u = none → nLive + 1 ≤ U := fun hn => (cap_lt_on_insert_none h hn).1
  refine ⟨fun h1 => by dsimp only [nLive', s_dict']; rw [ite_eq_left h1]; exact hdom_ins,
    fun h1 => by dsimp only [nLive', s_dict']; rw [ite_eq_right h1]; exact hdom_del,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [nLive', s_dict', nAlloc]
    by_cases h1 : opTag = 1
    · rw [ite_eq_left h1, ite_eq_left h1, hdom_ins]
      split_ifs with hn
      · have := hltU_none hn; omega
      · omega
    · rw [ite_eq_right h1, ite_eq_right h1, hdom_del]; split_ifs <;> omega
  · dsimp only [nLive', s_dict']
    by_cases h1 : opTag = 1
    · rw [ite_eq_left h1, hdom_ins]; split_ifs <;> omega
    · rw [ite_eq_right h1, hdom_del]; split_ifs <;> omega
  · dsimp only [nLive', s_dict']
    by_cases h1 : opTag = 1
    · rw [ite_eq_left h1, hdom_ins]; split_ifs <;> omega
    · rw [ite_eq_right h1, hdom_del]; split_ifs <;> omega
  · dsimp only [nLive', s_dict']
    by_cases h1 : opTag = 1
    · rw [ite_eq_left h1, hdom_ins]
      split_ifs with hn
      · exact hltU_none hn
      · exact hnL_U
    · rw [ite_eq_right h1, hdom_del]; split_ifs <;> omega
  · dsimp only [nAlloc]; split_ifs <;> omega
  · dsimp only [nAlloc]; split_ifs <;> omega

private theorem layout_step_of_dualStateInv {c U V w base : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s) :
    (s.mem (base + hdrPhase) ≤ 3 → s.mem (base + hdrStage) = 0) ∧
    base + 192 ≤ s.mem (base + hdrItemLo) ∧
    (s.mem (base + hdrItemLo) ≤ s.mem (base + hdrItemHi) ∧
      (2 ≤ s.mem (base + hdrPhase) → s.mem (base + hdrItemLo) + 4 ≤ s.mem (base + hdrItemHi)) ∧
      s.mem (base + hdrQLo) ≤ s.mem (base + hdrQHi)) ∧
    (s.mem (base + hdrNSrc) ≠ 0 →
      offPageDir c w (s.mem (base + hdrNSrc)) ≤ epochMetaWordsWhp c w (s.mem (base + hdrNSrc))) ∧
    (s.mem (base + hdrPhase) ≠ 0 → s.mem (base + hdrNDst) ≠ 0 →
      offPageDir c w (s.mem (base + hdrNDst)) ≤
        epochMetaWordsWhp c w (s.mem (base + hdrNDst))) := by
  obtain ⟨hsrc_safe, hdst_safe⟩ := dualCoreInv_cap_safe h
  have hstg_le := h.stg_le; have hmSrc_eq := h.mSrc_eq; have hsched := h.sched
  have hstg0_le3 : s.mem (base + hdrPhase) ≤ 3 → s.mem (base + hdrStage) = 0 := fun hle3 => by
    by_cases hp0 : s.mem (base + hdrPhase) = 0
    · have hs' := hsched; rw [ite_eq_left hp0] at hs'; exact hs'.stg_zero
    · have hs' := hsched; rw [ite_eq_right hp0] at hs'
      by_cases hs1 : s.mem (base + hdrStage) = 1
      · have := hs'.stg_one hs1; omega
      · omega
  have hibLo_ge : base + 192 ≤ s.mem (base + hdrItemLo) := by
    by_cases hp0 : s.mem (base + hdrPhase) = 0
    · have hs' := hsched; rw [ite_eq_left hp0] at hs'; have := hs'.ibLo_eq; omega
    · have hs' := hsched; rw [ite_eq_right hp0] at hs'
      have := hs'.ibLo_eq; split_ifs at this <;> omega
  have hibHi_ge_ibLo :
      s.mem (base + hdrItemLo) ≤ s.mem (base + hdrItemHi) ∧
      (2 ≤ s.mem (base + hdrPhase) → s.mem (base + hdrItemLo) + 4 ≤ s.mem (base + hdrItemHi)) ∧
      s.mem (base + hdrQLo) ≤ s.mem (base + hdrQHi) := by
    by_cases hp0 : s.mem (base + hdrPhase) = 0
    · have hs' := hsched; rw [ite_eq_left hp0] at hs'
      have h2 := hs'.ibHi_eq; have h4 := hs'.qHi_eq
      exact ⟨by omega, fun _ => absurd hp0 (by omega), by omega⟩
    · have hs' := hsched; rw [ite_eq_right hp0] at hs'
      have hibL := hs'.ibLo_eq; have hqL := hs'.qLo_eq
      by_cases hp1 : s.mem (base + hdrPhase) = 1
      · have h1 := hs'.ph1 hp1
        have hh := h1.2.2.2.1; have hq := h1.2.2.2.2.1
        exact ⟨by omega, fun _ => absurd hp1 (by omega), by omega⟩
      · obtain ⟨hmD, hp_eq, _, _, hibH, hqH⟩ := hs'.ge2 (by omega)
        have hpad_ge : s.mem (base + hdrMSrc) ≤ s.mem (base + hdrPad) ∧
            s.mem (base + hdrMDst) ≤ s.mem (base + hdrPad) := by
          rw [hp_eq, hmSrc_eq, hmD]; exact ⟨le_max_left _ _, le_max_right _ _⟩
        have hib4 : s.mem (base + hdrItemLo) + 4 ≤ s.mem (base + hdrItemHi) := by
          rw [hibL, hibH]
          by_cases h10 : s.mem (base + hdrPhase) < 10 <;>
            by_cases hd0 : s.mem (base + hdrNDst) = 0
          · rw [ite_eq_left h10, ite_eq_left hd0]; omega
          · rw [ite_eq_left h10, ite_eq_right hd0]; omega
          · rw [ite_eq_right h10, ite_eq_left hd0]
            have hm0 : s.mem (base + hdrMDst) = 0 := by
              rw [hmD, hd0]; unfold epochMetaWordsWhp; rw [ite_eq_left (whpThreshold_pos c)]
            omega
          · rw [ite_eq_right h10, ite_eq_right hd0]; omega
        have hq_le : s.mem (base + hdrQLo) ≤ s.mem (base + hdrQHi) := by
          rw [hqL, hqH]
          by_cases h10 : s.mem (base + hdrPhase) < 10
          · rw [ite_eq_left h10]; exact le_max_left _ _
          · rw [ite_eq_right h10]; exact le_max_right _ _
        exact ⟨by omega, fun _ => hib4, hq_le⟩
  have hod_le_nSrc : s.mem (base + hdrNSrc) ≠ 0 →
      offPageDir c w (s.mem (base + hdrNSrc)) ≤ epochMetaWordsWhp c w (s.mem (base + hdrNSrc)) :=
    fun hne => by
      have hth : whpThreshold c ≤ s.mem (base + hdrNSrc) := by
        simp only [EpochCapSafe, hne, ↓reduceIte] at hsrc_safe; exact hsrc_safe.1
      have hend := offEpochEnd_eq_epochMetaWordsWhp (c := c) (w := w) hth
      unfold offEpochEnd offPageTail at hend; omega
  have hod_le_nDst : s.mem (base + hdrPhase) ≠ 0 → s.mem (base + hdrNDst) ≠ 0 →
      offPageDir c w (s.mem (base + hdrNDst)) ≤ epochMetaWordsWhp c w (s.mem (base + hdrNDst)) :=
    fun hp_nz hne => by
      have hdst_s := hdst_safe; rw [ite_eq_right hp_nz] at hdst_s
      have hth : whpThreshold c ≤ s.mem (base + hdrNDst) := by
        simp only [EpochCapSafe, hne, ↓reduceIte] at hdst_s; exact hdst_s.1
      have hend := offEpochEnd_eq_epochMetaWordsWhp (c := c) (w := w) hth
      unfold offEpochEnd offPageTail at hend; omega
  exact ⟨hstg0_le3, hibLo_ge, hibHi_ge_ibLo, hod_le_nSrc, hod_le_nDst⟩

private theorem fr_bounds_of_dualStateInv {c U V w base opTag : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s) (hop_nz : opTag ≠ 0) (u : Fin U) (v : Fin V)
    (hcard_step :
      let nLive := (Dictionary.dom s_dict).card
      let s_dict' :=
        if opTag = 1 then Function.update s_dict u (some v.val) else Function.update s_dict u none
      let nLive' := (Dictionary.dom s_dict').card
      let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
      (opTag = 1 → nLive' = if s_dict u = none then nLive + 1 else nLive) ∧
      (opTag ≠ 1 → nLive' = if s_dict u = none then nLive else nLive - 1) ∧
      nLive' ≤ nAlloc ∧ nLive ≤ nLive' + 1 ∧ nLive' ≤ nLive + 1 ∧
      nLive' ≤ U ∧ nAlloc ≤ U ∧ nAlloc ≤ nLive + 1)
    (hibHi_ge_ibLo :
      s.mem (base + hdrItemLo) ≤ s.mem (base + hdrItemHi) ∧
      (2 ≤ s.mem (base + hdrPhase) → s.mem (base + hdrItemLo) + 4 ≤ s.mem (base + hdrItemHi)) ∧
      s.mem (base + hdrQLo) ≤ s.mem (base + hdrQHi)) :
    let nLive := (Dictionary.dom s_dict).card
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val) else Function.update s_dict u none
    let nLive' := (Dictionary.dom s_dict').card
    let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
    let ph := s.mem (base + hdrPhase)
    let nSrc := s.mem (base + hdrNSrc)
    let nDst := s.mem (base + hdrNDst)
    let ibLo := s.mem (base + hdrItemLo)
    let ibHi := s.mem (base + hdrItemHi)
    let qLo := s.mem (base + hdrQLo)
    let qHi := s.mem (base + hdrQHi)
    let vB := valBits V
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    (k_grow ≤ bulkBatchWhp ∧
      s_grow.frontier ≤ base + dualPaddedWords c U V w nSrc (if ph = 0 then nSrc else nDst) nLive ∧
      (ph ≤ 2 ∨ ph = 11 → ibLo + pairStreamWords nAlloc qLo vB w ≤ s_grow.frontier) ∧
      (3 ≤ ph ∧ ph ≤ 10 → ibHi + pairStreamWords nAlloc qHi vB w ≤ s_grow.frontier) ∧
      (ph ≤ 1 → s_grow.frontier ≤ ibLo + pairStreamWords (nLive' + 1) qLo vB w) ∧
      (2 ≤ ph → s_grow.frontier ≤ ibHi + pairStreamWords (nLive' + 1) qHi vB w) ∧
      (ph = 2 →
        ((ibHi + pairStreamWords nLive' qHi vB w) - s_grow.frontier) +
          (if s_grow.frontier < ibHi + pairStreamWords nLive' qHi vB w then 1022 else 0) ≤
          (ibHi + pairStreamWords nLive qHi vB w) - s.frontier) ∧
      (ph = 11 → s_grow.frontier - (ibLo + pairStreamWords nLive' qLo vB w) ≤
        (s.frontier - (ibLo + pairStreamWords nLive qLo vB w)) + 2)) ∧
    Memory.WellFormed w s_grow := by
  dsimp only at hcard_step ⊢
  obtain ⟨hvb_mem, hvb_w, hqLo_w, hqHi_w, hibLo_pad, hibHi_pad, _, _⟩ := dualCoreInv_ib_fits h
  have hw11 := h.hw11; have hU0 := h.U_pos; have hUw := h.U_lt; have hwf_s := h.wf
  have hhdr := h.hdr; have hnL_mem := h.live_eq; have hnL_U := h.live_le; have hph_le := h.ph_le
  have hsched := h.sched; have hpad_fits_old := h.pad_fits
  have hw_pos : 0 < w := by omega
  have hu1_eq : s.mem (base + hdrU1) + 1 = U := by rw [hhdr.1]; omega
  obtain ⟨hs_prep_eq, hk_grow_eq, _⟩ :=
    prepGrowProg_eval (opTag := opTag) (u_val := u.val) hop_nz hw_pos hhdr.2.2.1
      (hu1_eq ▸ hUw.le) (by rw [hnL_mem, hu1_eq]; exact hnL_U)
  dsimp only at hs_prep_eq hk_grow_eq
  rw [hu1_eq, hnL_mem] at hs_prep_eq hk_grow_eq
  rw [hvb_mem] at hk_grow_eq
  set nLive := (Dictionary.dom s_dict).card
  set s_dict' :=
    if opTag = 1 then Function.update s_dict u (some v.val)
    else Function.update s_dict u none
  set nLive' := (Dictionary.dom s_dict').card
  set nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
  have hpw_lo_s := pairStreamWords_succ_le_add_two (n := nLive) hw_pos
    (show s.mem (base + hdrQLo) + valBits V ≤ 2 * w by omega)
  have hpw_hi_s := pairStreamWords_succ_le_add_two (n := nLive) hw_pos
    (show s.mem (base + hdrQHi) + valBits V ≤ 2 * w by omega)
  have hpw_lo_al : pairStreamWords nAlloc (s.mem (base + hdrQLo)) (valBits V) w ≤
      pairStreamWords (nLive + 1) (s.mem (base + hdrQLo)) (valBits V) w :=
    pairStreamWords_mono_n hcard_step.2.2.2.2.2.2.2
  have hpw_hi_al : pairStreamWords nAlloc (s.mem (base + hdrQHi)) (valBits V) w ≤
      pairStreamWords (nLive + 1) (s.mem (base + hdrQHi)) (valBits V) w :=
    pairStreamWords_mono_n hcard_step.2.2.2.2.2.2.2
  have hpw_lo_n' : pairStreamWords nLive (s.mem (base + hdrQLo)) (valBits V) w ≤
      pairStreamWords (nLive' + 1) (s.mem (base + hdrQLo)) (valBits V) w :=
    pairStreamWords_mono_n hcard_step.2.2.2.1
  have hpw_hi_n' : pairStreamWords nLive (s.mem (base + hdrQHi)) (valBits V) w ≤
      pairStreamWords (nLive' + 1) (s.mem (base + hdrQHi)) (valBits V) w :=
    pairStreamWords_mono_n hcard_step.2.2.2.1
  have hpw_lo_mono : pairStreamWords nLive (s.mem (base + hdrQLo)) (valBits V) w ≤
      pairStreamWords (nLive + 1) (s.mem (base + hdrQLo)) (valBits V) w :=
    pairStreamWords_mono_n (Nat.le_succ _)
  have hal_le_n'1 : nAlloc ≤ nLive' + 1 := by
    by_cases h1 : opTag = 1
    · have h1' := hcard_step.1 h1
      dsimp only [nAlloc]; rw [ite_eq_left h1]
      split_ifs at h1' <;> omega
    · dsimp only [nAlloc]; rw [ite_eq_right h1]
      exact hcard_step.2.2.2.1
  have hpw_lo_al_n' : pairStreamWords nAlloc (s.mem (base + hdrQLo)) (valBits V) w ≤
      pairStreamWords (nLive' + 1) (s.mem (base + hdrQLo)) (valBits V) w :=
    pairStreamWords_mono_n hal_le_n'1
  have hpw_hi_al_n' : pairStreamWords nAlloc (s.mem (base + hdrQHi)) (valBits V) w ≤
      pairStreamWords (nLive' + 1) (s.mem (base + hdrQHi)) (valBits V) w :=
    pairStreamWords_mono_n hal_le_n'1
  have hfr_bounds :
      let k_grow :=
        (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
      let fr' := s.frontier + k_grow
      k_grow ≤ bulkBatchWhp ∧
      fr' ≤ base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
        (if s.mem (base + hdrPhase) = 0 then s.mem (base + hdrNSrc) else s.mem (base + hdrNDst))
        nLive ∧
      (s.mem (base + hdrPhase) ≤ 2 ∨ s.mem (base + hdrPhase) = 11 →
        s.mem (base + hdrItemLo) +
          pairStreamWords nAlloc (s.mem (base + hdrQLo)) (valBits V) w ≤ fr') ∧
      (3 ≤ s.mem (base + hdrPhase) ∧ s.mem (base + hdrPhase) ≤ 10 →
        s.mem (base + hdrItemHi) +
          pairStreamWords nAlloc (s.mem (base + hdrQHi)) (valBits V) w ≤ fr') ∧
      (s.mem (base + hdrPhase) ≤ 1 →
        fr' ≤ s.mem (base + hdrItemLo) +
          pairStreamWords (nLive' + 1) (s.mem (base + hdrQLo)) (valBits V) w) ∧
      (2 ≤ s.mem (base + hdrPhase) →
        fr' ≤ s.mem (base + hdrItemHi) +
          pairStreamWords (nLive' + 1) (s.mem (base + hdrQHi)) (valBits V) w) ∧
      (s.mem (base + hdrPhase) = 2 →
        ((s.mem (base + hdrItemHi) +
            pairStreamWords nLive' (s.mem (base + hdrQHi)) (valBits V) w) - fr') +
          (if fr' < s.mem (base + hdrItemHi) +
              pairStreamWords nLive' (s.mem (base + hdrQHi)) (valBits V) w
           then 1022 else 0) ≤
          (s.mem (base + hdrItemHi) +
            pairStreamWords nLive (s.mem (base + hdrQHi)) (valBits V) w) - s.frontier) ∧
      (s.mem (base + hdrPhase) = 11 →
        fr' - (s.mem (base + hdrItemLo) +
          pairStreamWords nLive' (s.mem (base + hdrQLo)) (valBits V) w) ≤
          (s.frontier - (s.mem (base + hdrItemLo) +
            pairStreamWords nLive (s.mem (base + hdrQLo)) (valBits V) w)) + 2) := by
    dsimp only
    rw [hk_grow_eq]
    unfold bulkBatchWhp
    by_cases hp0 : s.mem (base + hdrPhase) = 0
    · have hs' := hsched; rw [ite_eq_left hp0] at hs' hibLo_pad ⊢
      rw [ite_eq_left (by omega : s.mem (base + hdrPhase) < 2)]
      have hfr_s := hs'.safe_fr
      simp only [Bool.false_eq_true, ↓reduceIte] at hfr_s
      have hfr_eq := hfr_s.2.2
      exact ⟨by omega, by omega, fun _ => by omega, fun _ => absurd hp0 (by omega),
        fun _ => by omega, fun _ => absurd hp0 (by omega),
        fun _ => absurd hp0 (by omega), fun _ => absurd hp0 (by omega)⟩
    · rw [ite_eq_right hp0] at hsched hibLo_pad hibHi_pad ⊢
      by_cases hp1 : s.mem (base + hdrPhase) = 1
      · have h1_i := hsched.ph1 hp1
        simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at h1_i
        have hfr_lo := h1_i.2.2.2.2.2.1; have hfr_hi := h1_i.2.2.2.2.2.2
        rw [ite_eq_left (by omega : s.mem (base + hdrPhase) < 2)]
        have hpad_fr : s.frontier ≤
            base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
              (s.mem (base + hdrNDst)) nLive :=
          hfr_hi.trans ((Nat.add_le_add_left (pairStreamWords_mono_n (Nat.le_succ _)) _).trans
            hibLo_pad)
        exact ⟨by omega, by omega, fun _ => by omega, fun _ => absurd hp1 (by omega),
          fun _ => by omega, fun _ => absurd hp1 (by omega),
          fun _ => absurd hp1 (by omega), fun _ => absurd hp1 (by omega)⟩
      · rw [ite_eq_right (by omega : ¬(s.mem (base + hdrPhase) < 2))]
        by_cases hp11 : s.mem (base + hdrPhase) = 11
        · rw [ite_eq_left hp11]
          have h11_i := hsched.ph11 hp11
          simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at h11_i
          obtain ⟨hfr_lo, hfr_hi⟩ := h11_i
          have hpad_fr : s.frontier ≤
              base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
                (s.mem (base + hdrNDst)) nLive :=
            hfr_hi.trans ((Nat.add_le_add_left (pairStreamWords_mono_n (Nat.le_succ _)) _).trans
              hibHi_pad)
          have hib_lo_hi := hibHi_ge_ibLo.2.1 (by omega)
          have hpw_lh : pairStreamWords nAlloc (s.mem (base + hdrQLo)) (valBits V) w ≤
              pairStreamWords (nLive' + 1) (s.mem (base + hdrQHi)) (valBits V) w :=
            (pairStreamWords_mono_q hibHi_ge_ibLo.2.2).trans hpw_hi_al_n'
          have hsh_step :
              (s.frontier +
                ((s.mem (base + hdrItemLo) +
                  pairStreamWords nAlloc (s.mem (base + hdrQLo)) (valBits V) w) - s.frontier)) -
              (s.mem (base + hdrItemLo) +
                pairStreamWords nLive' (s.mem (base + hdrQLo)) (valBits V) w) ≤
              (s.frontier - (s.mem (base + hdrItemLo) +
                pairStreamWords nLive (s.mem (base + hdrQLo)) (valBits V) w)) + 2 := by
            by_cases h1 : opTag = 1
            · by_cases hn : s_dict u = none
              · have hn1 : nLive' = nLive + 1 := by rw [hcard_step.1 h1, ite_eq_left hn]
                have hal1 : nAlloc = nLive + 1 := by
                  dsimp only [nAlloc]; rw [ite_eq_left h1, min_eq_left (by omega)]
                rw [hn1, hal1]; omega
              · have hn1 : nLive' = nLive := by rw [hcard_step.1 h1, ite_eq_right hn]
                rw [hn1]; omega
            · have hal0 : nAlloc = nLive := by dsimp only [nAlloc]; rw [ite_eq_right h1]
              have hpw_n'_s : pairStreamWords nLive (s.mem (base + hdrQLo)) (valBits V) w ≤
                  pairStreamWords nLive' (s.mem (base + hdrQLo)) (valBits V) w + 2 :=
                (pairStreamWords_mono_n hcard_step.2.2.2.1).trans
                  (pairStreamWords_succ_le_add_two hw_pos (by omega))
              rw [hal0]; omega
          exact ⟨by omega, by omega,
            fun _ => by omega, fun _ => absurd hp11 (by omega),
            fun _ => absurd hp11 (by omega), fun _ => by omega,
            fun _ => absurd hp11 (by omega), fun _ => hsh_step⟩
        · rw [ite_eq_right hp11]
          by_cases hp2 : s.mem (base + hdrPhase) = 2
          · rw [ite_eq_left hp2]
            have h2_i := hsched.ph2 hp2
            simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at h2_i
            obtain ⟨_, hfr_lo, hfr_hi⟩ := h2_i
            have hib4 := hibHi_ge_ibLo.2.1 (by omega)
            have hpw_q := pairStreamWords_mono_q (n := nAlloc) (vb := valBits V) (w := w)
              hibHi_ge_ibLo.2.2
            have hpad_fr : s.frontier ≤
                base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
                  (s.mem (base + hdrNDst)) nLive :=
              hfr_hi.trans ((Nat.add_le_add_left (pairStreamWords_mono_n (Nat.le_succ _)) _).trans
                hibHi_pad)
            have hg_step :
                ((s.mem (base + hdrItemHi) +
                    pairStreamWords nLive' (s.mem (base + hdrQHi)) (valBits V) w) -
                  (s.frontier +
                    min ((s.mem (base + hdrItemHi) +
                      pairStreamWords nAlloc (s.mem (base + hdrQHi)) (valBits V) w) - s.frontier)
                      1024)) +
                (if s.frontier +
                    min ((s.mem (base + hdrItemHi) +
                      pairStreamWords nAlloc (s.mem (base + hdrQHi)) (valBits V) w) - s.frontier)
                      1024 <
                    s.mem (base + hdrItemHi) +
                      pairStreamWords nLive' (s.mem (base + hdrQHi)) (valBits V) w
                 then 1022 else 0) ≤
                (s.mem (base + hdrItemHi) +
                  pairStreamWords nLive (s.mem (base + hdrQHi)) (valBits V) w) - s.frontier := by
              have hpw_le_al := pairStreamWords_mono_n (qb := s.mem (base + hdrQHi))
                (vb := valBits V) (w := w) hcard_step.2.2.1
              have hpw_n'_2 : pairStreamWords nLive' (s.mem (base + hdrQHi)) (valBits V) w ≤
                  pairStreamWords nLive (s.mem (base + hdrQHi)) (valBits V) w + 2 :=
                (pairStreamWords_mono_n hcard_step.2.2.2.2.1).trans hpw_hi_s
              dsimp only [Nat.min_def]; split_ifs <;> omega
            exact ⟨min_le_right _ _,
              by dsimp only [Nat.min_def]; split_ifs <;> omega,
              fun _ => by dsimp only [Nat.min_def]; split_ifs <;> omega,
              fun _ => absurd hp2 (by omega), fun _ => absurd hp2 (by omega),
              fun _ => by dsimp only [Nat.min_def]; split_ifs <;> omega,
              fun _ => hg_step, fun _ => absurd hp2 (by omega)⟩
          · rw [ite_eq_right hp2]
            have h3_10_i := hsched.ph3_10 ⟨by omega, by omega⟩
            simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at h3_10_i
            obtain ⟨hfr_lo, hfr_hi⟩ := h3_10_i
            have hpad_fr : s.frontier ≤
                base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
                  (s.mem (base + hdrNDst)) nLive :=
              hfr_hi.trans ((Nat.add_le_add_left (pairStreamWords_mono_n (Nat.le_succ _)) _).trans
                hibHi_pad)
            exact ⟨by omega, by omega, fun hh => by rcases hh with hh | hh <;> omega,
              fun _ => by omega, fun hh => absurd hh (by omega), fun _ => by omega,
              fun hh => absurd hh (by omega), fun hh => absurd hh (by omega)⟩
  refine ⟨hfr_bounds, ⟨lt_of_le_of_lt hfr_bounds.2.1 hpad_fits_old, fun a => ?_⟩⟩
  dsimp only
  have hs_mem := congrArg Memory.State.mem hs_prep_eq
  dsimp only at hs_mem; rw [hs_mem]
  split_ifs
  · by_cases ha1 : a = base + hdrPBase1 + 60
    · subst ha1; rw [Function.update_self]; exact lt_of_le_of_lt hcard_step.2.2.2.2.2.2.1 hUw
    · rw [Function.update_of_ne ha1]
      by_cases ha0 : a = base + hdrPBase0 + 60
      · subst ha0; rw [Function.update_self]; exact lt_of_le_of_lt hcard_step.2.2.2.2.2.2.1 hUw
      · rw [Function.update_of_ne ha0]; exact hwf_s.2 a
  · exact hwf_s.2 a

private theorem slot_bounds_of_dualStateInv {c U V w base opTag : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s) (u : Fin U) (v : Fin V)
    (hcard_step :
      let nLive := (Dictionary.dom s_dict).card
      let s_dict' :=
        if opTag = 1 then Function.update s_dict u (some v.val) else Function.update s_dict u none
      let nLive' := (Dictionary.dom s_dict').card
      let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
      (opTag = 1 → nLive' = if s_dict u = none then nLive + 1 else nLive) ∧
      (opTag ≠ 1 → nLive' = if s_dict u = none then nLive else nLive - 1) ∧
      nLive' ≤ nAlloc ∧ nLive ≤ nLive' + 1 ∧ nLive' ≤ nLive + 1 ∧
      nLive' ≤ U ∧ nAlloc ≤ U ∧ nAlloc ≤ nLive + 1)
    (hstg0_le3 : s.mem (base + hdrPhase) ≤ 3 → s.mem (base + hdrStage) = 0)
    (hibLo_ge : base + 192 ≤ s.mem (base + hdrItemLo))
    (hibHi_ge_ibLo :
      s.mem (base + hdrItemLo) ≤ s.mem (base + hdrItemHi) ∧
      (2 ≤ s.mem (base + hdrPhase) → s.mem (base + hdrItemLo) + 4 ≤ s.mem (base + hdrItemHi)) ∧
      s.mem (base + hdrQLo) ≤ s.mem (base + hdrQHi))
    (hod_le_nSrc : s.mem (base + hdrNSrc) ≠ 0 →
      offPageDir c w (s.mem (base + hdrNSrc)) ≤ epochMetaWordsWhp c w (s.mem (base + hdrNSrc)))
    (hod_le_nDst : s.mem (base + hdrPhase) ≠ 0 → s.mem (base + hdrNDst) ≠ 0 →
      offPageDir c w (s.mem (base + hdrNDst)) ≤ epochMetaWordsWhp c w (s.mem (base + hdrNDst))) :
    let nLive := (Dictionary.dom s_dict).card
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val) else Function.update s_dict u none
    let nLive' := (Dictionary.dom s_dict').card
    let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
    let ph := s.mem (base + hdrPhase)
    let stg := s.mem (base + hdrStage)
    let nSrc := s.mem (base + hdrNSrc)
    let nDst := s.mem (base + hdrNDst)
    let pad := s.mem (base + hdrPad)
    let ibLo := s.mem (base + hdrItemLo)
    let ibHi := s.mem (base + hdrItemHi)
    let qHi := s.mem (base + hdrQHi)
    let nHost := if nDst = 0 then nSrc else nDst
    let mbHost := if nDst = 0 then base + 192
      else if stg = 0 then base + 192 + pad else base + 192
    let pgHost := hostPageLayout c w nHost mbHost ibHi qHi (valBits V) nLive
    let capSrc := if stg = 0 then nSrc else nDst
    let mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
      else base + 192 + pad
    let mbDst := if ph < 10 then
        (if nDst = 0 then base + hdrSmallMeta1
         else if stg = 0 then base + 192 + pad else base + 192)
      else
        (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
    (8 ≤ ph → ph ≤ 9 →
      nAlloc ≤ (pgHost.maxPages - 2) * pgHost.pgB ∧
      nLive' ≤ (pgHost.maxPages - 2) * pgHost.pgB) ∧
    (ph ≤ 8 → L.slotSrc.nCap = 0 → (liveDom L.slotSrc.s_abs).card ≤ 2 * whpThreshold c) ∧
    (8 ≤ ph → L.slotDst.nCap = 0 → (liveDom L.slotDst.s_abs).card ≤ 2 * whpThreshold c) ∧
    (ph ≤ 8 →
      L.slotSrc.nCap = capSrc ∧
      ((L.slotSrc.nCap = 0 ∧ (mbSrc = base + hdrSmallMeta0 ∨ mbSrc = base + hdrSmallMeta1)) ∨
        (L.slotSrc.nCap ≠ 0 ∧ base + 192 ≤ mbSrc)) ∧
      (ph ≤ 3 → mbSrc + (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤ ibLo) ∧
      (3 ≤ ph → mbSrc + (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤ ibHi)) ∧
    (8 ≤ ph →
      L.slotDst.nCap = nDst ∧
      ((L.slotDst.nCap = 0 ∧ (mbDst = base + hdrSmallMeta0 ∨ mbDst = base + hdrSmallMeta1)) ∨
        (L.slotDst.nCap ≠ 0 ∧ base + 192 ≤ mbDst)) ∧
      (ph ≤ 10 →
        mbDst + (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤ ibHi) ∧
      (10 ≤ ph →
        mbDst + (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤ ibLo)) := by
  dsimp only at hcard_step ⊢
  obtain ⟨hsrc_safe, hdst_safe⟩ := dualCoreInv_cap_safe h
  have hb192 := h.base_fr; have hmSrc_eq := h.mSrc_eq; have hsched := h.sched
  have hsl_le7 := h.sl_le7; have hsl_8 := h.sl_8; have hsl_ge9 := h.sl_ge9
  dsimp only [dualCapSrc, dualMbSrc, dualPSrc, dualMbDst, dualPDst, dualNHost, dualMbHost,
    dualPgHost] at hsl_le7 hsl_8 hsl_ge9
  set nLive := (Dictionary.dom s_dict).card
  set s_dict' :=
    if opTag = 1 then Function.update s_dict u (some v.val)
    else Function.update s_dict u none
  set nLive' := (Dictionary.dom s_dict').card
  set nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
  refine ⟨fun h8 h9 => ?_, fun hle8 h0 => ?_, fun hge8 h0 => ?_, ?_, ?_⟩
  · set nHost := if s.mem (base + hdrNDst) = 0 then s.mem (base + hdrNSrc)
      else s.mem (base + hdrNDst)
    have hs' := hsched; rw [ite_eq_right (by omega : s.mem (base + hdrPhase) ≠ 0)] at hs'
    have hd_hi := hs'.drift_hi; have hd_lo := hs'.drift_lo
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hd_hi hd_lo
    have hel := hs'.budget.2.2
    have har := active_rebuild_safe hs'.post_trig hs'.trig_cap (nCur := nAlloc) (d := L.elapsed + 1)
      (by omega) (by omega) (by omega) hcard_step.2.2.2.2.2.2.1
    have hnH_ge : nAlloc ≤ nHost + 1 := by
      dsimp only [nHost]
      by_cases hd0 : s.mem (base + hdrNDst) = 0
      · rw [ite_eq_left hd0]
        have hs_pos := (hs'.nDst_zero hd0).1
        have hs_c := har.2.1
        simp only [EpochCapSafe, hs_pos.ne', ↓reduceIte] at hs_c; omega
      · rw [ite_eq_right hd0]
        have hd_c := har.2.2.1
        simp only [EpochCapSafe, hd0, ↓reduceIte] at hd_c; omega
    dsimp only [hostPageLayout, epochPageArenaLayout]
    have hpg32 : 32 ≤ pageSizeWhp nHost := le_max_left 32 _
    have hdiv := Nat.div_add_mod nHost (pageSizeWhp nHost)
    have hmod : nHost % pageSizeWhp nHost < pageSizeWhp nHost := Nat.mod_lt _ (by omega)
    rw [Nat.add_sub_assoc (by decide : 2 ≤ 4)]
    change nAlloc ≤ (nHost / pageSizeWhp nHost + 2) * pageSizeWhp nHost ∧
      nLive' ≤ (nHost / pageSizeWhp nHost + 2) * pageSizeWhp nHost
    have hmul : (nHost / pageSizeWhp nHost + 2) * pageSizeWhp nHost =
        pageSizeWhp nHost * (nHost / pageSizeWhp nHost) + 2 * pageSizeWhp nHost := by
      rw [Nat.add_mul, Nat.mul_comm _ (pageSizeWhp nHost)]
    have hle_al := hcard_step.2.2.1
    omega
  · by_cases hle7 : s.mem (base + hdrPhase) ≤ 7
    · obtain ⟨hcap, hdict, _, _⟩ := hsl_le7 hle7
      have hcard : (liveDom L.slotSrc.s_abs).card = nLive := by rw [← dom_toDictState_card, hdict]
      rw [hcard]
      by_cases hst0 : s.mem (base + hdrStage) = 0
      · rw [hcap, ite_eq_left hst0] at h0
        simp only [EpochCapSafe, h0, ↓reduceIte] at hsrc_safe; exact hsrc_safe.1.le
      · have hph_nz : s.mem (base + hdrPhase) ≠ 0 := fun hp0 => hst0 (hstg0_le3 (by omega))
        rw [ite_eq_right hph_nz] at hdst_safe
        rw [hcap, ite_eq_right hst0] at h0
        simp only [EpochCapSafe, h0, ↓reduceIte] at hdst_safe; exact hdst_safe.1.le
    · have h8 : s.mem (base + hdrPhase) = 8 := by omega
      obtain ⟨hcap, _, hdj, hdict, _, _⟩ := hsl_8 h8
      have hle_tot : (liveDom L.slotSrc.s_abs).card ≤ nLive := by
        dsimp only [nLive]; rw [← hdict, dom_toDictState_card, liveDom_orOpt_card hdj]; omega
      by_cases hst0 : s.mem (base + hdrStage) = 0
      · rw [hcap, ite_eq_left hst0] at h0
        simp only [EpochCapSafe, h0, ↓reduceIte] at hsrc_safe; omega
      · rw [ite_eq_right (by omega : s.mem (base + hdrPhase) ≠ 0)] at hdst_safe
        rw [hcap, ite_eq_right hst0] at h0
        simp only [EpochCapSafe, h0, ↓reduceIte] at hdst_safe; omega
  · by_cases h8 : s.mem (base + hdrPhase) = 8
    · obtain ⟨_, hcap, hdj, hdict, _, _⟩ := hsl_8 h8
      have hle_tot : (liveDom L.slotDst.s_abs).card ≤ nLive := by
        dsimp only [nLive]; rw [← hdict, dom_toDictState_card, liveDom_orOpt_card hdj]; omega
      have hd0 : s.mem (base + hdrNDst) = 0 := hcap.symm.trans h0
      rw [ite_eq_right (by omega : s.mem (base + hdrPhase) ≠ 0), hd0] at hdst_safe
      simp only [EpochCapSafe, ↓reduceIte] at hdst_safe; omega
    · obtain ⟨hcap, hdict, _, _⟩ := hsl_ge9 (by omega)
      have hcard : (liveDom L.slotDst.s_abs).card = nLive := by rw [← dom_toDictState_card, hdict]
      have hd0 : s.mem (base + hdrNDst) = 0 := hcap.symm.trans h0
      rw [ite_eq_right (by omega : s.mem (base + hdrPhase) ≠ 0), hd0] at hdst_safe
      simp only [EpochCapSafe, ↓reduceIte] at hdst_safe; omega
  · intro hle8
    have hcap_s : L.slotSrc.nCap =
        if s.mem (base + hdrStage) = 0 then s.mem (base + hdrNSrc) else s.mem (base + hdrNDst) :=
      if h8 : s.mem (base + hdrPhase) = 8 then (hsl_8 h8).1 else (hsl_le7 (by omega)).1
    have hpos_s : (L.slotSrc.nCap = 0 ∧
        ((if s.mem (base + hdrStage) = 0 then
            if s.mem (base + hdrNSrc) = 0 then base + hdrSmallMeta0 else base + 192
          else base + 192 + s.mem (base + hdrPad)) = base + hdrSmallMeta0 ∨
         (if s.mem (base + hdrStage) = 0 then
            if s.mem (base + hdrNSrc) = 0 then base + hdrSmallMeta0 else base + 192
          else base + 192 + s.mem (base + hdrPad)) = base + hdrSmallMeta1)) ∨
        (L.slotSrc.nCap ≠ 0 ∧ base + 192 ≤
          (if s.mem (base + hdrStage) = 0 then
             if s.mem (base + hdrNSrc) = 0 then base + hdrSmallMeta0 else base + 192
           else base + 192 + s.mem (base + hdrPad))) := by
      rw [hcap_s]
      by_cases hst0 : s.mem (base + hdrStage) = 0
      · rw [ite_eq_left hst0, ite_eq_left hst0]
        by_cases hnS0 : s.mem (base + hdrNSrc) = 0
        · rw [ite_eq_left hnS0]; exact Or.inl ⟨hnS0, Or.inl rfl⟩
        · rw [ite_eq_right hnS0]; exact Or.inr ⟨hnS0, le_rfl⟩
      · rw [ite_eq_right hst0, ite_eq_right hst0]
        have hp_nz : s.mem (base + hdrPhase) ≠ 0 := fun hp0 => hst0 (hstg0_le3 (by omega))
        have hs' := hsched; rw [ite_eq_right hp_nz] at hs'
        have hd_pos := (hs'.stg_one (by have := h.stg_le; omega)).1
        exact Or.inr ⟨hd_pos.ne', by omega⟩
    have hlo : s.mem (base + hdrPhase) ≤ 3 →
        (if s.mem (base + hdrStage) = 0 then
           if s.mem (base + hdrNSrc) = 0 then base + hdrSmallMeta0 else base + 192
         else base + 192 + s.mem (base + hdrPad)) +
          (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤
          s.mem (base + hdrItemLo) := by
      intro hle3
      have hst0 := hstg0_le3 hle3
      rw [hcap_s, ite_eq_left hst0, ite_eq_left hst0]
      by_cases hnS0 : s.mem (base + hdrNSrc) = 0
      · rw [ite_eq_left hnS0, ite_eq_left hnS0]; unfold hdrSmallMeta0; omega
      · rw [ite_eq_right hnS0, ite_eq_right hnS0]
        have hod := hod_le_nSrc hnS0
        have hibL_eq : s.mem (base + hdrItemLo) = base + 192 + s.mem (base + hdrMSrc) := by
          by_cases hp0 : s.mem (base + hdrPhase) = 0
          · have hs' := hsched; rw [ite_eq_left hp0] at hs'; exact hs'.ibLo_eq
          · have hs' := hsched; rw [ite_eq_right hp0] at hs'
            rw [hs'.ibLo_eq, ite_eq_left (by omega)]
        rw [hibL_eq, hmSrc_eq]; omega
    have hhi : 3 ≤ s.mem (base + hdrPhase) →
        (if s.mem (base + hdrStage) = 0 then
           if s.mem (base + hdrNSrc) = 0 then base + hdrSmallMeta0 else base + 192
         else base + 192 + s.mem (base + hdrPad)) +
          (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤
          s.mem (base + hdrItemHi) := by
      intro hge3
      by_cases h3 : s.mem (base + hdrPhase) = 3
      · exact (hlo (by omega)).trans hibHi_ge_ibLo.1
      · have hs' := hsched; rw [ite_eq_right (by omega : s.mem (base + hdrPhase) ≠ 0)] at hs'
        obtain ⟨hmD, hp_eq, _, _, hibH, _⟩ := hs'.ge2 (by omega)
        have hp_ge : s.mem (base + hdrMSrc) ≤ s.mem (base + hdrPad) ∧
            s.mem (base + hdrMDst) ≤ s.mem (base + hdrPad) := by
          rw [hp_eq, hmSrc_eq, hmD]; exact ⟨le_max_left _ _, le_max_right _ _⟩
        rw [hcap_s]
        by_cases hst0 : s.mem (base + hdrStage) = 0
        · rw [ite_eq_left hst0, ite_eq_left hst0]
          by_cases hnS0 : s.mem (base + hdrNSrc) = 0
          · rw [ite_eq_left hnS0, ite_eq_left hnS0]; unfold hdrSmallMeta0
            have := hibHi_ge_ibLo.1; omega
          · rw [ite_eq_right hnS0, ite_eq_right hnS0]
            have hod := hod_le_nSrc hnS0
            rw [hibH]; split_ifs <;> omega
        · rw [ite_eq_right hst0, ite_eq_right hst0]
          have hd_pos := (hs'.stg_one (by have := h.stg_le; omega)).1
          rw [ite_eq_right hd_pos.ne', hibH, ite_eq_right hd_pos.ne']
          have hod := hod_le_nDst (by omega) hd_pos.ne'
          omega
    exact ⟨hcap_s, hpos_s, hlo, hhi⟩
  · intro hge8
    have hcap_d : L.slotDst.nCap = s.mem (base + hdrNDst) :=
      if h8 : s.mem (base + hdrPhase) = 8 then (hsl_8 h8).2.1 else (hsl_ge9 (by omega)).1
    have hs' := hsched; rw [ite_eq_right (by omega : s.mem (base + hdrPhase) ≠ 0)] at hs'
    obtain ⟨hmD, hp_eq, _, _, hibH, _⟩ := hs'.ge2 (by omega)
    have hp_ge : s.mem (base + hdrMDst) ≤ s.mem (base + hdrPad) := by
      rw [hp_eq, hmSrc_eq, hmD]; exact le_max_right _ _
    have hpos_d : (L.slotDst.nCap = 0 ∧
        ((if s.mem (base + hdrPhase) < 10 then
            if s.mem (base + hdrNDst) = 0 then base + hdrSmallMeta1
            else if s.mem (base + hdrStage) = 0 then base + 192 + s.mem (base + hdrPad)
            else base + 192
          else if s.mem (base + hdrNDst) = 0 then base + hdrSmallMeta0 else base + 192) =
            base + hdrSmallMeta0 ∨
         (if s.mem (base + hdrPhase) < 10 then
            if s.mem (base + hdrNDst) = 0 then base + hdrSmallMeta1
            else if s.mem (base + hdrStage) = 0 then base + 192 + s.mem (base + hdrPad)
            else base + 192
          else if s.mem (base + hdrNDst) = 0 then base + hdrSmallMeta0 else base + 192) =
            base + hdrSmallMeta1)) ∨
        (L.slotDst.nCap ≠ 0 ∧ base + 192 ≤
          (if s.mem (base + hdrPhase) < 10 then
             if s.mem (base + hdrNDst) = 0 then base + hdrSmallMeta1
             else if s.mem (base + hdrStage) = 0 then base + 192 + s.mem (base + hdrPad)
             else base + 192
           else if s.mem (base + hdrNDst) = 0 then base + hdrSmallMeta0 else base + 192)) := by
      rw [hcap_d]
      by_cases hnD0 : s.mem (base + hdrNDst) = 0
      · split_ifs <;> [exact Or.inl ⟨hnD0, Or.inr rfl⟩; exact Or.inl ⟨hnD0, Or.inl rfl⟩]
      · split_ifs <;> exact Or.inr ⟨hnD0, by omega⟩
    have hlo : 10 ≤ s.mem (base + hdrPhase) →
        (if s.mem (base + hdrPhase) < 10 then
           if s.mem (base + hdrNDst) = 0 then base + hdrSmallMeta1
           else if s.mem (base + hdrStage) = 0 then base + 192 + s.mem (base + hdrPad)
           else base + 192
         else if s.mem (base + hdrNDst) = 0 then base + hdrSmallMeta0 else base + 192) +
          (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤
          s.mem (base + hdrItemLo) := by
      intro h10
      rw [hcap_d, ite_eq_right (by omega : ¬(s.mem (base + hdrPhase) < 10))]
      have hibL_eq : s.mem (base + hdrItemLo) = base + 192 + s.mem (base + hdrMDst) := by
        rw [hs'.ibLo_eq, ite_eq_right (by omega)]
      by_cases hnD0 : s.mem (base + hdrNDst) = 0
      · rw [ite_eq_left hnD0, ite_eq_left hnD0]; unfold hdrSmallMeta0; omega
      · rw [ite_eq_right hnD0, ite_eq_right hnD0, hibL_eq, hmD]
        have hod := hod_le_nDst (by omega) hnD0; omega
    have hhi : s.mem (base + hdrPhase) ≤ 10 →
        (if s.mem (base + hdrPhase) < 10 then
           if s.mem (base + hdrNDst) = 0 then base + hdrSmallMeta1
           else if s.mem (base + hdrStage) = 0 then base + 192 + s.mem (base + hdrPad)
           else base + 192
         else if s.mem (base + hdrNDst) = 0 then base + hdrSmallMeta0 else base + 192) +
          (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤
          s.mem (base + hdrItemHi) := by
      intro hle10
      by_cases h10 : s.mem (base + hdrPhase) = 10
      · exact (hlo (by omega)).trans hibHi_ge_ibLo.1
      · rw [hcap_d, ite_eq_left (by omega : s.mem (base + hdrPhase) < 10)]
        by_cases hnD0 : s.mem (base + hdrNDst) = 0
        · rw [ite_eq_left hnD0, ite_eq_left hnD0]; unfold hdrSmallMeta1
          have := hibHi_ge_ibLo.1; omega
        · rw [ite_eq_right hnD0, ite_eq_right hnD0, hibH, ite_eq_right hnD0]
          have hod := hod_le_nDst (by omega) hnD0
          split_ifs <;> omega
    exact ⟨hcap_d, hpos_d, hhi, hlo⟩

/-- Extracts `FGSetup` from a resting `DualStateInv` state. -/
theorem fgSetup_of_dualStateInv {c U V w base opTag : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s) (hop_nz : opTag ≠ 0) (u : Fin U) (v : Fin V) :
    FGSetup c U V w base opTag u v s_dict L s := by
  obtain ⟨hsrc_safe, hdst_safe⟩ := dualCoreInv_cap_safe h
  have hlen_bounds := evs_len_le_four_mul_of_dualStateInv h
  obtain ⟨hvb_mem, hvb_w, hqLo_w, hqHi_w, _, _, _, _⟩ := dualCoreInv_ib_fits h
  have hw11 := h.hw11; have hU0 := h.U_pos; have hUw := h.U_lt; have hb192 := h.base_fr
  have hhdr := h.hdr; have hnL_mem := h.live_eq; have hnL_U := h.live_le
  have hsched := h.sched
  have hw_pos : 0 < w := by omega
  have hu1_eq : s.mem (base + hdrU1) + 1 = U := by rw [hhdr.1]; omega
  obtain ⟨hs_prep_eq, _, hmc_pg⟩ :=
    prepGrowProg_eval (opTag := opTag) (u_val := u.val) hop_nz hw_pos hhdr.2.2.1
      (hu1_eq ▸ hUw.le) (by rw [hnL_mem, hu1_eq]; exact hnL_U)
  dsimp only at hs_prep_eq
  rw [hu1_eq, hnL_mem] at hs_prep_eq
  have hs_prep_fr :
      ((Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))).frontier =
        s.frontier := by
    rw [hs_prep_eq]
  have hcard_step := card_step_of_dualStateInv (opTag := opTag) h u v
  dsimp only at hcard_step
  obtain ⟨hstg0_le3, hibLo_ge, hibHi_ge_ibLo, hod_le_nSrc, hod_le_nDst⟩ :=
    layout_step_of_dualStateInv h
  obtain ⟨hfr_bounds, hwf_grow⟩ :=
    fr_bounds_of_dualStateInv h hop_nz u v hcard_step hibHi_ge_ibLo
  obtain ⟨hpgHost_cap, hsm_src, hsm_dst, hmbSrc_info, hmbDst_info⟩ :=
    slot_bounds_of_dualStateInv h u v hcard_step hstg0_le3 hibLo_ge hibHi_ge_ibLo
      hod_le_nSrc hod_le_nDst
  have hpre_pg : PrepGrowPre w (((base, s.frontier), opTag), u.val) s :=
    Or.inr ⟨hw11, hhdr.2.2.1, hb192, hvb_mem ▸ hvb_w, hqLo_w, hqHi_w,
      hu1_eq ▸ hUw, by rwa [hnL_mem, hvb_mem], by rwa [hnL_mem, hvb_mem]⟩
  set nLive := (Dictionary.dom s_dict).card
  set nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
  set s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
  set k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
  set s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  have hgrow_below : ∀ addr < base, s_prep.mem addr = s.mem addr := fun addr ha => by
    rw [hs_prep_eq]; dsimp only
    split_ifs
    · unfold hdrPBase0 hdrPBase1
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · rfl
  have hgrow_low : ∀ off < 60, s_prep.mem (base + off) = s.mem (base + off) := fun off hoff => by
    rw [hs_prep_eq]; dsimp only
    split_ifs
    · unfold hdrPBase0 hdrPBase1
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · rfl
  have hgrow_ge192 : ∀ addr, base + 192 ≤ addr → s_prep.mem addr = s.mem addr := fun addr ha => by
    rw [hs_prep_eq]; dsimp only
    split_ifs
    · unfold hdrPBase0 hdrPBase1
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · rfl
  have hgrow_out_all : ∀ a,
      (a = base + hdrSplit ∨ (base + 48 ≤ a ∧ a < base + 64) ∨ base + 192 ≤ a) →
      s_grow.mem a = s.mem a := fun a ha => by
    dsimp only [s_grow]; rw [hs_prep_eq]; dsimp only
    split_ifs
    · simp only [hdrPBase0, hdrPBase1, hdrSplit] at ha ⊢
      rw [Function.update_of_ne (by rcases ha with rfl | _ | _ <;> omega),
        Function.update_of_ne (by rcases ha with rfl | _ | _ <;> omega)]
    · rfl
  have hgrow_p_rest : ∀ pB, (pB = base + hdrPBase0 ∨ pB = base + hdrPBase1) →
      ∀ a, pB ≤ a → a < pB + 64 → a ≠ pB + 60 → s_prep.mem a = s.mem a := by
    intro pB hpB a ha1 ha2 hne
    rw [hs_prep_eq]; dsimp only
    split_ifs
    · rcases hpB with rfl | rfl <;> simp only [hdrPBase0, hdrPBase1] at ha1 ha2 hne ⊢ <;>
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · rfl
  have hlift_grow_slot :
      ∀ {pB mb slack : ℕ} {io0 : SlotIoLayout} {dr : Bool} {sl : SlotLatent c U V},
        EpochSlotInv c U V w s.frontier pB mb io0 slack dr sl s.mem →
        io0.pgL.nCap = nLive →
        (pB = base + hdrPBase0 ∨ pB = base + hdrPBase1) →
        ((sl.nCap = 0 ∧ (mb = base + hdrSmallMeta0 ∨ mb = base + hdrSmallMeta1)) ∨
          (sl.nCap ≠ 0 ∧ base + 192 ≤ mb)) →
        ((io0.usePaged = 0 → io0.sideBit ≠ 0 →
            io0.pgL.metaBase = base + hdrSplit ∧ base + 192 ≤ io0.pgL.offDir) ∧
          (io0.usePaged ≠ 0 → base + 192 ≤ io0.pgL.metaBase) ∧
          base + 192 ≤ io0.pgL.itemBase) →
        (io0.usePaged = 0 → io0.sideBit = 0 →
          io0.pgL.itemBase + pairStreamWords nAlloc io0.pgL.qBits io0.pgL.vBits io0.pgL.w ≤
            s_grow.frontier) →
        (io0.usePaged = 0 → io0.sideBit ≠ 0 →
          io0.pgL.itemBase + pairStreamWords nAlloc io0.pgL.offTail io0.pgL.vBits io0.pgL.w ≤
            s_grow.frontier) →
        (io0.usePaged ≠ 0 →
          nAlloc ≤ (io0.pgL.maxPages - 2) * io0.pgL.pgB ∧
          io0.pgL.itemBase + pairStreamWords nAlloc io0.pgL.qBits io0.pgL.vBits io0.pgL.w ≤
            s_grow.frontier) →
        (mb + (if sl.nCap = 0 then 2 else offPageDir c w sl.nCap) ≤ io0.pgL.itemBase ∧
          (io0.usePaged = 0 → io0.sideBit ≠ 0 →
            mb + (if sl.nCap = 0 then 2 else offPageDir c w sl.nCap) ≤ io0.pgL.offDir)) →
        EpochSlotInv c U V w s_grow.frontier pB mb (io0.withNCap nAlloc) slack dr sl
          s_grow.mem := by
    intro pB mb slack io0 dr sl hsl hnc_eq hpB hmb_pos hio_pos hfd hfs hfp hm_ib
    by_cases h1 : opTag = 1
    · have hio_s := hsl.io_stateInv
      have hnc_le_al : nLive ≤ nAlloc := by
        dsimp only [nAlloc]; rw [ite_eq_left h1]; exact le_min (Nat.le_succ _) hnL_U
      have hns_al : s.mem (mb + 1) ≤ nAlloc := by
        unfold SlotIoLayout.StateInv at hio_s
        by_cases hup : io0.usePaged = 0
        · rw [ite_eq_left hup] at hio_s; have := hio_s.1; omega
        · rw [ite_eq_right hup] at hio_s
          have hti := hio_s.2.2.2.1; have hvl := hio_s.2.2.2.2.1
          unfold PagePairState.totalItems at hti
          cases hsd : io0.side <;> rw [hsd] at hvl <;> omega
      have hpg_al : io0.usePaged ≠ 0 → (extractPagePair io0.pgL s.mem).totalItems ≤ nAlloc := by
        intro hup; unfold SlotIoLayout.StateInv at hio_s
        rw [ite_eq_right hup] at hio_s
        exact hio_s.2.2.2.1.trans (hnc_eq ▸ hnc_le_al)
      have hp60 : s_grow.mem (pB + 60) = nAlloc := by
        dsimp only [s_grow]; rw [hs_prep_eq]; dsimp only; rw [ite_eq_left h1]
        rcases hpB with rfl | rfl <;> unfold hdrPBase0 hdrPBase1
        · rw [Function.update_of_ne (by omega), Function.update_self]
        · rw [Function.update_self]
      exact EpochSlotInv.lift_sync (base := base) hsl (Nat.le_add_right s.frontier k_grow)
        (lt_of_le_of_lt hcard_step.2.2.2.2.2.2.1 hUw)
        hpB hmb_pos hio_pos hfd hfs hfp hm_ib hns_al hpg_al hp60
        (hgrow_p_rest pB hpB) hgrow_out_all
    · have hal_eq : nAlloc = nLive := by dsimp only [nAlloc]; rw [ite_eq_right h1]
      have hmem_eq : s_grow.mem = s.mem := by
        dsimp only [s_grow]; rw [hs_prep_eq]; dsimp only; rw [ite_eq_right h1]
      have hio_eq : io0.withNCap nAlloc = io0 := by
        rcases io0 with ⟨up, sb, pg⟩; dsimp only [SlotIoLayout.withNCap] at hnc_eq ⊢
        rw [hal_eq, ← hnc_eq]
      rw [hmem_eq, hio_eq]
      exact hsl.mono_frontier (Nat.le_add_right s.frontier k_grow)
  exact
    { src_safe := hsrc_safe
      dst_safe := hdst_safe
      len_bounds := hlen_bounds
      card_step := hcard_step
      pre_pg := hpre_pg
      s_prep_fr := hs_prep_fr
      mc_pg := hmc_pg
      stg0_le3 := hstg0_le3
      ibLo_ge := hibLo_ge
      ibHi_ge_ibLo := hibHi_ge_ibLo
      nDst0_sched := fun hp0 => by
        have hs' := hsched; rw [ite_eq_right hp0] at hs'; exact hs'.nDst_zero
      ge2_sched := fun hp0 => by
        have hs' := hsched; rw [ite_eq_right hp0] at hs'; exact hs'.ge2
      fr_bounds := hfr_bounds
      wf_grow := hwf_grow
      grow_below := hgrow_below
      grow_low := hgrow_low
      grow_ge192 := hgrow_ge192
      grow_p_rest := hgrow_p_rest
      lift_grow_slot := hlift_grow_slot
      od_le_nSrc := hod_le_nSrc
      od_le_nDst := hod_le_nDst
      pgHost_cap := hpgHost_cap
      sm_src := hsm_src
      sm_dst := hsm_dst
      mbSrc_info := hmbSrc_info
      mbDst_info := hmbDst_info
      fr_n' :=
        ⟨fun hh => (Nat.add_le_add_left (pairStreamWords_mono_n hcard_step.2.2.1) _).trans
            (hfr_bounds.2.2.1 hh),
         fun hh => (Nat.add_le_add_left (pairStreamWords_mono_n hcard_step.2.2.1) _).trans
            (hfr_bounds.2.2.2.1 hh)⟩ }

/-- Post-condition of `userMutateProg` shared across phases `0..11`. -/
abbrev FGStepOut (c U V w base opTag v_val : ℕ) (u : Fin U) (v : Fin V)
    (s_dict : Dictionary.State U) (L : DualLatent c U V) (s : Memory.State) : Prop :=
  let nLive := (Dictionary.dom s_dict).card
  let s_dict' :=
    if opTag = 1 then Function.update s_dict u (some v.val)
    else Function.update s_dict u none
  let nLive' := (Dictionary.dom s_dict').card
  let ph := s.mem (base + hdrPhase)
  let stg := s.mem (base + hdrStage)
  let nSrc := s.mem (base + hdrNSrc)
  let nDst := s.mem (base + hdrNDst)
  let pad := s.mem (base + hdrPad)
  let ibLo := s.mem (base + hdrItemLo)
  let ibHi := s.mem (base + hdrItemHi)
  let qLo := s.mem (base + hdrQLo)
  let qHi := s.mem (base + hdrQHi)
  let sp := s.mem (base + hdrSplit)
  let cur := s.mem (base + hdrCur)
  let uDone := s.mem (base + hdrUnpermDone)
  let vB := valBits V
  let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
  let k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
  let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  let s_mid := (Memory.spec 0).clientState s_grow (userMutateProg ((base, opTag), (u.val, v_val)))
  let pSrc := if stg = 0 then base + hdrPBase0 else base + hdrPBase1
  let pDst := if ph < 10 then (if stg = 0 then base + hdrPBase1 else base + hdrPBase0)
    else base + hdrPBase0
  let nHost := if nDst = 0 then nSrc else nDst
  let mbHost := if nDst = 0 then base + 192
    else if stg = 0 then base + 192 + pad else base + 192
  let pgHost := hostPageLayout c w nHost mbHost ibHi qHi vB nLive
  let pgHost_fin := hostPageLayout c w nHost mbHost ibHi qHi vB nLive'
  let capSrc := if stg = 0 then nSrc else nDst
  let mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
    else base + 192 + pad
  let mbDst := if ph < 10 then
      (if nDst = 0 then base + hdrSmallMeta1
       else if stg = 0 then base + 192 + pad else base + 192)
    else
      (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
  let L_mid := L.applyFG ph opTag u v
  let slackDst' := if true ∧ ph = 9 ∧ uDone = 0 then 24 else 0
  UserMutatePre w ((base, opTag), (u.val, v_val)) s_grow ∧
  s_mid.frontier = s_grow.frontier ∧
  s_mid.mem (base + hdrLive) = nLive' ∧
  (∀ addr, addr < base + 48 → addr ≠ base + hdrLive → addr ≠ base + hdrSplit →
    s_mid.mem addr = s.mem addr) ∧
  (ph ≠ 3 → ph ≠ 10 → s_mid.mem (base + hdrSplit) = sp) ∧
  ((ph = 3 ∨ ph = 10) →
    s_mid.mem (base + hdrSplit) ≤ nLive' ∧
    s_mid.mem (base + hdrSplit) ≤ sp ∧
    nLive' - s_mid.mem (base + hdrSplit) ≤ (nLive - sp) + 1 ∧
    SplitHiQuotBounded (splitSlotIo w vB base ibLo qLo ibHi qHi nLive') nLive' s_mid.mem) ∧
  (ph = 4 → ∀ off < cur, s_mid.mem (mbDst + off) = 0) ∧
  (ph = 5 →
    ({ c := c, U := U, V := V, w := w, N := nDst, metaBase := mbDst, pBase := pDst,
       io := directSlotIo w vB base ibHi qHi nLive' } : FastEpochLayout).ParamTable
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update s_mid.mem
          (pDst + 48) 0) (pDst + 49) 0) (pDst + 50) (base + hdrSplit)) (pDst + 51) ibHi)
          (pDst + 52) qHi) (pDst + 53) 1) (pDst + 54) w) (pDst + 55) 32) (pDst + 56) 4)
          (pDst + 57) ibHi) (pDst + 58) qHi) (pDst + 59) vB) (pDst + 60) nLive') ∧
    (∀ k, 1 ≤ k → k < 32 → s_mid.mem (mbDst + k) = 0) ∧
    (∀ off, offBktMeta c w nDst ≤ off → off < offPageDir c w nDst →
      s_mid.mem (mbDst + off) = 0)) ∧
  ((ph = 6 ∨ ph = 7) →
    extractPagePair pgHost_fin s_mid.mem = extractPagePair pgHost s.mem ∧
    (0 < nDst →
      EpochSlotInv c U V w s_mid.frontier pDst mbDst
        (directSlotIo w vB base ibHi qHi nLive') 0 false L_mid.slotDst s_mid.mem)) ∧
  (ph = 9 → uDone = 0 →
    0 < (extractPageUnperm pgHost_fin s_mid.mem).cleanPhase ∧
    (extractPageUnperm pgHost_fin s_mid.mem).cleanPhase < 4 ∧
    (extractPageUnperm pgHost_fin s_mid.mem).unpermRank ≤ L.unpermBound + 64) ∧
  (ph ≤ 7 →
    L_mid.slotSrc.nCap = capSrc ∧
    toDictState L_mid.slotSrc.s_abs = s_dict' ∧
    EpochSlotInv c U V w s_mid.frontier pSrc mbSrc
      (activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive')
      0 false L_mid.slotSrc s_mid.mem ∧
    (0 < ph → 0 < capSrc → L_mid.slotSrc.evs.length ≤ 2 * capSrc + L.elapsed + 1)) ∧
  (ph = 8 →
    L_mid.slotSrc.nCap = capSrc ∧ L_mid.slotDst.nCap = nDst ∧
    DisjointOpt L_mid.slotDst.s_abs L_mid.slotSrc.s_abs ∧
    toDictState (orOpt L_mid.slotDst.s_abs L_mid.slotSrc.s_abs) = s_dict' ∧
    (extractPageUnperm pgHost_fin s_mid.mem).cleanPhase = 0 ∧
    EpochSlotInv c U V w s_mid.frontier pSrc mbSrc (pagedSlotIo 0 pgHost_fin) 0 true
      L_mid.slotSrc s_mid.mem ∧
    EpochSlotInv c U V w s_mid.frontier pDst mbDst (pagedSlotIo 1 pgHost_fin) 0 false
      L_mid.slotDst s_mid.mem ∧
    (0 < capSrc → L_mid.slotSrc.evs.length ≤ 3 * capSrc) ∧
    (0 < nDst →
      L_mid.slotDst.evs.length + (liveDom L_mid.slotSrc.s_abs).card ≤
        nDst + L.elapsed + 1)) ∧
  (9 ≤ ph →
    L_mid.slotDst.nCap = nDst ∧
    toDictState L_mid.slotDst.s_abs = s_dict' ∧
    EpochSlotInv c U V w s_mid.frontier pDst mbDst
      (activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive' uDone)
      slackDst' false L_mid.slotDst s_mid.mem ∧
    (0 < nDst → L_mid.slotDst.evs.length ≤ nDst + L.elapsed + 1)) ∧
  ((ph ≤ 7 → L_mid.slotSrc.GoodCovers) →
    (ph = 8 → L_mid.slotSrc.GoodCovers ∧ L_mid.slotDst.GoodCovers) →
    (9 ≤ ph → L_mid.slotDst.GoodCovers) →
    memoryCost (userMutateProg ((base, opTag), (u.val, v_val))) s_grow ≤
      2 * epochStepCost c + 80)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
