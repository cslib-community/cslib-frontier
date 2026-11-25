/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.Frame
-- `import all`: shares private internal helpers within the `TailSlabOps` split.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.WindowHelpers
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Compacted Last-Tail-Item Removal (`compRemoveLastTailItemGenProg`)

Implements and certifies `compRemoveLastTailItemGenProg`, coupling compacted circular-window
swap-and-shrink removal to `removeLastTailItemProg` via `FixedCoupled`.
-/

-- This proof-only companion is intentionally private; sibling `TailSlabOps` modules use
-- `import all`.
set_option linter.privateModule false

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

private def compRemoveTailReadGM1Prog : (CompParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, metaBase), b) => do
    let n_slabs ← readCompGMGenProg ((cp, metaBase), 0)
    let r_idx := 4 + (b + b + b) + 1
    let r_b ← readCompGMGenProg ((cp, metaBase), r_idx)
    pure (n_slabs, r_b)

private def compRemoveTailReadGM2Prog :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog ((ℕ × ℕ) × ℕ)
  | (((cp, metaBase), b), (n_slabs, r_b)) => do
    let ptr_del_idx := cpGmTailPtrBase cp + (b * cpTailCap cp + (r_b - 1))
    let t_del ← readCompGMGenProg ((cp, metaBase), ptr_del_idx)
    let n_tails ← readCompGMGenProg ((cp, metaBase), 1)
    pure ((n_slabs * cpSlabSize cp, n_tails - 1), t_del)

private def compRemoveTailReadTDProg : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((cp, metaBase), (t_del, n')) => do
    let c_del ← readCompTDGenProg ((cp, metaBase), t_del)
    let c_last ← readCompTDGenProg ((cp, metaBase), n')
    pure (c_del, c_last)

private def compRemoveTailCalcDenseProg : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((cp, b_win), (c_del, c_last)) => do
    let d_del ← denseOfCircGenProg (cp, (b_win, c_del))
    let d_last ← denseOfCircGenProg (cp, (b_win, c_last))
    pure (d_del, d_last)

private def compRemoveTailLocateProg : (CompParams × ℕ) × ℕ → Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | ((cp, metaBase), b) => do
    let gm1 ← compRemoveTailReadGM1Prog ((cp, metaBase), b)
    let gm2 ← compRemoveTailReadGM2Prog (((cp, metaBase), b), gm1)
    let cs ← compRemoveTailReadTDProg ((cp, metaBase), (gm2.2, gm2.1.2))
    let ds ← compRemoveTailCalcDenseProg ((cp, gm2.1.1), cs)
    pure (gm2.1, ds)

private def compRemoveTailApplyProg :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | (((cp, (metaBase, itemBase)), b), ((b_win, n'), (d_del, d_last))) => do
    copyCompItemGenProg ((cp, itemBase), (d_last, d_del))
    copyCompItemGenProg ((cp, itemBase), (b_win + n', d_last))
    winShrinkRightGenProg ((cp, metaBase), (b_win, n'))
    compRemoveTailGMOnlyGenProg ((cp, metaBase), b)

/-- Remove the last tail item of bucket `b` and shrink the circular tail window on the right. -/
private def compRemoveLastTailItemGenProg : (CompParams × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((cp, (metaBase, itemBase)), b) => do
    let loc ← compRemoveTailLocateProg ((cp, metaBase), b)
    compRemoveTailApplyProg ((((cp, (metaBase, itemBase)), b), loc))

@[simp] private theorem memoryCost_compRemoveLastTailItemGenProg
    (d : (CompParams × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (compRemoveLastTailItemGenProg d) s = 72 := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
  simp [compRemoveLastTailItemGenProg, compRemoveTailLocateProg, compRemoveTailReadGM1Prog,
    compRemoveTailReadGM2Prog, compRemoveTailReadTDProg, compRemoveTailCalcDenseProg,
    compRemoveTailApplyProg]

/-- Precondition for `compRemoveLastTailItemGenProg`. -/
private def CompRemoveLastTailPre (w : ℕ) :
    (CompParams × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((cp, (metaBase, itemBase)), b), s =>
    ∃ U V N m_cap s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b) ∧
      totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap

private def CompRemoveTailApplyPre (w : ℕ) :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), b), ((b_win, n'), (d_del, d_last))), s =>
    ∃ U V N m_cap,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) ∧
      1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b) ∧
      b_win + n' + 1 ≤ N ∧
      b_win + n' + 1 ≤ m_cap ∧
      d_del < b_win + n' + 1 ∧
      d_last < b_win + n' + 1 ∧
      n' < maxTailItems N ∧
      compDTAt metaBase U w N s.mem ((b_win + n') % maxTailItems N) < maxTailItems N ∧
      compTDAt metaBase U w N s.mem n' < maxTailItems N

private theorem compRemoveTailLocate_spec {metaBase itemBase U V w N m_cap b : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hb_pos : 0 < bucketBits N)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (hr_pos : 1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b)) :
    let gm := compGmAt metaBase U w N s.mem
    let td := compTDAt metaBase U w N s.mem
    let b_win := gm 0 * slabSize N
    let n' := gm 1 - 1
    let t_del := gm (gmTailPtrIdx N b (gm (gmRIdx b) - 1))
    let d_del := denseOfCirc (maxTailItems N) b_win (td t_del)
    let d_last := denseOfCirc (maxTailItems N) b_win (td n')
    (Memory.spec 0).clientState s
      (compRemoveTailLocateProg ((mkCompParams U V w N, metaBase), b)) = s ∧
    (Memory.spec 0).clientResult s
      (compRemoveTailLocateProg ((mkCompParams U V w N, metaBase), b)) =
      ((b_win, n'), (d_del, d_last)) ∧
    ValidProg w 0 s (compRemoveTailLocateProg ((mkCompParams U V w N, metaBase), b)) := by
  intro gm td b_win n' t_del d_del d_last
  dsimp only [gm, td, b_win, n', t_del, d_del, d_last] at *
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have htail := hslot.multi_tail hb_pos
  have hr_le_nt := r_le_ntails_of_tailBijection htail hb
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  have hr_del_lt : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 <
      compGmAt metaBase U w N s.mem (gmRIdx b) := by omega
  have hr_del_cap : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 < tailCapPerBucket N :=
    lt_of_lt_of_le hr_del_lt (htail.r_le b hb)
  have hptr_del_lt : gmTailPtrBase N +
      (b * tailCapPerBucket N + (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
      globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_del_cap
  have ht_del_lt : compGmAt metaBase U w N s.mem
      (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
      compGmAt metaBase U w N s.mem 1 := htail.ptr_lt b hb _ hr_del_lt
  have ht_del_max : compGmAt metaBase U w N s.mem
      (gmTailPtrBase N +
        (b * tailCapPerBucket N + (compGmAt metaBase U w N s.mem (gmRIdx b) - 1))) <
      maxTailItems N := lt_of_lt_of_le ht_del_lt htail.ntails_le
  have hn'_lt : compGmAt metaBase U w N s.mem 1 - 1 < compGmAt metaBase U w N s.mem 1 := by omega
  have hn'_max : compGmAt metaBase U w N s.mem 1 - 1 < maxTailItems N :=
    lt_of_lt_of_le hn'_lt htail.ntails_le
  have hwin0 : WindowInv (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
      (compGmAt metaBase U w N s.mem 1)
      (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem) := by
    have hw0 := hcpl.win_inv; simp only [hb0, ↓reduceIte] at hw0; exact hw0
  have ht_del_lt' : compGmAt metaBase U w N s.mem
      (gmTailPtrBase N +
        (b * tailCapPerBucket N + (compGmAt metaBase U w N s.mem (gmRIdx b) - 1))) <
      compGmAt metaBase U w N s.mem 1 := ht_del_lt
  have hst : (Memory.spec 0).clientState s
      (compRemoveTailLocateProg ((mkCompParams U V w N, metaBase), b)) = s := by
    unfold StateTransitionSpec.clientState
    simp [compRemoveTailLocateProg, compRemoveTailReadGM1Prog, compRemoveTailReadGM2Prog,
      compRemoveTailReadTDProg, compRemoveTailCalcDenseProg]
  have hres : (Memory.spec 0).clientResult s
      (compRemoveTailLocateProg ((mkCompParams U V w N, metaBase), b)) =
      ((compGmAt metaBase U w N s.mem 0 * slabSize N, compGmAt metaBase U w N s.mem 1 - 1),
       (denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
         (compTDAt metaBase U w N s.mem
           (compGmAt metaBase U w N s.mem
             (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)))),
        denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
          (compTDAt metaBase U w N s.mem (compGmAt metaBase U w N s.mem 1 - 1)))) := by
    dsimp only [compRemoveTailLocateProg, compRemoveTailReadGM1Prog, compRemoveTailReadGM2Prog,
      compRemoveTailReadTDProg, compRemoveTailCalcDenseProg]
    simp only [bind_assoc, pure_bind, cpGmTailPtrBase_mk, cpTailCap_mk, cpSlabSize_mk]
    rw [hr_eq, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg h0_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg hr_idx_lt, clientState_readCompGMGenProg,
      StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hptr_del_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg,
      StateTransitionSpec.clientResult_bind, clientResult_readCompTDGenProg ht_del_max,
      clientState_readCompTDGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompTDGenProg hn'_max, clientState_readCompTDGenProg,
      StateTransitionSpec.clientResult_bind,
      clientResult_denseOfCircGenProg (fun _ => hwin0.td_lt _ ht_del_lt'),
      clientState_denseOfCircGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_denseOfCircGenProg (fun _ => hwin0.td_lt _ hn'_lt),
      clientState_denseOfCircGenProg]
    rfl
  have hv : ValidProg w 0 s (compRemoveTailLocateProg ((mkCompParams U V w N, metaBase), b)) := by
    dsimp only [compRemoveTailLocateProg, compRemoveTailReadGM1Prog, compRemoveTailReadGM2Prog,
      compRemoveTailReadTDProg, compRemoveTailCalcDenseProg]
    simp only [bind_assoc, pure_bind, cpGmTailPtrBase_mk, cpTailCap_mk, cpSlabSize_mk, hr_eq]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h0_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg h0_lt]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, hr_idx_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hr_idx_lt]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, hptr_del_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hptr_del_lt]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h1_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg h1_lt]
    refine validProg_bind (validProg_readCompTDGen ⟨henv.compMetaEnv, ht_del_max⟩) ?_
    rw [clientState_readCompTDGenProg]
    refine validProg_bind (validProg_readCompTDGen ⟨henv.compMetaEnv, hn'_max⟩) ?_
    rw [clientState_readCompTDGenProg]
    refine validProg_bind (validProg_denseOfCircGen _ _) ?_
    rw [clientState_denseOfCircGenProg]
    exact validProg_bind (validProg_denseOfCircGen _ _) (validProg_pure _)
  exact ⟨hst, hres, hv⟩

private theorem compRemoveLastTailItem_effect {metaBase itemBase U V w N m_cap b : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hb_pos : 0 < bucketBits N)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (hr_pos : 1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b))
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap) :
    let s' := (Memory.spec 0).clientState s
      (compRemoveLastTailItemGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b))
    let s_fix' := (Memory.spec 0).clientState s_fix
      (removeLastTailItemProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro s' s_fix'
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  set gm := compGmAt metaBase U w N s.mem
  set td := compTDAt metaBase U w N s.mem
  set dt := compDTAt metaBase U w N s.mem
  set b_win := gm 0 * slabSize N
  set n' := gm 1 - 1
  set t_del := gm (gmTailPtrIdx N b (gm (gmRIdx b) - 1))
  set d_del := denseOfCirc (maxTailItems N) b_win (td t_del)
  set d_last := denseOfCirc (maxTailItems N) b_win (td n')
  have htail := hslot.multi_tail hb_pos
  have hr_le_nt := r_le_ntails_of_tailBijection htail hb
  have hn1_eq : n' + 1 = gm 1 := by dsimp only [n']; omega
  have hSN : b_win + (n' + 1) ≤ N := by rw [hn1_eq]; exact hslot.multi_total_le hb_pos
  have hm_le : b_win + (n' + 1) ≤ m_cap := by
    rw [hn1_eq]; unfold totalSlots at hm_cap; rw [ite_eq_right hb0] at hm_cap; exact hm_cap
  have hM_le : n' + 1 ≤ maxTailItems N := by rw [hn1_eq]; exact htail.ntails_le
  have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
  have hmax_eq : max (maxTailItems N) 1 = maxTailItems N := Nat.max_eq_left hM_pos
  obtain ⟨hloc_s, hloc_r, _⟩ := compRemoveTailLocate_spec henv hb_pos hcpl hslot hb hr_pos
  have hwin0 : WindowCoupled metaBase itemBase U V w N b_win (n' + 1) (b_win + (n' + 1))
      s_fix s := by
    have hc := hcpl; unfold FixedCoupled epochTotalSlots at hc
    simp only [hb0, ↓reduceIte] at hc
    simpa only [hn1_eq] using hc
  have ht_del_lt : t_del < n' + 1 := by rw [hn1_eq]; exact htail.ptr_lt b hb _ (by omega)
  have hp_del := physByBase_tail_denseOfCirc hb_pos hwin0.win_inv ht_del_lt
  have hp_last := physByBase_tail_denseOfCirc hb_pos hwin0.win_inv (Nat.lt_succ_self n')
  have hslot_fix : SlotStoreInv N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      s_fix.mem) := slotStoreInv_of_gm_eq hcpl.gm_eq.symm hslot
  obtain ⟨_, _, hq_fix, hv_fix, hl_fix, hgm_fix⟩ :=
    removeLastTailItemProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos hb s_fix
      (hslot_fix.multi_tail hb_pos) (by rw [← hcpl.gm_eq]; exact hr_pos)
  set s_fix_mid : Memory.State := {
    mem := writePacked (0 + offVal U (ghostW w) N (epochHashSpace U (ghostW w) N)) (valBits V)
      (ghostW w)
      (writePacked (0 + offQuot (epochHashSpace U (ghostW w) N)) (quotientBits U N) (ghostW w)
        s_fix.mem (N - 1 - t_del)
        (quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem (N - 1 - n')))
      (N - 1 - t_del)
      (valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem (N - 1 - n')),
    frontier := s_fix.frontier }
  have hg_del_lt : N - 1 - t_del < N := by omega
  obtain ⟨_, _, hq_m1, hv_m1, hl_m1, hg_m1⟩ :=
    writeQuotProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hg_del_lt (quotAt_lt _ _ _ _ _ _ _) s_fix
  obtain ⟨_, _, hq_m2, hv_m2, hl_m2, hg_m2⟩ :=
    writeValProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hg_del_lt (valAt_lt _ _ _ _ _ _ _ _)
      ((Memory.spec 0).clientState s_fix
        (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N)
          ((0, N - 1 - t_del),
            quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem (N - 1 - n'))))
  set s_mid_fix := (Memory.spec 0).clientState
    ((Memory.spec 0).clientState s_fix
      (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N)
        ((0, N - 1 - t_del),
          quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem (N - 1 - n'))))
    (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      ((0, N - 1 - t_del),
        valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem (N - 1 - n')))
  set s₁ := (Memory.spec 0).clientState s
    (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_last, d_del)))
  have hcpl1 : WindowCoupled metaBase itemBase U V w N b_win (n' + 1) (b_win + (n' + 1))
      s_mid_fix s₁ :=
    windowCoupled_copyCompItem henv.pos_w henv.meta_le_item hb_pos hSN hM_le hwin0
      hp_last.2.1 hp_del.2.1 hp_last.2.2 hp_del.2.2
      (hg_m2.trans hg_m1) (hl_m2.trans hl_m1) (hq_m2.trans hq_m1)
      (hv_m2.trans (congrArg (fun f => Function.update f _ _) hv_m1))
  have htd1_eq : compTDAt metaBase U w N s₁.mem = td := by
    dsimp only [s₁]; rw [clientState_copyCompItemGenProg hp_last.2.1]
    exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item hp_del.2.1 _).2.2.1.trans
      (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item hp_del.2.1 s.mem).2.2.1
  have hd_last1 : denseOfCirc (maxTailItems N) b_win (compTDAt metaBase U w N s₁.mem n') =
      d_last := by rw [htd1_eq]
  set s₂ := (Memory.spec 0).clientState s₁
    (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (b_win + n', d_last)))
  set s₃ := (Memory.spec 0).clientState s₂
    (winShrinkRightGenProg ((mkCompParams U V w N, metaBase), (b_win, n')))
  have hcpl3 : WindowCoupled metaBase itemBase U V w N b_win n' (b_win + n') s_mid_fix s₃ := by
    simpa only [hd_last1] using
      windowCoupled_shrinkRight henv.pos_w henv.meta_le_item hb_pos hM_le hcpl1
  have hgm3_eq : compGmAt metaBase U w N s₃.mem = gm :=
    hcpl3.gm_eq.trans ((hg_m2.trans hg_m1).trans hcpl.gm_eq.symm)
  set s₄ := (Memory.spec 0).clientState s₃
    (compRemoveTailGMOnlyGenProg ((mkCompParams U V w N, metaBase), b))
  obtain ⟨hfr4, hgm4⟩ := compRemoveTailGMOnlyGenProg_effect (metaBase := metaBase)
    (itemBase := itemBase) (U := U) (V := V) (w := w) (N := N) (m_items := b_win + n') (b := b)
    henv.pos_w henv.meta_le_item hb_pos hb s₃
    (tailBijection_of_gm_eq hgm3_eq htail) (by rw [hgm3_eq]; exact hr_pos)
  rw [hgm3_eq] at hgm4
  have hs'_eq : s' = s₄ := by
    dsimp only [s', compRemoveLastTailItemGenProg]
    rw [StateTransitionSpec.clientState_bind, hloc_s, hloc_r]
    dsimp only [compRemoveTailApplyProg]
    repeat rw [StateTransitionSpec.clientState_bind]
  have hdt2_eq : compDTAt metaBase U w N s₂.mem = compDTAt metaBase U w N s.mem := by
    dsimp only [s₂]; rw [clientState_copyCompItemGenProg (m_items := b_win + (n' + 1)) (by omega)]
    refine (writeCompVal_meta_frame henv.pos_w henv.meta_le_item hp_last.2.1 _).2.2.2.trans ?_
    refine (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item hp_last.2.1 s₁.mem).2.2.2.trans ?_
    dsimp only [s₁]; rw [clientState_copyCompItemGenProg hp_last.2.1]
    exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item hp_del.2.1 _).2.2.2.trans
      (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item hp_del.2.1 s.mem).2.2.2
  have htd2_eq : compTDAt metaBase U w N s₂.mem = td := by
    dsimp only [s₂]; rw [clientState_copyCompItemGenProg (m_items := b_win + (n' + 1)) (by omega)]
    exact ((writeCompVal_meta_frame henv.pos_w henv.meta_le_item hp_last.2.1 _).2.2.1.trans
      (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item hp_last.2.1 s₁.mem).2.2.1).trans
      htd1_eq
  obtain ⟨hf_w3, _, _, _, _, _, _, hout_w3⟩ :=
    winShrinkRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n')
      henv.pos_w henv.meta_le_item (by omega) s₂
      (by rw [hdt2_eq, ← hmax_eq]; exact hcpl.dt_lt _)
      (by rw [htd2_eq, ← hmax_eq]; exact hcpl.td_lt _)
  have hframe : CompOpFrame metaBase itemBase U V w N m_cap s s' := by
    rw [hs'_eq]
    exact (compOpFrame_copyCompItem henv.pos_w (lt_of_lt_of_le hp_last.2.1 hm_le)
        (lt_of_lt_of_le hp_del.2.1 hm_le) s).trans
      ((compOpFrame_copyCompItem henv.pos_w (by omega) (lt_of_lt_of_le hp_last.2.1 hm_le) s₁).trans
        ((compOpFrame_tailWindow hf_w3 hout_w3).trans (CompOpFrame.of_gmFrame hfr4)))
  have hpres := gmRemoveTail_preserves_nonTail hb hr_pos htail
  have hgm4_0 : compGmAt metaBase U w N s₄.mem 0 = gm 0 := by rw [hgm4, hpres.1]
  have hgm4_1 : compGmAt metaBase U w N s₄.mem 1 = n' := by rw [hgm4, hpres.2.1]
  have htot4 : epochTotalSlots N (compGmAt metaBase U w N s₄.mem) = b_win + n' := by
    unfold epochTotalSlots; rw [ite_eq_right hb0, hgm4_0, hgm4_1]
  have hgm_fix_eq : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem = gm :=
    hcpl.gm_eq.symm
  refine ⟨hframe, ?_⟩
  rw [hs'_eq]
  unfold FixedCoupled
  refine ⟨hgm4.trans (by rw [← hgm_fix_eq]; exact hgm_fix.symm),
    hfr4.lm_eq.trans (hcpl3.lm_eq.trans ((hl_m2.trans hl_m1).trans hl_fix.symm)),
    by simp only [hb0, ↓reduceIte]; rw [hgm4_0, hgm4_1, hfr4.td_eq, hfr4.dt_eq]
       exact hcpl3.win_inv,
    fun i => by rw [hfr4.td_eq]; exact hcpl3.td_lt i,
    fun i => by rw [hfr4.dt_eq]; exact hcpl3.dt_lt i,
    fun idx hidx => ?_,
    fun idx hidx => ?_⟩
  · rw [htot4] at hidx ⊢
    rw [congrFun hfr4.quot_eq idx, hgm4_0, hfr4.dt_eq, hcpl3.quot_eq idx hidx,
      hq_m2, hq_m1, hq_fix, hgm_fix_eq]
  · rw [htot4] at hidx ⊢
    rw [congrFun hfr4.val_eq idx, hgm4_0, hfr4.dt_eq, hcpl3.val_eq idx hidx,
      hv_m2, hv_m1, hv_fix, hgm_fix_eq]

private def CompRemoveTailLocatePre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N m_cap itemBase s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b)

private def CompRemoveTailReadGM1Pre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N

private theorem realizesBounded_compRemoveTailReadGM1 :
    RealizesBounded .exact compRemoveTailReadGM1Prog
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ × ℕ))
      CompRemoveTailReadGM1Pre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    dsimp only at *
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    try simp only [StateTransitionSpec.clientState, runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmRIdx at hr_idx_lt; omega)
  refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
  unfold gmRIdx at hr_idx_lt; omega

private def CompRemoveTailReadGM2Pre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (n_slabs, r_b)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      n_slabs * slabSize N ≤ N ∧
      1 ≤ r_b ∧ r_b ≤ tailCapPerBucket N ∧
      1 ≤ compGmAt metaBase U w N s.mem 1

private theorem realizesBounded_compRemoveTailReadGM2 :
    RealizesBounded .exact compRemoveTailReadGM2Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      CompRemoveTailReadGM2Pre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨n_slabs, r_b⟩⟩
    try dsimp only at *
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hns_le, hr_pos, hr_le,
      hnt_pos⟩ := h
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hptr_lt : gmTailPtrBase N + (b * tailCapPerBucket N + (r_b - 1)) < globalMetaLen N :=
      gmTailPtrIdx_lt hb_pos hb (by omega)
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    try simp only [cpGmTailPtrBase_mk, cpTailCap_mk, cpSlabSize_mk,
      StateTransitionSpec.clientState, runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg h1_lt] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; omega⟩
  all_goals try {
    change Fits w _
    first
      | exact fits_const_of_offCompItems hfit_meta (by omega)
      | exact fits_of_le_globalMetaLen_comp hb_pos hw hnU hU (by omega)
      | exact Fits.of_le hU (by omega)
  }
  all_goals omega

private def CompRemoveTailReadTDPre (w : ℕ) : (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, metaBase), (t_del, n')), s =>
    CompMetaEnv w cp metaBase s ∧ t_del < cpMaxTail cp ∧ n' < cpMaxTail cp

private theorem realizesBounded_compRemoveTailReadTD :
    RealizesBounded .exact compRemoveTailReadTDProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompRemoveTailReadTDPre (fun _ _ => 0) := by
  have hrtd := realizesBounded_readCompTDGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, ⟨t_del, n'⟩⟩
    dsimp only at *
    obtain ⟨hmeta, ht, hn'⟩ := h
    try simp only [StateTransitionSpec.clientState, runClient_state_readCompTDGenProg] at *)
  · exact ⟨hmeta, ht⟩
  · exact ⟨hmeta, hn'⟩

private def CompRemoveTailCalcDensePre (w : ℕ) :
    (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, b_win), (c_del, c_last)), _s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      b_win ≤ N ∧
      (0 < maxTailItems N →
        c_del < maxTailItems N ∧ denseOfCirc (maxTailItems N) b_win c_del ≤ N ∧
        c_last < maxTailItems N ∧ denseOfCirc (maxTailItems N) b_win c_last ≤ N)

private theorem realizesBounded_compRemoveTailCalcDense :
    RealizesBounded .exact compRemoveTailCalcDenseProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompRemoveTailCalcDensePre (fun _ _ => 0) := by
  have hdoc := realizesBounded_denseOfCircGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, b_win⟩, ⟨c_del, c_last⟩⟩
    dsimp only at *
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hb_le, hcond⟩ := h)
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hb_le,
      fun hb => ⟨(hcond hb).1, (hcond hb).2.1⟩⟩
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hb_le,
      fun hb => ⟨(hcond hb).2.2.1, (hcond hb).2.2.2⟩⟩

private theorem realizesBounded_compRemoveTailLocate :
    RealizesBounded .exact compRemoveTailLocateProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      CompRemoveTailLocatePre (fun _ _ => 0) := by
  have hg1 := realizesBounded_compRemoveTailReadGM1
  have hg2 := realizesBounded_compRemoveTailReadGM2
  have htd := realizesBounded_compRemoveTailReadTD
  have hdc := realizesBounded_compRemoveTailCalcDense
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    dsimp only at *
    obtain ⟨U, V, N, _m_cap, _itemBase, _s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, hr_pos⟩ := h
    have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
    have htail := hslot.multi_tail hb_pos
    have hr_le_nt := r_le_ntails_of_tailBijection htail hb
    have hSN := hslot.multi_total_le hb_pos
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
    have hr_del_lt : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 <
        compGmAt metaBase U w N s.mem (gmRIdx b) := by omega
    have hr_del_cap : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 < tailCapPerBucket N :=
      lt_of_lt_of_le hr_del_lt (htail.r_le b hb)
    have hptr_del_lt : gmTailPtrBase N +
        (b * tailCapPerBucket N + (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
        globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_del_cap
    have ht_del_lt : compGmAt metaBase U w N s.mem
        (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
        compGmAt metaBase U w N s.mem 1 := htail.ptr_lt b hb _ hr_del_lt
    have ht_del_max : compGmAt metaBase U w N s.mem
        (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
        maxTailItems N := lt_of_lt_of_le ht_del_lt htail.ntails_le
    have hn'_lt : compGmAt metaBase U w N s.mem 1 - 1 < compGmAt metaBase U w N s.mem 1 := by omega
    have hn'_max : compGmAt metaBase U w N s.mem 1 - 1 < maxTailItems N :=
      lt_of_lt_of_le hn'_lt htail.ntails_le
    have hwin0 : WindowInv (maxTailItems N)
        (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compGmAt metaBase U w N s.mem 1)
        (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem) := by
      have hw0 := hcpl.win_inv; simp only [hb0, ↓reduceIte] at hw0; exact hw0
    have hg1_s : (Memory.spec 0).clientState s
        (compRemoveTailReadGM1Prog ((mkCompParams U V w N, metaBase), b)) = s := by
      unfold StateTransitionSpec.clientState; simp [compRemoveTailReadGM1Prog]
    have hg1_r : (Memory.spec 0).clientResult s
        (compRemoveTailReadGM1Prog ((mkCompParams U V w N, metaBase), b)) =
        (compGmAt metaBase U w N s.mem 0, compGmAt metaBase U w N s.mem (gmRIdx b)) := by
      dsimp only [compRemoveTailReadGM1Prog]; rw [hr_eq]
      rw [StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg h0_lt,
        clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompGMGenProg hr_idx_lt, clientState_readCompGMGenProg]; rfl
    have hg2_s : (Memory.spec 0).clientState s
        (compRemoveTailReadGM2Prog (((mkCompParams U V w N, metaBase), b),
          (compGmAt metaBase U w N s.mem 0, compGmAt metaBase U w N s.mem (gmRIdx b)))) = s := by
      unfold StateTransitionSpec.clientState; simp [compRemoveTailReadGM2Prog]
    have hg2_r : (Memory.spec 0).clientResult s
        (compRemoveTailReadGM2Prog (((mkCompParams U V w N, metaBase), b),
          (compGmAt metaBase U w N s.mem 0, compGmAt metaBase U w N s.mem (gmRIdx b)))) =
        ((compGmAt metaBase U w N s.mem 0 * slabSize N, compGmAt metaBase U w N s.mem 1 - 1),
         compGmAt metaBase U w N s.mem
           (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1))) := by
      dsimp only [compRemoveTailReadGM2Prog, cpGmTailPtrBase_mk, cpTailCap_mk, cpSlabSize_mk]
      rw [StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hptr_del_lt,
        clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg]; rfl)
  · exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      henv.meta_le_frontier, hb_pos, hb⟩
  · rw [hg1_s, hg1_r]; dsimp only
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      henv.meta_le_frontier, hb_pos, hb, by omega, hr_pos, htail.r_le b hb, by omega⟩
  · rw [hg1_s, hg1_r, hg2_s, hg2_r]
    exact ⟨henv.compMetaEnv, by simp only [cpMaxTail_mk]; exact ht_del_max,
      by simp only [cpMaxTail_mk]; exact hn'_max⟩
  · rw [hg1_s, hg1_r, hg2_s, hg2_r]
    have htd_r : (Memory.spec 0).clientResult s
        (compRemoveTailReadTDProg ((mkCompParams U V w N, metaBase),
          (compGmAt metaBase U w N s.mem
            (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)),
           compGmAt metaBase U w N s.mem 1 - 1))) =
        (compTDAt metaBase U w N s.mem
          (compGmAt metaBase U w N s.mem
            (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1))),
         compTDAt metaBase U w N s.mem (compGmAt metaBase U w N s.mem 1 - 1)) := by
      dsimp only [compRemoveTailReadTDProg]
      rw [StateTransitionSpec.clientResult_bind, clientResult_readCompTDGenProg ht_del_max,
        clientState_readCompTDGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompTDGenProg hn'_max, clientState_readCompTDGenProg]; rfl
    rw [htd_r]; dsimp only
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      by omega, fun _ => ⟨hwin0.td_lt _ ht_del_lt,
        le_trans (le_of_lt (hwin0.dense_lt _ ht_del_lt)) hSN,
        hwin0.td_lt _ hn'_lt,
        le_trans (le_of_lt (hwin0.dense_lt _ hn'_lt)) hSN⟩⟩

private theorem realizesBounded_compRemoveTailApply :
    RealizesBounded .exact compRemoveTailApplyProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      CompRemoveTailApplyPre (fun _ _ => 0) := by
  have hcpy := realizesBounded_copyCompItemGen
  have hwsr := realizesBounded_winShrinkRightGen
  have hrm := realizesBounded_compRemoveTailGMOnlyGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, ⟨⟨b_win, n'⟩, ⟨d_del, d_last⟩⟩⟩
    obtain ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, htail, hr_pos, hbn_N, hbn_cap,
      hd_del, hd_last, hn'_max, hdt_lt, htd_lt⟩ := h
    dsimp only at *
    set s1 := (Memory.spec 0).clientState s
      (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_last, d_del)))
    set s2 := (Memory.spec 0).clientState s1
      (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (b_win + n', d_last)))
    set s3 := (Memory.spec 0).clientState s2
      (winShrinkRightGenProg ((mkCompParams U V w N, metaBase), (b_win, n')))
    have hs1_eq := clientState_copyCompItemGenProg (U := U) (V := V) (w := w) (N := N)
      (m_items := m_cap) (itemBase := itemBase) (dst := d_del) (by omega : d_last < m_cap) s
    have hs2_eq := clientState_copyCompItemGenProg (U := U) (V := V) (w := w) (N := N)
      (m_items := m_cap) (itemBase := itemBase) (dst := d_last) (by omega : b_win + n' < m_cap) s1
    have hgm2 : compGmAt metaBase U w N s2.mem = compGmAt metaBase U w N s.mem := by
      dsimp only [s2]; rw [hs2_eq]
      refine (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) _).2.1.trans ?_
      refine (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) s1.mem).2.1.trans ?_
      dsimp only [s1]; rw [hs1_eq]
      exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) _).2.1.trans
        (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap) (by omega)
          s.mem).2.1
    have htd2 : compTDAt metaBase U w N s2.mem = compTDAt metaBase U w N s.mem := by
      dsimp only [s2]; rw [hs2_eq]
      refine (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) _).2.2.1.trans ?_
      refine (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) s1.mem).2.2.1.trans ?_
      dsimp only [s1]; rw [hs1_eq]
      exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) _).2.2.1.trans
        (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap) (by omega)
          s.mem).2.2.1
    have hdt2 : compDTAt metaBase U w N s2.mem = compDTAt metaBase U w N s.mem := by
      dsimp only [s2]; rw [hs2_eq]
      refine (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) _).2.2.2.trans ?_
      refine (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) s1.mem).2.2.2.trans ?_
      dsimp only [s1]; rw [hs1_eq]
      exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
        (by omega) _).2.2.2.trans
        (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap) (by omega)
          s.mem).2.2.2)
  · exact ⟨m_cap, henv.compItemEnv, by omega, by omega⟩
  · exact lt_of_le_of_lt (by have := henv.le_U; omega) henv.lt_pow_U
  · refine ⟨m_cap, (henv.of_mem_eq ?_).compItemEnv, by omega, by omega⟩
    dsimp only [s1]; rw [hs1_eq]
  · refine ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      ?_, hn'_max, by omega, by rw [hdt2]; exact hdt_lt, by rw [htd2]; exact htd_lt⟩
    dsimp only [s2]; rw [hs2_eq]; dsimp only [s1]; rw [hs1_eq]
    exact henv.meta_le_frontier
  · obtain ⟨hf3, _, _, _, hgm3, _, _, _⟩ :=
      winShrinkRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n')
        henv.pos_w henv.meta_le_item hn'_max s2
        (by rw [hdt2]; exact hdt_lt) (by rw [htd2]; exact htd_lt)
    have hgm3' : compGmAt metaBase U w N s3.mem = compGmAt metaBase U w N s.mem :=
      hgm3.trans hgm2
    change CompRemoveTailGMOnlyPre w ((mkCompParams U V w N, metaBase), b) s3
    refine ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      ?_, hb_pos, hb, tailBijection_of_gm_eq hgm3' htail, by rw [hgm3']; exact hr_pos⟩
    rw [hf3]; dsimp only [s2]; rw [hs2_eq]; dsimp only [s1]; rw [hs1_eq]
    exact henv.meta_le_frontier

private theorem realizesBounded_compRemoveLastTailItemGen :
    RealizesBounded .exact compRemoveLastTailItemGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompRemoveLastTailPre (fun _ _ => 0) := by
  have hloc := realizesBounded_compRemoveTailLocate
  have happ := realizesBounded_compRemoveTailApply
  realize
  · rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, hr_pos, _⟩ := h
    exact ⟨U, V, N, m_cap, itemBase, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, hr_pos⟩
  · rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, hr_pos, hm_cap⟩ := h
    dsimp only at *
    obtain ⟨hloc_s, hloc_r, _⟩ := compRemoveTailLocate_spec henv hb_pos hcpl hslot hb hr_pos
    rw [hloc_s, hloc_r]
    dsimp only
    have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
    have htail := hslot.multi_tail hb_pos
    have hr_le_nt := r_le_ntails_of_tailBijection htail hb
    have hSN := hslot.multi_total_le hb_pos
    have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
    have hmax_eq : max (maxTailItems N) 1 = maxTailItems N := Nat.max_eq_left hM_pos
    have hwin0 : WindowInv (maxTailItems N)
        (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compGmAt metaBase U w N s.mem 1)
        (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem) := by
      have hw0 := hcpl.win_inv; simp only [hb0, ↓reduceIte] at hw0; exact hw0
    have ht_del_lt : compGmAt metaBase U w N s.mem
        (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) <
        compGmAt metaBase U w N s.mem 1 := htail.ptr_lt b hb _ (by omega)
    have hn'_lt : compGmAt metaBase U w N s.mem 1 - 1 < compGmAt metaBase U w N s.mem 1 := by omega
    unfold totalSlots at hm_cap; rw [ite_eq_right hb0] at hm_cap
    refine ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, htail, hr_pos, by omega, by omega, ?_, ?_,
      lt_of_lt_of_le hn'_lt htail.ntails_le,
      by rw [← hmax_eq]; exact hcpl.dt_lt _,
      by rw [← hmax_eq]; exact hcpl.td_lt _⟩
    · have := hwin0.dense_lt _ ht_del_lt; omega
    · have := hwin0.dense_lt _ hn'_lt; omega

private theorem validProg_compRemoveLastTailItemGen {w : ℕ} {d : (CompParams × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompRemoveLastTailPre w d s) :
    ValidProg w 0 s (compRemoveLastTailItemGenProg d) := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
  obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, hr_pos, hm_cap⟩ := h
  obtain ⟨hloc_s, hloc_r, hloc_v⟩ := compRemoveTailLocate_spec henv hb_pos hcpl hslot hb hr_pos
  dsimp only [compRemoveLastTailItemGenProg]
  refine validProg_bind hloc_v ?_
  rw [hloc_s, hloc_r]
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have htail := hslot.multi_tail hb_pos
  have hr_le_nt := r_le_ntails_of_tailBijection htail hb
  have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
  have hmax_eq : max (maxTailItems N) 1 = maxTailItems N := Nat.max_eq_left hM_pos
  have hwin0 : WindowInv (maxTailItems N)
      (compGmAt metaBase U w N s.mem 0 * slabSize N)
      (compGmAt metaBase U w N s.mem 1)
      (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem) := by
    have hw0 := hcpl.win_inv; simp only [hb0, ↓reduceIte] at hw0; exact hw0
  have ht_del_lt := htail.ptr_lt b hb (compGmAt metaBase U w N s.mem (gmRIdx b) - 1) (by omega)
  have hn'_lt : compGmAt metaBase U w N s.mem 1 - 1 < compGmAt metaBase U w N s.mem 1 := by omega
  have hd_del_lt := hwin0.dense_lt _ ht_del_lt
  have hd_last_lt := hwin0.dense_lt _ hn'_lt
  unfold totalSlots at hm_cap; rw [ite_eq_right hb0] at hm_cap
  dsimp only [compRemoveTailApplyProg]
  refine validProg_bind
    (validProg_copyCompItemGen ⟨m_cap, henv.compItemEnv, by omega, by omega⟩) ?_
  set s1 := (Memory.spec 0).clientState s
    (copyCompItemGenProg ((mkCompParams U V w N, itemBase),
      (denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compTDAt metaBase U w N s.mem (compGmAt metaBase U w N s.mem 1 - 1)),
       denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compTDAt metaBase U w N s.mem
          (compGmAt metaBase U w N s.mem
            (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)))))))
  have hs1_eq := clientState_copyCompItemGenProg (U := U) (V := V) (w := w) (N := N)
    (m_items := m_cap) (itemBase := itemBase)
    (src := denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
      (compTDAt metaBase U w N s.mem (compGmAt metaBase U w N s.mem 1 - 1)))
    (dst := denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
      (compTDAt metaBase U w N s.mem
        (compGmAt metaBase U w N s.mem
          (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)))))
    (by omega) s
  have henv1 := henv.of_mem_eq (s' := s1) (by dsimp only [s1]; rw [hs1_eq])
  refine validProg_bind
    (validProg_copyCompItemGen ⟨m_cap, henv1.compItemEnv, by omega, by omega⟩) ?_
  set s2 := (Memory.spec 0).clientState s1
    (copyCompItemGenProg ((mkCompParams U V w N, itemBase),
      (compGmAt metaBase U w N s.mem 0 * slabSize N + (compGmAt metaBase U w N s.mem 1 - 1),
       denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compTDAt metaBase U w N s.mem (compGmAt metaBase U w N s.mem 1 - 1)))))
  have hs2_eq := clientState_copyCompItemGenProg (U := U) (V := V) (w := w) (N := N)
    (m_items := m_cap) (itemBase := itemBase)
    (src := compGmAt metaBase U w N s.mem 0 * slabSize N + (compGmAt metaBase U w N s.mem 1 - 1))
    (dst := denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
      (compTDAt metaBase U w N s.mem (compGmAt metaBase U w N s.mem 1 - 1)))
    (by omega) s1
  have henv2 := henv1.of_mem_eq (s' := s2) (by dsimp only [s2]; rw [hs2_eq])
  have hgm2 : compGmAt metaBase U w N s2.mem = compGmAt metaBase U w N s.mem := by
    dsimp only [s2]; rw [hs2_eq]
    refine (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) _).2.1.trans ?_
    refine (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) s1.mem).2.1.trans ?_
    dsimp only [s1]; rw [hs1_eq]
    exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) _).2.1.trans
      (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap) (by omega)
        s.mem).2.1
  have htd2 : compTDAt metaBase U w N s2.mem = compTDAt metaBase U w N s.mem := by
    dsimp only [s2]; rw [hs2_eq]
    refine (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) _).2.2.1.trans ?_
    refine (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) s1.mem).2.2.1.trans ?_
    dsimp only [s1]; rw [hs1_eq]
    exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) _).2.2.1.trans
      (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap) (by omega)
        s.mem).2.2.1
  have hdt2 : compDTAt metaBase U w N s2.mem = compDTAt metaBase U w N s.mem := by
    dsimp only [s2]; rw [hs2_eq]
    refine (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) _).2.2.2.trans ?_
    refine (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) s1.mem).2.2.2.trans ?_
    dsimp only [s1]; rw [hs1_eq]
    exact (writeCompVal_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap)
      (by omega) _).2.2.2.trans
      (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item (m_items := m_cap) (by omega)
        s.mem).2.2.2
  have hn'_max : compGmAt metaBase U w N s.mem 1 - 1 < maxTailItems N :=
    lt_of_lt_of_le hn'_lt htail.ntails_le
  have hSN := hslot.multi_total_le hb_pos
  refine validProg_bind (validProg_winShrinkRightGen ⟨U, V, N, henv2.pos_w, henv2.pos_N,
    henv2.le_U, henv2.lt_pow_U, henv2.le_pow_V, rfl, henv2.meta_le_frontier,
    hn'_max, by omega,
    by rw [hdt2, ← hmax_eq]; exact hcpl.dt_lt _,
    by rw [htd2, ← hmax_eq]; exact hcpl.td_lt _⟩) ?_
  obtain ⟨hf3, _, _, _, hgm3, _, _, _⟩ :=
    winShrinkRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m_cap)
      (b_win := compGmAt metaBase U w N s.mem 0 * slabSize N)
      (n_win := compGmAt metaBase U w N s.mem 1 - 1)
      henv.pos_w henv.meta_le_item hn'_max s2
      (by rw [hdt2, ← hmax_eq]; exact hcpl.dt_lt _)
      (by rw [htd2, ← hmax_eq]; exact hcpl.td_lt _)
  have hgm3' := hgm3.trans hgm2
  exact validProg_compRemoveTailGMOnlyGen ⟨U, V, N, henv2.pos_w, henv2.pos_N, henv2.le_U,
    henv2.lt_pow_U, henv2.le_pow_V, rfl, by rw [hf3]; exact henv2.meta_le_frontier, hb_pos, hb,
    tailBijection_of_gm_eq hgm3' htail, by rw [hgm3']; exact hr_pos⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
