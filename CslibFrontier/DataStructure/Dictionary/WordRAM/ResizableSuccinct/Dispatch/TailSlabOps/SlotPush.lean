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
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.TailPush
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.PromoteSlab
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabMove
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabOps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Amortized `O(1)` Compacted Slot Push (`compPushBackSlotGenProg`)

Implements and certifies `compPushBackSlotGenProg`, appending `(q_val, v_val)` at logical slot
`bCount N gm b` of bucket `b` and promoting `K` tail items into a full slab when `r_b + 1 = 2 * K`,
with `O(1)` amortized `memoryCost` against `98 * slotPotential N gm`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compPushBackSlotGenProg`,
  `CompPushBackSlotPre`: compacted bucket-append operation and its parameter-free realization
  precondition.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compPushBackSlotGenProg_effect`,
  `realizesBounded_compPushBackSlotGen`, `validProg_compPushBackSlotGen`: `FixedCoupled` equivalence
  to `pushBackSlotProg`, `O(1)` amortized cost bound, `RealizesBounded .exact` certificate, and
  `ValidProg` admissibility.
-/

public section

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
attribute [local simp] prog_runClient_state_pure StateTransitionSpec.clientResult_map
  StateTransitionSpec.fst_snd_runClient_map
attribute [local simp] Realization.memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

private def compPushBackSingleGenProg :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, (metaBase, itemBase)), q_val), v_val) => do
    let c ← readCompGMGenProg ((cp, metaBase), 0)
    writeCompItemGenProg (((cp, itemBase), c), (q_val, v_val))
    writeCompGMGenProg (((cp, metaBase), 0), c + 1)

private def compPushBackMultiGenProg :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, (metaBase, itemBase)), b), q_val), v_val) => do
    let r_b_new ← compPushBackTailWriteGenProg
      ((((cp, (metaBase, itemBase)), b), q_val), v_val)
    if r_b_new = cpTwoSlabSize cp then
      compPromoteSlabGenProg ((cp, (metaBase, itemBase)), b)
    else
      pure ()

/-- Append `(q_val, v_val)` at logical slot `bCount N gm b` of bucket `b` in compacted layout
`(metaBase, itemBase)`, promoting `K = slabSize N` tail items into a full slab when
`r_b + 1 = 2 * K` (`¬ReadsWidth`). -/
def compPushBackSlotGenProg :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, (metaBase, itemBase)), b), q_val), v_val) =>
    if cpBucketBits cp = 0 then
      compPushBackSingleGenProg (((cp, (metaBase, itemBase)), q_val), v_val)
    else
      compPushBackMultiGenProg ((((cp, (metaBase, itemBase)), b), q_val), v_val)

/-- Precondition for `compPushBackSlotGenProg`. -/
@[expose] def CompPushBackSlotPre (w : ℕ) :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | ((((cp, (metaBase, itemBase)), b), q_val), v_val), s =>
    ∃ U V N m_cap s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      totalSlots N (compGmAt metaBase U w N s.mem) < N ∧
      totalSlots N (compGmAt metaBase U w N s.mem) + 1 ≤ m_cap ∧
      q_val < 2 ^ quotientBits U N ∧
      v_val < 2 ^ valBits V

private theorem promoteSlabInv_and_cap_of_tailWrite
    {metaBase itemBase U V w N m_cap b q_val v_val : ℕ} {s_fix s : Memory.State}
    (hb_pos : 0 < bucketBits N)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hcpl1 : FixedCoupled metaBase itemBase U V w N
      ((Memory.spec 0).clientState s_fix
        (pushBackTailWriteProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
          (((0, b), q_val), v_val)))
      ((Memory.spec 0).clientState s
        (compPushBackTailWriteGenProg
          ((((mkCompParams U V w N, (metaBase, itemBase)), b), q_val), v_val))))
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (htot : totalSlots N (compGmAt metaBase U w N s.mem) < N)
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) + 1 ≤ m_cap)
    (hq_lt : q_val < 2 ^ quotientBits U N) (hv_lt : v_val < 2 ^ valBits V)
    (hprom : compGmAt metaBase U w N s.mem (gmRIdx b) + 1 = 2 * slabSize N) :
    PromoteSlabInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b
        ((Memory.spec 0).clientState s_fix
          (pushBackTailWriteProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
            (((0, b), q_val), v_val))) ∧
      totalSlots N (compGmAt metaBase U w N
        ((Memory.spec 0).clientState s
          (compPushBackTailWriteGenProg
            ((((mkCompParams U V w N, (metaBase, itemBase)), b), q_val), v_val))).mem) ≤
        m_cap := by
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hwg : 0 < ghostW w := by
    unfold ghostW
    omega
  have hslot_fix : SlotStoreInv N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      s_fix.mem) := slotStoreInv_of_gm_eq hcpl.gm_eq.symm hslot
  have htot_fix : totalSlots N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      s_fix.mem) < N := hcpl.gm_eq ▸ htot
  obtain ⟨_, _, _, _, _, htail_f1, hslab_f1, htot_f1, _, hrb_f1, hother_f1, _⟩ :=
    pushBackTailWriteProg_effect (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos s_fix hslot_fix hb htot_fix
      hq_lt hv_lt
  have htot_f0 : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 0 *
      slabSize N + gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 1 < N := by
    unfold totalSlots at htot_fix
    rwa [ite_eq_right hb0] at htot_fix
  refine ⟨⟨hb, htail_f1, hslab_f1, ?_, fun b' hb' hne => ?_, by omega⟩, ?_⟩
  · rw [hrb_f1, congrFun hcpl.gm_eq.symm (gmRIdx b), hprom]
  · rw [(hother_f1 b' hb' hne).1, (hother_f1 b' hb' hne).2]
    exact hslot_fix.multi_r_bounds hb_pos b' hb'
  · rw [hcpl1.gm_eq]
    rw [hcpl.gm_eq] at hm_cap
    unfold totalSlots at hm_cap ⊢
    rw [ite_eq_right hb0] at hm_cap
    rw [ite_eq_right hb0, htot_f1]
    omega

/-- `compPushBackSlotGenProg` maintains `FixedCoupled` with `pushBackSlotProg`, preserves outside
memory via `CompOpFrame`, and satisfies the `O(1)` amortized `memoryCost` bound against
`98 * slotPotential N gm`. -/
theorem compPushBackSlotGenProg_effect {metaBase itemBase U V w N m_cap b q_val v_val : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (htot : totalSlots N (compGmAt metaBase U w N s.mem) < N)
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) + 1 ≤ m_cap)
    (hq_lt : q_val < 2 ^ quotientBits U N) (hv_lt : v_val < 2 ^ valBits V) :
    let d := ((((mkCompParams U V w N, (metaBase, itemBase)), b), q_val), v_val)
    let s' := (Memory.spec 0).clientState s (compPushBackSlotGenProg d)
    let s_fix' := (Memory.spec 0).clientState s_fix
      (pushBackSlotProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, b), q_val), v_val))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' ∧
    memoryCost (compPushBackSlotGenProg d) s +
      98 * slotPotential N (compGmAt metaBase U w N s'.mem) ≤
      98 * slotPotential N (compGmAt metaBase U w N s.mem) + 178 := by
  intro d s' s_fix'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  set gm₀ := compGmAt metaBase U w N s.mem
  have hslot_fix : SlotStoreInv N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      s_fix.mem) := slotStoreInv_of_gm_eq hcpl.gm_eq.symm hslot
  have htot_fix : totalSlots N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      s_fix.mem) < N := by rw [← hcpl.gm_eq]; exact htot
  by_cases hb0 : bucketBits N = 0
  · have hb_eq : b = 0 := by
      have hnb : numBuckets N = 1 := by simp [numBuckets, hb0]
      omega
    subst hb_eq
    unfold totalSlots at htot hm_cap; rw [ite_eq_left hb0] at htot hm_cap
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hc_cap : gm₀ 0 < m_cap := by omega
    have hc1_pow : gm₀ 0 + 1 < 2 ^ globalPtrBits N :=
      lt_two_pow_globalPtrBits_of_le_n_max (by omega)
    set s₁ := (Memory.spec 0).clientState s
      (writeCompQuotGenProg (((mkCompParams U V w N, itemBase), gm₀ 0), q_val))
    set s₂ := (Memory.spec 0).clientState s₁
      (writeCompValGenProg (((mkCompParams U V w N, itemBase), gm₀ 0), v_val))
    set s₃ := (Memory.spec 0).clientState s₂
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase), 0), gm₀ 0 + 1))
    have hs'_eq : s' = s₃ := by
      dsimp only [s', d, compPushBackSlotGenProg, compPushBackSingleGenProg, writeCompItemGenProg]
      simp only [bind_assoc, cpBucketBits_mk, hb0, ↓reduceIte]
      rw [StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg h0_lt,
        clientState_readCompGMGenProg, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_bind]
    obtain ⟨hfr3, hgm3⟩ := compGmFrame_writeCompGMGenProg (metaBase := metaBase)
      (itemBase := itemBase) (U := U) (V := V) (w := w) (N := N) (m_items := gm₀ 0 + 1)
      (idx := 0) (val := gm₀ 0 + 1) henv.pos_w henv.meta_le_item h0_lt hc1_pow s₂
    have hs1_mem : s₁.mem = writeCompQuot itemBase U V w N s.mem (gm₀ 0) q_val := by
      dsimp only [s₁]; rw [clientState_writeCompQuotGenProg]
    have hs2_mem : s₂.mem = writeCompVal itemBase U V w N s₁.mem (gm₀ 0) v_val := by
      dsimp only [s₂]; rw [clientState_writeCompValGenProg]
    have fq := writeCompQuot_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
      (m_items := gm₀ 0 + 1) (q := q_val) henv.pos_w henv.meta_le_item (Nat.lt_succ_self _) s.mem
    have fv := writeCompVal_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
      (m_items := gm₀ 0 + 1) (v := v_val) henv.pos_w henv.meta_le_item (Nat.lt_succ_self _) s₁.mem
    have hgm2 : compGmAt metaBase U w N s₂.mem = gm₀ := by
      rw [hs2_mem, fv.2.1, hs1_mem, fq.2.1]
    rw [hgm2] at hgm3
    have hframe : CompOpFrame metaBase itemBase U V w N m_cap s s' := by
      rw [hs'_eq]
      exact (compOpFrame_writeCompQuot henv.pos_w hc_cap s).trans
        ((compOpFrame_writeCompVal henv.pos_w hc_cap s₁).trans (CompOpFrame.of_gmFrame hfr3))
    obtain ⟨_, _, hq_f1, hv_f1, hl_f1, hg_f1⟩ :=
      writeQuotProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg htot hq_lt s_fix
    obtain ⟨_, _, hq_f2, hv_f2, hl_f2, hg_f2⟩ :=
      writeValProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg htot hv_lt _
    obtain ⟨_, _, hq_f3, hv_f3, hl_f3, hg_f3⟩ :=
      writeGMProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg h0_lt hc1_pow _
    have hgm_fix0 : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 0 =
        gm₀ 0 := congrFun hcpl.gm_eq.symm 0
    have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s_fix
            (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, gm₀ 0), q_val)))
          (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, gm₀ 0), v_val)))
        (writeGMProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, 0), gm₀ 0 + 1)) := by
      dsimp only [s_fix', pushBackSlotProg, pushBackSlotGenProg]
      simp only [p_bucketBits_mk, hb0, ↓reduceIte, readGMGenProg_mk, writeQuotGenProg_mk,
        writeValGenProg_mk, writeGMGenProg_mk]
      rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
        clientResult_readGMProg s_fix h0_lt, hgm_fix0]
      repeat rw [StateTransitionSpec.clientState_bind]
    refine ⟨hframe, ?_, ?_⟩
    · rw [hs'_eq, hs_fix'_eq]
      unfold FixedCoupled
      have hgm3_0 : compGmAt metaBase U w N s₃.mem 0 = gm₀ 0 + 1 := by
        rw [hgm3, Function.update_self]
      have htot3 : epochTotalSlots N (compGmAt metaBase U w N s₃.mem) = gm₀ 0 + 1 := by
        unfold epochTotalSlots; rw [ite_eq_left hb0, hgm3_0]
      have htd3 : compTDAt metaBase U w N s₃.mem = compTDAt metaBase U w N s.mem := by
        rw [hfr3.td_eq, hs2_mem, fv.2.2.1, hs1_mem, fq.2.2.1]
      have hdt3 : compDTAt metaBase U w N s₃.mem = compDTAt metaBase U w N s.mem := by
        rw [hfr3.dt_eq, hs2_mem, fv.2.2.2, hs1_mem, fq.2.2.2]
      have hlm3 : compLmAt metaBase U w N s₃.mem = compLmAt metaBase U w N s.mem := by
        rw [hfr3.lm_eq, hs2_mem, fv.1, hs1_mem, fq.1]
      refine ⟨hgm3.trans (by rw [hg_f3, hg_f2, hg_f1, ← hcpl.gm_eq]),
        hlm3.trans (by rw [hl_f3, hl_f2, hl_f1, ← hcpl.lm_eq]),
        by simp only [hb0, ↓reduceIte]; exact windowInv_zero _ _ _ _,
        fun i => by rw [htd3]; exact hcpl.td_lt i,
        fun i => by rw [hdt3]; exact hcpl.dt_lt i,
        fun idx hidx => ?_,
        fun idx hidx => ?_⟩
      · rw [htot3] at hidx ⊢
        rw [congrFun hfr3.quot_eq idx, hs2_mem, compQuotAt_writeCompVal henv.pos_w, hs1_mem,
          hq_f3, hq_f2, hq_f1]
        have hp_idx : physByBase N (compGmAt metaBase U w N s₃.mem 0 * slabSize N)
            (compDTAt metaBase U w N s₃.mem) idx = idx := by unfold physByBase; simp [hb0]
        rw [hp_idx]
        by_cases heq : idx = gm₀ 0
        · subst heq
          rw [compQuotAt_writeCompQuot_self s.mem (Nat.lt_succ_self _) hq_lt, Function.update_self]
        · have hlt0 : idx < gm₀ 0 := by omega
          rw [compQuotAt_writeCompQuot_of_ne henv.pos_w s.mem heq,
            compQuotAt_of_lt s.mem (by omega : idx < gm₀ 0 + 1) hlt0, Function.update_of_ne heq]
          have hq0 := hcpl.quot_eq idx (by unfold epochTotalSlots; rw [ite_eq_left hb0]; exact hlt0)
          unfold epochTotalSlots physByBase at hq0; simp only [hb0, ↓reduceIte] at hq0
          exact hq0
      · rw [htot3] at hidx ⊢
        rw [congrFun hfr3.val_eq idx, hs2_mem, hs1_mem, hv_f3, hv_f2, hv_f1]
        have hp_idx : physByBase N (compGmAt metaBase U w N s₃.mem 0 * slabSize N)
            (compDTAt metaBase U w N s₃.mem) idx = idx := by unfold physByBase; simp [hb0]
        rw [hp_idx]
        by_cases heq : idx = gm₀ 0
        · subst heq
          rw [compValAt_writeCompVal_self _ (Nat.lt_succ_self _) hv_lt, Function.update_self]
        · have hlt0 : idx < gm₀ 0 := by omega
          rw [compValAt_writeCompVal_of_ne henv.pos_w _ heq,
            compValAt_writeCompQuot henv.pos_w s.mem,
            compValAt_of_lt s.mem (by omega : idx < gm₀ 0 + 1) hlt0, Function.update_of_ne heq]
          have hv0 := hcpl.val_eq idx (by unfold epochTotalSlots; rw [ite_eq_left hb0]; exact hlt0)
          unfold epochTotalSlots physByBase at hv0; simp only [hb0, ↓reduceIte] at hv0
          exact hv0
    · have hcost : memoryCost (compPushBackSlotGenProg d) s = 14 := by
        dsimp only [d, compPushBackSlotGenProg, compPushBackSingleGenProg, writeCompItemGenProg]
        simp [hb0]
      have hpot' : slotPotential N (compGmAt metaBase U w N s'.mem) = 0 := by
        unfold slotPotential; simp [hb0]
      have hpot0 : slotPotential N gm₀ = 0 := by unfold slotPotential; simp [hb0]
      rw [hcost, hpot', hpot0]; omega
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    obtain ⟨hres1, hfr1, hcpl1⟩ :=
      compPushBackTailWrite_effect henv hb_pos hcpl hslot hb htot hm_cap hq_lt hv_lt
    obtain ⟨hres_f1, _, _, _, _, _, _, _, hqb_f1, hrb_f1, hother_f1, _⟩ :=
      pushBackTailWriteProg_effect (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos s_fix hslot_fix hb htot_fix
        hq_lt hv_lt
    set s₁ := (Memory.spec 0).clientState s (compPushBackTailWriteGenProg d)
    set s_fix₁ := (Memory.spec 0).clientState s_fix
      (pushBackTailWriteProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, b), q_val), v_val))
    have hgm0_rb_eq : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
        (gmRIdx b) = gm₀ (gmRIdx b) := congrFun hcpl.gm_eq.symm (gmRIdx b)
    rw [hgm0_rb_eq] at hres_f1 hrb_f1
    by_cases hprom : gm₀ (gmRIdx b) + 1 = 2 * slabSize N
    · have hs'_eq : s' = (Memory.spec 0).clientState s₁
          (compPromoteSlabGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b)) := by
        dsimp only [s', d, compPushBackSlotGenProg, compPushBackMultiGenProg]
        simp only [cpBucketBits_mk, hb0, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, hres1, cpTwoSlabSize_mk, ite_eq_left hprom]
      have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState s_fix₁
          (promoteSlabProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)) := by
        dsimp only [s_fix', pushBackSlotProg, pushBackSlotGenProg]
        simp only [p_bucketBits_mk, hb0, ↓reduceIte, pushBackTailWriteGenProg_mk,
          p_twoSlabSize_mk, promoteSlabGenProg_mk]
        rw [StateTransitionSpec.clientState_bind, hres_f1, ite_eq_left hprom]
      obtain ⟨hpre_prom, hm_cap1⟩ :
          PromoteSlabInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b s_fix₁ ∧
            totalSlots N (compGmAt metaBase U w N s₁.mem) ≤ m_cap :=
        promoteSlabInv_and_cap_of_tailWrite hb_pos hcpl hcpl1 hslot hb htot hm_cap hq_lt hv_lt hprom
      obtain ⟨hfr2, hcpl2, hcost2⟩ :=
        compPromoteSlab_effect (henv.of_mem_eq (s' := s₁) (by rw [hfr1.frontier_eq]))
          hb_pos hpre_prom hcpl1 hm_cap1
      obtain ⟨_, _, _, _, hqb_f2, hrb_f2, hother_f2, _, _, _⟩ :=
        promoteSlabProg_effect hwg hb_pos s_fix₁ hpre_prom
      have hcost_tot : memoryCost (compPushBackSlotGenProg d) s ≤ 42 + (98 * slabSize N + 38) := by
        dsimp only [d, compPushBackSlotGenProg, compPushBackMultiGenProg]
        simp only [cpBucketBits_mk, hb0, ↓reduceIte,
          Realization.memoryCost_bind', memoryCost_compPushBackTailWriteGenProg]
        rw [hres1, cpTwoSlabSize_mk, ite_eq_left hprom]
        exact Nat.add_le_add_left hcost2 42
      have hupd : compGmAt metaBase U w N s'.mem (gmQIdx b) =
            (pushBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).1 ∧
          compGmAt metaBase U w N s'.mem (gmRIdx b) =
            (pushBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).2 := by
        unfold pushBackCounts; rw [ite_eq_left hprom]
        rw [hs'_eq, hcpl2.gm_eq]
        exact ⟨hqb_f2.trans
          (congrArg (· + 1) (hqb_f1.trans (congrFun hcpl.gm_eq.symm (gmQIdx b)))), hrb_f2⟩
      have hother_all : ∀ b' < numBuckets N, b' ≠ b →
          compGmAt metaBase U w N s'.mem (gmQIdx b') = gm₀ (gmQIdx b') ∧
          compGmAt metaBase U w N s'.mem (gmRIdx b') = gm₀ (gmRIdx b') := by
        intro b' hb' hne
        rw [hs'_eq, hcpl2.gm_eq]
        exact ⟨(hother_f2 b' hb' hne).1.trans ((hother_f1 b' hb' hne).1.trans
            (congrFun hcpl.gm_eq.symm _)),
          (hother_f2 b' hb' hne).2.trans ((hother_f1 b' hb' hne).2.trans
            (congrFun hcpl.gm_eq.symm _))⟩
      have hpot := slotPotential_pushBack_le hb_pos hb hupd hother_all
      have hwork : pushBackWork (slabSize N) (gm₀ (gmRIdx b)) = slabSize N := by
        unfold pushBackWork; rw [ite_eq_left hprom]
      rw [hwork] at hpot
      exact ⟨by rw [hs'_eq]; exact hfr1.trans hfr2,
        by rw [hs'_eq, hs_fix'_eq]; exact hcpl2,
        by omega⟩
    · have hs'_eq : s' = s₁ := by
        dsimp only [s', d, compPushBackSlotGenProg, compPushBackMultiGenProg]
        simp only [cpBucketBits_mk, hb0, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, hres1, cpTwoSlabSize_mk, ite_eq_right hprom,
          StateTransitionSpec.clientState_pure]
      have hs_fix'_eq : s_fix' = s_fix₁ := by
        dsimp only [s_fix', pushBackSlotProg, pushBackSlotGenProg]
        simp only [p_bucketBits_mk, hb0, ↓reduceIte, pushBackTailWriteGenProg_mk,
          p_twoSlabSize_mk, promoteSlabGenProg_mk]
        rw [StateTransitionSpec.clientState_bind, hres_f1, ite_eq_right hprom,
          StateTransitionSpec.clientState_pure]
      have hcost_tot : memoryCost (compPushBackSlotGenProg d) s = 42 := by
        dsimp only [d, compPushBackSlotGenProg, compPushBackMultiGenProg]
        simp only [cpBucketBits_mk, hb0, ↓reduceIte,
          Realization.memoryCost_bind', memoryCost_compPushBackTailWriteGenProg]
        rw [hres1, cpTwoSlabSize_mk, ite_eq_right hprom, memoryCost_pure, Nat.add_zero]
      have hupd : compGmAt metaBase U w N s'.mem (gmQIdx b) =
            (pushBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).1 ∧
          compGmAt metaBase U w N s'.mem (gmRIdx b) =
            (pushBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).2 := by
        unfold pushBackCounts; rw [ite_eq_right hprom, hs'_eq, hcpl1.gm_eq]
        exact ⟨hqb_f1.trans (congrFun hcpl.gm_eq.symm _), hrb_f1⟩
      have hother_all : ∀ b' < numBuckets N, b' ≠ b →
          compGmAt metaBase U w N s'.mem (gmQIdx b') = gm₀ (gmQIdx b') ∧
          compGmAt metaBase U w N s'.mem (gmRIdx b') = gm₀ (gmRIdx b') := by
        intro b' hb' hne
        rw [hs'_eq, hcpl1.gm_eq]
        exact ⟨(hother_f1 b' hb' hne).1.trans (congrFun hcpl.gm_eq.symm _),
          (hother_f1 b' hb' hne).2.trans (congrFun hcpl.gm_eq.symm _)⟩
      have hpot := slotPotential_pushBack_le hb_pos hb hupd hother_all
      have hwork : pushBackWork (slabSize N) (gm₀ (gmRIdx b)) = 0 := by
        unfold pushBackWork; rw [ite_eq_right hprom]
      rw [hwork, Nat.add_zero] at hpot
      exact ⟨by rw [hs'_eq]; exact hfr1,
        by rw [hs'_eq, hs_fix'_eq]; exact hcpl1,
        by omega⟩

private theorem realizesBounded_compPushBackMultiGen :
    RealizesBounded .exact compPushBackMultiGenProg
      (WordEncoding.encode (α := (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompPushBackTailWritePre (fun _ _ => 0) := by
  have htw := realizesBounded_compPushBackTailWriteGen
  have hpr := realizesBounded_compPromoteSlabGen
  realize
  · exact h
  · rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, q_val⟩, v_val⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, htot, hm_cap,
      hq_lt, hv_lt⟩ := h
    obtain ⟨hres1, hfr1, hcpl1⟩ :=
      compPushBackTailWrite_effect henv hb_pos hcpl hslot hb htot hm_cap hq_lt hv_lt
    rw [hres1, cpTwoSlabSize_mk] at hc
    obtain ⟨hpre_prom, hm_cap1⟩ := promoteSlabInv_and_cap_of_tailWrite hb_pos hcpl hcpl1
      hslot hb htot hm_cap hq_lt hv_lt hc
    exact ⟨U, V, N, m_cap, _, rfl,
      henv.of_mem_eq (by rw [hfr1.frontier_eq]),
      hb_pos, hpre_prom, hcpl1, hm_cap1⟩

private def CompPushBackSinglePre (w : ℕ) :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), _q_val), _v_val), s =>
    ∃ U V N m_cap,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      compGmAt metaBase U w N s.mem 0 < N ∧
      compGmAt metaBase U w N s.mem 0 < m_cap

private theorem realizesBounded_compPushBackSingleGen :
    RealizesBounded .exact compPushBackSingleGenProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompPushBackSinglePre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hwit := realizesBounded_writeCompItemGen
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, q_val⟩, v_val⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, rfl, henv, hc_lt_N, hc_lt_cap⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    try simp only [StateTransitionSpec.clientState, runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg h0_lt] at *)
  · exact ⟨henv.compMetaEnv, by simp only [cpN_mk]; exact h0_lt⟩
  all_goals try {
    change Fits w _
    exact lt_of_le_of_lt (by have := henv.le_U; omega) henv.lt_pow_U
  }
  · exact ⟨m_cap, henv.compItemEnv, hc_lt_cap⟩
  · refine ⟨(henv.of_mem_eq ?_).compMetaEnv, by simp only [cpN_mk]; exact h0_lt⟩
    change s.frontier ≤ ((Memory.spec 0).clientState s _).frontier
    dsimp only [writeCompItemGenProg]
    rw [StateTransitionSpec.clientState_bind, clientState_writeCompValGenProg,
      clientState_writeCompQuotGenProg]

theorem realizesBounded_compPushBackSlotGen :
    RealizesBounded .exact compPushBackSlotGenProg
      (WordEncoding.encode (α := (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompPushBackSlotPre (fun _ _ => 0) := by
  have hsng := realizesBounded_compPushBackSingleGen
  have hmul := realizesBounded_compPushBackMultiGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, q_val⟩, v_val⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hcpl, hslot, hb, htot, hm_cap, hq_lt, hv_lt⟩ := h)
  · rw [cpBucketBits_mk] at hc
    unfold totalSlots at htot hm_cap; rw [ite_eq_left hc] at htot hm_cap
    exact ⟨U, V, N, m_cap, rfl, henv, htot, by omega⟩
  · rw [cpBucketBits_mk] at hc
    exact ⟨U, V, N, m_cap, s_fix, rfl, henv, Nat.pos_of_ne_zero hc, hcpl, hslot, hb, htot,
      hm_cap, hq_lt, hv_lt⟩

theorem validProg_compPushBackSlotGen {w : ℕ}
    {d : (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (h : CompPushBackSlotPre w d s) :
    ValidProg w 0 s (compPushBackSlotGenProg d) := by
  rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, q_val⟩, v_val⟩
  obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hcpl, hslot, hb, htot, hm_cap, hq_lt, hv_lt⟩ := h
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  dsimp only [compPushBackSlotGenProg, compPushBackSingleGenProg, compPushBackMultiGenProg]
  simp only [cpBucketBits_mk, cpTwoSlabSize_mk]
  refine validProg_ite (fun hb0 => ?_) (fun hb0 => ?_)
  · unfold totalSlots at hm_cap; rw [ite_eq_left hb0] at hm_cap
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h0_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg h0_lt]
    set c0 := compGmAt metaBase U w N s.mem 0
    refine validProg_bind_unit
      (validProg_writeCompItemGen ⟨m_cap, henv.compItemEnv, by omega⟩) fun s2 hs2 => ?_
    have hf2 : s2.frontier = s.frontier := by
      rw [hs2]; dsimp only [writeCompItemGenProg]
      rw [StateTransitionSpec.clientState_bind, clientState_writeCompValGenProg,
        clientState_writeCompQuotGenProg]
    exact validProg_writeCompGMGen ⟨(henv.of_mem_eq (by rw [hf2])).compMetaEnv, h0_lt⟩
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    obtain ⟨hres1, hfr1, hcpl1⟩ :=
      compPushBackTailWrite_effect henv hb_pos hcpl hslot hb htot hm_cap hq_lt hv_lt
    refine validProg_bind
      (validProg_compPushBackTailWriteGen
        ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, htot, hm_cap, hq_lt, hv_lt⟩)
      ?_
    rw [hres1]
    refine validProg_ite (fun hprom => ?_) (fun _ => validProg_pure ())
    obtain ⟨hpre_prom, hm_cap1⟩ := promoteSlabInv_and_cap_of_tailWrite hb_pos hcpl hcpl1
      hslot hb htot hm_cap hq_lt hv_lt hprom
    exact validProg_compPromoteSlabGen ⟨U, V, N, m_cap, _, rfl,
      henv.of_mem_eq (by rw [hfr1.frontier_eq]), hb_pos, hpre_prom, hcpl1, hm_cap1⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

end
