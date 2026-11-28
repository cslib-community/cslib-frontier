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
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.TailRemove
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.DemoteSlab
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabDemote
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabOps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Amortized `O(1)` Compacted Slot Pop (`compPopBackSlotGenProg`)

Implements and certifies `compPopBackSlotGenProg`, removing the last logical slot
`bCount N gm b - 1` of non-empty bucket `b` and demoting the top full slab into `K` tail items when
`r_b - 1 = 0 ∧ 0 < q_b`, with `O(1)` amortized `memoryCost` against `98 * slotPotential N gm`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compPopBackSlotGenProg`,
  `CompPopBackSlotPre`: compacted bucket-pop operation and its parameter-free realization
  precondition.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compPopBackSlotGenProg_effect`,
  `realizesBounded_compPopBackSlotGen`, `validProg_compPopBackSlotGen`: `FixedCoupled` equivalence
  to `popBackSlotProg`, `O(1)` amortized cost bound, `RealizesBounded .exact` certificate, and
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

private def compPopBackSingleGenProg : CompParams × ℕ → Memory.Prog Unit
  | (cp, metaBase) => do
    let c ← readCompGMGenProg ((cp, metaBase), 0)
    writeCompGMGenProg (((cp, metaBase), 0), c - 1)

private def compPopBackFinishProg :
    ((CompParams × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, (metaBase, itemBase)), b), (r_b_new, q_b)) =>
    if r_b_new = 0 then
      if 0 < q_b then
        compDemoteSlabGenProg ((cp, (metaBase, itemBase)), b)
      else
        pure ()
    else
      pure ()

private def compPopBackMultiGenProg : (CompParams × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((cp, (metaBase, itemBase)), b) => do
    compRemoveLastTailItemGenProg ((cp, (metaBase, itemBase)), b)
    let q_idx := 4 + (b + b + b)
    let r_b_new ← readCompGMGenProg ((cp, metaBase), q_idx + 1)
    let q_b ← readCompGMGenProg ((cp, metaBase), q_idx)
    compPopBackFinishProg (((cp, (metaBase, itemBase)), b), (r_b_new, q_b))

/-- Remove the last logical slot `bCount N gm b - 1` of non-empty bucket `b` in compacted layout
`(metaBase, itemBase)`, demoting the top full slab into `K = slabSize N` tail items when
`r_b - 1 = 0 ∧ 0 < q_b` (`¬ReadsWidth`). -/
def compPopBackSlotGenProg : (CompParams × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((cp, (metaBase, itemBase)), b) =>
    if cpBucketBits cp = 0 then
      compPopBackSingleGenProg (cp, metaBase)
    else
      compPopBackMultiGenProg ((cp, (metaBase, itemBase)), b)

/-- Precondition for `compPopBackSlotGenProg`. -/
@[expose] def CompPopBackSlotPre (w : ℕ) : (CompParams × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((cp, (metaBase, itemBase)), b), s =>
    ∃ U V N m_cap s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      1 ≤ bCount N (compGmAt metaBase U w N s.mem) b ∧
      totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap

/-- `compPopBackSlotGenProg` maintains `FixedCoupled` with `popBackSlotProg`, preserves outside
memory via `CompOpFrame`, and satisfies the `O(1)` amortized `memoryCost` bound against
`98 * slotPotential N gm`. -/
theorem compPopBackSlotGenProg_effect {metaBase itemBase U V w N m_cap b : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (hbc : 1 ≤ bCount N (compGmAt metaBase U w N s.mem) b)
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap) :
    let d := ((mkCompParams U V w N, (metaBase, itemBase)), b)
    let s' := (Memory.spec 0).clientState s (compPopBackSlotGenProg d)
    let s_fix' := (Memory.spec 0).clientState s_fix
      (popBackSlotProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' ∧
    memoryCost (compPopBackSlotGenProg d) s +
      98 * slotPotential N (compGmAt metaBase U w N s'.mem) ≤
      98 * slotPotential N (compGmAt metaBase U w N s.mem) + 242 := by
  intro d s' s_fix'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  set gm₀ := compGmAt metaBase U w N s.mem
  have hslot_fix : SlotStoreInv N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      s_fix.mem) := slotStoreInv_of_gm_eq hcpl.gm_eq.symm hslot
  by_cases hb0 : bucketBits N = 0
  · obtain rfl : b = 0 := Nat.lt_one_iff.mp (by simpa [numBuckets, hb0] using hb)
    unfold bCount at hbc; simp only [hb0, ↓reduceIte] at hbc
    have hgm0_le : gm₀ 0 ≤ N := hslot.single_valid hb0
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hc_pow : gm₀ 0 - 1 < 2 ^ globalPtrBits N :=
      lt_two_pow_globalPtrBits_of_le_n_max (by omega)
    set s₁ := (Memory.spec 0).clientState s
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase), 0), gm₀ 0 - 1))
    have hs'_eq : s' = s₁ := by
      dsimp only [s', d, compPopBackSlotGenProg, compPopBackSingleGenProg]
      simp only [cpBucketBits_mk, hb0, ↓reduceIte]
      rw [StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg h0_lt,
        clientState_readCompGMGenProg]
    obtain ⟨hfr1, hgm1⟩ := compGmFrame_writeCompGMGenProg (metaBase := metaBase)
      (itemBase := itemBase) (U := U) (V := V) (w := w) (N := N) (m_items := gm₀ 0)
      (idx := 0) (val := gm₀ 0 - 1) henv.pos_w henv.meta_le_item h0_lt hc_pow s
    obtain ⟨_, _, hq_f1, hv_f1, hl_f1, hg_f1⟩ :=
      writeGMProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg h0_lt hc_pow s_fix
    have hgm_fix0 : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem 0 =
        gm₀ 0 := congrFun hcpl.gm_eq.symm 0
    have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState s_fix
        (writeGMProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, 0), gm₀ 0 - 1)) := by
      dsimp only [s_fix', popBackSlotProg, popBackSlotGenProg]
      simp only [p_bucketBits_mk, hb0, ↓reduceIte, readGMGenProg_mk, writeGMGenProg_mk]
      rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
        clientResult_readGMProg s_fix h0_lt, hgm_fix0]
    refine ⟨by rw [hs'_eq]; exact CompOpFrame.of_gmFrame hfr1, ?_, ?_⟩
    · rw [hs'_eq, hs_fix'_eq]
      unfold FixedCoupled
      have htot1 : epochTotalSlots N (compGmAt metaBase U w N s₁.mem) = gm₀ 0 - 1 := by
        rw [epochTotalSlots, ite_eq_left hb0, hgm1, Function.update_self]
      refine ⟨hgm1.trans (by rw [hg_f1, ← hcpl.gm_eq]),
        hfr1.lm_eq.trans (by rw [hl_f1, ← hcpl.lm_eq]),
        by simp only [hb0, ↓reduceIte]; exact windowInv_zero _ _ _ _,
        fun i => by rw [hfr1.td_eq]; exact hcpl.td_lt i,
        fun i => by rw [hfr1.dt_eq]; exact hcpl.dt_lt i,
        fun idx hidx => ?_,
        fun idx hidx => ?_⟩
      · rw [htot1] at hidx ⊢
        rw [compQuotAt_of_lt s₁.mem hidx (Nat.lt_of_lt_of_le hidx (Nat.sub_le _ _)),
          congrFun hfr1.quot_eq idx, hq_f1]
        simpa only [epochTotalSlots, physByBase, hb0, ↓reduceIte] using
          hcpl.quot_eq idx (by simpa only [epochTotalSlots, hb0, ↓reduceIte] using
              Nat.lt_of_lt_of_le hidx (Nat.sub_le _ _))
      · rw [htot1] at hidx ⊢
        rw [compValAt_of_lt s₁.mem hidx (Nat.lt_of_lt_of_le hidx (Nat.sub_le _ _)),
          congrFun hfr1.val_eq idx, hv_f1]
        simpa only [epochTotalSlots, physByBase, hb0, ↓reduceIte] using
          hcpl.val_eq idx (by simpa only [epochTotalSlots, hb0, ↓reduceIte] using
              Nat.lt_of_lt_of_le hidx (Nat.sub_le _ _))
    · simp [d, compPopBackSlotGenProg, compPopBackSingleGenProg, hb0, slotPotential]
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have hK_pos : 0 < slabSize N := slabSize_pos N
    have hr_pos : 1 ≤ gm₀ (gmRIdx b) := pos_gmRIdx_of_pos_bCount hb_pos hslot hb hbc
    have hr2_lt : gm₀ (gmRIdx b) < 2 * slabSize N := by
      simpa only [tailCapPerBucket, ite_eq_right hb0] using (hslot.multi_r_bounds hb_pos b hb).1
    obtain ⟨hfr1, hcpl1⟩ :=
      compRemoveLastTailItem_effect henv hb_pos hcpl hslot hb hr_pos hm_cap
    obtain ⟨_, _, _, _, _, hgm_f1⟩ :=
      removeLastTailItemProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos hb s_fix
        (hslot_fix.multi_tail hb_pos) (by rw [← hcpl.gm_eq]; exact hr_pos)
    set s₁ := (Memory.spec 0).clientState s (compRemoveLastTailItemGenProg d)
    set s_fix₁ := (Memory.spec 0).clientState s_fix
      (removeLastTailItemProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b))
    have hgm1_eq : compGmAt metaBase U w N s₁.mem = gmRemoveTail N gm₀ b :=
      hcpl1.gm_eq.trans (hgm_f1.trans (congrArg (fun g => gmRemoveTail N g b) hcpl.gm_eq.symm))
    have htail₀ := hslot.multi_tail hb_pos
    have hslab₀ := hslot.multi_slab hb_pos
    have hpres1 := gmRemoveTail_preserves_nonTail hb hr_pos htail₀
    have htail1 := tailBijection_gmRemoveTail hb hr_pos htail₀
    have ⟨_, hslab1⟩ := slabBijection_gmRemoveTail hb hr_pos htail₀ hslab₀
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have hr_eq : gmQIdx b + 1 = gmRIdx b := rfl
    have hq_eq_fix : 4 + 3 * b = gmQIdx b := rfl
    have hrb1_s : compGmAt metaBase U w N s₁.mem (gmRIdx b) = gm₀ (gmRIdx b) - 1 := by
      rw [hgm1_eq, hpres1.2.2.1]
    have hqb1_s : compGmAt metaBase U w N s₁.mem (gmQIdx b) = gm₀ (gmQIdx b) := by
      rw [hgm1_eq, hpres1.2.2.2.2.1 b hb]
    have hrb1_f : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix₁.mem (gmRIdx b) =
        gm₀ (gmRIdx b) - 1 := by rw [← hcpl1.gm_eq, hrb1_s]
    have hqb1_f : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix₁.mem (gmQIdx b) =
        gm₀ (gmQIdx b) := by rw [← hcpl1.gm_eq, hqb1_s]
    by_cases hdem : gm₀ (gmRIdx b) - 1 = 0 ∧ 0 < gm₀ (gmQIdx b)
    · obtain ⟨hr0, hq_pos⟩ := hdem
      have hs'_eq : s' = (Memory.spec 0).clientState s₁ (compDemoteSlabGenProg d) := by
        dsimp only [s', d, compPopBackSlotGenProg, compPopBackMultiGenProg, compPopBackFinishProg]
        simp only [cpBucketBits_mk, hb0, ↓reduceIte, hq_eq, hr_eq]
        rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
          clientResult_readCompGMGenProg hr_idx_lt, clientState_readCompGMGenProg,
          StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg hq_idx_lt,
          clientState_readCompGMGenProg, hrb1_s, hqb1_s, ite_eq_left hr0, ite_eq_left hq_pos]
      have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState s_fix₁
          (demoteSlabProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)) := by
        dsimp only [s_fix', popBackSlotProg, popBackSlotGenProg]
        simp only [p_bucketBits_mk, hb0, ↓reduceIte, removeLastTailItemGenProg_mk,
          readGMGenProg_mk, demoteSlabGenProg_mk, hq_eq_fix, hr_eq]
        rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
          clientState_readGMProg, clientResult_readGMProg s_fix₁ hr_idx_lt,
          StateTransitionSpec.clientState_bind, clientState_readGMProg,
          clientResult_readGMProg s_fix₁ hq_idx_lt, hrb1_f, hqb1_f,
          ite_eq_left hr0, ite_eq_left hq_pos]
      have hSN0 := hslot.multi_total_le hb_pos
      have hpre_dem : DemoteSlabInv U V (ghostW w) N (epochHashSpace U (ghostW w) N)
          0 b s_fix₁ := by
        refine ⟨hb, hcpl1.gm_eq ▸ hgm1_eq ▸ htail1, hcpl1.gm_eq ▸ hgm1_eq ▸ hslab1,
          hrb1_f.trans hr0, hqb1_f.symm ▸ hq_pos, fun b' hb' hne => ?_, ?_⟩
        · rw [← hcpl1.gm_eq, hgm1_eq, hpres1.2.2.2.1 b' hb' hne, hpres1.2.2.2.2.1 b' hb']
          exact hslot.multi_r_bounds hb_pos b' hb'
        · rw [← hcpl1.gm_eq, hgm1_eq, hpres1.1, hpres1.2.1]; omega
      have hm_cap1 : totalSlots N (compGmAt metaBase U w N s₁.mem) ≤ m_cap := by
        simp only [totalSlots, hb0, ↓reduceIte, hgm1_eq, hpres1.1, hpres1.2.1] at hm_cap ⊢
        omega
      obtain ⟨hfr2, hcpl2, hcost2⟩ :=
        compDemoteSlab_effect (henv.of_mem_eq (s' := s₁) (by rw [hfr1.frontier_eq]))
          hb_pos hpre_dem hcpl1 hm_cap1
      obtain ⟨_, _, _, _, hqb_f2, hrb_f2, hother_f2, _, _, _⟩ :=
        demoteSlabProg_effect hwg hb_pos s_fix₁ hpre_dem
      have hcost_tot : memoryCost (compPopBackSlotGenProg d) s ≤ 76 + (58 * slabSize N + 68) := by
        dsimp only [d, compPopBackSlotGenProg, compPopBackMultiGenProg, compPopBackFinishProg]
        simp only [cpBucketBits_mk, hb0, ↓reduceIte, hq_eq, hr_eq,
          Realization.memoryCost_bind', memoryCost_compRemoveLastTailItemGenProg,
          memoryCost_readCompGMGenProg]
        rw [clientResult_readCompGMGenProg hr_idx_lt, clientState_readCompGMGenProg,
          clientResult_readCompGMGenProg hq_idx_lt, clientState_readCompGMGenProg,
          hrb1_s, hqb1_s, ite_eq_left hr0, ite_eq_left hq_pos]
        dsimp only [s₁, d] at hcost2
        omega
      have hr1_eq : gm₀ (gmRIdx b) = 1 := by omega
      have hupd : compGmAt metaBase U w N s'.mem (gmQIdx b) =
            (popBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).1 ∧
          compGmAt metaBase U w N s'.mem (gmRIdx b) =
            (popBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).2 := by
        rw [popBackCounts, hr1_eq, ite_eq_left ⟨rfl, hq_pos⟩, hs'_eq, hcpl2.gm_eq]
        exact ⟨hqb_f2.trans (congrArg (· - 1) hqb1_f), hrb_f2⟩
      have hother_all : ∀ b' < numBuckets N, b' ≠ b →
          compGmAt metaBase U w N s'.mem (gmQIdx b') = gm₀ (gmQIdx b') ∧
          compGmAt metaBase U w N s'.mem (gmRIdx b') = gm₀ (gmRIdx b') := fun b' hb' hne => by
        rw [hs'_eq, hcpl2.gm_eq, (hother_f2 b' hb' hne).1, (hother_f2 b' hb' hne).2,
          ← hcpl1.gm_eq, hgm1_eq]
        exact ⟨hpres1.2.2.2.2.1 b' hb', hpres1.2.2.2.1 b' hb' hne⟩
      have hpot := slotPotential_popBack_le hb_pos hb hr_pos hr2_lt hupd hother_all
      rw [popBackWork, hr1_eq, ite_eq_left ⟨rfl, hq_pos⟩] at hpot
      exact ⟨hs'_eq ▸ hfr1.trans hfr2, hs'_eq ▸ hs_fix'_eq ▸ hcpl2, by omega⟩
    · have hndem1 : ¬ (gm₀ (gmRIdx b) = 1 ∧ 0 < gm₀ (gmQIdx b)) :=
        fun ⟨h1, h2⟩ => hdem ⟨by omega, h2⟩
      have hite {α} (x y : α) :
          (if gm₀ (gmRIdx b) - 1 = 0 then if 0 < gm₀ (gmQIdx b) then x else y else y) = y := by
        split_ifs with h1 h2 <;> first | rfl | exact absurd ⟨h1, h2⟩ hdem
      have hs'_eq : s' = s₁ := by
        dsimp only [s', d, compPopBackSlotGenProg, compPopBackMultiGenProg, compPopBackFinishProg]
        simp only [cpBucketBits_mk, hb0, ↓reduceIte, hq_eq, hr_eq]
        rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
          clientResult_readCompGMGenProg hr_idx_lt, clientState_readCompGMGenProg,
          StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg hq_idx_lt,
          clientState_readCompGMGenProg, hrb1_s, hqb1_s, hite,
          StateTransitionSpec.clientState_pure]
      have hs_fix'_eq : s_fix' = s_fix₁ := by
        dsimp only [s_fix', popBackSlotProg, popBackSlotGenProg]
        simp only [p_bucketBits_mk, hb0, ↓reduceIte, removeLastTailItemGenProg_mk,
          readGMGenProg_mk, demoteSlabGenProg_mk, hq_eq_fix, hr_eq]
        rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
          clientState_readGMProg, clientResult_readGMProg s_fix₁ hr_idx_lt,
          StateTransitionSpec.clientState_bind, clientState_readGMProg,
          clientResult_readGMProg s_fix₁ hq_idx_lt, hrb1_f, hqb1_f, hite,
          StateTransitionSpec.clientState_pure]
      have hcost_tot : memoryCost (compPopBackSlotGenProg d) s = 76 := by
        dsimp only [d, compPopBackSlotGenProg, compPopBackMultiGenProg, compPopBackFinishProg]
        simp only [cpBucketBits_mk, hb0, ↓reduceIte, hq_eq, hr_eq,
          Realization.memoryCost_bind', memoryCost_compRemoveLastTailItemGenProg,
          memoryCost_readCompGMGenProg]
        rw [clientResult_readCompGMGenProg hr_idx_lt, clientState_readCompGMGenProg,
          clientResult_readCompGMGenProg hq_idx_lt, clientState_readCompGMGenProg,
          hrb1_s, hqb1_s, hite, memoryCost_pure, Nat.add_zero]
      have hupd : compGmAt metaBase U w N s'.mem (gmQIdx b) =
            (popBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).1 ∧
          compGmAt metaBase U w N s'.mem (gmRIdx b) =
            (popBackCounts (slabSize N) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).2 := by
        simp only [popBackCounts, ite_eq_right hndem1, hs'_eq, hqb1_s, hrb1_s, and_self]
      have hother_all : ∀ b' < numBuckets N, b' ≠ b →
          compGmAt metaBase U w N s'.mem (gmQIdx b') = gm₀ (gmQIdx b') ∧
          compGmAt metaBase U w N s'.mem (gmRIdx b') = gm₀ (gmRIdx b') := fun b' hb' hne => by
        rw [hs'_eq, hgm1_eq]
        exact ⟨hpres1.2.2.2.2.1 b' hb', hpres1.2.2.2.1 b' hb' hne⟩
      have hpot := slotPotential_popBack_le hb_pos hb hr_pos hr2_lt hupd hother_all
      rw [popBackWork, ite_eq_right hndem1, Nat.add_zero] at hpot
      exact ⟨hs'_eq ▸ hfr1, hs'_eq ▸ hs_fix'_eq ▸ hcpl1, by omega⟩

private def CompPopBackFinishPre (w : ℕ) :
    ((CompParams × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), b), (r_b_new, q_b)), s =>
    CompMetaEnv w cp metaBase s ∧
    (r_b_new = 0 → 0 < q_b → CompDemoteSlabPre w ((cp, (metaBase, itemBase)), b) s)

private theorem realizesBounded_compPopBackFinish :
    RealizesBounded .exact compPopBackFinishProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompPopBackFinishPre (fun _ _ => 0) := by
  realize [realizesBounded_compDemoteSlabGen]
  rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, ⟨r_b_new, q_b⟩⟩
  dsimp only at *
  exact h.2 ‹r_b_new = 0› ‹0 < q_b›

private theorem compDemoteSlabPre_of_removeTail {metaBase itemBase U V w N m_cap b : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hb_pos : 0 < bucketBits N)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N) (hr_pos : 1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b))
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap)
    (hr0_eq : compGmAt metaBase U w N
      ((Memory.spec 0).clientState s
        (compRemoveLastTailItemGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b))).mem
      (gmRIdx b) = 0)
    (hq_pos_eq : 0 < compGmAt metaBase U w N
      ((Memory.spec 0).clientState s
        (compRemoveLastTailItemGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b))).mem
      (gmQIdx b)) :
    CompDemoteSlabPre w ((mkCompParams U V w N, (metaBase, itemBase)), b)
      ((Memory.spec 0).clientState s
        (compRemoveLastTailItemGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b))) := by
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  obtain ⟨hfr1, hcpl1⟩ := compRemoveLastTailItem_effect henv hb_pos hcpl hslot hb hr_pos hm_cap
  set s₁ := (Memory.spec 0).clientState s
    (compRemoveLastTailItemGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b))
  obtain ⟨_, _, _, _, _, hgm_f1⟩ :=
    removeLastTailItemProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos hb s_fix
      ((slotStoreInv_of_gm_eq hcpl.gm_eq.symm hslot).multi_tail hb_pos) (hcpl.gm_eq ▸ hr_pos)
  set s_fix₁ := (Memory.spec 0).clientState s_fix
    (removeLastTailItemProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b))
  have hgm1_eq : compGmAt metaBase U w N s₁.mem =
      gmRemoveTail N (compGmAt metaBase U w N s.mem) b :=
    hcpl1.gm_eq.trans (hgm_f1.trans (congrArg (fun g => gmRemoveTail N g b) hcpl.gm_eq.symm))
  have htail₀ := hslot.multi_tail hb_pos
  have hpres1 := gmRemoveTail_preserves_nonTail hb hr_pos htail₀
  have htail1 := tailBijection_gmRemoveTail hb hr_pos htail₀
  have ⟨_, hslab1⟩ := slabBijection_gmRemoveTail hb hr_pos htail₀ (hslot.multi_slab hb_pos)
  have hSN0 := hslot.multi_total_le hb_pos
  have hpre_dem : DemoteSlabInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b s_fix₁ := by
    refine ⟨hb, hcpl1.gm_eq ▸ hgm1_eq ▸ htail1, hcpl1.gm_eq ▸ hgm1_eq ▸ hslab1,
      hcpl1.gm_eq ▸ hr0_eq, hcpl1.gm_eq ▸ hq_pos_eq, fun b' hb' hne => ?_, ?_⟩
    · rw [← hcpl1.gm_eq, hgm1_eq, hpres1.2.2.2.1 b' hb' hne, hpres1.2.2.2.2.1 b' hb']
      exact hslot.multi_r_bounds hb_pos b' hb'
    · rw [← hcpl1.gm_eq, hgm1_eq, hpres1.1, hpres1.2.1]; omega
  have hm_cap1 : totalSlots N (compGmAt metaBase U w N s₁.mem) ≤ m_cap := by
    simp only [totalSlots, ite_eq_right hb0, hgm1_eq, hpres1.1, hpres1.2.1] at hm_cap ⊢; omega
  exact ⟨U, V, N, m_cap, s_fix₁, rfl, henv.of_mem_eq (by rw [hfr1.frontier_eq]),
    hb_pos, hpre_dem, hcpl1, hm_cap1⟩

private theorem realizesBounded_compPopBackMultiGen :
    RealizesBounded .exact compPopBackMultiGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompRemoveLastTailPre (fun _ _ => 0) := by
  realize [realizesBounded_compRemoveLastTailItemGen, realizesBounded_readCompGMGen,
    realizesBounded_compPopBackFinish]
  all_goals (
    rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, hr_pos, hm_cap⟩ := h
    have hr_lt := gmRIdx_lt hb_pos hb
    have hq_lt := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have hr_eq : gmQIdx b + 1 = gmRIdx b := rfl
    obtain ⟨hfr1, _⟩ := compRemoveLastTailItem_effect henv hb_pos hcpl hslot hb hr_pos hm_cap
    have henv1 := (henv.of_mem_eq (s' := (Memory.spec 0).clientState s
      (compRemoveLastTailItemGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b)))
      (by rw [hfr1.frontier_eq])).compMetaEnv)
  · exact ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, hr_pos, hm_cap⟩
  all_goals try {
    change Fits w _
    refine fits_of_le_globalMetaLen_comp hb_pos henv.pos_w henv.le_U henv.lt_pow_U ?_
    unfold gmRIdx gmQIdx at *; omega
  }
  · exact ⟨henv1, by simpa only [cpN_mk, hq_eq, hr_eq] using hr_lt⟩
  · exact ⟨(henv.of_mem_eq (by rw [clientState_readCompGMGenProg, hfr1.frontier_eq])).compMetaEnv,
      by simpa only [cpN_mk, hq_eq] using hq_lt⟩
  · simp only [hq_eq, hr_eq]
    rw [clientResult_readCompGMGenProg hr_lt, clientState_readCompGMGenProg,
      clientResult_readCompGMGenProg hq_lt, clientState_readCompGMGenProg]
    exact ⟨henv1, fun hr0_eq hq_pos_eq =>
      compDemoteSlabPre_of_removeTail henv hb_pos hcpl hslot hb hr_pos hm_cap hr0_eq hq_pos_eq⟩

private def CompPopBackSinglePre (w : ℕ) : CompParams × ℕ → Memory.State → Prop
  | (cp, metaBase), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      1 ≤ compGmAt metaBase U w N s.mem 0

private theorem realizesBounded_compPopBackSingleGen :
    RealizesBounded .exact compPopBackSingleGenProg
      (WordEncoding.encode (α := CompParams × ℕ)) (WordEncoding.encode (α := Unit))
      CompPopBackSinglePre (fun _ _ => 0) := by
  realize [realizesBounded_readCompGMGen, realizesBounded_writeCompGMGen]
  all_goals (
    rcases d with ⟨cp, metaBase⟩
    dsimp only at *
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hc_pos⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega)
  · exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; exact h0_lt⟩
  · rw [clientResult_readCompGMGenProg h0_lt]; exact hc_pos
  · rw [clientState_readCompGMGenProg]
    exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; exact h0_lt⟩

theorem realizesBounded_compPopBackSlotGen :
    RealizesBounded .exact compPopBackSlotGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompPopBackSlotPre (fun _ _ => 0) := by
  realize [realizesBounded_compPopBackSingleGen, realizesBounded_compPopBackMultiGen]
  all_goals (
    rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hcpl, hslot, hb, hbc, hm_cap⟩ := h)
  · rw [cpBucketBits_mk] at hc
    obtain rfl : b = 0 := Nat.lt_one_iff.mp (by simpa [numBuckets, hc] using hb)
    unfold bCount at hbc; simp only [hc, ↓reduceIte] at hbc
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, henv.meta_le_frontier, hbc⟩
  · rw [cpBucketBits_mk] at hc
    have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hc
    exact ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb,
      pos_gmRIdx_of_pos_bCount hb_pos hslot hb hbc, hm_cap⟩

theorem validProg_compPopBackSlotGen {w : ℕ} {d : (CompParams × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : CompPopBackSlotPre w d s) :
    ValidProg w 0 s (compPopBackSlotGenProg d) := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩
  obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hcpl, hslot, hb, hbc, hm_cap⟩ := h
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  dsimp only [compPopBackSlotGenProg, compPopBackSingleGenProg, compPopBackMultiGenProg,
    compPopBackFinishProg]
  simp only [cpBucketBits_mk]
  refine validProg_ite (fun _ => ?_) (fun hb0 => ?_)
  · refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h0_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    exact validProg_writeCompGMGen ⟨henv.compMetaEnv, h0_lt⟩
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have hr_pos := pos_gmRIdx_of_pos_bCount hb_pos hslot hb hbc
    obtain ⟨hfr1, _⟩ := compRemoveLastTailItem_effect henv hb_pos hcpl hslot hb hr_pos hm_cap
    refine validProg_bind
      (validProg_compRemoveLastTailItemGen
        ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hcpl, hslot, hb, hr_pos, hm_cap⟩)
      ?_
    set s₁ := (Memory.spec 0).clientState s
      (compRemoveLastTailItemGenProg ((mkCompParams U V w N, (metaBase, itemBase)), b))
    have henv1 := henv.of_mem_eq (s' := s₁) (by rw [hfr1.frontier_eq])
    have hq_lt := gmQIdx_lt hb_pos hb
    have hr_lt := gmRIdx_lt hb_pos hb
    have hqr : 4 + (b + b + b) + 1 = gmRIdx b ∧ 4 + (b + b + b) = gmQIdx b := by
      simp only [gmRIdx, gmQIdx]; omega
    rw [hqr.1, hqr.2]
    refine validProg_bind (validProg_readCompGMGen ⟨henv1.compMetaEnv, hr_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hr_lt]
    refine validProg_bind (validProg_readCompGMGen ⟨henv1.compMetaEnv, hq_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hq_lt]
    refine validProg_ite (fun hr0_eq => ?_) (fun _ => validProg_pure ())
    refine validProg_ite (fun hq_pos_eq => ?_) (fun _ => validProg_pure ())
    exact validProg_compDemoteSlabGen
      (compDemoteSlabPre_of_removeTail henv hb_pos hcpl hslot hb hr_pos hm_cap hr0_eq hq_pos_eq)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

end
