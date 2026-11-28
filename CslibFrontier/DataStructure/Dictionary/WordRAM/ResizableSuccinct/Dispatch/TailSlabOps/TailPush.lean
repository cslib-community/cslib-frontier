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
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Compacted Tail Push-Write Subroutine (`compPushBackTailWriteGenProg`)

Implements and certifies `compPushBackTailWriteGenProg`, coupling compacted circular-window growth
and tail-item append to `pushBackTailWriteProg` via `FixedCoupled`.
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
attribute [local simp] prog_runClient_state_pure StateTransitionSpec.clientResult_map
  StateTransitionSpec.fst_snd_runClient_map
attribute [local simp] Realization.memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

private def compPushBackReadWinProg : CompParams × ℕ → Memory.Prog (ℕ × ℕ)
  | (cp, metaBase) => do
    let n_slabs ← readCompGMGenProg ((cp, metaBase), 0)
    let n_tails ← readCompGMGenProg ((cp, metaBase), 1)
    pure (n_slabs * cpSlabSize cp, n_tails)

private def compPushBackGrowGMProg : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | (((cp, metaBase), b), (b_win, n_tails)) => do
    winGrowRightGenProg ((cp, metaBase), (b_win, n_tails))
    let t_new ← compAppendTailGMGenProg ((cp, metaBase), b)
    pure (b_win + t_new)

private def compPushBackWriteReadProg :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((((cp, (metaBase, itemBase)), b), d_new), (q_val, v_val)) => do
    writeCompItemGenProg (((cp, itemBase), d_new), (q_val, v_val))
    let r_idx := 4 + (b + b + b) + 1
    readCompGMGenProg ((cp, metaBase), r_idx)

/-- Grow the circular tail window on the right, append a tail entry for bucket `b`, write
`(q_val, v_val)`, and return `r_b'`. -/
private def compPushBackTailWriteGenProg :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((((cp, (metaBase, itemBase)), b), q_val), v_val) => do
    let wn ← compPushBackReadWinProg (cp, metaBase)
    let d_new ← compPushBackGrowGMProg (((cp, metaBase), b), wn)
    compPushBackWriteReadProg ((((cp, (metaBase, itemBase)), b), d_new), (q_val, v_val))

@[simp] private theorem memoryCost_compPushBackTailWriteGenProg
    (d : (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compPushBackTailWriteGenProg d) s = 42 := by
  rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, q_val⟩, v_val⟩
  simp [compPushBackTailWriteGenProg, compPushBackReadWinProg, compPushBackGrowGMProg,
    compPushBackWriteReadProg, writeCompItemGenProg]

/-- Precondition for `compPushBackTailWriteGenProg`. -/
private def CompPushBackTailWritePre (w : ℕ) :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | ((((cp, (metaBase, itemBase)), b), q_val), v_val), s =>
    ∃ U V N m_cap s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      totalSlots N (compGmAt metaBase U w N s.mem) < N ∧
      totalSlots N (compGmAt metaBase U w N s.mem) + 1 ≤ m_cap ∧
      q_val < 2 ^ quotientBits U N ∧
      v_val < 2 ^ valBits V

private theorem compPushBackTailWrite_effect {metaBase itemBase U V w N m_cap b q_val v_val : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hb_pos : 0 < bucketBits N)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (htot : totalSlots N (compGmAt metaBase U w N s.mem) < N)
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) + 1 ≤ m_cap)
    (hq_lt : q_val < 2 ^ quotientBits U N) (hv_lt : v_val < 2 ^ valBits V) :
    let d := ((((mkCompParams U V w N, (metaBase, itemBase)), b), q_val), v_val)
    let s' := (Memory.spec 0).clientState s (compPushBackTailWriteGenProg d)
    let s_fix' := (Memory.spec 0).clientState s_fix
      (pushBackTailWriteProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, b), q_val), v_val))
    (Memory.spec 0).clientResult s (compPushBackTailWriteGenProg d) =
      compGmAt metaBase U w N s.mem (gmRIdx b) + 1 ∧
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro d s' s_fix'
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  set gm₀ := compGmAt metaBase U w N s.mem
  have hslot_fix : SlotStoreInv N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      s_fix.mem) := slotStoreInv_of_gm_eq hcpl.gm_eq.symm hslot
  have htot_fix : totalSlots N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      s_fix.mem) < N := by rw [← hcpl.gm_eq]; exact htot
  have htot_eq : totalSlots N gm₀ = gm₀ 0 * slabSize N + gm₀ 1 := by
    unfold totalSlots; rw [ite_eq_right hb0]
  have hSN_lt : gm₀ 0 * slabSize N + gm₀ 1 < N := by rw [← htot_eq]; exact htot
  have htail₀ := hslot.multi_tail hb_pos
  have hr_lt : gm₀ (gmRIdx b) < tailCapPerBucket N := (hslot.multi_r_bounds hb_pos b hb).1
  have ht_cap : gm₀ 1 < maxTailItems N := ntails_lt_maxTailItems_of_r_lt hb hr_lt htail₀
  have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
  have hmax_eq : max (maxTailItems N) 1 = maxTailItems N := Nat.max_eq_left hM_pos
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  set b_win := gm₀ 0 * slabSize N
  set n_win := gm₀ 1
  set s₁ := (Memory.spec 0).clientState s
    (winGrowRightGenProg ((mkCompParams U V w N, metaBase), (b_win, n_win)))
  obtain ⟨hf_w1, htd_w1, hdt_w1, hlm_w1, hgm_w1, hq_w1, hv_w1, hout_w1⟩ :=
    winGrowRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := b_win + n_win) (b_win := b_win) (n_win := n_win)
      henv.pos_w henv.meta_le_item ht_cap s
  set s₂ := (Memory.spec 0).clientState s₁
    (compAppendTailGMGenProg ((mkCompParams U V w N, metaBase), b))
  obtain ⟨hres_app, hfr_app, hgm_app⟩ :=
    compAppendTailGMGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := b_win + n_win) (b := b)
      henv.pos_w henv.meta_le_item hb_pos hb s₁ (by rw [hgm_w1]; exact htail₀)
      (by rw [hgm_w1]; exact hr_lt)
  rw [hgm_w1] at hres_app hgm_app
  set d_new := b_win + n_win
  have hd_new_cap : d_new < m_cap := by dsimp only [d_new, b_win, n_win]; omega
  set s₃ := (Memory.spec 0).clientState s₂
    (writeCompQuotGenProg (((mkCompParams U V w N, itemBase), d_new), q_val))
  set s₄ := (Memory.spec 0).clientState s₃
    (writeCompValGenProg (((mkCompParams U V w N, itemBase), d_new), v_val))
  have hs'_eq : s' = s₄ := by
    dsimp only [s', d, compPushBackTailWriteGenProg, compPushBackReadWinProg,
      compPushBackGrowGMProg, compPushBackWriteReadProg, writeCompItemGenProg]
    simp only [bind_assoc, pure_bind, cpSlabSize_mk]
    rw [StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg h0_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientState_bind,
      clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind, hres_app,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      clientState_readCompGMGenProg]
  have hd_new_lt1 : d_new < b_win + n_win + 1 := Nat.lt_succ_self d_new
  obtain ⟨hlm_q, hgm_q, htd_q, hdt_q⟩ := writeCompQuot_meta_frame (metaBase := metaBase)
    (U := U) (V := V) (N := N) (m_items := b_win + n_win + 1) (q := q_val)
    henv.pos_w henv.meta_le_item hd_new_lt1 s₂.mem
  obtain ⟨hlm_v, hgm_v, htd_v, hdt_v⟩ := writeCompVal_meta_frame (metaBase := metaBase)
    (U := U) (V := V) (N := N) (m_items := b_win + n_win + 1) (v := v_val)
    henv.pos_w henv.meta_le_item hd_new_lt1 s₃.mem
  have hs3_mem : s₃.mem = writeCompQuot itemBase U V w N s₂.mem d_new q_val := by
    dsimp only [s₃]; rw [clientState_writeCompQuotGenProg]
  have hs4_mem : s₄.mem = writeCompVal itemBase U V w N s₃.mem d_new v_val := by
    dsimp only [s₄]; rw [clientState_writeCompValGenProg]
  have hgm4 : compGmAt metaBase U w N s₄.mem = gmAppendTail N gm₀ b := by
    rw [hs4_mem, hgm_v, hs3_mem, hgm_q, hgm_app]
  have hpres_gm := gmAppendTail_preserves_nonTail gm₀ hb hr_lt ht_cap
  have hres_eq : (Memory.spec 0).clientResult s (compPushBackTailWriteGenProg d) =
      gm₀ (gmRIdx b) + 1 := by
    dsimp only [d, compPushBackTailWriteGenProg, compPushBackReadWinProg,
      compPushBackGrowGMProg, compPushBackWriteReadProg, writeCompItemGenProg]
    simp only [bind_assoc, pure_bind, cpSlabSize_mk]
    rw [StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg h0_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind, hres_app,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      hr_eq, clientResult_readCompGMGenProg hr_idx_lt, hgm4, hpres_gm.2.2.1]
  have hframe : CompOpFrame metaBase itemBase U V w N m_cap s s' := by
    rw [hs'_eq]
    exact (compOpFrame_tailWindow hf_w1 hout_w1).trans
      ((CompOpFrame.of_gmFrame hfr_app).trans
        ((compOpFrame_writeCompQuot henv.pos_w hd_new_cap s₂).trans
          (compOpFrame_writeCompVal henv.pos_w hd_new_cap s₃)))
  obtain ⟨_, _, _, hl_fix, hgm_fix, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    pushBackTailWriteProg_effect (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos s_fix hslot_fix hb htot_fix hq_lt hv_lt
  have hfix_q_v :
      quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem =
        Function.update (quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
          (N - 1 - n_win) q_val ∧
      valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem =
        Function.update (valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
          (N - 1 - n_win) v_val := by
    obtain ⟨hr_fa, _, _, hq_fa, hv_fa, _, _⟩ :=
      appendTailItemProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos hb s_fix
        (hslot_fix.multi_tail hb_pos) (hslot_fix.multi_r_bounds hb_pos b hb).1
    have hg_lt : N - 1 - n_win < N := by omega
    have hr_fa' : (Memory.spec 0).clientResult s_fix
        (appendTailItemProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)) = n_win := by
      rw [hr_fa]; exact congrFun hcpl.gm_eq.symm 1
    obtain ⟨_, _, hq_fq, hv_fq, _, _⟩ :=
      writeQuotProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg hg_lt hq_lt
        ((Memory.spec 0).clientState s_fix
          (appendTailItemProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)))
    obtain ⟨_, _, hq_fv, hv_fv, _, _⟩ :=
      writeValProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
        (h_space := epochHashSpace U (ghostW w) N) hwg hg_lt hv_lt _
    have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s_fix
            (appendTailItemProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)))
          (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N)
            ((0, N - 1 - n_win), q_val)))
        (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
          ((0, N - 1 - n_win), v_val)) := by
      dsimp only [s_fix', pushBackTailWriteProg, pushBackTailWriteGenProg]
      simp only [appendTailItemGenProg_mk, p_nMaxSubOne_mk, writeQuotGenProg_mk,
        writeValGenProg_mk, readGMGenProg_mk]
      rw [StateTransitionSpec.clientState_bind, hr_fa',
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        clientState_readGMProg]
    rw [hs_fix'_eq, hq_fv, hq_fq, hq_fa, hv_fv, hv_fq, hv_fa]
    exact ⟨rfl, rfl⟩
  have hwin0 : WindowInv (maxTailItems N) b_win n_win
      (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem) := by
    have hw0 := hcpl.win_inv; simp only [hb0, ↓reduceIte] at hw0; exact hw0
  have hwspec := winGrowRight_spec hwin0 (by omega : n_win + 1 ≤ maxTailItems N)
    (fun i => by have := hcpl.td_lt i; rw [hmax_eq] at this; exact this)
    (fun i => by have := hcpl.dt_lt i; rw [hmax_eq] at this; exact this)
  have hp_grow := physByBase_winGrowRight (N := N) (b := b_win) (n := n_win)
    (td := compTDAt metaBase U w N s.mem) (dt := compDTAt metaBase U w N s.mem)
    hb_pos (by omega)
  dsimp only [winGrowRight] at hwspec hp_grow htd_w1 hdt_w1
  set td_new := Function.update (compTDAt metaBase U w N s.mem) n_win
    ((b_win + n_win) % maxTailItems N)
  set dt_new := Function.update (compDTAt metaBase U w N s.mem)
    ((b_win + n_win) % maxTailItems N) n_win
  have htd4' : compTDAt metaBase U w N s₄.mem = td_new := by
    rw [hs4_mem, htd_v, hs3_mem, htd_q, hfr_app.td_eq]; exact htd_w1
  have hdt4' : compDTAt metaBase U w N s₄.mem = dt_new := by
    rw [hs4_mem, hdt_v, hs3_mem, hdt_q, hfr_app.dt_eq]; exact hdt_w1
  have hlm4 : compLmAt metaBase U w N s₄.mem = compLmAt metaBase U w N s.mem := by
    rw [hs4_mem, hlm_v, hs3_mem, hlm_q, hfr_app.lm_eq, hlm_w1]
  refine ⟨hres_eq, hframe, ?_⟩
  rw [hs'_eq]
  unfold FixedCoupled
  have hgm4_0 : compGmAt metaBase U w N s₄.mem 0 = gm₀ 0 := by rw [hgm4, hpres_gm.1]
  have hgm4_1 : compGmAt metaBase U w N s₄.mem 1 = n_win + 1 := by rw [hgm4, hpres_gm.2.1]
  have htot4 : epochTotalSlots N (compGmAt metaBase U w N s₄.mem) = b_win + n_win + 1 := by
    unfold epochTotalSlots; rw [ite_eq_right hb0, hgm4_0, hgm4_1]; dsimp only [b_win]; omega
  refine ⟨hgm4.trans ((congrArg (fun g => gmAppendTail N g b) hcpl.gm_eq).trans hgm_fix.symm),
    hlm4.trans (hcpl.lm_eq.trans hl_fix.symm),
    by simp only [hb0, ↓reduceIte, hgm4_0, hgm4_1, htd4', hdt4']; exact hwspec.1,
    fun i => by rw [htd4', hmax_eq]; exact hwspec.2.1 i,
    fun i => by rw [hdt4', hmax_eq]; exact hwspec.2.2 i,
    fun idx hidx => ?_,
    fun idx hidx => ?_⟩
  · rw [htot4] at hidx ⊢
    rw [hgm4_0, hdt4', hs4_mem, compQuotAt_writeCompVal henv.pos_w, hs3_mem, hfix_q_v.1]
    change compQuotAt itemBase U V w N (b_win + n_win + 1)
        (writeCompQuot itemBase U V w N s₂.mem d_new q_val) idx =
      Function.update (quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
        (N - 1 - n_win) q_val (physByBase N b_win dt_new idx)
    by_cases heq : idx = d_new
    · subst idx
      rw [compQuotAt_writeCompQuot_self s₂.mem hd_new_lt1 hq_lt, hp_grow.1, Function.update_self]
    · have hlt0 : idx < b_win + n_win := by dsimp only [d_new] at heq; omega
      have hne_g : physByBase N b_win (compDTAt metaBase U w N s.mem) idx ≠ N - 1 - n_win := by
        have hrng := (physByBase_range_and_inj hb_pos (by omega : b_win + n_win ≤ N)
          (by omega : n_win ≤ maxTailItems N) hwin0).1 idx hlt0
        rcases hrng with ⟨hlt_b, hp_eq⟩ | ⟨_, hlo, _⟩ <;> omega
      rw [compQuotAt_writeCompQuot_of_ne henv.pos_w s₂.mem heq,
        compQuotAt_of_lt s₂.mem hidx hlt0, congrFun hfr_app.quot_eq idx,
        congrFun hq_w1 idx, hp_grow.2 idx hlt0, Function.update_of_ne hne_g]
      have hq0 := hcpl.quot_eq idx (by unfold epochTotalSlots; rw [ite_eq_right hb0]; exact hlt0)
      unfold epochTotalSlots at hq0; rw [ite_eq_right hb0] at hq0
      exact hq0
  · rw [htot4] at hidx ⊢
    rw [hgm4_0, hdt4', hs4_mem, hs3_mem, hfix_q_v.2]
    change compValAt itemBase U V w N (b_win + n_win + 1)
        (writeCompVal itemBase U V w N (writeCompQuot itemBase U V w N s₂.mem d_new q_val)
          d_new v_val) idx =
      Function.update (valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem)
        (N - 1 - n_win) v_val (physByBase N b_win dt_new idx)
    by_cases heq : idx = d_new
    · subst idx
      rw [compValAt_writeCompVal_self _ hd_new_lt1 hv_lt, hp_grow.1, Function.update_self]
    · have hlt0 : idx < b_win + n_win := by dsimp only [d_new] at heq; omega
      have hne_g : physByBase N b_win (compDTAt metaBase U w N s.mem) idx ≠ N - 1 - n_win := by
        have hrng := (physByBase_range_and_inj hb_pos (by omega : b_win + n_win ≤ N)
          (by omega : n_win ≤ maxTailItems N) hwin0).1 idx hlt0
        rcases hrng with ⟨hlt_b, hp_eq⟩ | ⟨_, hlo, _⟩ <;> omega
      rw [compValAt_writeCompVal_of_ne henv.pos_w _ heq,
        compValAt_writeCompQuot henv.pos_w s₂.mem,
        compValAt_of_lt s₂.mem hidx hlt0, congrFun hfr_app.val_eq idx,
        congrFun hv_w1 idx, hp_grow.2 idx hlt0, Function.update_of_ne hne_g]
      have hv0 := hcpl.val_eq idx (by unfold epochTotalSlots; rw [ite_eq_right hb0]; exact hlt0)
      unfold epochTotalSlots at hv0; rw [ite_eq_right hb0] at hv0
      exact hv0

private def CompPushBackReadWinPre (w : ℕ) : CompParams × ℕ → Memory.State → Prop
  | (cp, metaBase), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      compGmAt metaBase U w N s.mem 0 * slabSize N ≤ N

private theorem realizesBounded_compPushBackReadWin :
    RealizesBounded .exact compPushBackReadWinProg
      (WordEncoding.encode (α := CompParams × ℕ)) (WordEncoding.encode (α := ℕ × ℕ))
      CompPushBackReadWinPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨cp, metaBase⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, _hb_pos, hb_le⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.frontier_fits
    try simp only [cpSlabSize_mk, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg h0_lt] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; omega⟩
  all_goals try exact fits_const_of_offCompItems hfit_meta (by omega)
  exact lt_of_le_of_lt (by omega) hU

private def CompPushBackGrowGMPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (b_win, n_tails)), s =>
    ∃ U V N m_cap itemBase,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      b_win + n_tails ≤ N ∧
      n_tails < maxTailItems N ∧
      b_win + compGmAt metaBase U w N s.mem 1 ≤ N ∧
      TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) ∧
      compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N

private theorem realizesBounded_compPushBackGrowGM :
    RealizesBounded .exact compPushBackGrowGMProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      CompPushBackGrowGMPre (fun _ _ => 0) := by
  have hwgr := realizesBounded_winGrowRightGen
  have happ := realizesBounded_compAppendTailGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨b_win, n_tails⟩⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, itemBase, rfl, henv, hb_pos, hb, hb_N, ht_cap, hbn_N,
      htail, hr_lt⟩ := h)
  · exact ⟨henv.compMetaEnv, ht_cap, by simp only [cpN_mk]; exact hb_N⟩
  · obtain ⟨hf_w1, _, _, _, hgm_w1, _, _, _⟩ :=
      winGrowRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n_tails)
        henv.pos_w henv.meta_le_item ht_cap s
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      by rw [hf_w1]; exact henv.meta_le_frontier, hb_pos, hb,
      tailBijection_of_gm_eq hgm_w1 htail, by rw [hgm_w1]; exact hr_lt⟩
  · obtain ⟨_, _, _, _, hgm_w1, _, _, _⟩ :=
      winGrowRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n_tails)
        henv.pos_w henv.meta_le_item ht_cap s
    obtain ⟨hres_app, _, _⟩ :=
      compAppendTailGMGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U)
        (V := V) (w := w) (N := N) (m_items := m_cap) (b := b)
        henv.pos_w henv.meta_le_item hb_pos hb _
        (tailBijection_of_gm_eq hgm_w1 htail) (by rw [hgm_w1]; exact hr_lt)
    rw [hres_app, hgm_w1]
    exact lt_of_le_of_lt (by have := henv.le_U; omega) henv.lt_pow_U

private def CompPushBackWriteReadPre (w : ℕ) :
    (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((((cp, (metaBase, itemBase)), b), d_new), _qv), s =>
    ∃ U V N m_cap,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      d_new < m_cap

private theorem realizesBounded_compPushBackWriteRead :
    RealizesBounded .exact compPushBackWriteReadProg
      (WordEncoding.encode (α := (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      CompPushBackWriteReadPre (fun _ _ => 0) := by
  have hwit := realizesBounded_writeCompItemGen
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, d_new⟩, ⟨q_val, v_val⟩⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, hd_cap⟩ := h
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hfit_meta : Fits w (metaBase + offCompItems U w N) :=
      lt_of_le_of_lt henv.meta_le_frontier hmem.frontier_fits)
  · exact ⟨m_cap, henv.compItemEnv, hd_cap⟩
  all_goals try {
    change Fits w _
    refine fits_of_le_globalMetaLen_comp hb_pos henv.pos_w henv.le_U henv.lt_pow_U ?_
    unfold gmRIdx at hr_idx_lt; omega
  }
  · refine ⟨(henv.of_mem_eq ?_).compMetaEnv,
      by simp only [cpN_mk]; unfold gmRIdx at hr_idx_lt; omega⟩
    dsimp only [writeCompItemGenProg]
    rw [StateTransitionSpec.clientState_bind, clientState_writeCompValGenProg,
      clientState_writeCompQuotGenProg]

private theorem realizesBounded_compPushBackTailWriteGen :
    RealizesBounded .exact compPushBackTailWriteGenProg
      (WordEncoding.encode (α := (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CompPushBackTailWritePre (fun _ _ => 0) := by
  have hrw := realizesBounded_compPushBackReadWin
  have hgg := realizesBounded_compPushBackGrowGM
  have hwr := realizesBounded_compPushBackWriteRead
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, q_val⟩, v_val⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, _s_fix, rfl, henv, hb_pos, _hcpl, hslot, hb, htot, hm_cap,
      _hq_lt, _hv_lt⟩ := h
    have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have htail₀ := hslot.multi_tail hb_pos
    have hr_lt : compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N :=
      (hslot.multi_r_bounds hb_pos b hb).1
    have ht_cap : compGmAt metaBase U w N s.mem 1 < maxTailItems N :=
      ntails_lt_maxTailItems_of_r_lt hb hr_lt htail₀
    have htot_eq : totalSlots N (compGmAt metaBase U w N s.mem) =
        compGmAt metaBase U w N s.mem 0 * slabSize N + compGmAt metaBase U w N s.mem 1 := by
      unfold totalSlots; rw [ite_eq_right hb0]
    have hrw_s : (Memory.spec 0).clientState s
        (compPushBackReadWinProg (mkCompParams U V w N, metaBase)) = s := by
      unfold StateTransitionSpec.clientState; simp [compPushBackReadWinProg]
    have hrw_r : (Memory.spec 0).clientResult s
        (compPushBackReadWinProg (mkCompParams U V w N, metaBase)) =
        (compGmAt metaBase U w N s.mem 0 * slabSize N, compGmAt metaBase U w N s.mem 1) := by
      dsimp only [compPushBackReadWinProg, cpSlabSize_mk]
      rw [StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg h0_lt,
        clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg]; rfl)
  · exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      henv.meta_le_frontier, hb_pos, by omega⟩
  · rw [hrw_s, hrw_r]
    exact ⟨U, V, N, m_cap, itemBase, rfl, henv, hb_pos, hb, by omega, ht_cap, by omega,
      htail₀, hr_lt⟩
  · rw [hrw_s, hrw_r]
    obtain ⟨hf_w1, _, _, _, hgm_w1, _, _, _⟩ :=
      winGrowRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap)
        (b_win := compGmAt metaBase U w N s.mem 0 * slabSize N)
        (n_win := compGmAt metaBase U w N s.mem 1)
        henv.pos_w henv.meta_le_item ht_cap s
    obtain ⟨hres_app, hfr_app, _⟩ :=
      compAppendTailGMGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U)
        (V := V) (w := w) (N := N) (m_items := m_cap) (b := b)
        henv.pos_w henv.meta_le_item hb_pos hb _
        (tailBijection_of_gm_eq hgm_w1 htail₀) (by rw [hgm_w1]; exact hr_lt)
    refine ⟨U, V, N, m_cap, rfl, henv.of_mem_eq ?_, hb_pos, hb, ?_⟩
    · dsimp only [compPushBackGrowGMProg]
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_pure, hfr_app.frontier_eq, hf_w1]
    · dsimp only [compPushBackGrowGMProg]
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind, hres_app,
        StateTransitionSpec.clientResult_pure, hgm_w1]
      omega

private theorem validProg_compPushBackTailWriteGen {w : ℕ}
    {d : (((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (h : CompPushBackTailWritePre w d s) :
    ValidProg w 0 s (compPushBackTailWriteGenProg d) := by
  rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, q_val⟩, v_val⟩
  obtain ⟨U, V, N, m_cap, _s_fix, rfl, henv, hb_pos, _hcpl, hslot, hb, htot, hm_cap,
    _hq_lt, _hv_lt⟩ := h
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  have htail₀ := hslot.multi_tail hb_pos
  have hr_lt : compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N :=
    (hslot.multi_r_bounds hb_pos b hb).1
  have ht_cap : compGmAt metaBase U w N s.mem 1 < maxTailItems N :=
    ntails_lt_maxTailItems_of_r_lt hb hr_lt htail₀
  have htot_eq : totalSlots N (compGmAt metaBase U w N s.mem) =
      compGmAt metaBase U w N s.mem 0 * slabSize N + compGmAt metaBase U w N s.mem 1 := by
    unfold totalSlots; rw [ite_eq_right hb0]
  obtain ⟨hf_w1, _, _, _, hgm_w1, _, _, _⟩ :=
    winGrowRightGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m_cap)
      (b_win := compGmAt metaBase U w N s.mem 0 * slabSize N)
      (n_win := compGmAt metaBase U w N s.mem 1)
      henv.pos_w henv.meta_le_item ht_cap s
  obtain ⟨hres_app, hfr_app, _⟩ :=
    compAppendTailGMGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m_cap) (b := b)
      henv.pos_w henv.meta_le_item hb_pos hb _
      (tailBijection_of_gm_eq hgm_w1 htail₀) (by rw [hgm_w1]; exact hr_lt)
  rw [hgm_w1] at hres_app
  have hv_rw : ValidProg w 0 s
      (compPushBackReadWinProg (mkCompParams U V w N, metaBase)) := by
    dsimp only [compPushBackReadWinProg]
    refine validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h0_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    exact validProg_bind (validProg_readCompGMGen ⟨henv.compMetaEnv, h1_lt⟩) (validProg_pure _)
  have hrw_s : (Memory.spec 0).clientState s
      (compPushBackReadWinProg (mkCompParams U V w N, metaBase)) = s := by
    unfold StateTransitionSpec.clientState; simp [compPushBackReadWinProg]
  have hrw_r : (Memory.spec 0).clientResult s
      (compPushBackReadWinProg (mkCompParams U V w N, metaBase)) =
      (compGmAt metaBase U w N s.mem 0 * slabSize N, compGmAt metaBase U w N s.mem 1) := by
    dsimp only [compPushBackReadWinProg, cpSlabSize_mk]
    rw [StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg h0_lt,
      clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
      clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg]; rfl
  dsimp only [compPushBackTailWriteGenProg]
  refine validProg_bind_of_eq hv_rw hrw_r fun s1 hs1 => ?_
  rw [hs1, hrw_s]
  set wn := (compGmAt metaBase U w N s.mem 0 * slabSize N, compGmAt metaBase U w N s.mem 1)
  have hv_gg : ValidProg w 0 s
      (compPushBackGrowGMProg (((mkCompParams U V w N, metaBase), b), wn)) := by
    dsimp only [compPushBackGrowGMProg]
    refine validProg_bind_unit
      (validProg_winGrowRightGen ⟨henv.compMetaEnv,
        by dsimp only [wn]; simp only [cpMaxTail_mk]; exact ht_cap,
        by dsimp only [wn]; simp only [cpN_mk]; omega⟩)
      fun sg1 hsg1 => ?_
    refine validProg_bind
      (validProg_compAppendTailGMGen ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U,
        henv.le_pow_V, rfl, by rw [hsg1, hf_w1]; exact henv.meta_le_frontier, hb_pos, hb,
        by rw [hsg1]; exact tailBijection_of_gm_eq hgm_w1 htail₀,
        by rw [hsg1, hgm_w1]; exact hr_lt⟩) ?_
    exact validProg_pure _
  have hgg_r : (Memory.spec 0).clientResult s
      (compPushBackGrowGMProg (((mkCompParams U V w N, metaBase), b), wn)) =
      compGmAt metaBase U w N s.mem 0 * slabSize N + compGmAt metaBase U w N s.mem 1 := by
    dsimp only [compPushBackGrowGMProg]
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind, hres_app,
      StateTransitionSpec.clientResult_pure]
  refine validProg_bind_of_eq hv_gg hgg_r fun s2 hs2 => ?_
  have hs2_fr : s2.frontier = s.frontier := by
    rw [hs2]; dsimp only [compPushBackGrowGMProg]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure, hfr_app.frontier_eq, hf_w1]
  have henv2 := henv.of_mem_eq (s' := s2) (by rw [hs2_fr])
  dsimp only [compPushBackWriteReadProg]
  rw [hr_eq]
  refine validProg_bind_unit
    (validProg_writeCompItemGen ⟨m_cap, henv2.compItemEnv, by omega⟩)
    fun s3 hs3 => ?_
  have hs3_fr : s3.frontier = s2.frontier := by
    rw [hs3]; dsimp only [writeCompItemGenProg]
    rw [StateTransitionSpec.clientState_bind, clientState_writeCompValGenProg,
      clientState_writeCompQuotGenProg]
  exact validProg_readCompGMGen ⟨(henv2.of_mem_eq (by rw [hs3_fr])).compMetaEnv, hr_idx_lt⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
