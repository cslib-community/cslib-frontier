/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.Frame
-- `import all`: shares private internal helpers within the `TailSlabOps` split.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.PromoteRead
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.WindowHelpers
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabMove
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# `WindowCoupled` Simulation for One Slab-Promotion Step (`compPromoteStep_effect`)

Proves `WindowCoupled` and `CompOpFrame` preservation for a single step `compPromoteStepGenProg`
against `promoteStepProg`.
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

private theorem compPromoteStep_effect {metaBase itemBase U V w N m_cap b k : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hb_pos : 0 < bucketBits N)
    (hstep : PromoteStepInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b k s_fix)
    (hcpl : WindowCoupled metaBase itemBase U V w N
      (compGmAt metaBase U w N s.mem 0 * slabSize N + k)
      (compGmAt metaBase U w N s.mem 1)
      ((compGmAt metaBase U w N s.mem 0 * slabSize N + k) + compGmAt metaBase U w N s.mem 1)
      s_fix s)
    (hm_cap : (compGmAt metaBase U w N s.mem 0 * slabSize N + k) +
      compGmAt metaBase U w N s.mem 1 ≤ m_cap) :
    let d := (((mkCompParams U V w N, (metaBase, itemBase)), b), k)
    let s' := (Memory.spec 0).clientState s (compPromoteStepGenProg d)
    let s_fix' := (Memory.spec 0).clientState s_fix
      (promoteStepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, b), k))
    (Memory.spec 0).clientResult s (compPromoteStepGenProg d) = k + 1 ∧
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    WindowCoupled metaBase itemBase U V w N
      (compGmAt metaBase U w N s'.mem 0 * slabSize N + (k + 1))
      (compGmAt metaBase U w N s'.mem 1)
      ((compGmAt metaBase U w N s'.mem 0 * slabSize N + (k + 1)) +
        compGmAt metaBase U w N s'.mem 1)
      s_fix' s' ∧
    (compGmAt metaBase U w N s'.mem 0 * slabSize N + (k + 1)) +
      compGmAt metaBase U w N s'.mem 1 ≤ m_cap := by
  intro d s' s_fix'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  have hK_pos : 0 < slabSize N := slabSize_pos N
  have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
  have hmax_eq : max (maxTailItems N) 1 = maxTailItems N := Nat.max_eq_left hM_pos
  obtain ⟨hst_gm, hres_gm, hst_ds, hres_ds, _⟩ :=
    compPromoteStep_read_spec henv hb_pos hstep hcpl
  rcases hstep with ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, htot_fix⟩
  set gm := compGmAt metaBase U w N s.mem
  set td := compTDAt metaBase U w N s.mem
  set u := (slabSize N - 1) - k
  set r_top := slabSize N + u
  set b_win := gm 0 * slabSize N + k
  set n' := gm 1 - 1
  set t_u := gm (gmTailPtrIdx N b u)
  set t_top := gm (gmTailPtrIdx N b r_top)
  set d_u := denseOfCirc (maxTailItems N) b_win (td t_u)
  set d_top := denseOfCirc (maxTailItems N) b_win (td t_top)
  set d_last := denseOfCirc (maxTailItems N) b_win (td n')
  have hgm_fix_eq : gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem = gm :=
    hcpl.gm_eq.symm
  have htail : TailBijection N gm (fun b' => gm (gmRIdx b')) (gm 1) :=
    tailBijection_of_gm_eq hcpl.gm_eq htail_fix
  have hrb : gm (gmRIdx b) = 2 * slabSize N - k := by simpa only [gm, hcpl.gm_eq] using hrb_fix
  have htot_N : b_win + gm 1 ≤ N := by simpa only [b_win, gm, hcpl.gm_eq] using htot_fix
  have hr_le_nt : gm (gmRIdx b) ≤ gm 1 := r_le_ntails_of_tailBijection htail hb
  have hn1_eq : n' + 1 = gm 1 := by dsimp only [n']; omega
  have hr_top_eq : r_top = gm (gmRIdx b) - 1 := by dsimp only [r_top, u]; omega
  have htu_lt : t_u < n' + 1 := by rw [hn1_eq]; exact htail.ptr_lt b hb u (by dsimp only [u]; omega)
  have httop_lt : t_top < n' + 1 := by
    rw [hn1_eq]; exact htail.ptr_lt b hb r_top (by dsimp only [r_top, u]; omega)
  have hM_le : n' + 1 ≤ maxTailItems N := by rw [hn1_eq]; exact htail.ntails_le
  have hcpl0 : WindowCoupled metaBase itemBase U V w N b_win (n' + 1) (b_win + (n' + 1))
      s_fix s := by simpa only [hn1_eq] using hcpl
  have hp_u := physByBase_tail_denseOfCirc hb_pos hcpl0.win_inv htu_lt
  have hp_top := physByBase_tail_denseOfCirc hb_pos hcpl0.win_inv httop_lt
  have hp_last := physByBase_tail_denseOfCirc hb_pos hcpl0.win_inv (Nat.lt_succ_self n')
  set qA := quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
  set vA := valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
  set g_u := N - 1 - t_u
  set g_top := N - 1 - t_top
  set g_last := N - 1 - n'
  have hqu_eq : compQuotAt itemBase U V w N (b_win + (n' + 1)) s.mem d_u = qA g_u := by
    rw [hcpl0.quot_eq d_u hp_u.2.1, hp_u.2.2]
  have hvu_eq : compValAt itemBase U V w N (b_win + (n' + 1)) s.mem d_u = vA g_u := by
    rw [hcpl0.val_eq d_u hp_u.2.1, hp_u.2.2]
  have hdu_cap : d_u < m_cap := lt_of_lt_of_le hp_u.2.1 (by rw [hn1_eq]; exact hm_cap)
  have hdtop_cap : d_top < m_cap := lt_of_lt_of_le hp_top.2.1 (by rw [hn1_eq]; exact hm_cap)
  have hdlast_cap : d_last < m_cap := lt_of_lt_of_le hp_last.2.1 (by rw [hn1_eq]; exact hm_cap)
  have hbwin_cap : b_win < m_cap := by omega
  set s₁ := (Memory.spec 0).clientState s
    (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_top, d_u)))
  set s₂ := (Memory.spec 0).clientState s₁
    (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_last, d_top)))
  set s₃ := (Memory.spec 0).clientState s₂
    (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (b_win, d_last)))
  have hmv_res : (Memory.spec 0).clientResult s
      (compPromoteMoveItemsProg (((mkCompParams U V w N, itemBase), b_win),
        (d_u, (d_top, d_last)))) = (qA g_u, vA g_u) := by
    dsimp only [compPromoteMoveItemsProg]
    repeat rw [StateTransitionSpec.clientResult_bind]
    rw [clientResult_readCompQuotGenProg hp_u.2.1, clientState_readCompQuotGenProg,
      clientResult_readCompValGenProg hp_u.2.1, clientState_readCompValGenProg,
      StateTransitionSpec.clientResult_pure, hqu_eq, hvu_eq]
  have hmv_st : (Memory.spec 0).clientState s
      (compPromoteMoveItemsProg (((mkCompParams U V w N, itemBase), b_win),
        (d_u, (d_top, d_last)))) = s₃ := by
    dsimp only [compPromoteMoveItemsProg]
    repeat rw [StateTransitionSpec.clientState_bind]
    rw [clientState_readCompQuotGenProg, clientState_readCompValGenProg,
      StateTransitionSpec.clientState_pure]
  set s₄ := (Memory.spec 0).clientState s₃
    (winShrinkLeftGenProg ((mkCompParams U V w N, metaBase), (b_win, n')))
  set s₅ := (Memory.spec 0).clientState s₄
    (writeCompQuotGenProg (((mkCompParams U V w N, itemBase), b_win), qA g_u))
  set s₆ := (Memory.spec 0).clientState s₅
    (writeCompValGenProg (((mkCompParams U V w N, itemBase), b_win), vA g_u))
  set s₇ := (Memory.spec 0).clientState s₆
    (compRemoveTailGMOnlyGenProg ((mkCompParams U V w N, metaBase), b))
  have hres_all : (Memory.spec 0).clientResult s (compPromoteStepGenProg d) = k + 1 := by
    simp only [d, compPromoteStepGenProg, compPromoteFinishStepProg,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure,
      hst_gm, hres_gm, hst_ds, hres_ds]
  have hst_all : s' = s₇ := by
    simp [s', d, compPromoteStepGenProg, compPromoteFinishStepProg,
      hst_gm, hres_gm, hst_ds, hres_ds, hmv_st, hmv_res, s₇, s₆, s₅, s₄]
  have hgu_lt : g_u < N := by dsimp only [g_u]; omega
  have hgtop_lt : g_top < N := by dsimp only [g_top]; omega
  have hbwin_lt_N : b_win < N := by omega
  set sf₁ := (Memory.spec 0).clientState
    ((Memory.spec 0).clientState s_fix
      (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, g_u), qA g_top)))
    (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, g_u), vA g_top))
  obtain ⟨_, _, hq_f1a, hv_f1a, hl_f1a, hg_f1a⟩ :=
    writeQuotProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hgu_lt (quotAt_lt _ _ _ _ _ _ _) s_fix
  obtain ⟨_, _, hq_f1b, hv_f1b, hl_f1b, hg_f1b⟩ :=
    writeValProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hgu_lt (valAt_lt _ _ _ _ _ _ _ _) _
  have hcpl1 : WindowCoupled metaBase itemBase U V w N b_win (n' + 1) (b_win + (n' + 1))
      sf₁ s₁ :=
    windowCoupled_copyCompItem henv.pos_w henv.meta_le_item hb_pos (by rw [hn1_eq]; exact htot_N)
      hM_le hcpl0 hp_top.2.1 hp_u.2.1 hp_top.2.2 hp_u.2.2
      (hg_f1b.trans hg_f1a) (hl_f1b.trans hl_f1a) (hq_f1b.trans hq_f1a)
      (hv_f1b.trans (congrArg (fun f => Function.update f _ _) hv_f1a))
  set qA₁ := quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) sf₁.mem
  set vA₁ := valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) sf₁.mem
  set sf₂ := (Memory.spec 0).clientState
    ((Memory.spec 0).clientState sf₁
      (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, g_top), qA₁ g_last)))
    (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, g_top), vA₁ g_last))
  obtain ⟨_, _, hq_f2a, hv_f2a, hl_f2a, hg_f2a⟩ :=
    writeQuotProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hgtop_lt (quotAt_lt _ _ _ _ _ _ _) sf₁
  obtain ⟨_, _, hq_f2b, hv_f2b, hl_f2b, hg_f2b⟩ :=
    writeValProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hgtop_lt (valAt_lt _ _ _ _ _ _ _ _) _
  have hcopy_meta {m_it src dst : ℕ} (hsrc : src < m_it) (hdst : dst < m_it) (st : Memory.State) :
      let st' := (Memory.spec 0).clientState st
        (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (src, dst)))
      compTDAt metaBase U w N st'.mem = compTDAt metaBase U w N st.mem ∧
        compDTAt metaBase U w N st'.mem = compDTAt metaBase U w N st.mem := by
    dsimp only
    rw [clientState_copyCompItemGenProg hsrc]
    exact ⟨(writeCompVal_meta_frame henv.pos_w henv.meta_le_item hdst _).2.2.1.trans
        (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item hdst st.mem).2.2.1,
      (writeCompVal_meta_frame henv.pos_w henv.meta_le_item hdst _).2.2.2.trans
        (writeCompQuot_meta_frame henv.pos_w henv.meta_le_item hdst st.mem).2.2.2⟩
  obtain ⟨htd1_eq, hdt1_eq⟩ := hcopy_meta hp_top.2.1 hp_u.2.1 s
  have hcpl2 : WindowCoupled metaBase itemBase U V w N b_win (n' + 1) (b_win + (n' + 1))
      sf₂ s₂ :=
    windowCoupled_copyCompItem henv.pos_w henv.meta_le_item hb_pos (by rw [hn1_eq]; exact htot_N)
      hM_le hcpl1 hp_last.2.1 hp_top.2.1
      (by rw [hdt1_eq]; exact hp_last.2.2) (by rw [hdt1_eq]; exact hp_top.2.2)
      (hg_f2b.trans hg_f2a) (hl_f2b.trans hl_f2a) (hq_f2b.trans hq_f2a)
      (hv_f2b.trans (congrArg (fun f => Function.update f _ _) hv_f2a))
  set sf₃ := (Memory.spec 0).clientState
    ((Memory.spec 0).clientState sf₂
      (writeQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, b_win), qA g_u)))
    (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, b_win), vA g_u))
  obtain ⟨_, _, hq_f3a, hv_f3a, hl_f3a, hg_f3a⟩ :=
    writeQuotProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hbwin_lt_N (quotAt_lt _ _ _ _ _ _ _) sf₂
  obtain ⟨_, _, hq_f3b, hv_f3b, hl_f3b, hg_f3b⟩ :=
    writeValProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hbwin_lt_N (valAt_lt _ _ _ _ _ _ _ _) _
  obtain ⟨htd2_step, hdt2_step⟩ := hcopy_meta hp_last.2.1 hp_top.2.1 s₁
  have htd2_eq : compTDAt metaBase U w N s₂.mem = td := htd2_step.trans htd1_eq
  have hcpl6 : WindowCoupled metaBase itemBase U V w N (b_win + 1) n' ((b_win + 1) + n')
      sf₃ s₆ := by
    have h := windowCoupled_shrinkLeft_write henv.pos_w henv.meta_le_item hb_pos
      (by rw [hn1_eq]; exact htot_N) hM_le hcpl2
      (quotAt_lt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem g_u)
      (valAt_lt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem g_u)
      (hg_f3b.trans hg_f3a) (hl_f3b.trans hl_f3a) (hq_f3b.trans hq_f3a)
      (hv_f3b.trans (congrArg (fun f => Function.update f _ _) hv_f3a))
    dsimp only [s₆, s₅] at h ⊢
    rw [clientState_writeCompValGenProg, clientState_writeCompQuotGenProg]
    rwa [htd2_eq] at h
  have hgm6_eq : compGmAt metaBase U w N s₆.mem = gm :=
    hcpl6.gm_eq.trans ((hg_f3b.trans (hg_f3a.trans (hg_f2b.trans (hg_f2a.trans
      (hg_f1b.trans hg_f1a))))).trans hgm_fix_eq)
  obtain ⟨hfr7, hgm7⟩ := compRemoveTailGMOnlyGenProg_effect (metaBase := metaBase)
    (itemBase := itemBase) (U := U) (V := V) (w := w) (N := N) (m_items := (b_win + 1) + n')
    (b := b) henv.pos_w henv.meta_le_item hb_pos hb s₆
    (tailBijection_of_gm_eq hgm6_eq htail) (by rw [hgm6_eq]; omega)
  rw [hgm6_eq] at hgm7
  obtain ⟨htd3_step, hdt3_step⟩ :=
    hcopy_meta (Nat.lt_add_of_pos_right (Nat.succ_pos n')) hp_last.2.1 s₂
  have hdt3_eq : compDTAt metaBase U w N s₃.mem = compDTAt metaBase U w N s.mem :=
    hdt3_step.trans (hdt2_step.trans hdt1_eq)
  have htd3_eq : compTDAt metaBase U w N s₃.mem = td := htd3_step.trans htd2_eq
  obtain ⟨hf_w4, _, _, _, _, _, _, hout_w4⟩ :=
    winShrinkLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n')
      henv.pos_w henv.meta_le_item (by omega) s₃
      (by rw [hdt3_eq, ← hmax_eq]; exact hcpl.dt_lt _)
      (by rw [htd3_eq, ← hmax_eq]; exact hcpl.td_lt _)
  have hframe : CompOpFrame metaBase itemBase U V w N m_cap s s' := by
    rw [hst_all]
    exact (compOpFrame_copyCompItem henv.pos_w hdtop_cap hdu_cap s).trans <|
      (compOpFrame_copyCompItem henv.pos_w hdlast_cap hdtop_cap s₁).trans <|
      (compOpFrame_copyCompItem henv.pos_w hbwin_cap hdlast_cap s₂).trans <|
      (compOpFrame_tailWindow hf_w4 hout_w4).trans <|
      (compOpFrame_writeCompQuot henv.pos_w hbwin_cap s₄).trans <|
      (compOpFrame_writeCompVal henv.pos_w hbwin_cap s₅).trans <|
      CompOpFrame.of_gmFrame hfr7
  obtain ⟨_, _, _, hq_ps, hv_ps, hl_ps, hgm_ps⟩ :=
    promoteStepProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hb_pos s_fix
      ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, htot_fix⟩
  have hpres := gmRemoveTail_preserves_nonTail hb (by omega : 1 ≤ gm (gmRIdx b)) htail
  have hgm7_0 : compGmAt metaBase U w N s₇.mem 0 = gm 0 := by rw [hgm7, hpres.1]
  have hgm7_1 : compGmAt metaBase U w N s₇.mem 1 = n' := by rw [hgm7, hpres.2.1]
  have hbwin1_eq : compGmAt metaBase U w N s₇.mem 0 * slabSize N + (k + 1) = b_win + 1 := by
    rw [hgm7_0]; dsimp only [b_win]; omega
  have hq_sf3_eq : quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) sf₃.mem =
      quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem := by
    dsimp only [sf₃, sf₂, qA₁] at hq_f1b hq_f2a ⊢
    rw [hq_f3b, hq_f3a, hq_ps, hgm_fix_eq, ← hr_top_eq, hq_f2b, hq_f2a, hq_f1b, hq_f1a]
  have hv_sf3_eq : valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) sf₃.mem =
      valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem := by
    dsimp only [sf₃, sf₂, vA₁] at hv_f1b hv_f2a ⊢
    rw [hv_f3b, hv_f3a, hv_ps, hgm_fix_eq, ← hr_top_eq, hv_f2b, hv_f2a, hv_f1b, hv_f1a]
  have hl_sf3_eq : lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) sf₃.mem =
      lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem := by
    rw [hl_f3b, hl_f3a, hl_f2b, hl_f2a, hl_f1b, hl_f1a, hl_ps]
  refine ⟨hres_all, hframe, ?_, ?_⟩
  · rw [hst_all, hbwin1_eq, hgm7_1]
    refine ⟨hgm7.trans (hgm_fix_eq ▸ hgm_ps.symm),
      hfr7.lm_eq.trans (hcpl6.lm_eq.trans hl_sf3_eq),
      hfr7.td_eq.symm ▸ hfr7.dt_eq.symm ▸ hcpl6.win_inv,
      fun i => hfr7.td_eq.symm ▸ hcpl6.td_lt i,
      fun i => hfr7.dt_eq.symm ▸ hcpl6.dt_lt i,
      fun idx hidx => by
        rw [congrFun hfr7.quot_eq idx, hfr7.dt_eq, hcpl6.quot_eq idx hidx, hq_sf3_eq],
      fun idx hidx => by
        rw [congrFun hfr7.val_eq idx, hfr7.dt_eq, hcpl6.val_eq idx hidx, hv_sf3_eq]⟩
  · simp only [hst_all, hbwin1_eq, hgm7_1]; omega

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
