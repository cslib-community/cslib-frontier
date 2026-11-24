/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.Frame
-- `import all`: shares private internal helpers within the `TailSlabOps` split.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.DemoteRead
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.WindowHelpers
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabDemote
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# `RealizesBounded` and `ValidProg` Certificates for `compDemoteStepGenProg`

Certifies `realizesBounded_compDemoteStep` and `validProg_compDemoteStep` for a single demotion
step.
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

private theorem realizesBounded_compDemoteReadGM :
    RealizesBounded .exact compDemoteReadGMProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      CompDemoteReadGMPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, k⟩
    try dsimp only at *
    obtain ⟨U, V, N, _m_cap, _itemBase, _s_fix, rfl, henv, hb_pos,
      ⟨hb, hk_lt, _, hslab_fix, _, hqb_fix, htot_fix⟩, hgm_eq⟩ := h
    have hslab : SlabBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmQIdx b'))
        (compGmAt metaBase U w N s.mem 0) :=
      slabBijection_of_gm_eq hgm_eq hslab_fix
    have hqb : 1 ≤ compGmAt metaBase U w N s.mem (gmQIdx b) := by
      rw [hgm_eq]; exact hqb_fix
    have htot : (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N +
        (slabSize N - k) + compGmAt metaBase U w N s.mem 1 ≤ N := by
      rw [hgm_eq]; exact htot_fix
    have hp_del_lt : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) <
        compGmAt metaBase U w N s.mem 0 := hslab.top_lt hb (by omega)
    have hK_pos : 0 < slabSize N := slabSize_pos N
    have hnU : N ≤ U := henv.le_U
    have htop_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
    have htop_eq : 4 + (b + b + b) + 2 = gmSlabTopIdx b := by unfold gmSlabTopIdx; omega
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hfit_meta : Fits w (metaBase + offCompItems U w N) :=
      lt_of_le_of_lt henv.meta_le_frontier hmem.1
    simp only [cpSlabSizeSubOne_mk, cpSlabSize_mk, htop_eq,
      StateTransitionSpec.clientState, runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg htop_lt] at *
    try rw [clientResult_readCompGMGenProg h0_lt] at *)
  all_goals try exact ⟨henv.compMetaEnv, by simp only [cpN_mk]; omega⟩
  all_goals try {
    change Fits w _
    first
      | exact fits_const_of_offCompItems hfit_meta (by omega)
      | { refine fits_of_le_globalMetaLen_comp hb_pos henv.pos_w henv.le_U henv.lt_pow_U ?_
          unfold gmSlabTopIdx at *; omega }
      | { have hmul : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) * slabSize N ≤
              (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N :=
            Nat.mul_le_mul_right _ (by omega)
          exact Fits.of_le henv.lt_pow_U (by omega) }
  }
  all_goals omega

private theorem realizesBounded_compDemoteReadItems :
    RealizesBounded .exact compDemoteReadItemsProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      CompDemoteReadItemsPre (fun _ _ => 0) := by
  have hrq := realizesBounded_readCompQuotGen
  have hrv := realizesBounded_readCompValGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, itemBase⟩, ⟨g_del, g_last⟩⟩
    obtain ⟨m_cap, hitem_env, hg_del, hg_last⟩ := h
    simp only [StateTransitionSpec.clientState, runClient_state_readCompQuotGenProg,
      runClient_state_readCompValGenProg] at *)
  · exact ⟨m_cap, hitem_env, hg_del⟩
  · exact ⟨m_cap, hitem_env, hg_del⟩
  · exact ⟨m_cap, hitem_env, hg_last⟩
  · exact ⟨m_cap, hitem_env, hg_last⟩

private def CompDemoteWinAppendPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (g_last, n_tails)), s =>
    ∃ U V N m_cap itemBase,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      g_last ≤ N ∧
      n_tails < maxTailItems N ∧
      TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) ∧
      compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N

private theorem realizesBounded_compDemoteWinAppend :
    RealizesBounded .exact compDemoteWinAppendProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompDemoteWinAppendPre (fun _ _ => 0) := by
  have hwgl := realizesBounded_winGrowLeftGen
  have happ := realizesBounded_compAppendTailGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨g_last, n_tails⟩⟩
    obtain ⟨U, V, N, m_cap, itemBase, rfl, henv, hb_pos, hb, hg_last_N, hnt_max,
      htail, hr_cap⟩ := h)
  · exact ⟨henv.compMetaEnv, hnt_max, by simp only [cpN_mk]; exact hg_last_N⟩
  · obtain ⟨hf1, _, _, _, hgm1, _, _, _⟩ :=
      winGrowLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap) (b_win := g_last) (n_win := n_tails)
        henv.pos_w henv.meta_le_item hnt_max s
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      by rw [hf1]; exact henv.meta_le_frontier, hb_pos, hb,
      tailBijection_of_gm_eq hgm1 htail, by rw [hgm1]; exact hr_cap⟩

private def CompDemoteSwapItemsPre (w : ℕ) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.State → Prop
  | (((cp, itemBase), (g_del, g_last)), _qv), s =>
    ∃ m_cap, CompItemEnv w cp itemBase m_cap s ∧ g_del < m_cap ∧ g_last < m_cap

private theorem realizesBounded_compDemoteSwapItems :
    RealizesBounded .exact compDemoteSwapItemsProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      CompDemoteSwapItemsPre (fun _ _ => 0) := by
  have hwit := realizesBounded_writeCompItemGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, itemBase⟩, ⟨g_del, g_last⟩⟩, ⟨⟨q_del, v_del⟩, ⟨q_last, v_last⟩⟩⟩
    obtain ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hg_del, hg_last⟩ := h)
  · exact ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hg_del⟩
  · refine ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_⟩, hg_last⟩
    dsimp only [writeCompItemGenProg]
    rw [StateTransitionSpec.clientState_bind, clientState_writeCompValGenProg,
      clientState_writeCompQuotGenProg]
    exact hfr

private theorem realizesBounded_compDemoteFinishStep :
    RealizesBounded .exact compDemoteFinishStepProg
      (WordEncoding.encode
        (α := (((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      CompDemoteFinishStepPre (fun _ _ => 0) := by
  have hwa := realizesBounded_compDemoteWinAppend
  have hsw := realizesBounded_compDemoteSwapItems
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, ⟨⟨g_del, g_last⟩, n_tails⟩⟩, qv⟩
    obtain ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, hg_del, hg_last, hg_last_N, hnt_max,
      htail, hr_cap⟩ := h)
  · exact ⟨U, V, N, m_cap, itemBase, rfl, henv, hb_pos, hb, hg_last_N, hnt_max, htail, hr_cap⟩
  · obtain ⟨hf1, _, _, _, hgm1, _, _, _⟩ :=
      winGrowLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap) (b_win := g_last) (n_win := n_tails)
        henv.pos_w henv.meta_le_item hnt_max s
    obtain ⟨_, hfr2, _⟩ :=
      compAppendTailGMGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U)
        (V := V) (w := w) (N := N) (m_items := m_cap) (b := b)
        henv.pos_w henv.meta_le_item hb_pos hb _
        (tailBijection_of_gm_eq hgm1 htail) (by rw [hgm1]; exact hr_cap)
    refine ⟨m_cap, (henv.of_mem_eq ?_).compItemEnv, hg_del, hg_last⟩
    dsimp only [compDemoteWinAppendProg]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure, hfr2.frontier_eq, hf1]

private theorem realizesBounded_compDemoteStep :
    RealizesBounded .exact compDemoteStepGenProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CompDemoteStepPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_compDemoteReadGM
  have hrit := realizesBounded_compDemoteReadItems
  have hfin := realizesBounded_compDemoteFinishStep
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, k⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hstep, hcpl, hm_cap⟩ := h
    obtain ⟨hst_gm, hres_gm, _⟩ := compDemoteStep_read_spec henv hb_pos hstep hcpl.gm_eq
    rcases hstep with ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, hqb_fix, htot_fix⟩
    have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
    have hK_pos : 0 < slabSize N := slabSize_pos N
    have htail : TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) :=
      tailBijection_of_gm_eq hcpl.gm_eq htail_fix
    have hslab : SlabBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmQIdx b'))
        (compGmAt metaBase U w N s.mem 0) :=
      slabBijection_of_gm_eq hcpl.gm_eq hslab_fix
    have hrb : compGmAt metaBase U w N s.mem (gmRIdx b) = k := by
      rw [hcpl.gm_eq]; exact hrb_fix
    have hqb : 1 ≤ compGmAt metaBase U w N s.mem (gmQIdx b) := by
      rw [hcpl.gm_eq]; exact hqb_fix
    have htot : (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N +
        (slabSize N - k) + compGmAt metaBase U w N s.mem 1 ≤ N := by
      rw [hcpl.gm_eq]; exact htot_fix
    have hp_del_lt := hslab.top_lt hb (by omega)
    have hmul : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) * slabSize N ≤
        (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N := Nat.mul_le_mul_right _ (by omega)
    have hr_cap : compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N := by
      unfold tailCapPerBucket; rw [ite_eq_right hb0, hrb]; omega
    have ht_cap := ntails_lt_maxTailItems_of_r_lt hb hr_cap htail)
  · exact ⟨U, V, N, m_cap, itemBase, s_fix, rfl, henv, hb_pos,
      ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, hqb_fix, htot_fix⟩, hcpl.gm_eq⟩
  · rw [hst_gm, hres_gm]; dsimp only
    exact ⟨m_cap, henv.compItemEnv, by omega, by omega⟩
  · rw [hst_gm, hres_gm]; dsimp only
    set gd := compGmAt metaBase U w N s.mem (gmSlabTopIdx b) * slabSize N + ((slabSize N - 1) - k)
    set gl := (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + ((slabSize N - 1) - k)
    have hrd_st : (Memory.spec 0).clientState s
        (compDemoteReadItemsProg ((mkCompParams U V w N, itemBase), (gd, gl))) = s := by
      unfold StateTransitionSpec.clientState; simp [compDemoteReadItemsProg]
    rw [hrd_st]
    exact ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, by dsimp only [gd]; omega,
      by dsimp only [gl]; omega, by dsimp only [gl]; omega, ht_cap, htail, hr_cap⟩
  · have hK_le := slabSize_le_max_n_one N
    exact fits_of_le_max_N_one henv.pos_w henv.le_U henv.lt_pow_U (by omega)

private theorem validProg_compDemoteReadItems {w : ℕ}
    {d : (CompParams × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompDemoteReadItemsPre w d s) :
    ValidProg w 0 s (compDemoteReadItemsProg d) := by
  rcases d with ⟨⟨cp, itemBase⟩, ⟨g_del, g_last⟩⟩
  obtain ⟨m_cap, hitem, hg_del, hg_last⟩ := h
  dsimp only [compDemoteReadItemsProg]
  refine validProg_bind (validProg_readCompQuotGen ⟨m_cap, hitem, hg_del⟩) ?_
  rw [clientState_readCompQuotGenProg]
  refine validProg_bind (validProg_readCompValGen ⟨m_cap, hitem, hg_del⟩) ?_
  rw [clientState_readCompValGenProg]
  refine validProg_bind (validProg_readCompQuotGen ⟨m_cap, hitem, hg_last⟩) ?_
  rw [clientState_readCompQuotGenProg]
  refine validProg_bind (validProg_readCompValGen ⟨m_cap, hitem, hg_last⟩) ?_
  exact validProg_pure _

private theorem validProg_compDemoteFinishStep {w : ℕ}
    {d : (((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))}
    {s : Memory.State} (h : CompDemoteFinishStepPre w d s) :
    ValidProg w 0 s (compDemoteFinishStepProg d) := by
  rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, ⟨⟨g_del, g_last⟩, n_tails⟩⟩, qv⟩
  obtain ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, hg_del, hg_last, hg_last_N, hnt_max,
    htail, hr_cap⟩ := h
  obtain ⟨hf1, _, _, _, hgm1, _, _, _⟩ :=
    winGrowLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m_cap) (b_win := g_last) (n_win := n_tails)
      henv.pos_w henv.meta_le_item hnt_max s
  obtain ⟨_, hfr2, _⟩ :=
    compAppendTailGMGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m_cap) (b := b)
      henv.pos_w henv.meta_le_item hb_pos hb _
      (tailBijection_of_gm_eq hgm1 htail) (by rw [hgm1]; exact hr_cap)
  have hv_wa : ValidProg w 0 s
      (compDemoteWinAppendProg (((mkCompParams U V w N, metaBase), b), (g_last, n_tails))) := by
    dsimp only [compDemoteWinAppendProg]
    refine validProg_bind_unit
      (validProg_winGrowLeftGen ⟨henv.compMetaEnv, hnt_max,
        by simp only [cpN_mk]; exact hg_last_N⟩) fun s1 hs1 => ?_
    refine validProg_bind
      (validProg_compAppendTailGMGen ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U,
        henv.le_pow_V, rfl, by rw [hs1, hf1]; exact henv.meta_le_frontier, hb_pos, hb,
        by rw [hs1]; exact tailBijection_of_gm_eq hgm1 htail,
        by rw [hs1, hgm1]; exact hr_cap⟩) ?_
    exact validProg_pure ()
  dsimp only [compDemoteFinishStepProg]
  refine validProg_bind_unit hv_wa fun s2 hs2 => ?_
  have hf2 : s2.frontier = s.frontier := by
    rw [hs2]; dsimp only [compDemoteWinAppendProg]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure, hfr2.frontier_eq, hf1]
  have henv2 := henv.of_mem_eq (s' := s2) (by rw [hf2])
  rcases qv with ⟨⟨q_del, v_del⟩, ⟨q_last, v_last⟩⟩
  dsimp only [compDemoteSwapItemsProg]
  refine validProg_bind_unit
    (validProg_writeCompItemGen ⟨m_cap, henv2.compItemEnv, hg_del⟩) fun s3 hs3 => ?_
  have hf3 : s3.frontier = s2.frontier := by
    rw [hs3]; dsimp only [writeCompItemGenProg]
    rw [StateTransitionSpec.clientState_bind, clientState_writeCompValGenProg,
      clientState_writeCompQuotGenProg]
  exact validProg_writeCompItemGen ⟨m_cap, (henv2.of_mem_eq (by rw [hf3])).compItemEnv, hg_last⟩

private theorem validProg_compDemoteStep {w : ℕ}
    {x : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ} {s : Memory.State}
    (h : CompDemoteStepPre w x s) :
    ValidProg w 0 s (compDemoteStepGenProg x) := by
  rcases x with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, k⟩
  obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hstep, hcpl, hm_cap⟩ := h
  obtain ⟨hst_gm, hres_gm, hv_gm⟩ := compDemoteStep_read_spec henv hb_pos hstep hcpl.gm_eq
  rcases hstep with ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, hqb_fix, htot_fix⟩
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hK_pos : 0 < slabSize N := slabSize_pos N
  have htail : TailBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
      (compGmAt metaBase U w N s.mem 1) :=
    tailBijection_of_gm_eq hcpl.gm_eq htail_fix
  have hslab : SlabBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmQIdx b'))
      (compGmAt metaBase U w N s.mem 0) :=
    slabBijection_of_gm_eq hcpl.gm_eq hslab_fix
  have hrb : compGmAt metaBase U w N s.mem (gmRIdx b) = k := by
    rw [hcpl.gm_eq]; exact hrb_fix
  have hqb : 1 ≤ compGmAt metaBase U w N s.mem (gmQIdx b) := by
    rw [hcpl.gm_eq]; exact hqb_fix
  have htot : (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N +
      (slabSize N - k) + compGmAt metaBase U w N s.mem 1 ≤ N := by
    rw [hcpl.gm_eq]; exact htot_fix
  have hp_del_lt := hslab.top_lt hb (by omega)
  have hmul : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) * slabSize N ≤
      (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N := Nat.mul_le_mul_right _ (by omega)
  have hr_cap : compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N := by
    unfold tailCapPerBucket; rw [ite_eq_right hb0, hrb]; omega
  have ht_cap := ntails_lt_maxTailItems_of_r_lt hb hr_cap htail
  set u := (slabSize N - 1) - k
  set g_del := compGmAt metaBase U w N s.mem (gmSlabTopIdx b) * slabSize N + u
  set g_last := (compGmAt metaBase U w N s.mem 0 - 1) * slabSize N + u
  have hg_del_cap : g_del < m_cap := by dsimp only [g_del, u]; omega
  have hg_last_cap : g_last < m_cap := by dsimp only [g_last, u]; omega
  have hg_last_N : g_last ≤ N := by dsimp only [g_last, u]; omega
  dsimp only [compDemoteStepGenProg]
  refine validProg_bind_of_eq hv_gm hres_gm fun s1 hs1 => ?_
  rw [hs1, hst_gm]
  dsimp only
  set qv := (Memory.spec 0).clientResult s
    (compDemoteReadItemsProg ((mkCompParams U V w N, itemBase), (g_del, g_last)))
  have hrd_st : (Memory.spec 0).clientState s
      (compDemoteReadItemsProg ((mkCompParams U V w N, itemBase), (g_del, g_last))) = s := by
    unfold StateTransitionSpec.clientState; simp [compDemoteReadItemsProg]
  refine validProg_bind_of_eq
    (validProg_compDemoteReadItems ⟨m_cap, henv.compItemEnv, hg_del_cap, hg_last_cap⟩)
    (rfl : _ = qv) fun s2 hs2 => ?_
  rw [hs2, hrd_st]
  refine validProg_bind_unit
    (validProg_compDemoteFinishStep ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, hg_del_cap,
      hg_last_cap, hg_last_N, ht_cap, htail, hr_cap⟩)
    fun _ _ => validProg_pure _

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
