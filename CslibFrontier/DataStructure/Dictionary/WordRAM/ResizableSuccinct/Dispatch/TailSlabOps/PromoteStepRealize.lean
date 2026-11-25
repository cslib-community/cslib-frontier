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
# `RealizesBounded` and `ValidProg` Certificates for `compPromoteStepGenProg`

Certifies `realizesBounded_compPromoteStep` and `validProg_compPromoteStep` for a single promotion
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
attribute [local simp] prog_runClient_state_pure StateTransitionSpec.clientResult_map
  StateTransitionSpec.fst_snd_runClient_map
attribute [local simp] Realization.memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

private def CompPromoteReadGMPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), b), k), s =>
    ∃ U V N m_cap itemBase s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      0 < bucketBits N ∧
      PromoteStepInv U V (ghostW w) N (epochHashSpace U (ghostW w) N) 0 b k s_fix ∧
      compGmAt metaBase U w N s.mem =
        gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem

private theorem copyCompItem_meta_frame {metaBase itemBase U V w N m_cap src dst : ℕ}
    (hw : 0 < w) (h_order : metaBase + offCompItems U w N ≤ itemBase)
    (hsrc : src < m_cap) (hdst : dst < m_cap) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s
      (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (src, dst)))
    s'.frontier = s.frontier ∧
    compLmAt metaBase U w N s'.mem = compLmAt metaBase U w N s.mem ∧
    compGmAt metaBase U w N s'.mem = compGmAt metaBase U w N s.mem ∧
    compTDAt metaBase U w N s'.mem = compTDAt metaBase U w N s.mem ∧
    compDTAt metaBase U w N s'.mem = compDTAt metaBase U w N s.mem := by
  intro s'
  have hs' := clientState_copyCompItemGenProg (U := U) (V := V) (w := w) (N := N)
    (m_items := m_cap) (itemBase := itemBase) (dst := dst) hsrc s
  obtain ⟨hlm1, hgm1, htd1, hdt1⟩ := writeCompQuot_meta_frame (metaBase := metaBase)
    (U := U) (V := V) (N := N) (q := compQuotAt itemBase U V w N m_cap s.mem src)
    hw h_order hdst s.mem
  obtain ⟨hlm2, hgm2, htd2, hdt2⟩ := writeCompVal_meta_frame (metaBase := metaBase)
    (U := U) (V := V) (N := N) (v := compValAt itemBase U V w N m_cap s.mem src)
    hw h_order hdst
    (writeCompQuot itemBase U V w N s.mem dst (compQuotAt itemBase U V w N m_cap s.mem src))
  dsimp only [s']
  rw [hs']
  exact ⟨rfl, hlm2.trans hlm1, hgm2.trans hgm1, htd2.trans htd1, hdt2.trans hdt1⟩

private theorem realizesBounded_compPromoteReadPtrs :
    RealizesBounded .exact compPromoteReadPtrsProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompPromoteReadGMPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, k⟩
    dsimp only at *
    obtain ⟨U, V, N, _m_cap, _itemBase, _s_fix, rfl, henv, hb_pos,
      ⟨hb, hk_lt, _, _, _, _⟩, _hgm_eq⟩ := h
    have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
    have hK_pos : 0 < slabSize N := slabSize_pos N
    have hTcap : tailCapPerBucket N = 2 * slabSize N := by
      unfold tailCapPerBucket; rw [ite_eq_right hb0]
    have hu_cap : (slabSize N - 1) - k < tailCapPerBucket N := by omega
    have hr_top_cap : slabSize N + ((slabSize N - 1) - k) < tailCapPerBucket N := by omega
    have hptr_u_lt : gmTailPtrBase N + (b * tailCapPerBucket N + ((slabSize N - 1) - k)) <
        globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hu_cap
    have hptr_top_lt : gmTailPtrBase N +
        (b * tailCapPerBucket N + (slabSize N + ((slabSize N - 1) - k))) <
        globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_top_cap
    simp only [cpSlabSizeSubOne_mk, cpSlabSize_mk, cpGmTailPtrBase_mk, cpTailCap_mk,
      StateTransitionSpec.clientState, runClient_state_readCompGMGenProg] at *)
  all_goals try exact ⟨henv.compMetaEnv, by simp only [cpN_mk]; omega⟩
  all_goals try {
    change Fits w _
    exact fits_of_le_globalMetaLen_comp hb_pos henv.pos_w henv.le_U henv.lt_pow_U (by omega)
  }
  omega

private def CompPromoteReadCountsPre (w : ℕ) :
    (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), k), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      compGmAt metaBase U w N s.mem 0 * slabSize N + k ≤ N ∧
      1 ≤ compGmAt metaBase U w N s.mem 1

private theorem realizesBounded_compPromoteReadCounts :
    RealizesBounded .exact compPromoteReadCountsProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompPromoteReadCountsPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, k⟩
    try dsimp only at *
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, htot, hnt_pos⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    try simp only [cpSlabSize_mk, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg h0_lt] at *
    try rw [clientResult_readCompGMGenProg h1_lt] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; omega⟩
  all_goals try {
    change Fits w _
    first
      | exact fits_const_of_offCompItems hfit_meta (by omega)
      | exact Fits.of_le hU (by omega)
  }
  omega

private theorem realizesBounded_compPromoteReadGM :
    RealizesBounded .exact compPromoteReadGMProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      CompPromoteReadGMPre (fun _ _ => 0) := by
  have hpt := realizesBounded_compPromoteReadPtrs
  have hct := realizesBounded_compPromoteReadCounts
  realize
  · exact h
  · rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, k⟩
    dsimp only at *
    obtain ⟨U, V, N, _m_cap, _itemBase, _s_fix, rfl, henv, hb_pos,
      ⟨hb, hk_lt, htail_fix, _, hrb_fix, htot_fix⟩, hgm_eq⟩ := h
    have hK_pos : 0 < slabSize N := slabSize_pos N
    have htail : TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) :=
      tailBijection_of_gm_eq hgm_eq htail_fix
    have hrb : compGmAt metaBase U w N s.mem (gmRIdx b) = 2 * slabSize N - k :=
      (congrFun hgm_eq (gmRIdx b)).trans hrb_fix
    have hr_le_nt := r_le_ntails_of_tailBijection htail hb
    have htot : compGmAt metaBase U w N s.mem 0 * slabSize N + k +
        compGmAt metaBase U w N s.mem 1 ≤ N := by
      rw [hgm_eq]; exact htot_fix
    have hst_pt : (Memory.spec 0).clientState s
        (compPromoteReadPtrsProg (((mkCompParams U V w N, metaBase), b), k)) = s := by
      unfold StateTransitionSpec.clientState; simp [compPromoteReadPtrsProg]
    rw [hst_pt]
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      henv.meta_le_frontier, by omega, by omega⟩

private def CompPromoteReadTDPre (w : ℕ) :
    (CompParams × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | ((cp, metaBase), (n', (t_u, t_top))), s =>
    CompMetaEnv w cp metaBase s ∧ t_u < cpMaxTail cp ∧ t_top < cpMaxTail cp ∧ n' < cpMaxTail cp

private theorem realizesBounded_compPromoteReadTD :
    RealizesBounded .exact compPromoteReadTDProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      CompPromoteReadTDPre (fun _ _ => 0) := by
  have hrtd := realizesBounded_readCompTDGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, ⟨n', ⟨t_u, t_top⟩⟩⟩
    dsimp only at *
    obtain ⟨hmeta, htu, httop, hn'⟩ := h
    try simp only [StateTransitionSpec.clientState, runClient_state_readCompTDGenProg] at *)
  · exact ⟨hmeta, htu⟩
  · exact ⟨hmeta, httop⟩
  · exact ⟨hmeta, hn'⟩

private def CompPromoteCalcDensePre (w : ℕ) :
    (CompParams × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | ((cp, b_win), (c_u, (c_top, c_last))), _s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      b_win ≤ N ∧
      (0 < maxTailItems N →
        c_u < maxTailItems N ∧ denseOfCirc (maxTailItems N) b_win c_u ≤ N ∧
        c_top < maxTailItems N ∧ denseOfCirc (maxTailItems N) b_win c_top ≤ N ∧
        c_last < maxTailItems N ∧ denseOfCirc (maxTailItems N) b_win c_last ≤ N)

private theorem realizesBounded_compPromoteCalcDense :
    RealizesBounded .exact compPromoteCalcDenseProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      CompPromoteCalcDensePre (fun _ _ => 0) := by
  have hdoc := realizesBounded_denseOfCircGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, b_win⟩, ⟨c_u, ⟨c_top, c_last⟩⟩⟩
    dsimp only at *
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hb_le, hcond⟩ := h)
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hb_le,
      fun hb => ⟨(hcond hb).1, (hcond hb).2.1⟩⟩
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hb_le,
      fun hb => ⟨(hcond hb).2.2.1, (hcond hb).2.2.2.1⟩⟩
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hb_le,
      fun hb => ⟨(hcond hb).2.2.2.2.1, (hcond hb).2.2.2.2.2⟩⟩

private theorem realizesBounded_compPromoteReadDense :
    RealizesBounded .exact compPromoteReadDenseProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      CompPromoteReadDensePre (fun _ _ => 0) := by
  have hrtd := realizesBounded_compPromoteReadTD
  have hdoc := realizesBounded_compPromoteCalcDense
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, ⟨⟨b_win, n'⟩, ⟨t_u, t_top⟩⟩⟩
    dsimp only at *
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hbn_N, htu_lt, httop_lt,
      hM_le, hwin⟩ := h
    have htu_max : t_u < maxTailItems N := lt_of_lt_of_le htu_lt hM_le
    have httop_max : t_top < maxTailItems N := lt_of_lt_of_le httop_lt hM_le
    have hn'_max : n' < maxTailItems N := lt_of_lt_of_le (Nat.lt_succ_self n') hM_le)
  · exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩,
      by simp only [cpMaxTail_mk]; exact htu_max,
      by simp only [cpMaxTail_mk]; exact httop_max,
      by simp only [cpMaxTail_mk]; exact hn'_max⟩
  · have htd_r : (Memory.spec 0).clientResult s
        (compPromoteReadTDProg ((mkCompParams U V w N, metaBase), (n', (t_u, t_top)))) =
        (compTDAt metaBase U w N s.mem t_u,
         (compTDAt metaBase U w N s.mem t_top, compTDAt metaBase U w N s.mem n')) := by
      dsimp only [compPromoteReadTDProg]
      rw [StateTransitionSpec.clientResult_bind, clientResult_readCompTDGenProg htu_max,
        clientState_readCompTDGenProg, StateTransitionSpec.clientResult_bind,
        clientResult_readCompTDGenProg httop_max, clientState_readCompTDGenProg,
        StateTransitionSpec.clientResult_bind, clientResult_readCompTDGenProg hn'_max,
        clientState_readCompTDGenProg]; rfl
    rw [htd_r]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, by omega,
      fun _ => ⟨hwin.td_lt _ htu_lt, le_trans (le_of_lt (hwin.dense_lt _ htu_lt)) hbn_N,
        hwin.td_lt _ httop_lt, le_trans (le_of_lt (hwin.dense_lt _ httop_lt)) hbn_N,
        hwin.td_lt _ (Nat.lt_succ_self n'),
        le_trans (le_of_lt (hwin.dense_lt _ (Nat.lt_succ_self n'))) hbn_N⟩⟩

private theorem realizesBounded_compPromoteMoveItems :
    RealizesBounded .exact compPromoteMoveItemsProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompPromoteMoveItemsPre (fun _ _ => 0) := by
  have hrq := realizesBounded_readCompQuotGen
  have hrv := realizesBounded_readCompValGen
  have hcpy := realizesBounded_copyCompItemGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, itemBase⟩, b_win⟩, ⟨d_u, ⟨d_top, d_last⟩⟩⟩
    dsimp only at *
    obtain ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb_lt, hdu, hdtop, hdlast⟩ := h)
  · exact ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hdu⟩
  · rw [clientState_readCompQuotGenProg]
    exact ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hdu⟩
  · rw [clientState_readCompValGenProg, clientState_readCompQuotGenProg]
    exact ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hdtop, hdu⟩
  · rw [clientState_readCompValGenProg, clientState_readCompQuotGenProg,
      clientState_copyCompItemGenProg hdtop]
    exact ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hdlast, hdtop⟩
  · rw [clientState_readCompValGenProg, clientState_readCompQuotGenProg]
    set s1 := (Memory.spec 0).clientState s
      (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_top, d_u)))
    have hs2 := clientState_copyCompItemGenProg (U := U) (V := V) (w := w) (N := N)
      (m_items := m_cap) (itemBase := itemBase) (dst := d_top) hdlast s1
    have hs1 := clientState_copyCompItemGenProg (U := U) (V := V) (w := w) (N := N)
      (m_items := m_cap) (itemBase := itemBase) (dst := d_u) hdtop s
    exact ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl,
      by rw [hs2]; dsimp only [s1]; rw [hs1]; exact hfr⟩, hb_lt, hdlast⟩

private theorem realizesBounded_compPromoteFinishStep :
    RealizesBounded .exact compPromoteFinishStepProg
      (WordEncoding.encode (α := (((CompParams × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompPromoteFinishStepPre (fun _ _ => 0) := by
  have hwsl := realizesBounded_winShrinkLeftGen
  have hwq := realizesBounded_writeCompQuotGen
  have hwv := realizesBounded_writeCompValGen
  have hrm := realizesBounded_compRemoveTailGMOnlyGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, ⟨b_win, n'⟩⟩, ⟨q_u, v_u⟩⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, hb_N, hb_cap, hn'_max, hdt_lt, htd_lt,
      htail, hr_pos⟩ := h)
  · exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      henv.meta_le_frontier, hn'_max, hb_N, hdt_lt, htd_lt⟩
  · obtain ⟨hf1, _, _, _, _, _, _, _⟩ :=
      winShrinkLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n')
        henv.pos_w henv.meta_le_item hn'_max s hdt_lt htd_lt
    exact ⟨m_cap, (henv.of_mem_eq (by rw [hf1])).compItemEnv, hb_cap⟩
  · obtain ⟨hf1, _, _, _, _, _, _, _⟩ :=
      winShrinkLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n')
        henv.pos_w henv.meta_le_item hn'_max s hdt_lt htd_lt
    exact ⟨m_cap, (henv.of_mem_eq (by rw [clientState_writeCompQuotGenProg, hf1])).compItemEnv,
      hb_cap⟩
  · obtain ⟨hf1, _, _, _, hgm1, _, _, _⟩ :=
      winShrinkLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
        (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n')
        henv.pos_w henv.meta_le_item hn'_max s hdt_lt htd_lt
    set s1 := (Memory.spec 0).clientState s
      (winShrinkLeftGenProg ((mkCompParams U V w N, metaBase), (b_win, n')))
    set s2 := (Memory.spec 0).clientState s1
      (writeCompQuotGenProg (((mkCompParams U V w N, itemBase), b_win), q_u))
    set s3 := (Memory.spec 0).clientState s2
      (writeCompValGenProg (((mkCompParams U V w N, itemBase), b_win), v_u))
    have hs2_eq := clientState_writeCompQuotGenProg U V w N itemBase b_win q_u s1
    have hs3_eq := clientState_writeCompValGenProg U V w N itemBase b_win v_u s2
    have hgm3 : compGmAt metaBase U w N s3.mem = compGmAt metaBase U w N s.mem := by
      dsimp only [s3]; rw [hs3_eq]
      refine (writeCompVal_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
        (m_items := m_cap) (v := v_u) henv.pos_w henv.meta_le_item hb_cap s2.mem).2.1.trans ?_
      dsimp only [s2]; rw [hs2_eq]
      exact (writeCompQuot_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
        (m_items := m_cap) (q := q_u) henv.pos_w henv.meta_le_item hb_cap s1.mem).2.1.trans hgm1
    refine ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      ?_, hb_pos, hb, tailBijection_of_gm_eq hgm3 htail, by rw [hgm3]; exact hr_pos⟩
    dsimp only [s3]; rw [hs3_eq]; dsimp only [s2]; rw [hs2_eq, hf1]
    exact henv.meta_le_frontier

private theorem realizesBounded_compPromoteStep :
    RealizesBounded .exact compPromoteStepGenProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CompPromoteStepPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_compPromoteReadGM
  have hrds := realizesBounded_compPromoteReadDense
  have hmv := realizesBounded_compPromoteMoveItems
  have hfin := realizesBounded_compPromoteFinishStep
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, k⟩
    dsimp only at *
    obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hstep, hcpl, hm_cap⟩ := h
    obtain ⟨hst_gm, hres_gm, hst_ds, hres_ds, _⟩ :=
      compPromoteStep_read_spec henv hb_pos hstep hcpl
    rcases hstep with ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, htot_fix⟩
    have htail : TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) :=
      tailBijection_of_gm_eq hcpl.gm_eq htail_fix
    have hrb : compGmAt metaBase U w N s.mem (gmRIdx b) = 2 * slabSize N - k :=
      (congrFun hcpl.gm_eq (gmRIdx b)).trans hrb_fix
    have htot_N : (compGmAt metaBase U w N s.mem 0 * slabSize N + k) +
        compGmAt metaBase U w N s.mem 1 ≤ N := by
      rw [hcpl.gm_eq]; exact htot_fix
    have hr_le_nt := r_le_ntails_of_tailBijection htail hb
    have hK_pos : 0 < slabSize N := slabSize_pos N
    have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
    have hmax_eq : max (maxTailItems N) 1 = maxTailItems N := Nat.max_eq_left hM_pos
    have hn1_eq : compGmAt metaBase U w N s.mem 1 - 1 + 1 = compGmAt metaBase U w N s.mem 1 := by
      omega
    have htu_lt := htail.ptr_lt b hb ((slabSize N - 1) - k) (by omega)
    have httop_lt := htail.ptr_lt b hb (slabSize N + ((slabSize N - 1) - k)) (by omega))
  · exact ⟨U, V, N, m_cap, itemBase, s_fix, rfl, henv, hb_pos,
      ⟨hb, hk_lt, htail_fix, hslab_fix, hrb_fix, htot_fix⟩, hcpl.gm_eq⟩
  · rw [hst_gm, hres_gm]; dsimp only
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
      henv.meta_le_frontier, hb_pos, by omega, by omega, by omega,
      by rw [hn1_eq]; exact htail.ntails_le, by rw [hn1_eq]; exact hcpl.win_inv⟩
  · rw [hst_gm, hres_gm, hst_ds, hres_ds]; dsimp only
    have hd_u := hcpl.win_inv.dense_lt _ htu_lt
    have hd_top := hcpl.win_inv.dense_lt _ httop_lt
    have hd_last := hcpl.win_inv.dense_lt (compGmAt metaBase U w N s.mem 1 - 1) (by omega)
    exact ⟨m_cap, henv.compItemEnv, by omega, by omega, by omega, by omega⟩
  · rw [hst_gm, hres_gm, hst_ds, hres_ds]; dsimp only
    set b_win := compGmAt metaBase U w N s.mem 0 * slabSize N + k
    set n' := compGmAt metaBase U w N s.mem 1 - 1
    set d_u := denseOfCirc (maxTailItems N) b_win
      (compTDAt metaBase U w N s.mem
        (compGmAt metaBase U w N s.mem (gmTailPtrIdx N b ((slabSize N - 1) - k))))
    set d_top := denseOfCirc (maxTailItems N) b_win
      (compTDAt metaBase U w N s.mem
        (compGmAt metaBase U w N s.mem
          (gmTailPtrIdx N b (slabSize N + ((slabSize N - 1) - k)))))
    set d_last := denseOfCirc (maxTailItems N) b_win (compTDAt metaBase U w N s.mem n')
    have hd_u : d_u < m_cap := lt_of_lt_of_le (hcpl.win_inv.dense_lt _ htu_lt) hm_cap
    have hd_top : d_top < m_cap := lt_of_lt_of_le (hcpl.win_inv.dense_lt _ httop_lt) hm_cap
    have hd_last : d_last < m_cap := lt_of_lt_of_le (hcpl.win_inv.dense_lt n' (by omega)) hm_cap
    have hb_cap : b_win < m_cap := by dsimp only [b_win]; omega
    set sm := (Memory.spec 0).clientState s
      (compPromoteMoveItemsProg (((mkCompParams U V w N, itemBase), b_win),
        (d_u, (d_top, d_last))))
    have hsm_eq : sm = (Memory.spec 0).clientState
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s
            (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_top, d_u))))
          (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_last, d_top))))
        (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (b_win, d_last))) := by
      dsimp only [sm, compPromoteMoveItemsProg]
      rw [StateTransitionSpec.clientState_bind, clientState_readCompQuotGenProg,
        StateTransitionSpec.clientState_bind, clientState_readCompValGenProg,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    have fc1 := copyCompItem_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
      henv.pos_w henv.meta_le_item hd_top hd_u s
    have fc2 := copyCompItem_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
      henv.pos_w henv.meta_le_item hd_last hd_top
      ((Memory.spec 0).clientState s
        (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_top, d_u))))
    have fc3 := copyCompItem_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
      henv.pos_w henv.meta_le_item hb_cap hd_last
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState s
          (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_top, d_u))))
        (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_last, d_top))))
    have hsm_fr : sm.frontier = s.frontier := by rw [hsm_eq]; exact fc3.1.trans (fc2.1.trans fc1.1)
    have hsm_gm : compGmAt metaBase U w N sm.mem = compGmAt metaBase U w N s.mem := by
      rw [hsm_eq]; exact fc3.2.2.1.trans (fc2.2.2.1.trans fc1.2.2.1)
    have hsm_td : compTDAt metaBase U w N sm.mem = compTDAt metaBase U w N s.mem := by
      rw [hsm_eq]; exact fc3.2.2.2.1.trans (fc2.2.2.2.1.trans fc1.2.2.2.1)
    have hsm_dt : compDTAt metaBase U w N sm.mem = compDTAt metaBase U w N s.mem := by
      rw [hsm_eq]; exact fc3.2.2.2.2.trans (fc2.2.2.2.2.trans fc1.2.2.2.2)
    have hn'_max : n' < maxTailItems N := lt_of_lt_of_le (by dsimp only [n']; omega) htail.ntails_le
    exact ⟨U, V, N, m_cap, rfl, henv.of_mem_eq (by rw [hsm_fr]), hb_pos, hb,
      by dsimp only [b_win]; omega, hb_cap, hn'_max,
      by rw [hsm_dt, ← hmax_eq]; exact hcpl.dt_lt _,
      by rw [hsm_td, ← hmax_eq]; exact hcpl.td_lt _,
      tailBijection_of_gm_eq hsm_gm htail, by rw [hsm_gm]; omega⟩
  · have hK_le := slabSize_le_max_n_one N
    exact fits_of_le_max_N_one henv.pos_w henv.le_U henv.lt_pow_U (by omega)

private theorem validProg_compPromoteMoveItems {w : ℕ}
    {d : ((CompParams × ℕ) × ℕ) × (ℕ × (ℕ × ℕ))} {s : Memory.State}
    (h : CompPromoteMoveItemsPre w d s) :
    ValidProg w 0 s (compPromoteMoveItemsProg d) := by
  rcases d with ⟨⟨⟨cp, itemBase⟩, b_win⟩, ⟨d_u, ⟨d_top, d_last⟩⟩⟩
  obtain ⟨m_cap, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hb_cap, hdu, hdtop, hdlast⟩ := h
  have mkIt : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompItemEnv w (mkCompParams U V w N) itemBase m_cap s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  dsimp only [compPromoteMoveItemsProg]
  refine validProg_bind (validProg_readCompQuotGen ⟨m_cap, mkIt s rfl, hdu⟩) ?_
  rw [clientState_readCompQuotGenProg]
  refine validProg_bind (validProg_readCompValGen ⟨m_cap, mkIt s rfl, hdu⟩) ?_
  rw [clientState_readCompValGenProg]
  refine validProg_bind_unit
    (validProg_copyCompItemGen ⟨m_cap, mkIt s rfl, hdtop, hdu⟩) fun s1 hs1 => ?_
  have hf1 : s1.frontier = s.frontier := by
    rw [hs1, clientState_copyCompItemGenProg hdtop]
  refine validProg_bind_unit
    (validProg_copyCompItemGen ⟨m_cap, mkIt s1 hf1, hdlast, hdtop⟩) fun s2 hs2 => ?_
  have hf2 : s2.frontier = s.frontier := by
    rw [hs2, clientState_copyCompItemGenProg hdlast, hf1]
  refine validProg_bind_unit
    (validProg_copyCompItemGen ⟨m_cap, mkIt s2 hf2, hb_cap, hdlast⟩) fun _ _ => ?_
  exact validProg_pure _

private theorem validProg_compPromoteFinishStep {w : ℕ}
    {d : (((CompParams × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompPromoteFinishStepPre w d s) :
    ValidProg w 0 s (compPromoteFinishStepProg d) := by
  rcases d with ⟨⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, ⟨b_win, n'⟩⟩, ⟨q_u, v_u⟩⟩
  obtain ⟨U, V, N, m_cap, rfl, henv, hb_pos, hb, hb_N, hb_cap, hn'_max, hdt_lt, htd_lt,
    htail, hr_pos⟩ := h
  obtain ⟨hf_w, _, _, _, hgm_w, _, _, _⟩ :=
    winShrinkLeftGenProg_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (w := w) (N := N) (m_items := m_cap) (b_win := b_win) (n_win := n')
      henv.pos_w henv.meta_le_item hn'_max s hdt_lt htd_lt
  dsimp only [compPromoteFinishStepProg]
  refine validProg_bind_unit
    (validProg_winShrinkLeftGen ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U,
      henv.le_pow_V, rfl, henv.meta_le_frontier, hn'_max, hb_N, hdt_lt, htd_lt⟩) fun s1 hs1 => ?_
  have hf1 : s1.frontier = s.frontier := (congrArg Memory.State.frontier hs1).trans hf_w
  refine validProg_bind_unit
    (validProg_writeCompQuotGen ⟨m_cap, (henv.of_mem_eq (by rw [hf1])).compItemEnv, hb_cap⟩)
    fun s2 hs2 => ?_
  have hf2 : s2.frontier = s.frontier := by
    rw [hs2, clientState_writeCompQuotGenProg, hf1]
  refine validProg_bind_unit
    (validProg_writeCompValGen ⟨m_cap, (henv.of_mem_eq (by rw [hf2])).compItemEnv, hb_cap⟩)
    fun s3 hs3 => ?_
  have hf3 : s3.frontier = s.frontier := by
    rw [hs3, clientState_writeCompValGenProg, hf2]
  have hgm3 : compGmAt metaBase U w N s3.mem = compGmAt metaBase U w N s.mem := by
    rw [hs3, clientState_writeCompValGenProg]
    refine (writeCompVal_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
      (m_items := m_cap) (v := v_u) henv.pos_w henv.meta_le_item hb_cap s2.mem).2.1.trans ?_
    rw [hs2, clientState_writeCompQuotGenProg]
    refine (writeCompQuot_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
      (m_items := m_cap) (q := q_u) henv.pos_w henv.meta_le_item hb_cap s1.mem).2.1.trans ?_
    rw [hs1]; exact hgm_w
  exact validProg_compRemoveTailGMOnlyGen ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U,
    henv.lt_pow_U, henv.le_pow_V, rfl, by rw [hf3]; exact henv.meta_le_frontier, hb_pos, hb,
    tailBijection_of_gm_eq hgm3 htail, by rw [hgm3]; exact hr_pos⟩

private theorem validProg_compPromoteStep {w : ℕ}
    {x : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ} {s : Memory.State}
    (h : CompPromoteStepPre w x s) :
    ValidProg w 0 s (compPromoteStepGenProg x) := by
  rcases x with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, k⟩
  obtain ⟨U, V, N, m_cap, s_fix, rfl, henv, hb_pos, hstep, hcpl, hm_cap⟩ := h
  obtain ⟨hst_gm, hres_gm, hst_ds, hres_ds, hv_gm, hv_ds⟩ :=
    compPromoteStep_read_spec henv hb_pos hstep hcpl
  rcases hstep with ⟨hb, hk_lt, htail_fix, _, hrb_fix, htot_fix⟩
  have htail : TailBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
      (compGmAt metaBase U w N s.mem 1) :=
    tailBijection_of_gm_eq hcpl.gm_eq htail_fix
  have hrb : compGmAt metaBase U w N s.mem (gmRIdx b) = 2 * slabSize N - k :=
    (congrFun hcpl.gm_eq (gmRIdx b)).trans hrb_fix
  have htot_N : (compGmAt metaBase U w N s.mem 0 * slabSize N + k) +
      compGmAt metaBase U w N s.mem 1 ≤ N := by
    rw [hcpl.gm_eq]; exact htot_fix
  have hr_le_nt := r_le_ntails_of_tailBijection htail hb
  have hK_pos : 0 < slabSize N := slabSize_pos N
  have hM_pos : 0 < maxTailItems N := maxTailItems_pos_of_bucketBits_pos hb_pos
  have hmax_eq : max (maxTailItems N) 1 = maxTailItems N := Nat.max_eq_left hM_pos
  have htu_lt := htail.ptr_lt b hb ((slabSize N - 1) - k) (by omega)
  have httop_lt := htail.ptr_lt b hb (slabSize N + ((slabSize N - 1) - k)) (by omega)
  set b_win := compGmAt metaBase U w N s.mem 0 * slabSize N + k
  set n' := compGmAt metaBase U w N s.mem 1 - 1
  set d_u := denseOfCirc (maxTailItems N) b_win
    (compTDAt metaBase U w N s.mem
      (compGmAt metaBase U w N s.mem (gmTailPtrIdx N b ((slabSize N - 1) - k))))
  set d_top := denseOfCirc (maxTailItems N) b_win
    (compTDAt metaBase U w N s.mem
      (compGmAt metaBase U w N s.mem
        (gmTailPtrIdx N b (slabSize N + ((slabSize N - 1) - k)))))
  set d_last := denseOfCirc (maxTailItems N) b_win (compTDAt metaBase U w N s.mem n')
  have hd_u : d_u < m_cap := lt_of_lt_of_le (hcpl.win_inv.dense_lt _ htu_lt) hm_cap
  have hd_top : d_top < m_cap := lt_of_lt_of_le (hcpl.win_inv.dense_lt _ httop_lt) hm_cap
  have hd_last : d_last < m_cap := lt_of_lt_of_le (hcpl.win_inv.dense_lt n' (by omega)) hm_cap
  have hb_cap : b_win < m_cap := by dsimp only [b_win]; omega
  dsimp only [compPromoteStepGenProg]
  refine validProg_bind_of_eq hv_gm hres_gm fun s1 hs1 => ?_
  rw [hs1, hst_gm]
  refine validProg_bind_of_eq hv_ds hres_ds fun s2 hs2 => ?_
  rw [hs2, hst_ds]
  set qv := (Memory.spec 0).clientResult s
    (compPromoteMoveItemsProg (((mkCompParams U V w N, itemBase), b_win),
      (d_u, (d_top, d_last))))
  refine validProg_bind_of_eq
    (validProg_compPromoteMoveItems ⟨m_cap, henv.compItemEnv, hb_cap, hd_u, hd_top, hd_last⟩)
    (rfl : _ = qv) fun sm hsm => ?_
  have hsm_eq : sm = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState s
          (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_top, d_u))))
        (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_last, d_top))))
      (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (b_win, d_last))) := by
    rw [hsm]; dsimp only [compPromoteMoveItemsProg]
    rw [StateTransitionSpec.clientState_bind, clientState_readCompQuotGenProg,
      StateTransitionSpec.clientState_bind, clientState_readCompValGenProg,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  have fc1 := copyCompItem_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
    henv.pos_w henv.meta_le_item hd_top hd_u s
  have fc2 := copyCompItem_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
    henv.pos_w henv.meta_le_item hd_last hd_top
    ((Memory.spec 0).clientState s
      (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_top, d_u))))
  have fc3 := copyCompItem_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N)
    henv.pos_w henv.meta_le_item hb_cap hd_last
    ((Memory.spec 0).clientState
      ((Memory.spec 0).clientState s
        (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_top, d_u))))
      (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (d_last, d_top))))
  have hsm_fr : sm.frontier = s.frontier := by rw [hsm_eq]; exact fc3.1.trans (fc2.1.trans fc1.1)
  have hsm_gm : compGmAt metaBase U w N sm.mem = compGmAt metaBase U w N s.mem := by
    rw [hsm_eq]; exact fc3.2.2.1.trans (fc2.2.2.1.trans fc1.2.2.1)
  have hsm_td : compTDAt metaBase U w N sm.mem = compTDAt metaBase U w N s.mem := by
    rw [hsm_eq]; exact fc3.2.2.2.1.trans (fc2.2.2.2.1.trans fc1.2.2.2.1)
  have hsm_dt : compDTAt metaBase U w N sm.mem = compDTAt metaBase U w N s.mem := by
    rw [hsm_eq]; exact fc3.2.2.2.2.trans (fc2.2.2.2.2.trans fc1.2.2.2.2)
  have hn'_max : n' < maxTailItems N := lt_of_lt_of_le (by dsimp only [n']; omega) htail.ntails_le
  refine validProg_bind_unit
    (validProg_compPromoteFinishStep ⟨U, V, N, m_cap, rfl,
      henv.of_mem_eq (by rw [hsm_fr]), hb_pos, hb, by dsimp only [b_win]; omega, hb_cap, hn'_max,
      by rw [hsm_dt, ← hmax_eq]; exact hcpl.dt_lt _,
      by rw [hsm_td, ← hmax_eq]; exact hcpl.td_lt _,
      tailBijection_of_gm_eq hsm_gm htail, by rw [hsm_gm]; omega⟩)
    fun _ _ => validProg_pure _

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
