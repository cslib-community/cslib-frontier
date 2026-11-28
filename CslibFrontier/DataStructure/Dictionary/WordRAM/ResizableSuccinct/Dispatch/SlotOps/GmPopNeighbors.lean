/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.Env
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.Internal
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Internal Neighbor-Link Helpers for `compGmPopSlabGenProg`

Internal subroutines, cost bounds, `CompGmFrame` effects, `RealizesBounded .exact`, and
`ValidProg w 0` certificates for neighbor-link updates (`compGmLinkMovedNeighborsGenProg`) during
slab-pool compaction, used privately by `Dispatch.SlotOps.GmPopSlab`.
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

private def compGmReadMovedMetaProg :
    (CompParams × ℕ) × ℕ → Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | ((cp, metaBase), p_last) => do
    let pl2 := p_last + p_last
    let ownB_last := cpGmSlabMetaBase cp + (pl2 + pl2)
    let b_last ← readCompGMGenProg ((cp, metaBase), ownB_last)
    let s_last ← readCompGMGenProg ((cp, metaBase), ownB_last + 1)
    let bel_last ← readCompGMGenProg ((cp, metaBase), ownB_last + 2)
    let abv_last ← readCompGMGenProg ((cp, metaBase), ownB_last + 3)
    pure ((b_last, s_last), (bel_last, abv_last))

private theorem clientState_compGmReadMovedMetaProg (d : (CompParams × ℕ) × ℕ)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (compGmReadMovedMetaProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, p_last⟩
  unfold StateTransitionSpec.clientState; simp [compGmReadMovedMetaProg]

/-- The four metadata words of full slab `p` lie in `globalMetaLen N`, and the first one is at
`gmSlabMetaBase N + 4 * p`. -/
private theorem gmSlabIdx_facts {N p : ℕ} (hb_pos : 0 < bucketBits N) (hp : p < maxFullSlabs N) :
    gmSlabOwnerBIdx N p < globalMetaLen N ∧ gmSlabOwnerBIdx N p + 1 < globalMetaLen N ∧
      gmSlabOwnerBIdx N p + 2 < globalMetaLen N ∧ gmSlabOwnerBIdx N p + 3 < globalMetaLen N ∧
      gmSlabMetaBase N + (p + p + (p + p)) = gmSlabOwnerBIdx N p :=
  ⟨gmSlabOwnerBIdx_lt hb_pos hp, gmSlabOwnerSIdx_lt hb_pos hp, gmSlabBelowIdx_lt hb_pos hp,
    gmSlabAboveIdx_lt hb_pos hp, by unfold gmSlabOwnerBIdx; omega⟩

private theorem clientResult_compGmReadMovedMetaProg {U V w N metaBase p_last : ℕ}
    (hb_pos : 0 < bucketBits N) (hp_last_cap : p_last < maxFullSlabs N) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (compGmReadMovedMetaProg ((mkCompParams U V w N, metaBase), p_last)) =
      ((compGmAt metaBase U w N s.mem (gmSlabOwnerBIdx N p_last),
        compGmAt metaBase U w N s.mem (gmSlabOwnerSIdx N p_last)),
       (compGmAt metaBase U w N s.mem (gmSlabBelowIdx N p_last),
        compGmAt metaBase U w N s.mem (gmSlabAboveIdx N p_last))) := by
  obtain ⟨hownB_last_lt, hownS_last_lt, hbel_last_lt, habv_last_lt, hpl4⟩ :=
    gmSlabIdx_facts hb_pos hp_last_cap
  dsimp only [compGmReadMovedMetaProg, cpGmSlabMetaBase_mk]
  rw [hpl4, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hownB_last_lt,
    clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
    clientResult_readCompGMGenProg hownS_last_lt, clientState_readCompGMGenProg,
    StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hbel_last_lt,
    clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
    clientResult_readCompGMGenProg habv_last_lt, clientState_readCompGMGenProg]
  rfl

private def compGmUpdateNeighborLinksProg :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | (((cp, metaBase), p_del), ((b_last, s_last), (bel_last, abv_last))) => do
    let q_idx := 4 + (b_last + b_last + b_last)
    let q_last ← readCompGMGenProg ((cp, metaBase), q_idx)
    (if 0 < s_last then
      let bl2 := bel_last + bel_last
      let bel_abv_idx := cpGmSlabMetaBase cp + (bl2 + bl2) + 3
      writeCompGMGenProg (((cp, metaBase), bel_abv_idx), p_del)
    else
      pure ()) >>= fun _ =>
      if s_last + 1 < q_last then
        let al2 := abv_last + abv_last
        let abv_bel_idx := cpGmSlabMetaBase cp + (al2 + al2) + 2
        writeCompGMGenProg (((cp, metaBase), abv_bel_idx), p_del)
      else
        pure ()

private def compGmCopyMovedMetaProg :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | (((cp, metaBase), p_del), ((b_last, s_last), (bel_last, abv_last))) => do
    let pd2 := p_del + p_del
    let ownB_del := cpGmSlabMetaBase cp + (pd2 + pd2)
    writeCompGMGenProg (((cp, metaBase), ownB_del), b_last)
    writeCompGMGenProg (((cp, metaBase), ownB_del + 1), s_last)
    writeCompGMGenProg (((cp, metaBase), ownB_del + 2), bel_last)
    writeCompGMGenProg (((cp, metaBase), ownB_del + 3), abv_last)

/-- Update neighbor links and metadata when relocating slab `p_last` into `p_del`. -/
def compGmLinkMovedNeighborsGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), p_del), p_last) => do
    let info ← compGmReadMovedMetaProg ((cp, metaBase), p_last)
    compGmUpdateNeighborLinksProg ((((cp, metaBase), p_del), info))
    compGmCopyMovedMetaProg ((((cp, metaBase), p_del), info))

theorem memoryCost_compGmLinkMovedNeighborsGenProg_le
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmLinkMovedNeighborsGenProg d) s ≤ 34 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
  dsimp only [compGmLinkMovedNeighborsGenProg, compGmReadMovedMetaProg,
    compGmUpdateNeighborLinksProg, compGmCopyMovedMetaProg]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg,
    memoryCost_writeCompGMGenProg, memoryCost_pure]
  split_ifs <;> simp

theorem compGmLinkMovedNeighborsGenProg_effect
    {metaBase itemBase U V w N m_items p_del p_last : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase) (s : Memory.State)
    (hpre : PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del p_last) :
    let gm := compGmAt metaBase U w N s.mem
    let s' := (Memory.spec 0).clientState s
      (compGmLinkMovedNeighborsGenProg (((mkCompParams U V w N, metaBase), p_del), p_last))
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = gmLinkMovedNeighbors N gm p_del p_last := by
  intro gm s'
  rcases hpre with ⟨hp_del_cap, hp_last_cap, hb_last, _, hbel_cap, habv_cap, hb_pos⟩
  let b_last := gm (gmSlabOwnerBIdx N p_last)
  let s_last := gm (gmSlabOwnerSIdx N p_last)
  let bel_last := gm (gmSlabBelowIdx N p_last)
  let abv_last := gm (gmSlabAboveIdx N p_last)
  let q_last := gm (gmQIdx b_last)
  have hq_last_lt : gmQIdx b_last < globalMetaLen N := gmQIdx_lt hb_pos hb_last
  have hownB_del_lt := gmSlabOwnerBIdx_lt hb_pos hp_del_cap
  have hownS_del_lt := gmSlabOwnerSIdx_lt hb_pos hp_del_cap
  have hbel_del_lt := gmSlabBelowIdx_lt hb_pos hp_del_cap
  have habv_del_lt := gmSlabAboveIdx_lt hb_pos hp_del_cap
  have habv_bel_lt : 0 < s_last → gmSlabAboveIdx N bel_last < globalMetaLen N :=
    fun hs => gmSlabAboveIdx_lt hb_pos (hbel_cap hs)
  have hbel_abv_lt : s_last + 1 < q_last → gmSlabBelowIdx N abv_last < globalMetaLen N :=
    fun hs => gmSlabBelowIdx_lt hb_pos (habv_cap hs)
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  have hp_del_val : p_del < 2 ^ globalPtrBits N := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hb_val : b_last < 2 ^ globalPtrBits N := compGmAt_lt ..
  have hs_val : s_last < 2 ^ globalPtrBits N := compGmAt_lt ..
  have hbel_val : bel_last < 2 ^ globalPtrBits N := compGmAt_lt ..
  have habv_val : abv_last < 2 ^ globalPtrBits N := compGmAt_lt ..
  have hq_eq : 4 + (b_last + b_last + b_last) = gmQIdx b_last := by unfold gmQIdx; omega
  have hbl4 : gmSlabMetaBase N + (bel_last + bel_last + (bel_last + bel_last)) + 3 =
      gmSlabAboveIdx N bel_last := by unfold gmSlabAboveIdx; omega
  have hal4 : gmSlabMetaBase N + (abv_last + abv_last + (abv_last + abv_last)) + 2 =
      gmSlabBelowIdx N abv_last := by unfold gmSlabBelowIdx; omega
  have hpd4 : gmSlabMetaBase N + (p_del + p_del + (p_del + p_del)) =
      gmSlabOwnerBIdx N p_del := by unfold gmSlabOwnerBIdx; omega
  have hrd_st := clientState_compGmReadMovedMetaProg ((mkCompParams U V w N, metaBase), p_last) s
  have hrd_res : (Memory.spec 0).clientResult s
      (compGmReadMovedMetaProg ((mkCompParams U V w N, metaBase), p_last)) =
      ((b_last, s_last), (bel_last, abv_last)) :=
    clientResult_compGmReadMovedMetaProg hb_pos hp_last_cap s
  let s_upd := (Memory.spec 0).clientState
    ((Memory.spec 0).clientState s
      (if 0 < s_last then
        writeCompGMGenProg (((mkCompParams U V w N, metaBase),
          gmSlabAboveIdx N bel_last), p_del)
      else pure ()))
    (if s_last + 1 < q_last then
      writeCompGMGenProg (((mkCompParams U V w N, metaBase),
        gmSlabBelowIdx N abv_last), p_del)
    else pure ())
  have hupd_st : (Memory.spec 0).clientState s
      (compGmUpdateNeighborLinksProg ((((mkCompParams U V w N, metaBase), p_del),
        ((b_last, s_last), (bel_last, abv_last))))) = s_upd := by
    dsimp only [compGmUpdateNeighborLinksProg, cpGmSlabMetaBase_mk, s_upd, q_last]
    dsimp only [b_last, bel_last, abv_last, gm] at hq_eq hq_last_lt hbl4 hal4 ⊢
    rw [hq_eq, StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg hq_last_lt,
      clientState_readCompGMGenProg, hbl4, hal4, StateTransitionSpec.clientState_bind]
  have hst : s' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s_upd
            (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
              gmSlabOwnerBIdx N p_del), b_last)))
          (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
            gmSlabOwnerSIdx N p_del), s_last)))
        (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
          gmSlabBelowIdx N p_del), bel_last)))
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
        gmSlabAboveIdx N p_del), abv_last)) := by
    change (Memory.spec 0).clientState s _ = _
    dsimp only [compGmLinkMovedNeighborsGenProg]
    rw [StateTransitionSpec.clientState_bind, hrd_st, hrd_res,
      StateTransitionSpec.clientState_bind, hupd_st]
    dsimp only [compGmCopyMovedMetaProg, cpGmSlabMetaBase_mk,
      gmSlabOwnerSIdx, gmSlabBelowIdx, gmSlabAboveIdx]
    rw [hpd4]
    repeat rw [StateTransitionSpec.clientState_bind]
    rfl
  obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGM_ite (m_items := m_items)
    (0 < s_last) hw hitem habv_bel_lt (fun _ => hp_del_val) s
  obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGM_ite (m_items := m_items)
    (s_last + 1 < q_last) hw hitem hbel_abv_lt (fun _ => hp_del_val) _
  obtain ⟨hf3, hg3⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hownB_del_lt
    hb_val _
  obtain ⟨hf4, hg4⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hownS_del_lt
    hs_val _
  obtain ⟨hf5, hg5⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hbel_del_lt
    hbel_val _
  obtain ⟨hf6, hg6⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem habv_del_lt
    habv_val _
  rw [hst]
  refine ⟨hf1.trans (hf2.trans (hf3.trans (hf4.trans (hf5.trans hf6)))), ?_⟩
  rw [hg6, hg5, hg4, hg3, hg2, hg1]; rfl

private def CompGmReadMovedMetaPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), p_last), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      p_last < maxFullSlabs N

private theorem realizesBounded_compGmReadMovedMeta :
    RealizesBounded .exact compGmReadMovedMetaProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      CompGmReadMovedMetaPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.frontier_fits
    obtain ⟨hownB_last_lt, hownS_last_lt, hbel_last_lt, habv_last_lt, hpl4⟩ :=
      gmSlabIdx_facts hb_pos hp_last_cap
    simp only [cpGmSlabMetaBase_mk, hpl4, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabOwnerBIdx gmSlabMetaBase at *; omega)

private def CompGmUpdateNeighborLinksPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.State → Prop
  | (((cp, metaBase), _p_del), ((b_last, s_last), (bel_last, abv_last))), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b_last < numBuckets N ∧
      s_last + 1 ≤ N ∧
      (0 < s_last → bel_last < maxFullSlabs N) ∧
      (s_last + 1 < compGmAt metaBase U w N s.mem (gmQIdx b_last) → abv_last < maxFullSlabs N)

private theorem realizesBounded_compGmUpdateNeighborLinks :
    RealizesBounded .exact compGmUpdateNeighborLinksProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      CompGmUpdateNeighborLinksPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, ⟨⟨b_last, s_last⟩, ⟨bel_last, abv_last⟩⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb_last, hs_le,
      hbel_cap, habv_cap⟩ := h
    have hq_lt := gmQIdx_lt hb_pos hb_last
    have hq_eq : 4 + (b_last + b_last + b_last) = gmQIdx b_last := by unfold gmQIdx; omega
    simp only [cpGmSlabMetaBase_mk, hq_eq, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg hq_lt] at *)
  all_goals try exact lt_of_le_of_lt (by omega) hU
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmQIdx at *; omega)
  all_goals try (
    have hc_s : 0 < s_last := by assumption
    have hbel_abv := gmSlabAboveIdx_lt hb_pos (hbel_cap hc_s)
    first
    | (refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
       simp only [cpN_mk]; unfold gmSlabAboveIdx at hbel_abv; omega)
    | (refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
       unfold gmSlabAboveIdx gmSlabMetaBase at *; omega))
  all_goals try (
    have hc_abv : s_last + 1 < compGmAt metaBase U w N s.mem (gmQIdx b_last) := by assumption
    have habv_bel := gmSlabBelowIdx_lt hb_pos (habv_cap hc_abv)
    first
    | (refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_⟩, ?_⟩
       · by_cases hc0 : 0 < s_last
         · simp [hc0, runClient_state_writeCompGMGenProg, hfr]
         · simp [hc0, hfr]
       · simp only [cpN_mk]; unfold gmSlabBelowIdx at habv_bel; omega)
    | (refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
       unfold gmSlabBelowIdx gmSlabMetaBase at *; omega))
  refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
  unfold gmQIdx at *; omega

private def CompGmCopyMovedMetaPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.State → Prop
  | (((cp, metaBase), p_del), _info), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      p_del < maxFullSlabs N

private theorem realizesBounded_compGmCopyMovedMeta :
    RealizesBounded .exact compGmCopyMovedMetaProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      CompGmCopyMovedMetaPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, ⟨⟨b_last, s_last⟩, ⟨bel_last, abv_last⟩⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_del_cap⟩ := h
    obtain ⟨hownB_del_lt, hownS_del_lt, hbel_del_lt, habv_del_lt, hpd4⟩ :=
      gmSlabIdx_facts hb_pos hp_del_cap
    simp only [cpGmSlabMetaBase_mk, hpd4, StateTransitionSpec.clientState,
      runClient_state_writeCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabOwnerBIdx gmSlabMetaBase at *; omega)

theorem realizesBounded_compGmLinkMovedNeighbors :
    RealizesBounded .exact compGmLinkMovedNeighborsGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmMovedSlabPre (fun _ _ => 0) := by
  have hrd := realizesBounded_compGmReadMovedMeta
  have hupd := realizesBounded_compGmUpdateNeighborLinks
  have hcpy := realizesBounded_compGmCopyMovedMeta
  realize
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr,
      _, hp_last_cap, _, _, _, _, hb_pos⟩ := h
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap⟩
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr,
      _, hp_last_cap, hb_last, hs_le, hbel_cap, habv_cap, hb_pos⟩ := h
    rw [clientState_compGmReadMovedMetaProg,
      clientResult_compGmReadMovedMetaProg hb_pos hp_last_cap s]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb_last, hs_le, hbel_cap, habv_cap⟩
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr,
      hp_del_cap, _, _, _, _, _, hb_pos⟩ := h
    refine ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_, hb_pos, hp_del_cap⟩
    rw [clientState_compGmReadMovedMetaProg]
    rcases (Memory.spec 0).clientResult s
        (compGmReadMovedMetaProg ((mkCompParams U V w N, metaBase), p_last)) with
      ⟨⟨bL, sL⟩, ⟨belL, abvL⟩⟩
    dsimp only [compGmUpdateNeighborLinksProg, StateTransitionSpec.clientState]
    simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg]
    split_ifs <;> simp [runClient_state_writeCompGMGenProg, hfr]

private theorem validProg_compGmReadMovedMeta {w : ℕ} {d : (CompParams × ℕ) × ℕ}
    {s : Memory.State} (h : CompGmReadMovedMetaPre w d s) :
    ValidProg w 0 s (compGmReadMovedMetaProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, p_last⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap⟩ := h
  have henv : CompMetaEnv w (mkCompParams U V w N) metaBase s :=
    ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩
  obtain ⟨hownB_last, hownS_last, hbel_last, habv_last, hpl4⟩ := gmSlabIdx_facts hb_pos hp_last_cap
  dsimp only [compGmReadMovedMetaProg, cpGmSlabMetaBase_mk]
  rw [hpl4]
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hownB_last⟩) ?_
  rw [clientState_readCompGMGenProg]
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hownS_last⟩) ?_
  rw [clientState_readCompGMGenProg]
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hbel_last⟩) ?_
  rw [clientState_readCompGMGenProg]
  exact validProg_bind (validProg_readCompGMGen ⟨henv, habv_last⟩) (validProg_pure _)

private theorem validProg_compGmUpdateNeighborLinks {w : ℕ}
    {d : ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {s : Memory.State}
    (h : CompGmUpdateNeighborLinksPre w d s) :
    ValidProg w 0 s (compGmUpdateNeighborLinksProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, ⟨⟨b_last, s_last⟩, ⟨bel_last, abv_last⟩⟩⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb_last, _hs_le,
    hbel_cap, habv_cap⟩ := h
  have mkEnv : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  have hq_lt : gmQIdx b_last < globalMetaLen N := gmQIdx_lt hb_pos hb_last
  have hq_eq : 4 + (b_last + b_last + b_last) = gmQIdx b_last := by unfold gmQIdx; omega
  have hbl4 : gmSlabMetaBase N + (bel_last + bel_last + (bel_last + bel_last)) + 3 =
      gmSlabAboveIdx N bel_last := by unfold gmSlabAboveIdx; omega
  have hal4 : gmSlabMetaBase N + (abv_last + abv_last + (abv_last + abv_last)) + 2 =
      gmSlabBelowIdx N abv_last := by unfold gmSlabBelowIdx; omega
  dsimp only [compGmUpdateNeighborLinksProg, cpGmSlabMetaBase_mk]
  rw [hq_eq, hbl4, hal4]
  refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hq_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hq_lt]
  refine validProg_writeCompGM_ite_bind (0 < s_last)
    (fun hs0 => ⟨mkEnv s rfl, gmSlabAboveIdx_lt hb_pos (hbel_cap hs0)⟩) fun s1 hs1 => ?_
  exact validProg_ite
    (fun hsa => validProg_writeCompGMGen ⟨mkEnv s1 hs1, gmSlabBelowIdx_lt hb_pos (habv_cap hsa)⟩)
    (fun _ => validProg_pure ())

private theorem validProg_compGmCopyMovedMeta {w : ℕ}
    {d : ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {s : Memory.State}
    (h : CompGmCopyMovedMetaPre w d s) :
    ValidProg w 0 s (compGmCopyMovedMetaProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, ⟨⟨b_last, s_last⟩, ⟨bel_last, abv_last⟩⟩⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_del_cap⟩ := h
  have mkEnv : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  obtain ⟨hownB_del, hownS_del, hbel_del, habv_del, hpd4⟩ := gmSlabIdx_facts hb_pos hp_del_cap
  dsimp only [compGmCopyMovedMetaProg, cpGmSlabMetaBase_mk]
  rw [hpd4]
  exact validProg_writeCompGM_bind ⟨mkEnv s rfl, hownB_del⟩ fun s1 hs1 =>
    validProg_writeCompGM_bind ⟨mkEnv s1 hs1, hownS_del⟩ fun s2 hs2 =>
      validProg_writeCompGM_bind ⟨mkEnv s2 (hs2.trans hs1), hbel_del⟩ fun s3 hs3 =>
        validProg_writeCompGMGen ⟨mkEnv s3 (hs3.trans (hs2.trans hs1)), habv_del⟩

theorem validProg_compGmLinkMovedNeighbors {w : ℕ} {d : ((CompParams × ℕ) × ℕ) × ℕ}
    {s : Memory.State} (h : CompGmMovedSlabPre w d s) :
    ValidProg w 0 s (compGmLinkMovedNeighborsGenProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hp_del_cap, hp_last_cap, hb_last, hs_le,
    hbel_cap, habv_cap, hb_pos⟩ := h
  dsimp only [compGmLinkMovedNeighborsGenProg]
  refine validProg_bind
    (validProg_compGmReadMovedMeta ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_last_cap⟩)
    ?_
  rw [clientState_compGmReadMovedMetaProg,
    clientResult_compGmReadMovedMetaProg hb_pos hp_last_cap s]
  refine validProg_bind_unit
    (validProg_compGmUpdateNeighborLinks
      ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb_last, hs_le, hbel_cap, habv_cap⟩)
    fun s1 hs1 => ?_
  have hfr1 : metaBase + offCompItems U w N ≤ s1.frontier := by
    have hs1_fr : s1.frontier = s.frontier := by
      rw [hs1]
      dsimp only [compGmUpdateNeighborLinksProg, StateTransitionSpec.clientState]
      simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
        runClient_state_readCompGMGenProg]
      split_ifs <;> simp [runClient_state_writeCompGMGenProg]
    exact hs1_fr ▸ hfr
  exact validProg_compGmCopyMovedMeta ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr1, hb_pos, hp_del_cap⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
