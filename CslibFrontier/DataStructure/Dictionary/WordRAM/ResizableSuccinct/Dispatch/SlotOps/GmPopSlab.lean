/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.Env
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.Internal
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.GmPopRelink
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.GmPopNeighbors
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Compacted `GlobalMeta` Slab Pop and Pool Compaction (`compGmPopSlabGenProg`)

Implements `compGmPopSlabGenProg` in `Memory.Prog` (`¬ReadsWidth`), combining top-slab unlinking
and swap-with-last pool compaction with exact `gmPopSlab` state effects, `CompGmFrame`
preservation, `RealizesBounded .exact`, and `ValidProg w 0` admissibility.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compGmPopSlabGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompGmPopSlabPre`:
  slab-pop and pool-compaction subroutine in compacted `GlobalMeta` and its precondition.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compGmPopSlabGenProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_compGmPopSlabGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.validProg_compGmPopSlabGen`:
  exact `gmPopSlab` effect, `RealizesBounded .exact`, and `ValidProg w 0` certificate.
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

private def compGmMoveLastSlabMetaProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), p_del), p_last) => do
    compGmRelinkMovedSlabGenProg (((cp, metaBase), p_del), p_last)
    compGmLinkMovedNeighborsGenProg (((cp, metaBase), p_del), p_last)

private def compGmCompactSlabStepProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), p_del), p_last) => do
    (if p_del < p_last then
      compGmMoveLastSlabMetaProg (((cp, metaBase), p_del), p_last)
    else
      pure ()) >>= fun _ =>
      writeCompGMGenProg (((cp, metaBase), 0), p_last)

private def compGmCompactSlabGenProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, metaBase), p_del) => do
    let n_slabs ← readCompGMGenProg ((cp, metaBase), 0)
    compGmCompactSlabStepProg (((cp, metaBase), p_del), n_slabs - 1)

/-- Pop the top slab of bucket `b` and compact the slab pool in `GlobalMeta` (`gmPopSlab`,
`¬ReadsWidth`). -/
def compGmPopSlabGenProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, metaBase), b) => do
    let p_del ← compGmUnlinkTopSlabGenProg ((cp, metaBase), b)
    compGmCompactSlabGenProg ((cp, metaBase), p_del)

private theorem memoryCost_compGmCompactSlabGenProg_le
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmCompactSlabGenProg d) s ≤ 54 := by
  rcases d with ⟨⟨cp, metaBase⟩, p_del⟩
  dsimp only [compGmCompactSlabGenProg, compGmCompactSlabStepProg, compGmMoveLastSlabMetaProg]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg,
    memoryCost_writeCompGMGenProg]
  split_ifs
  · simp only [Realization.memoryCost_bind']
    have h1 := memoryCost_compGmRelinkMovedSlabGenProg_le
      (((cp, metaBase), p_del),
        (Memory.spec 0).clientResult s (readCompGMGenProg ((cp, metaBase), 0)) - 1)
      ((Memory.spec 0).clientState s (readCompGMGenProg ((cp, metaBase), 0)))
    have h2 := memoryCost_compGmLinkMovedNeighborsGenProg_le
      (((cp, metaBase), p_del),
        (Memory.spec 0).clientResult s (readCompGMGenProg ((cp, metaBase), 0)) - 1)
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState s (readCompGMGenProg ((cp, metaBase), 0)))
        (compGmRelinkMovedSlabGenProg
          (((cp, metaBase), p_del),
            (Memory.spec 0).clientResult s (readCompGMGenProg ((cp, metaBase), 0)) - 1)))
    omega
  · simp

theorem memoryCost_compGmPopSlabGenProg_le
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmPopSlabGenProg d) s ≤ 68 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  dsimp only [compGmPopSlabGenProg]
  rw [Realization.memoryCost_bind', memoryCost_compGmUnlinkTopSlabGenProg_eq]
  have h2 := memoryCost_compGmCompactSlabGenProg_le
    ((cp, metaBase),
      (Memory.spec 0).clientResult s (compGmUnlinkTopSlabGenProg ((cp, metaBase), b)))
    ((Memory.spec 0).clientState s (compGmUnlinkTopSlabGenProg ((cp, metaBase), b)))
  omega

/-- Precondition for popping a slab in global metadata. -/
@[expose] def CompGmPopSlabPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      SlabBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmQIdx b'))
        (compGmAt metaBase U w N s.mem 0) ∧
      1 ≤ compGmAt metaBase U w N s.mem (gmQIdx b)

private def CompGmCompactSlabPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), p_del), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      1 ≤ compGmAt metaBase U w N s.mem 0 ∧
      compGmAt metaBase U w N s.mem 0 ≤ maxFullSlabs N ∧
      p_del < compGmAt metaBase U w N s.mem 0 ∧
      (p_del < compGmAt metaBase U w N s.mem 0 - 1 →
        PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del
          (compGmAt metaBase U w N s.mem 0 - 1))

private theorem realizesBounded_compGmUnlinkTopSlab :
    RealizesBounded .exact compGmUnlinkTopSlabGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompGmPopSlabPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hwr := realizesBounded_compGmUnlinkWrite
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hq_pos⟩ := h
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have htop_idx_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
    have htop_eq : gmQIdx b + 2 = gmSlabTopIdx b := rfl
    have hp_del_cap : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) < maxFullSlabs N :=
      lt_of_lt_of_le (hslab.top_lt hb hq_pos) hslab.nslabs_le
    have hbel_idx_lt := gmSlabBelowIdx_lt hb_pos hp_del_cap
    have hbel_eq : gmSlabMetaBase N +
        (compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
          compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
          (compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
            compGmAt metaBase U w N s.mem (gmSlabTopIdx b))) + 2 =
        gmSlabBelowIdx N (compGmAt metaBase U w N s.mem (gmSlabTopIdx b)) := by
      unfold gmSlabBelowIdx; omega
    simp only [cpGmSlabMetaBase_mk, hq_eq, htop_eq, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg htop_idx_lt] at *
    rw [hbel_eq] at *
    try rw [clientResult_readCompGMGenProg hq_idx_lt] at *
    try rw [clientResult_readCompGMGenProg hbel_idx_lt] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; omega⟩
  all_goals try exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hq_pos⟩
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabTopIdx gmSlabBelowIdx gmSlabMetaBase gmQIdx at *
    omega)

private theorem validProg_compGmUnlinkTopSlab {w : ℕ} {d : (CompParams × ℕ) × ℕ}
    {s : Memory.State} (h : CompGmPopSlabPre w d s) :
    ValidProg w 0 s (compGmUnlinkTopSlabGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hq_pos⟩ := h
  have mkEnv : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  have htop_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
  have htop_eq : gmQIdx b + 2 = gmSlabTopIdx b := rfl
  have hp_del_max : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) < maxFullSlabs N :=
    lt_of_lt_of_le (hslab.top_lt hb hq_pos) hslab.nslabs_le
  have hbel_lt := gmSlabBelowIdx_lt hb_pos hp_del_max
  have hp4 : gmSlabMetaBase N + (compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
      compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
      (compGmAt metaBase U w N s.mem (gmSlabTopIdx b) +
      compGmAt metaBase U w N s.mem (gmSlabTopIdx b))) + 2 =
      gmSlabBelowIdx N (compGmAt metaBase U w N s.mem (gmSlabTopIdx b)) := by
    unfold gmSlabBelowIdx; omega
  dsimp only [compGmUnlinkTopSlabGenProg, compGmUnlinkWriteProg, cpGmSlabMetaBase_mk]
  rw [hq_eq, htop_eq]
  refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, htop_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg htop_lt]
  refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hq_lt⟩) ?_
  rw [clientState_readCompGMGenProg, hp4]
  refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hbel_lt⟩) ?_
  rw [clientState_readCompGMGenProg]
  refine validProg_bind
    (validProg_writeCompGM_bind ⟨mkEnv s rfl, htop_lt⟩ fun s1 hs1 =>
      validProg_writeCompGMGen ⟨mkEnv s1 hs1, hq_lt⟩) ?_
  exact validProg_pure _

private theorem compGmCompactSlabGenProg_effect {metaBase itemBase U V w N m_items p_del : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase) (s : Memory.State)
    (h0_pos : 1 ≤ compGmAt metaBase U w N s.mem 0)
    (h0_le : compGmAt metaBase U w N s.mem 0 ≤ maxFullSlabs N)
    (hcond : p_del < compGmAt metaBase U w N s.mem 0 - 1 →
      PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del
        (compGmAt metaBase U w N s.mem 0 - 1)) :
    let gm := compGmAt metaBase U w N s.mem
    let s' := (Memory.spec 0).clientState s
      (compGmCompactSlabGenProg ((mkCompParams U V w N, metaBase), p_del))
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = gmCompactSlab N gm p_del := by
  intro gm s'
  let p_last := gm 0 - 1
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  have hp_last_val : p_last < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_n_max (by dsimp only [p_last, gm] at *; omega)
  dsimp only [s', compGmCompactSlabGenProg, compGmCompactSlabStepProg, compGmMoveLastSlabMetaProg]
  rw [StateTransitionSpec.clientState_bind, clientResult_readCompGMGenProg h0_lt,
    clientState_readCompGMGenProg, StateTransitionSpec.clientState_bind]
  by_cases hlt : p_del < p_last
  · have hm1 := hcond hlt
    obtain ⟨hf1, hg1⟩ := compGmRelinkMovedSlabGenProg_effect (m_items := m_items) hw hitem s hm1
    obtain ⟨hf2, hg2⟩ := compGmLinkMovedNeighborsGenProg_effect (m_items := m_items) hw hitem _
      (hg1.symm ▸ pureMovedSlabInv_after_relink hm1)
    obtain ⟨hf3, hg3⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem h0_lt
      hp_last_val _
    rw [ite_eq_left hlt, StateTransitionSpec.clientState_bind]
    refine ⟨hf1.trans (hf2.trans hf3), ?_⟩
    rw [hg3, hg2, hg1]
    exact gmCompactSlab_eq_parts gm hlt hm1.2.2.1
  · obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem h0_lt
      hp_last_val s
    rw [ite_eq_right hlt, StateTransitionSpec.clientState_pure]
    refine ⟨hf1, ?_⟩
    unfold gmCompactSlab; rw [ite_eq_right hlt, hg1]

private theorem realizesBounded_compGmMoveLastSlabMeta :
    RealizesBounded .exact compGmMoveLastSlabMetaProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmMovedSlabPre (fun _ _ => 0) := by
  have hrel := realizesBounded_compGmRelinkMovedSlab
  have hlnk := realizesBounded_compGmLinkMovedNeighbors
  realize
  · exact h
  · rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hinv⟩ := h
    obtain ⟨hf1, hg1⟩ := compGmRelinkMovedSlabGenProg_effect
      (itemBase := metaBase + offCompItems U w N) (U := U) (V := V) (m_items := 0)
      hw le_rfl s hinv
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hf1.frontier_eq.symm ▸ hfr,
      hg1.symm ▸ pureMovedSlabInv_after_relink hinv⟩

private def CompGmCompactSlabStepPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), p_del), p_last), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      (p_del < p_last → PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del p_last)

/-- The optional metadata move of a compaction step leaves the frontier unchanged. -/
private theorem frontier_compGmCompactSlabMove {metaBase U V w N p_del p_last : ℕ} (hw : 0 < w)
    (s : Memory.State)
    (hcond : p_del < p_last → PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del p_last) :
    ((Memory.spec 0).clientState s
      (if p_del < p_last then
        compGmMoveLastSlabMetaProg (((mkCompParams U V w N, metaBase), p_del), p_last)
      else pure ())).frontier = s.frontier := by
  split_ifs with hc
  · obtain ⟨hf1, hg1⟩ := compGmRelinkMovedSlabGenProg_effect
      (itemBase := metaBase + offCompItems U w N) (U := U) (V := V) (m_items := 0)
      hw le_rfl s (hcond hc)
    obtain ⟨hf2, _⟩ := compGmLinkMovedNeighborsGenProg_effect
      (itemBase := metaBase + offCompItems U w N) (U := U) (V := V) (m_items := 0)
      hw le_rfl _ (hg1.symm ▸ pureMovedSlabInv_after_relink (hcond hc))
    dsimp only [compGmMoveLastSlabMetaProg]
    rw [StateTransitionSpec.clientState_bind, hf2.frontier_eq, hf1.frontier_eq]
  · rfl

private theorem realizesBounded_compGmCompactSlabStep :
    RealizesBounded .exact compGmCompactSlabStepProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmCompactSlabStepPre (fun _ _ => 0) := by
  have hmov := realizesBounded_compGmMoveLastSlabMeta
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hcond⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega)
  all_goals try exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hcond hc⟩
  exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl,
    hfr.trans_eq (frontier_compGmCompactSlabMove hw s hcond).symm⟩, h0_lt⟩

private theorem realizesBounded_compGmCompactSlab :
    RealizesBounded .exact compGmCompactSlabGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmCompactSlabPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  have hstp := realizesBounded_compGmCompactSlabStep
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, p_del⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, h0_pos, h0_le, hp_lt, hcond⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    simp only [StateTransitionSpec.clientState, clientResult_readCompGMGenProg h0_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, h0_lt⟩
  all_goals try exact h0_pos
  exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hcond⟩

private theorem pureCompactSlab_of_slabBijection {N b : ℕ} {gm : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hslab : SlabBijection N gm (fun b' => gm (gmQIdx b')) (gm 0))
    (hq_pos : 1 ≤ gm (gmQIdx b)) :
    let p_del := gm (gmSlabTopIdx b)
    let gm' := gmUnlinkTopSlab N gm b
    1 ≤ gm' 0 ∧ gm' 0 ≤ maxFullSlabs N ∧ p_del < gm' 0 ∧
    (p_del < gm' 0 - 1 → PureMovedSlabInv N gm' p_del (gm' 0 - 1)) := by
  intro p_del gm'
  obtain ⟨hu0, _, _, huQ, _, huGe, _⟩ := gmUnlinkTopSlab_fields gm hb
  have hB_ge : ∀ p, gmSlabDirBase N ≤ gmSlabOwnerBIdx N p :=
    fun _ => by unfold gmSlabOwnerBIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hS_ge : ∀ p, gmSlabDirBase N ≤ gmSlabOwnerSIdx N p :=
    fun _ => by unfold gmSlabOwnerSIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hBel_ge : ∀ p, gmSlabDirBase N ≤ gmSlabBelowIdx N p :=
    fun _ => by unfold gmSlabBelowIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hAbv_ge : ∀ p, gmSlabDirBase N ≤ gmSlabAboveIdx N p :=
    fun _ => by unfold gmSlabAboveIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hp_del_lt : p_del < gm 0 := hslab.top_lt hb hq_pos
  dsimp only [gm']
  rw [hu0]
  refine ⟨by omega, hslab.nslabs_le, hp_del_lt, fun hlt => ?_⟩
  unfold PureMovedSlabInv; dsimp only
  rw [huGe _ (hB_ge _), huGe _ (hS_ge _), huGe _ (hBel_ge _), huGe _ (hAbv_ge _)]
  obtain ⟨hb_last, hs_last, hptr_last⟩ := hslab.owner_valid (gm 0 - 1) (by omega)
  have hq_last_le : gm (gmQIdx (gm (gmSlabOwnerBIdx N (gm 0 - 1)))) ≤ gm 0 :=
    q_le_nslabs_of_slabBijection hslab hb_last
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  refine ⟨lt_of_lt_of_le hp_del_lt hslab.nslabs_le,
    lt_of_lt_of_le (by omega : gm 0 - 1 < gm 0) hslab.nslabs_le,
    hb_last, by have := hslab.nslabs_le; omega, ?_, ?_, hb_pos⟩
  · intro hs_pos
    have hbel_eq := hslab.below_eq _ hb_last _ hs_last hs_pos
    rw [hptr_last] at hbel_eq
    rw [hbel_eq]
    exact hslab.ptr_lt_maxFullSlabs hb_last (by omega)
  · intro hs_lt_q
    rw [huQ _ hb_last] at hs_lt_q
    have hs1_lt : gm (gmSlabOwnerSIdx N (gm 0 - 1)) + 1 <
        gm (gmQIdx (gm (gmSlabOwnerBIdx N (gm 0 - 1)))) := by
      split_ifs at hs_lt_q with hbeq
      · subst hbeq; omega
      · exact hs_lt_q
    have habv_eq := hslab.above_eq _ hb_last _ hs_last hs1_lt
    rw [hptr_last] at habv_eq
    rw [habv_eq]
    exact hslab.ptr_lt_maxFullSlabs hb_last hs1_lt

theorem compGmPopSlabGenProg_effect {metaBase itemBase U V w N m_items b : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) (s : Memory.State)
    (hslab : SlabBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmQIdx b'))
      (compGmAt metaBase U w N s.mem 0))
    (hq_pos : 1 ≤ compGmAt metaBase U w N s.mem (gmQIdx b)) :
    let s' := (Memory.spec 0).clientState s
      (compGmPopSlabGenProg ((mkCompParams U V w N, metaBase), b))
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = gmPopSlab N (compGmAt metaBase U w N s.mem) b := by
  intro s'
  obtain ⟨hres1, hf1, hg1⟩ :=
    compGmUnlinkTopSlabGenProg_effect (m_items := m_items) hw hitem hb_pos hb s hslab hq_pos
  obtain ⟨hc1, hc2, _, hc4⟩ := pureCompactSlab_of_slabBijection hb_pos hb hslab hq_pos
  obtain ⟨hf2, hg2⟩ := compGmCompactSlabGenProg_effect
    (p_del := (Memory.spec 0).clientResult s
      (compGmUnlinkTopSlabGenProg ((mkCompParams U V w N, metaBase), b)))
    (m_items := m_items) hw hitem
    ((Memory.spec 0).clientState s
      (compGmUnlinkTopSlabGenProg ((mkCompParams U V w N, metaBase), b)))
    (hg1.symm ▸ hc1) (hg1.symm ▸ hc2)
    (by rw [hg1, hres1]; exact hc4)
  dsimp only [s', compGmPopSlabGenProg]
  rw [StateTransitionSpec.clientState_bind]
  refine ⟨hf1.trans hf2, ?_⟩
  rw [hg2, hg1, hres1]; rfl

theorem realizesBounded_compGmPopSlabGen :
    RealizesBounded .exact compGmPopSlabGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmPopSlabPre (fun _ _ => 0) := by
  have hunl := realizesBounded_compGmUnlinkTopSlab
  have hcmp := realizesBounded_compGmCompactSlab
  realize
  · exact h
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hq_pos⟩ := h
    obtain ⟨hres1, hf1, hg1⟩ :=
      compGmUnlinkTopSlabGenProg_effect (itemBase := metaBase + offCompItems U w N) (m_items := 0)
        hw le_rfl hb_pos hb s hslab hq_pos
    obtain ⟨hc1, hc2, hc3, hc4⟩ := pureCompactSlab_of_slabBijection hb_pos hb hslab hq_pos
    refine ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hf1.frontier_eq.symm ▸ hfr, hb_pos, ?_⟩
    rw [hres1, hg1]
    exact ⟨hc1, hc2, hc3, hc4⟩

private theorem validProg_compGmMoveLastSlabMeta {w : ℕ} {d : ((CompParams × ℕ) × ℕ) × ℕ}
    {s : Memory.State} (h : CompGmMovedSlabPre w d s) :
    ValidProg w 0 s (compGmMoveLastSlabMetaProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hm1⟩ := h
  obtain ⟨hf_r, hg_r⟩ := compGmRelinkMovedSlabGenProg_effect
    (itemBase := metaBase + offCompItems U w N) (m_items := 0) hw le_rfl s hm1
  refine validProg_bind_unit
    (validProg_compGmRelinkMovedSlab ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hm1⟩)
    fun s1 hs1 => ?_
  have hfr1 : metaBase + offCompItems U w N ≤ s1.frontier :=
    hfr.trans_eq ((congrArg Memory.State.frontier hs1).trans hf_r.frontier_eq).symm
  have hgm1 := (congrArg (fun st : Memory.State => compGmAt metaBase U w N st.mem) hs1).trans hg_r
  have hm2 : PureMovedSlabInv N (compGmAt metaBase U w N s1.mem) p_del p_last :=
    pureMovedSlabInv_congr hgm1.symm rfl (pureMovedSlabInv_after_relink hm1)
  exact validProg_compGmLinkMovedNeighbors ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr1, hm2⟩

private theorem validProg_compGmCompactSlabStep {w : ℕ} {d : ((CompParams × ℕ) × ℕ) × ℕ}
    {s : Memory.State} (h : CompGmCompactSlabStepPre w d s) :
    ValidProg w 0 s (compGmCompactSlabStepProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, p_del⟩, p_last⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hcond⟩ := h
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  dsimp only [compGmCompactSlabStepProg]
  refine validProg_bind_unit
    (validProg_ite (fun hlt => ?_) (fun _ => validProg_pure ())) fun s1 hs1 => ?_
  · exact validProg_compGmMoveLastSlabMeta ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hcond hlt⟩
  · have hfr1 : metaBase + offCompItems U w N ≤ s1.frontier := by
      rw [hs1, frontier_compGmCompactSlabMove hw s hcond]; exact hfr
    exact validProg_writeCompGMGen ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr1⟩, h0_lt⟩

private theorem validProg_compGmCompactSlab {w : ℕ} {d : (CompParams × ℕ) × ℕ}
    {s : Memory.State} (h : CompGmCompactSlabPre w d s) :
    ValidProg w 0 s (compGmCompactSlabGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, p_del⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, _, _, _, hcond⟩ := h
  have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
  dsimp only [compGmCompactSlabGenProg]
  refine validProg_bind_of_eq
    (validProg_readCompGMGen ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, h0_lt⟩)
    (clientResult_readCompGMGenProg (U := U) (V := V) (w := w) (metaBase := metaBase) h0_lt s)
    fun s1 hs1 => ?_
  have hs1_eq : s1 = s := hs1.trans (clientState_readCompGMGenProg _ s)
  subst hs1_eq
  exact validProg_compGmCompactSlabStep ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hcond⟩

theorem validProg_compGmPopSlabGen {w : ℕ} {d : (CompParams × ℕ) × ℕ} {s : Memory.State}
    (h : CompGmPopSlabPre w d s) : ValidProg w 0 s (compGmPopSlabGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hq_pos⟩ := h
  dsimp only [compGmPopSlabGenProg]
  obtain ⟨hres1, hf1, hg1⟩ :=
    compGmUnlinkTopSlabGenProg_effect (itemBase := metaBase + offCompItems U w N) (m_items := 0)
      hw le_rfl hb_pos hb s hslab hq_pos
  obtain ⟨hc1, hc2, hc3, hc4⟩ := pureCompactSlab_of_slabBijection hb_pos hb hslab hq_pos
  refine validProg_bind_of_eq
    (validProg_compGmUnlinkTopSlab ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab,
      hq_pos⟩) hres1 fun s1 hs1 => ?_
  have hfr1 : metaBase + offCompItems U w N ≤ s1.frontier :=
    hfr.trans_eq ((congrArg Memory.State.frontier hs1).trans hf1.frontier_eq).symm
  have hgm1 : compGmAt metaBase U w N s1.mem =
      gmUnlinkTopSlab N (compGmAt metaBase U w N s.mem) b :=
    (congrArg (fun st : Memory.State => compGmAt metaBase U w N st.mem) hs1).trans hg1
  refine validProg_compGmCompactSlab ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr1, hb_pos,
    by rwa [hgm1], by rwa [hgm1], by rwa [hgm1], fun hlt => ?_⟩
  have hlt' : compGmAt metaBase U w N s.mem (gmSlabTopIdx b) <
      gmUnlinkTopSlab N (compGmAt metaBase U w N s.mem) b 0 - 1 :=
    hlt.trans_eq (congrArg (· - 1) (congrFun hgm1 0))
  exact pureMovedSlabInv_congr hgm1.symm (congrArg (· - 1) (congrFun hgm1.symm 0)) (hc4 hlt')

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
