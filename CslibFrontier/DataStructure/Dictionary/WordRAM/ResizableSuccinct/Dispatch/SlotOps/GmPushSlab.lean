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
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Compacted `GlobalMeta` Slab Push (`compGmPushSlabGenProg`)

Implements `compGmPushSlabGenProg` in `Memory.Prog` (`¬ReadsWidth`), proving its exact
`gmPushSlab` state effect, `CompGmFrame` preservation, `RealizesBounded .exact`, and
`ValidProg w 0` admissibility.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compGmPushSlabGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompGmPushSlabPre`:
  slab-push subroutine in compacted `GlobalMeta` and its precondition.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compGmPushSlabGenProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_compGmPushSlabGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.validProg_compGmPushSlabGen`:
  exact `gmPushSlab` effect, `RealizesBounded .exact`, and `ValidProg w 0` certificate.
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

private def compGmPushReadProg :
    (CompParams × ℕ) × ℕ → Memory.Prog ((ℕ × ℕ) × ℕ)
  | ((cp, metaBase), b) => do
    let q_idx := 4 + (b + b + b)
    let q_b ← readCompGMGenProg ((cp, metaBase), q_idx)
    let p_new ← readCompGMGenProg ((cp, metaBase), 0)
    let top_old ← readCompGMGenProg ((cp, metaBase), q_idx + 2)
    pure ((q_b, p_new), top_old)

private theorem clientState_compGmPushReadProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compGmPushReadProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  unfold StateTransitionSpec.clientState; simp [compGmPushReadProg]

private theorem gmPush_q_indices {N b : ℕ} (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) :
    gmQIdx b < globalMetaLen N ∧ 4 + (b + b + b) = gmQIdx b ∧
    gmSlabTopIdx b < globalMetaLen N ∧ gmQIdx b + 2 = gmSlabTopIdx b ∧
    0 < globalMetaLen N :=
  ⟨gmQIdx_lt hb_pos hb, by simp only [gmQIdx]; omega, gmSlabTopIdx_lt hb_pos hb, rfl,
    by simp only [globalMetaLen]; omega⟩

private theorem clientResult_compGmPushReadProg {U V w N metaBase b : ℕ}
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (compGmPushReadProg ((mkCompParams U V w N, metaBase), b)) =
      ((compGmAt metaBase U w N s.mem (gmQIdx b), compGmAt metaBase U w N s.mem 0),
        compGmAt metaBase U w N s.mem (gmSlabTopIdx b)) := by
  obtain ⟨hq_idx_lt, hq_eq, htop_idx_lt, htop_eq, h0_lt⟩ := gmPush_q_indices hb_pos hb
  dsimp only [compGmPushReadProg]
  rw [hq_eq, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hq_idx_lt,
    clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
    clientResult_readCompGMGenProg h0_lt, clientState_readCompGMGenProg,
    htop_eq, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg htop_idx_lt,
    clientState_readCompGMGenProg]
  rfl

private def compGmPushWriteOwnerProg :
    ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), (b, q_b)), (p_new, top_old)) => do
    let p2 := p_new + p_new
    let ownB_idx := cpGmSlabMetaBase cp + (p2 + p2)
    writeCompGMGenProg (((cp, metaBase), ownB_idx), b)
    writeCompGMGenProg (((cp, metaBase), ownB_idx + 1), q_b)
    writeCompGMGenProg (((cp, metaBase), ownB_idx + 2), top_old)

private def compGmPushWriteLinksProg :
    ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), (b, q_b)), (p_new, top_old)) =>
    (if 0 < q_b then
      let t2 := top_old + top_old
      let abv_idx := cpGmSlabMetaBase cp + (t2 + t2) + 3
      writeCompGMGenProg (((cp, metaBase), abv_idx), p_new)
    else
      pure ()) >>= fun _ =>
      if q_b < cpDirSlabs cp then
        let dir_idx := cpGmSlabDirBase cp + b * cpDirSlabs cp + q_b
        writeCompGMGenProg (((cp, metaBase), dir_idx), p_new)
      else
        pure ()

private def compGmPushFinishProg :
    ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), (b, q_b)), p_new) => do
    let q_idx := 4 + (b + b + b)
    let top_idx := q_idx + 2
    writeCompGMGenProg (((cp, metaBase), top_idx), p_new)
    writeCompGMGenProg (((cp, metaBase), q_idx), q_b + 1)
    writeCompGMGenProg (((cp, metaBase), 0), p_new + 1)

private def compGmPushApplyProg :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), b), ((q_b, p_new), top_old)) => do
    compGmPushWriteOwnerProg ((((cp, metaBase), (b, q_b)), (p_new, top_old)))
    compGmPushWriteLinksProg ((((cp, metaBase), (b, q_b)), (p_new, top_old)))
    compGmPushFinishProg ((((cp, metaBase), (b, q_b)), p_new))

/-- Push a new full slab `p_new = gm 0` onto bucket `b` in compacted `GlobalMeta` (`gmPushSlab`,
`¬ReadsWidth`). -/
def compGmPushSlabGenProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, metaBase), b) => do
    let info ← compGmPushReadProg ((cp, metaBase), b)
    compGmPushApplyProg (((cp, metaBase), b), info)

theorem memoryCost_compGmPushSlabGenProg_le
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compGmPushSlabGenProg d) s ≤ 38 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  dsimp only [compGmPushSlabGenProg, compGmPushReadProg, compGmPushApplyProg,
    compGmPushWriteOwnerProg, compGmPushWriteLinksProg, compGmPushFinishProg]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg,
    memoryCost_writeCompGMGenProg, memoryCost_pure]
  split_ifs <;> simp

/-- Precondition for pushing a slab in global metadata. -/
@[expose] def CompGmPushSlabPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
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
      compGmAt metaBase U w N s.mem 0 < maxFullSlabs N

theorem compGmPushSlabGenProg_effect {metaBase itemBase U V w N m_items b : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) (s : Memory.State)
    (hslab : SlabBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmQIdx b'))
      (compGmAt metaBase U w N s.mem 0))
    (hp_lt : compGmAt metaBase U w N s.mem 0 < maxFullSlabs N) :
    let s' := (Memory.spec 0).clientState s
      (compGmPushSlabGenProg ((mkCompParams U V w N, metaBase), b))
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = gmPushSlab N (compGmAt metaBase U w N s.mem) b := by
  intro s'
  let gm := compGmAt metaBase U w N s.mem
  obtain ⟨hq_idx_lt, hq_eq, htop_idx_lt, htop_eq, h0_lt⟩ := gmPush_q_indices hb_pos hb
  have hownB_lt : gmSlabOwnerBIdx N (gm 0) < globalMetaLen N := gmSlabOwnerBIdx_lt hb_pos hp_lt
  have hownS_lt : gmSlabOwnerBIdx N (gm 0) + 1 < globalMetaLen N := gmSlabOwnerSIdx_lt hb_pos hp_lt
  have hbel_lt : gmSlabOwnerBIdx N (gm 0) + 2 < globalMetaLen N := gmSlabBelowIdx_lt hb_pos hp_lt
  have habv_lt : 0 < gm (gmQIdx b) → gmSlabAboveIdx N (gm (gmSlabTopIdx b)) < globalMetaLen N :=
    fun hq_pos => gmSlabAboveIdx_lt hb_pos ((hslab.top_lt hb hq_pos).trans hp_lt)
  have hdir_lt : gm (gmQIdx b) < dirSlabsPerBucket N →
      gmSlabDirBase N + b * dirSlabsPerBucket N + gm (gmQIdx b) < globalMetaLen N :=
    fun hdir => gmSlabDirIdx_lt hb_pos hb hdir
  have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
  have hq_le_p : gm (gmQIdx b) ≤ gm 0 := q_le_nslabs_of_slabBijection hslab hb
  have hb_val : b < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos (by unfold gmQIdx at hq_idx_lt; omega)
  have hp_val : gm 0 < 2 ^ globalPtrBits N := compGmAt_lt ..
  have hq1_val : gm (gmQIdx b) + 1 < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_n_max (by dsimp only [gm] at *; omega)
  have hp1_val : gm 0 + 1 < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_n_max (by dsimp only [gm] at *; omega)
  have hp4 : gmSlabMetaBase N + (gm 0 + gm 0 + (gm 0 + gm 0)) =
      gmSlabOwnerBIdx N (gm 0) := by unfold gmSlabOwnerBIdx; omega
  have ht4 : gmSlabMetaBase N +
      (gm (gmSlabTopIdx b) + gm (gmSlabTopIdx b) +
        (gm (gmSlabTopIdx b) + gm (gmSlabTopIdx b))) + 3 =
      gmSlabAboveIdx N (gm (gmSlabTopIdx b)) := by unfold gmSlabAboveIdx; omega
  dsimp only [gm, s', compGmPushSlabGenProg] at *
  rw [StateTransitionSpec.clientState_bind, clientState_compGmPushReadProg,
    clientResult_compGmPushReadProg hb_pos hb]
  dsimp only [compGmPushApplyProg, compGmPushWriteOwnerProg, compGmPushWriteLinksProg,
    compGmPushFinishProg, cpGmSlabMetaBase_mk, cpDirSlabs_mk, cpGmSlabDirBase_mk]
  rw [hp4, ht4, hq_eq, htop_eq]
  repeat rw [StateTransitionSpec.clientState_bind]
  obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hownB_lt
    hb_val s
  obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hownS_lt
    (compGmAt_lt ..) _
  obtain ⟨hf3, hg3⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hbel_lt
    (compGmAt_lt ..) _
  obtain ⟨hf4, hg4⟩ := compGmFrame_writeCompGM_ite (m_items := m_items) _ hw hitem habv_lt
    (fun _ => hp_val) _
  obtain ⟨hf5, hg5⟩ := compGmFrame_writeCompGM_ite (m_items := m_items) _ hw hitem hdir_lt
    (fun _ => hp_val) _
  obtain ⟨hf6, hg6⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem htop_idx_lt
    hp_val _
  obtain ⟨hf7, hg7⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hq_idx_lt
    hq1_val _
  obtain ⟨hf8, hg8⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem h0_lt
    hp1_val _
  refine ⟨hf1.trans (hf2.trans (hf3.trans (hf4.trans (hf5.trans (hf6.trans (hf7.trans hf8)))))),
    ?_⟩
  -- `dsimp` leaves `cpDirSlabs` in a `Decidable` instance, so match the goal up to defeq.
  exact hg8.trans (by rw [hg7, hg6, hg5, hg4, hg3, hg2, hg1]; rfl)

private def CompGmPushMetaPre (w : ℕ) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), (b, q_b)), (p_new, top_old)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      q_b ≤ p_new ∧
      p_new < maxFullSlabs N ∧
      (0 < q_b → top_old < maxFullSlabs N)

private theorem realizesBounded_compGmPushWriteOwner :
    RealizesBounded .exact compGmPushWriteOwnerProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompGmPushMetaPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, q_b⟩⟩, ⟨p_new, top_old⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, _, hp_lt, _⟩ := h
    have := gmSlabOwnerBIdx_lt hb_pos hp_lt
    have : gmSlabOwnerBIdx N p_new + 1 < globalMetaLen N := gmSlabOwnerSIdx_lt hb_pos hp_lt
    have : gmSlabOwnerBIdx N p_new + 2 < globalMetaLen N := gmSlabBelowIdx_lt hb_pos hp_lt
    have hp4 : gmSlabMetaBase N + (p_new + p_new + (p_new + p_new)) =
        gmSlabOwnerBIdx N p_new := by unfold gmSlabOwnerBIdx; omega
    simp only [cpGmSlabMetaBase_mk, hp4,
      StateTransitionSpec.clientState, runClient_state_writeCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabOwnerBIdx gmSlabMetaBase at *; omega)

private theorem realizesBounded_compGmPushWriteLinks :
    RealizesBounded .exact compGmPushWriteLinksProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompGmPushMetaPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, q_b⟩⟩, ⟨p_new, top_old⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, _, hp_lt, htop_lt⟩ := h
    simp only [cpGmSlabMetaBase_mk, cpDirSlabs_mk, cpGmSlabDirBase_mk,
      StateTransitionSpec.clientState] at *)
  all_goals try (
    have hc_pos : 0 < q_b := by assumption
    have habv_lt := gmSlabAboveIdx_lt hb_pos (htop_lt hc_pos)
    first
    | (refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
       simp only [cpN_mk]; unfold gmSlabAboveIdx at habv_lt; omega)
    | (refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
       unfold gmSlabAboveIdx gmSlabMetaBase at *; omega))
  all_goals (
    have hc_dir : q_b < dirSlabsPerBucket N := by assumption
    have hdir_lt := gmSlabDirIdx_lt hb_pos hb hc_dir
    first
    | (refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_⟩, ?_⟩
       · split_ifs <;> simp [runClient_state_writeCompGMGenProg, hfr]
       · simp only [cpN_mk]; unfold gmSlabDirIdx at hdir_lt; omega)
    | (refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
       unfold gmSlabDirIdx gmSlabDirBase at *; omega))

private def CompGmPushFinishPre (w : ℕ) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((cp, metaBase), (b, q_b)), p_new), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      q_b ≤ p_new ∧
      p_new < maxFullSlabs N

private theorem realizesBounded_compGmPushFinish :
    RealizesBounded .exact compGmPushFinishProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompGmPushFinishPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨b, q_b⟩⟩, p_new⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hq_le_p, hp_lt⟩ := h
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have htop_idx_lt : gmSlabTopIdx b < globalMetaLen N := gmSlabTopIdx_lt hb_pos hb
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hmax_le : maxFullSlabs N ≤ N := maxFullSlabs_le N
    simp only [StateTransitionSpec.clientState, runClient_state_writeCompGMGenProg] at *)
  all_goals try exact lt_of_le_of_lt (by omega) hU
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabTopIdx gmQIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabTopIdx gmQIdx at *; omega)

private def CompGmPushApplyPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), ((q_b, p_new), top_old)), s =>
    CompGmPushMetaPre w ((((cp, metaBase), (b, q_b)), (p_new, top_old))) s

private theorem realizesBounded_compGmPushApply :
    RealizesBounded .exact compGmPushApplyProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompGmPushApplyPre (fun _ _ => 0) := by
  have hown := realizesBounded_compGmPushWriteOwner
  have hlnk := realizesBounded_compGmPushWriteLinks
  have hfin := realizesBounded_compGmPushFinish
  realize
  · exact h
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨⟨q_b, p_new⟩, top_old⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hq_le_p, hp_lt, htop_lt⟩ := h)
  · refine ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_, hb_pos, hb, hq_le_p, hp_lt, htop_lt⟩
    simp [compGmPushWriteOwnerProg, StateTransitionSpec.clientState,
      runClient_state_writeCompGMGenProg, hfr]
  · refine ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_, hb_pos, hb, hq_le_p, hp_lt⟩
    dsimp only [compGmPushWriteOwnerProg, compGmPushWriteLinksProg, StateTransitionSpec.clientState]
    split_ifs <;> simp [runClient_state_writeCompGMGenProg, hfr]

private theorem realizesBounded_compGmPushRead :
    RealizesBounded .exact compGmPushReadProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      CompGmPushSlabPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hp_lt⟩ := h
    obtain ⟨hq_idx_lt, hq_eq, htop_idx_lt, htop_eq, h0_lt⟩ := gmPush_q_indices hb_pos hb
    simp only [hq_eq, htop_eq, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; omega⟩
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabTopIdx gmQIdx at *; omega)

theorem realizesBounded_compGmPushSlabGen :
    RealizesBounded .exact compGmPushSlabGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompGmPushSlabPre (fun _ _ => 0) := by
  have hrd := realizesBounded_compGmPushRead
  have happ := realizesBounded_compGmPushApply
  realize
  · exact h
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hp_lt⟩ := h
    have hq_le_p := q_le_nslabs_of_slabBijection hslab hb
    rw [clientState_compGmPushReadProg, clientResult_compGmPushReadProg hb_pos hb s]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hq_le_p, hp_lt,
      fun hq_pos => (hslab.top_lt hb hq_pos).trans hp_lt⟩

theorem validProg_compGmPushSlabGen {w : ℕ} {d : (CompParams × ℕ) × ℕ} {s : Memory.State}
    (h : CompGmPushSlabPre w d s) : ValidProg w 0 s (compGmPushSlabGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslab, hp_lt⟩ := h
  have mkEnv : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  obtain ⟨hq_lt, hq_eq, htop_lt, htop_eq, h0_lt⟩ := gmPush_q_indices hb_pos hb
  dsimp only [compGmPushSlabGenProg]
  refine validProg_bind (by
    rw [compGmPushReadProg, hq_eq, htop_eq]
    refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hq_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, h0_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    exact validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, htop_lt⟩) (validProg_pure _)) ?_
  rw [clientState_compGmPushReadProg, clientResult_compGmPushReadProg hb_pos hb s]
  set q_b := compGmAt metaBase U w N s.mem (gmQIdx b)
  set p_new := compGmAt metaBase U w N s.mem 0
  set top_old := compGmAt metaBase U w N s.mem (gmSlabTopIdx b)
  have hp4 : gmSlabMetaBase N + (p_new + p_new + (p_new + p_new)) = gmSlabOwnerBIdx N p_new := by
    unfold gmSlabOwnerBIdx; omega
  have ht4 : gmSlabMetaBase N + (top_old + top_old + (top_old + top_old)) + 3 =
      gmSlabAboveIdx N top_old := by unfold gmSlabAboveIdx; omega
  dsimp only [compGmPushApplyProg, compGmPushWriteOwnerProg, compGmPushWriteLinksProg,
    compGmPushFinishProg, cpGmSlabMetaBase_mk, cpDirSlabs_mk, cpGmSlabDirBase_mk]
  simp only [bind_assoc, hp4, ht4, hq_eq, htop_eq]
  refine validProg_writeCompGM_bind ⟨mkEnv s rfl, gmSlabOwnerBIdx_lt hb_pos hp_lt⟩ fun s1 hs1 =>
    validProg_writeCompGM_bind ⟨mkEnv s1 hs1, gmSlabOwnerSIdx_lt hb_pos hp_lt⟩ fun s2 hs2 =>
      validProg_writeCompGM_bind
        ⟨mkEnv s2 (hs2.trans hs1), gmSlabBelowIdx_lt hb_pos hp_lt⟩ fun s3 hs3 => ?_
  refine validProg_writeCompGM_ite_bind (0 < q_b)
    (fun hq_pos => ⟨mkEnv s3 (hs3.trans (hs2.trans hs1)),
      gmSlabAboveIdx_lt hb_pos ((hslab.top_lt hb hq_pos).trans hp_lt)⟩) fun s4 hs4 => ?_
  refine validProg_writeCompGM_ite_bind (q_b < dirSlabsPerBucket N)
    (fun hdir => ⟨mkEnv s4 (hs4.trans (hs3.trans (hs2.trans hs1))),
      gmSlabDirIdx_lt hb_pos hb hdir⟩) fun s5 hs5 => ?_
  have hs5_eq : s5.frontier = s.frontier := hs5.trans (hs4.trans (hs3.trans (hs2.trans hs1)))
  exact validProg_writeCompGM_bind ⟨mkEnv s5 hs5_eq, htop_lt⟩ fun s6 hs6 =>
    validProg_writeCompGM_bind ⟨mkEnv s6 (hs6.trans hs5_eq), hq_lt⟩ fun s7 hs7 =>
      validProg_writeCompGMGen ⟨mkEnv s7 (hs7.trans (hs6.trans hs5_eq)), h0_lt⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
