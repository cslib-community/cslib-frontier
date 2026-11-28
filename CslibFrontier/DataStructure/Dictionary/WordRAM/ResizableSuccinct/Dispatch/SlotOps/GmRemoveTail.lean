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
# Compacted `GlobalMeta` Tail Removal (`compRemoveTailGMOnlyGenProg`)

Implements `compRemoveTailGMOnlyGenProg` in `Memory.Prog` (`¬ReadsWidth`), proving its exact
`gmRemoveTail` state effect, `CompGmFrame` preservation, `RealizesBounded .exact`, and
`ValidProg w 0` admissibility.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compRemoveTailGMOnlyGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompRemoveTailGMOnlyPre`:
  metadata-only tail-descriptor removal subroutine and its precondition.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compRemoveTailGMOnlyGenProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.validProg_compRemoveTailGMOnlyGen`:
  exact `gmRemoveTail` effect and `ValidProg w 0` certificate.
* `realizesBounded_compRemoveTailGMOnlyGen`:
  `RealizesBounded .exact` certificate for `compRemoveTailGMOnlyGenProg`.
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

private def compRemoveTailReadGMProg : (CompParams × ℕ) × ℕ → Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | ((cp, metaBase), b) => do
    let r_idx := 4 + (b + b + b) + 1
    let r_b ← readCompGMGenProg ((cp, metaBase), r_idx)
    let ptr_del_idx := cpGmTailPtrBase cp + (b * cpTailCap cp + (r_b - 1))
    let t_del ← readCompGMGenProg ((cp, metaBase), ptr_del_idx)
    let n_tails ← readCompGMGenProg ((cp, metaBase), 1)
    let own_last_idx := cpGmTailOwnerBase cp + (n_tails - 1)
    let d_last ← readCompGMGenProg ((cp, metaBase), own_last_idx)
    pure ((r_b - 1, t_del), (n_tails - 1, d_last))

private theorem clientState_compRemoveTailReadGMProg (d : (CompParams × ℕ) × ℕ)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (compRemoveTailReadGMProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  unfold StateTransitionSpec.clientState; simp [compRemoveTailReadGMProg]

/-- Index bounds for the four `GlobalMeta` reads of `compRemoveTailReadGMProg`. -/
private theorem compRemoveTailReadGM_idx_lt {U w N metaBase b : ℕ} {s : Memory.State}
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (htail : TailBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
      (compGmAt metaBase U w N s.mem 1))
    (hr_pos : 1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b)) :
    gmRIdx b < globalMetaLen N ∧
      gmTailPtrBase N + (b * tailCapPerBucket N +
        (compGmAt metaBase U w N s.mem (gmRIdx b) - 1)) < globalMetaLen N ∧
      1 < globalMetaLen N ∧
      gmTailOwnerBase N + (compGmAt metaBase U w N s.mem 1 - 1) < globalMetaLen N := by
  have hr_le_nt := r_le_ntails_of_tailBijection htail hb
  exact ⟨gmRIdx_lt hb_pos hb,
    gmTailPtrIdx_lt hb_pos hb (lt_of_lt_of_le (by omega) (htail.r_le b hb)),
    by unfold globalMetaLen; omega,
    gmTailOwnerIdx_lt hb_pos (lt_of_lt_of_le (by omega) htail.ntails_le)⟩

private theorem clientResult_compRemoveTailReadGMProg {U V w N metaBase b : ℕ}
    {s : Memory.State} (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (htail : TailBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
      (compGmAt metaBase U w N s.mem 1))
    (hr_pos : 1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b)) :
    (Memory.spec 0).clientResult s
        (compRemoveTailReadGMProg ((mkCompParams U V w N, metaBase), b)) =
      ((compGmAt metaBase U w N s.mem (gmRIdx b) - 1,
        compGmAt metaBase U w N s.mem
          (gmTailPtrIdx N b (compGmAt metaBase U w N s.mem (gmRIdx b) - 1))),
       (compGmAt metaBase U w N s.mem 1 - 1,
        compGmAt metaBase U w N s.mem
          (gmTailOwnerIdx N (compGmAt metaBase U w N s.mem 1 - 1)))) := by
  obtain ⟨hr_idx_lt, hptr_del_lt, h1_lt, hown_last_lt⟩ :=
    compRemoveTailReadGM_idx_lt hb_pos hb htail hr_pos
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  dsimp only [compRemoveTailReadGMProg, succinct_param_simps]
  simp only [client_simps, StateTransitionSpec.clientState, hr_eq,
    clientResult_readCompGMGenProg hr_idx_lt, runClient_state_readCompGMGenProg,
    clientResult_readCompGMGenProg hptr_del_lt, clientResult_readCompGMGenProg h1_lt,
    clientResult_readCompGMGenProg hown_last_lt]
  rfl

private def compRemoveTailWriteGMProg :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | (((cp, metaBase), b), ((r_del, t_del), (t_last, d_last))) => do
    let r_idx := 4 + (b + b + b) + 1
    let ptr_last_idx := cpGmTailPtrBase cp + d_last
    let own_del_idx := cpGmTailOwnerBase cp + t_del
    writeCompGMGenProg (((cp, metaBase), ptr_last_idx), t_del)
    writeCompGMGenProg (((cp, metaBase), own_del_idx), d_last)
    writeCompGMGenProg (((cp, metaBase), r_idx), r_del)
    writeCompGMGenProg (((cp, metaBase), 1), t_last)

/-- Remove the last tail descriptor of bucket `b` in compacted `GlobalMeta` (`gmRemoveTail`)
without touching item arrays (`¬ReadsWidth`). -/
def compRemoveTailGMOnlyGenProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, metaBase), b) => do
    let info ← compRemoveTailReadGMProg ((cp, metaBase), b)
    compRemoveTailWriteGMProg (((cp, metaBase), b), info)

@[simp] theorem memoryCost_compRemoveTailGMOnlyGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compRemoveTailGMOnlyGenProg d) s = 24 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  simp [compRemoveTailGMOnlyGenProg, compRemoveTailReadGMProg, compRemoveTailWriteGMProg]

theorem compRemoveTailGMOnlyGenProg_effect {metaBase itemBase U V w N m_items b : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) (s : Memory.State)
    (htail : TailBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
      (compGmAt metaBase U w N s.mem 1))
    (hr_pos : 1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b)) :
    let s' := (Memory.spec 0).clientState s
      (compRemoveTailGMOnlyGenProg ((mkCompParams U V w N, metaBase), b))
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = gmRemoveTail N (compGmAt metaBase U w N s.mem) b := by
  intro s'
  have hnt_le : compGmAt metaBase U w N s.mem 1 ≤ N := htail.ntails_le.trans (maxTailItems_le N)
  let r_del := compGmAt metaBase U w N s.mem (gmRIdx b) - 1
  let t_del := compGmAt metaBase U w N s.mem (gmTailPtrIdx N b r_del)
  let t_last := compGmAt metaBase U w N s.mem 1 - 1
  let d_last := compGmAt metaBase U w N s.mem (gmTailOwnerIdx N t_last)
  have hr_del_lt : r_del < compGmAt metaBase U w N s.mem (gmRIdx b) := by
    dsimp only [r_del]; omega
  have ht_del_lt : t_del < compGmAt metaBase U w N s.mem 1 := htail.ptr_lt b hb r_del hr_del_lt
  have ht_last_lt : t_last < compGmAt metaBase U w N s.mem 1 := by
    dsimp only [t_last]; omega
  have hd_last_lt : d_last < maxTailItems N := htail.owner_lt_maxTailItems ht_last_lt
  obtain ⟨hr_idx_lt, hptr_del_lt, h1_lt, -⟩ := compRemoveTailReadGM_idx_lt hb_pos hb htail hr_pos
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  have hptr_last_lt : gmTailPtrBase N + d_last < globalMetaLen N :=
    gmTailPtrFlatIdx_lt hb_pos hd_last_lt
  have hown_del_lt : gmTailOwnerBase N + t_del < globalMetaLen N :=
    gmTailOwnerIdx_lt hb_pos (lt_of_lt_of_le ht_del_lt htail.ntails_le)
  have ht_del_val : t_del < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_n_max (by dsimp only [t_del] at *; omega)
  have hd_last_val : d_last < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos
      (by unfold gmTailPtrBase at hptr_last_lt; omega)
  have hr_del_val : r_del < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos
      (by unfold gmTailPtrBase gmSlabDirBase at hptr_del_lt; dsimp only [r_del]; omega)
  have ht_last_val : t_last < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_n_max (by dsimp only [t_last]; omega)
  have hread_st := clientState_compRemoveTailReadGMProg ((mkCompParams U V w N, metaBase), b) s
  have hread_res : (Memory.spec 0).clientResult s
      (compRemoveTailReadGMProg ((mkCompParams U V w N, metaBase), b)) =
      ((r_del, t_del), (t_last, d_last)) :=
    clientResult_compRemoveTailReadGMProg hb_pos hb htail hr_pos
  have hst : s' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s
            (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
              gmTailPtrBase N + d_last), t_del)))
          (writeCompGMGenProg (((mkCompParams U V w N, metaBase),
            gmTailOwnerBase N + t_del), d_last)))
        (writeCompGMGenProg (((mkCompParams U V w N, metaBase), gmRIdx b), r_del)))
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase), 1), t_last)) := by
    change (Memory.spec 0).clientState s _ = _
    dsimp only [compRemoveTailGMOnlyGenProg]
    rw [StateTransitionSpec.clientState_bind, hread_st, hread_res]
    dsimp only [compRemoveTailWriteGMProg, succinct_param_simps]
    rw [hr_eq]
    repeat rw [StateTransitionSpec.clientState_bind]
  obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hptr_last_lt
    ht_del_val s
  obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hown_del_lt
    hd_last_val _
  obtain ⟨hf3, hg3⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hr_idx_lt
    hr_del_val _
  obtain ⟨hf4, hg4⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem h1_lt
    ht_last_val _
  rw [hst]
  refine ⟨hf1.trans (hf2.trans (hf3.trans hf4)), ?_⟩
  rw [hg4, hg3, hg2, hg1]; rfl

/-- Precondition for removing only the tail descriptor in global metadata. -/
@[expose] def CompRemoveTailGMOnlyPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      TailBijection N (compGmAt metaBase U w N s.mem)
        (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
        (compGmAt metaBase U w N s.mem 1) ∧
      1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b)

private theorem realizesBounded_compRemoveTailReadGM :
    RealizesBounded .exact compRemoveTailReadGMProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      CompRemoveTailGMOnlyPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_pos⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    have hr_le_nt := r_le_ntails_of_tailBijection htail hb
    obtain ⟨hr_idx_lt, hptr_del_lt, h1_lt, hown_last_lt⟩ :=
      compRemoveTailReadGM_idx_lt hb_pos hb htail hr_pos
    have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
    simp only [succinct_param_simps, hr_eq, StateTransitionSpec.clientState,
      runClient_state_readCompGMGenProg] at *
    try rw [clientResult_readCompGMGenProg hr_idx_lt] at *
    try rw [clientResult_readCompGMGenProg h1_lt] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmRIdx at *
    omega)
  all_goals try omega
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmTailPtrBase at *
    unfold gmTailOwnerBase at *
    unfold gmRIdx at *
    omega)

private def CompRemoveTailWriteGMPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.State → Prop
  | (((cp, metaBase), b), ((_r_del, t_del), (_t_last, d_last))), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      t_del < maxTailItems N ∧
      d_last < maxTailItems N

private theorem realizesBounded_compRemoveTailWriteGM :
    RealizesBounded .exact compRemoveTailWriteGMProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      CompRemoveTailWriteGMPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨⟨r_del, t_del⟩, ⟨t_last, d_last⟩⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, ht_del_lt, hd_last_lt⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hptr_last_lt := gmTailPtrFlatIdx_lt hb_pos hd_last_lt
    have hown_del_lt := gmTailOwnerIdx_lt hb_pos ht_del_lt
    try simp only [cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk,
      StateTransitionSpec.clientState, runClient_state_writeCompGMGenProg] at *)
  all_goals try exact fits_const_of_offCompItems hfit_meta (by decide)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmTailPtrFlatIdx gmTailOwnerIdx gmRIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmTailPtrFlatIdx gmTailPtrBase gmTailOwnerIdx gmTailOwnerBase gmRIdx at *
    omega)

theorem realizesBounded_compRemoveTailGMOnlyGen :
    RealizesBounded .exact compRemoveTailGMOnlyGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CompRemoveTailGMOnlyPre (fun _ _ => 0) := by
  have hrd := realizesBounded_compRemoveTailReadGM
  have hwr := realizesBounded_compRemoveTailWriteGM
  realize
  · exact h
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_pos⟩ := h
    have hr_del_lt : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 <
        compGmAt metaBase U w N s.mem (gmRIdx b) := by omega
    have hr_le_nt := r_le_ntails_of_tailBijection htail hb
    have ht_last_lt : compGmAt metaBase U w N s.mem 1 - 1 < compGmAt metaBase U w N s.mem 1 := by
      omega
    rw [clientState_compRemoveTailReadGMProg,
      clientResult_compRemoveTailReadGMProg hb_pos hb htail hr_pos]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb,
      lt_of_lt_of_le (htail.ptr_lt b hb _ hr_del_lt) htail.ntails_le,
      htail.owner_lt_maxTailItems ht_last_lt⟩

theorem validProg_compRemoveTailGMOnlyGen {w : ℕ} {d : (CompParams × ℕ) × ℕ} {s : Memory.State}
    (h : CompRemoveTailGMOnlyPre w d s) : ValidProg w 0 s (compRemoveTailGMOnlyGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_pos⟩ := h
  have mkEnv : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  have hr_del_lt : compGmAt metaBase U w N s.mem (gmRIdx b) - 1 <
      compGmAt metaBase U w N s.mem (gmRIdx b) := by omega
  obtain ⟨hr_idx_lt, hptr_del_lt, h1_lt, hown_last_lt⟩ :=
    compRemoveTailReadGM_idx_lt hb_pos hb htail hr_pos
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  have hr_le_nt := r_le_ntails_of_tailBijection htail hb
  have ht_last_lt : compGmAt metaBase U w N s.mem 1 - 1 < compGmAt metaBase U w N s.mem 1 := by
    omega
  have hptr_last_lt := gmTailPtrFlatIdx_lt hb_pos (htail.owner_lt_maxTailItems ht_last_lt)
  have hown_del_lt :=
    gmTailOwnerIdx_lt hb_pos (lt_of_lt_of_le (htail.ptr_lt b hb _ hr_del_lt) htail.ntails_le)
  have hrd_v : ValidProg w 0 s
      (compRemoveTailReadGMProg ((mkCompParams U V w N, metaBase), b)) := by
    dsimp only [compRemoveTailReadGMProg, succinct_param_simps]
    rw [hr_eq]
    refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hr_idx_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hr_idx_lt]
    refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hptr_del_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, h1_lt⟩) ?_
    rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg h1_lt]
    exact validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hown_last_lt⟩) (validProg_pure _)
  dsimp only [compRemoveTailGMOnlyGenProg]
  refine validProg_bind hrd_v ?_
  rw [clientState_compRemoveTailReadGMProg,
    clientResult_compRemoveTailReadGMProg hb_pos hb htail hr_pos]
  dsimp only [compRemoveTailWriteGMProg, succinct_param_simps]
  rw [hr_eq]
  exact validProg_writeCompGM_bind ⟨mkEnv s rfl, hptr_last_lt⟩ fun s1 hs1 =>
    validProg_writeCompGM_bind ⟨mkEnv s1 hs1, hown_del_lt⟩ fun s2 hs2 =>
      validProg_writeCompGM_bind ⟨mkEnv s2 (hs2.trans hs1), hr_idx_lt⟩ fun s3 hs3 =>
        validProg_writeCompGMGen ⟨mkEnv s3 (hs3.trans (hs2.trans hs1)), h1_lt⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
