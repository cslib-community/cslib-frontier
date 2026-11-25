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
# Compacted `GlobalMeta` Tail Append (`compAppendTailGMGenProg`)

Implements `compAppendTailGMGenProg` in `Memory.Prog` (`¬ReadsWidth`), proving its exact
`gmAppendTail` state effect, `CompGmFrame` preservation, `RealizesBounded .exact`, and
`ValidProg w 0` admissibility.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compAppendTailGMGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompAppendTailGMPre`:
  tail-descriptor append subroutine in compacted `GlobalMeta` and its precondition.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compAppendTailGMGenProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_compAppendTailGMGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.validProg_compAppendTailGMGen`:
  exact `gmAppendTail` effect, `RealizesBounded .exact`, and `ValidProg w 0` certificate.
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

private def compAppendTailReadGMProg : (CompParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, metaBase), b) => do
    let r_idx := 4 + (b + b + b) + 1
    let r_b ← readCompGMGenProg ((cp, metaBase), r_idx)
    let t_new ← readCompGMGenProg ((cp, metaBase), 1)
    pure (r_b, t_new)

private theorem clientState_compAppendTailReadGMProg (d : (CompParams × ℕ) × ℕ)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (compAppendTailReadGMProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  unfold StateTransitionSpec.clientState; simp [compAppendTailReadGMProg]

private theorem clientResult_compAppendTailReadGMProg {U V w N metaBase b : ℕ}
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (compAppendTailReadGMProg ((mkCompParams U V w N, metaBase), b)) =
      (compGmAt metaBase U w N s.mem (gmRIdx b), compGmAt metaBase U w N s.mem 1) := by
  have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  dsimp only [compAppendTailReadGMProg]
  rw [hr_eq, StateTransitionSpec.clientResult_bind, clientResult_readCompGMGenProg hr_idx_lt,
    clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind,
    clientResult_readCompGMGenProg h1_lt, clientState_readCompGMGenProg]
  rfl

private def compAppendTailWrite1Prog :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, metaBase), b), (r_b, t_new)) => do
    let off_b := b * cpTailCap cp + r_b
    let ptr_idx := cpGmTailPtrBase cp + off_b
    let own_idx := cpGmTailOwnerBase cp + t_new
    writeCompGMGenProg (((cp, metaBase), ptr_idx), t_new)
    writeCompGMGenProg (((cp, metaBase), own_idx), off_b)

private def compAppendTailWrite2Prog :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | (((cp, metaBase), b), (r_b, t_new)) => do
    let r_idx := 4 + (b + b + b) + 1
    writeCompGMGenProg (((cp, metaBase), r_idx), r_b + 1)
    writeCompGMGenProg (((cp, metaBase), 1), t_new + 1)
    pure t_new

private def compAppendTailWriteGMProg :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | (((cp, metaBase), b), info) => do
    compAppendTailWrite1Prog ((((cp, metaBase), b), info))
    compAppendTailWrite2Prog ((((cp, metaBase), b), info))

private def CompAppendTailWriteGMPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (r_b, t_new)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      r_b < tailCapPerBucket N ∧
      t_new < maxTailItems N

private theorem realizesBounded_compAppendTailWrite1 :
    RealizesBounded .exact compAppendTailWrite1Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompAppendTailWriteGMPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨r_b, t_new⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hr_lt, ht_cap⟩ := h
    have hptr_lt := gmTailPtrIdx_lt hb_pos hb hr_lt
    have hown_lt := gmTailOwnerIdx_lt hb_pos ht_cap
    simp only [cpTailCap_mk, cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk,
      StateTransitionSpec.clientState, runClient_state_writeCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmTailPtrIdx gmTailPtrFlatIdx gmTailOwnerIdx at *; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    have := tailCapPerBucket_le_globalMetaLen hb_pos
    unfold gmTailPtrIdx gmTailPtrFlatIdx gmTailPtrBase gmTailOwnerIdx gmTailOwnerBase at *
    omega)

private theorem realizesBounded_compAppendTailWrite2 :
    RealizesBounded .exact compAppendTailWrite2Prog
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      CompAppendTailWriteGMPre (fun _ _ => 0) := by
  have hwgm := realizesBounded_writeCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨r_b, t_new⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hr_lt, ht_cap⟩ := h
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    have hmax_le : maxTailItems N ≤ N := maxTailItems_le N
    try simp only [StateTransitionSpec.clientState, runClient_state_writeCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmRIdx at *; omega)
  all_goals try exact lt_of_le_of_lt (by omega) hU
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    have := tailCapPerBucket_le_globalMetaLen hb_pos
    unfold gmRIdx at *; omega)

private theorem realizesBounded_compAppendTailWriteGM :
    RealizesBounded .exact compAppendTailWriteGMProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      CompAppendTailWriteGMPre (fun _ _ => 0) := by
  have hw1 := realizesBounded_compAppendTailWrite1
  have hw2 := realizesBounded_compAppendTailWrite2
  realize
  · exact h
  · rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨r_b, t_new⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hr_lt, ht_cap⟩ := h
    refine ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, ?_, hb_pos, hb, hr_lt, ht_cap⟩
    dsimp only [compAppendTailWrite1Prog, StateTransitionSpec.clientState]
    simp [runClient_state_writeCompGMGenProg, hfr]

/-- Append one tail descriptor to bucket `b` in compacted `GlobalMeta` (`gmAppendTail`), returning
`t_new = gm 1` (`¬ReadsWidth`). -/
def compAppendTailGMGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), b) => do
    let info ← compAppendTailReadGMProg ((cp, metaBase), b)
    compAppendTailWriteGMProg (((cp, metaBase), b), info)

@[simp] theorem memoryCost_compAppendTailGMGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compAppendTailGMGenProg d) s = 20 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  simp [compAppendTailGMGenProg, compAppendTailReadGMProg, compAppendTailWriteGMProg,
    compAppendTailWrite1Prog, compAppendTailWrite2Prog]

theorem compAppendTailGMGenProg_effect {metaBase itemBase U V w N m_items b : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) (s : Memory.State)
    (htail : TailBijection N (compGmAt metaBase U w N s.mem)
      (fun b' => compGmAt metaBase U w N s.mem (gmRIdx b'))
      (compGmAt metaBase U w N s.mem 1))
    (hr_lt : compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N) :
    let s' := (Memory.spec 0).clientState s
      (compAppendTailGMGenProg ((mkCompParams U V w N, metaBase), b))
    (Memory.spec 0).clientResult s
      (compAppendTailGMGenProg ((mkCompParams U V w N, metaBase), b)) =
      compGmAt metaBase U w N s.mem 1 ∧
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = gmAppendTail N (compGmAt metaBase U w N s.mem) b := by
  intro s'
  set gm := compGmAt metaBase U w N s.mem
  have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  have hptr_lt : gmTailPtrBase N + (b * tailCapPerBucket N + gm (gmRIdx b)) < globalMetaLen N :=
    gmTailPtrIdx_lt hb_pos hb hr_lt
  have ht_cap : gm 1 < maxTailItems N := ntails_lt_maxTailItems_of_r_lt hb hr_lt htail
  have := maxTailItems_le N
  have hown_lt : gmTailOwnerBase N + gm 1 < globalMetaLen N := gmTailOwnerIdx_lt hb_pos ht_cap
  have ht_val : gm 1 < 2 ^ globalPtrBits N := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hd_val : b * tailCapPerBucket N + gm (gmRIdx b) < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos (by unfold gmTailPtrBase at hptr_lt; omega)
  have hr1_val : gm (gmRIdx b) + 1 < 2 ^ globalPtrBits N :=
    lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos
      (by unfold gmTailPtrBase gmSlabDirBase at hptr_lt; omega)
  have ht1_val : gm 1 + 1 < 2 ^ globalPtrBits N := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hread := clientResult_compAppendTailReadGMProg
    (U := U) (V := V) (w := w) (metaBase := metaBase) hb_pos hb s
  refine ⟨?_, ?_⟩
  · rw [compAppendTailGMGenProg, StateTransitionSpec.clientResult_bind,
      clientState_compAppendTailReadGMProg, hread]
    simp only [compAppendTailWriteGMProg, compAppendTailWrite1Prog, compAppendTailWrite2Prog,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
    rfl
  dsimp only [s', compAppendTailGMGenProg]
  rw [StateTransitionSpec.clientState_bind, clientState_compAppendTailReadGMProg, hread]
  dsimp only [compAppendTailWriteGMProg, compAppendTailWrite1Prog, compAppendTailWrite2Prog,
    cpTailCap_mk, cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk]
  rw [hr_eq]
  repeat rw [StateTransitionSpec.clientState_bind]
  rw [StateTransitionSpec.clientState_pure]
  obtain ⟨hf1, hg1⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hptr_lt ht_val s
  obtain ⟨hf2, hg2⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hown_lt hd_val _
  obtain ⟨hf3, hg3⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem hr_idx_lt
    hr1_val _
  obtain ⟨hf4, hg4⟩ := compGmFrame_writeCompGMGenProg (m_items := m_items) hw hitem h1_lt ht1_val _
  refine ⟨hf1.trans (hf2.trans (hf3.trans hf4)), ?_⟩
  rw [hg4, hg3, hg2, hg1]; rfl

/-- Precondition for appending to the tail of global metadata. -/
@[expose] def CompAppendTailGMPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
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
      compGmAt metaBase U w N s.mem (gmRIdx b) < tailCapPerBucket N

private theorem realizesBounded_compAppendTailReadGM :
    RealizesBounded .exact compAppendTailReadGMProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ × ℕ))
      CompAppendTailGMPre (fun _ _ => 0) := by
  have hrgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_lt⟩ := h
    have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
    have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
    simp only [hr_eq, StateTransitionSpec.clientState, runClient_state_readCompGMGenProg] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; omega⟩
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmRIdx at *; omega)

theorem realizesBounded_compAppendTailGMGen :
    RealizesBounded .exact compAppendTailGMGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompAppendTailGMPre (fun _ _ => 0) := by
  have hrd := realizesBounded_compAppendTailReadGM
  have hwr := realizesBounded_compAppendTailWriteGM
  realize
  · exact h
  · rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_lt⟩ := h
    have ht_cap : compGmAt metaBase U w N s.mem 1 < maxTailItems N :=
      ntails_lt_maxTailItems_of_r_lt hb hr_lt htail
    rw [clientState_compAppendTailReadGMProg, clientResult_compAppendTailReadGMProg hb_pos hb s]
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hr_lt, ht_cap⟩

theorem validProg_compAppendTailGMGen {w : ℕ} {d : (CompParams × ℕ) × ℕ} {s : Memory.State}
    (h : CompAppendTailGMPre w d s) : ValidProg w 0 s (compAppendTailGMGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, htail, hr_lt⟩ := h
  have mkEnv : ∀ s' : Memory.State, s'.frontier = s.frontier →
      CompMetaEnv w (mkCompParams U V w N) metaBase s' :=
    fun s' hs' => ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hs' ▸ hfr⟩
  have hr_idx_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hr_eq : 4 + (b + b + b) + 1 = gmRIdx b := by unfold gmRIdx; omega
  have h1_lt : 1 < globalMetaLen N := by unfold globalMetaLen; omega
  have hptr_lt := gmTailPtrIdx_lt hb_pos hb hr_lt
  have hown_lt := gmTailOwnerIdx_lt hb_pos (ntails_lt_maxTailItems_of_r_lt hb hr_lt htail)
  dsimp only [compAppendTailGMGenProg]
  refine validProg_bind ?_ ?_
  · dsimp only [compAppendTailReadGMProg]
    rw [hr_eq]
    refine validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, hr_idx_lt⟩) ?_
    rw [clientState_readCompGMGenProg]
    exact validProg_bind (validProg_readCompGMGen ⟨mkEnv s rfl, h1_lt⟩) (validProg_pure _)
  rw [clientState_compAppendTailReadGMProg, clientResult_compAppendTailReadGMProg hb_pos hb s]
  dsimp only [compAppendTailWriteGMProg, compAppendTailWrite1Prog, compAppendTailWrite2Prog,
    cpTailCap_mk, cpGmTailPtrBase_mk, cpGmTailOwnerBase_mk]
  simp only [bind_assoc, hr_eq]
  exact validProg_writeCompGM_bind ⟨mkEnv s rfl, hptr_lt⟩ fun s1 hs1 =>
    validProg_writeCompGM_bind ⟨mkEnv s1 hs1, hown_lt⟩ fun s2 hs2 =>
      validProg_writeCompGM_bind ⟨mkEnv s2 (hs2.trans hs1), hr_idx_lt⟩ fun s3 hs3 =>
        validProg_writeCompGM_bind ⟨mkEnv s3 (hs3.trans (hs2.trans hs1)), h1_lt⟩ fun _ _ =>
          validProg_pure _

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
