/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.Internal

/-!
# Compacted Phase-2 Overflow Resolvers (`RealizesBounded .exact`)

Implements `compResolveOvfStepGenProg` and `compInitOvfSearchGenProg` in `Memory.Prog`
(`¬ReadsWidth`), matching fixed-capacity `Succinct.resolveOvfStepProg` and
`Succinct.initOvfSearchProg` along with `RealizesBounded .exact` and `ValidProg w 0` certificates.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compResolveOvfStepGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompResolveOvfStepPre`:
  single-step Phase-2 overflow slot resolver on compacted metadata.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compInitOvfSearchGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompInitOvfSearchPre`:
  Phase-2 overflow `(p_init, fuel)` initializer on compacted metadata.

## Main results

* `clientResult_compResolveOvfStepGenProg_eq`,
  `realizesBounded_compResolveOvfStepGen`, `validProg_compResolveOvfStepGen`:
  fixed-capacity agreement, `RealizesBounded .exact`, and `ValidProg w 0` for
  `compResolveOvfStepGenProg`.
* `clientResult_compInitOvfSearchGenProg_eq`,
  `realizesBounded_compInitOvfSearchGen`, `validProg_compInitOvfSearchGen`:
  fixed-capacity agreement, `RealizesBounded .exact`, and `ValidProg w 0` for
  `compInitOvfSearchGenProg`.
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
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

private def compResolveOvfAdvanceGenProg :
    ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (((cp, metaBase), (j1, qK)), (phys, p_cur)) =>
    if j1 < qK then do
      let p2 := p_cur + p_cur
      let abv_idx := cpGmSlabMetaBase cp + (p2 + p2) + 3
      let p_next ← readCompGMGenProg ((cp, metaBase), abv_idx)
      pure (phys, p_next)
    else
      pure (phys, p_cur)

private def compResolveOvfInSlabGenProg :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (((cp, metaBase), qK), (j, p_cur)) =>
    let off := cpSlabSizeSubOne cp - j % cpSlabSize cp
    let phys := p_cur * cpSlabSize cp + off
    if off = 0 then
      compResolveOvfAdvanceGenProg ((((cp, metaBase), (j + 1, qK)), (phys, p_cur)))
    else
      pure (phys, p_cur)

/-- Single-step overflow slot resolver on compacted metadata (`¬ReadsWidth`). -/
def compResolveOvfStepGenProg : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (((cp, metaBase), b), (j, p_cur)) => do
    let b3 := b + b + b
    let q_idx := 4 + b3
    let q_b ← readCompGMGenProg ((cp, metaBase), q_idx)
    let qK := q_b * cpSlabSize cp
    if j < qK then
      compResolveOvfInSlabGenProg (((cp, metaBase), qK), (j, p_cur))
    else do
      let r := j - qK
      let t_idx := cpGmTailPtrBase cp + (b * cpTailCap cp + r)
      let t ← readCompGMGenProg ((cp, metaBase), t_idx)
      pure (cpNSubOne cp - t, p_cur)

theorem clientState_compResolveOvfStepGenProg
    (d : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (compResolveOvfStepGenProg d) = s := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨j, p_cur⟩⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compResolveOvfStepGenProg, compResolveOvfInSlabGenProg, compResolveOvfAdvanceGenProg]
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    runClient_state_readCompGMGenProg]
  split_ifs <;> simp

@[simp] theorem runClient_state_compResolveOvfStepGenProg
    (d : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compResolveOvfStepGenProg d))) = s :=
  clientState_compResolveOvfStepGenProg d s

theorem memoryCost_compResolveOvfStepGenProg_pos
    (d : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (compResolveOvfStepGenProg d) s := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨j, p_cur⟩⟩
  dsimp only [compResolveOvfStepGenProg]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg]
  omega

theorem memoryCost_compResolveOvfStepGenProg_le
    (d : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (compResolveOvfStepGenProg d) s ≤ 4 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨j, p_cur⟩⟩
  dsimp only [compResolveOvfStepGenProg, compResolveOvfInSlabGenProg, compResolveOvfAdvanceGenProg]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg]
  split_ifs <;> simp

/-- Under `compGmAt = gmAt`, `compResolveOvfStepGenProg` returns the exact same `(phys, p_next)`
pair as `Succinct.resolveOvfStepProg` on `s_fix`. -/
theorem clientResult_compResolveOvfStepGenProg_eq {U V w w₀ N h_space metaBase b j p_cur : ℕ}
    {s_fix s : Memory.State}
    (hgm_eq : compGmAt metaBase U w N s.mem = gmAt 0 U V w₀ N h_space s_fix.mem)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hj_bc : j < bCount N (compGmAt metaBase U w N s.mem) b)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hp : j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N →
      p_cur = slabPtrOf N (compGmAt metaBase U w N s.mem) b (j / slabSize N)) :
    (Memory.spec 0).clientResult s
        (compResolveOvfStepGenProg (((mkCompParams U V w N, metaBase), b), (j, p_cur))) =
      (Memory.spec 0).clientResult s_fix
        (resolveOvfStepProg U V w₀ N h_space ((0, b), (j, p_cur))) := by
  have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hq_eq1 : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  have hq_eq2 : 4 + 3 * b = gmQIdx b := rfl
  simp only [compResolveOvfStepGenProg, compResolveOvfInSlabGenProg, compResolveOvfAdvanceGenProg,
    resolveOvfStepProg, ovfBucketBase, ovfBucketIdx, ovfResolveIdx, ovfResolveSlabPtr,
    cpSlabSize_mk, cpSlabSizeSubOne_mk, cpGmSlabMetaBase_mk, cpGmTailPtrBase_mk,
    cpTailCap_mk, cpNSubOne_mk, pure_bind, hq_eq1, hq_eq2]
  rw [prog_clientResult_bind, clientResult_readCompGMGenProg hq_lt,
    clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind, clientState_readGMProg,
    clientResult_readGMProg s_fix hq_lt, ← hgm_eq]
  by_cases hj_slab : j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N
  · simp only [hj_slab, ↓reduceIte]
    by_cases hoff : slabSize N - 1 - j % slabSize N = 0
    · simp only [hoff, ↓reduceIte]
      by_cases hj1_slab : j + 1 < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N
      · have hp_eq := hp hj_slab
        have hs_lt : j / slabSize N < compGmAt metaBase U w N s.mem (gmQIdx b) :=
          (Nat.div_lt_iff_lt_mul (slabSize_pos N)).2 hj_slab
        have hp_lt_max : p_cur < maxFullSlabs N :=
          hp_eq ▸ (hslot.multi_slab hb_pos).ptr_lt_maxFullSlabs hb hs_lt
        have habv_lt : gmSlabMetaBase N + 4 * p_cur + 3 < globalMetaLen N :=
          gmSlabAboveIdx_lt hb_pos hp_lt_max
        have habv_eq : gmSlabMetaBase N + (p_cur + p_cur + (p_cur + p_cur)) + 3 =
            gmSlabMetaBase N + 4 * p_cur + 3 := by omega
        simp only [hj1_slab, ↓reduceIte, habv_eq]
        rw [prog_clientResult_bind, clientResult_readCompGMGenProg habv_lt,
          clientState_readCompGMGenProg, prog_clientResult_pure,
          StateTransitionSpec.clientResult_bind, clientState_readGMProg,
          clientResult_readGMProg s_fix habv_lt, ← hgm_eq]
        rfl
      · simp only [hj1_slab, ↓reduceIte]; rfl
    · simp only [hoff, ↓reduceIte]; rfl
  · simp only [hj_slab, ↓reduceIte]
    obtain ⟨-, hr_cap⟩ := hslot.tailOffset_lt hb_pos hb hj_bc hj_slab
    have hptr_lt : gmTailPtrBase N +
        (b * tailCapPerBucket N + (j - compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N)) <
        globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_cap
    rw [prog_clientResult_bind, clientResult_readCompGMGenProg hptr_lt,
      clientState_readCompGMGenProg, prog_clientResult_pure,
      StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s_fix hptr_lt, ← hgm_eq]
    rfl

private def CompResolveOvfAdvancePre (w : ℕ) :
    ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), (_j1, _qK)), (_phys, p_cur)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      p_cur < maxFullSlabs N

private theorem realizesBounded_compResolveOvfAdvanceGen :
    RealizesBounded .exact compResolveOvfAdvanceGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompResolveOvfAdvancePre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, ⟨j1, qK⟩⟩, ⟨phys, p_cur⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_lt_max⟩ := h
    have habv_lt := gmSlabAboveIdx_lt hb_pos hp_lt_max
    simp only [cpGmSlabMetaBase_mk] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabAboveIdx at habv_lt; omega)
  refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
  unfold gmSlabAboveIdx gmSlabMetaBase at *
  omega

private def CompResolveOvfInSlabPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), qK), (j, p_cur)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      qK ≤ N ∧
      j < qK ∧
      p_cur < maxFullSlabs N ∧
      (p_cur + 1) * slabSize N ≤ N

private theorem realizesBounded_compResolveOvfInSlabGen :
    RealizesBounded .exact compResolveOvfInSlabGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompResolveOvfInSlabPre (fun _ _ => 0) := by
  have hadv := realizesBounded_compResolveOvfAdvanceGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, qK⟩, ⟨j, p_cur⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hqK_le, hj_lt, hp_lt_max, hpK_le⟩ := h
    have hK : 0 < slabSize N := slabSize_pos N
    have hmod_lt := Nat.mod_lt j hK
    simp only [cpSlabSize_mk, cpSlabSizeSubOne_mk] at *)
  all_goals try exact hK.ne'
  all_goals try exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hp_lt_max⟩
  all_goals try omega
  all_goals (rw [Nat.add_one_mul] at hpK_le; exact lt_of_le_of_lt (by omega) hU)

/-- Precondition for stepping overflow resolution. -/
@[expose] def CompResolveOvfStepPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (j, p_cur)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      j < bCount N (compGmAt metaBase U w N s.mem) b ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      (j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N →
        p_cur = slabPtrOf N (compGmAt metaBase U w N s.mem) b (j / slabSize N))

theorem realizesBounded_compResolveOvfStepGen :
    RealizesBounded .exact compResolveOvfStepGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompResolveOvfStepPre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  have hins := realizesBounded_compResolveOvfInSlabGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨j, p_cur⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hj_bc, hslot, hp⟩ := h
    have hb_ne : bucketBits N ≠ 0 := hb_pos.ne'
    have hK : 0 < slabSize N := slabSize_pos N
    have hfit_meta : Fits w (metaBase + offCompItems U w N) := lt_of_le_of_lt hfr hmem.1
    have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have hbc_le : bCount N (compGmAt metaBase U w N s.mem) b ≤ N := bCount_le_n_max hslot b
    unfold bCount at hbc_le; simp only [hb_ne, ↓reduceIte, hb] at hbc_le
    simp only [cpSlabSize_mk, cpGmTailPtrBase_mk, cpTailCap_mk, cpNSubOne_mk, hq_eq,
      StateTransitionSpec.clientState, clientResult_readCompGMGenProg hq_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hq_lt⟩
  all_goals try (
    have hc_pos : j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N := by assumption
    have hp_eq := hp hc_pos
    have hs_lt : j / slabSize N < compGmAt metaBase U w N s.mem (gmQIdx b) :=
      (Nat.div_lt_iff_lt_mul hK).2 hc_pos
    have hp_lt_max : p_cur < maxFullSlabs N :=
      hp_eq ▸ (hslot.multi_slab hb_pos).ptr_lt_maxFullSlabs hb hs_lt
    have hp_lt : p_cur < compGmAt metaBase U w N s.mem 0 := by
      rw [hp_eq, (hslot.multi_slab hb_pos).nslabs_eq]
      exact (hslot.multi_slab hb_pos).ptr_lt b hb _ hs_lt
    have hSN := hslot.multi_total_le hb_pos
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, by omega, hc_pos, hp_lt_max,
      (Nat.mul_le_mul_right (slabSize N) hp_lt).trans (by omega)⟩)
  all_goals try (
    have hc_neg : ¬(j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N) := by assumption
    obtain ⟨hptr_lt, ht_le⟩ := tailPtr_read_bounds hN hb_pos hb hslot hj_bc hc_neg
    try rw [clientResult_readCompGMGenProg hptr_lt]
    try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; exact hptr_lt⟩
    try omega)
  all_goals try exact fits_of_le_globalMetaLen_comp hb_pos hw hnU hU (by unfold gmQIdx at *; omega)
  all_goals exact lt_of_le_of_lt (by omega) hU

theorem validProg_compResolveOvfStepGen {w : ℕ} {d : ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)}
    {s : Memory.State} (h : CompResolveOvfStepPre w d s) :
    ValidProg w 0 s (compResolveOvfStepGenProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨j, p_cur⟩⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hj_bc, hslot, hp⟩ := h
  have henv : CompMetaEnv w (mkCompParams U V w N) metaBase s :=
    ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩
  have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  dsimp only [compResolveOvfStepGenProg, compResolveOvfInSlabGenProg, compResolveOvfAdvanceGenProg]
  simp only [cpSlabSize_mk, cpSlabSizeSubOne_mk, cpGmSlabMetaBase_mk,
    cpGmTailPtrBase_mk, cpTailCap_mk, hq_eq]
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hq_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hq_lt]
  refine validProg_ite (fun hj_slab => ?_) (fun hj_ge => ?_)
  · refine validProg_ite (fun _ => ?_) (fun _ => validProg_pure _)
    refine validProg_ite (fun _ => ?_) (fun _ => validProg_pure _)
    have hs_lt : j / slabSize N < compGmAt metaBase U w N s.mem (gmQIdx b) :=
      (Nat.div_lt_iff_lt_mul (slabSize_pos N)).2 hj_slab
    have hp_lt_max : p_cur < maxFullSlabs N :=
      hp hj_slab ▸ (hslot.multi_slab hb_pos).ptr_lt_maxFullSlabs hb hs_lt
    have habv_lt : gmSlabMetaBase N + (p_cur + p_cur + (p_cur + p_cur)) + 3 < globalMetaLen N := by
      have := gmSlabAboveIdx_lt hb_pos hp_lt_max; unfold gmSlabAboveIdx at this; omega
    exact validProg_bind (validProg_readCompGMGen ⟨henv, habv_lt⟩) (validProg_pure _)
  · obtain ⟨hptr_lt, _⟩ := tailPtr_read_bounds hN hb_pos hb hslot hj_bc hj_ge
    exact validProg_bind (validProg_readCompGMGen ⟨henv, hptr_lt⟩) (validProg_pure _)

private def compInitOvfFromDirGenProg :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (((cp, metaBase), b), (qK, fuel)) =>
    if cpMinCap cp < qK then do
      let dir_idx := cpGmSlabDirBase cp + b * cpDirSlabs cp + cpDirSlabsSubOne cp
      let p_prev ← readCompGMGenProg ((cp, metaBase), dir_idx)
      let p2 := p_prev + p_prev
      let abv_idx := cpGmSlabMetaBase cp + (p2 + p2) + 3
      let p_init ← readCompGMGenProg ((cp, metaBase), abv_idx)
      pure (p_init, fuel)
    else
      pure (0, fuel)

/-- Initialize `(p_init, fuel)` for Phase 2 overflow search on compacted metadata
(`¬ReadsWidth`). -/
def compInitOvfSearchGenProg : (CompParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, metaBase), b) => do
    let b3 := b + b + b
    let q_idx := 4 + b3
    let q_b ← readCompGMGenProg ((cp, metaBase), q_idx)
    let r_b ← readCompGMGenProg ((cp, metaBase), q_idx + 1)
    let qK := q_b * cpSlabSize cp
    let c := qK + r_b
    let cap := cpMinCap cp
    if cap < c then
      compInitOvfFromDirGenProg (((cp, metaBase), b), (qK, c - cap))
    else
      pure (0, 0)

theorem clientState_compInitOvfSearchGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compInitOvfSearchGenProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compInitOvfSearchGenProg, compInitOvfFromDirGenProg]
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    runClient_state_readCompGMGenProg]
  split_ifs <;> simp

@[simp] theorem runClient_state_compInitOvfSearchGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compInitOvfSearchGenProg d))) = s :=
  clientState_compInitOvfSearchGenProg d s

theorem memoryCost_compInitOvfSearchGenProg_le
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compInitOvfSearchGenProg d) s ≤ 8 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  dsimp only [compInitOvfSearchGenProg, compInitOvfFromDirGenProg]
  simp only [Realization.memoryCost_bind', memoryCost_readCompGMGenProg]
  split_ifs <;> simp

/-- Under `compGmAt = gmAt`, `compInitOvfSearchGenProg` returns the exact same `(p_init, fuel)`
pair as `Succinct.initOvfSearchProg` on `s_fix`. -/
theorem clientResult_compInitOvfSearchGenProg_eq {U V w w₀ N h_space metaBase b : ℕ}
    {s_fix s : Memory.State}
    (hgm_eq : compGmAt metaBase U w N s.mem = gmAt 0 U V w₀ N h_space s_fix.mem)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem)) :
    (Memory.spec 0).clientResult s
        (compInitOvfSearchGenProg ((mkCompParams U V w N, metaBase), b)) =
      (Memory.spec 0).clientResult s_fix
        (initOvfSearchProg U V w₀ N h_space (0, b)) := by
  have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hr_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hq_eq1 : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  have hq_eq2 : 4 + 3 * b = gmQIdx b := rfl
  have hr_eq : gmQIdx b + 1 = gmRIdx b := rfl
  simp only [compInitOvfSearchGenProg, compInitOvfFromDirGenProg, initOvfSearchProg, cpSlabSize_mk,
    cpMinCap_mk, cpGmSlabDirBase_mk, cpDirSlabs_mk, cpDirSlabsSubOne_mk, cpGmSlabMetaBase_mk,
    pure_bind, hq_eq1, hq_eq2, hr_eq]
  rw [prog_clientResult_bind, clientResult_readCompGMGenProg hq_lt,
    clientState_readCompGMGenProg, prog_clientResult_bind, clientResult_readCompGMGenProg hr_lt,
    clientState_readCompGMGenProg, StateTransitionSpec.clientResult_bind, clientState_readGMProg,
    clientResult_readGMProg s_fix hq_lt, StateTransitionSpec.clientResult_bind,
    clientState_readGMProg, clientResult_readGMProg s_fix hr_lt, ← hgm_eq]
  by_cases hcap : min N (effBucketCap N) <
      compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N +
        compGmAt metaBase U w N s.mem (gmRIdx b)
  · simp only [hcap, ↓reduceIte]
    by_cases hqK : min N (effBucketCap N) <
        compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N
    · simp only [hqK, ↓reduceIte]
      have hcap_le : effBucketCap N ≤ compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N := by
        by_cases hN_le : N ≤ effBucketCap N
        · have hbc_le : compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N +
              compGmAt metaBase U w N s.mem (gmRIdx b) ≤ N := by
            have h := bCount_le_n_max hslot b
            unfold bCount at h; simp only [hb_pos.ne', ↓reduceIte, hb] at h; exact h
          rw [min_eq_left hN_le] at hcap; omega
        · rw [min_eq_right (by omega)] at hqK; omega
      obtain ⟨hdir_lt, hdir_eq, hp_prev_max⟩ := hslot.lastDirSlab_ptr hb_pos hb hcap_le
      let p_prev := compGmAt metaBase U w N s.mem
        (gmSlabDirBase N + b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1))
      have hp_prev_lt : p_prev < maxFullSlabs N := by
        dsimp only [p_prev]; rw [hdir_eq]; exact hp_prev_max
      have habv_lt : gmSlabMetaBase N + 4 * p_prev + 3 < globalMetaLen N :=
        gmSlabAboveIdx_lt hb_pos hp_prev_lt
      have habv_eq : gmSlabMetaBase N +
          (compGmAt metaBase U w N s.mem
              (gmSlabDirBase N + b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1)) +
            compGmAt metaBase U w N s.mem
              (gmSlabDirBase N + b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1)) +
            (compGmAt metaBase U w N s.mem
                (gmSlabDirBase N + b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1)) +
              compGmAt metaBase U w N s.mem
                (gmSlabDirBase N + b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1)))) + 3 =
          gmSlabMetaBase N + 4 * p_prev + 3 := by dsimp only [p_prev]; omega
      have hp_eq : gmAt 0 U V w₀ N h_space s_fix.mem
          (gmSlabDirBase N + b * dirSlabsPerBucket N + (dirSlabsPerBucket N - 1)) = p_prev := by
        dsimp only [p_prev]; rw [← hgm_eq]
      rw [prog_clientResult_bind, clientResult_readCompGMGenProg hdir_lt,
        clientState_readCompGMGenProg, habv_eq,
        prog_clientResult_bind, clientResult_readCompGMGenProg habv_lt,
        clientState_readCompGMGenProg, prog_clientResult_pure,
        StateTransitionSpec.clientResult_bind, clientState_readGMProg,
        clientResult_readGMProg s_fix hdir_lt,
        StateTransitionSpec.clientResult_bind, clientState_readGMProg,
        hp_eq, clientResult_readGMProg s_fix habv_lt,
        StateTransitionSpec.clientResult_pure,
        ← hgm_eq]
    · simp only [hqK, ↓reduceIte]; rfl
  · simp only [hcap, ↓reduceIte]; rfl

private def CompInitOvfFromDirPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, metaBase), b), (qK, _fuel)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      effBucketCap N < N ∧
      qK = compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem)

private theorem realizesBounded_compInitOvfFromDirGen :
    RealizesBounded .exact compInitOvfFromDirGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompInitOvfFromDirPre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, ⟨qK, fuel⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hcapN, rfl, hslot⟩ := h
    simp only [cpMinCap_mk, cpGmSlabDirBase_mk, cpDirSlabs_mk, cpDirSlabsSubOne_mk,
      cpGmSlabMetaBase_mk] at *)
  all_goals (
    have hcap_le : effBucketCap N ≤ compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N := by
      rw [min_eq_right hcapN.le] at hc; omega
    obtain ⟨hdir_lt, hdir_eq, hp_prev_max⟩ := hslot.lastDirSlab_ptr hb_pos hb hcap_le
    have habv_lt := gmSlabAboveIdx_lt hb_pos hp_prev_max
    try simp only [StateTransitionSpec.clientState, clientResult_readCompGMGenProg hdir_lt,
      runClient_state_readCompGMGenProg] at *
    rw [hdir_eq] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; unfold gmSlabAboveIdx at habv_lt; omega)
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmSlabDirBase gmSlabAboveIdx gmSlabMetaBase at *
    omega)

/-- Precondition for initializing overflow search. -/
@[expose] def CompInitOvfSearchPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      b < numBuckets N ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem)

theorem realizesBounded_compInitOvfSearchGen :
    RealizesBounded .exact compInitOvfSearchGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      CompInitOvfSearchPre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  have hdir := realizesBounded_compInitOvfFromDirGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslot⟩ := h
    have hb_ne : bucketBits N ≠ 0 := hb_pos.ne'
    have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hr_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have hr_eq : gmQIdx b + 1 = gmRIdx b := rfl
    have hbc_le : bCount N (compGmAt metaBase U w N s.mem) b ≤ N := bCount_le_n_max hslot b
    unfold bCount at hbc_le; simp only [hb_ne, ↓reduceIte, hb] at hbc_le
    simp only [cpSlabSize_mk, cpMinCap_mk, hq_eq, hr_eq, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg hq_lt, clientResult_readCompGMGenProg hr_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try (
    refine ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ?_⟩
    simp only [cpN_mk]; omega)
  all_goals try (
    have hcapN : effBucketCap N < N := by
      by_contra hnot; rw [min_eq_left (by omega)] at hc; omega
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hcapN, rfl, hslot⟩)
  all_goals try omega
  all_goals try exact lt_of_le_of_lt (by omega) hU
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmQIdx gmRIdx at *
    omega)

theorem validProg_compInitOvfSearchGen {w : ℕ} {d : (CompParams × ℕ) × ℕ} {s : Memory.State}
    (h : CompInitOvfSearchPre w d s) : ValidProg w 0 s (compInitOvfSearchGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hb, hslot⟩ := h
  have henv : CompMetaEnv w (mkCompParams U V w N) metaBase s :=
    ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩
  have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hr_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
  have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  have hr_eq : gmQIdx b + 1 = gmRIdx b := rfl
  dsimp only [compInitOvfSearchGenProg, compInitOvfFromDirGenProg]
  simp only [cpSlabSize_mk, cpMinCap_mk, cpGmSlabDirBase_mk, cpDirSlabs_mk,
    cpDirSlabsSubOne_mk, cpGmSlabMetaBase_mk, hq_eq, hr_eq]
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hq_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hq_lt]
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hr_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hr_lt]
  refine validProg_ite (fun hcap => ?_) (fun _ => validProg_pure _)
  refine validProg_ite (fun hqK => ?_) (fun _ => validProg_pure _)
  have hcap_le : effBucketCap N ≤ compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N := by
    by_cases hN_le : N ≤ effBucketCap N
    · have hbc_le := bCount_le_n_max hslot b
      unfold bCount at hbc_le; simp only [hb_pos.ne', ↓reduceIte, hb] at hbc_le
      rw [min_eq_left hN_le] at hcap; omega
    · rw [min_eq_right (by omega)] at hqK; omega
  obtain ⟨hdir_lt, hdir_eq, hp_prev_max⟩ := hslot.lastDirSlab_ptr hb_pos hb hcap_le
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hdir_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hdir_lt, hdir_eq]
  have habv_lt := gmSlabAboveIdx_lt hb_pos hp_prev_max
  have habv_eq : gmSlabMetaBase N + (slabPtrOf N (compGmAt metaBase U w N s.mem) b
        (dirSlabsPerBucket N - 1) + slabPtrOf N (compGmAt metaBase U w N s.mem) b
        (dirSlabsPerBucket N - 1) + (slabPtrOf N (compGmAt metaBase U w N s.mem) b
        (dirSlabsPerBucket N - 1) + slabPtrOf N (compGmAt metaBase U w N s.mem) b
        (dirSlabsPerBucket N - 1))) + 3 =
      gmSlabAboveIdx N (slabPtrOf N (compGmAt metaBase U w N s.mem) b
        (dirSlabsPerBucket N - 1)) := by unfold gmSlabAboveIdx; omega
  rw [habv_eq]
  exact validProg_bind (validProg_readCompGMGen ⟨henv, habv_lt⟩) (validProg_pure _)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
