/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.Internal
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Compacted Last-Slot and Indexed-Slot Resolvers (`RealizesBounded .exact`)

Implements `compLastSlotOfGenProg` and `compResolveIndexedSlotGenProg` in `Memory.Prog`
(`¬ReadsWidth`), with exact `clientResult` specs and `RealizesBounded .exact` / `ValidProg w 0`
certificates.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compLastSlotOfGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompLastSlotOfPre`:
  resolver for the last physical slot `slotOf N gm b (bCount N gm b - 1)` in bucket `b`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compResolveIndexedSlotGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompResolveIndexedSlotPre`:
  resolver for indexed bucket slot `j < effBucketCap N`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_compLastSlotOfGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.validProg_compLastSlotOfGen`:
  `RealizesBounded .exact` and `ValidProg w 0` certificates for `compLastSlotOfGenProg`.
* `realizesBounded_compResolveIndexedSlotGen`, `validProg_compResolveIndexedSlotGen`:
  `RealizesBounded .exact` and `ValidProg w 0` certificates for `compResolveIndexedSlotGenProg`.
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

/-- Resolve physical slot `slotOf N gm b (bCount N gm b - 1)` of the last item in bucket `b`. -/
def compLastSlotOfGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), b) => do
    let z0 ← pure 0
    if cpBucketBits cp = z0 then do
      let c ← readCompGMGenProg ((cp, metaBase), z0)
      pure (c - 1)
    else do
      let b3 := b + b + b
      let r_idx ← pure (4 + b3 + 1)
      let r_b ← readCompGMGenProg ((cp, metaBase), r_idx)
      let t_idx ← pure (cpGmTailPtrBase cp + (b * cpTailCap cp + (r_b - 1)))
      let t_last ← readCompGMGenProg ((cp, metaBase), t_idx)
      pure (cpNSubOne cp - t_last)

theorem clientState_compLastSlotOfGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compLastSlotOfGenProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  unfold StateTransitionSpec.clientState; dsimp only [compLastSlotOfGenProg]
  simp only [pure_bind]; split_ifs <;> simp

@[simp] theorem runClient_state_compLastSlotOfGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compLastSlotOfGenProg d))) = s :=
  clientState_compLastSlotOfGenProg d s

theorem memoryCost_compLastSlotOfGenProg_le (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compLastSlotOfGenProg d) s ≤ 4 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  dsimp only [compLastSlotOfGenProg]; simp only [pure_bind]; split_ifs <;> simp

/-- `GlobalMeta` index facts for reading `r_b` and then the last tail pointer of bucket `b`. -/
private theorem lastTailPtr_read_bounds {N b : ℕ} {gm : ℕ → ℕ} (hslot : SlotStoreInv N gm)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) :
    4 + (b + b + b) + 1 = gmRIdx b ∧ gmRIdx b < globalMetaLen N ∧
      gmTailPtrBase N + (b * tailCapPerBucket N + (gm (gmRIdx b) - 1)) < globalMetaLen N :=
  ⟨by unfold gmRIdx; omega, gmRIdx_lt hb_pos hb,
    gmTailPtrIdx_lt hb_pos hb (Nat.sub_lt_of_lt (hslot.multi_r_bounds hb_pos b hb).1)⟩

theorem clientResult_compLastSlotOfGenProg {U V w N metaBase b : ℕ} {s : Memory.State}
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (hbc : 1 ≤ bCount N (compGmAt metaBase U w N s.mem) b) :
    (Memory.spec 0).clientResult s
        (compLastSlotOfGenProg ((mkCompParams U V w N, metaBase), b)) =
      slotOf N (compGmAt metaBase U w N s.mem) b
        (bCount N (compGmAt metaBase U w N s.mem) b - 1) := by
  set gm := compGmAt metaBase U w N s.mem
  simp only [compLastSlotOfGenProg, cpBucketBits_mk, cpGmTailPtrBase_mk, cpTailCap_mk,
    cpNSubOne_mk, pure_bind]
  by_cases hb0 : bucketBits N = 0
  · have hb_eq : b = 0 := by simp only [numBuckets, hb0, pow_zero] at hb; omega
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    simp [hb0, hb_eq, gm, slotOf, bCount, clientResult_readCompGMGenProg h0_lt]
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have hr_pos : 1 ≤ gm (gmRIdx b) := pos_gmRIdx_of_pos_bCount hb_pos hslot hb hbc
    obtain ⟨hr_eq, hr_idx_lt, hptr_lt⟩ := lastTailPtr_read_bounds hslot hb_pos hb
    rw [ite_eq_right hb0, hr_eq, prog_clientResult_bind, clientResult_readCompGMGenProg hr_idx_lt,
      clientState_readCompGMGenProg, prog_clientResult_bind,
      clientResult_readCompGMGenProg hptr_lt, clientState_readCompGMGenProg,
      prog_clientResult_pure]
    simp only [slotOf, bCount, hb0, ↓reduceIte, hb, Nat.add_sub_assoc hr_pos,
      Nat.add_sub_cancel_left, Nat.not_lt.mpr (Nat.le_add_right _ _)]
    rfl

/-- Precondition for retrieving the last physical slot of bucket `b`. -/
@[expose] def CompLastSlotOfPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      1 ≤ bCount N (compGmAt metaBase U w N s.mem) b

theorem realizesBounded_compLastSlotOfGen :
    RealizesBounded .exact compLastSlotOfGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompLastSlotOfPre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hslot, hb, hbc⟩ := h
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    simp only [cpBucketBits_mk, cpGmTailPtrBase_mk, cpTailCap_mk, cpNSubOne_mk,
      StateTransitionSpec.clientState, clientResult_readCompGMGenProg h0_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, h0_lt⟩
  · have hb_eq : b = 0 := by simp only [numBuckets, hc, pow_zero] at hb; omega
    unfold bCount at hbc; simp only [hc, ↓reduceIte, hb_eq] at hbc; exact hbc
  all_goals (
    have hb_pos : 0 < bucketBits N := by omega
    have hr_pos : 1 ≤ compGmAt metaBase U w N s.mem (gmRIdx b) :=
      pos_gmRIdx_of_pos_bCount hb_pos hslot hb hbc
    obtain ⟨hr_eq, hr_idx_lt, hptr_lt⟩ := lastTailPtr_read_bounds hslot hb_pos hb
    have ht_lt : compGmAt metaBase U w N s.mem
        (gmTailPtrBase N + (b * tailCapPerBucket N +
          (compGmAt metaBase U w N s.mem (gmRIdx b) - 1))) <
        compGmAt metaBase U w N s.mem 1 :=
      (hslot.multi_tail hb_pos).ptr_lt b hb _ (by omega)
    have hSN := hslot.multi_total_le hb_pos
    simp only [hr_eq, clientResult_readCompGMGenProg hr_idx_lt,
      clientResult_readCompGMGenProg hptr_lt] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by simp only [cpN_mk]; omega⟩
  all_goals try omega
  all_goals (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmTailPtrBase gmRIdx at *
    omega)

theorem validProg_compLastSlotOfGen {w : ℕ} {d : (CompParams × ℕ) × ℕ} {s : Memory.State}
    (h : CompLastSlotOfPre w d s) : ValidProg w 0 s (compLastSlotOfGenProg d) := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hslot, hb, _hbc⟩ := h
  have henv : CompMetaEnv w (mkCompParams U V w N) metaBase s :=
    ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩
  simp only [compLastSlotOfGenProg, pure_bind, cpBucketBits_mk, cpGmTailPtrBase_mk, cpTailCap_mk]
  refine validProg_ite
    (fun _ => validProg_bind
      (validProg_readCompGMGen ⟨henv, by simp only [globalMetaLen]; omega⟩) (validProg_pure _))
    (fun hb0 => ?_)
  obtain ⟨hr_eq, hr_idx_lt, hptr_lt⟩ :=
    lastTailPtr_read_bounds hslot (Nat.pos_of_ne_zero hb0) hb
  rw [hr_eq]
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hr_idx_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hr_idx_lt]
  exact validProg_bind (validProg_readCompGMGen ⟨henv, hptr_lt⟩) (validProg_pure _)

private def compResolveMultiSlotGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, metaBase), b), j) => do
    let b3 := b + b + b
    let q_idx := 4 + b3
    let q_b ← readCompGMGenProg ((cp, metaBase), q_idx)
    let qK := q_b * cpSlabSize cp
    if j < qK then do
      let dir_idx := cpGmSlabDirBase cp + (b * cpDirSlabs cp + j / cpSlabSize cp)
      let p ← readCompGMGenProg ((cp, metaBase), dir_idx)
      pure (p * cpSlabSize cp + (cpSlabSizeSubOne cp - j % cpSlabSize cp))
    else do
      let t_idx := cpGmTailPtrBase cp + (b * cpTailCap cp + (j - qK))
      let t ← readCompGMGenProg ((cp, metaBase), t_idx)
      pure (cpNSubOne cp - t)

/-- Resolve indexed local slot `j < effBucketCap N` of bucket `b` to `slotOf N gm b j`. -/
def compResolveIndexedSlotGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, metaBase), b), j) =>
    if cpBucketBits cp = 0 then
      pure j
    else
      compResolveMultiSlotGenProg (((cp, metaBase), b), j)

theorem clientState_compResolveIndexedSlotGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compResolveIndexedSlotGenProg d) = s := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, j⟩
  dsimp only [StateTransitionSpec.clientState, compResolveIndexedSlotGenProg,
    compResolveMultiSlotGenProg]
  split_ifs <;> simp only [prog_runClient_state_pure, prog_runClient_state_bind,
    runClient_state_readCompGMGenProg]
  split_ifs <;> simp

@[simp] theorem runClient_state_compResolveIndexedSlotGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compResolveIndexedSlotGenProg d))) = s :=
  clientState_compResolveIndexedSlotGenProg d s

theorem memoryCost_compResolveIndexedSlotGenProg_le
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compResolveIndexedSlotGenProg d) s ≤ 4 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, j⟩
  dsimp only [compResolveIndexedSlotGenProg, compResolveMultiSlotGenProg]
  split_ifs
  · simp
  · rw [Realization.memoryCost_bind', memoryCost_readCompGMGenProg, clientState_readCompGMGenProg]
    split_ifs <;> simp

/-- The slab of local slot `j < effBucketCap N` has a `slabDir` entry inside `GlobalMeta`. -/
private theorem slabDir_read_bounds {N b j : ℕ} (hb_pos : 0 < bucketBits N)
    (hb : b < numBuckets N) (hj_cap : j < effBucketCap N) :
    j / slabSize N < dirSlabsPerBucket N ∧
      gmSlabDirBase N + (b * dirSlabsPerBucket N + j / slabSize N) < globalMetaLen N := by
  have hs := (Nat.div_lt_iff_lt_mul (slabSize_pos N)).2
    (effBucketCap_eq_dirSlabs_mul_slabSize hb_pos ▸ hj_cap)
  exact ⟨hs, Nat.add_assoc _ _ _ ▸ gmSlabDirIdx_lt hb_pos hb hs⟩

/-- A slot `j` inside the full slabs of bucket `b` reads its physical slab from `slabDir`. -/
private theorem slabDir_read_eq {N b j : ℕ} {gm : ℕ → ℕ} (hslot : SlotStoreInv N gm)
    (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N) (hj_cap : j < effBucketCap N)
    (hj_slab : j < gm (gmQIdx b) * slabSize N) :
    gm (gmSlabDirBase N + (b * dirSlabsPerBucket N + j / slabSize N)) =
      slabPtrOf N gm b (j / slabSize N) := by
  have := (hslot.multi_slab hb_pos).dir_eq b hb _
    ((Nat.div_lt_iff_lt_mul (slabSize_pos N)).2 hj_slab) (slabDir_read_bounds hb_pos hb hj_cap).1
  simpa only [gmSlabDirIdx, Nat.add_assoc] using this

theorem clientResult_compResolveIndexedSlotGenProg {U V w N metaBase b j : ℕ} {s : Memory.State}
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (hj_bc : j < bCount N (compGmAt metaBase U w N s.mem) b)
    (hj_cap : j < effBucketCap N) :
    (Memory.spec 0).clientResult s
        (compResolveIndexedSlotGenProg (((mkCompParams U V w N, metaBase), b), j)) =
      slotOf N (compGmAt metaBase U w N s.mem) b j := by
  by_cases hb0 : bucketBits N = 0
  · simp [compResolveIndexedSlotGenProg, slotOf, hb0]
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by simp only [gmQIdx]; omega
    simp only [compResolveIndexedSlotGenProg, compResolveMultiSlotGenProg, cpBucketBits_mk,
      cpSlabSize_mk, cpGmSlabDirBase_mk, cpDirSlabs_mk, cpSlabSizeSubOne_mk, cpGmTailPtrBase_mk,
      cpTailCap_mk, cpNSubOne_mk, hb0, ↓reduceIte, hq_eq]
    rw [prog_clientResult_bind, clientResult_readCompGMGenProg hq_idx_lt,
      clientState_readCompGMGenProg]
    by_cases hj_slab : j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N
    · simp only [hj_slab, ↓reduceIte, prog_clientResult_bind,
        clientResult_readCompGMGenProg (slabDir_read_bounds hb_pos hb hj_cap).2,
        prog_clientResult_pure, slabDir_read_eq hslot hb_pos hb hj_cap hj_slab, slotOf, hb0]
    · have hN : 0 < N := Nat.pos_of_ne_zero fun h0 => hb0 (congrArg bucketBits h0)
      obtain ⟨hptr_lt, _⟩ := tailPtr_read_bounds hN hb_pos hb hslot hj_bc hj_slab
      simp only [hj_slab, ↓reduceIte, prog_clientResult_bind,
        clientResult_readCompGMGenProg hptr_lt, prog_clientResult_pure, slotOf, hb0]
      rfl

private def CompResolveMultiSlotPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), b), j), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      j < bCount N (compGmAt metaBase U w N s.mem) b ∧
      j < effBucketCap N

private theorem realizesBounded_compResolveMultiSlotGen :
    RealizesBounded .exact compResolveMultiSlotGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompResolveMultiSlotPre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, j⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hslot, hb, hj_bc, hj_cap⟩ := h
    have henv : CompMetaEnv w (mkCompParams U V w N) metaBase s :=
      ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩
    have hb_ne : bucketBits N ≠ 0 := hb_pos.ne'
    have hK : 0 < slabSize N := slabSize_pos N
    have hmod_lt := Nat.mod_lt j hK
    have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    obtain ⟨-, hdir_lt⟩ := slabDir_read_bounds hb_pos hb hj_cap
    have hbc_le : bCount N (compGmAt metaBase U w N s.mem) b ≤ N := bCount_le_n_max hslot b
    unfold bCount at hbc_le; simp only [hb_ne, ↓reduceIte, hb] at hbc_le
    simp only [cpSlabSize_mk, cpGmSlabDirBase_mk, cpDirSlabs_mk, cpSlabSizeSubOne_mk,
      cpGmTailPtrBase_mk, cpTailCap_mk, cpNSubOne_mk, hq_eq, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg hq_idx_lt, runClient_state_readCompGMGenProg] at *)
  all_goals try exact hK.ne'
  all_goals try exact ⟨henv, hq_idx_lt⟩
  all_goals try exact ⟨henv, by simp only [cpN_mk]; omega⟩
  all_goals try (
    have hc_neg : ¬(j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N) := by assumption
    obtain ⟨hptr_lt, ht_le⟩ := tailPtr_read_bounds hN hb_pos hb hslot hj_bc hc_neg
    try rw [clientResult_readCompGMGenProg hptr_lt]
    try exact ⟨henv, by simpa only [cpN_mk] using hptr_lt⟩
    try omega)
  all_goals try omega
  all_goals try (
    refine fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ?_
    unfold gmQIdx gmSlabDirBase at *
    omega)
  all_goals try exact lt_of_le_of_lt (by omega) hU
  rw [clientResult_readCompGMGenProg hdir_lt, slabDir_read_eq hslot hb_pos hb hj_cap ‹_›]
  have hp_lt := (hslot.multi_slab hb_pos).nslabs_eq ▸
    (hslot.multi_slab hb_pos).ptr_lt b hb _ ((Nat.div_lt_iff_lt_mul hK).2 ‹_›)
  have h1 := Nat.add_one_mul
    (slabPtrOf N (compGmAt metaBase U w N s.mem) b (j / slabSize N)) (slabSize N) ▸
    Nat.mul_le_mul_right (slabSize N) hp_lt
  have hSN := hslot.multi_total_le hb_pos
  exact lt_of_le_of_lt (by omega) hU

/-- Precondition for resolving indexed slot entries. -/
@[expose] def CompResolveIndexedSlotPre (w : ℕ) :
    ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), b), j), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      j < bCount N (compGmAt metaBase U w N s.mem) b ∧
      j < effBucketCap N

theorem realizesBounded_compResolveIndexedSlotGen :
    RealizesBounded .exact compResolveIndexedSlotGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompResolveIndexedSlotPre (fun _ _ => 0) := by
  have hm := realizesBounded_compResolveMultiSlotGen
  realize
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, j⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hslot, hb, hj_bc, hj_cap⟩ := h
  simp only [cpBucketBits_mk] at *
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, Nat.pos_of_ne_zero hc, hslot, hb, hj_bc, hj_cap⟩

theorem validProg_compResolveIndexedSlotGen {w : ℕ} {d : ((CompParams × ℕ) × ℕ) × ℕ}
    {s : Memory.State} (h : CompResolveIndexedSlotPre w d s) :
    ValidProg w 0 s (compResolveIndexedSlotGenProg d) := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, b⟩, j⟩
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hslot, hb, hj_bc, hj_cap⟩ := h
  have henv : CompMetaEnv w (mkCompParams U V w N) metaBase s :=
    ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩
  simp only [compResolveIndexedSlotGenProg, compResolveMultiSlotGenProg, cpBucketBits_mk,
    cpSlabSize_mk, cpGmSlabDirBase_mk, cpDirSlabs_mk, cpGmTailPtrBase_mk, cpTailCap_mk]
  refine validProg_ite (fun _ => validProg_pure j) (fun hb0 => ?_)
  have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
  have hq_idx_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
  have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
  rw [hq_eq]
  refine validProg_bind (validProg_readCompGMGen ⟨henv, hq_idx_lt⟩) ?_
  rw [clientState_readCompGMGenProg, clientResult_readCompGMGenProg hq_idx_lt]
  refine validProg_ite (fun _ => ?_) (fun hj_ge => ?_)
  · exact validProg_bind
      (validProg_readCompGMGen ⟨henv, (slabDir_read_bounds hb_pos hb hj_cap).2⟩) (validProg_pure _)
  · obtain ⟨hptr_lt, _⟩ := tailPtr_read_bounds hN hb_pos hb hslot hj_bc hj_ge
    exact validProg_bind (validProg_readCompGMGen ⟨henv, hptr_lt⟩) (validProg_pure _)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
