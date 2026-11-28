/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctMicroChain
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.WramOmega

/-!
# Succinct Dictionary Bucket Search and Query in `Memory.Prog` via `realize`

This module implements Phase 2 overflow search (`resolveOvfStepProg`, `ovfStepProg`,
`ovfLoopProg`, `searchOverflowProg`), the combined two-phase bucket search (`searchBucketProg`),
and the dictionary lookup body (`queryBodyProg`) in the `Memory.Prog` monad, certifying each via
`Realizes .exact` and the `realize` tactic.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.resolveOvfStepProg`: single-step overflow slot
  resolver advancing along `slabAbove` across slab boundaries.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.ovfStepProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.ovfLoopProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.searchOverflowProg`: Phase 2 overflow scan over
  `j ∈ [effBucketCap n_max, bCount n_max gm b)`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.searchBucketProg`: combined two-phase bucket
  search (`searchMicroChainProg` followed by `searchOverflowProg`).
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.queryBodyProg`: `Memory.Prog` lookup body
  returning `Option ℕ`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.searchOverflowProg_spec`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_searchOverflowGen`: specification and
  `Realizes` certificate for `searchOverflowProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.searchBucketProg_spec`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_searchBucketGen`: specification and
  `Realizes` certificate for `searchBucketProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.queryBodyProg_spec`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_queryBodyGen`: specification and
  `Realizes` certificate for `queryBodyProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

/-! ## Section 1: Overflow Slot Resolution (`resolveOvfStepProg`) -/

/-- Arithmetic helper: when `(K - 1) - j % K = 0` (`0 < K`), `(j + 1) / K = j / K + 1` and
`(j / K + 1) * K = j + 1`. -/
private theorem div_succ_of_sub_mod_eq_zero {j K : ℕ} (hK : 0 < K) (hoff : (K - 1) - j % K = 0) :
    (j + 1) / K = j / K + 1 ∧ (j / K + 1) * K = j + 1 := by
  have hmod := Nat.mod_lt j hK
  have hdiv := Nat.div_add_mod j K
  have hj_eq : j + 1 = (j / K + 1) * K := by rw [Nat.add_one_mul, Nat.mul_comm _ K]; omega
  exact ⟨by rw [hj_eq, Nat.mul_div_cancel _ hK], hj_eq.symm⟩

/-- Arithmetic helper: when `(K - 1) - j % K ≠ 0` (`0 < K`), `(j + 1) / K = j / K`. -/
private theorem div_succ_of_sub_mod_ne_zero {j K : ℕ} (hK : 0 < K) (hoff : (K - 1) - j % K ≠ 0) :
    (j + 1) / K = j / K := by
  have hmod := Nat.mod_lt j hK
  have hdiv := Nat.div_add_mod j K
  rw [show j + 1 = (j % K + 1) + K * (j / K) by omega,
    Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt (by omega), Nat.zero_add]

/-- Dictionary parameters `x.1.1` in a parameter-free step input `((dp, arg), state)`. -/
abbrev ovfGenParams {α β : Type} (x : (DictParams × α) × β) : DictParams := x.1.1

/-- Base address `base` in a parameter-free overflow-resolver input
`((dp, (base, b)), extra)`. -/
abbrev ovfGenBase {β : Type} (x : (DictParams × (ℕ × ℕ)) × β) : ℕ := x.1.2.1

/-- Bucket index `b` in a parameter-free overflow-resolver input
`((dp, (base, b)), extra)`. -/
abbrev ovfGenBucket {β : Type} (x : (DictParams × (ℕ × ℕ)) × β) : ℕ := x.1.2.2

/-- Base address `d.1.1` in a bucket-prefixed input `((base, b), extra)`. -/
abbrev ovfBucketBase {α : Type} (d : (ℕ × ℕ) × α) : ℕ := d.1.1

/-- Bucket index `d.1.2` in a bucket-prefixed input `((base, b), extra)`. -/
abbrev ovfBucketIdx {α : Type} (d : (ℕ × ℕ) × α) : ℕ := d.1.2

/-- Logical slot index `j` in an overflow-step input `(ctx, (j, p_cur))`. -/
abbrev ovfResolveIdx {α : Type} (d : α × (ℕ × ℕ)) : ℕ := d.2.1

/-- Current slab pointer `p_cur` in an overflow-step input `(ctx, (j, p_cur))`. -/
abbrev ovfResolveSlabPtr {α : Type} (d : α × (ℕ × ℕ)) : ℕ := d.2.2

/-- Parameter-free single-step overflow slot resolver (`d = ((dp, (base, b)), (j, p_cur))`),
returning `(slotOf n_max gm b j, p_next)` where `p_next` advances along `slabAbove` at the end of
each full slab (`off = 0` and `j + 1 < q_b * slabSize n_max`). -/
@[expose] def resolveOvfStepGenProg
    (d : (DictParams × (ℕ × ℕ)) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) :=
  let dp := ovfGenParams d
  let base := ovfGenBase d
  let b := ovfGenBucket d
  let j := ovfResolveIdx d
  let p_cur := ovfResolveSlabPtr d
  do
    let q_idx ← pure (4 + 3 * b)
    let q_b ← readGMGenProg (dp, (base, q_idx))
    let qK ← pure (q_b * dpSlabSize dp)
    if j < qK then do
      let off ← pure (dpSlabSizeSubOne dp - j % dpSlabSize dp)
      let phys ← pure (p_cur * dpSlabSize dp + off)
      let z0 ← pure 0
      if off = z0 then do
        let j1 ← pure (j + 1)
        if j1 < qK then do
          let abv_idx ← pure (dpGmSlabMetaBase dp + 4 * p_cur + 3)
          let p_next ← readGMGenProg (dp, (base, abv_idx))
          pure (phys, p_next)
        else
          pure (phys, p_cur)
      else
        pure (phys, p_cur)
    else do
      let r ← pure (j - qK)
      let t_idx ← pure (dpGmTailPtrBase dp + (b * dpTailCap dp + r))
      let t ← readGMGenProg (dp, (base, t_idx))
      let phys ← pure (dpNMaxSubOne dp - t)
      pure (phys, p_cur)

/-- Single-step overflow slot resolver (`d = ((base, b), (j, p_cur))`), returning
`(slotOf n_max gm b j, p_next)` where `p_next` advances along `slabAbove` at the end of each
full slab (`off = 0` and `j + 1 < q_b * slabSize n_max`). -/
@[expose] def resolveOvfStepProg (U V w n_max h_space : ℕ)
    (d : (ℕ × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) :=
  let base := ovfBucketBase d
  let b := ovfBucketIdx d
  let j := ovfResolveIdx d
  let p_cur := ovfResolveSlabPtr d
  do
    let q_idx ← pure (4 + 3 * b)
    let q_b ← readGMProg U V w n_max h_space (base, q_idx)
    let qK ← pure (q_b * slabSize n_max)
    if j < qK then do
      let off ← pure ((slabSize n_max - 1) - j % slabSize n_max)
      let phys ← pure (p_cur * slabSize n_max + off)
      let z0 ← pure 0
      if off = z0 then do
        let j1 ← pure (j + 1)
        if j1 < qK then do
          let abv_idx ← pure (gmSlabMetaBase n_max + 4 * p_cur + 3)
          let p_next ← readGMProg U V w n_max h_space (base, abv_idx)
          pure (phys, p_next)
        else
          pure (phys, p_cur)
      else
        pure (phys, p_cur)
    else do
      let r ← pure (j - qK)
      let t_idx ← pure (gmTailPtrBase n_max + (b * tailCapPerBucket n_max + r))
      let t ← readGMProg U V w n_max h_space (base, t_idx)
      let phys ← pure ((n_max - 1) - t)
      pure (phys, p_cur)

@[simp]
theorem resolveOvfStepGenProg_mk (U V w n_max h_space : ℕ)
    (d1 d2 : ℕ × ℕ) :
    resolveOvfStepGenProg ((mkDictParams U V w n_max h_space, d1), d2) =
      resolveOvfStepProg U V w n_max h_space (d1, d2) := by
  simp only [resolveOvfStepGenProg, resolveOvfStepProg, ovfGenParams, ovfGenBase, ovfGenBucket,
    ovfBucketBase, ovfBucketIdx, ovfResolveIdx, ovfResolveSlabPtr, p_slabSize_mk,
    p_slabSizeSubOne_mk, p_gmSlabMetaBase_mk, p_gmTailPtrBase_mk, p_tailCap_mk, p_nMaxSubOne_mk,
    readGMGenProg_mk]

theorem memoryCost_resolveOvfStepGenProg_pos
    (d : (DictParams × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (resolveOvfStepGenProg d) s := by
  unfold resolveOvfStepGenProg readGMGenProg readPackedGenProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind, memoryCost_readPackedProg]
  omega

theorem clientState_resolveOvfStepProg (U V w n_max h_space : ℕ)
    (d : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (resolveOvfStepProg U V w n_max h_space d) = s := by
  unfold resolveOvfStepProg
  simp only [ovfBucketBase, ovfBucketIdx, ovfResolveIdx, ovfResolveSlabPtr, pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_readGMProg]
  split_ifs <;> first
    | (rw [StateTransitionSpec.clientState_bind, clientState_readGMProg]; rfl)
    | rfl

theorem memoryCost_resolveOvfStepProg_le (U V w n_max h_space : ℕ)
    (d : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (resolveOvfStepProg U V w n_max h_space d) s ≤ 4 := by
  unfold resolveOvfStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind, clientState_readGMProg, memoryCost_readGMProg]
  split_ifs <;>
    simp only [memoryCost_bind, memoryCost_readGMProg, memoryCost_pure] <;>
    omega

/-- Precondition for `resolveOvfStepProg` (`d = ((base, b), (j, p_cur))`). -/
@[expose] def ResolveOvfStepPre (U V w₀ n_max h_space w : ℕ)
    (d : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let base := ovfBucketBase d
  let b := ovfBucketIdx d
  let j := ovfResolveIdx d
  let p_cur := ovfResolveSlabPtr d
  let gm := gmAt base U V w₀ n_max h_space s.mem
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  b < numBuckets n_max ∧
  j < bCount n_max gm b ∧
  SlotStoreInv n_max gm ∧
  (j < gm (gmQIdx b) * slabSize n_max →
    p_cur = slabPtrOf n_max gm b (j / slabSize n_max)) ∧
  0 < bucketBits n_max

/-- Parameter-free precondition for `resolveOvfStepGenProg`. -/
@[expose] def ResolveOvfStepGenPre (w : ℕ)
    (d : (DictParams × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let dp := ovfGenParams d
  let base := ovfGenBase d
  let b := ovfGenBucket d
  let j := ovfResolveIdx d
  let p_cur := ovfResolveSlabPtr d
  let gm := gmAt base (dpU dp) (dpV dp) (dpW dp) (dpNMax dp) (dpHSpace dp) s.mem
  DictEnvGen w dp base ∧
  b < numBuckets (dpNMax dp) ∧
  j < bCount (dpNMax dp) gm b ∧
  SlotStoreInv (dpNMax dp) gm ∧
  (j < gm (gmQIdx b) * slabSize (dpNMax dp) →
    p_cur = slabPtrOf (dpNMax dp) gm b (j / slabSize (dpNMax dp))) ∧
  0 < bucketBits (dpNMax dp)

@[simp]
theorem resolveOvfStepGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d1 d2 : ℕ × ℕ) (s : Memory.State) :
    ResolveOvfStepGenPre w ((mkDictParams U V w₀ n_max h_space, d1), d2) s ↔
      ResolveOvfStepPre U V w₀ n_max h_space w (d1, d2) s := Iff.rfl

theorem clientResult_resolveOvfStepProg {U V w n_max h_space : ℕ}
    {d : (ℕ × ℕ) × (ℕ × ℕ)} (s : Memory.State)
    (hb_pos : 0 < bucketBits n_max)
    (hb : ovfBucketIdx d < numBuckets n_max)
    (hj_bc : ovfResolveIdx d < bCount n_max (gmAt (ovfBucketBase d) U V w n_max h_space s.mem)
      (ovfBucketIdx d))
    (hinv : SlotStoreInv n_max (gmAt (ovfBucketBase d) U V w n_max h_space s.mem))
    (hp : ovfResolveIdx d <
        gmAt (ovfBucketBase d) U V w n_max h_space s.mem (gmQIdx (ovfBucketIdx d)) *
          slabSize n_max →
      ovfResolveSlabPtr d = slabPtrOf n_max (gmAt (ovfBucketBase d) U V w n_max h_space s.mem)
        (ovfBucketIdx d) (ovfResolveIdx d / slabSize n_max)) :
    let gm := gmAt (ovfBucketBase d) U V w n_max h_space s.mem
    let res := (Memory.spec 0).clientResult s (resolveOvfStepProg U V w n_max h_space d)
    res.1 = slotOf n_max gm (ovfBucketIdx d) (ovfResolveIdx d) ∧
    (ovfResolveIdx d + 1 < gm (gmQIdx (ovfBucketIdx d)) * slabSize n_max →
      res.2 = slabPtrOf n_max gm (ovfBucketIdx d) ((ovfResolveIdx d + 1) / slabSize n_max)) := by
  intro gm res
  dsimp only [gm, res, ovfBucketBase, ovfBucketIdx, ovfResolveIdx, ovfResolveSlabPtr] at *
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK : 0 < slabSize n_max := slabSize_pos n_max
  have hq_lt : 4 + 3 * d.1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
  have hslab := hinv.multi_slab hb_pos
  have hslot_slab : ∀ hj : d.2.1 < gmAt d.1.1 U V w n_max h_space s.mem (gmQIdx d.1.2) *
        slabSize n_max,
      d.2.2 * slabSize n_max + (slabSize n_max - 1 - d.2.1 % slabSize n_max) =
        slotOf n_max (gmAt d.1.1 U V w n_max h_space s.mem) d.1.2 d.2.1 := fun hj => by
    unfold slotOf; rw [ite_eq_right hb0, ite_eq_left hj, hp hj]
  unfold resolveOvfStepProg
  simp only [ovfBucketBase, ovfBucketIdx, ovfResolveIdx, ovfResolveSlabPtr, pure_bind]
  rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
    clientResult_readGMProg s hq_lt, show 4 + 3 * d.1.2 = gmQIdx d.1.2 from rfl]
  split_ifs with hj_slab hoff hj1_slab
  · have ⟨hdiv_eq, hmul_eq⟩ := div_succ_of_sub_mod_eq_zero hK hoff
    have hs_lt := (Nat.div_lt_iff_lt_mul hK).2 hj_slab
    have hs1_lt : d.2.1 / slabSize n_max + 1 <
        gmAt d.1.1 U V w n_max h_space s.mem (gmQIdx d.1.2) :=
      (Nat.mul_lt_mul_right hK).mp (hmul_eq ▸ hj1_slab)
    have habove_lt : gmSlabMetaBase n_max + 4 * d.2.2 + 3 < globalMetaLen n_max :=
      gmSlabAboveIdx_lt hb_pos (hp hj_slab ▸ hslab.ptr_lt_maxFullSlabs hb hs_lt)
    rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s habove_lt]
    refine ⟨hslot_slab hj_slab, fun _ => ?_⟩
    change gmAt d.1.1 U V w n_max h_space s.mem (gmSlabAboveIdx n_max d.2.2) = _
    rw [hp hj_slab, hslab.above_eq d.1.2 hb _ hs_lt hs1_lt, hdiv_eq]
  · exact ⟨hslot_slab hj_slab, fun h => (hj1_slab h).elim⟩
  · exact ⟨hslot_slab hj_slab, fun _ => by
      rw [hp hj_slab, div_succ_of_sub_mod_ne_zero hK hoff]; rfl⟩
  · obtain ⟨-, hr_cap⟩ := hinv.tailOffset_lt hb_pos hb hj_bc hj_slab
    have hptr_lt : gmTailPtrBase n_max + (d.1.2 * tailCapPerBucket n_max +
        (d.2.1 - gmAt d.1.1 U V w n_max h_space s.mem (gmQIdx d.1.2) * slabSize n_max)) <
        globalMetaLen n_max := gmTailPtrIdx_lt hb_pos hb hr_cap
    rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s hptr_lt]
    refine ⟨?_, fun h => by omega⟩
    unfold slotOf; rw [ite_eq_right hb0, ite_eq_right hj_slab]; rfl

/-- Shared `gmSlabAboveIdx` bound for `realizes_resolveOvfStepGen` (word-fit and index-in-range). -/
private theorem resolveOvfStep_aboveIdx_lt {n_max : ℕ} {gm : ℕ → ℕ} {b j p_cur : ℕ}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max) (hinv : SlotStoreInv n_max gm)
    (hp : j < gm (gmQIdx b) * slabSize n_max → p_cur = slabPtrOf n_max gm b (j / slabSize n_max))
    (hj1 : j + 1 < gm (gmQIdx b) * slabSize n_max) :
    gmSlabMetaBase n_max + 4 * p_cur + 3 < globalMetaLen n_max := by
  have hj := Nat.lt_of_succ_lt hj1
  have hs := (Nat.div_lt_iff_lt_mul (slabSize_pos n_max)).2 hj
  exact gmSlabAboveIdx_lt hb_pos (hp hj ▸ (hinv.multi_slab hb_pos).ptr_lt_maxFullSlabs hb hs)

theorem realizes_resolveOvfStepGen :
    Realizes .exact resolveOvfStepGenProg
      (WordEncoding.encode (α := (DictParams × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      ResolveOvfStepGenPre
      (fun _ _ => 0) := by
  realize [realizes_readGMGen]
  all_goals (
    rcases d with ⟨⟨dp, d1⟩, d2⟩
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1
    have hb_pos : 0 < bucketBits n_max := h.2.2.2.2.2
    have hK : 0 < slabSize n_max := slabSize_pos n_max
    simpDictParamsWith [resolveOvfStepGenPre_mk, ResolveOvfStepPre, resolveOvfStepGenProg_mk,
      ovfGenParams, ovfGenBase, ovfGenBucket, ovfBucketBase, ovfBucketIdx, ovfResolveIdx,
      ovfResolveSlabPtr]
    have hq_lt : 4 + 3 * d1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.1
  )
  · exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU hq_lt.le
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact h.1
  · exact hq_lt
  · rw [clientResult_readGMProg _ hq_lt]
    have hbc := bCount_le_n_max h.2.2.2.1 d1.2
    unfold bCount at hbc
    simp only [Nat.ne_of_gt hb_pos, ↓reduceIte, h.2.1, gmQIdx] at hbc
    exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)
  · exact Nat.ne_of_gt hK
  · have := Nat.mod_lt d2.1 hK; omega
  · rw [clientResult_readGMProg s hq_lt] at hc
    have hslab := h.2.2.2.1.multi_slab hb_pos
    have hp_lt : d2.2 < gmAt d1.1 U V w₀ n_max h_space s.mem 0 := by
      rw [h.2.2.2.2.1 hc, hslab.nslabs_eq]
      exact hslab.ptr_lt d1.2 h.2.1 _ ((Nat.div_lt_iff_lt_mul hK).2 hc)
    have h1 := Nat.mul_le_mul_right (slabSize n_max) hp_lt
    rw [Nat.add_one_mul] at h1
    have := Nat.mod_lt d2.1 hK
    have := h.2.2.2.1.multi_total_le hb_pos
    exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)
  · have hbc := bCount_le_n_max h.2.2.2.1 d1.2; have := h.2.2.1
    exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)
  · rw [clientResult_readGMProg s hq_lt] at hc
    exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU
      (resolveOvfStep_aboveIdx_lt hb_pos h.2.1 h.2.2.2.1 h.2.2.2.2.1 hc).le
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact h.1
  · rw [clientResult_readGMProg s hq_lt] at hc
    exact resolveOvfStep_aboveIdx_lt hb_pos h.2.1 h.2.2.2.1 h.2.2.2.2.1 hc
  · omega
  · rw [clientResult_readGMProg s hq_lt] at hc ⊢
    exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU
      (gmTailPtrIdx_lt hb_pos h.2.1
        (h.2.2.2.1.tailOffset_lt hb_pos h.2.1 h.2.2.1 hc).2).le
  · exact h.1
  · rw [clientResult_readGMProg s hq_lt] at hc ⊢
    exact gmTailPtrIdx_lt hb_pos h.2.1 (h.2.2.2.1.tailOffset_lt hb_pos h.2.1 h.2.2.1 hc).2
  · rw [clientState_readGMProg]
    rw [clientResult_readGMProg s hq_lt] at hc ⊢
    obtain ⟨hr_lt, hr_cap⟩ := h.2.2.2.1.tailOffset_lt hb_pos h.2.1 h.2.2.1 hc
    have hptr_lt : gmTailPtrBase n_max + (d1.2 * tailCapPerBucket n_max +
        (d2.1 - gmAt d1.1 U V w₀ n_max h_space s.mem (4 + 3 * d1.2) * slabSize n_max)) <
        globalMetaLen n_max := gmTailPtrIdx_lt hb_pos h.2.1 hr_cap
    rw [clientResult_readGMProg _ hptr_lt]
    have htail := h.2.2.2.1.multi_tail hb_pos
    have ht_lt : gmAt d1.1 U V w₀ n_max h_space s.mem (gmTailPtrIdx n_max d1.2
        (d2.1 - gmAt d1.1 U V w₀ n_max h_space s.mem (4 + 3 * d1.2) * slabSize n_max)) <
        gmAt d1.1 U V w₀ n_max h_space s.mem 1 := by
      rw [htail.ntails_eq]; exact htail.ptr_lt d1.2 h.2.1 _ hr_lt
    have htot := h.2.2.2.1.multi_total_le hb_pos
    have hn_pos := one_le_n_max_of_bucketBits_pos hb_pos
    wram_omega [ht_lt]

/-! ## Section 2: Phase 2 Overflow Search (`ovfStepProg`, `ovfLoopProg`, `searchOverflowProg`) -/

/-- Bucket location `(base, b)` in a query-prefixed input `(((base, b), q_target), extra)`. -/
abbrev ovfQueryLoc {α : Type} (x : ((ℕ × ℕ) × ℕ) × α) : ℕ × ℕ := x.1.1

/-- Base address `base` in a query-prefixed input `(((base, b), q_target), extra)`. -/
abbrev ovfQueryBase {α : Type} (x : ((ℕ × ℕ) × ℕ) × α) : ℕ := x.1.1.1

/-- Bucket index `b` in a query-prefixed input `(((base, b), q_target), extra)`. -/
abbrev ovfQueryBucket {α : Type} (x : ((ℕ × ℕ) × ℕ) × α) : ℕ := x.1.1.2

/-- Target quotient `q_target` in a query-prefixed input `(((base, b), q_target), extra)`. -/
abbrev ovfQueryQuot {α : Type} (x : ((ℕ × ℕ) × ℕ) × α) : ℕ := x.1.2

/-- Cursor `(j, p_cur)` in an overflow-search accumulator
`((((j, p_cur), found), j_found), phys_found)`. -/
abbrev ovfAccCursor (acc : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : ℕ × ℕ := acc.1.1.1

/-- Current logical slot index `j` in an overflow-search accumulator. -/
abbrev ovfAccSlotIdx (acc : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : ℕ := acc.1.1.1.1

/-- Current slab pointer `p_cur` in an overflow-search accumulator. -/
abbrev ovfAccSlabPtr (acc : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : ℕ := acc.1.1.1.2

/-- Found flag `found` in an overflow-search accumulator. -/
abbrev ovfAccFound (acc : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : ℕ := acc.1.1.2

/-- Matched logical slot index `j_found` in an overflow-search accumulator. -/
abbrev ovfAccMatchIdx (acc : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : ℕ := acc.1.2

/-- Matched physical slot `phys_found` in an overflow-search accumulator. -/
abbrev ovfAccPhys (acc : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : ℕ := acc.2

/-- Bucket location `(base, b)` in a parameter-free overflow-search step input
`((dp, ((base, b), q_target)), acc)`. -/
abbrev ovfStepGenLoc {β : Type} (x : (DictParams × ((ℕ × ℕ) × ℕ)) × β) : ℕ × ℕ := x.1.2.1

/-- Base address `base` in a parameter-free overflow-search step input
`((dp, ((base, b), q_target)), acc)`. -/
abbrev ovfStepGenBase {β : Type} (x : (DictParams × ((ℕ × ℕ) × ℕ)) × β) : ℕ := x.1.2.1.1

/-- Target quotient `q_target` in a parameter-free overflow-search step input
`((dp, ((base, b), q_target)), acc)`. -/
abbrev ovfStepGenQuot {β : Type} (x : (DictParams × ((ℕ × ℕ) × ℕ)) × β) : ℕ := x.1.2.2

/-- Parameter-free step of Phase 2 overflow search (`x = ((dp, ((base, b), q_target)),
((((j, p_cur), found), j_found), phys_found))`). -/
@[expose] def ovfStepGenProg
    (x : (DictParams × ((ℕ × ℕ) × ℕ)) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) :
    Memory.Prog ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) :=
  let dp := ovfGenParams x
  let acc := x.2
  do
    let pair ← resolveOvfStepGenProg ((dp, ovfStepGenLoc x), ovfAccCursor acc)
    let q_val ← readQuotGenProg (dp, (ovfStepGenBase x, pair.1))
    let j1 ← pure (ovfAccSlotIdx acc + 1)
    let z0 ← pure 0
    if ovfAccFound acc = z0 then
      if q_val = ovfStepGenQuot x then do
        let z1 ← pure 1
        pure ((((j1, pair.2), z1), ovfAccSlotIdx acc), pair.1)
      else
        pure ((((j1, pair.2), z0), ovfAccMatchIdx acc), ovfAccPhys acc)
    else
      pure ((((j1, pair.2), ovfAccFound acc), ovfAccMatchIdx acc), ovfAccPhys acc)

/-- One step of Phase 2 overflow search (`x = (((base, b), q_target), ((((j, p_cur), found),
j_found), phys_found))`). Resolves `(phys, p_next) ← resolveOvfStepProg` and reads `q_val` at
`phys`, recording the first matching slot `(1, j, phys)` when `found = 0 ∧ q_val = q_target`. -/
@[expose] def ovfStepProg (U V w n_max h_space : ℕ)
    (x : ((ℕ × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) :
    Memory.Prog ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) :=
  let acc := x.2
  do
    let pair ← resolveOvfStepProg U V w n_max h_space (ovfQueryLoc x, ovfAccCursor acc)
    let q_val ← readQuotProg U w n_max h_space (ovfQueryBase x, pair.1)
    let j1 ← pure (ovfAccSlotIdx acc + 1)
    let z0 ← pure 0
    if ovfAccFound acc = z0 then
      if q_val = ovfQueryQuot x then do
        let z1 ← pure 1
        pure ((((j1, pair.2), z1), ovfAccSlotIdx acc), pair.1)
      else
        pure ((((j1, pair.2), z0), ovfAccMatchIdx acc), ovfAccPhys acc)
    else
      pure ((((j1, pair.2), ovfAccFound acc), ovfAccMatchIdx acc), ovfAccPhys acc)

@[simp]
theorem ovfStepGenProg_mk (U V w n_max h_space : ℕ)
    (x1 : (ℕ × ℕ) × ℕ) (x2 : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) :
    ovfStepGenProg ((mkDictParams U V w n_max h_space, x1), x2) =
      ovfStepProg U V w n_max h_space (x1, x2) := by
  simp only [ovfStepGenProg, ovfStepProg, ovfGenParams, ovfStepGenLoc, ovfStepGenBase,
    ovfStepGenQuot, ovfQueryLoc, ovfQueryBase, ovfQueryQuot, ovfAccCursor, ovfAccSlotIdx,
    ovfAccFound, ovfAccMatchIdx, ovfAccPhys, resolveOvfStepGenProg_mk, readQuotGenProg_mk]

theorem memoryCost_ovfStepGenProg_pos
    (x : (DictParams × ((ℕ × ℕ) × ℕ)) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (ovfStepGenProg x) s := by
  unfold ovfStepGenProg
  simp only [← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind]
  have := memoryCost_resolveOvfStepGenProg_pos
    ((ovfGenParams x, ovfStepGenLoc x), ovfAccCursor x.2) s
  omega

theorem clientState_ovfStepProg (U V w n_max h_space : ℕ)
    (x : ((ℕ × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (ovfStepProg U V w n_max h_space x) = s := by
  unfold ovfStepProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_resolveOvfStepProg,
    StateTransitionSpec.clientState_bind, clientState_readQuotProg]
  split_ifs <;> rfl

theorem memoryCost_ovfStepProg_le (U V w n_max h_space : ℕ)
    (x : ((ℕ × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) (s : Memory.State) :
    memoryCost (ovfStepProg U V w n_max h_space x) s ≤ 6 := by
  unfold ovfStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind, clientState_resolveOvfStepProg, memoryCost_bind]
  have := memoryCost_resolveOvfStepProg_le U V w n_max h_space (ovfQueryLoc x, ovfAccCursor x.2) s
  split_ifs <;> · change memoryCost (resolveOvfStepProg _ _ _ _ _ _) s + (2 + 0) ≤ 6; omega

/-- Precondition for `ovfStepProg`. -/
@[expose] def OvfStepPre (U V w₀ n_max h_space w : ℕ)
    (x : ((ℕ × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  ResolveOvfStepPre U V w₀ n_max h_space w (ovfQueryLoc x, ovfAccCursor x.2) s

/-- Parameter-free precondition for `ovfStepGenProg`. -/
@[expose] def OvfStepGenPre (w : ℕ)
    (x : (DictParams × ((ℕ × ℕ) × ℕ)) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  ResolveOvfStepGenPre w ((ovfGenParams x, ovfStepGenLoc x), ovfAccCursor x.2) s

@[simp]
theorem ovfStepGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (x1 : (ℕ × ℕ) × ℕ) (x2 : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    OvfStepGenPre w ((mkDictParams U V w₀ n_max h_space, x1), x2) s ↔
      OvfStepPre U V w₀ n_max h_space w (x1, x2) s := Iff.rfl

theorem clientResult_ovfStepProg {U V w n_max h_space : ℕ}
    {x : ((ℕ × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)} (s : Memory.State)
    (hb_pos : 0 < bucketBits n_max)
    (hb : ovfQueryBucket x < numBuckets n_max)
    (hj_bc : ovfAccSlotIdx x.2 <
      bCount n_max (gmAt (ovfQueryBase x) U V w n_max h_space s.mem) (ovfQueryBucket x))
    (hinv : SlotStoreInv n_max (gmAt (ovfQueryBase x) U V w n_max h_space s.mem))
    (hp : ovfAccSlotIdx x.2 <
        gmAt (ovfQueryBase x) U V w n_max h_space s.mem (gmQIdx (ovfQueryBucket x)) *
          slabSize n_max →
      ovfAccSlabPtr x.2 = slabPtrOf n_max (gmAt (ovfQueryBase x) U V w n_max h_space s.mem)
        (ovfQueryBucket x) (ovfAccSlotIdx x.2 / slabSize n_max)) :
    let gm := gmAt (ovfQueryBase x) U V w n_max h_space s.mem
    let pair := (Memory.spec 0).clientResult s
      (resolveOvfStepProg U V w n_max h_space (ovfQueryLoc x, ovfAccCursor x.2))
    let phys := slotOf n_max gm (ovfQueryBucket x) (ovfAccSlotIdx x.2)
    let q_val := quotAt (ovfQueryBase x) U w n_max h_space s.mem phys
    (Memory.spec 0).clientResult s (ovfStepProg U V w n_max h_space x) =
      (if ovfAccFound x.2 = 0 then
        if q_val = ovfQueryQuot x then
          ((((ovfAccSlotIdx x.2 + 1, pair.2), 1), ovfAccSlotIdx x.2), phys)
        else
          ((((ovfAccSlotIdx x.2 + 1, pair.2), 0), ovfAccMatchIdx x.2), ovfAccPhys x.2)
       else
         ((((ovfAccSlotIdx x.2 + 1, pair.2), ovfAccFound x.2), ovfAccMatchIdx x.2),
           ovfAccPhys x.2)) ∧
    (ovfAccSlotIdx x.2 + 1 < gm (gmQIdx (ovfQueryBucket x)) * slabSize n_max →
      pair.2 = slabPtrOf n_max gm (ovfQueryBucket x)
        ((ovfAccSlotIdx x.2 + 1) / slabSize n_max)) := by
  intro gm pair phys q_val
  dsimp only [gm, pair, phys, q_val, ovfQueryLoc, ovfQueryBase, ovfQueryBucket, ovfQueryQuot,
    ovfAccCursor, ovfAccSlotIdx, ovfAccSlabPtr, ovfAccFound, ovfAccMatchIdx, ovfAccPhys] at *
  have hres := clientResult_resolveOvfStepProg (d := (x.1.1, x.2.1.1.1))
    s hb_pos hb hj_bc hinv hp
  dsimp only [ovfBucketBase, ovfBucketIdx, ovfResolveIdx] at hres
  have hphys_lt : slotOf n_max (gmAt x.1.1.1 U V w n_max h_space s.mem) x.1.1.2 x.2.1.1.1.1 <
      n_max := (slotOf_lt_and_injective hinv).1 x.1.1.2 hb x.2.1.1.1.1 hj_bc
  unfold ovfStepProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientResult_bind, clientState_resolveOvfStepProg,
    StateTransitionSpec.clientResult_bind, clientState_readQuotProg]
  rw [show ((Memory.spec 0).clientResult s
      (resolveOvfStepProg U V w n_max h_space (x.1.1, x.2.1.1.1))).1 =
      slotOf n_max (gmAt x.1.1.1 U V w n_max h_space s.mem) x.1.1.2 x.2.1.1.1.1 from hres.1,
    clientResult_readQuotProg s hphys_lt]
  split_ifs <;> exact ⟨rfl, hres.2⟩

theorem realizes_ovfStepGen :
    Realizes .exact ovfStepGenProg
      (WordEncoding.encode (α := (DictParams × ((ℕ × ℕ) × ℕ)) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ))
      OvfStepGenPre
      (fun _ _ => 0) := by
  realize [realizes_resolveOvfStepGen, realizes_readQuotGen]
  all_goals (
    rcases d with ⟨⟨dp, d1⟩, d2⟩
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1
    have hb_pos : 0 < bucketBits n_max := h.2.2.2.2.2
    simpDictParamsWith [ovfStepGenPre_mk, OvfStepPre, ovfStepGenProg_mk,
      resolveOvfStepGenPre_mk, ResolveOvfStepPre, resolveOvfStepGenProg_mk,
      ovfGenParams, ovfGenBase, ovfGenBucket, ovfStepGenLoc, ovfStepGenBase, ovfStepGenQuot,
      ovfBucketBase, ovfBucketIdx, ovfResolveIdx, ovfResolveSlabPtr,
      ovfQueryLoc, ovfQueryBase, ovfQueryQuot, ovfAccCursor, ovfAccSlotIdx, ovfAccFound,
      ovfAccMatchIdx, ovfAccPhys]
  )
  · exact h
  · exact h.1
  · rw [(clientResult_resolveOvfStepProg (d := (d1.1, d2.1.1.1)) s
      hb_pos h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1).1]
    exact (slotOf_lt_and_injective h.2.2.2.1).1 d1.1.2 h.2.1 d2.1.1.1.1 h.2.2.1
  · have hbc := bCount_le_n_max h.2.2.2.1 d1.1.2
    have := h.2.2.1
    exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)
  · exact fits_const_of_dictEnv h.1 (by decide)

/-- Loop context `d.1.1` in an overflow-loop input `((ctx, acc), fuel)`. -/
abbrev ovfLoopCtx {α β : Type} (d : (α × β) × ℕ) : α := d.1.1

/-- Initial accumulator `d.1.2` in an overflow-loop input `((ctx, acc), fuel)`. -/
abbrev ovfLoopAcc {α β : Type} (d : (α × β) × ℕ) : β := d.1.2

/-- Parameter-free wrapper for `iterate ovfStepGenProg` matching `Realizes.iterate₀`. -/
@[expose] def ovfLoopGenProg
    (d : ((DictParams × ((ℕ × ℕ) × ℕ)) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) × ℕ) :
    Memory.Prog ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) :=
  iterate ovfStepGenProg (ovfLoopCtx d) d.2 (ovfLoopAcc d)

/-- Wrapper for `iterate (ovfStepProg ...)` matching `Realizes.iterate₀`. -/
@[expose] def ovfLoopProg (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) × ℕ) :
    Memory.Prog ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) :=
  iterate (ovfStepProg U V w n_max h_space) (ovfLoopCtx d) d.2 (ovfLoopAcc d)

@[simp]
theorem iterate_ovfStepGenProg_mk (U V w n_max h_space : ℕ)
    (ctx : (ℕ × ℕ) × ℕ) (m : ℕ) (acc : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) :
    iterate ovfStepGenProg (mkDictParams U V w n_max h_space, ctx) m acc =
      iterate (ovfStepProg U V w n_max h_space) ctx m acc :=
  iterate_congr (fun a => ovfStepGenProg_mk U V w n_max h_space ctx a) m acc

@[simp]
theorem ovfLoopGenProg_mk (U V w n_max h_space : ℕ)
    (ctx : (ℕ × ℕ) × ℕ) (acc : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) (m : ℕ) :
    ovfLoopGenProg (((mkDictParams U V w n_max h_space, ctx), acc), m) =
      ovfLoopProg U V w n_max h_space ((ctx, acc), m) :=
  iterate_ovfStepGenProg_mk U V w n_max h_space ctx m acc

@[simp]
theorem iterationSafe_ovfStepGenProg_mk (U V w₀ n_max h_space w : ℕ)
    (ctx : (ℕ × ℕ) × ℕ) (m : ℕ) (acc : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    iterationSafe ovfStepGenProg OvfStepGenPre w
      (mkDictParams U V w₀ n_max h_space, ctx) m acc s ↔
    iterationSafe (ovfStepProg U V w₀ n_max h_space) (OvfStepPre U V w₀ n_max h_space)
      w ctx m acc s :=
  iterationSafe_congr (fun a => ovfStepGenProg_mk U V w₀ n_max h_space ctx a)
    (fun a t => ovfStepGenPre_mk U V w₀ n_max h_space w ctx a t) m acc s

theorem realizes_ovfLoopGen :
    Realizes .exact ovfLoopGenProg
      (WordEncoding.encode (α := ((DictParams × ((ℕ × ℕ) × ℕ)) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) × ℕ))
      (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ))
      (fun w d s =>
        iterationSafe ovfStepGenProg OvfStepGenPre w (ovfLoopCtx d) d.2 (ovfLoopAcc d) s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ)))
    (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ))
    realizes_ovfStepGen
    memoryCost_ovfStepGenProg_pos

open Classical in
/-- Structural induction lemma for `iterate (ovfStepProg ...)` over `m` overflow slots
`j .. j + m - 1`. -/
theorem iterate_ovfStepProg_spec {U V w₀ n_max h_space w base b q_target : ℕ} {s : Memory.State}
    (hb_pos : 0 < bucketBits n_max)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb : b < numBuckets n_max)
    (hinv : SlotStoreInv n_max (gmAt base U V w₀ n_max h_space s.mem)) :
    ∀ m j p_cur found j_found phys_found,
      j + m ≤ bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b →
      (j < gmAt base U V w₀ n_max h_space s.mem (gmQIdx b) * slabSize n_max →
        p_cur = slabPtrOf n_max (gmAt base U V w₀ n_max h_space s.mem) b (j / slabSize n_max)) →
      let prog := iterate (ovfStepProg U V w₀ n_max h_space) ((base, b), q_target) m
        ((((j, p_cur), found), j_found), phys_found)
      (Memory.spec 0).clientState s prog = s ∧
      memoryCost prog s ≤ 6 * m ∧
      iterationSafe (ovfStepProg U V w₀ n_max h_space)
        (OvfStepPre U V w₀ n_max h_space) w ((base, b), q_target) m
        ((((j, p_cur), found), j_found), phys_found) s ∧
      (let res := (Memory.spec 0).clientResult s prog
       if found = 0 then
         if ∃ k, j ≤ k ∧ k < j + m ∧
             quotAt base U w₀ n_max h_space s.mem
               (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b k) = q_target then
           ovfAccFound res = 1 ∧ j ≤ ovfAccMatchIdx res ∧ ovfAccMatchIdx res < j + m ∧
           quotAt base U w₀ n_max h_space s.mem
             (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b (ovfAccMatchIdx res)) =
             q_target ∧
           res.2 = slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b (ovfAccMatchIdx res)
         else
           ovfAccFound res = 0
       else
         ovfAccFound res = found ∧ ovfAccMatchIdx res = j_found ∧ res.2 = phys_found) := by
  intro m
  induction m with
  | zero =>
    intro j p_cur found j_found phys_found _ _ prog
    refine ⟨rfl, by simp [prog, iterate], trivial, ?_⟩
    dsimp only [prog, iterate, StateTransitionSpec.clientResult, StateTransitionSpec.runClient]
    split_ifs with hf hex
    · obtain ⟨k, hk1, hk2, _⟩ := hex; omega
    · exact hf
    · exact ⟨rfl, rfl, rfl⟩
  | succ m ih =>
    intro j p_cur found j_found phys_found hjm hp prog
    dsimp only [prog] at *
    have hj_bc : j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b := by omega
    have hpre : OvfStepPre U V w₀ n_max h_space w
        (((base, b), q_target), ((((j, p_cur), found), j_found), phys_found)) s :=
      ⟨henv, hb, hj_bc, hinv, hp, hb_pos⟩
    obtain ⟨hstep_res, hp_next⟩ :=
      clientResult_ovfStepProg
        (x := (((base, b), q_target), ((((j, p_cur), found), j_found), phys_found)))
        s hb_pos hb hj_bc hinv hp
    dsimp only [ovfQueryLoc, ovfQueryBase, ovfQueryBucket, ovfQueryQuot, ovfAccCursor,
      ovfAccSlotIdx, ovfAccFound, ovfAccMatchIdx, ovfAccPhys] at hstep_res hp_next
    have hstep_st := clientState_ovfStepProg U V w₀ n_max h_space
      (((base, b), q_target), ((((j, p_cur), found), j_found), phys_found)) s
    have hstep_cost := memoryCost_ovfStepProg_le U V w₀ n_max h_space
      (((base, b), q_target), ((((j, p_cur), found), j_found), phys_found)) s
    set pair := (Memory.spec 0).clientResult s
      (resolveOvfStepProg U V w₀ n_max h_space ((base, b), (j, p_cur)))
    set phys := slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j
    set q_val := quotAt base U w₀ n_max h_space s.mem phys
    have hjm' : (j + 1) + m ≤ bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b := by omega
    unfold iterate
    rw [iterationSafe, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      memoryCost_bind_of_clientState_eq hstep_st, hstep_st, hstep_res]
    by_cases hf0 : found = 0
    · by_cases hmatch : q_val = q_target
      · rw [ite_eq_left hf0, ite_eq_left hmatch]
        have hih := ih (j + 1) pair.2 1 j phys hjm' hp_next
        refine ⟨hih.1, by have := hih.2.1; omega, ⟨hpre, hih.2.2.1⟩, ?_⟩
        have hih_res := hih.2.2.2
        rw [ite_eq_right (by decide : (1 : ℕ) ≠ 0)] at hih_res
        rw [ite_eq_left hf0, ite_eq_left ⟨j, le_rfl, by omega, hmatch⟩]
        exact ⟨hih_res.1, by rw [hih_res.2.1], by rw [hih_res.2.1]; omega,
          by rw [hih_res.2.1]; exact hmatch, by rw [hih_res.2.1, hih_res.2.2]⟩
      · rw [ite_eq_left hf0, ite_eq_right hmatch]
        have hih := ih (j + 1) pair.2 0 j_found phys_found hjm' hp_next
        refine ⟨hih.1, by have := hih.2.1; omega, ⟨hpre, hih.2.2.1⟩, ?_⟩
        have hih_res := hih.2.2.2
        rw [ite_eq_left rfl] at hih_res
        rw [ite_eq_left hf0]
        split_ifs at hih_res with hex'
        · obtain ⟨k, hk1, hk2, hqk⟩ := hex'
          split_ifs with hex
          · exact ⟨hih_res.1, by omega, by omega, hih_res.2.2.2.1, hih_res.2.2.2.2⟩
          · exact (hex ⟨k, by omega, by omega, hqk⟩).elim
        · rw [ite_eq_right fun ⟨k, hk1, hk2, hqk⟩ =>
            (eq_or_lt_of_le hk1).elim (fun h => hmatch (by rwa [← h] at hqk))
              (fun hlt => hex' ⟨k, by omega, by omega, hqk⟩)]
          exact hih_res
    · rw [ite_eq_right hf0]
      have hih := ih (j + 1) pair.2 found j_found phys_found hjm' hp_next
      exact ⟨hih.1, by have := hih.2.1; omega, ⟨hpre, hih.2.2.1⟩,
        by simpa only [ite_eq_right hf0] using hih.2.2.2⟩

/-- Base address `d.2.1` in an overflow-init call `(dp, (base, b))`. -/
abbrev ovfInitBase (d : DictParams × (ℕ × ℕ)) : ℕ := d.2.1

/-- Bucket index `d.2.2` in an overflow-init call `(dp, (base, b))`. -/
abbrev ovfInitBucket (d : DictParams × (ℕ × ℕ)) : ℕ := d.2.2

/-- Parameter-free helper initializing `(p_init, fuel)` for Phase 2 overflow search
(`d = (dp, (base, b))`). -/
@[expose] def initOvfSearchGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let q_idx ← pure (4 + 3 * ovfInitBucket d)
  let q_b ← readGMGenProg (d.1, (ovfInitBase d, q_idx))
  let r_idx ← pure (q_idx + 1)
  let r_b ← readGMGenProg (d.1, (ovfInitBase d, r_idx))
  let qK ← pure (q_b * dpSlabSize d.1)
  let c ← pure (qK + r_b)
  let cap ← pure (dpMinCap d.1)
  let z0 ← pure 0
  if cap < c then do
    let fuel ← pure (c - cap)
    if cap < qK then do
      let dir_idx ← pure (dpGmSlabDirBase d.1 + ovfInitBucket d * dpDirSlabs d.1 +
        dpDirSlabsSubOne d.1)
      let p_prev ← readGMGenProg (d.1, (ovfInitBase d, dir_idx))
      let abv_idx ← pure (dpGmSlabMetaBase d.1 + 4 * p_prev + 3)
      let p_init ← readGMGenProg (d.1, (ovfInitBase d, abv_idx))
      pure (p_init, fuel)
    else
      pure (z0, fuel)
  else
    pure (z0, z0)

/-- Helper initializing `(p_init, fuel)` for Phase 2 overflow search (`d = (base, b)`). -/
@[expose] def initOvfSearchProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog (ℕ × ℕ) := do
  let q_idx ← pure (4 + 3 * d.2)
  let q_b ← readGMProg U V w n_max h_space (d.1, q_idx)
  let r_idx ← pure (q_idx + 1)
  let r_b ← readGMProg U V w n_max h_space (d.1, r_idx)
  let qK ← pure (q_b * slabSize n_max)
  let c ← pure (qK + r_b)
  let cap ← pure (min n_max (effBucketCap n_max))
  let z0 ← pure 0
  if cap < c then do
    let fuel ← pure (c - cap)
    if cap < qK then do
      let dir_idx ← pure (gmSlabDirBase n_max + d.2 * dirSlabsPerBucket n_max +
        (dirSlabsPerBucket n_max - 1))
      let p_prev ← readGMProg U V w n_max h_space (d.1, dir_idx)
      let abv_idx ← pure (gmSlabMetaBase n_max + 4 * p_prev + 3)
      let p_init ← readGMProg U V w n_max h_space (d.1, abv_idx)
      pure (p_init, fuel)
    else
      pure (z0, fuel)
  else
    pure (z0, z0)

@[simp]
theorem initOvfSearchGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    initOvfSearchGenProg (mkDictParams U V w n_max h_space, d) =
      initOvfSearchProg U V w n_max h_space d := by
  simp only [initOvfSearchGenProg, initOvfSearchProg, ovfInitBase, ovfInitBucket,
    p_slabSize_mk, p_minCap_mk, p_gmSlabDirBase_mk, p_dirSlabs_mk, p_dirSlabsSubOne_mk,
    p_gmSlabMetaBase_mk, readGMGenProg_mk]

theorem clientState_initOvfSearchProg (U V w n_max h_space : ℕ)
    (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (initOvfSearchProg U V w n_max h_space d) = s := by
  unfold initOvfSearchProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
    StateTransitionSpec.clientState_bind, clientState_readGMProg]
  split_ifs <;> first
    | (rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
        StateTransitionSpec.clientState_bind, clientState_readGMProg]; rfl)
    | rfl

theorem memoryCost_initOvfSearchProg_le (U V w n_max h_space : ℕ)
    (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (initOvfSearchProg U V w n_max h_space d) s ≤ 8 := by
  unfold initOvfSearchProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind, clientState_readGMProg, memoryCost_readGMProg,
    memoryCost_bind, clientState_readGMProg, memoryCost_readGMProg]
  split_ifs <;>
    simp only [memoryCost_bind, memoryCost_readGMProg, memoryCost_pure] <;>
    omega

theorem dirSlabsPerBucket_pos_of_pos {n_max : ℕ} (hb : 0 < bucketBits n_max) :
    0 < dirSlabsPerBucket n_max := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hS := two_le_slabScale n_max
  unfold dirSlabsPerBucket
  rw [ite_eq_right hb0]
  omega

/-- In a bucket whose full slabs hold at least `effBucketCap` items, the last directory slot is
in range of `GlobalMeta`, it stores the bucket's last directory slab, and that slab is below the
slab-pool capacity. The slot index is stated unfolded, as the overflow search reads it. -/
theorem SlotStoreInv.lastDirSlab_ptr {n_max : ℕ} {gm : ℕ → ℕ} (hinv : SlotStoreInv n_max gm)
    (hb_pos : 0 < bucketBits n_max) {b : ℕ} (hb : b < numBuckets n_max)
    (hcap : effBucketCap n_max ≤ gm (gmQIdx b) * slabSize n_max) :
    gmSlabDirBase n_max + b * dirSlabsPerBucket n_max + (dirSlabsPerBucket n_max - 1) <
        globalMetaLen n_max ∧
      gm (gmSlabDirBase n_max + b * dirSlabsPerBucket n_max + (dirSlabsPerBucket n_max - 1)) =
        slabPtrOf n_max gm b (dirSlabsPerBucket n_max - 1) ∧
      slabPtrOf n_max gm b (dirSlabsPerBucket n_max - 1) < maxFullSlabs n_max := by
  have hdir_pos := dirSlabsPerBucket_pos_of_pos hb_pos
  have hs_last_dir : dirSlabsPerBucket n_max - 1 < dirSlabsPerBucket n_max := by omega
  rw [effBucketCap_eq_dirSlabs_mul_slabSize hb_pos] at hcap
  have hdir_le_q : dirSlabsPerBucket n_max ≤ gm (gmQIdx b) :=
    Nat.le_of_mul_le_mul_right hcap (slabSize_pos n_max)
  have hs_last_q : dirSlabsPerBucket n_max - 1 < gm (gmQIdx b) := by omega
  have hslab := hinv.multi_slab hb_pos
  exact ⟨gmSlabDirIdx_lt hb_pos hb hs_last_dir, hslab.dir_eq b hb _ hs_last_q hs_last_dir,
    hslab.ptr_lt_maxFullSlabs hb hs_last_q⟩

theorem clientResult_initOvfSearchProg {U V w n_max h_space : ℕ}
    {d : ℕ × ℕ} (s : Memory.State)
    (hb_pos : 0 < bucketBits n_max)
    (hb : d.2 < numBuckets n_max)
    (hinv : SlotStoreInv n_max (gmAt d.1 U V w n_max h_space s.mem)) :
    let gm := gmAt d.1 U V w n_max h_space s.mem
    let res := (Memory.spec 0).clientResult s (initOvfSearchProg U V w n_max h_space d)
    res.2 = bCount n_max gm d.2 - effBucketCap n_max ∧
    (effBucketCap n_max < bCount n_max gm d.2 →
      effBucketCap n_max < gm (gmQIdx d.2) * slabSize n_max →
      res.1 = slabPtrOf n_max gm d.2 (effBucketCap n_max / slabSize n_max)) := by
  intro gm res
  dsimp only [gm, res] at *
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK := slabSize_pos n_max
  have hq_lt : 4 + 3 * d.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
  have hr_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
  have hbc_eq : gmAt d.1 U V w n_max h_space s.mem (4 + 3 * d.2) * slabSize n_max +
      gmAt d.1 U V w n_max h_space s.mem (4 + 3 * d.2 + 1) =
      bCount n_max (gmAt d.1 U V w n_max h_space s.mem) d.2 := by
    unfold bCount gmQIdx gmRIdx; simp only [hb0, ↓reduceIte, hb]
  have hbc_le := bCount_le_n_max hinv d.2
  unfold initOvfSearchProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
    clientResult_readGMProg s hq_lt, StateTransitionSpec.clientResult_bind,
    clientState_readGMProg, clientResult_readGMProg s hr_lt, hbc_eq]
  split_ifs with hcap_c hcap_q
  · have hcap_eq : min n_max (effBucketCap n_max) = effBucketCap n_max := by omega
    rw [hcap_eq] at hcap_c hcap_q ⊢
    have hcap_dir := effBucketCap_eq_dirSlabs_mul_slabSize hb_pos
    have hdir_lt_q : dirSlabsPerBucket n_max <
        gmAt d.1 U V w n_max h_space s.mem (4 + 3 * d.2) :=
      (Nat.mul_lt_mul_right hK).mp (by rwa [← hcap_dir])
    obtain ⟨hdir_lt, hp_eq, hp_lt⟩ := hinv.lastDirSlab_ptr hb_pos hb hcap_q.le
    have habv_lt : gmSlabMetaBase n_max + 4 * slabPtrOf n_max (gmAt d.1 U V w n_max h_space s.mem)
        d.2 (dirSlabsPerBucket n_max - 1) + 3 < globalMetaLen n_max :=
      gmSlabAboveIdx_lt hb_pos hp_lt
    rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s hdir_lt, hp_eq, StateTransitionSpec.clientResult_bind,
      clientState_readGMProg, clientResult_readGMProg s habv_lt]
    refine ⟨rfl, fun _ _ => ?_⟩
    have hdir_pos := dirSlabsPerBucket_pos_of_pos hb_pos
    change gmAt d.1 U V w n_max h_space s.mem (gmSlabAboveIdx n_max _) = _
    rw [(hinv.multi_slab hb_pos).above_eq d.2 hb _ (by wram_omega) (by wram_omega),
      Nat.sub_add_cancel hdir_pos, hcap_dir, Nat.mul_div_cancel _ hK]
  · refine ⟨by change _ - _ = _ - _; omega, fun _ hq => by wram_omega [hq]⟩
  · refine ⟨by change 0 = _ - _; omega, fun hc _ => by omega⟩

/-- Shared `gmSlabAboveIdx` bound on the last directory slab read by `initOvfSearchProg`. -/
private theorem initOvfSearch_aboveIdx_lt {U V w₀ n_max h_space base b : ℕ} {s : Memory.State}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (hinv : SlotStoreInv n_max (gmAt base U V w₀ n_max h_space s.mem))
    (hc : min n_max (effBucketCap n_max) <
      (Memory.spec 0).clientResult s (readGMProg U V w₀ n_max h_space (base, 4 + 3 * b)) *
        slabSize n_max) :
    gmSlabMetaBase n_max + 4 * (Memory.spec 0).clientResult s
        (readGMProg U V w₀ n_max h_space (base,
          gmSlabDirBase n_max + b * dirSlabsPerBucket n_max + (dirSlabsPerBucket n_max - 1))) +
        3 < globalMetaLen n_max := by
  have hq_lt : 4 + 3 * b < globalMetaLen n_max := gmQIdx_lt hb_pos hb
  rw [clientResult_readGMProg s hq_lt] at hc
  have hbc := bCount_le_n_max hinv b
  unfold bCount at hbc
  simp only [Nat.ne_of_gt hb_pos, ↓reduceIte, hb, gmQIdx] at hbc
  have hcap_le : effBucketCap n_max ≤
      gmAt base U V w₀ n_max h_space s.mem (4 + 3 * b) * slabSize n_max := by omega
  obtain ⟨hdir_lt, hp_eq, hp_lt⟩ := hinv.lastDirSlab_ptr hb_pos hb hcap_le
  rw [clientResult_readGMProg s hdir_lt, hp_eq]
  exact gmSlabAboveIdx_lt hb_pos hp_lt

theorem realizes_initOvfSearchGen :
    Realizes .exact initOvfSearchGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d s => DictEnvGen w d.1 (ovfInitBase d) ∧
        ovfInitBucket d < numBuckets (dpNMax d.1) ∧
        SlotStoreInv (dpNMax d.1)
          (gmAt (ovfInitBase d) (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem) ∧
        0 < bucketBits (dpNMax d.1))
      (fun _ _ => 0) := by
  realizeDictWith [initOvfSearchGenProg_mk, ovfInitBase, ovfInitBucket] using [realizes_readGMGen]
  all_goals (
    have hb_pos := h.2.2.2
    have hq_lt : 4 + 3 * d.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.1
    have hr_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos h.2.1
    have hdir_lt := gmSlabDirIdx_lt hb_pos h.2.1
      (Nat.sub_lt (dirSlabsPerBucket_pos_of_pos hb_pos) Nat.zero_lt_one)
  )
  · exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU hq_lt.le
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact h.1
  · exact hq_lt
  · exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU hr_lt.le
  · exact hr_lt
  · rw [clientResult_readGMProg _ hq_lt]
    have hbc := bCount_le_n_max h.2.2.1 d.2
    unfold bCount at hbc
    simp only [Nat.ne_of_gt hb_pos, ↓reduceIte, h.2.1, gmQIdx] at hbc
    exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)
  · rw [clientState_readGMProg, clientResult_readGMProg _ hq_lt, clientResult_readGMProg _ hr_lt]
    have hbc := bCount_le_n_max h.2.2.1 d.2
    unfold bCount at hbc
    simp only [Nat.ne_of_gt hb_pos, ↓reduceIte, h.2.1, gmQIdx, gmRIdx] at hbc
    exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)
  · exact le_of_lt hc
  · exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU hdir_lt.le
  · exact h.1
  · exact hdir_lt
  · repeat rw [clientState_readGMProg]
    exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU
      (initOvfSearch_aboveIdx_lt hb_pos h.2.1 h.2.2.1 hc).le
  · exact fits_const_of_dictEnv h.1 (by decide)
  · repeat rw [clientState_readGMProg]
    exact initOvfSearch_aboveIdx_lt hb_pos h.2.1 h.2.2.1 hc

/-- Base address `base` in a parameter-free overflow-search call
`(dp, ((base, b), q_target))`. -/
abbrev ovfSearchBase (d : DictParams × ((ℕ × ℕ) × ℕ)) : ℕ := d.2.1.1

/-- Bucket index `b` in a parameter-free overflow-search call
`(dp, ((base, b), q_target))`. -/
abbrev ovfSearchBucket (d : DictParams × ((ℕ × ℕ) × ℕ)) : ℕ := d.2.1.2

/-- Bucket location `(base, b)` in a parameter-free overflow-search call
`(dp, ((base, b), q_target))`. -/
abbrev ovfSearchBucketLoc (d : DictParams × ((ℕ × ℕ) × ℕ)) : ℕ × ℕ := d.2.1

/-- Found flag (`1` if matched, `0` otherwise) in a search result `((found, j_found), phys)`. -/
abbrev ovfSearchFound (res : (ℕ × ℕ) × ℕ) : ℕ := res.1.1

/-- Matched bucket-local slot index `j_found` in a search result `((found, j_found), phys)`. -/
abbrev ovfSearchIdx (res : (ℕ × ℕ) × ℕ) : ℕ := res.1.2

/-- Parameter-free Phase 2 overflow search `searchOverflowGenProg`: scans overflow slots
`j ∈ [effBucketCap n_max, bCount n_max gm b)` in bucket `b = ovfSearchBucket d` for
quotient `q_target = d.2.2`, returning `((found, j_found), phys_found)`. -/
@[expose] def searchOverflowGenProg (d : DictParams × ((ℕ × ℕ) × ℕ)) :
    Memory.Prog ((ℕ × ℕ) × ℕ) :=
  if dpBucketBits d.1 = 0 then do
    let z0 ← pure 0
    pure ((z0, z0), z0)
  else do
    let init ← initOvfSearchGenProg (d.1, ovfSearchBucketLoc d)
    let j0 ← pure (dpMinCap d.1)
    let z0 ← pure 0
    let res ← ovfLoopGenProg
      (((d.1, d.2), ((((j0, init.1), z0), z0), z0)), init.2)
    pure ((ovfAccFound res, ovfAccMatchIdx res), res.2)

/-- Phase 2 overflow search `searchOverflowProg`: scans overflow slots
`j ∈ [effBucketCap n_max, bCount n_max gm b)` in bucket `b = d.1.2` for quotient `q_target = d.2`,
returning `((found, j_found), phys_found)`. -/
@[expose] def searchOverflowProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) :
    Memory.Prog ((ℕ × ℕ) × ℕ) :=
  if bucketBits n_max = 0 then do
    let z0 ← pure 0
    pure ((z0, z0), z0)
  else do
    let init ← initOvfSearchProg U V w n_max h_space d.1
    let j0 ← pure (min n_max (effBucketCap n_max))
    let z0 ← pure 0
    let res ← ovfLoopProg U V w n_max h_space
      ((d, ((((j0, init.1), z0), z0), z0)), init.2)
    pure ((ovfAccFound res, ovfAccMatchIdx res), res.2)

@[simp]
theorem searchOverflowGenProg_mk (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) :
    searchOverflowGenProg (mkDictParams U V w n_max h_space, d) =
      searchOverflowProg U V w n_max h_space d := by
  simp only [searchOverflowGenProg, searchOverflowProg, ovfSearchBucketLoc,
    p_bucketBits_mk, p_minCap_mk, initOvfSearchGenProg_mk, ovfLoopGenProg_mk]

/-- Precondition for `searchOverflowProg` (`d = ((base, b), q_target)`). -/
@[expose] def SearchOverflowPre (U V w₀ n_max h_space w : ℕ)
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State) : Prop :=
  let base := ovfBucketBase d
  let b := ovfBucketIdx d
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  b < numBuckets n_max ∧
  SlotStoreInv n_max (gmAt base U V w₀ n_max h_space s.mem)

/-- Parameter-free precondition for `searchOverflowGenProg`. -/
@[expose] def SearchOverflowGenPre (w : ℕ)
    (d : DictParams × ((ℕ × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  let dp := d.1
  let base := ovfSearchBase d
  let b := ovfSearchBucket d
  DictEnvGen w dp base ∧
  b < numBuckets (dpNMax dp) ∧
  SlotStoreInv (dpNMax dp)
    (gmAt base (dpU dp) (dpV dp) (dpW dp) (dpNMax dp) (dpHSpace dp) s.mem)

@[simp]
theorem searchOverflowGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    SearchOverflowGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      SearchOverflowPre U V w₀ n_max h_space w d s := Iff.rfl

open Classical in
theorem searchOverflowProg_spec {U V w₀ n_max h_space w : ℕ}
    {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) (ovfBucketBase d))
    (hb : ovfBucketIdx d < numBuckets n_max)
    (hinv : SlotStoreInv n_max (gmAt (ovfBucketBase d) U V w₀ n_max h_space s.mem)) :
    let gm := gmAt (ovfBucketBase d) U V w₀ n_max h_space s.mem
    let prog := searchOverflowProg U V w₀ n_max h_space d
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s ≤ 8 + 6 * (bCount n_max gm (ovfBucketIdx d) - effBucketCap n_max) ∧
    (0 < bucketBits n_max →
      let init := (Memory.spec 0).clientResult s (initOvfSearchProg U V w₀ n_max h_space d.1)
      iterationSafe (ovfStepProg U V w₀ n_max h_space)
        (OvfStepPre U V w₀ n_max h_space) w d init.2
        ((((min n_max (effBucketCap n_max), init.1), 0), 0), 0) s) ∧
    (let res := (Memory.spec 0).clientResult s prog
     if ∃ j, effBucketCap n_max ≤ j ∧ j < bCount n_max gm (ovfBucketIdx d) ∧
         quotAt (ovfBucketBase d) U w₀ n_max h_space s.mem
           (slotOf n_max gm (ovfBucketIdx d) j) = d.2 then
       ovfSearchFound res = 1 ∧
       effBucketCap n_max ≤ ovfSearchIdx res ∧
       ovfSearchIdx res < bCount n_max gm (ovfBucketIdx d) ∧
       quotAt (ovfBucketBase d) U w₀ n_max h_space s.mem
         (slotOf n_max gm (ovfBucketIdx d) (ovfSearchIdx res)) = d.2 ∧
       res.2 = slotOf n_max gm (ovfBucketIdx d) (ovfSearchIdx res)
     else
       ovfSearchFound res = 0) := by
  intro gm prog
  dsimp only [gm, prog, ovfBucketBase, ovfBucketIdx, ovfSearchFound, ovfSearchIdx] at *
  have hbc_le := bCount_le_n_max hinv d.1.2
  have hno_of (hle : bCount n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2 ≤
      effBucketCap n_max) : ¬∃ j, effBucketCap n_max ≤ j ∧
      j < bCount n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2 ∧
      quotAt d.1.1 U w₀ n_max h_space s.mem
        (slotOf n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2 j) = d.2 :=
    fun ⟨_, hj1, hj2, _⟩ => by omega
  rcases Nat.eq_zero_or_pos (bucketBits n_max) with hb0 | hb_pos
  · have hlt_cap := lt_effBucketCap_of_bucketBits_eq_zero hb0
    unfold searchOverflowProg; rw [ite_eq_left hb0]
    simp only [pure_bind, memoryCost_pure]
    exact ⟨rfl, by omega, fun h => by omega, by rw [ite_eq_right (hno_of (by omega))]; rfl⟩
  · unfold searchOverflowProg ovfLoopProg
    rw [ite_eq_right (Nat.ne_of_gt hb_pos)]
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      memoryCost_bind_of_clientState_eq (clientState_initOvfSearchProg ..),
      clientState_initOvfSearchProg]
    have hinit := clientResult_initOvfSearchProg (d := d.1) s hb_pos hb hinv
    have hcost_init := memoryCost_initOvfSearchProg_le U V w₀ n_max h_space d.1 s
    set init := (Memory.spec 0).clientResult s (initOvfSearchProg U V w₀ n_max h_space d.1)
    dsimp only at hinit
    by_cases hovf : effBucketCap n_max <
        bCount n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2
    · have hjm_eq : effBucketCap n_max + init.2 =
          bCount n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2 := by rw [hinit.1]; omega
      have hloop := iterate_ovfStepProg_spec (q_target := d.2) hb_pos henv hb hinv
        init.2 (effBucketCap n_max) init.1 0 0 0 hjm_eq.le (hinit.2 hovf)
      dsimp only [Prod.mk.eta] at hloop
      rw [show min n_max (effBucketCap n_max) = effBucketCap n_max by omega,
        StateTransitionSpec.clientState_bind, hloop.1, StateTransitionSpec.clientResult_bind,
        memoryCost_bind_of_clientState_eq hloop.1]
      have hres := hloop.2.2.2; rw [ite_eq_left rfl, hjm_eq] at hres
      have hlc := hloop.2.1; rw [hinit.1] at hlc
      exact ⟨rfl, by simp only [memoryCost_pure]; omega, fun _ => hloop.2.2.1, hres⟩
    · rw [show init.2 = 0 by rw [hinit.1]; omega, iterate,
        ite_eq_right (hno_of (Nat.le_of_not_lt hovf))]
      simp only [pure_bind, memoryCost_pure]
      exact ⟨rfl, by omega, fun _ => trivial, rfl⟩

theorem realizes_searchOverflowGen :
    Realizes .exact searchOverflowGenProg
      (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      SearchOverflowGenPre
      (fun _ _ => 0) := by
  have hinit := realizes_initOvfSearchGen
  have hloop := realizes_ovfLoopGen
  realizeDictWith [searchOverflowGenPre_mk, SearchOverflowPre,
    initOvfSearchGenProg_mk, ovfLoopGenProg_mk, iterationSafe_ovfStepGenProg_mk,
    ovfBucketBase, ovfBucketIdx, ovfInitBase, ovfInitBucket, ovfLoopCtx, ovfLoopAcc,
    ovfSearchBase, ovfSearchBucket, ovfSearchBucketLoc, ovfAccFound, ovfAccMatchIdx]
  · exact h.1
  · exact h.2.1
  · exact h.2.2
  · exact Nat.pos_of_ne_zero hc
  · rw [clientState_initOvfSearchProg]
    exact (searchOverflowProg_spec h.1 h.2.1 h.2.2).2.2.1 (Nat.pos_of_ne_zero hc)

/-! ## Section 3: Combined Two-Phase Bucket Search (`searchBucketProg`) and `queryBodyProg` -/

/-- Found flag (`1` if matched) in a `searchMicroChainProg` result
`(((ptr, found), j_found), phys_found)`. -/
abbrev microSearchFound (res : ((ℕ × ℕ) × ℕ) × ℕ) : ℕ := res.1.1.2

/-- Matched logical slot index `j_found` in a `searchMicroChainProg` result. -/
abbrev microSearchIdx (res : ((ℕ × ℕ) × ℕ) × ℕ) : ℕ := res.1.2

/-- Query prefix `((base, b), q_target)` in a parameter-free bucket-search call
`(dp, (((base, b), q_target), m))`. -/
abbrev searchBucketGenQuery (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) : (ℕ × ℕ) × ℕ := d.2.1

/-- Parameter-free two-phase bucket search `searchBucketGenProg`
(`d = (dp, (((base, b), q_target), m))`):
first searches the micro-bucket chain `(b, m)` via `searchMicroChainGenProg`; if not found,
searches any overflow slots `j ∈ [effBucketCap n_max, bCount n_max gm b)` via
`searchOverflowGenProg`. Returns `((found, j_found), phys_found)`. -/
@[expose] def searchBucketGenProg
    (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) : Memory.Prog ((ℕ × ℕ) × ℕ) := do
  let res1 ← searchMicroChainGenProg d
  let z1 ← pure 1
  if microSearchFound res1 = z1 then
    pure ((z1, microSearchIdx res1), res1.2)
  else
    searchOverflowGenProg (d.1, searchBucketGenQuery d)

/-- Two-phase bucket search `searchBucketProg` (`d = (((base, b), q_target), m)`):
first searches the micro-bucket chain `(b, m)` via `searchMicroChainProg`; if not found,
searches any overflow slots `j ∈ [effBucketCap n_max, bCount n_max gm b)` via
`searchOverflowProg`. Returns `((found, j_found), phys_found)`. -/
@[expose] def searchBucketProg (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ((ℕ × ℕ) × ℕ) := do
  let res1 ← searchMicroChainProg U V w n_max h_space d
  let z1 ← pure 1
  if microSearchFound res1 = z1 then
    pure ((z1, microSearchIdx res1), res1.2)
  else
    searchOverflowProg U V w n_max h_space d.1

@[simp]
theorem searchBucketGenProg_mk (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    searchBucketGenProg (mkDictParams U V w n_max h_space, d) =
      searchBucketProg U V w n_max h_space d := by
  simp only [searchBucketGenProg, searchBucketProg, searchBucketGenQuery,
    searchMicroChainGenProg_mk, searchOverflowGenProg_mk]

open Classical in
theorem searchBucketProg_spec {U V w₀ n_max h_space w : ℕ}
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State} {L : List ℕ}
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) (ovfQueryBase d))
    (hb : ovfQueryBucket d < numBuckets n_max)
    (hm : d.2 < numMicroPerBucket n_max)
    (hinv : SlotStoreInv n_max (gmAt (ovfQueryBase d) U V w₀ n_max h_space s.mem))
    (hchain : IsDLChain n_max
      (lmHead n_max (lmAt (ovfQueryBase d) U V w₀ n_max h_space s.mem) (ovfQueryBucket d) d.2)
      (lmPrev n_max (lmAt (ovfQueryBase d) U V w₀ n_max h_space s.mem) (ovfQueryBucket d))
      (lmNext n_max (lmAt (ovfQueryBase d) U V w₀ n_max h_space s.mem) (ovfQueryBucket d)) L)
    (hc_lt : ∀ j ∈ L,
      j < bCount n_max (gmAt (ovfQueryBase d) U V w₀ n_max h_space s.mem) (ovfQueryBucket d)) :
    let gm := gmAt (ovfQueryBase d) U V w₀ n_max h_space s.mem
    let prog := searchBucketProg U V w₀ n_max h_space d
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s ≤
      10 + 8 * L.length + 6 * (bCount n_max gm (ovfQueryBucket d) - effBucketCap n_max) ∧
    (let res := (Memory.spec 0).clientResult s prog
     if (∃ j ∈ L, quotAt (ovfQueryBase d) U w₀ n_max h_space s.mem
           (slotOf n_max gm (ovfQueryBucket d) j) = ovfQueryQuot d) ∨
        (∃ j, effBucketCap n_max ≤ j ∧ j < bCount n_max gm (ovfQueryBucket d) ∧
          quotAt (ovfQueryBase d) U w₀ n_max h_space s.mem
            (slotOf n_max gm (ovfQueryBucket d) j) = ovfQueryQuot d) then
       ovfSearchFound res = 1 ∧
       ovfSearchIdx res < bCount n_max gm (ovfQueryBucket d) ∧
       (ovfSearchIdx res ∈ L ∨ effBucketCap n_max ≤ ovfSearchIdx res) ∧
       quotAt (ovfQueryBase d) U w₀ n_max h_space s.mem
         (slotOf n_max gm (ovfQueryBucket d) (ovfSearchIdx res)) = ovfQueryQuot d ∧
       res.2 = slotOf n_max gm (ovfQueryBucket d) (ovfSearchIdx res)
     else
       ovfSearchFound res = 0) := by
  intro gm prog
  dsimp only [gm, prog, ovfQueryBase, ovfQueryBucket, ovfQueryQuot,
    ovfSearchFound, ovfSearchIdx] at *
  have h1 := searchMicroChainProg_spec henv hb hm hinv hchain hc_lt
  have h2 := searchOverflowProg_spec (d := d.1) henv hb hinv
  dsimp only [lmEntryBase, lmEntryBucket, lmEntryIdx, microAccStatus, microAccIdx,
    ovfBucketBase, ovfBucketIdx, ovfSearchFound, ovfSearchIdx] at h1 h2
  unfold searchBucketProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    memoryCost_bind_of_clientState_eq h1.1, h1.1]
  set res1 := (Memory.spec 0).clientResult s (searchMicroChainProg U V w₀ n_max h_space d)
  have hres1 := h1.2.2.2
  split_ifs at hres1 with hex1
  · rw [ite_eq_left (by rw [hres1.1] : res1.1.1.2 = 1), ite_eq_left (Or.inl hex1)]
    exact ⟨rfl, by have := h1.2.1; simp only [memoryCost_pure]; omega, rfl,
      hc_lt _ hres1.2.1, Or.inl hres1.2.1, hres1.2.2.1, hres1.2.2.2⟩
  · rw [ite_eq_right (by rw [hres1]; decide : res1.1.1.2 ≠ 1)]
    refine ⟨h2.1, by have := h1.2.1; have := h2.2.1; omega, ?_⟩
    have hres2 := h2.2.2.2
    split_ifs at hres2 with hex2
    · rw [ite_eq_left (Or.inr hex2)]
      exact ⟨hres2.1, hres2.2.2.1, Or.inr hres2.2.1, hres2.2.2.2.1, hres2.2.2.2.2⟩
    · rw [ite_eq_right (not_or.mpr ⟨hex1, hex2⟩)]
      exact hres2

theorem realizes_searchBucketGen :
    Realizes .exact searchBucketGenProg
      (WordEncoding.encode (α := DictParams × (((ℕ × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      SearchMicroChainGenPre
      (fun _ _ => 0) := by
  have hm := realizes_searchMicroChainGen
  have ho := realizes_searchOverflowGen
  realizeDictWith [searchMicroChainGenPre_mk, SearchMicroChainPre, lmEntryBase, lmEntryBucket,
    searchMicroChainGenProg_mk, searchOverflowGenPre_mk, SearchOverflowPre,
    searchOverflowGenProg_mk, microSearchFound, microSearchIdx, searchBucketGenQuery]
  · exact h
  · exact fits_const_of_dictEnv h.1 (by decide)
  · obtain ⟨L, hchain, hc_lt⟩ := h.2.2.2.2
    rw [(searchMicroChainProg_spec h.1 h.2.1 h.2.2.1 h.2.2.2.1 hchain hc_lt).1]
    exact ⟨h.1, h.2.1, h.2.2.2.1⟩

/-- Parameter-free dictionary lookup body `queryBodyGenProg`
(`d = (dp, (((base, b), q_target), m))`):
calls `searchBucketGenProg` and, if found (`ovfSearchFound res = 1`), reads and returns `some v`
from `Values` at physical slot `res.2`, otherwise returns `none`. -/
@[expose] def queryBodyGenProg
    (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) : Memory.Prog (Option ℕ) := do
  let res ← searchBucketGenProg d
  let z1 ← pure 1
  if ovfSearchFound res = z1 then do
    let v ← readValGenProg (d.1, (ovfQueryBase d.2, res.2))
    pure (some v)
  else
    pure none

/-- Dictionary lookup body `queryBodyProg` (`d = (((base, b), q_target), m)`):
calls `searchBucketProg` and, if found (`ovfSearchFound res = 1`), reads and returns `some v`
from `Values` at physical slot `res.2`, otherwise returns `none`. -/
@[expose] def queryBodyProg (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog (Option ℕ) := do
  let res ← searchBucketProg U V w n_max h_space d
  let z1 ← pure 1
  if ovfSearchFound res = z1 then do
    let v ← readValProg U V w n_max h_space (ovfQueryBase d, res.2)
    pure (some v)
  else
    pure none

@[simp]
theorem queryBodyGenProg_mk (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    queryBodyGenProg (mkDictParams U V w n_max h_space, d) =
      queryBodyProg U V w n_max h_space d := by
  simp only [queryBodyGenProg, queryBodyProg, ovfSearchFound, ovfQueryBase,
    searchBucketGenProg_mk, readValGenProg_mk]

open Classical in
theorem queryBodyProg_spec {U V w₀ n_max h_space w : ℕ}
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State} {L : List ℕ}
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) (ovfQueryBase d))
    (hb : ovfQueryBucket d < numBuckets n_max)
    (hm : d.2 < numMicroPerBucket n_max)
    (hinv : SlotStoreInv n_max (gmAt (ovfQueryBase d) U V w₀ n_max h_space s.mem))
    (hchain : IsDLChain n_max
      (lmHead n_max (lmAt (ovfQueryBase d) U V w₀ n_max h_space s.mem) (ovfQueryBucket d) d.2)
      (lmPrev n_max (lmAt (ovfQueryBase d) U V w₀ n_max h_space s.mem) (ovfQueryBucket d))
      (lmNext n_max (lmAt (ovfQueryBase d) U V w₀ n_max h_space s.mem) (ovfQueryBucket d)) L)
    (hc_lt : ∀ j ∈ L,
      j < bCount n_max (gmAt (ovfQueryBase d) U V w₀ n_max h_space s.mem) (ovfQueryBucket d)) :
    let gm := gmAt (ovfQueryBase d) U V w₀ n_max h_space s.mem
    let prog := queryBodyProg U V w₀ n_max h_space d
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s ≤
      12 + 8 * L.length + 6 * (bCount n_max gm (ovfQueryBucket d) - effBucketCap n_max) ∧
    (let res := (Memory.spec 0).clientResult s prog
     if (∃ j ∈ L, quotAt (ovfQueryBase d) U w₀ n_max h_space s.mem
           (slotOf n_max gm (ovfQueryBucket d) j) = ovfQueryQuot d) ∨
        (∃ j, effBucketCap n_max ≤ j ∧ j < bCount n_max gm (ovfQueryBucket d) ∧
          quotAt (ovfQueryBase d) U w₀ n_max h_space s.mem
            (slotOf n_max gm (ovfQueryBucket d) j) = ovfQueryQuot d) then
       ∃ j < bCount n_max gm (ovfQueryBucket d),
         quotAt (ovfQueryBase d) U w₀ n_max h_space s.mem
           (slotOf n_max gm (ovfQueryBucket d) j) = ovfQueryQuot d ∧
         res = some (valAt (ovfQueryBase d) U V w₀ n_max h_space s.mem
           (slotOf n_max gm (ovfQueryBucket d) j))
     else
       res = none) := by
  intro gm prog
  dsimp only [gm, prog, ovfQueryBase, ovfQueryBucket, ovfQueryQuot] at *
  have hsb := searchBucketProg_spec henv hb hm hinv hchain hc_lt
  dsimp only [ovfQueryBase, ovfQueryBucket, ovfQueryQuot, ovfSearchFound, ovfSearchIdx] at hsb
  unfold queryBodyProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    memoryCost_bind_of_clientState_eq hsb.1, hsb.1]
  set res := (Memory.spec 0).clientResult s (searchBucketProg U V w₀ n_max h_space d)
  have hsb_res := hsb.2.2
  split_ifs at hsb_res with hex
  · have hphys_lt : (slotOf n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 res.1.2) <
        n_max := (slotOf_lt_and_injective hinv).1 d.1.1.2 hb res.1.2 hsb_res.2.1
    rw [ite_eq_left hsb_res.1, ite_eq_left hex, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientResult_bind,
      memoryCost_bind_of_clientState_eq (clientState_readValProg ..),
      clientState_readValProg, memoryCost_readValProg, hsb_res.2.2.2.2,
      clientResult_readValProg s hphys_lt]
    exact ⟨rfl, by have := hsb.2.1; simp only [memoryCost_pure]; omega,
      res.1.2, hsb_res.2.1, hsb_res.2.2.2.1, rfl⟩
  · rw [ite_eq_right (by omega : res.1.1 ≠ 1), ite_eq_right hex]
    exact ⟨rfl, by have := hsb.2.1; simp only [memoryCost_pure]; omega, rfl⟩

theorem realizes_queryBodyGen :
    Realizes .exact queryBodyGenProg
      (WordEncoding.encode (α := DictParams × (((ℕ × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := Option ℕ))
      SearchMicroChainGenPre
      (fun _ _ => 0) := by
  realizeDictWith [searchMicroChainGenPre_mk, SearchMicroChainPre, searchBucketGenProg_mk,
    ovfSearchFound, ovfQueryBase] using
    [realizes_searchBucketGen, realizes_readValGen]
  · exact h
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact h.1
  · obtain ⟨L, hchain, hc_lt⟩ := h.2.2.2.2
    have hspec := (searchBucketProg_spec h.1 h.2.1 h.2.2.1 h.2.2.2.1 hchain hc_lt).2.2
    dsimp only [ovfQueryBase, ovfQueryBucket, ovfQueryQuot, ovfSearchFound,
      ovfSearchIdx] at hspec
    split_ifs at hspec
    · rw [hspec.2.2.2.2]
      exact (slotOf_lt_and_injective h.2.2.2.1).1 d.1.1.2 h.2.1 _ hspec.2.1
    · omega
  · exact fits_const_of_dictEnv h.1 (by decide)

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
