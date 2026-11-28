/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.Invariants
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.MapRel
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.DeleteHelpers
import Mathlib.Tactic.NormNum

/-!
# Fast-Mode Deletion With Swap-Last Relocation (`fastDelete_afterDel_reloc_spec`)

This module proves `fastDelete_afterDel_reloc_spec`: when `fastFindLoc` locates key `u` at an
interior coordinate `loc_del < fs.bktCount b - 1`, `fastDeleteRemove` followed by
`fastDeleteMoveLast` and `fastDeleteShrink` relocates the terminal item `loc_last` into `loc_del`
across physical arrays, epoch buffers, the live B+-tree, the Overmars shadow B+-tree, and any
in-progress Stage-2 bucket rebuild, preserving `CoreFastInv`, `OvermarsBucketInv` on other buckets,
`PreOvermarsBucketInv` on bucket `b`, and `ValidEpochStagePreTick`.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.fastDelete_afterDel_reloc_spec`: invariant
  preservation for fast-mode deletion with last-element relocation.
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctWhp.ModelStepAux

/-- Intermediate `fsAfterDel` invariant when `fastFindLoc` finds `loc_del < loc_last`. -/
theorem fastDelete_afterDel_reloc_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict)
    (u : Fin U) {loc_del : ℕ}
    (hld_lt : loc_del < fs.bktCount (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val))
    (hq_del : fs.quotArr
      (fs.physSlot n_max (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val) loc_del) =
      keyQuotient (bWhp n_max) u.val)
    (hlt_ll : loc_del <
      fs.bktCount (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val) - 1) :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let loc_last := fs.bktCount b - 1
    let rebActiveB : Bool :=
      decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
        fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
        fs.rebCollision = 0)
    let fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
    let fs2 := fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1
    let fsA := fastDeleteShrink n_max b loc_last fs2
    CoreFastInv c U V n_max θ fsA (Function.update dict u none) ∧
    (∀ b' < numBucketsWhp n_max, b' ≠ b → OvermarsBucketInv c U n_max θ fsA b') ∧
    PreOvermarsBucketInv c U n_max θ fsA b ∧
    ValidEpochStagePreTick c U n_max θ fsA := by
  intro b loc_last rebActiveB
  set st_del := fs.locState b loc_del
  set rKey_u := fpReducedKey c U n_max θ.2 u
  set fp_live_u := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  set buf1 :=
    if st_del = 2 then
      Function.update fs.buf 0 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 0) rKey_u)
    else if st_del = 3 then
      Function.update fs.buf 1 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 1) rKey_u)
    else fs.buf
  set lIdx := fs.liveSliceIdx b
  set slices1 :=
    if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
      Function.update fs.slices lIdx
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices lIdx) fp_live_u)
    else fs.slices
  set omIdx := fs.overmarsSliceIdx b
  set slices2 :=
    if fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
      Function.update slices1 omIdx
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (slices1 omIdx) fp_live_u)
    else slices1
  set rIdx := fs.rebSliceIdx b
  set slices3 :=
    if rebActiveB && decide (loc_del < fs.rebScanCursor ∧
        (st_del = 1 ∨ st_del = 2 + fs.oldEp)) then
      Function.update slices2 rIdx
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (slices2 rIdx) (fpOfSalt c U n_max θ.2 fs.rebCandSalt u))
    else slices2
  set fs1 : FastState := { fs with buf := buf1, slices := slices3 }
  have hfs1_eq : fastDeleteRemove c U n_max θ fs u b loc_del = fs1 := rfl
  set p_last := fs1.physSlot n_max b loc_last
  set p_del := fs1.physSlot n_max b loc_del
  set st_last := fs1.locState b loc_last
  set rKey_last := fs1.rKeyAt c U n_max θ b loc_last
  set fp_live_last := fs1.fpAt c U n_max θ (fs1.bktSalt b) b loc_last
  set fp_cand_last := fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last
  set qArr' := Function.update fs1.quotArr p_del (fs1.quotArr p_last)
  set vArr' := Function.update fs1.valArr p_del (fs1.valArr p_last)
  set buf2 :=
    if st_last = 2 then
      Function.update fs1.buf 0
        (bufInsert (cTabWhp c) (bCharWhp n_max) (fs1.buf 0) rKey_last b loc_del)
    else if st_last = 3 then
      Function.update fs1.buf 1
        (bufInsert (cTabWhp c) (bCharWhp n_max) (fs1.buf 1) rKey_last b loc_del)
    else fs1.buf
  set sl_live' :=
    if inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last then
      Function.update fs1.slices lIdx
        (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs1.slices lIdx) fp_live_last loc_del)
    else fs1.slices
  set omPair :=
    if fs1.overmarsActive b = 1 ∧
        inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last then
      if loc_last < fs1.overmarsCursor b then
        (Function.update sl_live' omIdx
          (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (sl_live' omIdx) fp_live_last loc_del),
         fs1.overmarsInsCount)
      else if loc_del < fs1.overmarsCursor b then
        (Function.update sl_live' omIdx
          (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (sl_live' omIdx) fp_live_last loc_del),
         Function.update fs1.overmarsInsCount b (fs1.overmarsInsCount b + 1))
      else (sl_live', fs1.overmarsInsCount)
    else (sl_live', fs1.overmarsInsCount)
  set sl_om' := omPair.1
  set omIns' := omPair.2
  set rebQuad :=
    if rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs1.oldEp) then
      if loc_last < fs1.rebScanCursor then
        (Function.update sl_om' rIdx
          (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (sl_om' rIdx) fp_cand_last loc_del),
         (fs1.rebCandSalt, (fs1.rebScanCursor, fs1.rebInsCount)))
      else if loc_del < fs1.rebScanCursor then
        match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (sl_om' rIdx) fp_cand_last with
        | some _ =>
          (Function.update sl_om' rIdx (resetBTreeSlice (sl_om' rIdx)),
           (fs1.rebCandSalt + 1, (0, 0)))
        | none =>
          (Function.update sl_om' rIdx
            (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (sl_om' rIdx) fp_cand_last loc_del),
           (fs1.rebCandSalt, (fs1.rebScanCursor, fs1.rebInsCount + 1)))
      else (sl_om', (fs1.rebCandSalt, (fs1.rebScanCursor, fs1.rebInsCount)))
    else (sl_om', (fs1.rebCandSalt, (fs1.rebScanCursor, fs1.rebInsCount)))
  set fs2 : FastState :=
    { fs1 with
      quotArr := qArr'
      valArr := vArr'
      locState := Function.update fs1.locState b
        (Function.update (fs1.locState b) loc_del st_last)
      buf := buf2
      slices := rebQuad.1
      overmarsInsCount := omIns'
      rebCandSalt := rebQuad.2.1
      rebScanCursor := rebQuad.2.2.1
      rebInsCount := rebQuad.2.2.2 }
  have hfs2_eq :
      fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1 = fs2 := rfl
  let fsA := fastDeleteShrink n_max b loc_last fs2
  have hfsA_eq : fastDeleteShrink n_max b loc_last fs2 = fsA := rfl
  dsimp only
  rw [hfs1_eq, hfs2_eq, hfsA_eq]
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  have hld_lt_b : loc_del < fs.bktCount b := hld_lt
  have hlt_ll_b : loc_del < loc_last := hlt_ll
  have hcnt : fs.bktCount b = loc_last + 1 := by
    dsimp only [loc_last] at hlt_ll_b ⊢; omega
  have hll_lt : loc_last < fs.bktCount b := by omega
  have hL2 : 2 ≤ slabScale n_max := two_le_slabScale n_max
  have hL12 : 4096 ≤ (slabScale n_max) ^ 12 := by
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ (slabScale n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
  have hcnt_3L : fs.bktCount b ≤ 3 * (slabScale n_max) ^ 12 :=
    (hv.bktCount_le b hb).trans totalLocalCoordsWhp_le_three_mul
  have hkv_del : fs.keyValAt c U n_max θ.1 b loc_del = u.val := by
    dsimp only [FastState.keyValAt, b]
    rw [hq_del]
    exact feistelReconstruct_feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  have hrk_del : fs.rKeyAt c U n_max θ b loc_del = rKey_u := by
    dsimp only [FastState.rKeyAt, rKey_u]; simp [hkv_del, u.isLt]
  have hs_b : fs.bktSalt b < sMaxWhp c n_max := hv.bktSalt_lt b hb
  have hfp_live_del : fs.fpAt c U n_max θ (fs.bktSalt b) b loc_del = fp_live_u := by
    dsimp only [FastState.fpAt, fp_live_u, fpOfSalt]; simp [hs_b, hkv_del, u.isLt]
  have hfp_cand_del : fs.fpAt c U n_max θ fs.rebCandSalt b loc_del =
      fpOfSalt c U n_max θ.2 fs.rebCandSalt u := by
    dsimp only [FastState.fpAt, fpOfSalt]
    by_cases hs : fs.rebCandSalt < sMaxWhp c n_max <;> simp [hs, hkv_del, u.isLt]
  have hrk1_last : rKey_last = fs.rKeyAt c U n_max θ b loc_last :=
    congrFun (congrFun (rKeyAt_eq_of_fields (fs₁ := fs1) (fs₂ := fs) rfl rfl) b) loc_last
  have hfp1_live : fp_live_last = fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last :=
    congrFun (fpAt_eq_of_fields (fs₁ := fs1) (fs₂ := fs) rfl rfl (fs.bktSalt b) b) loc_last
  have hfp1_cand : fp_cand_last = fs.fpAt c U n_max θ fs.rebCandSalt b loc_last :=
    congrFun (fpAt_eq_of_fields (fs₁ := fs1) (fs₂ := fs) rfl rfl fs.rebCandSalt b) loc_last
  obtain ⟨hlr_b, hor_b, hro_ne⟩ := hv.roles_valid b hb
  have hrr_b := rebRole_props hlr_b hor_b hro_ne
  have hl_ne_om : lIdx ≠ omIdx := by
    dsimp only [lIdx, omIdx, FastState.liveSliceIdx, FastState.overmarsSliceIdx]; omega
  have hl_ne_r : lIdx ≠ rIdx := by
    dsimp only [lIdx, rIdx, FastState.liveSliceIdx, FastState.rebSliceIdx, FastState.rebRole]; omega
  have hom_ne_r : omIdx ≠ rIdx := by
    dsimp only [omIdx, rIdx, FastState.overmarsSliceIdx, FastState.rebSliceIdx, FastState.rebRole]
    omega
  have hslice_other : ∀ b' < numBucketsWhp n_max, b' ≠ b → ∀ r < 3,
      3 * b' + r ≠ lIdx ∧ 3 * b' + r ≠ omIdx ∧ 3 * b' + r ≠ rIdx := by
    intro b' _ hbb r hr
    refine ⟨fun h => hbb (sliceIdx_inj hr hlr_b h).1,
      fun h => hbb (sliceIdx_inj hr hor_b h).1,
      fun h => hbb (sliceIdx_inj hr hrr_b.1 h).1⟩
  -- Physical-slot & coordinate transport
  obtain ⟨_, hphys_inj⟩ := hv.physSlot_lt_and_inj
  have hphys_eq : fsA.physSlot n_max = fs.physSlot n_max := rfl
  have hcnt_lt_orig : ∀ {b' loc}, loc < fsA.bktCount b' → loc < fs.bktCount b' :=
    fun hloc => lt_of_lt_update_le (by omega) hloc
  have hcntA_b : fsA.bktCount b = loc_last := Function.update_self _ _ _
  have hcntA_other {b' : ℕ} (hbb : b' ≠ b) : fsA.bktCount b' = fs.bktCount b' :=
    Function.update_of_ne hbb _ _
  have hqv_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fsA.bktCount b',
      ¬(b' = b ∧ loc = loc_del) →
      fsA.quotArr (fs.physSlot n_max b' loc) = fs.quotArr (fs.physSlot n_max b' loc) ∧
      fsA.valArr (fs.physSlot n_max b' loc) = fs.valArr (fs.physSlot n_max b' loc) := by
    intro b' hb' loc hloc hne
    have hp_ne : fs.physSlot n_max b' loc ≠ p_del := fun heq =>
      hne (hphys_inj b' hb' loc (hcnt_lt_orig hloc) b hb loc_del hld_lt_b heq)
    exact ⟨Function.update_of_ne hp_ne _ _, Function.update_of_ne hp_ne _ _⟩
  have hqv_at_del :
      fsA.quotArr (fs.physSlot n_max b loc_del) = fs.quotArr (fs.physSlot n_max b loc_last) ∧
      fsA.valArr (fs.physSlot n_max b loc_del) = fs.valArr (fs.physSlot n_max b loc_last) := by
    dsimp only [fsA, fastDeleteShrink, fs2, qArr', vArr', fs1]
    exact ⟨Function.update_self _ _ _, Function.update_self _ _ _⟩
  have hkv_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fsA.bktCount b',
      ¬(b' = b ∧ loc = loc_del) →
      fsA.keyValAt c U n_max θ.1 b' loc = fs.keyValAt c U n_max θ.1 b' loc := by
    intro b' hb' loc hloc hne
    dsimp only [FastState.keyValAt]
    rw [hphys_eq, (hqv_pres b' hb' loc hloc hne).1]
  have hkv_at_del :
      fsA.keyValAt c U n_max θ.1 b loc_del = fs.keyValAt c U n_max θ.1 b loc_last := by
    dsimp only [FastState.keyValAt]
    rw [hphys_eq, hqv_at_del.1]
  have hfp_pres : ∀ salt b', b' < numBucketsWhp n_max → ∀ loc < fsA.bktCount b',
      ¬(b' = b ∧ loc = loc_del) →
      FastState.fpAt c U n_max θ fsA salt b' loc = FastState.fpAt c U n_max θ fs salt b' loc := by
    intro salt b' hb' loc hloc hne
    dsimp only [FastState.fpAt]; rw [hkv_pres b' hb' loc hloc hne]
  have hfp_at_del : ∀ salt,
      FastState.fpAt c U n_max θ fsA salt b loc_del =
        FastState.fpAt c U n_max θ fs salt b loc_last := by
    intro salt; dsimp only [FastState.fpAt]; rw [hkv_at_del]
  have hrk_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fsA.bktCount b',
      ¬(b' = b ∧ loc = loc_del) →
      fsA.rKeyAt c U n_max θ b' loc = fs.rKeyAt c U n_max θ b' loc := by
    intro b' hb' loc hloc hne
    dsimp only [FastState.rKeyAt]; rw [hkv_pres b' hb' loc hloc hne]
  have hrk_at_del : fsA.rKeyAt c U n_max θ b loc_del = fs.rKeyAt c U n_max θ b loc_last := by
    dsimp only [FastState.rKeyAt]; rw [hkv_at_del]
  have hls_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fsA.bktCount b',
      ¬(b' = b ∧ loc = loc_del) → fsA.locState b' loc = fs.locState b' loc := by
    intro b' _ loc hloc hne
    dsimp only [fsA, fastDeleteShrink, fs2, fs1] at hloc ⊢
    by_cases hbb : b' = b
    · rw [hbb] at hloc hne ⊢
      rw [Function.update_self] at hloc ⊢
      have hne_d : loc ≠ loc_del := fun h => hne ⟨rfl, h⟩
      rw [Function.update_self, Function.update_of_ne (Nat.ne_of_lt hloc),
        Function.update_of_ne hne_d]
    · simp [hbb]
  have hls_at_del : fsA.locState b loc_del = fs.locState b loc_last := by
    dsimp only [fsA, fastDeleteShrink, fs2, fs1, st_last]
    rw [Function.update_self, Function.update_self,
      Function.update_of_ne (Nat.ne_of_lt hlt_ll_b), Function.update_self]
  -- Coordinate `l` of bucket `b'` in `fsA` holds the item of coordinate `orig b' l` in `fs`.
  let orig (b' l : ℕ) : ℕ := if b' = b ∧ l = loc_del then loc_last else l
  have horig : ∀ b' < numBucketsWhp n_max, ∀ l < fsA.bktCount b',
      orig b' l < fs.bktCount b' ∧ fsA.locState b' l = fs.locState b' (orig b' l) ∧
      (∀ salt, fsA.fpAt c U n_max θ salt b' l = fs.fpAt c U n_max θ salt b' (orig b' l)) ∧
      fsA.rKeyAt c U n_max θ b' l = fs.rKeyAt c U n_max θ b' (orig b' l) ∧
      fsA.keyValAt c U n_max θ.1 b' l = fs.keyValAt c U n_max θ.1 b' (orig b' l) ∧
      fsA.quotArr (fs.physSlot n_max b' l) = fs.quotArr (fs.physSlot n_max b' (orig b' l)) ∧
      fsA.valArr (fs.physSlot n_max b' l) = fs.valArr (fs.physSlot n_max b' (orig b' l)) ∧
      (b' = b → orig b' l ≠ loc_del) := by
    intro b' hb' l hl
    by_cases hbd : b' = b ∧ l = loc_del
    · simp only [orig, ite_eq_left hbd]
      rw [hbd.1, hbd.2]
      exact ⟨hll_lt, hls_at_del, hfp_at_del, hrk_at_del, hkv_at_del, hqv_at_del.1, hqv_at_del.2,
        fun _ => (Nat.ne_of_lt hlt_ll_b).symm⟩
    · simp only [orig, ite_eq_right hbd]
      exact ⟨hcnt_lt_orig hl, hls_pres b' hb' l hl hbd, fun salt => hfp_pres salt b' hb' l hl hbd,
        hrk_pres b' hb' l hl hbd, hkv_pres b' hb' l hl hbd, (hqv_pres b' hb' l hl hbd).1,
        (hqv_pres b' hb' l hl hbd).2, fun h h' => hbd ⟨h, h'⟩⟩
  have horig_inj : ∀ {b' l₁ l₂}, l₁ < fsA.bktCount b' → l₂ < fsA.bktCount b' →
      orig b' l₁ = orig b' l₂ → l₁ = l₂ := by
    intro b' l₁ l₂ h₁ h₂ heq
    by_cases hbb : b' = b
    · rw [hbb, hcntA_b] at h₁ h₂
      simp only [orig, hbb, true_and] at heq
      split_ifs at heq <;> omega
    · simpa only [orig, hbb, false_and, ↓reduceIte] using heq
  -- Parametric slice non-interference across `slices1`, `slices2`, `slices3`, `sl_live'`,
  -- `sl_om'`, and `rebQuad.1`
  have hsl1_ne : ∀ {idx}, idx ≠ lIdx → slices1 idx = fs.slices idx := fun hne => by
    dsimp only [slices1]; split_ifs <;> [exact Function.update_of_ne hne _ _; rfl]
  have hsl2_ne : ∀ {idx}, idx ≠ omIdx → slices2 idx = slices1 idx := fun hne => by
    dsimp only [slices2]; split_ifs <;> [exact Function.update_of_ne hne _ _; rfl]
  have hsl3_ne : ∀ {idx}, idx ≠ rIdx → slices3 idx = slices2 idx := fun hne => by
    dsimp only [slices3]; split_ifs <;> [exact Function.update_of_ne hne _ _; rfl]
  have hsll_ne : ∀ {idx}, idx ≠ lIdx → sl_live' idx = slices3 idx := fun hne => by
    dsimp only [sl_live', fs1]; split_ifs <;> [exact Function.update_of_ne hne _ _; rfl]
  have hslom_ne : ∀ {idx}, idx ≠ omIdx → sl_om' idx = sl_live' idx := fun hne => by
    dsimp only [sl_om', omPair]
    split_ifs <;> first | rfl | exact Function.update_of_ne hne _ _
  have hrebQ_ne : ∀ {idx}, idx ≠ rIdx → rebQuad.1 idx = sl_om' idx := fun hne => by
    dsimp only [rebQuad]
    split_ifs <;> (try split) <;> first | rfl | exact Function.update_of_ne hne _ _
  have hsl3_l : slices3 lIdx = slices1 lIdx := (hsl3_ne hl_ne_r).trans (hsl2_ne hl_ne_om)
  have hsl1_om : slices1 omIdx = fs.slices omIdx := hsl1_ne hl_ne_om.symm
  have hsl2_r : slices2 rIdx = fs.slices rIdx :=
    (hsl2_ne hom_ne_r.symm).trans (hsl1_ne hl_ne_r.symm)
  have hreb_l : rebQuad.1 lIdx = sl_live' lIdx := (hrebQ_ne hl_ne_r).trans (hslom_ne hl_ne_om)
  have hreb_om : rebQuad.1 omIdx = sl_om' omIdx := hrebQ_ne hom_ne_r
  have hsll_om : sl_live' omIdx = slices2 omIdx :=
    (hsll_ne hl_ne_om.symm).trans (hsl3_ne hom_ne_r)
  have hslom_r : sl_om' rIdx = slices3 rIdx :=
    (hslom_ne hom_ne_r.symm).trans (hsll_ne hl_ne_r.symm)
  have hreb_other : ∀ b' < numBucketsWhp n_max, b' ≠ b → ∀ r < 3,
      rebQuad.1 (3 * b' + r) = fs.slices (3 * b' + r) := fun b' hb' hbb r hr => by
    obtain ⟨hne1, hne2, hne3⟩ := hslice_other b' hb' hbb r hr
    exact (hrebQ_ne hne3).trans ((hslom_ne hne2).trans ((hsll_ne hne1).trans
      ((hsl3_ne hne3).trans ((hsl2_ne hne2).trans (hsl1_ne hne1)))))
  have hpool := pool_release_last (fs' := fsA) hv.toCore hb hcnt rfl rfl rfl
    (by dsimp only [fsA, fastDeleteShrink, fs2, fs1]; split_ifs <;> rfl)
    (by dsimp only [fsA, fastDeleteShrink, fs2, fs1]; split_ifs <;> rfl)
  obtain ⟨hq_inj, hdict_map⟩ := dict_map_after_delete (fs' := fsA) hv.toCore rfl hcnt
    (by omega) hq_del rfl
    (fun b' hb' hbb loc hloc =>
      hqv_pres b' hb' loc (hcntA_other hbb ▸ hloc) (fun ⟨h, _⟩ => hbb h))
    (fun loc' hloc' => by
      have hl' : loc' < fsA.bktCount b := by omega
      obtain ⟨ho, -, -, -, -, hq, hv', hne⟩ := horig b hb loc' hl'
      refine ⟨orig b loc', by omega, hne rfl, hq, hv',
        fun l₂ hl₂ heq => horig_inj hl' (by omega) ?_⟩
      obtain ⟨ho₂, -, -, -, -, hq₂, -⟩ := horig b hb l₂ (by omega)
      rw [hphys_eq, hq, hq₂] at heq
      exact hv.quot_inj b hb _ ho _ ho₂ heq)
    (fun loc hloc hne => by
      by_cases hll : loc = loc_last
      · rw [hll]; exact ⟨loc_del, hlt_ll_b, hqv_at_del.1, hqv_at_del.2⟩
      · have hp := hqv_pres b hb loc (by omega) (fun ⟨_, h⟩ => hne h)
        exact ⟨loc, by omega, hp.1, hp.2⟩)
  -- Live slice preservation on bucket `b` via `sliceMapRel_relocate_full`
  have hlive_b : ∃ liveMap',
      ValidWhpSlice n_max (fsA.liveInsCount b) (fsA.slices (fsA.liveSliceIdx b)) liveMap' ∧
      SliceMapRel (fsA.fpAt c U n_max θ (fsA.bktSalt b) b)
        (fun loc => inLiveTree fsA.rebStage fsA.oldEp (fsA.rebDoneFlag b) (fsA.locState b loc) =
          true)
        (fsA.bktCount b) liveMap' := by
    obtain ⟨lm0, hvl0, hrl0⟩ := hv.live_valid b hb
    rw [hcnt] at hrl0
    obtain ⟨hm1_some, hrel_full⟩ := sliceMapRel_relocate_full hrl0
      (f' := fsA.fpAt c U n_max θ (fs.bktSalt b) b)
      (P' := fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fsA.locState b loc) =
        true)
      hlt_ll_b (fun l₁ hl₁ l₂ hl₂ => hv.live_fp_inj b hb l₁ (hcnt ▸ hl₁) l₂ (hcnt ▸ hl₂))
      (fun loc hlt hne => hfp_pres _ b hb loc (by omega) (fun ⟨_, h⟩ => hne h))
      (hfp_at_del _)
      (fun loc hlt hne => by rw [hls_pres b hb loc (by omega) (fun ⟨_, h⟩ => hne h)])
      (by rw [hls_at_del])
    have hlic_le := hv.liveInsCount_le hb
    let m1 :=
      if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) = true then
        Function.update lm0 (fs.fpAt c U n_max θ (fs.bktSalt b) b loc_del) none
      else lm0
    have hv_s1 : ValidWhpSlice n_max (fs.liveInsCount b) (slices1 lIdx) m1 := by
      dsimp only [slices1, m1]
      split_ifs with hin_d
      · rw [Function.update_self, ← hfp_live_del]
        exact hvl0.delete_spec hv.hth hlic_le (fpAt_lt θ fs (fs.bktSalt b) b loc_del)
      · exact hvl0
    have hv_s2 : ValidWhpSlice n_max (fs.liveInsCount b) (sl_live' lIdx)
        (if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_last) = true then
          Function.update m1 (fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last) (some loc_del)
        else m1) := by
      by_cases hin_l :
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_last) = true
      · have hsll_eq : sl_live' lIdx =
            btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (slices1 lIdx) (fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last) loc_del := by
          dsimp only [sl_live']
          have hin_l1 : inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last = true :=
            hin_l
          rw [ite_eq_left hin_l1, Function.update_self]
          dsimp only [fs1]; rw [hsl3_l, hfp1_live]
        rw [hsll_eq, ite_eq_left hin_l]
        have hloc_val : loc_del < 2 ^ valLaneBitsWhp n_max := by rw [two_pow_valLaneBitsWhp]; omega
        have hupd := hv_s1.update_spec hv.hth hlic_le
          (fpAt_lt θ fs (fs.bktSalt b) b loc_last) hloc_val
        rwa [ite_eq_left (hm1_some hin_l)] at hupd
      · have hsll_eq : sl_live' lIdx = slices1 lIdx := by
          dsimp only [sl_live']
          have hnin_l1 : ¬(inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last = true) :=
            hin_l
          rw [ite_eq_right hnin_l1]
          exact hsl3_l
        rw [hsll_eq, ite_eq_right hin_l]
        exact hv_s1
    let m2 :=
      if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_last) = true then
        Function.update m1 (fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last) (some loc_del)
      else m1
    refine ⟨m2, ?_, ?_⟩
    · change ValidWhpSlice n_max (fs.liveInsCount b) (rebQuad.1 lIdx) m2
      rw [hreb_l]; exact hv_s2
    · change SliceMapRel (fsA.fpAt c U n_max θ (fs.bktSalt b) b)
        (fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b)
          (fsA.locState b loc) = true)
        (Function.update fs.bktCount b loc_last b) m2
      rw [Function.update_self]
      exact hrel_full
  have hpres_lt : loc_del < loc_last →
      (∀ b' < numBucketsWhp n_max, ∀ loc < fsA.bktCount b', ¬(b' = b ∧ loc = loc_del) →
        fsA.locState b' loc = fs.locState b' loc ∧
        fsA.rKeyAt c U n_max θ b' loc = fs.rKeyAt c U n_max θ b' loc) ∧
      fsA.locState b loc_del = fs.locState b loc_last ∧
      fsA.rKeyAt c U n_max θ b loc_del = fs.rKeyAt c U n_max θ b loc_last :=
    fun _ => ⟨fun b' hb' loc hloc hne => ⟨hls_pres b' hb' loc hloc hne,
      hrk_pres b' hb' loc hloc hne⟩, hls_at_del, hrk_at_del⟩
  have hb_old_eq : fsA.buf fs.oldEp =
      (let tr1 :=
        if fs.locState b loc_del = 2 + fs.oldEp then
          bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey_u
        else fs.buf fs.oldEp
      if loc_del < loc_last then
        if fs.locState b loc_last = 2 + fs.oldEp then
          bufInsert (cTabWhp c) (bCharWhp n_max) tr1
            (fs.rKeyAt c U n_max θ b loc_last) b loc_del
        else tr1
      else tr1) := by
    have hb1_old : buf1 fs.oldEp =
        if fs.locState b loc_del = 2 + fs.oldEp then
          bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey_u
        else fs.buf fs.oldEp := buf_del_at_ep fs.buf (FastState.oldEp_or hv.curEp_or)
    have hb2_old : fsA.buf fs.oldEp =
        if fs.locState b loc_last = 2 + fs.oldEp then
          bufInsert (cTabWhp c) (bCharWhp n_max) (buf1 fs.oldEp)
            (fs.rKeyAt c U n_max θ b loc_last) b loc_del
        else buf1 fs.oldEp := by
      rw [← hrk1_last]
      exact buf_ins_at_ep buf1 (FastState.oldEp_or hv.curEp_or)
    dsimp only
    rw [ite_eq_left hlt_ll_b, hb2_old, hb1_old]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine
      { hth := hv.hth
        curEp_or := hv.curEp_or
        epochClock_lt := hv.epochClock_lt
        rebStage_le := hv.rebStage_le
        rebCollision_zero := hv.rebCollision_zero
        qv_global := fun p => by
          dsimp only [fsA, fastDeleteShrink, fs2, qArr', vArr', fs1]
          by_cases hp : p = p_del
          · rw [hp]; simp [hv.qv_global p_last]
          · simp [hp, hv.qv_global p]
        bktCount_le := fun b' hb' => by
          dsimp only [fsA, fastDeleteShrink, fs2, fs1]
          by_cases hbb : b' = b
          · rw [hbb, Function.update_self]
            have := hv.bktCount_le b hb; omega
          · rw [Function.update_of_ne hbb]; exact hv.bktCount_le b' hb'
        bktCount_ge_zero := fun b' hge => by
          dsimp only [fsA, fastDeleteShrink, fs2, fs1]
          rw [Function.update_of_ne (by omega)]; exact hv.bktCount_ge_zero b' hge
        locState_active := fun b' hb' loc hloc => by
          obtain ⟨ho, hs, -⟩ := horig b' hb' loc hloc
          rw [hs]; exact hv.locState_active b' hb' _ ho
        locState_inactive := fun b' loc hna => by
          dsimp only [fsA, fastDeleteShrink, fs2, fs1] at hna ⊢
          by_cases hbb : b' = b
          · rw [hbb] at hna ⊢
            rw [Function.update_self] at hna ⊢
            rw [Function.update_self]
            by_cases hll : loc = loc_last
            · rw [hll]; simp
            · have hne_d : loc ≠ loc_del := fun hd => hna ⟨hb, hd ▸ hlt_ll_b⟩
              rw [Function.update_of_ne hll, Function.update_of_ne hne_d]
              exact hv.locState_inactive b loc fun ⟨_, hlt⟩ => hna ⟨hb, by omega⟩
          · simp only [Function.update_of_ne hbb] at hna ⊢
            exact hv.locState_inactive b' loc hna
        active_item := fun b' hb' loc hloc => by
          obtain ⟨ho, -, -, -, hk, hq, hv', -⟩ := horig b' hb' loc hloc
          dsimp only
          rw [hk, hphys_eq, hq, hv']
          exact hv.active_item b' hb' _ ho
        quot_inj := hq_inj
        dict_map := hdict_map
        poolFreeTop_le := hpool.1
        backPtr_valid := hpool.2.1
        freeStack_lt := hpool.2.2.1
        backPtr_inj := hpool.2.2.2.1
        freeStack_inj := hpool.2.2.2.2.1
        back_free_disj := hpool.2.2.2.2.2.1
        pool_conservation := hpool.2.2.2.2.2.2
        roles_valid := hv.roles_valid
        bktSalt_lt := hv.bktSalt_lt
        live_fp_inj := fun b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq => by
          obtain ⟨ho₁, hs₁, hf₁, -⟩ := horig b' hb' l₁ hl₁
          obtain ⟨ho₂, hs₂, hf₂, -⟩ := horig b' hb' l₂ hl₂
          rw [hs₁] at hin₁; rw [hs₂] at hin₂
          change FastState.fpAt c U n_max θ fsA (fs.bktSalt b') b' l₁ =
            FastState.fpAt c U n_max θ fsA (fs.bktSalt b') b' l₂ at hfeq
          rw [hf₁, hf₂] at hfeq
          exact horig_inj hl₁ hl₂ (hv.live_fp_inj b' hb' _ ho₁ _ ho₂ hin₁ hin₂ hfeq)
        live_valid := fun b' hb' => by
          by_cases hbb : b' = b
          · rw [hbb]; exact hlive_b
          · obtain ⟨lm, hvl, hrl⟩ := hv.live_valid b' hb'
            refine ⟨lm, ?_, ?_⟩
            · dsimp only [fsA, fastDeleteShrink, fs2, FastState.liveSliceIdx, fs1]
              rw [hreb_other b' hb' hbb _ (hv.roles_valid b' hb').1]
              exact hvl
            · rw [hcntA_other hbb]
              refine hrl.congr
                (fun loc hloc => hfp_pres _ b' hb' loc (hcntA_other hbb ▸ hloc)
                  (fun ⟨h, _⟩ => hbb h))
                (fun loc _ => ?_)
              dsimp only [fsA, fastDeleteShrink, fs2, fs1, FastState.oldEp]
              simp only [Function.update_of_ne hbb]
        rKey_buf_inj := fun b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂ hst₁ hst₂ hrkeq => by
          obtain ⟨ho₁, hs₁, -, hr₁, -⟩ := horig b₁ hb₁ l₁ hl₁
          obtain ⟨ho₂, hs₂, -, hr₂, -⟩ := horig b₂ hb₂ l₂ hl₂
          rw [hs₁] at hst₁; rw [hs₂] at hst₂; rw [hr₁, hr₂] at hrkeq
          obtain ⟨rfl, heq_o⟩ := hv.rKey_buf_inj b₁ hb₁ _ ho₁ b₂ hb₂ _ ho₂ hst₁ hst₂ hrkeq
          exact ⟨rfl, horig_inj hl₁ hl₂ heq_o⟩
        bufCur_valid := by
          have hb1 : buf1 fs.curEp =
              if st_del = 2 + fs.curEp then
                bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey_u
              else fs.buf fs.curEp := buf_del_at_ep fs.buf hv.curEp_or
          have hb2 : buf2 fs.curEp =
              if fs.locState b loc_last = 2 + fs.curEp then
                bufInsert (cTabWhp c) (bCharWhp n_max) (buf1 fs.curEp)
                  (fs.rKeyAt c U n_max θ b loc_last) b loc_del
              else buf1 fs.curEp := by
            rw [← hrk1_last]
            exact buf_ins_at_ep buf1 hv.curEp_or
          obtain ⟨hia_eq, hna_eq, hmap_cur, _⟩ :=
            buf_valid_after_delete (ep := fs.curEp) (fs' := fsA) hv.toCore hb hcnt
              (hcnt ▸ hld_lt_b) hrk_del hv.bufCur_valid rfl
              (fun heq => absurd heq (Nat.ne_of_lt hlt_ll_b)) hpres_lt
          dsimp only [st_del] at hb1 ⊢
          rw [ite_eq_left hlt_ll_b, ← hb1, ← hb2] at hia_eq hna_eq hmap_cur
          exact ⟨hia_eq ▸ hv.bufCur_valid.1,
            hna_eq ▸ hia_eq ▸ hv.bufCur_valid.2.1, hmap_cur⟩
        bufOld_valid := bufOld_valid_after_delete hv.toCore hb hcnt (hcnt ▸ hld_lt_b) hrk_del rfl
          rfl rfl hb_old_eq (fun heq => absurd heq (Nat.ne_of_lt hlt_ll_b)) hpres_lt }
  · -- `OvermarsBucketInv` on `b' ≠ b`
    intro b' hb' hbb
    refine OvermarsBucketInv.of_eq_lt (hv.overmars_valid b' hb') rfl
      (fun loc hloc => hfp_pres _ b' hb' loc (hcntA_other hbb ▸ hloc) (fun ⟨h, _⟩ => hbb h))
      rfl rfl rfl
      (fun loc hloc => hls_pres b' hb' loc (hcntA_other hbb ▸ hloc) (fun ⟨h, _⟩ => hbb h))
      (hcntA_other hbb).ge rfl rfl rfl ?_ ?_
    · dsimp only [fsA, fastDeleteShrink, fs2, omIns', omPair]
      split_ifs <;> first | rfl | exact Function.update_of_ne hbb _ _
    · dsimp only [fsA, fastDeleteShrink, fs2, FastState.overmarsSliceIdx, fs1]
      exact hreb_other b' hb' hbb _ (hv.roles_valid b' hb').2.1
  · -- `PreOvermarsBucketInv` on `b`
    rcases hv.overmars_valid b hb with
      ⟨ha0, hlic⟩ | ⟨ha1, h16, hcur_lt, hlin, hins, omM, hv_om, hr_om⟩
    · exact Or.inl ⟨ha0, hlic.le⟩
    dsimp only [PreOvermarsBucketInv]
    right
    have hcur_le : fs.overmarsCursor b ≤ loc_last := by omega
    have hnll_cur : ¬(loc_last < fs.overmarsCursor b) := by omega
    have hoi_ub : fs.overmarsInsCount b ≤ 8 * (slabScale n_max) ^ 12 := by omega
    have hom_sl : fsA.slices (fsA.overmarsSliceIdx b) = omPair.1 omIdx := hreb_om
    have hom_ins : fsA.overmarsInsCount b = omPair.2 b := rfl
    have hoa_eq : fsA.overmarsActive b = fs.overmarsActive b := rfl
    have hlic_eq : fsA.liveInsCount b = fs.liveInsCount b := rfl
    have hreb_eq : fsA.rebStage = fs.rebStage := rfl
    have hold_eq : fsA.oldEp = fs.oldEp := rfl
    have hdone_eq : fsA.rebDoneFlag b = fs.rebDoneFlag b := rfl
    have hsalt_eq : fsA.bktSalt b = fs.bktSalt b := rfl
    have hoc_eq : fsA.overmarsCursor b = fs.overmarsCursor b := rfl
    rw [hom_sl, hom_ins, hoa_eq, hoc_eq, hlic_eq, hcntA_b, Nat.min_eq_right hcur_le,
      hsalt_eq, hreb_eq, hold_eq, hdone_eq]
    by_cases hld_cur : loc_del < fs.overmarsCursor b
    · let m1 :=
        if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) = true then
          Function.update omM (fs.fpAt c U n_max θ (fs.bktSalt b) b loc_del) none
        else omM
      have hv_om1 : ValidWhpSlice n_max (fs.overmarsInsCount b) (slices2 omIdx) m1 := by
        dsimp only [slices2, m1, st_del]
        by_cases hin_d :
            inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) = true
        · rw [ite_eq_left ⟨ha1, hld_cur, hin_d⟩, ite_eq_left hin_d, Function.update_self,
            hsl1_om, ← hfp_live_del]
          exact hv_om.delete_spec hv.hth hoi_ub (fpAt_lt θ fs (fs.bktSalt b) b loc_del)
        · rw [ite_eq_right (fun ⟨_, _, h⟩ => hin_d h), ite_eq_right hin_d, hsl1_om]
          exact hv_om
      have hrel_pre := sliceMapRel_relocate_prefix hr_om
        (f' := fsA.fpAt c U n_max θ (fs.bktSalt b) b)
        (P' := fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b)
          (fsA.locState b loc) = true)
        (loc_last := loc_last)
        hld_cur
        (fun l₁ hl₁ l₂ hl₂ => hv.live_fp_inj b hb l₁ (hl₁.trans hcur_lt) l₂ (hl₂.trans hcur_lt))
        (fun hpl l hl _ hpl_l heq =>
          Nat.ne_of_lt (hl.trans_le hcur_le)
            (hv.live_fp_inj b hb l (hl.trans hcur_lt) loc_last hll_lt hpl_l hpl heq))
        (fun loc hlt hne => hfp_pres _ b hb loc (by omega) (fun ⟨_, h⟩ => hne h))
        (hfp_at_del _)
        (fun loc hlt hne => by rw [hls_pres b hb loc (by omega) (fun ⟨_, h⟩ => hne h)])
        (by rw [hls_at_del])
      dsimp only at hrel_pre
      by_cases hin_l :
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_last) = true
      · have hcond_om : fs1.overmarsActive b = 1 ∧
            inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last = true :=
          ⟨ha1, hin_l⟩
        have homPair_eq : omPair =
            (Function.update sl_live' omIdx
              (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                (sl_live' omIdx) fp_live_last loc_del),
             Function.update fs.overmarsInsCount b (fs.overmarsInsCount b + 1)) := by
          dsimp only [omPair]
          rw [ite_eq_left hcond_om, ite_eq_right hnll_cur, ite_eq_left hld_cur]
        have hloc_val : loc_del < 2 ^ valLaneBitsWhp n_max := by
          rw [two_pow_valLaneBitsWhp]; omega
        have hins_om := hv_om1.insert_spec hv.hth hoi_ub
          (fpAt_lt θ fs (fs.bktSalt b) b loc_last) hloc_val
        rw [homPair_eq]; dsimp only
        rw [Function.update_self, Function.update_self, hsll_om, hfp1_live]
        rw [ite_eq_left hin_l] at hrel_pre
        exact ⟨ha1, h16, hcur_le, by omega, by omega, _, hins_om.2, hrel_pre⟩
      · have hncond_om : ¬(fs1.overmarsActive b = 1 ∧
            inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last = true) :=
          fun ⟨_, h⟩ => hin_l h
        have homPair_eq : omPair = (sl_live', fs.overmarsInsCount) := by
          dsimp only [omPair]; rw [ite_eq_right hncond_om]
        rw [homPair_eq]; dsimp only; rw [hsll_om]
        rw [ite_eq_right hin_l] at hrel_pre
        exact ⟨ha1, h16, hcur_le, by omega, by omega, m1, hv_om1, hrel_pre⟩
    · have homPair_eq : omPair = (sl_live', fs.overmarsInsCount) := by
        dsimp only [omPair]; rw [ite_eq_right hnll_cur, ite_eq_right hld_cur, ite_self]
      have hsl2_om : slices2 omIdx = fs.slices omIdx := by
        dsimp only [slices2]
        rw [ite_eq_right (fun ⟨_, h, _⟩ => hld_cur h), hsl1_om]
      rw [homPair_eq]; dsimp only; rw [hsll_om, hsl2_om]
      refine ⟨ha1, h16, hcur_le, by omega, by omega, omM, hv_om, hr_om.congr
        (fun loc hlt => hfp_pres _ b hb loc (by omega) (fun ⟨_, h⟩ => hld_cur (h ▸ hlt)))
        (fun loc hlt => ?_)⟩
      rw [hls_pres b hb loc (by omega) (fun ⟨_, h⟩ => hld_cur (h ▸ hlt))]
  · -- `ValidEpochStagePreTick` on `fsA`: Stages 0, 1, 3 via `preTick_after_delete_of_stage2`
    refine preTick_after_delete_of_stage2 hv.toCore hv.stage_valid.toPreTick hb hcnt
      (hcnt ▸ hld_lt_b) hrk_del rfl rfl rfl rfl rfl rfl rfl rfl rfl hb_old_eq
      (fun heq => absurd heq (Nat.ne_of_lt hlt_ll_b)) hpres_lt fun hs2 => ?_
    have hstg_full := hv.stage_valid
    dsimp only [ValidEpochStage] at hstg_full
    simp only [hs2, show ¬(2 = 0) by decide, show ¬(2 = 1) by decide, ↓reduceIte] at hstg_full
    rcases hstg_full with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hreb⟩
    refine ⟨hd1, hd2, hd3, hd4, hd5, fun b' hb' loc hloc hst_old => ?_, ?_⟩
    · obtain ⟨ho, hs, -⟩ := horig b' hb' loc hloc
      rw [hs] at hst_old
      exact hd6 b' hb' _ ho hst_old
    · set bc := fs.dirtyBuckets fs.dirtyIdx
      have hbc : bc < numBucketsWhp n_max := hd3 fs.dirtyIdx hd2
      change rebQuad.2.1 < sMaxWhp c n_max →
        ((rebQuad.2.2.1 = 0 ∧ rebQuad.2.2.2 = 0) ∨
         (16 ≤ rebQuad.2.2.1 ∧ rebQuad.2.2.1 ≤ fsA.bktCount bc ∧
          16 * rebQuad.2.2.2 ≤ 17 * rebQuad.2.2.1)) ∧
        (∀ l₁ < min (fsA.bktCount bc) rebQuad.2.2.1,
         ∀ l₂ < min (fsA.bktCount bc) rebQuad.2.2.1,
          (fsA.locState bc l₁ = 1 ∨ fsA.locState bc l₁ = 2 + fs.oldEp) →
          (fsA.locState bc l₂ = 1 ∨ fsA.locState bc l₂ = 2 + fs.oldEp) →
          fsA.fpAt c U n_max θ rebQuad.2.1 bc l₁ =
            fsA.fpAt c U n_max θ rebQuad.2.1 bc l₂ →
          l₁ = l₂) ∧
        ∃ rebMap,
          ValidWhpSlice n_max rebQuad.2.2.2 (rebQuad.1 (fs.rebSliceIdx bc)) rebMap ∧
          SliceMapRel (fsA.fpAt c U n_max θ rebQuad.2.1 bc)
            (fun loc => fsA.locState bc loc = 1 ∨ fsA.locState bc loc = 2 + fs.oldEp)
            (min (fsA.bktCount bc) rebQuad.2.2.1) rebMap
      intro hcs_new
      by_cases hbb : bc = b
      · have hcs0 : fs.rebCandSalt < sMaxWhp c n_max := by
          by_contra hge
          have hrbf : rebActiveB = false :=
            decide_eq_false (fun ⟨_, _, _, h, _⟩ => hge h)
          have hcs_eq : rebQuad.2.1 = fs.rebCandSalt := by
            dsimp only [rebQuad, fs1]; rw [hrbf]; rfl
          omega
        have hrbt : rebActiveB = true :=
          decide_eq_true ⟨hs2, hd2, hbb, hcs0, hv.rebCollision_zero⟩
        obtain ⟨hcur_r, hinj_r, rm0, hvr0, hrr0⟩ := hreb hcs0
        rw [hbb] at hcur_r hinj_r hvr0 hrr0 ⊢
        change _ ∧ _ ∧ ∃ rebMap,
          ValidWhpSlice n_max rebQuad.2.2.2 (rebQuad.1 rIdx) rebMap ∧ _
        rw [hcntA_b]
        have hcur_le_ll : fs.rebScanCursor ≤ loc_last := by omega
        have hnll_r : ¬(loc_last < fs.rebScanCursor) := by omega
        have hmin_old : min (fs.bktCount b) fs.rebScanCursor = fs.rebScanCursor :=
          Nat.min_eq_right (by omega)
        rw [hmin_old] at hinj_r hrr0
        have hri_ub : fs.rebInsCount ≤ 8 * (slabScale n_max) ^ 12 := by omega
        let P_r (st : ℕ → ℕ) (loc : ℕ) : Prop :=
          st loc = 1 ∨ st loc = 2 + fs.oldEp
        -- Coordinates below the cursor other than `loc_del` are unchanged.
        have hpres_r : ∀ l < fs.rebScanCursor, l ≠ loc_del →
            fsA.locState b l = fs.locState b l ∧
            fsA.fpAt c U n_max θ fs.rebCandSalt b l = fs.fpAt c U n_max θ fs.rebCandSalt b l :=
          fun l _ hne => ⟨hls_pres b hb l (by omega) (fun ⟨_, h⟩ => hne h),
            hfp_pres _ b hb l (by omega) (fun ⟨_, h⟩ => hne h)⟩
        have hinj_ne : ∀ l₁ < fs.rebScanCursor, ∀ l₂ < fs.rebScanCursor,
            l₁ ≠ loc_del → l₂ ≠ loc_del → P_r (fsA.locState b) l₁ → P_r (fsA.locState b) l₂ →
            fsA.fpAt c U n_max θ fs.rebCandSalt b l₁ = fsA.fpAt c U n_max θ fs.rebCandSalt b l₂ →
            l₁ = l₂ := by
          intro l₁ hl₁ l₂ hl₂ hne₁ hne₂ hp₁ hp₂ hfeq
          obtain ⟨hs₁, hf₁⟩ := hpres_r l₁ hl₁ hne₁
          obtain ⟨hs₂, hf₂⟩ := hpres_r l₂ hl₂ hne₂
          dsimp only [P_r] at hp₁ hp₂
          rw [hs₁] at hp₁; rw [hs₂] at hp₂; rw [hf₁, hf₂] at hfeq
          exact hinj_r l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
        by_cases hld_r : loc_del < fs.rebScanCursor
        · have hcur_pos :
              16 ≤ fs.rebScanCursor ∧ 16 * fs.rebInsCount + 16 ≤ 17 * fs.rebScanCursor := by
            omega
          let mr1 :=
            if P_r (fs.locState b) loc_del then
              Function.update rm0 (fs.fpAt c U n_max θ fs.rebCandSalt b loc_del) none
            else rm0
          have hv_r1 : ValidWhpSlice n_max fs.rebInsCount (slices3 rIdx) mr1 := by
            dsimp only [slices3, mr1, P_r, st_del]
            rw [hrbt, Bool.true_and]
            by_cases hpd : fs.locState b loc_del = 1 ∨ fs.locState b loc_del = 2 + fs.oldEp
            · rw [decide_eq_true ⟨hld_r, hpd⟩, ite_eq_left rfl, ite_eq_left hpd,
                Function.update_self, hsl2_r, ← hfp_cand_del]
              exact hvr0.delete_spec hv.hth hri_ub (fpAt_lt θ fs fs.rebCandSalt b loc_del)
            · rw [decide_eq_false (fun ⟨_, h⟩ => hpd h)]
              simp only [Bool.false_eq_true, ↓reduceIte]
              rw [ite_eq_right hpd, hsl2_r]
              exact hvr0
          have hrel_of := fun hno => sliceMapRel_relocate_prefix hrr0
            (f' := fsA.fpAt c U n_max θ fs.rebCandSalt b)
            (P' := P_r (fsA.locState b)) (loc_last := loc_last) hld_r hinj_r hno
            (fun loc hlt hne => (hpres_r loc hlt hne).2) (hfp_at_del _)
            (fun loc hlt hne => by dsimp only [P_r]; rw [(hpres_r loc hlt hne).1])
            (by dsimp only [P_r]; rw [hls_at_del])
          by_cases hpl_r : fs.locState b loc_last = 1 ∨ fs.locState b loc_last = 2 + fs.oldEp
          · have hcond_q :
                (rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs1.oldEp)) = true := by
              rw [hrbt, Bool.true_and]
              exact decide_eq_true hpl_r
            have hrebQ_branch : rebQuad =
                match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                    (sl_om' rIdx) fp_cand_last with
                | some _ =>
                  (Function.update sl_om' rIdx (resetBTreeSlice (sl_om' rIdx)),
                   (fs.rebCandSalt + 1, (0, 0)))
                | none =>
                  (Function.update sl_om' rIdx
                    (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                      (sl_om' rIdx) fp_cand_last loc_del),
                   (fs.rebCandSalt, (fs.rebScanCursor, fs.rebInsCount + 1))) := by
              dsimp only [rebQuad, fs1]
              rw [hcond_q, ite_eq_left rfl, ite_eq_right hnll_r, ite_eq_left hld_r]
            rw [hrebQ_branch]
            have hlk_eq :
                btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                  (sl_om' rIdx) fp_cand_last = mr1 fp_cand_last := by
              rw [hslom_r, hfp1_cand]
              exact hv_r1.lookup_eq hv.hth hri_ub (fpAt_lt θ fs fs.rebCandSalt b loc_last)
            cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                (sl_om' rIdx) fp_cand_last with
            | some _ =>
              dsimp only
              rw [Nat.min_zero, Function.update_self]
              exact ⟨Or.inl ⟨rfl, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
                fun _ => none, validWhpSlice_zero _ 0 _,
                SliceMapRel.empty_of_not _ _ 0 fun _ h => absurd h (Nat.not_lt_zero _)⟩
            | none =>
              have hmr1_none : mr1 (fs.fpAt c U n_max θ fs.rebCandSalt b loc_last) = none := by
                rw [← hfp1_cand, ← hlk_eq, hlk]
              have hno_coll_r : ∀ l < fs.rebScanCursor, l ≠ loc_del →
                  P_r (fs.locState b) l →
                  fs.fpAt c U n_max θ fs.rebCandSalt b l ≠
                    fs.fpAt c U n_max θ fs.rebCandSalt b loc_last := by
                intro l hl hne hpl_l heq
                have h0_some : rm0 (fs.fpAt c U n_max θ fs.rebCandSalt b l) = some l :=
                  (hrr0.2 _ l).mpr ⟨hl, hpl_l, rfl⟩
                have hmr1_some : mr1 (fs.fpAt c U n_max θ fs.rebCandSalt b l) = some l := by
                  dsimp only [mr1]
                  split_ifs with hpd
                  · have hne_fp : fs.fpAt c U n_max θ fs.rebCandSalt b l ≠
                        fs.fpAt c U n_max θ fs.rebCandSalt b loc_del := fun hfe =>
                      hne (hinj_r l hl loc_del hld_r hpl_l hpd hfe)
                    rwa [Function.update_of_ne hne_fp]
                  · exact h0_some
                rw [heq, hmr1_none] at hmr1_some
                cases hmr1_some
              dsimp only
              rw [Nat.min_eq_right hcur_le_ll, Function.update_self, hslom_r, hfp1_cand]
              have hloc_val : loc_del < 2 ^ valLaneBitsWhp n_max := by
                rw [two_pow_valLaneBitsWhp]; omega
              have hins_r := hv_r1.insert_spec hv.hth hri_ub
                (fpAt_lt θ fs fs.rebCandSalt b loc_last) hloc_val
              have hrel_r := hrel_of fun _ => hno_coll_r
              dsimp only at hrel_r
              rw [ite_eq_left hpl_r] at hrel_r
              refine ⟨Or.inr ⟨hcur_pos.1, hcur_le_ll, by omega⟩, ?_, _, hins_r.2, hrel_r⟩
              intro l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
              by_cases hd1 : l₁ = loc_del <;> by_cases hd2 : l₂ = loc_del
              · exact hd1.trans hd2.symm
              · obtain ⟨hs₂, hf₂⟩ := hpres_r l₂ hl₂ hd2
                rw [hd1, hfp_at_del, hf₂] at hfeq; rw [hs₂] at hp₂
                exact absurd hfeq.symm (hno_coll_r l₂ hl₂ hd2 hp₂)
              · obtain ⟨hs₁, hf₁⟩ := hpres_r l₁ hl₁ hd1
                rw [hd2, hfp_at_del, hf₁] at hfeq; rw [hs₁] at hp₁
                exact absurd hfeq (hno_coll_r l₁ hl₁ hd1 hp₁)
              · exact hinj_ne l₁ hl₁ l₂ hl₂ hd1 hd2 hp₁ hp₂ hfeq
          · have hcond_q :
                (rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs1.oldEp)) = false := by
              rw [Bool.and_eq_false_iff]
              exact Or.inr (decide_eq_false hpl_r)
            have hrebQ_eq :
                rebQuad = (sl_om', (fs.rebCandSalt, (fs.rebScanCursor, fs.rebInsCount))) := by
              dsimp only [rebQuad, fs1]; rw [hcond_q]; rfl
            rw [hrebQ_eq]
            dsimp only
            rw [Nat.min_eq_right hcur_le_ll, hslom_r]
            have hrel_r := hrel_of fun h => absurd h hpl_r
            dsimp only at hrel_r
            rw [ite_eq_right hpl_r] at hrel_r
            refine ⟨Or.inr ⟨hcur_pos.1, hcur_le_ll, by omega⟩,
              fun l₁ hl₁ l₂ hl₂ hp₁ hp₂ => hinj_ne l₁ hl₁ l₂ hl₂ ?_ ?_ hp₁ hp₂, mr1, hv_r1, hrel_r⟩
            · intro h; rw [h, hls_at_del] at hp₁; exact hpl_r hp₁
            · intro h; rw [h, hls_at_del] at hp₂; exact hpl_r hp₂
        · have hrebQ_eq :
              rebQuad = (sl_om', (fs.rebCandSalt, (fs.rebScanCursor, fs.rebInsCount))) := by
            dsimp only [rebQuad]
            by_cases h1 : (rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs1.oldEp)) = true
            · rw [ite_eq_left h1, ite_eq_right hnll_r, ite_eq_right hld_r]
            · rw [ite_eq_right h1]
          have hsl3_r : slices3 rIdx = fs.slices rIdx := by
            dsimp only [slices3]
            have hd_fls : (rebActiveB && decide (loc_del < fs.rebScanCursor ∧
                (st_del = 1 ∨ st_del = 2 + fs.oldEp))) = false := by
              rw [Bool.and_eq_false_iff]
              exact Or.inr (decide_eq_false (fun ⟨h, _⟩ => hld_r h))
            rw [hd_fls]; exact hsl2_r
          rw [hrebQ_eq]
          dsimp only
          rw [Nat.min_eq_right hcur_le_ll, hslom_r, hsl3_r]
          have hne : ∀ l < fs.rebScanCursor, l ≠ loc_del := fun l hl h => hld_r (h ▸ hl)
          refine ⟨by omega, fun l₁ hl₁ l₂ hl₂ =>
              hinj_ne l₁ hl₁ l₂ hl₂ (hne l₁ hl₁) (hne l₂ hl₂), rm0, hvr0, ?_⟩
          exact hrr0.congr (fun loc hlt => (hpres_r loc hlt (hne loc hlt)).2)
            (fun loc hlt => by rw [(hpres_r loc hlt (hne loc hlt)).1])
      · have hrbf : rebActiveB = false :=
          decide_eq_false (fun ⟨_, _, h, _, _⟩ => hbb h)
        have hrebQ_eq :
            rebQuad = (sl_om', (fs.rebCandSalt, (fs.rebScanCursor, fs.rebInsCount))) := by
          dsimp only [rebQuad, fs1]; rw [hrbf]; rfl
        rw [hrebQ_eq] at hcs_new ⊢
        dsimp only at hcs_new ⊢
        obtain ⟨hcur_r, hinj_r, rm0, hvr0, hrr0⟩ := hreb hcs_new
        have hsl_bc : sl_om' (fs.rebSliceIdx bc) = fs.slices (fs.rebSliceIdx bc) := by
          have hr_lt := (rebRole_props (hv.roles_valid bc hbc).1
            (hv.roles_valid bc hbc).2.1 (hv.roles_valid bc hbc).2.2).1
          have hsl_eq := hreb_other bc hbc hbb (fs.rebRole bc) hr_lt
          rw [hrebQ_eq] at hsl_eq
          exact hsl_eq
        have hpres_bc : ∀ l < min (fs.bktCount bc) fs.rebScanCursor,
            fsA.locState bc l = fs.locState bc l ∧
            fsA.fpAt c U n_max θ fs.rebCandSalt bc l = fs.fpAt c U n_max θ fs.rebCandSalt bc l :=
          fun l hl =>
            have hlt := hcntA_other hbb ▸ hl.trans_le (Nat.min_le_left _ _)
            ⟨hls_pres bc hbc l hlt (fun ⟨h, _⟩ => hbb h),
              hfp_pres _ bc hbc l hlt (fun ⟨h, _⟩ => hbb h)⟩
        rw [hcntA_other hbb, hsl_bc]
        refine ⟨by omega, fun l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq => ?_, rm0, hvr0,
          hrr0.congr (fun loc hlt => (hpres_bc loc hlt).2)
            (fun loc hlt => by rw [(hpres_bc loc hlt).1])⟩
        obtain ⟨hs₁, hf₁⟩ := hpres_bc l₁ hl₁
        obtain ⟨hs₂, hf₂⟩ := hpres_bc l₂ hl₂
        rw [hs₁] at hp₁; rw [hs₂] at hp₂; rw [hf₁, hf₂] at hfeq
        exact hinj_r l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
