/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModel
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.MapRel

/-!
# Core and Pre-Tick Fast-Mode Invariants for `SuccinctWhpModel`

This module defines the intermediate fast-mode invariants (`CoreFastInv`, `PreOvermarsBucketInv`,
`ValidEpochStagePreTick`) shared across `overmarsStep`, `fastDelete`, `fastInsert`, and
`epochTick`, together with conversion and field-congruence lemmas.

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctWhp.CoreFastInv`: all fields of `ValidFastState` except
  `overmars_valid` and `stage_valid`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.PreOvermarsBucketInv`: relaxed per-bucket Overmars
  invariant immediately prior to `overmarsStep`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidEpochStagePreTick`: relaxed epoch-stage
  invariant between `fastDelete` / `fastInsert` and `epochTick`.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidFastState.toCore`,
  `CoreFastInv.toValidFastState`, `OvermarsBucketInv.toPre`, `ValidEpochStage.toPreTick`:
  conversions between full and pre-step invariants.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.fpAt_lt`, `keyValAt_eq_of_fields`,
  `fpAt_eq_of_fields`, `rKeyAt_eq_of_fields`, `OvermarsBucketInv.of_eq_on`,
  `OvermarsBucketInv.of_eq_lt`: field-congruence helpers for `FastState`.
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset
open scoped BigOperators

/-- Core fast-state invariant (all fields of `ValidFastState` except `overmars_valid` and
`stage_valid`), shared across intermediate pre-`overmarsStep` and pre-`epochTick` states. -/
structure CoreFastInv (c U V n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) (dict : State U) : Prop where
  hth : whpThreshold c ≤ n_max
  curEp_or : fs.curEp = 0 ∨ fs.curEp = 1
  epochClock_lt : fs.epochClock < qEpochWhp n_max
  rebStage_le : fs.rebStage ≤ 5
  rebCollision_zero : fs.rebCollision = 0
  qv_global : ∀ p, fs.quotArr p < 2 ^ quotBitsWhp U n_max ∧ fs.valArr p < max V 1
  bktCount_le : ∀ b < numBucketsWhp n_max, fs.bktCount b ≤ totalLocalCoordsWhp n_max
  bktCount_ge_zero : ∀ b, numBucketsWhp n_max ≤ b → fs.bktCount b = 0
  locState_active : ∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b,
    1 ≤ fs.locState b loc ∧ fs.locState b loc ≤ 3
  locState_inactive : ∀ b loc, ¬(b < numBucketsWhp n_max ∧ loc < fs.bktCount b) →
    fs.locState b loc = 0
  active_item : ∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b,
    let kv := fs.keyValAt c U n_max θ.1 b loc
    kv < U ∧
    feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) kv = b ∧
    keyQuotient (bWhp n_max) kv = fs.quotArr (fs.physSlot n_max b loc) ∧
    fs.valArr (fs.physSlot n_max b loc) < V
  quot_inj : ∀ b < numBucketsWhp n_max, ∀ l₁ < fs.bktCount b, ∀ l₂ < fs.bktCount b,
    fs.quotArr (fs.physSlot n_max b l₁) = fs.quotArr (fs.physSlot n_max b l₂) → l₁ = l₂
  dict_map : ∀ u : Fin U,
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let q := keyQuotient (bWhp n_max) u.val
    (dict u = none ↔ ∀ loc < fs.bktCount b, fs.quotArr (fs.physSlot n_max b loc) ≠ q) ∧
    (∀ v, dict u = some v ↔
      ∃ loc < fs.bktCount b,
        fs.quotArr (fs.physSlot n_max b loc) = q ∧
        fs.valArr (fs.physSlot n_max b loc) = v)
  poolFreeTop_le : fs.poolFreeTop ≤ poolSizeWhp n_max
  backPtr_valid : ∀ b < numBucketsWhp n_max, ∀ k < fs.bktCount b - capFrontWhp n_max,
    fs.backPtr b k < poolSizeWhp n_max ∧
    fs.poolOwner (fs.backPtr b k) = b * capBackWhp n_max + k
  freeStack_lt : ∀ j < fs.poolFreeTop, fs.poolFreeStack j < poolSizeWhp n_max
  backPtr_inj : ∀ b₁ < numBucketsWhp n_max, ∀ k₁ < fs.bktCount b₁ - capFrontWhp n_max,
    ∀ b₂ < numBucketsWhp n_max, ∀ k₂ < fs.bktCount b₂ - capFrontWhp n_max,
      fs.backPtr b₁ k₁ = fs.backPtr b₂ k₂ → b₁ = b₂ ∧ k₁ = k₂
  freeStack_inj : ∀ j₁ < fs.poolFreeTop, ∀ j₂ < fs.poolFreeTop,
    fs.poolFreeStack j₁ = fs.poolFreeStack j₂ → j₁ = j₂
  back_free_disj : ∀ b < numBucketsWhp n_max, ∀ k < fs.bktCount b - capFrontWhp n_max,
    ∀ j < fs.poolFreeTop, fs.backPtr b k ≠ fs.poolFreeStack j
  pool_conservation : fs.poolFreeTop +
    ∑ b ∈ range (numBucketsWhp n_max), (fs.bktCount b - capFrontWhp n_max) = poolSizeWhp n_max
  roles_valid : ∀ b < numBucketsWhp n_max,
    fs.liveRole b < 3 ∧ fs.overmarsRole b < 3 ∧ fs.liveRole b ≠ fs.overmarsRole b
  bktSalt_lt : ∀ b < numBucketsWhp n_max, fs.bktSalt b < sMaxWhp c n_max
  live_fp_inj : ∀ b < numBucketsWhp n_max, ∀ l₁ < fs.bktCount b, ∀ l₂ < fs.bktCount b,
    inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b l₁) = true →
    inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b l₂) = true →
    fs.fpAt c U n_max θ (fs.bktSalt b) b l₁ = fs.fpAt c U n_max θ (fs.bktSalt b) b l₂ →
    l₁ = l₂
  live_valid : ∀ b < numBucketsWhp n_max,
    ∃ liveMap,
      ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) liveMap ∧
      SliceMapRel (fs.fpAt c U n_max θ (fs.bktSalt b) b)
        (fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true)
        (fs.bktCount b) liveMap
  rKey_buf_inj : ∀ b₁ < numBucketsWhp n_max, ∀ l₁ < fs.bktCount b₁,
    ∀ b₂ < numBucketsWhp n_max, ∀ l₂ < fs.bktCount b₂,
      2 ≤ fs.locState b₁ l₁ → 2 ≤ fs.locState b₂ l₂ →
      fs.rKeyAt c U n_max θ b₁ l₁ = fs.rKeyAt c U n_max θ b₂ l₂ →
      b₁ = b₂ ∧ l₁ = l₂
  bufCur_valid :
    (fs.buf fs.curEp).itemAlloc ≤ 2 * sMaxWhp c n_max ∧
    (fs.buf fs.curEp).nodeAlloc ≤ 1 + cTabWhp c * (fs.buf fs.curEp).itemAlloc ∧
    ∃ curMap,
      ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap ∧
      BufMapRel (numBucketsWhp n_max) (2 + fs.curEp) fs.bktCount fs.locState
        (fs.rKeyAt c U n_max θ) curMap
  bufOld_valid :
    if fs.rebStage ≤ 3 then
      (fs.buf fs.oldEp).itemAlloc ≤ 2 * sMaxWhp c n_max ∧
      (fs.buf fs.oldEp).nodeAlloc ≤ 1 + cTabWhp c * (fs.buf fs.oldEp).itemAlloc ∧
      ∃ oldMap,
        ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap ∧
        BufMapRel (numBucketsWhp n_max) (2 + fs.oldEp) fs.bktCount fs.locState
          (fs.rKeyAt c U n_max θ) oldMap
    else if fs.rebStage = 4 then
      (∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b, fs.locState b loc ≠ 2 + fs.oldEp) ∧
      ClearableBufTrie (fs.buf fs.oldEp) ∧
      (fs.buf fs.oldEp).nodeAlloc ≤ 1 + cTabWhp c * (2 * sMaxWhp c n_max)
    else
      (∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b, fs.locState b loc ≠ 2 + fs.oldEp) ∧
      ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) (fun _ => none) ∧
      (fs.buf fs.oldEp).nodeAlloc = 1 ∧
      (fs.buf fs.oldEp).itemAlloc = 0

/-- Relaxed per-bucket Overmars invariant immediately prior to `overmarsStep` on bucket `b`. -/
@[expose] def PreOvermarsBucketInv (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) (b : ℕ) : Prop :=
  (fs.overmarsActive b = 0 ∧ fs.liveInsCount b ≤ 5 * (slabScale n_max) ^ 12) ∨
  (fs.overmarsActive b = 1 ∧
    16 ≤ fs.overmarsCursor b ∧
    fs.overmarsCursor b ≤ fs.bktCount b ∧
    16 * (fs.liveInsCount b - 5 * (slabScale n_max) ^ 12) ≤ fs.overmarsCursor b + 16 ∧
    16 * fs.overmarsInsCount b ≤ 17 * fs.overmarsCursor b ∧
    ∃ omMap,
      ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) omMap ∧
      SliceMapRel (fs.fpAt c U n_max θ (fs.bktSalt b) b)
        (fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true)
        (min (fs.bktCount b) (fs.overmarsCursor b)) omMap)

/-- Stage invariant between `fastDelete` and `epochTick` (relaxing `rebScanCursor < bktCount b_cur`
to `≤` and removing the `+ 16` slack in `16 * rebInsCount ≤ 17 * rebScanCursor` until `epochTick`
scans the next `16` slots). -/
@[expose] def ValidEpochStagePreTick (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) : Prop :=
  let M := numBucketsWhp n_max
  let oldEp := fs.oldEp
  let oldTr := fs.buf oldEp
  if fs.rebStage = 0 then
    fs.stageCursor ≤ oldTr.itemAlloc ∧
    ∀ id < fs.stageCursor, ∀ b loc,
      bufCheckSlot oldTr id = some (b, loc) →
        fs.rebQueued b = 0 ∧ fs.rebDoneFlag b = 0
  else if fs.rebStage = 1 then
    fs.stageCursor ≤ oldTr.itemAlloc ∧
    fs.dirtyCount ≤ fs.stageCursor ∧
    (∀ j < fs.dirtyCount,
      fs.dirtyBuckets j < M ∧
      fs.rebQueued (fs.dirtyBuckets j) = 1 ∧
      fs.rebDoneFlag (fs.dirtyBuckets j) = 0) ∧
    (∀ j₁ < fs.dirtyCount, ∀ j₂ < fs.dirtyCount,
      fs.dirtyBuckets j₁ = fs.dirtyBuckets j₂ → j₁ = j₂) ∧
    (∀ id < oldTr.itemAlloc, ∀ b loc,
      bufCheckSlot oldTr id = some (b, loc) →
        (fs.rebQueued b = 0 ∧ fs.rebDoneFlag b = 0) ∨
        ∃ j < fs.dirtyCount, fs.dirtyBuckets j = b) ∧
    (∀ id < fs.stageCursor, ∀ b loc,
      bufCheckSlot oldTr id = some (b, loc) →
        ∃ j < fs.dirtyCount, fs.dirtyBuckets j = b)
  else if fs.rebStage = 2 then
    fs.dirtyCount ≤ 2 * sMaxWhp c n_max ∧
    fs.dirtyIdx < fs.dirtyCount ∧
    (∀ j < fs.dirtyCount, fs.dirtyBuckets j < M) ∧
    (∀ j₁ < fs.dirtyCount, ∀ j₂ < fs.dirtyCount,
      fs.dirtyBuckets j₁ = fs.dirtyBuckets j₂ → j₁ = j₂) ∧
    (∀ j < fs.dirtyCount,
      (j < fs.dirtyIdx → fs.rebDoneFlag (fs.dirtyBuckets j) = 1) ∧
      (fs.dirtyIdx ≤ j → fs.rebDoneFlag (fs.dirtyBuckets j) = 0)) ∧
    (∀ b < M, ∀ loc < fs.bktCount b, fs.locState b loc = 2 + oldEp →
      ∃ j < fs.dirtyCount, fs.dirtyBuckets j = b) ∧
    (fs.rebCandSalt < sMaxWhp c n_max →
      let b_cur := fs.dirtyBuckets fs.dirtyIdx
      ((fs.rebScanCursor = 0 ∧ fs.rebInsCount = 0) ∨
       (16 ≤ fs.rebScanCursor ∧ fs.rebScanCursor ≤ fs.bktCount b_cur ∧
        16 * fs.rebInsCount ≤ 17 * fs.rebScanCursor)) ∧
      (∀ l₁ < min (fs.bktCount b_cur) fs.rebScanCursor,
       ∀ l₂ < min (fs.bktCount b_cur) fs.rebScanCursor,
        (fs.locState b_cur l₁ = 1 ∨ fs.locState b_cur l₁ = 2 + oldEp) →
        (fs.locState b_cur l₂ = 1 ∨ fs.locState b_cur l₂ = 2 + oldEp) →
        fs.fpAt c U n_max θ fs.rebCandSalt b_cur l₁ =
          fs.fpAt c U n_max θ fs.rebCandSalt b_cur l₂ →
        l₁ = l₂) ∧
      ∃ rebMap,
        ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b_cur)) rebMap ∧
        SliceMapRel (fs.fpAt c U n_max θ fs.rebCandSalt b_cur)
          (fun loc => fs.locState b_cur loc = 1 ∨ fs.locState b_cur loc = 2 + oldEp)
          (min (fs.bktCount b_cur) fs.rebScanCursor) rebMap)
  else if fs.rebStage = 3 then
    fs.stageCursor ≤ oldTr.itemAlloc ∧
    (∀ id < fs.stageCursor, bufCheckSlot oldTr id = none)
  else
    True

theorem ValidFastState.toCore {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict) :
    CoreFastInv c U V n_max θ fs dict :=
  let ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, f22, f23, f24, _, f25, f26, f27, _⟩ := hv
  ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, f22, f23, f24, f25, f26, f27⟩

theorem CoreFastInv.toValidFastState {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hst : ValidEpochStage c U n_max θ fs) :
    ValidFastState c U V n_max θ fs dict :=
  let ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, f22, f23, f24, f25, f26, f27⟩ := hc
  ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, f22, f23, f24, hom, f25, f26, f27, hst⟩

theorem OvermarsBucketInv.toPre {c U n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {b : ℕ} (h : OvermarsBucketInv c U n_max θ fs b) :
    PreOvermarsBucketInv c U n_max θ fs b := by
  rcases h with ⟨h0, hlt⟩ | ⟨h1, h16, hcur, hlin, hins, omMap, hv, hrel⟩
  · exact Or.inl ⟨h0, hlt.le⟩
  · exact Or.inr ⟨h1, h16, hcur.le, by omega, by omega, omMap, hv,
      by rwa [Nat.min_eq_right hcur.le]⟩

theorem ValidEpochStage.toPreTick {c U n_max : ℕ} {θ : SeedWhp c U n_max} {fs : FastState}
    (h : ValidEpochStage c U n_max θ fs) : ValidEpochStagePreTick c U n_max θ fs := by
  dsimp only [ValidEpochStage, ValidEpochStagePreTick] at h ⊢
  split_ifs at h ⊢ with h0 h1 h2 h3 <;> try exact h
  rcases h with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hs⟩
  refine ⟨hd1, hd2, hd3, hd4, hd5, hd6, fun hlt => ?_⟩
  obtain ⟨⟨hc0, hi0⟩ | ⟨h16, hc_lt, hins⟩, hinj, hmap⟩ := hs hlt
  · exact ⟨Or.inl ⟨hc0, hi0⟩, hinj, hmap⟩
  · exact ⟨Or.inr ⟨h16, hc_lt.le, by omega⟩, hinj, hmap⟩

theorem fpAt_lt {c U n_max : ℕ} (θ : SeedWhp c U n_max) (fs : FastState)
    (salt b loc : ℕ) : fs.fpAt c U n_max θ salt b loc < 2 ^ fpBitsWhp n_max := by
  dsimp only [FastState.fpAt]
  split_ifs with hs hu
  · exact fpHash_lt c U n_max θ.2 ⟨salt, hs⟩ ⟨_, hu⟩
  all_goals exact Nat.two_pow_pos _

theorem keyValAt_eq_of_fields {c U n_max : ℕ} {θ₁ : BktSeed c U n_max} {fs₁ fs₂ : FastState}
    (hq : fs₁.quotArr = fs₂.quotArr) (hbp : fs₁.backPtr = fs₂.backPtr) :
    fs₁.keyValAt c U n_max θ₁ = fs₂.keyValAt c U n_max θ₁ := by
  funext b loc
  simp [FastState.keyValAt, FastState.physSlot, hq, hbp]

theorem fpAt_eq_of_fields {c U n_max : ℕ} {θ : SeedWhp c U n_max} {fs₁ fs₂ : FastState}
    (hq : fs₁.quotArr = fs₂.quotArr) (hbp : fs₁.backPtr = fs₂.backPtr) (salt b : ℕ) :
    fs₁.fpAt c U n_max θ salt b = fs₂.fpAt c U n_max θ salt b := by
  funext loc
  simp [FastState.fpAt, keyValAt_eq_of_fields hq hbp]

theorem rKeyAt_eq_of_fields {c U n_max : ℕ} {θ : SeedWhp c U n_max} {fs₁ fs₂ : FastState}
    (hq : fs₁.quotArr = fs₂.quotArr) (hbp : fs₁.backPtr = fs₂.backPtr) :
    fs₁.rKeyAt c U n_max θ = fs₂.rKeyAt c U n_max θ := by
  funext b loc
  simp [FastState.rKeyAt, keyValAt_eq_of_fields hq hbp]

theorem OvermarsBucketInv.of_eq_on {c U n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState} {b : ℕ}
    (h : OvermarsBucketInv c U n_max θ fs b)
    (hfp : fs'.fpAt c U n_max θ (fs'.bktSalt b) b = fs.fpAt c U n_max θ (fs.bktSalt b) b)
    (hst : fs'.rebStage = fs.rebStage)
    (hep : fs'.curEp = fs.curEp)
    (hdn : fs'.rebDoneFlag b = fs.rebDoneFlag b)
    (hls : fs'.locState b = fs.locState b)
    (hcnt : fs'.bktCount b = fs.bktCount b)
    (hlic : fs'.liveInsCount b = fs.liveInsCount b)
    (hoa : fs'.overmarsActive b = fs.overmarsActive b)
    (hoc : fs'.overmarsCursor b = fs.overmarsCursor b)
    (hoi : fs'.overmarsInsCount b = fs.overmarsInsCount b)
    (hsl : fs'.slices (fs'.overmarsSliceIdx b) = fs.slices (fs.overmarsSliceIdx b)) :
    OvermarsBucketInv c U n_max θ fs' b := by
  have hold : fs'.oldEp = fs.oldEp := by simp [FastState.oldEp, hep]
  rcases h with ⟨h0, hlt⟩ | ⟨h1, h16, hcur, hlin, hins, omMap, hv, hrel⟩
  · exact Or.inl ⟨hoa.trans h0, hlic.symm ▸ hlt⟩
  · exact Or.inr ⟨hoa.trans h1, hoc.symm ▸ h16, by omega, by omega, by omega,
      omMap, by rwa [hoi, hsl], by rwa [hfp, hst, hold, hdn, hls, hoc]⟩

theorem OvermarsBucketInv.of_eq_lt {c U n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState} {b : ℕ}
    (h : OvermarsBucketInv c U n_max θ fs b)
    (hsalt : fs'.bktSalt b = fs.bktSalt b)
    (hfp : ∀ loc < fs.bktCount b,
      fs'.fpAt c U n_max θ (fs.bktSalt b) b loc = fs.fpAt c U n_max θ (fs.bktSalt b) b loc)
    (hst : fs'.rebStage = fs.rebStage)
    (hep : fs'.curEp = fs.curEp)
    (hdn : fs'.rebDoneFlag b = fs.rebDoneFlag b)
    (hls : ∀ loc < fs.bktCount b, fs'.locState b loc = fs.locState b loc)
    (hcnt : fs.bktCount b ≤ fs'.bktCount b)
    (hlic : fs'.liveInsCount b = fs.liveInsCount b)
    (hoa : fs'.overmarsActive b = fs.overmarsActive b)
    (hoc : fs'.overmarsCursor b = fs.overmarsCursor b)
    (hoi : fs'.overmarsInsCount b = fs.overmarsInsCount b)
    (hsl : fs'.slices (fs'.overmarsSliceIdx b) = fs.slices (fs.overmarsSliceIdx b)) :
    OvermarsBucketInv c U n_max θ fs' b := by
  have hold : fs'.oldEp = fs.oldEp := by simp [FastState.oldEp, hep]
  rcases h with ⟨h0, hlt⟩ | ⟨h1, h16, hcur, hlin, hins, omMap, hv, hrel⟩
  · exact Or.inl ⟨hoa.trans h0, hlic.symm ▸ hlt⟩
  · refine Or.inr ⟨hoa.trans h1, hoc.symm ▸ h16, by omega, by omega, by omega,
      omMap, by rwa [hoi, hsl], ?_⟩
    rw [hsalt, hst, hold, hdn, hoc]
    exact hrel.congr (fun loc hlt => hfp loc (hlt.trans hcur))
      fun loc hlt => by rw [hls loc (hlt.trans hcur)]

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
