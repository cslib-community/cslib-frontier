/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpSwarBTreeInsert
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpBufferTrie
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpFallback
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pure Deamortized WHP Succinct Dynamic Dictionary Model

This module combines the SWAR B+-tree query mappers (`SuccinctWhpSwarBTreeInsert`), bounded-depth
character-trie collision buffers (`SuccinctWhpBufferTrie`), probabilistic window tail bounds
(`SuccinctWhpProb`), and small-regime / in-place CSR fallback primitives (`SuccinctWhpFallback`)
into the complete pure state-transition model (`WhpDictState`, `whpInitPure`, `whpStepPure`,
`whpRunPure`) of the with-high-probability fixed-capacity succinct dynamic dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]).

## Architecture

1. **Three execution regimes (`WhpDictState`)**:
   * `.small`: when `n_max < whpThreshold c`, uses `SmallDictState` (deterministic linear scan over
     `n_max < whpThreshold c` slots, zero failure probability).
   * `.fast`: when `whpThreshold c ≤ n_max`, maintains `M = numBucketsWhp n_max` Feistel buckets
     with dense local coordinates `0 .. bktCount b - 1` (front-yard `0 .. capFrontWhp - 1` plus
     backyard pointers `backPtr b k` backed by `poolFreeStack`/`poolOwner`), three orthogonal SWAR
     B+-tree slices per bucket (`liveRole`, `overmarsRole`, `rebRole`), and two epoch collision
     buffers (`buf 0`, `buf 1`) rotated every `qEpochWhp n_max` operations across stages `0 .. 5`.
   * `.fallback`: rare compressed-sparse-row (`CsrState`) mode for adversarial seed collisions or
     load imbalance; at the end of every fallback operation, `trySelfHeal` runs
     `checkGoodSeedOnState` and immediately restores `.fast` in place via `permuteByTarget` whenever
     `GoodSeedOnState` holds.

2. **Exact correctness for every seed + fast-branch hit under `GoodSeedOnWindow`**:
   * `whpStepPure_spec` (in `SuccinctWhpModelTick`): for **every** static seed `θ` and every
     admissible operation `o`, `whpStepPure` refines `Dynamic.step` while preserving
     `ValidWhpState`.
   * `isFastStepHit_of_goodSeedOnWindow` (in `SuccinctWhpFastProb`): whenever
     `whpThreshold c ≤ n_max` and `GoodSeedOnWindow c U n_max (ops ++ [o]) θ` holds after an
     admissible prefix `ops` of **any** length, `whpRunPure` is in `.fast` mode at `ops` and
     `whpStepPure` executes `o` on the fast branch (`fastStepPure` returns `some _`).

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctWhp.FastState`, `WhpDictState`: pure fast-mode and
  combined dictionary states.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.fastQuery`, `fastInsert`, `fastDelete`,
  `overmarsStep`, `epochTick`, `fastStepPure`: fast-branch operations and background deamortization
  ticks.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.fastToCsr`, `csrToFast`, `trySelfHeal`: in-place
  mode transitions via `permuteByTarget`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.whpInitPure`, `whpStepPure`, `whpRunPure`,
  `OvermarsBucketInv`, `ValidFastState`, `ValidWhpState`: top-level pure transitions and
  representation invariants.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.whpInitPure_spec`: initial state validity.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidFastState.fastFindLoc_spec`,
  `ValidFastState.fastQuery_spec`: exact fast-mode coordinate and value lookup for all seeds.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidFastState.fastToCsr_spec`,
  `trySelfHeal_spec`, `csrStepOp_spec`: exact mode-conversion, self-healing, and fallback step
  specifications (full step and window theorems are proved in `SuccinctWhpModelStep` and
  `SuccinctWhpModelTick`).

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset
open scoped BigOperators

/-! ## Section 1: `FastState`, `WhpDictState`, and fast-mode helper operations -/

/-- Total local coordinates per bucket `capFrontWhp n_max + capBackWhp n_max`. -/
@[expose] def totalLocalCoordsWhp (n_max : ℕ) : ℕ :=
  capFrontWhp n_max + capBackWhp n_max

/-- Unallocated zero `BTreeSlice` (`alloc = 0`, `root = 0`, all-zero nodes). -/
@[expose] def zeroBTreeSlice : BTreeSlice where
  alloc := 0
  root := 0
  nodes := fun _ => ⟨0, 0, 0⟩

/-- Header-only slice reset (`alloc := 0`, `root := 0`, leaving `nodes` untouched). -/
@[expose] def resetBTreeSlice (sl : BTreeSlice) : BTreeSlice where
  alloc := 0
  root := 0
  nodes := sl.nodes

/-- Pure state of the fast mode (`whpThreshold c ≤ n_max`). -/
structure FastState where
  /-- Stored Feistel quotients `< 2 ^ quotBitsWhp U n_max` across `0 .. n_max - 1`. -/
  quotArr : ℕ → ℕ
  /-- Stored values `< V` across `0 .. n_max - 1`. -/
  valArr : ℕ → ℕ
  /-- Per-coordinate location tag `∈ {0, 1, 2, 3}` (`0` = free, `1` = live B+-tree only,
  `2` = in `buf 0`, `3` = in `buf 1`). -/
  locState : ℕ → ℕ → ℕ
  /-- Active item count `≤ totalLocalCoordsWhp n_max` in bucket `b`. -/
  bktCount : ℕ → ℕ
  /-- Active fingerprint salt `< sMaxWhp c n_max` of bucket `b`. -/
  bktSalt : ℕ → ℕ
  /-- Role offset `∈ {0, 1, 2}` of bucket `b`'s live B+-tree slice (`3 * b + liveRole b`). -/
  liveRole : ℕ → ℕ
  /-- Cumulative insertions into bucket `b`'s current live B+-tree slice. -/
  liveInsCount : ℕ → ℕ
  /-- Role offset `∈ {0, 1, 2}` of bucket `b`'s Overmars shadow slice (`3 * b + overmarsRole b`). -/
  overmarsRole : ℕ → ℕ
  /-- Whether Overmars per-bucket rebuild is active (`0` or `1`) on bucket `b`. -/
  overmarsActive : ℕ → ℕ
  /-- Next local coordinate to scan in bucket `b`'s Overmars rebuild. -/
  overmarsCursor : ℕ → ℕ
  /-- Cumulative insertions into bucket `b`'s Overmars shadow slice. -/
  overmarsInsCount : ℕ → ℕ
  /-- Flag (`0` or `1`) marking that dirty bucket `b` finished Stage-2 rebuild in this epoch. -/
  rebDoneFlag : ℕ → ℕ
  /-- Deduplication flag (`0` or `1`) for dirty-bucket collection in Stage 1. -/
  rebQueued : ℕ → ℕ
  /-- Backyard pointer table mapping `(b, k)` (`k = loc - capFrontWhp`) to `< poolSizeWhp`. -/
  backPtr : ℕ → ℕ → ℕ
  /-- Number of free slots on `poolFreeStack` (`≤ poolSizeWhp n_max`). -/
  poolFreeTop : ℕ
  /-- Stack of free backyard pool indices `< poolSizeWhp n_max`. -/
  poolFreeStack : ℕ → ℕ
  /-- Reverse owner tag `b * capBackWhp n_max + k` for allocated pool slot `poolIdx`. -/
  poolOwner : ℕ → ℕ
  /-- Array of `3 * numBucketsWhp n_max` SWAR B+-tree slices. -/
  slices : ℕ → BTreeSlice
  /-- Two epoch collision buffers (`buf 0` and `buf 1`). -/
  buf : ℕ → BufTrie
  /-- Current active collision-buffer index (`0` or `1`; `oldEp = 1 - curEp`). -/
  curEp : ℕ
  /-- Tick counter `0 .. qEpochWhp n_max - 1` within the current epoch. -/
  epochClock : ℕ
  /-- Global epoch rebuild stage (`0` = reset flags, `1` = queue dirty buckets, `2` = rebuild dirty
  buckets, `3` = drain `BufOld`, `4` = clear `BufOld` nodes, `5` = idle until rotation). -/
  rebStage : ℕ
  /-- Cursor for Stages `0`, `1`, and `3` (`0 .. (buf oldEp).itemAlloc`). -/
  stageCursor : ℕ
  /-- Number of deduplicated dirty buckets queued for Stage `2`. -/
  dirtyCount : ℕ
  /-- Deduplicated dirty bucket indices `0 .. dirtyCount - 1`. -/
  dirtyBuckets : ℕ → ℕ
  /-- Index `0 .. dirtyCount` of the dirty bucket currently being rebuilt in Stage `2`. -/
  dirtyIdx : ℕ
  /-- Candidate salt `< sMaxWhp c n_max` currently being tested in Stage `2`. -/
  rebCandSalt : ℕ
  /-- Local coordinate cursor for the current `(dirtyBuckets dirtyIdx, rebCandSalt)` scan. -/
  rebScanCursor : ℕ
  /-- Cumulative insertions into the current `rebSlice` scan. -/
  rebInsCount : ℕ
  /-- Collision flag (`0` = collision-free so far, `1` = collision detected) in Stage `2`. -/
  rebCollision : ℕ

/-- Combined pure state of the WHP succinct dynamic dictionary across all `n_max`. -/
inductive WhpDictState where
  | small (st : SmallDictState)
  | fast (fs : FastState)
  | fallback (csr : CsrState)

/-- Clean initial `FastState` (`empty U`: all counts `0`, `curEp = 0`, `epochClock = 0`,
`rebStage = 5`, `poolFreeStack i = i` for `i < poolSizeWhp n_max`). -/
@[expose] def emptyFastState (n_max : ℕ) : FastState where
  quotArr := fun _ => 0
  valArr := fun _ => 0
  locState := fun _ _ => 0
  bktCount := fun _ => 0
  bktSalt := fun _ => 0
  liveRole := fun _ => 0
  liveInsCount := fun _ => 0
  overmarsRole := fun _ => 1
  overmarsActive := fun _ => 0
  overmarsCursor := fun _ => 0
  overmarsInsCount := fun _ => 0
  rebDoneFlag := fun _ => 0
  rebQueued := fun _ => 0
  backPtr := fun _ _ => 0
  poolFreeTop := poolSizeWhp n_max
  poolFreeStack := fun i => if i < poolSizeWhp n_max then i else 0
  poolOwner := fun _ => 0
  slices := fun _ => zeroBTreeSlice
  buf := fun _ => emptyBufTrie
  curEp := 0
  epochClock := 0
  rebStage := 5
  stageCursor := 0
  dirtyCount := 0
  dirtyBuckets := fun _ => 0
  dirtyIdx := 0
  rebCandSalt := 0
  rebScanCursor := 0
  rebInsCount := 0
  rebCollision := 0

/-- Old collision-buffer index `1 - fs.curEp`. -/
@[expose] def FastState.oldEp (fs : FastState) : ℕ :=
  1 - fs.curEp

/-- If `fs.curEp ∈ {0, 1}`, then `fs.oldEp ∈ {0, 1}`. -/
theorem FastState.oldEp_or {fs : FastState} (h : fs.curEp = 0 ∨ fs.curEp = 1) :
    fs.oldEp = 0 ∨ fs.oldEp = 1 := by
  rcases h with hc | hc <;> simp [FastState.oldEp, hc]

/-- Role offset `3 - liveRole b - overmarsRole b` of bucket `b`'s epoch-rebuild B+-tree slice. -/
@[expose] def FastState.rebRole (fs : FastState) (b : ℕ) : ℕ :=
  3 - fs.liveRole b - fs.overmarsRole b

/-- Global slice index `3 * b + liveRole b` of bucket `b`'s live B+-tree. -/
@[expose] def FastState.liveSliceIdx (fs : FastState) (b : ℕ) : ℕ :=
  3 * b + fs.liveRole b

/-- Global slice index `3 * b + overmarsRole b` of bucket `b`'s Overmars shadow B+-tree. -/
@[expose] def FastState.overmarsSliceIdx (fs : FastState) (b : ℕ) : ℕ :=
  3 * b + fs.overmarsRole b

/-- Global slice index `3 * b + rebRole b` of bucket `b`'s epoch-rebuild B+-tree. -/
@[expose] def FastState.rebSliceIdx (fs : FastState) (b : ℕ) : ℕ :=
  3 * b + fs.rebRole b

/-- Physical `(quotArr, valArr)` index `< n_max` corresponding to `(b, loc)` in `fs`. -/
@[expose] def FastState.physSlot (n_max : ℕ) (fs : FastState) (b loc : ℕ) : ℕ :=
  let cf := capFrontWhp n_max
  if loc < cf then
    b * cf + loc
  else
    numBucketsWhp n_max * cf + fs.backPtr b (loc - cf)

/-- Reconstructed universe key `feistelReconstruct b (quotArr (physSlot b loc))` at `(b, loc)`. -/
@[expose] def FastState.keyValAt (c U n_max : ℕ) (θ₁ : BktSeed c U n_max) (fs : FastState)
    (b loc : ℕ) : ℕ :=
  feistelReconstruct (bWhp n_max) (bktHash c U n_max θ₁) b
    (fs.quotArr (fs.physSlot n_max b loc))

/-- Reduced key `fpReducedKey θ₂` at `(b, loc)` (or `0` if out of range). -/
@[expose] def FastState.rKeyAt (c U n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState)
    (b loc : ℕ) : ℕ :=
  let kv := fs.keyValAt c U n_max θ.1 b loc
  if h : kv < U then fpReducedKey c U n_max θ.2 ⟨kv, h⟩ else 0

/-- Salted fingerprint `fpHash θ₂ salt` at `(b, loc)` (or `0` if out of range). -/
@[expose] def FastState.fpAt (c U n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState)
    (salt b loc : ℕ) : ℕ :=
  if hs : salt < sMaxWhp c n_max then
    let kv := fs.keyValAt c U n_max θ.1 b loc
    if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
  else 0

/-- Salted fingerprint of key `u : Fin U` at `salt` (`0` if `salt ≥ sMaxWhp`). -/
@[expose] def fpOfSalt (c U n_max : ℕ) (θ₂ : FpSeed c U n_max) (salt : ℕ) (u : Fin U) : ℕ :=
  if hs : salt < sMaxWhp c n_max then fpHash c U n_max θ₂ ⟨salt, hs⟩ u else 0

/-- Whether an active coordinate with tag `st = locState b loc` currently resides in `liveSlice[b]`:
either `st = 1`, or `st = 2 + oldEp` after bucket `b` has already swapped in its rebuilt slice in
Stage `2` (`rebStage = 2 ∧ rebDoneB = 1`) or during Stage `3` (`rebStage = 3`). -/
@[expose] def inLiveTree (rebStage oldEp rebDoneB st : ℕ) : Bool :=
  st == 1 || (st == 2 + oldEp && ((rebStage == 2 && rebDoneB == 1) || rebStage == 3))

/-- Verify whether candidate `(b_cand, loc)` holds an active item of bucket `b` with quotient
`q_val`. -/
@[expose] def FastState.matchesKey (n_max : ℕ) (fs : FastState) (b q_val b_cand loc : ℕ) : Bool :=
  b_cand == b && decide (loc < fs.bktCount b) &&
    decide (fs.quotArr (fs.physSlot n_max b loc) = q_val)

/-- Fast-mode coordinate lookup for `u : Fin U`: probes `buf curEp`, then `buf oldEp`, then
`liveSlice[b]`, verifying `(b, q_val)` at the candidate slot so false positives are impossible for
every seed `θ`. -/
@[expose] def fastFindLoc (c U n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState)
    (u : Fin U) : Option ℕ :=
  let h1 := bktHash c U n_max θ.1
  let b := feistelBucket (bWhp n_max) h1 u.val
  let q_val := keyQuotient (bWhp n_max) u.val
  let rKey := fpReducedKey c U n_max θ.2 u
  let c1 :=
    match bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey with
    | some (b', loc) => if fs.matchesKey n_max b q_val b' loc then some loc else none
    | none => none
  match c1 with
  | some loc => some loc
  | none =>
    let c2 :=
      if fs.rebStage ≤ 3 then
        match bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey with
        | some (b', loc) => if fs.matchesKey n_max b q_val b' loc then some loc else none
        | none => none
      else none
    match c2 with
    | some loc => some loc
    | none =>
      let fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
      match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) fp with
      | some loc => if fs.matchesKey n_max b q_val b loc then some loc else none
      | none => none

/-- Fast-mode value query for `u : Fin U`. -/
@[expose] def fastQuery (c U n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState)
    (u : Fin U) : Option ℕ :=
  let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  match fastFindLoc c U n_max θ fs u with
  | some loc => some (fs.valArr (fs.physSlot n_max b loc))
  | none => none

/-! ## Section 2: Background Overmars rebuild, global `epochTick`, `fastDelete`, `fastInsert` -/

/-- Scan `rem` coordinates starting at `fs.overmarsCursor b` for bucket `b`'s Overmars shadow
slice. -/
@[expose] def overmarsScanSteps (c U n_max : ℕ) (θ : SeedWhp c U n_max) (b : ℕ) :
    ℕ → FastState → FastState
  | 0, fs => fs
  | rem + 1, fs =>
    let cur := fs.overmarsCursor b
    let fs1 :=
      if cur < fs.bktCount b ∧
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b cur) then
        let fp := fs.fpAt c U n_max θ (fs.bktSalt b) b cur
        let slIdx := fs.overmarsSliceIdx b
        let sl' := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices slIdx) fp cur
        { fs with
          slices := Function.update fs.slices slIdx sl'
          overmarsCursor := Function.update fs.overmarsCursor b (cur + 1)
          overmarsInsCount := Function.update fs.overmarsInsCount b (fs.overmarsInsCount b + 1) }
      else
        { fs with overmarsCursor := Function.update fs.overmarsCursor b (cur + 1) }
    overmarsScanSteps c U n_max θ b rem fs1

/-- Activation substep of `overmarsStep` on bucket `b`. -/
@[expose] def overmarsAfterActivate (n_max b : ℕ) (fs : FastState) : FastState :=
  if fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fs.liveInsCount b then
    let omIdx := fs.overmarsSliceIdx b
    { fs with
      overmarsActive := Function.update fs.overmarsActive b 1
      overmarsCursor := Function.update fs.overmarsCursor b 0
      overmarsInsCount := Function.update fs.overmarsInsCount b 0
      slices := Function.update fs.slices omIdx (resetBTreeSlice (fs.slices omIdx)) }
  else fs

/-- Advance Overmars per-bucket shadow rebuild on bucket `b` by `16` coordinates (activating when
`liveInsCount b ≥ 5 * (slabScale n_max) ^ 12`, and swapping roles once `overmarsCursor b ≥
bktCount b`). -/
@[expose] def overmarsStep (c U n_max : ℕ) (θ : SeedWhp c U n_max) (b : ℕ)
    (fs : FastState) : FastState :=
  let fs0 := overmarsAfterActivate n_max b fs
  if fs0.overmarsActive b = 1 then
    let fs1 := overmarsScanSteps c U n_max θ b 16 fs0
    if fs1.bktCount b ≤ fs1.overmarsCursor b then
      let oldLive := fs1.liveRole b
      let oldOm := fs1.overmarsRole b
      { fs1 with
        liveRole := Function.update fs1.liveRole b oldOm
        overmarsRole := Function.update fs1.overmarsRole b oldLive
        liveInsCount := Function.update fs1.liveInsCount b (fs1.overmarsInsCount b)
        overmarsActive := Function.update fs1.overmarsActive b 0
        overmarsCursor := Function.update fs1.overmarsCursor b 0
        overmarsInsCount := Function.update fs1.overmarsInsCount b 0 }
    else fs1
  else fs0

/-- Scan `rem` coordinates starting at `fs.rebScanCursor` for Stage-2 bucket `b` under candidate
salt `fs.rebCandSalt`. -/
@[expose] def rebScanSteps (c U n_max : ℕ) (θ : SeedWhp c U n_max) (b : ℕ) :
    ℕ → FastState → FastState
  | 0, fs => fs
  | rem + 1, fs =>
    if fs.rebCollision ≠ 0 then fs
    else
      let cur := fs.rebScanCursor
      let st := fs.locState b cur
      let fs1 :=
        if cur < fs.bktCount b ∧ (st = 1 ∨ st = 2 + fs.oldEp) then
          let fp := fs.fpAt c U n_max θ fs.rebCandSalt b cur
          let rIdx := fs.rebSliceIdx b
          let sl := fs.slices rIdx
          match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl fp with
          | some _ =>
            { fs with rebCollision := 1 }
          | none =>
            let sl' := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              sl fp cur
            { fs with
              slices := Function.update fs.slices rIdx sl'
              rebScanCursor := cur + 1
              rebInsCount := fs.rebInsCount + 1 }
        else
          { fs with rebScanCursor := cur + 1 }
      rebScanSteps c U n_max θ b rem fs1

/-- Stage 0 of `epochTick`: clear `rebQueued` and `rebDoneFlag` across `oldTr`'s slots. -/
@[expose] def epochTickStage0 (fs : FastState) : FastState :=
  let oldTr := fs.buf fs.oldEp
  if fs.stageCursor < oldTr.itemAlloc then
    match bufCheckSlot oldTr fs.stageCursor with
    | some (b, _) =>
      let nextCur := fs.stageCursor + 1
      let fs' := { fs with
        rebQueued := Function.update fs.rebQueued b 0
        rebDoneFlag := Function.update fs.rebDoneFlag b 0
        stageCursor := nextCur }
      if oldTr.itemAlloc ≤ nextCur then
        { fs' with rebStage := 1, stageCursor := 0, dirtyCount := 0 }
      else fs'
    | none =>
      let nextCur := fs.stageCursor + 1
      if oldTr.itemAlloc ≤ nextCur then
        { fs with rebStage := 1, stageCursor := 0, dirtyCount := 0 }
      else { fs with stageCursor := nextCur }
  else
    { fs with rebStage := 1, stageCursor := 0, dirtyCount := 0 }

/-- End-of-Stage-1 transition of `epochTick`: enter Stage 3 when `dirtyCount = 0`, otherwise
initialize Stage 2 on `dirtyBuckets 0`. -/
@[expose] def epochTickStage1Finish (s : FastState) : FastState :=
  if s.dirtyCount = 0 then
    { s with rebStage := 3, stageCursor := 0 }
  else
    let b0 := s.dirtyBuckets 0
    let rIdx0 := s.rebSliceIdx b0
    { s with
      rebStage := 2
      dirtyIdx := 0
      rebCandSalt := 0
      rebScanCursor := 0
      rebInsCount := 0
      rebCollision := 0
      slices := Function.update s.slices rIdx0 (resetBTreeSlice (s.slices rIdx0)) }

/-- Stage 1 of `epochTick`: collect distinct dirty buckets from `oldTr` into `dirtyBuckets`. -/
@[expose] def epochTickStage1 (fs : FastState) : FastState :=
  let oldTr := fs.buf fs.oldEp
  if fs.stageCursor < oldTr.itemAlloc then
    let nextCur := fs.stageCursor + 1
    let fs' :=
      match bufCheckSlot oldTr fs.stageCursor with
      | some (b, _) =>
        if fs.rebQueued b = 0 then
          { fs with
            rebQueued := Function.update fs.rebQueued b 1
            dirtyBuckets := Function.update fs.dirtyBuckets fs.dirtyCount b
            dirtyCount := fs.dirtyCount + 1
            stageCursor := nextCur }
        else { fs with stageCursor := nextCur }
      | none => { fs with stageCursor := nextCur }
    if oldTr.itemAlloc ≤ nextCur then epochTickStage1Finish fs' else fs'
  else epochTickStage1Finish fs

/-- Role swap at the end of a collision-free Stage-2 bucket scan for `b`. -/
@[expose] def epochTickStage2Swap (b : ℕ) (fsScan : FastState) : FastState :=
  let oldReb := fsScan.rebRole b
  let omIdx := fsScan.overmarsSliceIdx b
  let nextIdx := fsScan.dirtyIdx + 1
  { fsScan with
    liveRole := Function.update fsScan.liveRole b oldReb
    bktSalt := Function.update fsScan.bktSalt b fsScan.rebCandSalt
    liveInsCount := Function.update fsScan.liveInsCount b fsScan.rebInsCount
    overmarsActive := Function.update fsScan.overmarsActive b 0
    overmarsCursor := Function.update fsScan.overmarsCursor b 0
    overmarsInsCount := Function.update fsScan.overmarsInsCount b 0
    slices := Function.update fsScan.slices omIdx (resetBTreeSlice (fsScan.slices omIdx))
    rebDoneFlag := Function.update fsScan.rebDoneFlag b 1
    dirtyIdx := nextIdx
    rebCandSalt := 0
    rebScanCursor := 0
    rebInsCount := 0
    rebCollision := 0 }

/-- Post-swap Stage-2 transition: advance to Stage 3 or reset the next dirty bucket's rebuild
slice. -/
@[expose] def epochTickStage2AfterSwap (nextIdx : ℕ) (fsSwapped : FastState) : FastState :=
  if fsSwapped.dirtyCount ≤ nextIdx then
    { fsSwapped with rebStage := 3, stageCursor := 0 }
  else
    let bNext := fsSwapped.dirtyBuckets nextIdx
    let rIdxNext := fsSwapped.rebSliceIdx bNext
    { fsSwapped with
      slices := Function.update fsSwapped.slices rIdxNext
        (resetBTreeSlice (fsSwapped.slices rIdxNext)) }

/-- Post-scan decision of Stage 2 after `rebScanSteps ... 16`. -/
@[expose] def epochTickStage2PostScan (b : ℕ) (fsScan : FastState) : FastState :=
  if fsScan.rebCollision ≠ 0 then
    let rIdx := fsScan.rebSliceIdx b
    { fsScan with
      rebCandSalt := fsScan.rebCandSalt + 1
      rebScanCursor := 0
      rebInsCount := 0
      rebCollision := 0
      slices := Function.update fsScan.slices rIdx (resetBTreeSlice (fsScan.slices rIdx)) }
  else if fsScan.bktCount b ≤ fsScan.rebScanCursor then
    epochTickStage2AfterSwap (fsScan.dirtyIdx + 1) (epochTickStage2Swap b fsScan)
  else fsScan

/-- Stage 2 of `epochTick`: scan 16 coordinates of `dirtyBuckets dirtyIdx` under `rebCandSalt`. -/
@[expose] def epochTickStage2 (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) : FastState :=
  if fs.dirtyIdx < fs.dirtyCount then
    let b := fs.dirtyBuckets fs.dirtyIdx
    if fs.rebCandSalt < sMaxWhp c n_max then
      epochTickStage2PostScan b (rebScanSteps c U n_max θ b 16 fs)
    else fs
  else { fs with rebStage := 3, stageCursor := 0 }

/-- Stage 3 of `epochTick`: untag one item from `oldTr` (`locState := 1`) and delete its key. -/
@[expose] def epochTickStage3 (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) : FastState :=
  let oldEp := fs.oldEp
  let oldTr := fs.buf oldEp
  if fs.stageCursor < oldTr.itemAlloc then
    let nextCur := fs.stageCursor + 1
    let fs' :=
      match bufCheckSlot oldTr fs.stageCursor with
      | some (b, loc) =>
        let rKey := fs.rKeyAt c U n_max θ b loc
        let tr' := bufDelete (cTabWhp c) (bCharWhp n_max) oldTr rKey
        { fs with
          buf := Function.update fs.buf oldEp tr'
          locState := Function.update fs.locState b (Function.update (fs.locState b) loc 1)
          stageCursor := nextCur }
      | none =>
        { fs with stageCursor := nextCur }
    if (fs'.buf oldEp).itemAlloc ≤ nextCur then { fs' with rebStage := 4 } else fs'
  else
    { fs with rebStage := 4 }

/-- Stage 4 of `epochTick`: clear up to 8 trie nodes of `oldTr` via `bufClearSteps 8`. -/
@[expose] def epochTickStage4 (fs : FastState) : FastState :=
  let oldEp := fs.oldEp
  let oldTr := fs.buf oldEp
  let doneClear := decide (oldTr.nodeAlloc ≤ 8)
  let tr' := bufClearSteps 8 oldTr
  { fs with
    buf := Function.update fs.buf oldEp tr'
    rebStage := if doneClear then 5 else 4 }

/-- Combined Stage `0 .. 5` step of `epochTick` prior to `epochClock` rollover. -/
@[expose] def epochTickStage (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) : FastState :=
  if fs.rebStage = 0 then epochTickStage0 fs
  else if fs.rebStage = 1 then epochTickStage1 fs
  else if fs.rebStage = 2 then epochTickStage2 c U n_max θ fs
  else if fs.rebStage = 3 then epochTickStage3 c U n_max θ fs
  else if fs.rebStage = 4 then epochTickStage4 fs
  else fs

/-- Advance `epochClock` after `epochTickStage`, flipping `curEp` at `qEpochWhp n_max` iff
`rebStage = 5` and returning `none` otherwise. -/
@[expose] def epochTickRollover (n_max : ℕ) (fs1 : FastState) : Option FastState :=
  let nextClk := fs1.epochClock + 1
  if qEpochWhp n_max ≤ nextClk then
    if fs1.rebStage = 5 then
      some { fs1 with
        curEp := 1 - fs1.curEp
        epochClock := 0
        rebStage := 0
        stageCursor := 0 }
    else none
  else
    some { fs1 with epochClock := nextClk }

/-- Execute one global deamortization tick across Stages `0 .. 5` and advance `epochClock`
(returning `none` iff `epochClock + 1 = qEpochWhp n_max` while `rebStage ≠ 5`). -/
@[expose] def epochTick (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) : Option FastState :=
  epochTickRollover n_max (epochTickStage c U n_max θ fs)

/-- Substep 1 of `fastDelete`: remove `(u, loc_del)` from the epoch buffers and B+-tree slices. -/
@[expose] def fastDeleteRemove (c U n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState)
    (u : Fin U) (b loc_del : ℕ) : FastState :=
  let st_del := fs.locState b loc_del
  let rKey_u := fpReducedKey c U n_max θ.2 u
  let fp_live_u := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  let buf1 :=
    if st_del = 2 then
      Function.update fs.buf 0 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 0) rKey_u)
    else if st_del = 3 then
      Function.update fs.buf 1 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 1) rKey_u)
    else fs.buf
  let lIdx := fs.liveSliceIdx b
  let slices1 :=
    if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
      Function.update fs.slices lIdx
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices lIdx) fp_live_u)
    else fs.slices
  let omIdx := fs.overmarsSliceIdx b
  let slices2 :=
    if fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
      Function.update slices1 omIdx
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (slices1 omIdx) fp_live_u)
    else slices1
  let rebActiveB : Bool :=
    decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
      fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
      fs.rebCollision = 0)
  let rIdx := fs.rebSliceIdx b
  let slices3 :=
    if rebActiveB && decide (loc_del < fs.rebScanCursor ∧
        (st_del = 1 ∨ st_del = 2 + fs.oldEp)) then
      Function.update slices2 rIdx
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (slices2 rIdx) (fpOfSalt c U n_max θ.2 fs.rebCandSalt u))
    else slices2
  { fs with buf := buf1, slices := slices3 }

/-- Helper for `fastDeleteMoveLast`: relocate `loc_last → loc_del` in `liveSlice` and
`overmarsSlice`. -/
@[expose] def fastDeleteMoveSlices (n_max b loc_del loc_last fp_live_last : ℕ)
    (fs1 : FastState) : (ℕ → BTreeSlice) × (ℕ → ℕ) :=
  let st_last := fs1.locState b loc_last
  let lIdx := fs1.liveSliceIdx b
  let omIdx := fs1.overmarsSliceIdx b
  let sl_live' :=
    if inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last then
      Function.update fs1.slices lIdx
        (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs1.slices lIdx) fp_live_last loc_del)
    else fs1.slices
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

/-- Substep 2 of `fastDelete` (when `loc_del < loc_last`): relocate `loc_last` into `loc_del`. -/
@[expose] def fastDeleteMoveLast (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (b loc_del loc_last : ℕ) (rebActiveB : Bool) (fs1 : FastState) : FastState :=
  let p_last := fs1.physSlot n_max b loc_last
  let p_del := fs1.physSlot n_max b loc_del
  let st_last := fs1.locState b loc_last
  let rKey_last := fs1.rKeyAt c U n_max θ b loc_last
  let fp_live_last := fs1.fpAt c U n_max θ (fs1.bktSalt b) b loc_last
  let fp_cand_last := fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last
  let qArr' := Function.update fs1.quotArr p_del (fs1.quotArr p_last)
  let vArr' := Function.update fs1.valArr p_del (fs1.valArr p_last)
  let buf2 :=
    if st_last = 2 then
      Function.update fs1.buf 0
        (bufInsert (cTabWhp c) (bCharWhp n_max) (fs1.buf 0) rKey_last b loc_del)
    else if st_last = 3 then
      Function.update fs1.buf 1
        (bufInsert (cTabWhp c) (bCharWhp n_max) (fs1.buf 1) rKey_last b loc_del)
    else fs1.buf
  let omPair := fastDeleteMoveSlices n_max b loc_del loc_last fp_live_last fs1
  let sl_om' := omPair.1
  let omIns' := omPair.2
  let rIdx := fs1.rebSliceIdx b
  let rebQuad :=
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
  let (sl_reb', (cand', (cur', ins'))) := rebQuad
  { fs1 with
    quotArr := qArr'
    valArr := vArr'
    locState := Function.update fs1.locState b
      (Function.update (fs1.locState b) loc_del st_last)
    buf := buf2
    slices := sl_reb'
    overmarsInsCount := omIns'
    rebCandSalt := cand'
    rebScanCursor := cur'
    rebInsCount := ins' }

/-- Substep 3 of `fastDelete`: clear `loc_last`, decrement `bktCount b`, and release any backyard
slot at `loc_last`. -/
@[expose] def fastDeleteShrink (n_max b loc_last : ℕ) (fs2 : FastState) : FastState :=
  let cf := capFrontWhp n_max
  let freePair :=
    if cf ≤ loc_last then
      (fs2.poolFreeTop + 1,
       Function.update fs2.poolFreeStack fs2.poolFreeTop (fs2.backPtr b (loc_last - cf)))
    else (fs2.poolFreeTop, fs2.poolFreeStack)
  { fs2 with
    locState := Function.update fs2.locState b (Function.update (fs2.locState b) loc_last 0)
    bktCount := Function.update fs2.bktCount b loc_last
    poolFreeTop := freePair.1
    poolFreeStack := freePair.2 }

/-- Fast-mode deletion of `u : Fin U`, relocating `loc_last = bktCount b - 1` into `loc_del` to
maintain dense coordinates `0 .. bktCount b - 1`, followed by `overmarsStep` on bucket `b`. -/
@[expose] def fastDelete (c U n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState)
    (u : Fin U) : FastState :=
  let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  let fsAfterDel : FastState :=
    match fastFindLoc c U n_max θ fs u with
    | none => fs
    | some loc_del =>
      let loc_last := fs.bktCount b - 1
      let rebActiveB : Bool :=
        decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
          fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
          fs.rebCollision = 0)
      let fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
      let fs2 :=
        if loc_del < loc_last then
          fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1
        else fs1
      fastDeleteShrink n_max b loc_last fs2
  overmarsStep c U n_max θ b fsAfterDel

/-- Backyard pool allocation substep of `fastInsert` at coordinate `(b, X)`. -/
@[expose] def fastInsertAlloc (n_max b X : ℕ) (fs : FastState) : FastState :=
  let cf := capFrontWhp n_max
  let allocTriple :=
    if cf ≤ X then
      let k := X - cf
      let top' := fs.poolFreeTop - 1
      let pSlot := fs.poolFreeStack top'
      (Function.update fs.backPtr b (Function.update (fs.backPtr b) k pSlot),
       (top',
        Function.update fs.poolOwner pSlot (b * capBackWhp n_max + k)))
    else
      (fs.backPtr, (fs.poolFreeTop, fs.poolOwner))
  let bp' := allocTriple.1
  let rest := allocTriple.2
  { fs with
    backPtr := bp'
    poolFreeTop := rest.1
    poolOwner := rest.2 }

/-- Fresh-key insertion substep of `fastInsert` prior to `overmarsStep`. -/
@[expose] def fastInsertFresh (c n_max b X q_val v rKey fp lIdx : ℕ)
    (hasFpCollision : Bool) (fsAlloc : FastState) : FastState :=
  let p_new := fsAlloc.physSlot n_max b X
  let qArr' := Function.update fsAlloc.quotArr p_new q_val
  let vArr' := Function.update fsAlloc.valArr p_new v
  if hasFpCollision then
    let ep := fsAlloc.curEp
    let tr' := bufInsert (cTabWhp c) (bCharWhp n_max) (fsAlloc.buf ep) rKey b X
    { fsAlloc with
      quotArr := qArr'
      valArr := vArr'
      bktCount := Function.update fsAlloc.bktCount b (X + 1)
      locState := Function.update fsAlloc.locState b
        (Function.update (fsAlloc.locState b) X (2 + ep))
      buf := Function.update fsAlloc.buf ep tr' }
  else
    let sl' := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fsAlloc.slices lIdx) fp X
    { fsAlloc with
      quotArr := qArr'
      valArr := vArr'
      bktCount := Function.update fsAlloc.bktCount b (X + 1)
      locState := Function.update fsAlloc.locState b
        (Function.update (fsAlloc.locState b) X 1)
      slices := Function.update fsAlloc.slices lIdx sl'
      liveInsCount := Function.update fsAlloc.liveInsCount b (fsAlloc.liveInsCount b + 1) }

/-- Fast-mode insertion / overwrite of `(u, v)`, returning `none` iff a capacity, backyard-pool,
Stage-1 `rKey` collision, or epoch collision-buffer cap guard fires. -/
@[expose] def fastInsert (c U n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState)
    (u : Fin U) (v : ℕ) : Option FastState :=
  let h1 := bktHash c U n_max θ.1
  let b := feistelBucket (bWhp n_max) h1 u.val
  let q_val := keyQuotient (bWhp n_max) u.val
  match fastFindLoc c U n_max θ fs u with
  | some loc =>
    let p := fs.physSlot n_max b loc
    let fs' := { fs with valArr := Function.update fs.valArr p v }
    some (overmarsStep c U n_max θ b fs')
  | none =>
    let X := fs.bktCount b
    let cf := capFrontWhp n_max
    if totalLocalCoordsWhp n_max ≤ X ∨ (cf ≤ X ∧ fs.poolFreeTop = 0) then
      none
    else
      let rKey := fpReducedKey c U n_max θ.2 u
      if (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey).isSome ∨
          (fs.rebStage ≤ 3 ∧
            (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome) then
        none
      else
        let fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
        let lIdx := fs.liveSliceIdx b
        let hasFpCollision :=
          (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices lIdx) fp).isSome
        if hasFpCollision ∧
            !bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey ∧
            2 * sMaxWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc then
          none
        else
          let fsAlloc := fastInsertAlloc n_max b X fs
          let fsInserted :=
            fastInsertFresh c n_max b X q_val v rKey fp lIdx hasFpCollision fsAlloc
          some (overmarsStep c U n_max θ b fsInserted)

/-- Combined fast-branch step (`foreground op` + `epochTick`), returning `none` iff a
fallback guard fires. -/
@[expose] def fastStepPure (c U n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState)
    (op : Dynamic.Op U) : Option (FastState × Option ℕ) :=
  match op with
  | .query u =>
    let res := fastQuery c U n_max θ fs u
    match epochTick c U n_max θ fs with
    | some fs' => some (fs', res)
    | none => none
  | .delete u =>
    let fs1 := fastDelete c U n_max θ fs u
    match epochTick c U n_max θ fs1 with
    | some fs' => some (fs', none)
    | none => none
  | .insert u v =>
    match fastInsert c U n_max θ fs u v with
    | some fs1 =>
      match epochTick c U n_max θ fs1 with
      | some fs' => some (fs', none)
      | none => none
    | none => none

/-! ## Section 3: In-place `fastToCsr`, `csrToFast`, `trySelfHeal`, and `whpStepPure` -/

/-- Prefix sums `0, bktCount 0, bktCount 0 + bktCount 1, …` up to `M`. -/
@[expose] def buildFbStart (M : ℕ) (bktCount : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => buildFbStart M bktCount k + (if k < M then bktCount k else 0)

/-- Convert `FastState` in place via `permuteByTarget` into an equivalent `CsrState`. -/
@[expose] def fastToCsr (n_max : ℕ) (fs : FastState) : CsrState :=
  let M := numBucketsWhp n_max
  let cf := capFrontWhp n_max
  let cb := capBackWhp n_max
  let frontTotal := M * cf
  let fb := buildFbStart M fs.bktCount
  let act₀ : ℕ → Bool := fun p =>
    if p < frontTotal then
      if 0 < cf then
        let b := p / cf
        let loc := p % cf
        decide (b < M ∧ loc < fs.bktCount b)
      else false
    else
      let poolIdx := p - frontTotal
      if poolIdx < poolSizeWhp n_max ∧ 0 < cb then
        let enc := fs.poolOwner poolIdx
        let b := enc / cb
        let k := enc % cb
        let loc := cf + k
        decide (b < M ∧ loc < fs.bktCount b ∧ fs.backPtr b k = poolIdx)
      else false
  let dest : ℕ → ℕ := fun p =>
    if p < frontTotal then
      if 0 < cf then
        let b := p / cf
        let loc := p % cf
        fb b + loc
      else 0
    else
      let poolIdx := p - frontTotal
      if 0 < cb then
        let enc := fs.poolOwner poolIdx
        let b := enc / cb
        let k := enc % cb
        fb b + cf + k
      else 0
  let pv := permuteByTarget n_max dest act₀ fs.quotArr fs.valArr
  ⟨fb, pv.1, pv.2⟩

/-- Prefix sums of backyard excesses `∑_{b' < k} ((fbStart (b' + 1) - fbStart b') - capFront)`. -/
@[expose] def buildBackPrefix (M cf : ℕ) (fbStart : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    buildBackPrefix M cf fbStart k + (if k < M then (fbStart (k + 1) - fbStart k) - cf else 0)

/-- Build a fresh `BTreeSlice` for bucket `b` inserting coordinates `0 .. rem - 1` under `salt`. -/
@[expose] def buildBucketSlice (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (quotArr : ℕ → ℕ) (backPtr : ℕ → ℕ → ℕ) (b salt : ℕ) : ℕ → BTreeSlice
  | 0 => zeroBTreeSlice
  | loc + 1 =>
    let prev := buildBucketSlice c U n_max θ quotArr backPtr b salt loc
    let cf := capFrontWhp n_max
    let p := if loc < cf then b * cf + loc else numBucketsWhp n_max * cf + backPtr b (loc - cf)
    let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b (quotArr p)
    let fp :=
      if hs : salt < sMaxWhp c n_max then
        if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
      else 0
    btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) prev fp loc

/-- Convert `CsrState` in place via `permuteByTarget` into a clean `FastState` using verified
collision-free `salts`. -/
@[expose] def csrToFast (c U n_max : ℕ) (θ : SeedWhp c U n_max) (csr : CsrState)
    (salts : ℕ → ℕ) : FastState :=
  let M := numBucketsWhp n_max
  let cf := capFrontWhp n_max
  let cb := capBackWhp n_max
  let N := csr.fbStart M
  let bktCnt : ℕ → ℕ := fun b => if b < M then csr.fbStart (b + 1) - csr.fbStart b else 0
  let bp := buildBackPrefix M cf csr.fbStart
  let totalBack := bp M
  let backPtr : ℕ → ℕ → ℕ := fun b k =>
    if b < M ∧ k < bktCnt b - cf then bp b + k else 0
  let act₀ : ℕ → Bool := fun i => decide (i < N)
  let dest : ℕ → ℕ := fun i =>
    let b := csrBucketOfIdx csr.fbStart i M
    let loc := i - csr.fbStart b
    if loc < cf then b * cf + loc
    else M * cf + backPtr b (loc - cf)
  let pv := permuteByTarget n_max dest act₀ csr.qArr csr.vArr
  let q' := pv.1
  let v' := pv.2
  let findOwner : ℕ → ℕ := fun poolIdx =>
    let b := csrBucketOfIdx bp poolIdx M
    let k := poolIdx - bp b
    if poolIdx < totalBack then b * cb + k else 0
  let freeTop := poolSizeWhp n_max - totalBack
  { quotArr := q'
    valArr := v'
    locState := fun b loc => if b < M ∧ loc < bktCnt b then 1 else 0
    bktCount := bktCnt
    bktSalt := fun b => if b < M then salts b else 0
    liveRole := fun _ => 0
    liveInsCount := bktCnt
    overmarsRole := fun _ => 1
    overmarsActive := fun _ => 0
    overmarsCursor := fun _ => 0
    overmarsInsCount := fun _ => 0
    rebDoneFlag := fun _ => 0
    rebQueued := fun _ => 0
    backPtr := backPtr
    poolFreeTop := freeTop
    poolFreeStack := fun j => if j < freeTop then totalBack + j else 0
    poolOwner := findOwner
    slices := fun sIdx =>
      let b := sIdx / 3
      let role := sIdx % 3
      if b < M ∧ role = 0 then
        buildBucketSlice c U n_max θ q' backPtr b (salts b) (bktCnt b)
      else zeroBTreeSlice
    buf := fun _ => emptyBufTrie
    curEp := 0
    epochClock := 0
    rebStage := 5
    stageCursor := 0
    dirtyCount := 0
    dirtyBuckets := fun _ => 0
    dirtyIdx := 0
    rebCandSalt := 0
    rebScanCursor := 0
    rebInsCount := 0
    rebCollision := 0 }

/-- Execute one operation on `CsrState` (`query`, `delete`, `insert`). -/
@[expose] def csrStepOp (c U n_max : ℕ) (θ₁ : BktSeed c U n_max) (csr : CsrState)
    (op : Dynamic.Op U) : CsrState × Option ℕ :=
  let h1 := bktHash c U n_max θ₁
  let M := numBucketsWhp n_max
  match op with
  | .query u =>
    (csr, csrQuery csr (feistelBucket (bWhp n_max) h1 u.val) (keyQuotient (bWhp n_max) u.val))
  | .delete u =>
    (csrDelete M csr (feistelBucket (bWhp n_max) h1 u.val) (keyQuotient (bWhp n_max) u.val), none)
  | .insert u v =>
    (csrInsert M csr (feistelBucket (bWhp n_max) h1 u.val) (keyQuotient (bWhp n_max) u.val) v, none)

/-- Check `GoodSeedOnState` on `csr`; if `true`, immediately self-heal into `.fast`, else remain in
`.fallback`. -/
@[expose] def trySelfHeal (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (csr : CsrState) : WhpDictState :=
  let (ok, salts) := checkGoodSeedOnState c U n_max θ csr
  if ok then .fast (csrToFast c U n_max θ csr salts)
  else .fallback csr

/-- Initial state of the WHP succinct dynamic dictionary. -/
@[expose] def whpInitPure (c n_max : ℕ) : WhpDictState :=
  if n_max < whpThreshold c then
    .small emptySmallState
  else
    .fast (emptyFastState n_max)

/-- Single-operation deterministic transition of the WHP succinct dynamic dictionary for fixed seed
`θ`. -/
@[expose] def whpStepPure (c U n_max : ℕ) (θ : SeedWhp c U n_max) (st : WhpDictState)
    (op : Dynamic.Op U) : WhpDictState × Option ℕ :=
  match st with
  | .small sm =>
    match op with
    | .query u => (.small sm, smallQuery n_max sm u.val)
    | .delete u => (.small (smallDelete n_max sm u.val), none)
    | .insert u v => (.small (smallInsert n_max sm u.val v), none)
  | .fast fs =>
    match fastStepPure c U n_max θ fs op with
    | some (fs', res) => (.fast fs', res)
    | none =>
      let csr0 := fastToCsr n_max fs
      let (csr1, res) := csrStepOp c U n_max θ.1 csr0 op
      (trySelfHeal c U n_max θ csr1, res)
  | .fallback csr0 =>
    let (csr1, res) := csrStepOp c U n_max θ.1 csr0 op
    (trySelfHeal c U n_max θ csr1, res)

/-- Execute a sequence of operations sequentially from pure state `st`. -/
@[expose] def whpRunFrom (c U n_max : ℕ) (θ : SeedWhp c U n_max) :
    WhpDictState → List (Dynamic.Op U) → WhpDictState
  | st, [] => st
  | st, op :: ops => whpRunFrom c U n_max θ (whpStepPure c U n_max θ st op).1 ops

/-- Pure state reached from `whpInitPure c n_max` after running `ops : List (Dynamic.Op U)`. -/
@[expose] def whpRunPure (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (ops : List (Dynamic.Op U)) : WhpDictState :=
  whpRunFrom c U n_max θ (whpInitPure c n_max) ops

theorem whpRunFrom_append (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (st : WhpDictState) (l₁ l₂ : List (Dynamic.Op U)) :
    whpRunFrom c U n_max θ st (l₁ ++ l₂) =
      whpRunFrom c U n_max θ (whpRunFrom c U n_max θ st l₁) l₂ := by
  induction l₁ generalizing st with
  | nil => rfl
  | cons o rest ih => exact ih (whpStepPure c U n_max θ st o).1

/-! ## Section 4: `ValidFastState`, `ValidWhpState`, `whpInitPure_spec`, and `fastQuery_spec` -/

/-- Relational map characterization for a `BTreeSlice` indexing `{loc < X | P loc}` under `f`. -/
@[expose] def SliceMapRel (f : ℕ → ℕ) (P : ℕ → Prop) (X : ℕ) (m : ℕ → Option ℕ) : Prop :=
  (∀ fp, m fp = none ↔ ∀ loc < X, P loc → f loc ≠ fp) ∧
  (∀ fp loc, m fp = some loc ↔ loc < X ∧ P loc ∧ f loc = fp)

/-- Relational map characterization for a `BufTrie` indexing `{b < M, loc < bktCnt b | locSt = tag}`
under `rKeyOf`. -/
@[expose] def BufMapRel (M tag : ℕ) (bktCnt : ℕ → ℕ) (locSt rKeyOf : ℕ → ℕ → ℕ)
    (m : ℕ → Option (ℕ × ℕ)) : Prop :=
  (∀ rk, m rk = none ↔ ∀ b < M, ∀ loc < bktCnt b, locSt b loc = tag → rKeyOf b loc ≠ rk) ∧
  (∀ rk b loc, m rk = some (b, loc) ↔
    b < M ∧ loc < bktCnt b ∧ locSt b loc = tag ∧ rKeyOf b loc = rk)

theorem SliceMapRel.empty_of_not (f : ℕ → ℕ) (P : ℕ → Prop) (X : ℕ)
    (hnone : ∀ loc < X, ¬P loc) :
    SliceMapRel f P X (fun _ => none) := by
  refine ⟨fun _ => ⟨fun _ loc hlt hp => absurd hp (hnone loc hlt), fun _ => rfl⟩,
    fun _ loc => ⟨fun h => (by cases h), fun ⟨hlt, hp, _⟩ => absurd hp (hnone loc hlt)⟩⟩

theorem BufMapRel.empty_of_not (M tag : ℕ) (bktCnt : ℕ → ℕ) (locSt rKeyOf : ℕ → ℕ → ℕ)
    (hnone : ∀ b < M, ∀ loc < bktCnt b, locSt b loc ≠ tag) :
    BufMapRel M tag bktCnt locSt rKeyOf (fun _ => none) := by
  refine ⟨fun _ => ⟨fun _ b hb loc hloc hst => absurd hst (hnone b hb loc hloc), fun _ => rfl⟩,
    fun _ b loc => ⟨fun h => (by cases h),
      fun ⟨hb, hloc, hst, _⟩ => absurd hst (hnone b hb loc hloc)⟩⟩

/-- Global epoch stage invariant across Stages `0 .. 5`. -/
@[expose] def ValidEpochStage (c U n_max : ℕ) (θ : SeedWhp c U n_max)
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
       (16 ≤ fs.rebScanCursor ∧ fs.rebScanCursor < fs.bktCount b_cur ∧
        16 * fs.rebInsCount + 16 ≤ 17 * fs.rebScanCursor)) ∧
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

/-- Per-bucket Overmars shadow-rebuild invariant in `ValidFastState`. -/
@[expose] def OvermarsBucketInv (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) (b : ℕ) : Prop :=
  (fs.overmarsActive b = 0 ∧ fs.liveInsCount b < 5 * (slabScale n_max) ^ 12) ∨
  (fs.overmarsActive b = 1 ∧
    16 ≤ fs.overmarsCursor b ∧
    fs.overmarsCursor b < fs.bktCount b ∧
    16 * (fs.liveInsCount b - 5 * (slabScale n_max) ^ 12) ≤ fs.overmarsCursor b ∧
    16 * fs.overmarsInsCount b + 16 ≤ 17 * fs.overmarsCursor b ∧
    ∃ omMap,
      ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) omMap ∧
      SliceMapRel (fs.fpAt c U n_max θ (fs.bktSalt b) b)
        (fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true)
        (fs.overmarsCursor b) omMap)

/-- Complete deterministic invariant of `FastState` valid for **every** static seed `θ`. -/
structure ValidFastState (c U V n_max : ℕ) (θ : SeedWhp c U n_max)
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
  overmars_valid : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b
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
  stage_valid : ValidEpochStage c U n_max θ fs

/-- Combined representation invariant for `WhpDictState` across all `n_max`. -/
@[expose] def ValidWhpState (c U V n_max : ℕ) (θ : SeedWhp c U n_max)
    (st : WhpDictState) (dict : State U) : Prop :=
  match st with
  | .small sm => n_max < whpThreshold c ∧ ValidSmallState U V n_max sm dict
  | .fast fs => ValidFastState c U V n_max θ fs dict
  | .fallback csr =>
    whpThreshold c ≤ n_max ∧
    ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict ∧
    (∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1)

theorem validFastState_empty {c U V n_max : ℕ} (hth : whpThreshold c ≤ n_max)
    (θ : SeedWhp c U n_max) :
    ValidFastState c U V n_max θ (emptyFastState n_max) (Dictionary.empty U) := by
  have hq_pos : 0 < qEpochWhp n_max := by
    unfold qEpochWhp; have := slabScale_pos n_max; positivity
  refine
    { hth := hth
      curEp_or := Or.inl rfl
      epochClock_lt := hq_pos
      rebStage_le := le_rfl
      rebCollision_zero := rfl
      qv_global := fun _ => ⟨Nat.two_pow_pos _, by positivity⟩
      bktCount_le := fun _ _ => Nat.zero_le _
      bktCount_ge_zero := fun _ _ => rfl
      locState_active := fun _ _ _ h => absurd h (Nat.not_lt_zero _)
      locState_inactive := fun _ _ _ => rfl
      active_item := fun _ _ _ h => absurd h (Nat.not_lt_zero _)
      quot_inj := fun _ _ _ h => absurd h (Nat.not_lt_zero _)
      dict_map := fun u => ⟨by simp [Dictionary.empty, emptyFastState],
        fun v => by simp [Dictionary.empty, emptyFastState]⟩
      poolFreeTop_le := le_rfl
      backPtr_valid := fun _ _ _ h => by simp [emptyFastState] at h
      freeStack_lt := fun j hj => by
        dsimp only [emptyFastState] at hj ⊢; simp [hj]
      backPtr_inj := fun _ _ _ h => by simp [emptyFastState] at h
      freeStack_inj := fun j₁ hj₁ j₂ hj₂ heq => by
        dsimp only [emptyFastState] at hj₁ hj₂ heq
        simpa [hj₁, hj₂] using heq
      back_free_disj := fun _ _ _ h => by simp [emptyFastState] at h
      pool_conservation := by simp [emptyFastState]
      roles_valid := fun _ _ => by simp [emptyFastState]
      bktSalt_lt := fun _ _ => sMaxWhp_pos c n_max
      live_fp_inj := fun _ _ _ h => absurd h (Nat.not_lt_zero _)
      live_valid := fun _ _ => ⟨fun _ => none, validWhpSlice_zero _ 0 _,
        SliceMapRel.empty_of_not _ _ 0 fun _ h => absurd h (Nat.not_lt_zero _)⟩
      overmars_valid := fun _ _ => Or.inl ⟨rfl, by
        dsimp only [emptyFastState]; have := slabScale_pos n_max; positivity⟩
      rKey_buf_inj := fun _ _ _ h => absurd h (Nat.not_lt_zero _)
      bufCur_valid := ⟨Nat.zero_le _, by simp [emptyFastState, emptyBufTrie],
        fun _ => none, validBufTrie_empty _ _,
        BufMapRel.empty_of_not _ _ _ _ _ fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
      bufOld_valid := by
        dsimp only [emptyFastState, FastState.oldEp]
        simp only [show ¬(5 ≤ 3) by decide, show ¬(5 = 4) by decide, ↓reduceIte]
        exact ⟨fun _ _ _ h => absurd h (Nat.not_lt_zero _),
          validBufTrie_empty _ _, rfl, rfl⟩
      stage_valid := by simp [ValidEpochStage, emptyFastState] }

/-- `whpInitPure` satisfies `ValidWhpState` for `Dictionary.empty U`. -/
theorem whpInitPure_spec (c U V n_max : ℕ) (θ : SeedWhp c U n_max) :
    ValidWhpState c U V n_max θ (whpInitPure c n_max) (Dictionary.empty U) := by
  unfold whpInitPure
  split_ifs with hsm
  · exact ⟨hsm, validSmallState_empty U V n_max⟩
  · exact validFastState_empty (Nat.le_of_not_lt hsm) θ

theorem ValidFastState.liveInsCount_le {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict)
    {b : ℕ} (hb : b < numBucketsWhp n_max) :
    fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 := by
  have hcf_le : capFrontWhp n_max ≤ 2 * (slabScale n_max) ^ 12 := by
    have hM_pos : 0 < numBucketsWhp n_max := by unfold numBucketsWhp; positivity
    have h2M := n_max_le_two_mul_numBuckets_scale_pow12 n_max
    have hdiv : n_max / numBucketsWhp n_max ≤ 2 * (slabScale n_max) ^ 12 := by
      rw [Nat.div_le_iff_le_mul_add_pred hM_pos]
      have hmul : numBucketsWhp n_max * (2 * (slabScale n_max) ^ 12) =
          2 * numBucketsWhp n_max * (slabScale n_max) ^ 12 := by ring
      omega
    exact (Nat.sub_le _ _).trans hdiv
  have htot_le : totalLocalCoordsWhp n_max ≤ 3 * (slabScale n_max) ^ 12 := by
    have hL2 := two_le_slabScale n_max
    have hcb_le : capBackWhp n_max ≤ (slabScale n_max) ^ 12 := by
      calc capBackWhp n_max = 2 * (slabScale n_max) ^ 11 := rfl
        _ ≤ slabScale n_max * (slabScale n_max) ^ 11 := Nat.mul_le_mul_right _ hL2
        _ = (slabScale n_max) ^ 12 := by ring
    unfold totalLocalCoordsWhp
    omega
  rcases hv.overmars_valid b hb with ⟨_, hlt⟩ | ⟨_, _, hcur_lt, hlin, _⟩
  · omega
  · have hcnt := hv.bktCount_le b hb
    have hcur_le : fs.overmarsCursor b ≤ 3 * (slabScale n_max) ^ 12 :=
      hcur_lt.le.trans (hcnt.trans htot_le)
    omega

/-- Exact soundness and completeness of `fastFindLoc` for **every** seed `θ`:
* If `fastFindLoc` returns `some loc`, then `loc < fs.bktCount b` and `quotArr (physSlot b loc) =
  keyQuotient u.val`;
* If `fastFindLoc` returns `none`, then `dict u = none`. -/
theorem ValidFastState.fastFindLoc_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict) (u : Fin U) :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let q := keyQuotient (bWhp n_max) u.val
    match fastFindLoc c U n_max θ fs u with
    | some loc => loc < fs.bktCount b ∧ fs.quotArr (fs.physSlot n_max b loc) = q
    | none => dict u = none := by
  set h1 := bktHash c U n_max θ.1
  set b := feistelBucket (bWhp n_max) h1 u.val
  set q := keyQuotient (bWhp n_max) u.val
  set rKey := fpReducedKey c U n_max θ.2 u
  set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  have hb_lt : b < numBucketsWhp n_max := feistelBucket_lt (bWhp n_max) h1 u.val
  have hrk_lt : rKey < 2 ^ (cTabWhp c * bCharWhp n_max) := fpReducedKey_lt c U n_max θ.2 u
  have hs_lt : fs.bktSalt b < sMaxWhp c n_max := hv.bktSalt_lt b hb_lt
  have hfp_lt : fp < 2 ^ fpBitsWhp n_max := by
    dsimp only [fp, fpOfSalt]; simp [hs_lt, fpHash_lt]
  obtain ⟨_, _, curMap, hcurV, hcurRel⟩ := hv.bufCur_valid
  obtain ⟨liveMap, hliveV, hliveRel⟩ := hv.live_valid b hb_lt
  have hcur_eq := hcurV.lookup_eq hrk_lt
  have hlive_eq := hliveV.lookup_eq hv.hth (hv.liveInsCount_le hb_lt) hfp_lt
  have hmatch_iff : ∀ b' loc,
      fs.matchesKey n_max b q b' loc = true ↔
        b' = b ∧ loc < fs.bktCount b ∧ fs.quotArr (fs.physSlot n_max b loc) = q := by
    intro b' loc
    simp [FastState.matchesKey, Bool.and_eq_true, beq_iff_eq, and_assoc]
  have key_from_quotient (loc : ℕ) (hquot : fs.quotArr (fs.physSlot n_max b loc) = q) :
      fs.keyValAt c U n_max θ.1 b loc = u.val := by
    dsimp only [FastState.keyValAt]
    rw [hquot]
    exact feistelReconstruct_feistelBucket (bWhp n_max) h1 u.val
  let checked (entry : Option (ℕ × ℕ)) : Option ℕ := match entry with
    | some (b', loc) => if fs.matchesKey n_max b q b' loc then some loc else none
    | none => none
  let BufferCases (ep : ℕ) (candidate : Option ℕ) : Prop :=
    (∃ loc, candidate = some loc ∧ loc < fs.bktCount b ∧
      fs.quotArr (fs.physSlot n_max b loc) = q) ∨
    (candidate = none ∧ ∀ loc < fs.bktCount b, fs.quotArr (fs.physSlot n_max b loc) = q →
      fs.locState b loc ≠ 2 + ep)
  have check_buffer (ep : ℕ) (m : ℕ → Option (ℕ × ℕ))
      (hm : BufMapRel (numBucketsWhp n_max) (2 + ep) fs.bktCount fs.locState
        (fs.rKeyAt c U n_max θ) m) : BufferCases ep (checked (m rKey)) := by
    have reduced_key (loc : ℕ) (hquot : fs.quotArr (fs.physSlot n_max b loc) = q) :
        fs.rKeyAt c U n_max θ b loc = rKey := by
      simp [FastState.rKeyAt, key_from_quotient loc hquot, u.isLt, rKey]
    unfold BufferCases checked
    rcases hentry : m rKey with _ | ⟨b', loc'⟩
    · exact Or.inr ⟨rfl, fun loc hloc hquot hst =>
        ((hm.1 rKey).mp hentry b hb_lt loc hloc hst) (reduced_key loc hquot)⟩
    · by_cases hmatch : fs.matchesKey n_max b q b' loc' = true
      · exact Or.inl ⟨loc', by simp [hmatch], ((hmatch_iff b' loc').mp hmatch).2⟩
      · refine Or.inr ⟨by simp [hmatch], fun loc hloc hquot hst => ?_⟩
        obtain ⟨hb', hloc', hst', hrk'⟩ := (hm.2 rKey b' loc').mp hentry
        have heq := hv.rKey_buf_inj b' hb' loc' hloc' b hb_lt loc hloc
          (hst' ▸ Nat.le_add_right 2 ep) (hst ▸ Nat.le_add_right 2 ep)
          (hrk'.trans (reduced_key loc hquot).symm)
        obtain ⟨rfl, rfl⟩ := heq
        exact hmatch ((hmatch_iff b loc').mpr ⟨rfl, hloc, hquot⟩)
  dsimp only [fastFindLoc]
  rw [show fpReducedKey c U n_max θ.2 u = rKey from rfl, hcur_eq]
  have hc1_cases := check_buffer fs.curEp curMap hcurRel
  dsimp only [BufferCases, checked] at hc1_cases
  rcases hc1_cases with ⟨loc, hc1_eq, hlt, hqe⟩ | ⟨hc1_none, hnot_cur⟩
  · rw [hc1_eq]; exact ⟨hlt, hqe⟩
  · rw [hc1_none]
    dsimp only
    have hc2_cases : BufferCases fs.oldEp (if fs.rebStage ≤ 3 then
        checked (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey) else none) := by
      by_cases hst3 : fs.rebStage ≤ 3
      · have hold := hv.bufOld_valid
        simp only [hst3, ↓reduceIte] at hold ⊢
        obtain ⟨_, _, oldMap, holdV, holdRel⟩ := hold
        rw [holdV.lookup_eq hrk_lt]
        exact check_buffer fs.oldEp oldMap holdRel
      · have hold := hv.bufOld_valid
        simp only [hst3, ↓reduceIte] at hold ⊢
        refine Or.inr ⟨rfl, fun loc hloc _ => ?_⟩
        by_cases hst4 : fs.rebStage = 4
        · simp only [hst4, ↓reduceIte] at hold
          exact hold.1 b hb_lt loc hloc
        · simp only [hst4, ↓reduceIte] at hold
          exact hold.1 b hb_lt loc hloc
    dsimp only [BufferCases, checked] at hc2_cases
    rcases hc2_cases with ⟨loc, hc2_eq, hlt, hqe⟩ | ⟨hc2_none, hnot_old⟩
    · rw [hc2_eq]; exact ⟨hlt, hqe⟩
    · rw [hc2_none]
      dsimp only
      rw [show fpOfSalt c U n_max θ.2 (fs.bktSalt b) u = fp from rfl, hlive_eq]
      have live_entry (loc : ℕ) (hloc : loc < fs.bktCount b)
          (hq_eq : fs.quotArr (fs.physSlot n_max b loc) = q) :
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true ∧
            fs.fpAt c U n_max θ (fs.bktSalt b) b loc = fp := by
        have hst_bnd := hv.locState_active b hb_lt loc hloc
        have hnc := hnot_cur loc hloc hq_eq
        have hno := hnot_old loc hloc hq_eq
        have hst1 : fs.locState b loc = 1 := by
          rcases hv.curEp_or with hc0 | hc1
          · simp only [FastState.oldEp, hc0] at hnc hno; omega
          · simp only [FastState.oldEp, hc1] at hnc hno; omega
        have hinL : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) =
            true := by simp [inLiveTree, hst1]
        have hkv := key_from_quotient loc hq_eq
        have hfp_loc : fs.fpAt c U n_max θ (fs.bktSalt b) b loc = fp := by
          dsimp only [FastState.fpAt, fp, fpOfSalt]
          simp [hs_lt, hkv, u.isLt]
        exact ⟨hinL, hfp_loc⟩
      cases hlm : liveMap fp with
      | none =>
        dsimp only
        refine (hv.dict_map u).1.mpr fun loc hloc hq_eq => ?_
        obtain ⟨hinL, hfp_loc⟩ := live_entry loc hloc hq_eq
        exact (hliveRel.1 fp).mp hlm loc hloc hinL hfp_loc
      | some loc' =>
        dsimp only
        by_cases hm_ok : fs.matchesKey n_max b q b loc' = true
        · obtain ⟨_, hlt, hqe⟩ := (hmatch_iff b loc').mp hm_ok
          have hm_ok' : fs.matchesKey n_max
              (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val)
              (keyQuotient (bWhp n_max) u.val)
              (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val) loc' = true := hm_ok
          rw [hm_ok']
          exact ⟨hlt, hqe⟩
        · have hm_fls : fs.matchesKey n_max
              (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val)
              (keyQuotient (bWhp n_max) u.val)
              (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val) loc' = false :=
            Bool.eq_false_iff.mpr hm_ok
          rw [hm_fls]
          obtain ⟨hloc', hinL', hfp'⟩ := (hliveRel.2 fp loc').mp hlm
          refine (hv.dict_map u).1.mpr fun loc hloc hq_eq => ?_
          obtain ⟨hinL, hfp_loc⟩ := live_entry loc hloc hq_eq
          have heq_l := hv.live_fp_inj b hb_lt loc' hloc' loc hloc hinL' hinL
            (hfp'.trans hfp_loc.symm)
          subst heq_l
          exact hm_ok ((hmatch_iff b loc').mpr ⟨rfl, hloc, hq_eq⟩)

/-- `fastQuery` returns `dict u` for **every** seed `θ` whenever `ValidFastState` holds. -/
theorem ValidFastState.fastQuery_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict) (u : Fin U) :
    fastQuery c U n_max θ fs u = dict u := by
  have hfl := hv.fastFindLoc_spec u
  unfold fastQuery
  cases h : fastFindLoc c U n_max θ fs u with
  | none =>
    rw [h] at hfl
    exact hfl.symm
  | some loc =>
    rw [h] at hfl
    symm
    exact ((hv.dict_map u).2 _).mpr ⟨loc, hfl.1, hfl.2, rfl⟩

/-! ## Section 5: Mode transitions (`fastToCsr_spec`, `csrToFast_spec`, `trySelfHeal_spec`) -/

private theorem buildFbStart_props (M : ℕ) (cnt : ℕ → ℕ) :
    buildFbStart M cnt 0 = 0 ∧
    (∀ b < M, buildFbStart M cnt (b + 1) = buildFbStart M cnt b + cnt b) ∧
    (∀ k ≤ M, buildFbStart M cnt k = ∑ b ∈ range k, cnt b) := by
  refine ⟨rfl, fun b hb => ?_, fun k hk => ?_⟩
  · simp [buildFbStart, hb]
  · induction k with
    | zero => simp [buildFbStart]
    | succ k ih =>
      have hk_lt : k < M := Nat.lt_of_succ_le hk
      rw [Finset.sum_range_succ, ← ih (Nat.le_of_succ_le hk)]
      simp [buildFbStart, hk_lt]

private theorem buildBackPrefix_props (M cf : ℕ) (fb : ℕ → ℕ) :
    buildBackPrefix M cf fb 0 = 0 ∧
    (∀ b < M, buildBackPrefix M cf fb (b + 1) =
      buildBackPrefix M cf fb b + ((fb (b + 1) - fb b) - cf)) ∧
    (∀ k ≤ M, buildBackPrefix M cf fb k =
      ∑ b ∈ range k, ((fb (b + 1) - fb b) - cf)) := by
  refine ⟨rfl, fun b hb => ?_, fun k hk => ?_⟩
  · simp [buildBackPrefix, hb]
  · induction k with
    | zero => simp [buildBackPrefix]
    | succ k ih =>
      have hk_lt : k < M := Nat.lt_of_succ_le hk
      rw [Finset.sum_range_succ, ← ih (Nat.le_of_succ_le hk)]
      simp [buildBackPrefix, hk_lt]

/-- Mixed-radix bound: a digit `l < c` after `b < M` full blocks stays below `M * c`. -/
private theorem mul_add_lt_mul_of_lt {b l c M : ℕ} (hb : b < M) (hl : l < c) :
    b * c + l < M * c :=
  mul_comm c b ▸ Nat.mul_add_lt_mul_of_lt_of_lt hb hl

/-- Mixed-radix injectivity: `b * c + l` with `l < c` determines `b` and `l`. -/
private theorem eq_of_mul_add_eq {b₁ b₂ l₁ l₂ c : ℕ} (h₁ : l₁ < c) (h₂ : l₂ < c)
    (h : b₁ * c + l₁ = b₂ * c + l₂) : b₁ = b₂ ∧ l₁ = l₂ := by
  have hd : ∀ b l, l < c → (b * c + l) / c = b := fun b l hl => by
    rw [mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hl, Nat.add_zero]
  obtain rfl : b₁ = b₂ := by rw [← hd b₁ l₁ h₁, h, hd b₂ l₂ h₂]
  exact ⟨rfl, by omega⟩

private theorem fb_offset_inj {M : ℕ} {fb cnt : ℕ → ℕ}
    (hadj : ∀ b < M, fb (b + 1) = fb b + cnt b)
    {b₁ l₁ b₂ l₂ : ℕ} (hb₁ : b₁ < M) (hl₁ : l₁ < cnt b₁)
    (hb₂ : b₂ < M) (hl₂ : l₂ < cnt b₂)
    (heq : fb b₁ + l₁ = fb b₂ + l₂) :
    b₁ = b₂ ∧ l₁ = l₂ := by
  have hmono : ∀ x y, x ≤ y → y ≤ M → fb x ≤ fb y :=
    fbStart_mono_of_adj fun b hb => by rw [hadj b hb]; exact Nat.le_add_right _ _
  rcases lt_trichotomy b₁ b₂ with hlt | rfl | hgt
  · have h1 : fb (b₁ + 1) ≤ fb b₂ := hmono (b₁ + 1) b₂ (by omega) (by omega)
    rw [hadj b₁ hb₁] at h1
    omega
  · exact ⟨rfl, by omega⟩
  · have h1 : fb (b₂ + 1) ≤ fb b₁ := hmono (b₂ + 1) b₁ (by omega) (by omega)
    rw [hadj b₂ hb₂] at h1
    omega

/-- Physical slot `< n_max` and injectivity for any `ValidFastState`. -/
theorem ValidFastState.physSlot_lt_and_inj {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict) :
    (∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b,
      fs.physSlot n_max b loc < n_max) ∧
    (∀ b₁ < numBucketsWhp n_max, ∀ l₁ < fs.bktCount b₁,
     ∀ b₂ < numBucketsWhp n_max, ∀ l₂ < fs.bktCount b₂,
      fs.physSlot n_max b₁ l₁ = fs.physSlot n_max b₂ l₂ → b₁ = b₂ ∧ l₁ = l₂) := by
  let M := numBucketsWhp n_max
  let cf := capFrontWhp n_max
  have hM_cf : M * cf ≤ n_max :=
    (Nat.mul_le_mul_left M (Nat.sub_le _ _)).trans (Nat.mul_div_le n_max M)
  refine ⟨fun b hb loc hloc => ?_, fun b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂ heq => ?_⟩
  · change (if loc < cf then b * cf + loc else M * cf + fs.backPtr b (loc - cf)) < n_max
    by_cases hlt : loc < cf
    · simp only [hlt, ↓reduceIte]
      have h1 : b * cf + loc < M * cf := mul_add_lt_mul_of_lt hb hlt
      omega
    · simp only [hlt, ↓reduceIte]
      have hbp := (hv.backPtr_valid b hb (loc - cf) (by omega)).1
      unfold poolSizeWhp at hbp
      dsimp only [M, cf] at hM_cf hbp ⊢
      omega
  · change (if l₁ < cf then b₁ * cf + l₁ else M * cf + fs.backPtr b₁ (l₁ - cf)) =
        (if l₂ < cf then b₂ * cf + l₂ else M * cf + fs.backPtr b₂ (l₂ - cf)) at heq
    by_cases h1 : l₁ < cf <;> by_cases h2 : l₂ < cf
    · simp only [h1, h2, ↓reduceIte] at heq
      exact eq_of_mul_add_eq h1 h2 heq
    · simp only [h1, h2, ↓reduceIte] at heq
      have hlt : b₁ * cf + l₁ < M * cf := mul_add_lt_mul_of_lt hb₁ h1
      omega
    · simp only [h1, h2, ↓reduceIte] at heq
      have hlt : b₂ * cf + l₂ < M * cf := mul_add_lt_mul_of_lt hb₂ h2
      omega
    · simp only [h1, h2, ↓reduceIte] at heq
      have hbp_eq : fs.backPtr b₁ (l₁ - cf) = fs.backPtr b₂ (l₂ - cf) := by omega
      obtain ⟨rfl, hk_eq⟩ := hv.backPtr_inj b₁ hb₁ (l₁ - cf) (by omega) b₂ hb₂ (l₂ - cf)
        (by omega) hbp_eq
      exact ⟨rfl, by omega⟩

/-- `fastToCsr` converts any `ValidFastState` into a `ValidCsrState` preserving global `(q, v)`
bounds. -/
theorem ValidFastState.fastToCsr_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict) :
    let csr := fastToCsr n_max fs
    ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict ∧
    (∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1) := by
  let M := numBucketsWhp n_max
  let cf := capFrontWhp n_max
  let cb := capBackWhp n_max
  let frontTotal := M * cf
  obtain ⟨hfb0, hfb_adj, hfb_sum⟩ := buildFbStart_props M fs.bktCount
  set fb := buildFbStart M fs.bktCount
  obtain ⟨hp_lt, hp_inj⟩ := hv.physSlot_lt_and_inj
  have hsum_le : fb M ≤ n_max := by
    rw [hfb_sum M le_rfl]
    let S := (range M).sigma fun b => range (fs.bktCount b)
    have hcard_S : #S = ∑ b ∈ range M, fs.bktCount b := by
      simp [S, Finset.card_sigma]
    let fSlot : (b : ℕ) × ℕ → ℕ := fun x => fs.physSlot n_max x.1 x.2
    have hinj_S : Set.InjOn fSlot S := by
      intro x hx y hy heq
      rw [mem_coe, mem_sigma, mem_range, mem_range] at hx hy
      obtain ⟨hb_eq, hl_eq⟩ := hp_inj x.1 hx.1 x.2 hx.2 y.1 hy.1 y.2 hy.2 heq
      rcases x with ⟨bx, lx⟩; rcases y with ⟨by_, ly⟩
      dsimp only at hb_eq hl_eq
      subst hb_eq; subst hl_eq; rfl
    have hsub : S.image fSlot ⊆ range n_max := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hp
      rw [mem_sigma, mem_range, mem_range] at hx
      exact mem_range.mpr (hp_lt x.1 hx.1 x.2 hx.2)
    calc ∑ b ∈ range M, fs.bktCount b = #S := hcard_S.symm
      _ = #(S.image fSlot) := (card_image_of_injOn hinj_S).symm
      _ ≤ #(range n_max) := card_le_card hsub
      _ = n_max := card_range n_max
  let act₀ : ℕ → Bool := fun p =>
    if p < frontTotal then
      if 0 < cf then
        decide (p / cf < M ∧ p % cf < fs.bktCount (p / cf))
      else false
    else
      let poolIdx := p - frontTotal
      if poolIdx < poolSizeWhp n_max ∧ 0 < cb then
        let enc := fs.poolOwner poolIdx
        let b := enc / cb
        let k := enc % cb
        decide (b < M ∧ cf + k < fs.bktCount b ∧ fs.backPtr b k = poolIdx)
      else false
  let dest : ℕ → ℕ := fun p =>
    if p < frontTotal then
      if 0 < cf then fb (p / cf) + p % cf else 0
    else
      let poolIdx := p - frontTotal
      if 0 < cb then
        let enc := fs.poolOwner poolIdx
        fb (enc / cb) + cf + enc % cb
      else 0
  have hact_fwd : ∀ b < M, ∀ loc < fs.bktCount b,
      let p := fs.physSlot n_max b loc
      act₀ p = true ∧ dest p = fb b + loc := by
    intro b hb loc hloc
    change act₀ (if loc < cf then b * cf + loc else frontTotal + fs.backPtr b (loc - cf)) = true ∧
      dest (if loc < cf then b * cf + loc else frontTotal + fs.backPtr b (loc - cf)) = fb b + loc
    by_cases hlt : loc < cf
    · simp only [hlt, ↓reduceIte]
      have hcf_pos : 0 < cf := by omega
      have hp_ft : b * cf + loc < frontTotal := mul_add_lt_mul_of_lt hb hlt
      have hdiv : (b * cf + loc) / cf = b := by
        rw [mul_comm, Nat.mul_add_div hcf_pos, Nat.div_eq_of_lt hlt, Nat.add_zero]
      have hmod : (b * cf + loc) % cf = loc := by
        rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      dsimp only [act₀, dest]
      simp [hp_ft, hcf_pos, hdiv, hmod, hb, hloc]
    · simp only [hlt, ↓reduceIte]
      set k := loc - cf
      have hk_lt : k < fs.bktCount b - cf := by omega
      have hcnt_le := hv.bktCount_le b hb
      have hk_cb : k < cb := by
        unfold totalLocalCoordsWhp at hcnt_le
        dsimp only [cf, cb] at hcnt_le hk_lt ⊢
        omega
      have hcb_pos : 0 < cb := by omega
      obtain ⟨hbp_lt, hown⟩ := hv.backPtr_valid b hb k hk_lt
      set poolIdx := fs.backPtr b k
      have hn_ft : ¬(frontTotal + poolIdx < frontTotal) := by omega
      have hsub_ft : frontTotal + poolIdx - frontTotal = poolIdx := by omega
      have hdiv : (b * cb + k) / cb = b := by
        rw [mul_comm, Nat.mul_add_div hcb_pos, Nat.div_eq_of_lt hk_cb, Nat.add_zero]
      have hmod : (b * cb + k) % cb = k := by
        rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hk_cb]
      have hcf_k : cf + k = loc := by omega
      dsimp only [act₀, dest]
      dsimp only [cb] at hdiv hmod hown hcb_pos ⊢
      simp only [hn_ft, ↓reduceIte, hsub_ft, hbp_lt, hcb_pos, and_self, hown, hdiv, hmod,
        hcf_k, hb, hloc]
      exact ⟨decide_eq_true ⟨trivial, trivial, rfl⟩, by dsimp only [cf] at hcf_k ⊢; omega⟩
  have hact_bwd : ∀ p < n_max, act₀ p = true →
      ∃ b < M, ∃ loc < fs.bktCount b, p = fs.physSlot n_max b loc ∧ dest p = fb b + loc := by
    intro p _ hact
    dsimp only [act₀] at hact
    by_cases hp_ft : p < frontTotal
    · simp only [hp_ft, ↓reduceIte] at hact
      by_cases hcf_pos : 0 < cf
      · simp only [hcf_pos, ↓reduceIte, decide_eq_true_eq] at hact
        set b := p / cf
        set loc := p % cf
        have hloc_cf : loc < cf := Nat.mod_lt p hcf_pos
        have hp_eq : fs.physSlot n_max b loc = p := by
          change (if loc < cf then b * cf + loc else frontTotal + fs.backPtr b (loc - cf)) = p
          simp only [hloc_cf, ↓reduceIte]
          dsimp only [b, loc]
          rw [mul_comm]
          exact Nat.div_add_mod p cf
        refine ⟨b, hact.1, loc, hact.2, hp_eq.symm, ?_⟩
        dsimp only [dest]
        simp [hp_ft, hcf_pos, b, loc]
      · simp [hcf_pos] at hact
    · simp only [hp_ft, ↓reduceIte] at hact
      set poolIdx := p - frontTotal
      by_cases hcond : poolIdx < poolSizeWhp n_max ∧ 0 < cb
      · rw [ite_eq_left hcond] at hact
        simp only [decide_eq_true_eq] at hact
        set enc := fs.poolOwner poolIdx
        set b := enc / cb
        set k := enc % cb
        set loc := cf + k
        have hn_lt : ¬(loc < cf) := by omega
        have hp_eq : fs.physSlot n_max b loc = p := by
          change (if loc < cf then b * cf + loc else frontTotal + fs.backPtr b (loc - cf)) = p
          simp only [hn_lt, ↓reduceIte, show loc - cf = k by omega, hact.2.2]
          dsimp only [poolIdx]; omega
        refine ⟨b, hact.1, loc, hact.2.1, hp_eq.symm, ?_⟩
        dsimp only [dest]
        simp only [hp_ft, hcond.2, ↓reduceIte]
        dsimp only [poolIdx, enc, b, k, loc]
        omega
      · simp [hcond] at hact
  have hdest_inj : ∀ s₁ < n_max, ∀ s₂ < n_max, act₀ s₁ = true → act₀ s₂ = true →
      dest s₁ = dest s₂ → s₁ = s₂ := by
    intro s₁ hs₁ s₂ hs₂ ha₁ ha₂ hd_eq
    obtain ⟨b₁, hb₁, l₁, hl₁, rfl, hd₁⟩ := hact_bwd s₁ hs₁ ha₁
    obtain ⟨b₂, hb₂, l₂, hl₂, rfl, hd₂⟩ := hact_bwd s₂ hs₂ ha₂
    obtain ⟨rfl, rfl⟩ := fb_offset_inj hfb_adj hb₁ hl₁ hb₂ hl₂ (hd₁.symm.trans (hd_eq.trans hd₂))
    rfl
  obtain ⟨hplaced, hqv'⟩ := permuteByTarget_spec hdest_inj hv.qv_global
  dsimp only [fastToCsr]
  change ValidCsrState U V n_max (bktHash c U n_max θ.1)
      ⟨fb, (permuteByTarget n_max dest act₀ fs.quotArr fs.valArr).1,
        (permuteByTarget n_max dest act₀ fs.quotArr fs.valArr).2⟩ dict ∧ _
  set q' := (permuteByTarget n_max dest act₀ fs.quotArr fs.valArr).1
  set v' := (permuteByTarget n_max dest act₀ fs.quotArr fs.valArr).2
  have hqv_eq : ∀ b < M, ∀ loc < fs.bktCount b,
      q' (fb b + loc) = fs.quotArr (fs.physSlot n_max b loc) ∧
      v' (fb b + loc) = fs.valArr (fs.physSlot n_max b loc) := by
    intro b hb loc hloc
    obtain ⟨ha, hd⟩ := hact_fwd b hb loc hloc
    have hp := hplaced (fs.physSlot n_max b loc) (hp_lt b hb loc hloc) ha
    rwa [hd] at hp
  dsimp only [ValidCsrState]
  refine ⟨⟨hfb0, fun b hb => by rw [hfb_adj b hb]; exact Nat.le_add_right _ _, hsum_le,
    ?_, ?_, ?_⟩, hqv'⟩
  · intro b hb i hlo hhi
    rw [hfb_adj b hb] at hhi
    set loc := i - fb b
    have hloc : loc < fs.bktCount b := by omega
    have hi_eq : i = fb b + loc := by omega
    obtain ⟨hq_e, hv_e⟩ := hqv_eq b hb loc hloc
    obtain ⟨hu, hfb_u, hkq_u, hv_lt⟩ := hv.active_item b hb loc hloc
    dsimp only [FastState.keyValAt] at hu hfb_u hkq_u
    rw [hi_eq, hq_e, hv_e]
    exact ⟨hu, hfb_u, hkq_u, (hv.qv_global _).1, hv_lt⟩
  · intro b hb i j hloi hhii hloj hhij hq_eq
    rw [hfb_adj b hb] at hhii hhij
    set l₁ := i - fb b
    set l₂ := j - fb b
    have hl₁ : l₁ < fs.bktCount b := by omega
    have hl₂ : l₂ < fs.bktCount b := by omega
    have hi_eq : i = fb b + l₁ := by omega
    have hj_eq : j = fb b + l₂ := by omega
    rw [hi_eq, hj_eq, (hqv_eq b hb l₁ hl₁).1, (hqv_eq b hb l₂ hl₂).1] at hq_eq
    have hl_eq := hv.quot_inj b hb l₁ hl₁ l₂ hl₂ hq_eq
    omega
  · intro u
    have hb_lt : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val < M :=
      feistelBucket_lt (bWhp n_max) _ u.val
    refine ⟨?_, fun v => ?_⟩
    · rw [(hv.dict_map u).1]
      set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
      set q := keyQuotient (bWhp n_max) u.val
      constructor
      · intro hall i hlo hhi
        rw [hfb_adj b hb_lt] at hhi
        set loc := i - fb b
        have hloc : loc < fs.bktCount b := by omega
        rw [show i = fb b + loc by omega, (hqv_eq b hb_lt loc hloc).1]
        exact hall loc hloc
      · intro hall loc hloc
        rw [← (hqv_eq b hb_lt loc hloc).1]
        exact hall (fb b + loc) (by omega) (by rw [hfb_adj b hb_lt]; omega)
    · rw [(hv.dict_map u).2 v]
      set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
      set q := keyQuotient (bWhp n_max) u.val
      constructor
      · rintro ⟨loc, hloc, hqe, hve⟩
        refine ⟨fb b + loc, by omega, by rw [hfb_adj b hb_lt]; omega, ?_, ?_⟩
        · rw [(hqv_eq b hb_lt loc hloc).1]; exact hqe
        · rw [(hqv_eq b hb_lt loc hloc).2]; exact hve
      · rintro ⟨i, hlo, hhi, hqe, hve⟩
        rw [hfb_adj b hb_lt] at hhi
        set loc := i - fb b
        have hloc : loc < fs.bktCount b := by omega
        have hi_eq : i = fb b + loc := by omega
        rw [hi_eq, (hqv_eq b hb_lt loc hloc).1] at hqe
        rw [hi_eq, (hqv_eq b hb_lt loc hloc).2] at hve
        exact ⟨loc, hloc, hqe, hve⟩

theorem totalLocalCoordsWhp_le_three_mul {n_max : ℕ} :
    totalLocalCoordsWhp n_max ≤ 3 * (slabScale n_max) ^ 12 := by
  have hM_pos : 0 < numBucketsWhp n_max := by unfold numBucketsWhp; positivity
  have h2M := n_max_le_two_mul_numBuckets_scale_pow12 n_max
  have hcf_le : capFrontWhp n_max ≤ 2 * (slabScale n_max) ^ 12 := by
    have hdiv : n_max / numBucketsWhp n_max ≤ 2 * (slabScale n_max) ^ 12 := by
      rw [Nat.div_le_iff_le_mul_add_pred hM_pos]
      have hmul : numBucketsWhp n_max * (2 * (slabScale n_max) ^ 12) =
          2 * numBucketsWhp n_max * (slabScale n_max) ^ 12 := by ring
      omega
    exact (Nat.sub_le _ _).trans hdiv
  have hL2 := two_le_slabScale n_max
  have hcb_le : capBackWhp n_max ≤ (slabScale n_max) ^ 12 := by
    calc capBackWhp n_max = 2 * (slabScale n_max) ^ 11 := rfl
      _ ≤ slabScale n_max * (slabScale n_max) ^ 11 := Nat.mul_le_mul_right _ hL2
      _ = (slabScale n_max) ^ 12 := by ring
  unfold totalLocalCoordsWhp
  omega

private theorem buildBucketSlice_spec {c U n_max : ℕ} (hth : whpThreshold c ≤ n_max)
    (θ : SeedWhp c U n_max) (quotArr : ℕ → ℕ) (backPtr : ℕ → ℕ → ℕ) (b salt X : ℕ)
    (hX : X ≤ 3 * (slabScale n_max) ^ 12) :
    let fpFn : ℕ → ℕ := fun loc =>
      let cf := capFrontWhp n_max
      let p := if loc < cf then b * cf + loc else numBucketsWhp n_max * cf + backPtr b (loc - cf)
      let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b (quotArr p)
      if hs : salt < sMaxWhp c n_max then
        if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
      else 0
    (∀ l₁ < X, ∀ l₂ < X, fpFn l₁ = fpFn l₂ → l₁ = l₂) →
    ∀ k ≤ X,
      ∃ m,
        ValidWhpSlice n_max k (buildBucketSlice c U n_max θ quotArr backPtr b salt k) m ∧
        SliceMapRel fpFn (fun _ => True) k m := by
  intro fpFn hinj k hk
  induction k with
  | zero =>
    exact ⟨fun _ => none, validWhpSlice_zero _ 0 _,
      SliceMapRel.empty_of_not _ _ 0 fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨m, hvm, hrel⟩ := ih (Nat.le_of_succ_le hk)
    have hk_ins : k ≤ 8 * (slabScale n_max) ^ 12 := by omega
    have hfp_lt : fpFn k < 2 ^ fpBitsWhp n_max := by
      dsimp only [fpFn]
      set pk := if k < capFrontWhp n_max then b * capFrontWhp n_max + k
        else numBucketsWhp n_max * capFrontWhp n_max + backPtr b (k - capFrontWhp n_max)
      set kvk := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b (quotArr pk)
      split_ifs with hs hu
      · exact fpHash_lt c U n_max θ.2 ⟨salt, hs⟩ ⟨kvk, hu⟩
      · exact Nat.two_pow_pos _
      · exact Nat.two_pow_pos _
    have hk_val : k < 2 ^ valLaneBitsWhp n_max := by
      rw [two_pow_valLaneBitsWhp]; omega
    have hins := hvm.insert_spec hth hk_ins hfp_lt hk_val
    refine ⟨Function.update m (fpFn k) (some k), hins.2, ⟨fun fp => ?_, fun fp loc => ?_⟩⟩
    · by_cases hfp : fp = fpFn k
      · subst hfp
        simp only [Function.update_self, reduceCtorEq, false_iff, not_forall, not_not]
        exact ⟨k, Nat.lt_succ_self k, trivial, rfl⟩
      · rw [Function.update_of_ne hfp, hrel.1 fp]
        constructor
        · intro hall loc hlt _
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
          · exact hall loc hlt' trivial
          · exact Ne.symm hfp
        · intro hall loc hlt _
          exact hall loc (Nat.lt_succ_of_lt hlt) trivial
    · by_cases hfp : fp = fpFn k
      · subst hfp
        simp only [Function.update_self, Option.some.injEq]
        constructor
        · rintro rfl; exact ⟨Nat.lt_succ_self k, trivial, rfl⟩
        · rintro ⟨hlt, _, heq⟩
          exact (hinj loc (Nat.lt_of_lt_of_le hlt hk) k (Nat.lt_of_succ_le hk) heq).symm
      · rw [Function.update_of_ne hfp, hrel.2 fp loc]
        constructor
        · rintro ⟨hlt, _, heq⟩; exact ⟨Nat.lt_succ_of_lt hlt, trivial, heq⟩
        · rintro ⟨hlt, _, heq⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
          · exact ⟨hlt', trivial, heq⟩
          · exact absurd heq.symm hfp

/-- `trySelfHeal` preserves `ValidWhpState` and, whenever `GoodSeedOnState c U n_max θ dict` holds,
produces a clean `.fast` state (`Buf[0] = emptyBufTrie`, `Buf[1] = emptyBufTrie`, `epochClock = 0`,
`rebStage = 5`). -/
theorem trySelfHeal_spec {c U V n_max : ℕ} (hth : whpThreshold c ≤ n_max)
    {θ : SeedWhp c U n_max} {csr : CsrState} {dict : State U}
    (hcsr : ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict)
    (hqv : ∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1) :
    let st' := trySelfHeal c U n_max θ csr
    ValidWhpState c U V n_max θ st' dict ∧
    (GoodSeedOnState c U n_max θ dict →
      ∃ fs', st' = .fast fs' ∧
        fs'.buf 0 = emptyBufTrie ∧
        fs'.buf 1 = emptyBufTrie ∧
        fs'.curEp = 0 ∧
        fs'.epochClock = 0 ∧
        fs'.rebStage = 5) := by
  have hchk := checkGoodSeedOnState_spec hcsr
  dsimp only [trySelfHeal]
  set res := checkGoodSeedOnState c U n_max θ csr
  rcases res with ⟨ok, salts⟩
  dsimp only at hchk ⊢
  cases hok : ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨hth, hcsr, hqv⟩, fun hgood => ?_⟩
    have ht := hchk.1.mpr hgood
    rw [hok] at ht; cases ht
  · simp only [↓reduceIte]
    have hgood : GoodSeedOnState c U n_max θ dict := hchk.1.mp hok
    have hsalts := hchk.2 hok
    obtain ⟨hcard_b, hcard_dom⟩ := hcsr.bucket_and_dom_card
    obtain ⟨hfb0, hadj, hfbM_le, hvalid_i, hinj_q, hmap⟩ := hcsr
    obtain ⟨hbp0, hbp_adj, hbp_sum⟩ :=
      buildBackPrefix_props (numBucketsWhp n_max) (capFrontWhp n_max) csr.fbStart
    set bp := buildBackPrefix (numBucketsWhp n_max) (capFrontWhp n_max) csr.fbStart
    -- Apply `sum_sub_capFront_le_poolSize` via `GoodSeedOnState`'s `BalancedBuckets`!
    let X_fin : Fin (numBucketsWhp n_max) → ℕ :=
      fun b => csr.fbStart (b.val + 1) - csr.fbStart b.val
    have hsum_X : ∑ b : Fin (numBucketsWhp n_max), X_fin b = csr.fbStart (numBucketsWhp n_max) := by
      rw [← hcard_dom, Finset.card_eq_sum_card_fiberwise (t := univ) fun u _ => Finset.mem_univ
        (⟨_, feistelBucket_lt (bWhp n_max) (bktHash c U n_max θ.1) u.val⟩ :
          Fin (numBucketsWhp n_max))]
      exact Fintype.sum_congr _ _ fun b => by simp only [Fin.ext_iff, hcard_b, X_fin]
    obtain ⟨hback_lt_cb, _, hpool_le⟩ := sum_sub_capFront_le_poolSize hth X_fin
      (hsum_X.trans_le hfbM_le)
      (fun b => by
        have hb := (hgood.2.1 b).1
        rwa [hcard_b b, hcard_dom, ← hsum_X] at hb)
      (fun b => by
        have hb := (hgood.2.1 b).2
        rwa [hcard_b b, hcard_dom, ← hsum_X] at hb)
    let bktCnt : ℕ → ℕ := fun b =>
      if b < numBucketsWhp n_max then csr.fbStart (b + 1) - csr.fbStart b else 0
    have hbktCnt_le : ∀ b < numBucketsWhp n_max, bktCnt b ≤ totalLocalCoordsWhp n_max := by
      intro b hb
      have hcb := hback_lt_cb ⟨b, hb⟩
      dsimp only [bktCnt, X_fin] at hcb ⊢
      simp only [hb, ↓reduceIte]
      unfold totalLocalCoordsWhp
      omega
    have hbpM_eq : bp (numBucketsWhp n_max) =
        ∑ b : Fin (numBucketsWhp n_max), (X_fin b - capFrontWhp n_max) := by
      rw [hbp_sum (numBucketsWhp n_max) le_rfl, ← Fin.sum_univ_eq_sum_range]
    have htotalBack_le : bp (numBucketsWhp n_max) ≤ poolSizeWhp n_max := hbpM_eq ▸ hpool_le
    -- Set up `permuteByTarget` for `csrToFast`
    let backPtr : ℕ → ℕ → ℕ := fun b k =>
      if b < numBucketsWhp n_max ∧ k < bktCnt b - capFrontWhp n_max then bp b + k else 0
    let act₀ : ℕ → Bool := fun i => decide (i < csr.fbStart (numBucketsWhp n_max))
    let dest : ℕ → ℕ := fun i =>
      let b := csrBucketOfIdx csr.fbStart i (numBucketsWhp n_max)
      let loc := i - csr.fbStart b
      if loc < capFrontWhp n_max then b * capFrontWhp n_max + loc
      else numBucketsWhp n_max * capFrontWhp n_max + backPtr b (loc - capFrontWhp n_max)
    have hbp_adj' : ∀ b < numBucketsWhp n_max,
        bp (b + 1) = bp b + (bktCnt b - capFrontWhp n_max) := fun b hb => by
      rw [hbp_adj b hb]; dsimp only [bktCnt]; simp only [hb, ↓reduceIte]
    have hdest_inj : ∀ i₁ < n_max, ∀ i₂ < n_max, act₀ i₁ = true → act₀ i₂ = true →
        dest i₁ = dest i₂ → i₁ = i₂ := by
      intro i₁ _ i₂ _ ha₁ ha₂ hd_eq
      simp only [act₀, decide_eq_true_eq] at ha₁ ha₂
      obtain ⟨hb₁, hlo₁, hhi₁⟩ := csrBucketOfIdx_spec hfb0 hadj (numBucketsWhp n_max) le_rfl i₁ ha₁
      obtain ⟨hb₂, hlo₂, hhi₂⟩ := csrBucketOfIdx_spec hfb0 hadj (numBucketsWhp n_max) le_rfl i₂ ha₂
      set b₁ := csrBucketOfIdx csr.fbStart i₁ (numBucketsWhp n_max)
      set b₂ := csrBucketOfIdx csr.fbStart i₂ (numBucketsWhp n_max)
      set l₁ := i₁ - csr.fbStart b₁
      set l₂ := i₂ - csr.fbStart b₂
      have hl₁ : l₁ < bktCnt b₁ := by dsimp only [bktCnt]; simp only [hb₁, ↓reduceIte]; omega
      have hl₂ : l₂ < bktCnt b₂ := by dsimp only [bktCnt]; simp only [hb₂, ↓reduceIte]; omega
      dsimp only [dest] at hd_eq
      change (if l₁ < capFrontWhp n_max then b₁ * capFrontWhp n_max + l₁
          else numBucketsWhp n_max * capFrontWhp n_max + backPtr b₁ (l₁ - capFrontWhp n_max)) =
        (if l₂ < capFrontWhp n_max then b₂ * capFrontWhp n_max + l₂
          else numBucketsWhp n_max * capFrontWhp n_max + backPtr b₂ (l₂ - capFrontWhp n_max))
        at hd_eq
      by_cases h1 : l₁ < capFrontWhp n_max <;> by_cases h2 : l₂ < capFrontWhp n_max
      · simp only [h1, h2, ↓reduceIte] at hd_eq
        obtain ⟨hb_eq, hl_eq⟩ := eq_of_mul_add_eq h1 h2 hd_eq
        dsimp only [l₁, l₂] at hl_eq
        rw [hb_eq] at hlo₁ hl_eq
        omega
      · simp only [h1, h2, ↓reduceIte] at hd_eq
        have hlt := mul_add_lt_mul_of_lt hb₁ h1
        omega
      · simp only [h1, h2, ↓reduceIte] at hd_eq
        have hlt := mul_add_lt_mul_of_lt hb₂ h2
        omega
      · simp only [h1, h2, ↓reduceIte] at hd_eq
        have hk₁ : l₁ - capFrontWhp n_max < bktCnt b₁ - capFrontWhp n_max := by omega
        have hk₂ : l₂ - capFrontWhp n_max < bktCnt b₂ - capFrontWhp n_max := by omega
        have hbp_eq : bp b₁ + (l₁ - capFrontWhp n_max) = bp b₂ + (l₂ - capFrontWhp n_max) := by
          dsimp only [backPtr] at hd_eq
          simp only [hb₁, hk₁, hb₂, hk₂, and_self, ↓reduceIte] at hd_eq
          omega
        obtain ⟨hb_eq, hk_eq⟩ := fb_offset_inj hbp_adj' hb₁ hk₁ hb₂ hk₂ hbp_eq
        have hl_eq : l₁ = l₂ := by omega
        dsimp only [l₁, l₂] at hl_eq
        rw [hb_eq] at hlo₁ hl_eq
        omega
    obtain ⟨hplaced, hqv'⟩ := permuteByTarget_spec hdest_inj hqv
    refine ⟨?_, fun _ => ⟨csrToFast c U n_max θ csr salts, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    change ValidFastState c U V n_max θ (csrToFast c U n_max θ csr salts) dict
    dsimp only [csrToFast]
    -- Fold `permuteByTarget` and `buildBackPrefix` into opaque `set`-bindings so structure
    -- projections reduce in O(1) without ever unfolding `permuteOuterLoop`!
    set pv := permuteByTarget n_max dest act₀ csr.qArr csr.vArr
    let q' := pv.1
    let v' := pv.2
    let findOwner : ℕ → ℕ := fun poolIdx =>
      let b := csrBucketOfIdx bp poolIdx (numBucketsWhp n_max)
      let k := poolIdx - bp b
      if poolIdx < bp (numBucketsWhp n_max) then b * capBackWhp n_max + k else 0
    let freeTop := poolSizeWhp n_max - bp (numBucketsWhp n_max)
    let fs' : FastState :=
      { quotArr := q'
        valArr := v'
        locState := fun b loc => if b < numBucketsWhp n_max ∧ loc < bktCnt b then 1 else 0
        bktCount := bktCnt
        bktSalt := fun b => if b < numBucketsWhp n_max then salts b else 0
        liveRole := fun _ => 0
        liveInsCount := bktCnt
        overmarsRole := fun _ => 1
        overmarsActive := fun _ => 0
        overmarsCursor := fun _ => 0
        overmarsInsCount := fun _ => 0
        rebDoneFlag := fun _ => 0
        rebQueued := fun _ => 0
        backPtr := backPtr
        poolFreeTop := freeTop
        poolFreeStack := fun j => if j < freeTop then bp (numBucketsWhp n_max) + j else 0
        poolOwner := findOwner
        slices := fun sIdx =>
          let b := sIdx / 3
          let role := sIdx % 3
          if b < numBucketsWhp n_max ∧ role = 0 then
            buildBucketSlice c U n_max θ q' backPtr b (salts b) (bktCnt b)
          else zeroBTreeSlice
        buf := fun _ => emptyBufTrie
        curEp := 0
        epochClock := 0
        rebStage := 5
        stageCursor := 0
        dirtyCount := 0
        dirtyBuckets := fun _ => 0
        dirtyIdx := 0
        rebCandSalt := 0
        rebScanCursor := 0
        rebInsCount := 0
        rebCollision := 0 }
    change ValidFastState c U V n_max θ fs' dict
    let M := numBucketsWhp n_max
    let cf := capFrontWhp n_max
    let cb := capBackWhp n_max
    let N := csr.fbStart M
    have hqv_at : ∀ b < M, ∀ loc < bktCnt b,
        let i := csr.fbStart b + loc
        q' (fs'.physSlot n_max b loc) = csr.qArr i ∧
        v' (fs'.physSlot n_max b loc) = csr.vArr i := by
      intro b hb loc hloc
      have hbc : bktCnt b = csr.fbStart (b + 1) - csr.fbStart b := ite_eq_left hb
      have hloc_csr : loc < csr.fbStart (b + 1) - csr.fbStart b := by omega
      set i := csr.fbStart b + loc
      have hi_hi : i < csr.fbStart (b + 1) := by omega
      have hmono := fbStart_mono_of_adj hadj
      have hi_N : i < csr.fbStart (numBucketsWhp n_max) :=
        hi_hi.trans_le (hmono (b + 1) (numBucketsWhp n_max) (by omega) le_rfl)
      have hb_eq := csrBucketOfIdx_eq_of_in_range hfb0 hadj hb (by omega) hi_hi
      have hd_eq : dest i = fs'.physSlot n_max b loc := by
        dsimp only [dest, FastState.physSlot, fs']
        rw [hb_eq, show i - csr.fbStart b = loc by omega]
      have hp := hplaced i (hi_N.trans_le hfbM_le) (by simp [act₀, hi_N])
      change q' (dest i) = csr.qArr i ∧ v' (dest i) = csr.vArr i at hp
      rwa [hd_eq] at hp
    -- Fingerprints of a live bucket under its discovered salt are injective on local coordinates.
    have hfp_inj : ∀ b < M, ∀ l₁ < bktCnt b, ∀ l₂ < bktCnt b,
        fs'.fpAt c U n_max θ (salts b) b l₁ = fs'.fpAt c U n_max θ (salts b) b l₂ → l₁ = l₂ := by
      intro b hb
      obtain ⟨hs_b, hinj_b⟩ := hsalts ⟨b, hb⟩
      have hbc : bktCnt b = csr.fbStart (b + 1) - csr.fbStart b := ite_eq_left hb
      -- Each live coordinate `l` holds a key of bucket `b` whose fingerprint is `fpAt … l`.
      have hkey : ∀ l < bktCnt b, ∃ u ∈ (Dictionary.dom dict).filter
          (fun u => feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b),
          fs'.fpAt c U n_max θ (salts b) b l = fpHash c U n_max θ.2 ⟨salts b, hs_b⟩ u ∧
          keyQuotient (bWhp n_max) u.val = csr.qArr (csr.fbStart b + l) := by
        intro l hl
        have hp := hvalid_i b hb (csr.fbStart b + l) (by omega) (by omega)
        have hkv : fs'.keyValAt c U n_max θ.1 b l =
            feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b
              (csr.qArr (csr.fbStart b + l)) := by
          dsimp only [FastState.keyValAt]
          change feistelReconstruct _ _ b (q' (fs'.physSlot n_max b l)) = _
          rw [(hqv_at b hb l hl).1]
        have hU : fs'.keyValAt c U n_max θ.1 b l < U := hkv ▸ hp.1
        refine ⟨⟨_, hU⟩, ?_, by simp [FastState.fpAt, hs_b, hU], by
          dsimp only; rw [hkv]; exact hp.2.2.1⟩
        rw [mem_filter, Dictionary.mem_dom_iff]
        refine ⟨⟨csr.vArr (csr.fbStart b + l), ((hmap _).2 _).mpr ?_⟩, by
          dsimp only; rw [hkv]; exact hp.2.1⟩
        dsimp only
        rw [hkv, hp.2.1, hp.2.2.1]
        exact ⟨csr.fbStart b + l, by omega, by omega, rfl, rfl⟩
      intro l₁ hl₁ l₂ hl₂ hfp_eq
      obtain ⟨u₁, hm₁, hf₁, hq₁⟩ := hkey l₁ hl₁
      obtain ⟨u₂, hm₂, hf₂, hq₂⟩ := hkey l₂ hl₂
      have hu := hinj_b hm₁ hm₂ (hf₁.symm.trans (hfp_eq.trans hf₂))
      subst hu
      have := hinj_q b hb _ _ (by omega) (by omega) (by omega) (by omega) (hq₁.symm.trans hq₂)
      omega
    have hbp_mono := fbStart_mono_of_adj (f := bp) fun b hb => by
      rw [hbp_adj' b hb]; exact Nat.le_add_right _ _
    have hq_pos : 0 < qEpochWhp n_max := by
      unfold qEpochWhp; have := slabScale_pos n_max; positivity
    refine
      { hth := hth
        curEp_or := Or.inl rfl
        epochClock_lt := hq_pos
        rebStage_le := le_rfl
        rebCollision_zero := rfl
        qv_global := hqv'
        bktCount_le := fun b hb => hbktCnt_le b hb
        bktCount_ge_zero := fun b hb => ite_eq_right (Nat.not_lt.mpr hb)
        locState_active := fun b hb loc hloc => by
          have hls : fs'.locState b loc = 1 := ite_eq_left ⟨hb, hloc⟩
          rw [hls]; decide
        locState_inactive := fun b loc hnot => ite_eq_right hnot
        active_item := fun b hb loc hloc => by
          have hq_e : fs'.quotArr (fs'.physSlot n_max b loc) = csr.qArr (csr.fbStart b + loc) :=
            (hqv_at b hb loc hloc).1
          have hv_e : fs'.valArr (fs'.physSlot n_max b loc) = csr.vArr (csr.fbStart b + loc) :=
            (hqv_at b hb loc hloc).2
          have hbc : fs'.bktCount b = csr.fbStart (b + 1) - csr.fbStart b := ite_eq_left hb
          have hp := hvalid_i b hb (csr.fbStart b + loc) (by omega) (by omega)
          dsimp only [FastState.keyValAt]
          rw [hq_e, hv_e]
          exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.2⟩
        quot_inj := fun b hb l₁ hl₁ l₂ hl₂ hqe => by
          change q' (fs'.physSlot n_max b l₁) = q' (fs'.physSlot n_max b l₂) at hqe
          rw [(hqv_at b hb l₁ hl₁).1, (hqv_at b hb l₂ hl₂).1] at hqe
          have hbc : fs'.bktCount b = csr.fbStart (b + 1) - csr.fbStart b := ite_eq_left hb
          have hi_eq := hinj_q b hb (csr.fbStart b + l₁) (csr.fbStart b + l₂)
            (by omega) (by omega) (by omega) (by omega) hqe
          omega
        dict_map := fun u => by
          have hm_u := hmap u
          dsimp only at hm_u
          set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
          set q := keyQuotient (bWhp n_max) u.val
          have hb : b < M := feistelBucket_lt (bWhp n_max) _ u.val
          have hb_cnt : fs'.bktCount b = csr.fbStart (b + 1) - csr.fbStart b := ite_eq_left hb
          have hbc_eq : bktCnt b = csr.fbStart (b + 1) - csr.fbStart b := ite_eq_left hb
          refine ⟨?_, fun v => ?_⟩
          · rw [hm_u.1]
            constructor
            · intro hall loc hloc
              have hloc_b : loc < bktCnt b := hloc
              change q' (fs'.physSlot n_max b loc) ≠ q
              rw [(hqv_at b hb loc hloc_b).1]
              exact hall (csr.fbStart b + loc) (by omega) (by omega)
            · intro hall i hlo hhi
              set loc := i - csr.fbStart b
              have hloc_f : loc < fs'.bktCount b := by omega
              have hloc_b : loc < bktCnt b := hloc_f
              have hi_eq : i = csr.fbStart b + loc := by omega
              rw [hi_eq, ← (hqv_at b hb loc hloc_b).1]
              exact hall loc hloc_f
          · rw [hm_u.2 v]
            constructor
            · rintro ⟨i, hlo, hhi, hqe, hve⟩
              set loc := i - csr.fbStart b
              have hloc_f : loc < fs'.bktCount b := by omega
              have hloc_b : loc < bktCnt b := hloc_f
              have hi_eq : i = csr.fbStart b + loc := by omega
              refine ⟨loc, hloc_f, ?_, ?_⟩
              · change q' (fs'.physSlot n_max b loc) = q
                rw [(hqv_at b hb loc hloc_b).1, ← hi_eq]; exact hqe
              · change v' (fs'.physSlot n_max b loc) = v
                rw [(hqv_at b hb loc hloc_b).2, ← hi_eq]; exact hve
            · rintro ⟨loc, hloc_f, hqe, hve⟩
              have hloc_b : loc < bktCnt b := hloc_f
              refine ⟨csr.fbStart b + loc, by omega, by omega, ?_, ?_⟩
              · rw [← (hqv_at b hb loc hloc_b).1]; exact hqe
              · rw [← (hqv_at b hb loc hloc_b).2]; exact hve
        poolFreeTop_le := Nat.sub_le _ _
        backPtr_valid := fun b hb k hk => by
          have hk' : k < bktCnt b - capFrontWhp n_max := hk
          have hhi : bp b + k < bp (b + 1) := by rw [hbp_adj' b hb]; omega
          have hlt_M : bp b + k < bp (numBucketsWhp n_max) :=
            hhi.trans_le (hbp_mono (b + 1) (numBucketsWhp n_max) (by omega) le_rfl)
          have hb_idx := csrBucketOfIdx_eq_of_in_range hbp0
            (fun x hx => by rw [hbp_adj' x hx]; exact Nat.le_add_right _ _) hb (by omega) hhi
          dsimp only [fs', findOwner]
          have hbk : backPtr b k = bp b + k := ite_eq_left ⟨hb, hk'⟩
          rw [hbk, ite_eq_left hlt_M, hb_idx]
          exact ⟨hlt_M.trans_le htotalBack_le, by omega⟩
        freeStack_lt := fun j hj => by
          dsimp only [fs', freeTop] at hj ⊢
          rw [ite_eq_left hj]
          omega
        backPtr_inj := fun b₁ hb₁ k₁ hk₁ b₂ hb₂ k₂ hk₂ heq => by
          dsimp only [fs', backPtr] at hk₁ hk₂ heq
          rw [ite_eq_left ⟨hb₁, hk₁⟩, ite_eq_left ⟨hb₂, hk₂⟩] at heq
          exact fb_offset_inj hbp_adj' hb₁ hk₁ hb₂ hk₂ heq
        freeStack_inj := fun j₁ hj₁ j₂ hj₂ heq => by
          dsimp only [fs', freeTop] at hj₁ hj₂ heq
          rw [ite_eq_left hj₁, ite_eq_left hj₂] at heq
          omega
        back_free_disj := fun b hb k hk j hj => by
          dsimp only [fs', freeTop, backPtr] at hk hj ⊢
          rw [ite_eq_left ⟨hb, hk⟩, ite_eq_left hj]
          have hhi : bp b + k < bp (b + 1) := by rw [hbp_adj' b hb]; omega
          have hlt_M : bp b + k < bp (numBucketsWhp n_max) :=
            hhi.trans_le (hbp_mono (b + 1) (numBucketsWhp n_max) (by omega) le_rfl)
          omega
        pool_conservation := by
          dsimp only [fs', freeTop]
          have hsum_eq : ∑ b ∈ range (numBucketsWhp n_max), (bktCnt b - capFrontWhp n_max) =
              bp (numBucketsWhp n_max) := by
            rw [hbp_sum (numBucketsWhp n_max) le_rfl]
            refine Finset.sum_congr rfl fun b hb => ?_
            have hbc : bktCnt b = csr.fbStart (b + 1) - csr.fbStart b :=
              ite_eq_left (mem_range.mp hb)
            rw [hbc]
          rw [hsum_eq]
          omega
        roles_valid := fun _ _ => by
          dsimp only [fs']
          exact ⟨by decide, by decide, by decide⟩
        bktSalt_lt := fun b hb => by
          dsimp only [fs']; simp only [hb, ↓reduceIte]
          exact (hsalts ⟨b, hb⟩).1
        live_fp_inj := fun b hb l₁ hl₁ l₂ hl₂ _ _ hfp_eq => hfp_inj b hb l₁ hl₁ l₂ hl₂
          (by rwa [show fs'.bktSalt b = salts b from ite_eq_left hb] at hfp_eq)
        live_valid := fun b hb => by
          have hX3 : bktCnt b ≤ 3 * (slabScale n_max) ^ 12 :=
            (hbktCnt_le b hb).trans totalLocalCoordsWhp_le_three_mul
          have hdiv3 : (3 * b + 0) / 3 = b := by omega
          have hmod3 : (3 * b + 0) % 3 = 0 := by omega
          have hsl_eq : fs'.slices (fs'.liveSliceIdx b) =
              buildBucketSlice c U n_max θ q' backPtr b (salts b) (bktCnt b) := by
            change (if (3 * b + 0) / 3 < M ∧ (3 * b + 0) % 3 = 0 then
              buildBucketSlice c U n_max θ q' backPtr ((3 * b + 0) / 3) (salts ((3 * b + 0) / 3))
                (bktCnt ((3 * b + 0) / 3))
              else zeroBTreeSlice) = _
            rw [hdiv3, hmod3]
            exact ite_eq_left ⟨hb, rfl⟩
          have hs_eq : fs'.bktSalt b = salts b := ite_eq_left hb
          have hinj_fp := hfp_inj b hb
          obtain ⟨m, hvm, hrel⟩ := buildBucketSlice_spec hth θ q' backPtr b (salts b) (bktCnt b)
            hX3 hinj_fp (bktCnt b) le_rfl
          have hst5 : fs'.rebStage = 5 := rfl
          have ho1 : fs'.oldEp = 1 := rfl
          have hdf0 : fs'.rebDoneFlag b = 0 := rfl
          rw [hsl_eq, hs_eq]
          refine ⟨m, hvm, ⟨fun fp => ?_, fun fp loc => ?_⟩⟩
          · rw [hrel.1 fp]
            constructor
            · intro hall loc hloc _; exact hall loc hloc trivial
            · intro hall loc hloc _
              have hinL : inLiveTree fs'.rebStage fs'.oldEp (fs'.rebDoneFlag b)
                  (fs'.locState b loc) = true := by
                have hls : fs'.locState b loc = 1 := ite_eq_left ⟨hb, hloc⟩
                rw [hst5, ho1, hdf0, hls]; decide
              exact hall loc hloc hinL
          · rw [hrel.2 fp loc]
            constructor
            · rintro ⟨hloc, _, heq⟩
              refine ⟨hloc, ?_, heq⟩
              dsimp only
              have hls : fs'.locState b loc = 1 := ite_eq_left ⟨hb, hloc⟩
              rw [hst5, ho1, hdf0, hls]; decide
            · rintro ⟨hloc, _, heq⟩; exact ⟨hloc, trivial, heq⟩
        overmars_valid := fun b hb => Or.inl ⟨rfl, by
          have hX3 : fs'.liveInsCount b ≤ 3 * (slabScale n_max) ^ 12 :=
            (hbktCnt_le b hb).trans totalLocalCoordsWhp_le_three_mul
          have hpos : 0 < (slabScale n_max) ^ 12 := Nat.pow_pos (slabScale_pos n_max)
          omega⟩
        rKey_buf_inj := fun b₁ hb₁ l₁ hl₁ _ _ _ _ h2 _ => by
          have hls : fs'.locState b₁ l₁ = 1 := ite_eq_left ⟨hb₁, hl₁⟩
          omega
        bufCur_valid := ⟨Nat.zero_le _, by simp [fs', emptyBufTrie],
          fun _ => none, validBufTrie_empty _ _,
          BufMapRel.empty_of_not _ _ _ _ _ fun b hb loc hloc => by
            have hls : fs'.locState b loc = 1 := ite_eq_left ⟨hb, hloc⟩
            have hc0 : fs'.curEp = 0 := rfl
            rw [hls, hc0]; decide⟩
        bufOld_valid := by
          have hst5 : fs'.rebStage = 5 := rfl
          have ho1 : fs'.oldEp = 1 := rfl
          simp only [hst5, show ¬(5 ≤ 3) by decide, show ¬(5 = 4) by decide, ↓reduceIte]
          refine ⟨fun b hb loc hloc => ?_, validBufTrie_empty _ _, rfl, rfl⟩
          have hls : fs'.locState b loc = 1 := ite_eq_left ⟨hb, hloc⟩
          rw [hls, ho1]; decide
        stage_valid := by simp [ValidEpochStage, fs'] }

/-- Convert dependent `op.Result` into homogeneous `Option ℕ` (`some`/`none` for `.query`, `none`
for updates). -/
@[expose] def opResultOpt {U : ℕ} : (op : Dynamic.Op U) → op.Result → Option ℕ
  | .query _, r => r
  | .delete _, _ => none
  | .insert _ _, _ => none

/-- `csrStepOp` preserves `ValidCsrState` and global `(q, v)` bounds while refining
`Dynamic.step`. -/
theorem csrStepOp_spec {c U V n_max : ℕ} (hnU : n_max ≤ U) (θ₁ : BktSeed c U n_max)
    {csr : CsrState} {dict : State U}
    (hcsr : ValidCsrState U V n_max (bktHash c U n_max θ₁) csr dict)
    (hqv : ∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1)
    {op : Dynamic.Op U} (hvalid : Dynamic.valid V n_max dict op) :
    let (csr', res) := csrStepOp c U n_max θ₁ csr op
    ValidCsrState U V n_max (bktHash c U n_max θ₁) csr' (Dynamic.step dict op).1 ∧
    res = opResultOpt op (Dynamic.step dict op).2 ∧
    (∀ p, csr'.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr'.vArr p < max V 1) := by
  cases op with
  | query u =>
    exact ⟨hcsr, csrQuery_spec hcsr u, hqv⟩
  | delete u =>
    refine ⟨csrDelete_spec hcsr u, rfl, fun p => ?_⟩
    dsimp only [csrStepOp, csrDelete]
    split_ifs with hfnz
    · dsimp only
      rw [(csrShiftDown_apply _ _ _ _ p).1, (csrShiftDown_apply _ _ _ _ p).2]
      split_ifs <;> exact hqv _
    · exact hqv p
  | insert u v =>
    refine ⟨csrInsert_spec hnU hcsr hvalid, rfl, fun p => ?_⟩
    dsimp only [csrStepOp, csrInsert]
    set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ₁) u.val
    split_ifs with hfnz
    · dsimp only
      by_cases hp : p = csrScanRange csr.qArr (csr.fbStart b) (keyQuotient (bWhp n_max) u.val)
          (csr.fbStart (b + 1) - csr.fbStart b) - 1
      · subst hp; simp [(hqv _).1, hvalid.2.trans_le (le_max_left V 1)]
      · simp [hp, (hqv p).1, (hqv p).2]
    · dsimp only
      set hi := csr.fbStart (feistelBucket (bWhp n_max) (bktHash c U n_max θ₁) u.val + 1)
      by_cases hp : p = hi
      · subst hp
        simp only [Function.update_self]
        refine ⟨?_, hvalid.2.trans_le (le_max_left V 1)⟩
        have hq_lt : keyQuotient (bWhp n_max) u.val < 2 ^ (keyBits U - bWhp n_max) := by
          have hsplit := (quotBitsWhp_add_bWhp hnU).symm
          have hu_pow : u.val < 2 ^ keyBits U :=
            u.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two U)
          unfold keyQuotient
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
          unfold quotBitsWhp at hsplit
          rwa [← hsplit]
        exact hq_lt
      · simp only [Function.update_of_ne hp]
        have hmono := fbStart_mono_of_adj hcsr.2.1
        have hhi_le : hi ≤ csr.fbStart (numBucketsWhp n_max) :=
          hmono _ _ (Nat.succ_le_of_lt (feistelBucket_lt _ _ _)) le_rfl
        have hcnt_le : csr.fbStart (numBucketsWhp n_max) - hi ≤
            csr.fbStart (numBucketsWhp n_max) := Nat.sub_le _ _
        rw [(csrShiftUp_apply _ _ hcnt_le _ _ p).1, (csrShiftUp_apply _ _ hcnt_le _ _ p).2]
        split_ifs <;> exact hqv _

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
