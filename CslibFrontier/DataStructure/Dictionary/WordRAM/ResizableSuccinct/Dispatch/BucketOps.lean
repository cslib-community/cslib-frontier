/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.CoordsDelta
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.QueryInsert
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.DeletePrep
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.DeleteFinish
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.QueryInsertSpec
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.DeleteSpec

/-!
# Compacted Bucket-Level and Feistel-Dispatched Dictionary Operations in `Memory.Prog`

This module completes the `Memory.Prog` subroutine layer (`¬ReadsWidth`, certified via
`RealizesBounded .exact`) for in-epoch operations on the compacted resizable succinct dictionary,
coupling every mutating and read-only path via `FixedCoupled` to the fixed-capacity reference
operations in `SuccinctBucketOps.lean`, `SuccinctDeleteOps.lean`, and `SuccinctHash.lean`:
* `compGrowDeltaGenProg`, `compShrinkDeltaGenProg`: overflow-free `0..2`-word item-stream delta
  evaluators for pre-insert `growZeroCode` and post-delete `shrinkCode`;
* `compFeistelCoordsProg`: shared Feistel `(b, q, m)` coordinate extractor;
* `compQueryWithHashGenProg`: Feistel-dispatched lookup returning `s_abs u`;
* `compInsertSearchWithHashGenProg`, `compWritePhysValGenProg`, `compInsertAppendNewGenProg`:
  split two-phase insertion allowing the Resizable Word RAM caller to grow the hardware frontier by
  `compactedItemWords U V w N (n + 1) - compactedItemWords U V w N n ≤ 2` words only on a miss
  (`found = 0`) before writing the new dense slot;
* `compDeletePrepWithHashGenProg`, `compDeleteFinishWithHashGenProg`: two-phase compacted deletion
  coupled to `deletePrepWithHashProg` and `deleteFinishWithHashProg` (via internal payload-copy and
  bucket-level helpers).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compGrowDeltaGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compShrinkDeltaGenProg`:
  overflow-free word-delta evaluators for item-count transitions `n → n + 1` and `n → n - 1`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compQueryWithHashGenProg`:
  compacted Feistel-dispatched dictionary lookup.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compInsertSearchWithHashGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compWritePhysValGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compInsertAppendNewGenProg`:
  compacted split insertion subroutines (search, in-place value update, and post-grow slot append).
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compDeletePrepWithHashGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compDeleteFinishWithHashGenProg`:
  compacted two-phase Feistel-dispatched deletion subroutines.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compQueryWithHashGenProg_dict_spec`:
  dictionary-level lookup correctness and `O(1 + probeExcess)` `memoryCost` bound.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compInsertHit_dict_spec`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compInsertMiss_dict_spec`:
  dictionary-level `DictStateInv` and `FixedCoupled` preservation and amortized `memoryCost` bounds
  for hit (in-place update) and miss (post-grow append) insertion paths.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compDeleteWithHashGenProg_dict_spec`:
  dictionary-level `DictStateInv` and `FixedCoupled` preservation and amortized `memoryCost` bound
  for two-phase compacted deletion.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.DataStructure

@[simp] theorem runClient_state_compFeistelCoordsProg
    (d : CompParams × (ℕ × ℕ)) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compFeistelCoordsProg d))) = s :=
  clientState_compFeistelCoordsProg d s

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
