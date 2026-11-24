/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.Env
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.GmAppendTail
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.GmPopSlab
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.GmPushSlab
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.GmRemoveTail
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.ItemWords
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.ResolveOvf
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.ResolveSlot

/-!
# Compacted Slot Resolvers and `GlobalMeta` Pool Updates in `Memory.Prog`

This module implements the compacted slot-resolution and `GlobalMeta` pool-update subroutines in
`Memory.Prog` (`¬ReadsWidth`, certified via `by realize` with `RealizesBounded .exact`), bridging
them via `FixedCoupled` to their fixed-capacity counterparts in `Succinct`:
* overflow-free item-stream word-count evaluation (`compItemWordsGenProg`) and quotient extraction
  (`compExtractQuotGenProg`);
* ghost fixed-capacity parameter/envelope certificates (`ghostDictParamsWf`, `ghostDictEnvGen`) and
  `FixedCoupled` dense-to-physical lookup and in-place value-update bridges;
* compacted slot and overflow-search resolvers (`compLastSlotOfGenProg`,
  `compResolveIndexedSlotGenProg`, `compResolveOvfStepGenProg`, `compInitOvfSearchGenProg`);
* compacted `GlobalMeta` pool updates (`compAppendTailGMGenProg`, `compRemoveTailGMOnlyGenProg`,
  `compGmPushSlabGenProg`, `compGmPopSlabGenProg`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compItemWordsGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compExtractQuotGenProg`:
  overflow-free item-stream word-count evaluation and Feistel key-quotient extraction.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompEpochEnv`:
  parameter and frontier envelope covering compacted metadata and `m_items` dense item slots.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compLastSlotOfGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compResolveIndexedSlotGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compResolveOvfStepGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compInitOvfSearchGenProg`:
  compacted read-only slot and overflow-search resolvers.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompGmFrame`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compAppendTailGMGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compRemoveTailGMOnlyGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compGmPushSlabGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compGmPopSlabGenProg`:
  compacted `GlobalMeta` tail and slab pool updates.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_compItemWordsGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_compExtractQuotGen`:
  `RealizesBounded .exact` certificates for `compItemWordsGenProg` and `compExtractQuotGenProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.FixedCoupled.quot_val_at_slotOf`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.FixedCoupled.writeVal_slotOf`:
  dense-to-physical lookup agreement and in-place value-update coupling preservation.
* `realizesBounded_compResolveIndexedSlotGen`, `realizesBounded_compResolveOvfStepGen`,
  `realizesBounded_compInitOvfSearchGen`:
  `RealizesBounded .exact` certificates for compacted indexed and overflow slot resolution.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compAppendTailGMGenProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compRemoveTailGMOnlyGenProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compGmPushSlabGenProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compGmPopSlabGenProg_effect`:
  exact `GlobalMeta` state effects and `CompGmFrame` preservation, paired with
  `RealizesBounded .exact` certificates.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4][BenderFarachColtonKuszmaulKuszmaul2024]
-/
