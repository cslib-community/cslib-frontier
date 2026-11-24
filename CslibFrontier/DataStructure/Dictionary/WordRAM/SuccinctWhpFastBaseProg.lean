/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpPermHealProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.Frame
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.SliceBuf
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.HeaderBkt
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.SlotArrays
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.LocPoolArrays
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.Lookup
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.Overmars

/-!
# Fast-Mode Frame Primitives, Lookup, and Overmars Rebuild `Memory.Prog` Subroutines

This umbrella module re-exports the foundational parameter-free `Memory.Prog` subroutines and
`Realizes .exact` certificates for `FastMemRep` in `SuccinctWhpModel`, organized into seven
parallelizable public topic sub-modules (plus privately imported `Internal` proof helpers):

1. `SuccinctWhpFastBaseProg.Frame`: `FastStateStep`, large-regime index bounds, and `FastMemRep`
   slice/buffer projections.
2. `SuccinctWhpFastBaseProg.SliceBuf`: `FastStateStep` wrappers for SWAR B+-tree slices and
   character-trie epoch buffers.
3. `SuccinctWhpFastBaseProg.HeaderBkt`: header, `bktMeta` scalar, dirty-bucket queue, and
   control-predicate subroutines (`inLiveTreeProg`, `readRebActiveBGenProg`, `readOldEpProg`,
   `readLiveSaltIdxGenProg`).
4. `SuccinctWhpFastBaseProg.SlotArrays`: `quotArr`, `valArr`, `backPtr`, `physSlot`, `rKeyAt`,
   and `fpAt` subroutines.
5. `SuccinctWhpFastBaseProg.LocPoolArrays`: 2-bit `locState` and backyard-pool (`poolFreeStack`,
   `poolOwner`) subroutines.
6. `SuccinctWhpFastBaseProg.Lookup`: worst-case `O_c(1)` coordinate and value lookup
   (`fastFindLocBqGenProg`, `fastQueryGenProg`) across `buf curEp`, `buf oldEp`, and
   `liveSlice[b]`.
7. `SuccinctWhpFastBaseProg.Overmars`: worst-case `O_c(1)` per-bucket Overmars shadow B+-tree
   rebuild (`overmarsStepGenProg`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.FastStateStep`: compositional invariant
  preserving `SeedWhpMemRep`, `FastMemRep`, `frontier`, and memory outside `largeSpaceWhp`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastQueryGenProg`,
  `overmarsStepGenProg`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fastQueryGen`,
  `fastQueryGenProg_spec`, `realizes_overmarsStepGen`, `overmarsStepGenProg_fastStep`.
-/
