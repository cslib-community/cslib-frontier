/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.Frame
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.SlotPush
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.TailSlabOps.SlotPop

/-!
# Compacted Tail Allocation, `K`-Step Slab Promotion/Demotion, and Amortized Slot Operations

This module re-exports the compacted tail-allocation, `K`-step (`K = slabSize N`) circular-window
slab promotion/demotion, and amortized `O(1)` slot push/pop subroutines across focused parallel
topic submodules under `ResizableSuccinct/Dispatch/TailSlabOps`:

* `TailSlabOps.Frame`: `CompOpFrame` memory frame relation preserving `frontier` and outside memory.
* `TailSlabOps.SlotPush`: `compPushBackSlotGenProg` and its `FixedCoupled`, amortized `memoryCost`,
  `RealizesBounded .exact`, and `ValidProg` certificates (backed by internal `TailPush` and
  `PromoteSlab` submodules).
* `TailSlabOps.SlotPop`: `compPopBackSlotGenProg` and its `FixedCoupled`, amortized `memoryCost`,
  `RealizesBounded .exact`, and `ValidProg` certificates (backed by internal `TailRemove` and
  `DemoteSlab` submodules).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompOpFrame`:
  frame predicate preserving outside memory, root header, stored parameters, and hash tables.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compPushBackSlotGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompPushBackSlotPre`:
  compacted bucket-append operation and its parameter-free realization precondition.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compPopBackSlotGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompPopBackSlotPre`:
  compacted bucket-pop operation and its parameter-free realization precondition.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compPushBackSlotGenProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_compPushBackSlotGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.validProg_compPushBackSlotGen`:
  `FixedCoupled` equivalence to `pushBackSlotProg`, `O(1)` amortized cost bound,
  `RealizesBounded .exact` certificate, and `ValidProg` admissibility.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compPopBackSlotGenProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_compPopBackSlotGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.validProg_compPopBackSlotGen`:
  `FixedCoupled` equivalence to `popBackSlotProg`, `O(1)` amortized cost bound,
  `RealizesBounded .exact` certificate, and `ValidProg` admissibility.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4][BenderFarachColtonKuszmaulKuszmaul2024]
-/
