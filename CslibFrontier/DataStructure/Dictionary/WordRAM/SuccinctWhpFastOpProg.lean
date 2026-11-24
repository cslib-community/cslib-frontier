/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.RebRole
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.FastDelete
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.FastInsert

/-!
# Fast-Mode Deletion and Guarded Insertion `Memory.Prog` Subroutines

This module re-exports the fast-mode foreground operation `Memory.Prog` subroutines and
`Realizes .exact` certificates on top of `SuccinctWhpFastBaseProg`, split across focused
submodules under `SuccinctWhpFastOpProg`:

1. `SuccinctWhpFastOpProg.RebRole`: `readRebAndOmRoleGenProg` and `readRebSliceIdxGenProg`.
2. `SuccinctWhpFastOpProg.FastDelete`: `fastDeleteGenProg`, worst-case `O_c(1)` dense-coordinate
   deletion (`fastDeleteRemove`, `fastDeleteMoveLast`, `fastDeleteShrink`, and `overmarsStep`)
   preserving `FastStateStep` across all epoch rebuild stages (`0 .. 5`).
3. `SuccinctWhpFastOpProg.FastInsert`: `fastInsertGenProg`, worst-case `O_c(1)` guarded insertion
   and overwrite refining `fastInsert`, evaluating all guards before mutating memory so
   `clientState s prog = s` whenever `fastInsert` returns `none`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.readRebSliceIdxGenProg`,
  `fastDeleteGenProg`, `fastInsertGenProg`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fastDeleteGen`,
  `fastDeleteGenProg_fastStep`, `realizes_fastInsertGen`, `fastInsertGenProg_spec`.
-/
