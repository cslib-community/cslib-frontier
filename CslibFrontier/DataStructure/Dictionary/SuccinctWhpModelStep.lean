/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.MapRel
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.Invariants
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.Overmars
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.DeleteLast
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.DeleteReloc
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.FastDelete

/-!
# Shadow-Rebuild and Deletion Invariants for the Pure WHP Succinct Dynamic Dictionary

This module re-exports the map-correspondence combinators (`SliceMapRel`, `BufMapRel`),
core/pre-tick invariants (`CoreFastInv`, `PreOvermarsBucketInv`, `ValidEpochStagePreTick`),
and step preservation for `overmarsStep` and `fastDelete` in `SuccinctWhpModel` from its parallel
submodules under `SuccinctWhpModelStep/`:
* `MapRel`: `sliceIdx_inj`, `SliceMapRel`, and `BufMapRel` forward/congruence combinators.
* `Invariants`: `CoreFastInv`, `PreOvermarsBucketInv`, `ValidEpochStagePreTick`, and conversions.
* `Overmars`: `overmarsStep_spec`.
* `DeleteLast` / `DeleteReloc` / `FastDelete`: `fastDelete_afterDel_last_spec`,
  `fastDelete_afterDel_reloc_spec`, and `ValidFastState.fastDelete_spec` (sharing internal
  combinators privately via `DeleteHelpers`).

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
-/
