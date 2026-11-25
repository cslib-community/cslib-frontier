/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpTickHealProg.StepDispatch

/-!
# Self-Healing `csrToFast` / `trySelfHeal` and Top-Level `whpStepPureGenProg`

This module re-exports the `Memory.Prog` self-healing and top-level step-dispatch realization of the
SOSA 2024 fixed-capacity high-probability succinct dynamic dictionary
(`[BenderFarachColtonKuszmaulKuszmaul2024]`, `DOI: 10.1137/1.9781611977936.33`) inside genuine
`whpSpace c U V w n_max` words, decomposed across parallel internal phase modules under
`SuccinctWhpTickHealProg/`:

* `HealRt`: `HealRt` 16-word runtime bundle, capacity bounds, and `StepSpec` monadic combinators;
* `PrefixBackPtr`, `PoolLocSlices`, `BucketRebuild`, `MetaFinalize`: parallel array/slice phase
  loops for `csrToFastGenProg`, decoupled from `SuccinctWhpEpochTickProg`;
* `SelfHeal`: `csrToFastGenProg` and `trySelfHealGenProg` (`CsrMemRep → WhpMemRep`);
* `StepDispatch`: `whpFastBranchCost`, `whpStepPureGenProg`, `WhpStepPurePre`,
  `realizes_whpStepPureGen`, and `whpStepPureGenProg_spec`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
-/
