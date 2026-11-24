/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Resizable.Rename
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.DeleteLast
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.InitFirst
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.MigrateActive
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.Registers

/-!
# Native `RCode` Epoch-Migration, First-Epoch Initialization, and Last-Delete Subroutines

Compiles the verified `Memory.Prog` subroutines from `Migration.ParamsCompute` and
`Migration.StreamStep` together with `growZeroCode`, `shrinkCode`, and `resampleHashCode` into
parameter-free (`¬ReadsWidth`) native `RCode .exact rResize` epoch-transition programs on the
**Resizable Word RAM**:

1. **`migrateActiveCode`**: single-tape `1 · OPT` streaming rebuild from `(N_old, n, n_init_old)` to
   `(targetCap U n, n, n)` (`1 ≤ n ≤ U`, `EpochValid U n N_old`), keeping the hardware frontier
   `≤ base + migratePeakWords U V w N_old n` (`≤ base + Dynamic.succinctWords 2699 888 U V w n`,
   never `2 · OPT`), sampling a fresh uniform `QuotHashSeed U (targetCap U n)`, and bounding
   expected instructions plus post-migration `inEpochPotential` by `migLinearFactor * n`.
2. **`initFirstEpochCode`**: empty-to-active transition (`n = 0 → n' = 1`, `N₁ = targetCap U 1`) on
   `insert u v` in `O(1)` instructions within `base + compactedEpochWords U V w (targetCap U 1) 1`.
3. **`deleteLastOneCode`**: singleton deletion (`n = 1 → 1` or `1 → 0`) on `delete u` in `O(1)`
   deterministic instructions, collapsing to the 8-word empty header when the sole key matches `u`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.rResize`, `epochEmb`, `migFactor`,
  `migLinearFactor`, `initFirstCharge`, `deleteLastOneCharge`: parameter-free register budget,
  `rEpoch` embedding, and cost constants.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.migrateActiveCode`,
  `initFirstEpochCode`, `deleteLastOneCode`: parameter-free `RCode .exact rResize` epoch-boundary
  subroutines.

## Main results

* `not_readsWidth_migrateActiveCode`, `not_readsWidth_initFirstEpochCode`,
  `not_readsWidth_deleteLastOneCode`: width-independence (`¬ReadsWidth`) of all three subroutines.
* `migrateActiveCode_execRCodeDist`: `ExecRCodeDist` specification for single-tape `1 · OPT`
  capacity doubling and halving.
* `initFirstEpochCode_execRCodeDist`: `ExecRCodeDist` specification for `0 → 1` epoch creation.
* `deleteLastOneCode_demonicExec`: `RDemonicExec` specification for `n = 1` deletion and empty
  collapse.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4 and 6][BenderFarachColtonKuszmaulKuszmaul2024]
* [W. Kuszmaul, J. Liang, and R. Zhou, *Succinct Dynamic Rank/Select: Bypassing the Tree-Structure
  Bottleneck*, Section 5.1][KuszmaulLiangZhou2026]
-/
