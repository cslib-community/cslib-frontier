/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute.Arena
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute.TargetCap
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute.EpochParams

/-!
# `1 · OPT` Migration Arena Accounting and Runtime Epoch-Parameter Computation

Re-exports the public migration arena accounting and parameter-free (`¬ReadsWidth`) runtime
epoch-parameter computation interface for single-tape capacity migration in the resizable succinct
dynamic dictionary ([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA
2024][BenderFarachColtonKuszmaulKuszmaul2024]; [Kuszmaul, Liang, and Zhou, SODA
2026][KuszmaulLiangZhou2026]):

* `Migration.ParamsCompute.Arena`: `migrateArenaWords`, `migratePeakWords`, shared-arena
  non-overlap (`newItemEnd_le_oldItemNextWord`), `1 · OPT` succinct space bounds
  (`migratePeakWords_le_succinctWords`, `w_mul_migratePeakWords_le_bits`), and `O(n)` linear word
  bounds (`migratePeakWords_le_linear`).
* `Migration.ParamsCompute.TargetCap`: overflow-free `targetCap U n` evaluator
  (`computeTargetCapProg`, `realizesBounded_computeTargetCap`, `computeTargetCapProg_spec`).
* `Migration.ParamsCompute.EpochParams`: overflow-free 63-word active epoch parameter writer
  (`writeEpochParamsGenProg`, `realizesBounded_writeEpochParamsGen`,
  `writeEpochParamsGenProg_spec`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.migrateArenaWords`,
  `migratePeakWords`: shared single-tape item-arena length and peak migration word footprint.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.computeTargetCapProg`,
  `writeEpochParamsGenProg`: parameter-free `Memory.Prog` evaluators for `targetCap U n` and the
  63-word active epoch parameter header `[dstMetaBase, dstMetaBase + 63)`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.newItemEnd_le_oldItemNextWord`: exact
  word-level non-overlap between written new items `[0, j)` and unread right-aligned old items
  `[j, n)` across both growing and shrinking epochs.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.migratePeakWords_le_succinctWords`,
  `w_mul_migratePeakWords_le_bits`, `migratePeakWords_le_linear`: `1 · OPT` succinct space bounds
  and `O(n)` linear word bound.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_computeTargetCap`,
  `computeTargetCapProg_spec`, `realizesBounded_writeEpochParamsGen`,
  `writeEpochParamsGenProg_spec`: `RealizesBounded .exact` certificates and functional
  specifications.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4 and 6][BenderFarachColtonKuszmaulKuszmaul2024]
* [W. Kuszmaul, J. Liang, and R. Zhou, *Succinct Dynamic Rank/Select: Bypassing the Tree-Structure
  Bottleneck*, Section 5.1][KuszmaulLiangZhou2026]
-/
