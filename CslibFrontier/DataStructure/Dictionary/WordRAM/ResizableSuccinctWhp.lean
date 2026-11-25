/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochExec

/-!
# Deamortized Worst-Case WHP Resizable Succinct Dynamic Dictionary

This module packages the deamortized worst-case with-high-probability (`WHP`) resizable succinct
dynamic dictionary supporting `insert`, `delete`, and `query` over `Cslib.WordRAM.Basis.exact` and
`Cslib.WordRAM.Basis.standard` on the word-granular **Resizable Word RAM**
(`Cslib.WordRAM.Resizable`), certified as reusable
`Cslib.DataStructure.WordRAM.Resizable.Randomized.HighProbStateTransitionImpl` and
`Cslib.DataStructure.WordRAM.Resizable.Randomized.HighProbObliviousImpl` packages
(`highProbStateImpl`, `highProbImpl`, and `highProbImplStandard`) for
`(Cslib.DataStructure.Dictionary.Dynamic.spec U V U).toObliviousSequenceSpec (Dictionary.empty U)`.

## Source attribution and Word-RAM adaptation

This formalization adapts the resizable succinct partition hash table of
[Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024, Theorem 1.1 and
Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024] (`DOI: 10.1137/1.9781611977936.33`) to
**oblivious operation sequences** on the Resizable Word RAM
([Kuszmaul, Liang, and Zhou, SODA 2026, Section 5.1][KuszmaulLiangZhou2026]), combining one-round
Feistel quotienting ([Arbitman, Naor, and Segev, FOCS 2010, Claim 5.7][ArbitmanNaorSegev2010]),
dynamic full slabs with a shared circular tail pool ([Bender, Farach-Colton, J. Kuszmaul,
W. Kuszmaul, and M. Liu, STOC 2022, Sections 5.2 and
6.1][BenderFarachColtonKuszmaulKuszmaulLiu2022]), and Thorup's salted bit-packed double tabulation
([Thorup, FOCS 2013][Thorup2013]):

1. **Explicit `BitPackedDoubleTabulation` hashing via `RInstr.rand` (vs. random oracles)**:
   * Theorem 1.1 and Sections 3–6 of [Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul,
     SOSA 2024][BenderFarachColtonKuszmaulKuszmaul2024] assume zero-space oracle access to fully
     random hash functions on `w = Θ(log n)`-bit keys without associated values.
   * Here, across all word widths `11 ≤ w`, key universes `0 < U < 2 ^ w`, full-word value ranges
     `0 < V ≤ 2 ^ w`, and failure exponents `c : ℕ`, all bucket and fingerprint hash functions are
     stored explicitly inside the `1 · OPT` frontier as two-level `BitPackedDoubleTabulation` tables
     (`cTabWhp c`, `dTabWhp c`), sampled incrementally in worst-case `O(1)` word batches via
     `RInstr.rand` (`randFillBatchCode`) with zero external hash or prime hypotheses.
2. **12-phase deamortized dual-epoch rebuild within strict `1 · OPT` space**:
   * Resting memory above `base` never exceeds `spaceBoundWhp c V w s_t` words, i.e., at most
     `Dynamic.optBits U V n_t + whpResizableSpaceFactor c * n_t * Dynamic.logLogFactor n_t +
     (whpResizableSpaceConst + 1) * w` bits (`w_mul_spaceBoundWhp_le_bits`).
   * Across every intermediate step—including all 12 background migration phases (`0..11`),
     `SplitPair` / `PageUnperm` lossless `SlotIoLayout` switching, `RInstr.rand` seed-table
     sampling (Phase `5`), batched item migration (Phase `8`), and word-granular `.grow` / `.shrink`
     frontier adjustments—the active hardware frontier above `base` never exceeds
     `stepSuccinctPeakWordsWhp c V w s_t o_t` words (`1 · OPT`, never `2 · OPT`;
     `w_mul_stepSuccinctPeakWordsWhp_le_bits`). While the dictionary operation sequence `ops` is
     oblivious (fixed before initialization randomness, `ValidHistory (Dictionary.empty U) ops`),
     newly `.grow`-allocated words may be chosen by any demonic allocation policy (`RAdv`).
3. **5-regime distributional coupling and Las Vegas WHP `O_c(1)` worst-case time**:
   * The 5-regime distributional invariant (`DualDistInv` across `ph ≤ 4`, `ph = 5`, `ph ∈ {6, 7}`,
     `ph = 8` via `Rel8` fibre quotients, and `9 ≤ ph`) couples exact `DualRep` semantics and
     seed-independent schedule alignment (`SchedEq`) with uniform `SeedWords` laws on live epochs.
   * Every trajectory in the support of `τ_final` is `Las Vegas` exact: it stays `w`-bounded, rests
     within `base + spaceBoundWhp c V w s_fin`, preserves caller memory `[0, base)`, and produces
     the exact canonical dictionary transcript.
   * With probability at least `1 - ∑_t stepFailureProbWhp c s_t o_t` (where
     `stepFailureProbWhp c s_t o_t = 0` when `U < whpThreshold c` and
     `(max #(dom s_t) (whpThreshold c))⁻¹ ^ c` otherwise), **every** operation in an arbitrary
     admissible oblivious sequence `ops` completes within `worstCaseTimeWhp c` (`O_c(1)`) Resizable
     Word RAM instructions (`seq_whp_succinct` and `seq_whp_succinct_standard`).
4. **Uniformity and width-independence**:
   * The operational body `opCodeWhp` is a single fixed `RCode .exact rWhp` independent of
     `(c, U, V, w, base)`. The initializer `initCodeWhp c U V w` executes in `initStepsWhp = 1164`
     deterministic instructions and depends on `(c, U, V, w)` only through root header constants;
     neither program inspects the ambient word width (`not_readsWidth_initCodeWhp`,
     `not_readsWidth_opCodeWhp`, `not_readsWidth_subroutineCodeWhp`,
     `not_readsWidth_subroutineCodeWhpStandard`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.rWhp`, `mBaseWhp`, `mFrWhp`,
  `rOutFlag`, `rOutVal`: register file size, persistent base-address and frontier registers
  preserved across calls, and query output registers.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.initStepsWhp`, `worstCaseTimeWhp`,
  `spaceBoundWhp`, `stepSuccinctPeakWordsWhp`, `stepFailureProbWhp`: deterministic initialization
  budget (`1164`), `O_c(1)` worst-case step budget, `1 · OPT` resting and peak word bounds, and
  per-step WHP slow-path probability bound.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.initCodeWhp`, `opCodeWhp`,
  `subroutineCodeWhp`, `subroutineCodeWhpStandard`: initializer, parameter-free operational body,
  and relocatable `Resizable.SubroutineCode` packages over `Basis.exact` and `Basis.standard`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.highProbStateImpl`, `highProbImpl`,
  `highProbImplStandard`: `HighProbStateTransitionImpl` and `HighProbObliviousImpl` certificates
  over `Basis.exact` and `Basis.standard`.

## Main results

* `not_readsWidth_initCodeWhp`, `not_readsWidth_opCodeWhp`, `not_readsWidth_subroutineCodeWhp`,
  `not_readsWidth_subroutineCodeWhpStandard`: width-independence (`¬ReadsWidth`) of initializer and
  operational subroutines.
* `w_mul_spaceBoundWhp_le_bits`, `w_mul_stepSuccinctPeakWordsWhp_le_bits`: resting and stepwise-peak
  `1 · OPT` bit-space bounds (`OPT(U, V, n_t) + O_c(n_t log log n_t) + O(w)` bits).
* `obliviousPeakFits_of_succinctWords`: discharges `ObliviousPeakFits` from specification-level
  `PeakFitsHistory` over `stepSuccinctPeakWordsWhp`.
* `seq_whp_succinct`, `seq_whp_succinct_standard`: end-to-end `O_c(1)` worst-case instruction time
  with high probability `1 - ∑_t (max n_t (whpThreshold c))⁻¹ ^ c`, strict `1 · OPT` resting and
  peak space, caller `[0, base)` preservation, and exact Las Vegas dictionary transcripts over
  oblivious operation sequences in `Basis.exact` and `Basis.standard`.

## References

* [Y. Arbitman, M. Naor, and G. Segev, *Backyard Cuckoo Hashing: Constant Worst-Case Operations
  with a Succinct Representation*, Claim 5.7][ArbitmanNaorSegev2010]
* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul, and M. Liu,
  *On the Optimal Time/Space Tradeoff for Hash Tables*, Sections 5.2 and
  6.1][BenderFarachColtonKuszmaulKuszmaulLiu2022]
* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul,
  *Modern Hashing Made Simple*, Theorem 1.1 and
  Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]
* [W. Kuszmaul, J. Liang, and R. Zhou, *Succinct Dynamic Rank/Select: Bypassing the Tree-Structure
  Bottleneck*, Section 5.1][KuszmaulLiangZhou2026]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation, and High
  Independence*][Thorup2013]
-/

public section
end
