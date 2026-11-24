/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Core
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Spec
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.UniformBipartite
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.UniformFlow
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.UniformVertexSeparator

/-!
# Dense Edmonds–Karp maximum flow, bipartite matching, and vertex separators on the Word-RAM

Umbrella module re-exporting the dense Edmonds–Karp solver (`Core`, `Spec`) and the three uniform
`Basis.exact` reductions (`UniformFlow`, `UniformBipartite`, `UniformVertexSeparator`); internal
helpers (`Internal`, `BfsSemantics`, `Bounds`) stay out of the public surface. Clients such as
`CslibFrontier.Algorithms.WordRAM.GomoryHu` that only call `ekProg` directly may import
`CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Core` publicly and
`CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Spec` privately.

## Main definitions

* `Cslib.Algorithms.WordRAM.EdmondsKarp.Ctx`, `Ctx.equiv`, `distAddr`, `ekScratch`, `ekBound`,
  `CtxFits`, `ekProg`, `ekCost`: the relocatable solver context, output distance address, scratch
  size, word bound, subroutine, and memory budget.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.fillRange`: fill a range of memory with one word.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.encodeFlowInput`, `ekFlowAddr`, `ekCutAddr`,
  `ekWorkspace`: input encoding, output flow and cut addresses, and workspace frontier for dense
  maximum flow.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.encodeBipartiteMatrix`, `encodeBipartiteInput`,
  `bmMatchAddr`, `bmCovLAddr`, `bmCovRAddr`: input encoding and output matching and König cover
  addresses for bipartite matching.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.encodeBoolVec`, `encodeSepInput`, `sepOutAddr`,
  `sepSideAddr`: input encoding and output separator and side-labelling addresses for minimum
  vertex separators.

## Main results

* `Cslib.Algorithms.WordRAM.EdmondsKarp.ekProg_spec`, `memoryCost_ekProg_le`, `ekProg_realizes`,
  `validHistory_ekProg`, `preservesAt_ekProg`, `ekProg_result_le`: correctness, `O(n ^ 5)` memory
  cost, compilation to `Basis.exact`, admissibility, frame, and return-value bound for clients
  calling `ekProg` as a subroutine (such as Gomory–Hu construction).
* `Cslib.Algorithms.WordRAM.EdmondsKarp.exists_edmondsKarp_program`: uniform `O((n + 1) ^ 5)`
  flat program over `Basis.exact` computing a maximum flow and minimum `s`–`t` cut.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.exists_bipartiteMatching_program`,
  `Cslib.Algorithms.WordRAM.EdmondsKarp.exists_perfectMatching_program`: uniform
  `O((m + r + 1) ^ 5)` maximum bipartite matching with König minimum vertex cover, and uniform
  `O((n + 1) ^ 5)` bipartite perfect-matching decision.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.exists_minSeparator_program`: uniform `O((n + 1) ^ 5)`
  minimum vertex separator and side-labelling certificate by vertex splitting.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.fillRange_realizes`, `fillRange_spec`,
  `memoryCost_fillRange_le`, `validHistory_fillRange`: realization and specification of
  `fillRange`.

## References

* [EdmondsKarp1972]
* [CLRS2009]
* [Koenig1931]
* [Menger1927]
-/
