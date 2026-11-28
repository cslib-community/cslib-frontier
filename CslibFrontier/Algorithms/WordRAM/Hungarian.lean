/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.Hungarian
public import CslibFrontier.Algorithms.WordRAM.Hungarian.Core
public import CslibFrontier.Algorithms.WordRAM.Hungarian.Instance
public import CslibFrontier.Algorithms.WordRAM.Hungarian.Programs
public import CslibFrontier.Algorithms.WordRAM.Hungarian.Regs
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Signed.Encoding

/-!
# The Hungarian method in `O(n³)` time on the word RAM

This file implements and proves the `O(n³)` slack-array Kuhn–Munkres (Hungarian) algorithm on the
standard-basis word RAM (`Basis.standard`), connecting its output directly to the pure
specification `Cslib.Algorithms.Lean.MaxFlow.hungarian` and Egerváry's optimality theorem
(`IsMinCostPerfectMatching`).

Two layers are provided:

1. **In-memory nonnegative/shifted cost matrices (`coreCode`, `core_exec`).** Given an `n × n`
   matrix `C : Fin n × Fin n → ℕ` of unsigned costs bounded by `W` stored row-major at `baseC`,
   `coreCode` executes row reduction followed by `n` alternating-tree phases with per-column slacks
   `minv` and predecessor rows `bestRow` in `O(n³)` instructions at every word width satisfying
   `Fits w (baseC + n * n + 8 * n + 2 * W + 2)`. By `HgOuterBound` and `HgStepInv`, all row
   potentials remain in `[0, W]`, negated column potentials remain in `[0, W]`, and reduced costs
   and slacks remain in `[0, 2 * W]`, so unsigned word arithmetic never underflows or overflows.
2. **Signed integer assignment instances from `State.init` (`inputCode`, `assignmentProgram`,
   `minCostProgram`).** An `Instance` specifies `n` and `cost : Fin n × Fin n → ℤ`, encoded as
   `n` followed by the `n²` row-major `Signed.encode` words. `inputCode` scans the input for a
   magnitude bound `M ≤ inst.maxMag`, shifts every cost by `+ M` into `[0, 2 * M]` (preserving
   optimal matchings and dual slack steps by `hungarian_add_const`), runs `coreCode`, writes the
   length-prefixed optimal row-to-column assignment list `inst.assignment` for `ExecutesList` /
   `Program.ComputesListInTime`, and computes `Signed.encode` of the minimum matching cost for
   `Executes` / `Program.ComputesInTime`, all within `hungarianTime inst.n` (`O(n³)`) instructions.

## Main definitions

* `Cslib.Algorithms.WordRAM.Hungarian.Instance`: an `n × n` integer assignment instance.
* `Cslib.Algorithms.WordRAM.Hungarian.Instance.encode`,
  `Cslib.Algorithms.WordRAM.Hungarian.Instance.maxMag`,
  `Cslib.Algorithms.WordRAM.Hungarian.Instance.wordBound`,
  `Cslib.Algorithms.WordRAM.Hungarian.Instance.assignedCol`,
  `Cslib.Algorithms.WordRAM.Hungarian.Instance.assignment`,
  `Cslib.Algorithms.WordRAM.Hungarian.Instance.encodedMinCost`: input encoding, word-width
  envelope, and canonical optimal assignment and minimum-cost outputs.
* `Cslib.Algorithms.WordRAM.Hungarian.BaseRegs`,
  `Cslib.Algorithms.WordRAM.Hungarian.CostMem`: register frame and row-major cost-matrix assertion
  for in-memory calls to `coreCode`.
* `Cslib.Algorithms.WordRAM.Hungarian.coreCode`, `Cslib.Algorithms.WordRAM.Hungarian.inputCode`,
  `Cslib.Algorithms.WordRAM.Hungarian.assignmentProgram`,
  `Cslib.Algorithms.WordRAM.Hungarian.minCostProgram`: structured and flat word-RAM programs.
* `Cslib.Algorithms.WordRAM.Hungarian.coreTime`,
  `Cslib.Algorithms.WordRAM.Hungarian.hungarianTime`: explicit `O(n³)` instruction bounds.

## Main results

* `Cslib.Algorithms.WordRAM.Hungarian.Instance.isMinCostPerfectMatching_assignment`: the pairs
  `(u, inst.assignedCol u)` form `(hungarian inst.cost).matching`, hence a minimum-cost perfect
  matching.
* `Cslib.Algorithms.WordRAM.Hungarian.core_exec`: `O(n³)` word-RAM execution of `coreCode` on an
  in-memory `n × n` unsigned cost matrix `C` bounded by `W`.
* `Cslib.Algorithms.WordRAM.Hungarian.executesList_assignment`,
  `Cslib.Algorithms.WordRAM.Hungarian.computesListInTime_assignment`: `assignmentProgram` computes
  the optimal assignment list in `hungarianTime n = O(n³)` instructions.
* `Cslib.Algorithms.WordRAM.Hungarian.executes_minCost`,
  `Cslib.Algorithms.WordRAM.Hungarian.computesInTime_minCost`: `minCostProgram` computes the
  signed-encoded minimum matching cost in `hungarianTime n = O(n³)` instructions.

## References

* [H. W. Kuhn, *The Hungarian Method for the Assignment Problem*][Kuhn1955]
* [J. Munkres, *Algorithms for the Assignment and Transportation Problems*][Munkres1957]
* [J. Edmonds and R. M. Karp, *Theoretical Improvements in Algorithmic Efficiency for Network Flow
  Problems*][EdmondsKarp1972]
* [A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*][Schrijver2003]
-/
