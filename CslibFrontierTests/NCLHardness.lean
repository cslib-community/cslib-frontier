/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

import CslibFrontier.Computability.Complexity.Problems.NCL.Hardness

/-! Checked examples of the three reductions to explicit AND/OR reachability. -/

open Cslib.Complexity Cslib.Complexity.NCL QBF

namespace CslibFrontierTests.NCLHardness

example (x : Source.Input) : (Reduction.graphData x).checkValid = true :=
  (AndOrGraph.checkValid_eq_true_iff _).2 (Reduction.graphData_valid x)

example : Reduction.toConfig ([], []) ∈ AndOrNCL :=
  (Reduction.mem_toConfig_iff ([], [])).2 ⟨rfl, rfl⟩

example : Reduction.toEdge ([], [[]]) ∉ AndOrNCLEdge := by
  rw [Reduction.mem_toEdge_iff]
  unfold TQBFCNF TQBF
  decide +kernel

example : Reduction.toEdgeToEdge ([], []) ∈ AndOrNCLEdgeToEdge :=
  (Reduction.mem_toEdgeToEdge_iff ([], [])).2 ⟨rfl, rfl⟩

end CslibFrontierTests.NCLHardness
