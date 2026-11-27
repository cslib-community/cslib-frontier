/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

import CslibFrontier.Computability.Complexity.Problems.NCL.Hardness

/-! Checked examples of the three reductions to explicit AND/OR reachability. -/

open Cslib.Complexity Cslib.Complexity.NCL QBF Turing.MultiTapeTM

namespace CslibFrontierTests.NCLHardness

example (x : PrenexCNF) :
    encPrenexCNF x = encPair (encList (encPair encNat encNat)) encCNF
      (x.rounds, x.matrix) := rfl

example (x : PrenexCNF) : (Reduction.graphData x).checkValid = true :=
  (AndOrGraph.checkValid_eq_true_iff _).2 (Reduction.graphData_valid x)

example : Reduction.toConfig ⟨[], []⟩ ∈ AndOrNCL := by
  rw [Reduction.mem_toConfig_iff, mem_TQBFCNF, mem_TQBF]
  exact ⟨rfl, rfl⟩

example : Reduction.toEdge ⟨[], [[]]⟩ ∉ AndOrNCLEdge := by
  rw [Reduction.mem_toEdge_iff, mem_TQBFCNF, mem_TQBF]
  decide +kernel

example : Reduction.toEdgeToEdge ⟨[], []⟩ ∈ AndOrNCLEdgeToEdge := by
  rw [Reduction.mem_toEdgeToEdge_iff, mem_TQBFCNF, mem_TQBF]
  exact ⟨rfl, rfl⟩

end CslibFrontierTests.NCLHardness
