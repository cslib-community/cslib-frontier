/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.NetAccess
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.NetSystemTerm

/-!
# The constraint system of a block-counting network

For the network `d` of input `x`, clock `t` and schedule `σ`, the constraint
`v` of `NetworkSystem.toSystem d` has scope the ports `explicitPortsNum` of
vertex `v` and weight the table entries `tableEntryNum`. These are the facts
the counter's accessor contracts need.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open Cslib.Complexity.CountingSimulation Cslib.Circuits.Frontier _root_.Turing
    _root_.Turing.MultiTapePTM

variable {k s : ℕ} {State : Type} [DecidableEq State] (machine : MultiTapePTM k Bool State)
  (e : State ≃ Fin s)

/-- The ports of vertex `v` of the network of clock `t` and schedule `σ`. -/
def netPorts (k s t σ v : ℕ) : List ℕ :=
  explicitPortsNum k (numBlocks t) (letterBits k s (blockLength t)) σ v

theorem lt_numEdges_of_mem_netPorts {t σ v j : ℕ} (h : j ∈ netPorts k s t σ v) :
    j < 2 * (numBlocks t * (3 * k + 1) * letterBits k s (blockLength t)) := by
  unfold netPorts explicitPortsNum at h
  exact List.mem_range.mp (List.mem_filter.mp h).1

end Cslib.Complexity.NtimeDspace.LocalSim
