/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.PolyTime.Configurations
public import CslibFrontier.Computability.Complexity.Problems.NCL.PSPACE.EdgeToEdge

/-!
# AND/OR NCL on finite multigraphs is PSPACE-complete

The polynomial-time source emitter maps alternating prenex CNF to a well-formed, loop-free
AND/OR graph, explicit initial and fixed target configurations, and distinguished edge
positions. Its circuit semantics preserve all three reachability questions. Upstream source
hardness and the space upper bounds give PSPACE-completeness for inputs allowing self-loops
and parallel edges [HearnDemaine2005, Theorem 5 and Corollary 6, authors’ version, pp. 7–8].

## Main results

* `Cslib.Complexity.NCL.polyTimeReducible_TQBFCNF_AndOrNCL`: fixed-target source reduction.
* `Cslib.Complexity.NCL.polyTimeReducible_TQBFCNF_AndOrNCLEdge`: configuration-to-edge reduction.
* `Cslib.Complexity.NCL.polyTimeReducible_TQBFCNF_AndOrNCLEdgeToEdge`: directional source reduction.
* `Cslib.Complexity.NCL.AndOrNCL_pspaceComplete`,
  `Cslib.Complexity.NCL.AndOrNCLEdge_pspaceComplete`,
  `Cslib.Complexity.NCL.AndOrNCLEdgeToEdge_pspaceComplete`: the three completeness theorems.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL

/-- Alternating prenex CNF reduces to fixed-target AND/OR NCL in polynomial time. -/
theorem polyTimeReducible_TQBFCNF_AndOrNCL :
    PolyTimeReducible encPrenexCNF encAndOrNCL TQBFCNF AndOrNCL :=
  ⟨QBF.Reduction.toConfig, QBF.Reduction.computableInPolyTime_toConfig,
    fun x => (QBF.Reduction.mem_toConfig_iff x).symm⟩

/-- Fixed-target AND/OR NCL is PSPACE-hard. -/
theorem AndOrNCL_pspaceHard : PSPACEHard encAndOrNCL AndOrNCL :=
  TQBFCNF_pspaceHard.trans polyTimeReducible_TQBFCNF_AndOrNCL

/-- Fixed-target AND/OR NCL is PSPACE-complete. -/
theorem AndOrNCL_pspaceComplete : PSPACEComplete encAndOrNCL AndOrNCL :=
  ⟨AndOrNCL_mem_PSPACE, AndOrNCL_pspaceHard⟩

/-- Alternating prenex CNF reduces to configuration-to-edge AND/OR NCL in polynomial time. -/
theorem polyTimeReducible_TQBFCNF_AndOrNCLEdge :
    PolyTimeReducible encPrenexCNF encAndOrNCLEdge TQBFCNF AndOrNCLEdge :=
  ⟨QBF.Reduction.toEdge, QBF.Reduction.computableInPolyTime_toEdge,
    fun x => (QBF.Reduction.mem_toEdge_iff x).symm⟩

/-- Configuration-to-edge AND/OR NCL is PSPACE-hard. -/
theorem AndOrNCLEdge_pspaceHard : PSPACEHard encAndOrNCLEdge AndOrNCLEdge :=
  TQBFCNF_pspaceHard.trans polyTimeReducible_TQBFCNF_AndOrNCLEdge

/-- Configuration-to-edge AND/OR NCL is PSPACE-complete. -/
theorem AndOrNCLEdge_pspaceComplete : PSPACEComplete encAndOrNCLEdge AndOrNCLEdge :=
  ⟨AndOrNCLEdge_mem_PSPACE, AndOrNCLEdge_pspaceHard⟩

/-- Alternating prenex CNF reduces to directional edge-to-edge AND/OR NCL in polynomial time. -/
theorem polyTimeReducible_TQBFCNF_AndOrNCLEdgeToEdge :
    PolyTimeReducible encPrenexCNF encAndOrNCLEdgeToEdge TQBFCNF AndOrNCLEdgeToEdge :=
  ⟨QBF.Reduction.toEdgeToEdge, QBF.Reduction.computableInPolyTime_toEdgeToEdge,
    fun x => (QBF.Reduction.mem_toEdgeToEdge_iff x).symm⟩

/-- Directional edge-to-edge AND/OR NCL is PSPACE-hard. -/
theorem AndOrNCLEdgeToEdge_pspaceHard : PSPACEHard encAndOrNCLEdgeToEdge AndOrNCLEdgeToEdge :=
  TQBFCNF_pspaceHard.trans polyTimeReducible_TQBFCNF_AndOrNCLEdgeToEdge

/-- Directional edge-to-edge AND/OR NCL is PSPACE-complete. -/
theorem AndOrNCLEdgeToEdge_pspaceComplete :
    PSPACEComplete encAndOrNCLEdgeToEdge AndOrNCLEdgeToEdge :=
  ⟨AndOrNCLEdgeToEdge_mem_PSPACE, AndOrNCLEdgeToEdge_pspaceHard⟩

end Cslib.Complexity.NCL
