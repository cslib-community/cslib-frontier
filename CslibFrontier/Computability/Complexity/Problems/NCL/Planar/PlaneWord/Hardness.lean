/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.PlaneWord.Reduction
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.PlaneWord.PSPACE

/-!
# Plane-word AND/OR NCL is PSPACE-complete

These structurally encoded languages are intermediate targets for planar puzzle reductions. The
source emitter runs in polynomial time and preserves all three reachability questions. Compilation
yields the planar multigraph instances used for [HearnDemaine2005, Theorem 9].

## Main results

* `Cslib.Complexity.NCL.polyTimeReducible_TQBFCNF_PlaneWordAndOrNCL` and its edge variants:
  the three source reductions.
* `Cslib.Complexity.NCL.PlaneWordAndOrNCL_pspaceComplete`,
  `Cslib.Complexity.NCL.PlaneWordAndOrNCLEdge_pspaceComplete`,
  `Cslib.Complexity.NCL.PlaneWordAndOrNCLEdgeToEdge_pspaceComplete`: the completeness theorems.

## References

* [Hearn and Demaine][HearnDemaine2005, Theorem 9]
-/

public section

namespace Cslib.Complexity.NCL

/-- Alternating prenex CNF reduces to fixed-target plane AND/OR NCL in polynomial time. -/
theorem polyTimeReducible_TQBFCNF_PlaneWordAndOrNCL :
    PolyTimeReducible encPrenexCNF encPlaneWordAndOrNCL TQBFCNF PlaneWordAndOrNCL :=
  ⟨PlaneWordAndOrNCL.reduce, PlaneWordAndOrNCL.computableInPolyTime_reduce,
    fun x => (PlaneWordAndOrNCL.reduce_mem_iff x).symm⟩

/-- Fixed-target plane AND/OR NCL is PSPACE-hard. -/
theorem PlaneWordAndOrNCL_pspaceHard : PSPACEHard encPlaneWordAndOrNCL PlaneWordAndOrNCL :=
  TQBFCNF_pspaceHard.trans polyTimeReducible_TQBFCNF_PlaneWordAndOrNCL

/-- Fixed-target plane AND/OR NCL is PSPACE-complete. -/
theorem PlaneWordAndOrNCL_pspaceComplete : PSPACEComplete encPlaneWordAndOrNCL PlaneWordAndOrNCL :=
  ⟨PlaneWordAndOrNCL_mem_PSPACE, PlaneWordAndOrNCL_pspaceHard⟩

/-- Alternating prenex CNF reduces to configuration-to-edge plane AND/OR NCL in polynomial time. -/
theorem polyTimeReducible_TQBFCNF_PlaneWordAndOrNCLEdge :
    PolyTimeReducible encPrenexCNF encPlaneWordAndOrNCLEdge TQBFCNF PlaneWordAndOrNCLEdge :=
  ⟨PlaneWordAndOrNCLEdge.reduce, PlaneWordAndOrNCLEdge.computableInPolyTime_reduce,
    fun x => (PlaneWordAndOrNCLEdge.reduce_mem_iff x).symm⟩

/-- Configuration-to-edge plane AND/OR NCL is PSPACE-hard. -/
theorem PlaneWordAndOrNCLEdge_pspaceHard :
    PSPACEHard encPlaneWordAndOrNCLEdge PlaneWordAndOrNCLEdge :=
  TQBFCNF_pspaceHard.trans polyTimeReducible_TQBFCNF_PlaneWordAndOrNCLEdge

/-- Configuration-to-edge plane AND/OR NCL is PSPACE-complete. -/
theorem PlaneWordAndOrNCLEdge_pspaceComplete :
    PSPACEComplete encPlaneWordAndOrNCLEdge PlaneWordAndOrNCLEdge :=
  ⟨PlaneWordAndOrNCLEdge_mem_PSPACE, PlaneWordAndOrNCLEdge_pspaceHard⟩

/-- Alternating prenex CNF reduces to directional plane AND/OR NCL in polynomial time. -/
theorem polyTimeReducible_TQBFCNF_PlaneWordAndOrNCLEdgeToEdge :
    PolyTimeReducible encPrenexCNF encPlaneWordAndOrNCLEdgeToEdge
      TQBFCNF PlaneWordAndOrNCLEdgeToEdge :=
  ⟨PlaneWordAndOrNCLEdgeToEdge.reduce, PlaneWordAndOrNCLEdgeToEdge.computableInPolyTime_reduce,
    fun x => (PlaneWordAndOrNCLEdgeToEdge.reduce_mem_iff x).symm⟩

/-- Directional edge-to-edge plane AND/OR NCL is PSPACE-hard. -/
theorem PlaneWordAndOrNCLEdgeToEdge_pspaceHard :
    PSPACEHard encPlaneWordAndOrNCLEdgeToEdge PlaneWordAndOrNCLEdgeToEdge :=
  TQBFCNF_pspaceHard.trans polyTimeReducible_TQBFCNF_PlaneWordAndOrNCLEdgeToEdge

/-- Directional edge-to-edge plane AND/OR NCL is PSPACE-complete. -/
theorem PlaneWordAndOrNCLEdgeToEdge_pspaceComplete :
    PSPACEComplete encPlaneWordAndOrNCLEdgeToEdge PlaneWordAndOrNCLEdgeToEdge :=
  ⟨PlaneWordAndOrNCLEdgeToEdge_mem_PSPACE, PlaneWordAndOrNCLEdgeToEdge_pspaceHard⟩

end Cslib.Complexity.NCL
