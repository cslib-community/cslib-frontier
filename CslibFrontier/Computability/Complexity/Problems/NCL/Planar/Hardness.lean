/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Reduction
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.PSPACE

/-!
# Planar AND/OR multigraph reachability is PSPACE-complete

Under the general AND/OR graph encodings, restricting the underlying incidence multigraph to
have a continuous polygonal embedding preserves PSPACE-completeness for all three reachability
questions [HearnDemaine2005, Theorem 9]. Self-loops and parallel edges are admitted. The canonical
reductions have loop-free source images with orthogonal grid drawings.

## Main results

* `Cslib.Complexity.NCL.polyTimeReducible_TQBFCNF_PlanarAndOrNCL` and its edge variants:
  the three source reductions.
* `Cslib.Complexity.NCL.PlanarAndOrNCL_pspaceComplete`,
  `Cslib.Complexity.NCL.PlanarAndOrNCLEdge_pspaceComplete`,
  `Cslib.Complexity.NCL.PlanarAndOrNCLEdgeToEdge_pspaceComplete`: the completeness theorems.

## References

* [Hearn and Demaine][HearnDemaine2005, Theorem 9]
-/

public section

namespace Cslib.Complexity.NCL

/-- Alternating prenex CNF reduces to fixed-target planar NCL in polynomial time. -/
theorem polyTimeReducible_TQBFCNF_PlanarAndOrNCL :
    PolyTimeReducible encPrenexCNF encAndOrNCL TQBFCNF PlanarAndOrNCL :=
  ⟨PlanarAndOrNCL.reduce, PlanarAndOrNCL.computableInPolyTime_reduce,
    fun x => (PlanarAndOrNCL.reduce_mem_iff x).symm⟩

/-- Fixed-target planar AND/OR multigraph reachability is PSPACE-hard. -/
theorem PlanarAndOrNCL_pspaceHard : PSPACEHard encAndOrNCL PlanarAndOrNCL :=
  TQBFCNF_pspaceHard.trans polyTimeReducible_TQBFCNF_PlanarAndOrNCL

/-- Fixed-target planar AND/OR multigraph reachability is PSPACE-complete. -/
theorem PlanarAndOrNCL_pspaceComplete : PSPACEComplete encAndOrNCL PlanarAndOrNCL :=
  ⟨PlanarAndOrNCL_mem_PSPACE, PlanarAndOrNCL_pspaceHard⟩

/-- Alternating prenex CNF reduces to configuration-to-edge planar NCL in polynomial time. -/
theorem polyTimeReducible_TQBFCNF_PlanarAndOrNCLEdge :
    PolyTimeReducible encPrenexCNF encAndOrNCLEdge TQBFCNF PlanarAndOrNCLEdge :=
  ⟨PlanarAndOrNCLEdge.reduce, PlanarAndOrNCLEdge.computableInPolyTime_reduce,
    fun x => (PlanarAndOrNCLEdge.reduce_mem_iff x).symm⟩

/-- Configuration-to-edge planar AND/OR multigraph reachability is PSPACE-hard. -/
theorem PlanarAndOrNCLEdge_pspaceHard : PSPACEHard encAndOrNCLEdge PlanarAndOrNCLEdge :=
  TQBFCNF_pspaceHard.trans polyTimeReducible_TQBFCNF_PlanarAndOrNCLEdge

/-- Configuration-to-edge planar AND/OR multigraph reachability is PSPACE-complete. -/
theorem PlanarAndOrNCLEdge_pspaceComplete :
    PSPACEComplete encAndOrNCLEdge PlanarAndOrNCLEdge :=
  ⟨PlanarAndOrNCLEdge_mem_PSPACE, PlanarAndOrNCLEdge_pspaceHard⟩

/-- Alternating prenex CNF reduces to directional planar NCL in polynomial time. -/
theorem polyTimeReducible_TQBFCNF_PlanarAndOrNCLEdgeToEdge :
    PolyTimeReducible encPrenexCNF encAndOrNCLEdgeToEdge TQBFCNF PlanarAndOrNCLEdgeToEdge :=
  ⟨PlanarAndOrNCLEdgeToEdge.reduce, PlanarAndOrNCLEdgeToEdge.computableInPolyTime_reduce,
    fun x => (PlanarAndOrNCLEdgeToEdge.reduce_mem_iff x).symm⟩

/-- Directional edge-to-edge planar AND/OR multigraph reachability is PSPACE-hard. -/
theorem PlanarAndOrNCLEdgeToEdge_pspaceHard :
    PSPACEHard encAndOrNCLEdgeToEdge PlanarAndOrNCLEdgeToEdge :=
  TQBFCNF_pspaceHard.trans polyTimeReducible_TQBFCNF_PlanarAndOrNCLEdgeToEdge

/-- Directional edge-to-edge planar AND/OR multigraph reachability is PSPACE-complete. -/
theorem PlanarAndOrNCLEdgeToEdge_pspaceComplete :
    PSPACEComplete encAndOrNCLEdgeToEdge PlanarAndOrNCLEdgeToEdge :=
  ⟨PlanarAndOrNCLEdgeToEdge_mem_PSPACE, PlanarAndOrNCLEdgeToEdge_pspaceHard⟩

end Cslib.Complexity.NCL
