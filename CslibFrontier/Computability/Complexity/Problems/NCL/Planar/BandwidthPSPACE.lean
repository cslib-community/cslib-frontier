/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Bandwidth
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.PSPACE
import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.Bandwidth
import CslibFrontier.Computability.Complexity.Classes.Inclusions

/-!
# Bounded-bandwidth planar AND/OR reachability is in PSPACE

The bandwidth condition has polynomially bounded rank certificates. Intersecting its NP upper
bound with ordinary planar NCL reachability gives PSPACE membership on the general graph input.

## Main results

* `BandwidthPlanarAndOrNCL_mem_PSPACE`: the upper bound for every fixed bandwidth.

## References

* [T. C. van der Zanden, *Parameterized Complexity of Graph Constraint Logic*]
  [VanDerZanden2015], Theorem 6.
-/

public section

namespace Cslib.Complexity.NCL

/-- Planar AND/OR reachability with any fixed bandwidth bound is in PSPACE under `encAndOrNCL`. -/
theorem BandwidthPlanarAndOrNCL_mem_PSPACE (bound : ℕ) :
    BandwidthPlanarAndOrNCL bound ∈ PSPACE encAndOrNCL := by
  have hr : PolyTimeReducible encAndOrNCL encAndOrGraph
      {x : AndOrNCL.Instance | x.graph.graph.HasBandwidth bound}
      {g : AndOrGraph | g.graph.HasBandwidth bound} :=
    ⟨AndOrNCL.Instance.graph, by fun_prop, fun _ => Iff.rfl⟩
  exact inter_mem_PSPACE PlanarAndOrNCL_mem_PSPACE
    (hr.mem_PSPACE (NP_subset_PSPACE (AndOrGraph.hasBandwidth_mem_NP bound)))

end Cslib.Complexity.NCL
