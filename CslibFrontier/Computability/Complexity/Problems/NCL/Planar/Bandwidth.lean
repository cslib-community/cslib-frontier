/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Reachability
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Bandwidth

/-!
# Planar AND/OR reachability with bounded bandwidth

The input is an ordinary numbered AND/OR graph and its two configurations, under `encAndOrNCL`.
The underlying graph is planar and admits a vertex order with the specified edge-span bound.

## Main definitions

* `BandwidthPlanarAndOrNCL`: configuration reachability with a fixed bandwidth bound.

## References

* [T. C. van der Zanden, *Parameterized Complexity of Graph Constraint Logic*]
  [VanDerZanden2015], Definition 4 and Theorem 6.
-/

public section

namespace Cslib.Complexity.NCL

/-- Planar configuration-to-configuration AND/OR reachability with bandwidth at most `bound`,
under the general graph instance type and encoding. -/
@[expose] def BandwidthPlanarAndOrNCL (bound : ℕ) : Set AndOrNCL.Instance :=
  {x | x ∈ PlanarAndOrNCL ∧ x.graph.graph.HasBandwidth bound}

end Cslib.Complexity.NCL
