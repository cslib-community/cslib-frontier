/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Bandwidth

/-!
# Transporting bandwidth certificates through graph numbering

Vertex equivalences retain the supplied order; injective edge renaming preserves which ports
belong to the same edge. This transports a diagram certificate to its serialized finite graph.

## Main definitions

* `ConstraintGraph.BandwidthCertificate.ofEquiv`: transport a certificate with its actual order.
-/

public section

namespace Cslib.Complexity.NCL.ConstraintGraph

/-- Rename vertices and edges while retaining the existing bandwidth order. -/
@[expose] def BandwidthCertificate.ofEquiv {V V' E E' : Type*} {bound : ℕ}
    {G : ConstraintGraph V E} {G' : ConstraintGraph V' E'} (C : BandwidthCertificate G bound)
    (vertices : V ≃ V') (edges : E → E') (hinj : Function.Injective edges)
    (hgraph : ∀ v, G' (vertices v) = (G v).map edges) : BandwidthCertificate G' bound where
  size := C.size
  order := vertices.symm.trans C.order
  span u v p hp q hq he := by
    have hu : G' u = (G (vertices.symm u)).map edges := by
      simpa only [Equiv.apply_symm_apply] using hgraph (vertices.symm u)
    have hv : G' v = (G (vertices.symm v)).map edges := by
      simpa only [Equiv.apply_symm_apply] using hgraph (vertices.symm v)
    rw [hu] at hp
    rw [hv] at hq
    change p ∈ (G (vertices.symm u)).ports.map (WeightedPort.map edges) at hp
    change q ∈ (G (vertices.symm v)).ports.map (WeightedPort.map edges) at hq
    obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
    obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
    exact C.span _ _ p₀ hp₀ q₀ hq₀ (hinj he)

end Cslib.Complexity.NCL.ConstraintGraph
