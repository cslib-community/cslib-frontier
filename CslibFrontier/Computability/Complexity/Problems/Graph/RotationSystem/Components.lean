/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Dual
public import CslibFrontier.Computability.Complexity.Problems.Graph.DartConnectivity

/-!
# Edge components of indexed rotations

The source and actual indexed dual have the same edge components on identified darts.
Vertex and edge-reversal invariants connect the permutation generators to the existing
graph reachability relation. Loops and parallel positions are retained; isolated source
points have no darts in this correspondence.

## Main results

* `Cslib.Complexity.Graph.RotationSystem.sameComponent_dual_iff`: exact edge components.
-/

public section

namespace Cslib.Complexity.Graph


namespace RotationSystem

/-- Dual and source edge components agree on the same indexed darts. Isolated source points
are excluded automatically, since this correspondence is stated at darts. -/
theorem sameComponent_dual_iff {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d e : Dart G) :
    RotationCertificate.SameComponent r.dualGraph
      (r.dualDartEquiv d).vertex (r.dualDartEquiv e).vertex ↔
      RotationCertificate.SameComponent G d.vertex e.vertex := by
  let src (d : Dart G) := G.induced.connectedComponentMk ⟨d.vertex, vertex_mem hG d⟩
  let dst (d : Dart r.dualGraph) := r.dualGraph.induced.connectedComponentMk
    ⟨d.vertex, r.dual_vertex_mem d⟩
  constructor
  · intro h
    have heq := Dart.eq_of_sameComponent (fun d => src (r.dualDartEquiv.symm d))
      (fun d e hv => by
        obtain ⟨d, rfl⟩ := r.dualDartEquiv.surjective d
        obtain ⟨e, rfl⟩ := r.dualDartEquiv.surjective e
        exact SimpleGraph.ConnectedComponent.sound
          (r.sameComponent_of_sameFace hG
            ((r.faceId_eq_iff d e).mp (by simpa only [vertex_dualDartEquiv] using hv))).2.2)
      (fun d => by
        obtain ⟨d, rfl⟩ := r.dualDartEquiv.surjective d
        simpa only [← dualDartEquiv_reverse, Equiv.symm_apply_apply] using
          SimpleGraph.ConnectedComponent.sound (sameComponent_reverse hG d).2.2) h
    exact ⟨vertex_mem hG d, vertex_mem hG e,
      SimpleGraph.ConnectedComponent.exact (by simpa only [Equiv.symm_apply_apply] using heq)⟩
  · intro h
    have hv (d e : Dart G) (hde : d.vertex = e.vertex) :
        dst (r.dualDartEquiv d) = dst (r.dualDartEquiv e) := by
      have hmid := r.dualRotation.sameComponent_of_sameFace r.dualGraph_endpoints_declared
        ((r.dual_sameFace_iff d.reverse e.reverse).mpr (by simpa using hde))
      rw [dualDartEquiv_reverse, dualDartEquiv_reverse] at hmid
      exact SimpleGraph.ConnectedComponent.sound
        ((sameComponent_reverse r.dualGraph_endpoints_declared (r.dualDartEquiv d)).trans
          (hmid.trans (sameComponent_reverse r.dualGraph_endpoints_declared
            (r.dualDartEquiv e)).symm)).2.2
    have heq := Dart.eq_of_sameComponent (fun d => dst (r.dualDartEquiv d)) hv
      (fun d => SimpleGraph.ConnectedComponent.sound (by
        rw [dualDartEquiv_reverse]
        exact (sameComponent_reverse r.dualGraph_endpoints_declared (r.dualDartEquiv d)).2.2)) h
    exact ⟨r.dual_vertex_mem _, r.dual_vertex_mem _,
      SimpleGraph.ConnectedComponent.exact heq⟩

end RotationSystem

end Cslib.Complexity.Graph
