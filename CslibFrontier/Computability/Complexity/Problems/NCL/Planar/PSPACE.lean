/-
Copyright (c) 2026 Samuel Schlesinger, Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Reachability
public import CslibFrontier.Computability.Complexity.Problems.NCL.PSPACE.EdgeToEdge
import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GraphPolyTime
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Classes.Alternation.NP
import CslibFrontier.Computability.Complexity.Classes.Alternation.TQBF
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Equivalence
import CslibFrontier.Computability.PolyTime.Graph.RotationSystem
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat

/-!
# Planar AND/OR multigraph reachability is in PSPACE

Planarity is verified by a polynomially bounded rotation certificate, using the equivalence
between numerical genus zero and a continuous polygonal embedding. The resulting NP bound and
the general reachability upper bounds give PSPACE membership under the general graph encodings.

## Main results

* `PlanarAndOrNCL_mem_PSPACE` and its edge variants give the three planar reachability upper bounds.

## References

* [Hearn and Demaine][HearnDemaine2005, Theorem 9]
-/

public section

namespace Cslib.Complexity.NCL

open _root_.Turing.MultiTapeTM

private theorem isPlanar_mem_NP : {g : AndOrGraph | g.IsPlanar} ∈ NP encAndOrGraph := by
  let D : Decoder Graph.encRotationCertificate :=
    Decoder.nat.list.map Graph.RotationCertificate.mk Graph.RotationCertificate.successor
      (fun _ => rfl) (fun _ => rfl)
  have hg := AndOrGraph.computableInPolyTime_incidenceGraph
  have hcheck : ComputableInPolyTime
      (fun p : AndOrGraph × Graph.RotationCertificate =>
        Graph.RotationCertificate.verifyGenusZero p.1.incidenceGraph p.2)
      (encPair encAndOrGraph Graph.encRotationCertificate) encBool := by fun_prop
  obtain ⟨p, hp⟩ :=
    AndOrGraph.computableInPolyTime_incidenceGraph.polyBounded_length.exists_polynomial
  have hequiv (x : AndOrGraph) :=
    (Graph.RotationSystem.exists_numericalGenusZero_iff_exists_polygonalDrawing
      (AndOrGraph.incidenceGraph_endpoints x)).symm.trans
      (Graph.RotationCertificate.exists_bounded_certificate_iff x.incidenceGraph
        (AndOrGraph.incidenceGraph_endpoints x))
  refine mem_NP_of_check (p := 10 * (p + 1) ^ 2) D hcheck ?_ ?_
  · intro x c hc
    obtain ⟨hr, hn⟩ := (Graph.RotationCertificate.verifyGenusZero_eq_true_iff _ _).mp hc
    exact (Graph.RotationSystem.exists_numericalGenusZero_iff_exists_polygonalDrawing
      (AndOrGraph.incidenceGraph_endpoints x)).mp ⟨_, hn⟩
  · intro x hx
    obtain ⟨c, hsize, hc⟩ := (hequiv x).mp hx
    refine ⟨c, hc, hsize.trans ?_⟩
    simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_ofNat, Polynomial.eval_one] using
        Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left (Nat.add_le_add_right (hp x) 1) 2)

private theorem isPlanar_mem_PSPACE : {g : AndOrGraph | g.IsPlanar} ∈ PSPACE encAndOrGraph :=
  (NP_subset_AP.trans AP_subset_PSPACE) isPlanar_mem_NP

private theorem planarProblem_mem_PSPACE {A : Type} {enc : A ↪ List Bool} {S : Set A}
    (graph : A → AndOrGraph) (hg : ComputableInPolyTime graph enc encAndOrGraph)
    (hS : S ∈ PSPACE enc) : {x | x ∈ S ∧ (graph x).IsPlanar} ∈ PSPACE enc :=
  inter_mem_PSPACE hS
    ((show PolyTimeReducible enc encAndOrGraph
      {x | (graph x).IsPlanar} {g | g.IsPlanar} from
        ⟨graph, hg, fun _ => Iff.rfl⟩).mem_PSPACE isPlanar_mem_PSPACE)

/-- Fixed-target reachability on planar AND/OR multigraphs is in PSPACE. -/
theorem PlanarAndOrNCL_mem_PSPACE : PlanarAndOrNCL ∈ PSPACE encAndOrNCL :=
  planarProblem_mem_PSPACE AndOrNCL.Instance.graph (by fun_prop) AndOrNCL_mem_PSPACE

/-- Configuration-to-edge reachability on planar AND/OR multigraphs is in PSPACE. -/
theorem PlanarAndOrNCLEdge_mem_PSPACE : PlanarAndOrNCLEdge ∈ PSPACE encAndOrNCLEdge :=
  planarProblem_mem_PSPACE AndOrNCLEdge.Instance.graph (by fun_prop) AndOrNCLEdge_mem_PSPACE

/-- Directional edge-to-edge reachability on planar AND/OR multigraphs is in PSPACE. -/
theorem PlanarAndOrNCLEdgeToEdge_mem_PSPACE :
    PlanarAndOrNCLEdgeToEdge ∈ PSPACE encAndOrNCLEdgeToEdge :=
  planarProblem_mem_PSPACE AndOrNCLEdgeToEdge.Instance.graph (by fun_prop)
    AndOrNCLEdgeToEdge_mem_PSPACE

end Cslib.Complexity.NCL
