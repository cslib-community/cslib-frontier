/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.ComponentCounts
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Differences
public import CslibFrontier.Foundations.Data.BitString.ZModTwo
import CslibFrontier.Foundations.LinearAlgebra.Matrix.EndpointIncidence
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Lifting face-even edge labels to vertex spins

The finite-field proof uses the actual indexed source and dual incidence matrices.
Connectedness gives their ranks; componentwise Euler makes the included cut and face-kernel
spaces have equal dimension. This finite-field argument is an original reconstruction.

[DvorakKupec2015], Section 3, Lemma 5 and Corollary 4 (printed p. 439), use differences on
connected plane instances; the proof of Theorem 2 (printed p. 440) applies that correspondence
to satisfiability. Here the statement is the graph-theoretic lifting prerequisite for arbitrary
listed graphs and arbitrary edge bits. Its hypotheses are declared endpoints and the existing
componentwise numerical Euler predicate. It asserts neither the cited CSP equivalence nor a
geometric realization or native complexity bound. Spanning-cotree certificates, runtime
oracles, and a finite natural-number universe are not assumed.

## Main results

* `Cslib.Complexity.Graph.RotationSystem.component_euler_le`: the matrix Euler bound for an
  incident component, without a numerical genus hypothesis.
* `Cslib.Complexity.Graph.RotationSystem.exists_vertexSpins_of_faceEven`: disconnected lifting.
* `Cslib.Complexity.Graph.RotationSystem.faceEven_iff_exists_vertexSpins`: the exact parity test.
* `Cslib.Complexity.Graph.RotationSystem.numericalGenusZero_of_faceEven_lifts`: its algebraic
  converse, with component restriction and zero extension discharged internally.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

private abbrev Vertex (G : Graph) (root : ℕ) := ↥(G.componentVertexSet root)
private abbrev Edge (G : Graph) (root : ℕ) := ↥(G.componentEdgeSet root)

private noncomputable def endpoint (G : Graph) (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (i : Edge G root) (b : Bool) : Vertex G root :=
  ⟨Dart.vertex (G := G) (i.val, b),
    (mem_componentEdgeSet_iff root hG i.val b).mp i.property⟩

private noncomputable def extend (G : Graph) (root : ℕ) (s : Vertex G root → ZMod 2)
    (v : ℕ) : ZMod 2 :=
  if h : v ∈ G.componentVertexSet root then s ⟨v, h⟩ else 0

private theorem extend_endpoint (G : Graph) (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (s : Vertex G root → ZMod 2)
    (i : Edge G root) (b : Bool) :
    extend G root s (Dart.vertex (G := G) (i.val, b)) = s (endpoint G root hG i b) := by
  simp only [extend, dite_eq_left ((mem_componentEdgeSet_iff root hG i.val b).mp i.property),
    endpoint]

private noncomputable def rootVertex (G : Graph)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart G) : Vertex G d.vertex :=
  ⟨d.vertex, (mem_componentVertexSet_dart _ hG d).mpr (.refl (vertex_mem hG d))⟩

private theorem component_constant (G : Graph)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart G)
    (s : Vertex G d.vertex → ZMod 2)
    (hs : ∀ i : Edge G d.vertex,
      s (endpoint G d.vertex hG i false) = s (endpoint G d.vertex hG i true)) :
    ∀ a b, s a = s b := by
  classical
  have hedge (i : Fin G.edges.length) :
      extend G d.vertex s (Dart.vertex (G := G) (i, false)) =
        extend G d.vertex s (Dart.vertex (G := G) (i, true)) := by
    by_cases hi : i ∈ G.componentEdgeSet d.vertex
    · simpa only [extend_endpoint G d.vertex hG s ⟨i, hi⟩] using hs ⟨i, hi⟩
    · simp only [extend, dite_eq_right (mt (mem_componentEdgeSet_iff d.vertex hG i false).mpr hi),
        dite_eq_right (mt (mem_componentEdgeSet_iff d.vertex hG i true).mpr hi)]
  intro a b
  have hda := (Finset.mem_filter.mp a.property).2
  have hdb := (Finset.mem_filter.mp b.property).2
  obtain ⟨p, hp⟩ := Dart.exists_of_sameComponent d a.val hda
  obtain ⟨q, hq⟩ := Dart.exists_of_sameComponent d b.val hdb
  simpa only [hp, hq, extend, dite_eq_left a.property, dite_eq_left b.property] using
    Dart.eq_of_sameComponent (fun p : Dart G => extend G d.vertex s p.vertex)
      (fun _ _ => congrArg (extend G d.vertex s))
      (fun ⟨i, side⟩ => by
        cases side
        · exact hedge i
        · exact (hedge i).symm)
      (d := p) (e := q) (by simpa only [hp, hq] using hda.symm.trans hdb)

private noncomputable def primalMatrix (G : Graph)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart G) :
    Matrix (Vertex G d.vertex) (Edge G d.vertex) (ZMod 2) :=
  Matrix.endpointIncidence (fun i => endpoint G d.vertex hG i false)
    (fun i => endpoint G d.vertex hG i true)

private theorem rank_primalMatrix (G : Graph)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart G) :
    (primalMatrix G hG d).rank + 1 = Fintype.card (Vertex G d.vertex) :=
  Matrix.rank_endpointIncidence_add_one _ _ (rootVertex G hG d)
    (component_constant G hG d)

private noncomputable def dualEndpoint {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart G)
    (i : Edge G d.vertex) (b : Bool) :
    Vertex r.dualGraph (r.dualDartEquiv d).vertex :=
  endpoint r.dualGraph (r.dualDartEquiv d).vertex r.dualGraph_endpoints_declared
    (r.componentEdgeDualEquiv hG d i) b

private theorem dualEndpoint_val {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart G)
    (i : Edge G d.vertex) (b : Bool) :
    (dualEndpoint r hG d i b).val = r.faceId (i.val, b) :=
  r.vertex_dualDartEquiv (i.val, b)

private noncomputable def dualMatrix {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart G) :
    Matrix (Vertex r.dualGraph (r.dualDartEquiv d).vertex) (Edge G d.vertex) (ZMod 2) :=
  Matrix.endpointIncidence (fun i => dualEndpoint r hG d i false)
    (fun i => dualEndpoint r hG d i true)

private theorem rank_dualMatrix {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart G) :
    (dualMatrix r hG d).rank + 1 =
      Fintype.card (Vertex r.dualGraph (r.dualDartEquiv d).vertex) := by
  refine Matrix.rank_endpointIncidence_add_one _ _
    (rootVertex r.dualGraph r.dualGraph_endpoints_declared (r.dualDartEquiv d)) fun s hs =>
    component_constant r.dualGraph r.dualGraph_endpoints_declared (r.dualDartEquiv d) s fun i => ?_
  obtain ⟨i, rfl⟩ := (r.componentEdgeDualEquiv hG d).surjective i
  exact hs i

private theorem dualMatrix_mulVec_sum {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart G)
    (x : Fin G.edges.length → ZMod 2)
    (v : Vertex r.dualGraph (r.dualDartEquiv d).vertex) :
    (dualMatrix r hG d).mulVec (fun i => x i.val) v =
      ∑ a : Dart G, if r.faceId a = v.val then x a.1 else 0 := by
  have hsum (b : Bool) :
      (∑ i : Edge G d.vertex, if r.faceId (i.val, b) = v.val then x i.val else 0) =
        ∑ i : Fin G.edges.length, if r.faceId (i, b) = v.val then x i else 0 := by
    rw [Finset.sum_coe_sort (G.componentEdgeSet d.vertex)
      (fun i => if r.faceId (i, b) = v.val then x i else 0)]
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ite_eq_right fun h => hi ?_
    refine (mem_componentEdgeSet_iff d.vertex hG i b).mpr ((mem_componentVertexSet_dart _ hG _).mpr
      ((r.sameComponent_dual_iff hG d (i, b)).mp
        ((mem_componentVertexSet_dart _ r.dualGraph_endpoints_declared _).mp ?_)))
    rw [r.vertex_dualDartEquiv (i, b), h]
    exact v.property
  have heq (i : Edge G d.vertex) (b : Bool) :
      v = dualEndpoint r hG d i b ↔ r.faceId (i.val, b) = v.val := by
    rw [Subtype.ext_iff, dualEndpoint_val, eq_comm]
  calc (dualMatrix r hG d).mulVec (fun i => x i.val) v
      = (∑ i : Fin G.edges.length, if r.faceId (i, false) = v.val then x i else 0) +
          ∑ i : Fin G.edges.length, if r.faceId (i, true) = v.val then x i else 0 := by
        simp only [dualMatrix, Matrix.endpointIncidence, Matrix.mulVec, dotProduct, add_mul,
          ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, heq, hsum false, hsum true]
    _ = ∑ a : Dart G, if r.faceId a = v.val then x a.1 else 0 := by
        simp only [Dart, Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib]
        exact add_comm _ _

private theorem dualMatrix_mulVec_bit {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart G)
    (x : Fin G.edges.length → Bool)
    (v : Vertex r.dualGraph (r.dualDartEquiv d).vertex) (a : Dart G)
    (ha : r.faceId a = v.val) :
    (dualMatrix r hG d).mulVec (fun i => BitString.bitEquiv.symm (x i.val)) v =
      BitString.bitEquiv.symm (r.faceParity x (Quotient.mk _ a)) := by
  rw [dualMatrix_mulVec_sum r hG d (fun i => BitString.bitEquiv.symm (x i)) v,
    r.faceParity_eq_sum_faceId, map_sum]
  simp only [apply_ite, map_zero, ha]

private theorem primalMatrix_gradient (G : Graph)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart G)
    (s : Vertex G d.vertex → ZMod 2) (i : Edge G d.vertex) :
    (primalMatrix G hG d).transpose.mulVec s i =
      BitString.bitEquiv.symm
        (G.edgeGradient (fun v => BitString.bitEquiv (extend G d.vertex s v)) i.val) := by
  rw [primalMatrix, Matrix.endpointIncidence_transpose_mulVec]
  apply BitString.bitEquiv.injective
  simp only [map_add, RingEquiv.apply_symm_apply, edgeGradient, ← Bool.add_eq_xor]
  rw [extend_endpoint G d.vertex hG s i false, extend_endpoint G d.vertex hG s i true]

private theorem matrix_product_zero {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart G) :
    dualMatrix r hG d * (primalMatrix G hG d).transpose = 0 := by
  classical
  refine Matrix.mulVec_injective (funext fun s => funext fun v => ?_)
  obtain ⟨a, ha⟩ :=
    r.dualGraph_no_isolates v.val (List.mem_toFinset.mp (Finset.mem_filter.mp v.property).1)
  obtain ⟨a, rfl⟩ := r.dualDartEquiv.surjective a
  rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, Pi.zero_apply,
    funext (primalMatrix_gradient G hG d s),
    dualMatrix_mulVec_bit r hG d _ v a (by simpa only [vertex_dualDartEquiv] using ha),
    r.faceEven_edgeGradient]
  rfl

/-- The actual vertices and face cycles of an incident component satisfy the Euler bound.
This elementary consequence of the primal and dual incidence ranks needs neither numerical
genus zero nor global connectedness. The supplied dart selects an incident component; this
statement does not apply to isolated points or assert a geometric realization. -/
theorem component_euler_le {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart G) :
    (G.componentVertexSet d.vertex).card + (r.componentFaceIndices d.vertex).card ≤
      (G.componentEdgeSet d.vertex).card + 2 := by
  classical
  have h := Matrix.rank_add_rank_le_card_of_mul_eq_zero (matrix_product_zero r hG d)
  have hp := rank_primalMatrix G hG d
  have hd := rank_dualMatrix r hG d
  rw [Matrix.rank_transpose] at h
  rw [r.card_component_faces_eq_dual_vertices hG]
  simp only [Vertex, Edge, Fintype.card_coe] at h hp hd; omega

/-- Every face-even assignment lifts on each edge component, with all rank and dimension
ingredients discharged internally from existing reachability and componentwise Euler. -/
theorem exists_vertexSpins_on_component {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hgenus : r.NumericalGenusZero)
    (x : Fin G.edges.length → Bool) (hx : r.FaceEven x) (d : Dart G) :
    ∃ spin : ℕ → Bool, ∀ i ∈ G.componentEdgeSet d.vertex, G.edgeGradient spin i = x i := by
  classical
  have heuler := (r.numericalGenusZero_iff_component_cards hG).mp hgenus d
  rw [r.card_component_faces_eq_dual_vertices hG] at heuler
  have heq := Matrix.range_transpose_eq_ker_of_euler (primalMatrix G hG d)
    (dualMatrix r hG d) (matrix_product_zero r hG d)
    (rank_primalMatrix G hG d) (rank_dualMatrix r hG d)
    (by simpa only [Vertex, Edge, Fintype.card_coe] using heuler)
  have hk : (fun i : Edge G d.vertex => BitString.bitEquiv.symm (x i.val)) ∈
      (dualMatrix r hG d).mulVecLin.ker := by
    rw [LinearMap.mem_ker]
    ext v
    obtain ⟨a, ha⟩ := r.dualGraph_no_isolates v.val
      (List.mem_toFinset.mp (Finset.mem_filter.mp v.property).1)
    obtain ⟨a, rfl⟩ := r.dualDartEquiv.surjective a
    rw [Matrix.mulVecLin_apply, dualMatrix_mulVec_bit r hG d x v a
      (by simpa only [vertex_dualDartEquiv] using ha), hx]
    rfl
  obtain ⟨s, hs⟩ := heq ▸ hk
  exact ⟨fun v => BitString.bitEquiv (extend G d.vertex s v), fun i hi =>
    BitString.bitEquiv.symm.injective
      ((primalMatrix_gradient G hG d s ⟨i, hi⟩).symm.trans (congrFun hs ⟨i, hi⟩))⟩

private theorem range_transpose_eq_ker_of_faceEven_lifts {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices)
    (hlift : ∀ x : Fin G.edges.length → Bool, r.FaceEven x →
      ∃ spin : ℕ → Bool, G.edgeGradient spin = x) (d : Dart G) :
    LinearMap.range (primalMatrix G hG d).transpose.mulVecLin =
      LinearMap.ker (dualMatrix r hG d).mulVecLin := by
  classical
  refine le_antisymm ?_ fun y hy => ?_
  · rw [LinearMap.range_le_ker_iff, ← Matrix.mulVecLin_mul, matrix_product_zero,
      Matrix.mulVecLin_zero]
  · let x (i : Fin G.edges.length) : Bool :=
      if h : i ∈ G.componentEdgeSet d.vertex then BitString.bitEquiv (y ⟨i, h⟩) else false
    have hrestrict : (fun i : Edge G d.vertex => BitString.bitEquiv.symm (x i.val)) = y :=
      funext fun i => by simp only [x, dite_eq_left i.property, RingEquiv.symm_apply_apply]
    have hx : r.FaceEven x := (r.faceEven_iff_dart x).mpr fun a => by
      by_cases ha : RotationCertificate.SameComponent G d.vertex a.vertex
      · let v : Vertex r.dualGraph (r.dualDartEquiv d).vertex :=
          ⟨(r.dualDartEquiv a).vertex, (mem_componentVertexSet_dart _
            r.dualGraph_endpoints_declared _).mpr ((r.sameComponent_dual_iff hG d a).mpr ha)⟩
        have hcalc := dualMatrix_mulVec_bit r hG d x v a (r.vertex_dualDartEquiv a).symm
        rw [hrestrict] at hcalc
        exact BitString.bitEquiv.symm.injective
          (hcalc.symm.trans (congrFun (LinearMap.mem_ker.mp hy) v))
      · rw [r.faceParity_mk, parityOn_eq_sum]
        refine Finset.sum_eq_zero fun e he => ?_
        have hn : e.1 ∉ G.componentEdgeSet d.vertex := fun hm => ha
          (((mem_componentVertexSet_dart _ hG e).mp
            ((mem_componentEdgeSet_iff d.vertex hG e.1 e.2).mp hm)).trans
            (r.sameComponent_of_sameFace hG (Finset.mem_filter.mp he).2).symm)
        simp only [x, dite_eq_right hn, Bool.zero_eq_false]
    obtain ⟨spin, hspin⟩ := hlift x hx
    refine ⟨fun v => BitString.bitEquiv.symm (spin v.val), funext fun i => ?_⟩
    change (primalMatrix G hG d).transpose.mulVec _ i = y i
    rw [primalMatrix, Matrix.endpointIncidence_transpose_mulVec]
    apply BitString.bitEquiv.injective
    simp only [map_add, RingEquiv.apply_symm_apply, Bool.add_eq_xor]
    simpa only [endpoint, edgeGradient, x, dite_eq_left i.property] using congrFun hspin i.val

/-- Algebraic converse to face-even lifting: if every face-even edge labeling is a vertex
gradient, the existing componentwise numerical Euler predicate holds. The component proof
extends edge vectors by zero before applying the hypothesis and reuses the actual incidence
ranks. Declared points use the separate conventional face and require no invented dart.
This characterizes numerical genus zero and asserts no geometric realization. -/
theorem numericalGenusZero_of_faceEven_lifts {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices)
    (hlift : ∀ x : Fin G.edges.length → Bool, r.FaceEven x →
      ∃ spin : ℕ → Bool, G.edgeGradient spin = x) : r.NumericalGenusZero := by
  classical
  refine (r.numericalGenusZero_iff_component_cards hG).mpr fun d => ?_
  have hnull := (dualMatrix r hG d).mulVecLin.finrank_range_add_finrank_ker
  rw [← range_transpose_eq_ker_of_faceEven_lifts r hG hlift d] at hnull
  simp only [Matrix.finrank_range_mulVecLin] at hnull
  rw [Matrix.rank_transpose, Module.finrank_pi] at hnull
  have hp := rank_primalMatrix G hG d
  have hd := rank_dualMatrix r hG d
  rw [r.card_component_faces_eq_dual_vertices hG]
  simp only [Vertex, Edge, Fintype.card_coe] at hnull hp hd; omega

private noncomputable def chosenVertex (G : Graph) (c : G.induced.ConnectedComponent) :
    {v // v ∈ G.vertices} :=
  (Quot.exists_rep c).choose

private theorem chosenVertex_spec (G : Graph) (c : G.induced.ConnectedComponent) :
    G.induced.connectedComponentMk (chosenVertex G c) = c :=
  (Quot.exists_rep c).choose_spec

private noncomputable def componentSpin {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hgenus : r.NumericalGenusZero)
    (x : Fin G.edges.length → Bool) (hx : r.FaceEven x) (c : G.induced.ConnectedComponent) :
    ℕ → Bool :=
  if h : ∃ d : Dart G, d.vertex = (chosenVertex G c).val then
    (r.exists_vertexSpins_on_component hG hgenus x hx h.choose).choose
  else fun _ => false

private theorem componentSpin_correct {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hgenus : r.NumericalGenusZero)
    (x : Fin G.edges.length → Bool) (hx : r.FaceEven x) (c : G.induced.ConnectedComponent)
    (h : ∃ d : Dart G, d.vertex = (chosenVertex G c).val)
    (i : Fin G.edges.length) (hi : i ∈ G.componentEdgeSet (chosenVertex G c).val) :
    G.edgeGradient (componentSpin r hG hgenus x hx c) i = x i := by
  rw [componentSpin, dite_eq_left h]
  exact (r.exists_vertexSpins_on_component hG hgenus x hx h.choose).choose_spec _
    (h.choose_spec.symm ▸ hi)

/-- Every face-even assignment on a componentwise numerically genus-zero indexed rotation
lifts to spins on the original natural-number names. Components are solved independently;
isolated declared points and names outside the graph may be assigned `false`. -/
theorem exists_vertexSpins_of_faceEven {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hgenus : r.NumericalGenusZero)
    (x : Fin G.edges.length → Bool) (hx : r.FaceEven x) :
    ∃ spin : ℕ → Bool, G.edgeGradient spin = x := by
  refine ⟨fun v => if hv : v ∈ G.vertices then
    componentSpin r hG hgenus x hx (G.induced.connectedComponentMk ⟨v, hv⟩) v else false,
    funext fun i => ?_⟩
  have hu : Dart.vertex (G := G) (i, false) ∈ G.vertices := vertex_mem hG (i, false)
  have hv : Dart.vertex (G := G) (i, true) ∈ G.vertices := vertex_mem hG (i, true)
  let c := G.induced.connectedComponentMk ⟨_, hu⟩
  have hcc : c = G.induced.connectedComponentMk ⟨_, hv⟩ :=
    SimpleGraph.ConnectedComponent.sound (sameComponent_reverse hG (i, false)).2.2
  have hroot : RotationCertificate.SameComponent G (Dart.vertex (G := G) (i, false))
      (chosenVertex G c).val :=
    ⟨hu, (chosenVertex G c).property,
      SimpleGraph.ConnectedComponent.exact (chosenVertex_spec G c).symm⟩
  simpa only [edgeGradient, dite_eq_left hu, dite_eq_left hv, ← hcc] using
    componentSpin_correct r hG hgenus x hx c
      (Dart.exists_of_sameComponent ((i, false) : Dart G) _ hroot) i
      ((mem_componentEdgeSet_iff _ hG i false).mpr
        ((mem_componentVertexSet_dart _ hG _).mpr hroot.symm))

/-- Face parity characterizes vertex gradients for arbitrary finite listed graphs under the
existing componentwise numerical genus-zero predicate. The endpoint-declaration hypothesis
is explicit. Loops, parallel occurrences, disconnected components, points, duplicate vertex
declarations, and sparse natural-number names are all retained. The converse needs no genus
assumption; see `faceEven_edgeGradient`. -/
theorem faceEven_iff_exists_vertexSpins {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hgenus : r.NumericalGenusZero)
    (x : Fin G.edges.length → Bool) :
    r.FaceEven x ↔ ∃ spin : ℕ → Bool, G.edgeGradient spin = x :=
  ⟨r.exists_vertexSpins_of_faceEven hG hgenus x, fun ⟨spin, h⟩ => h ▸ r.faceEven_edgeGradient spin⟩

end Cslib.Complexity.Graph.RotationSystem
