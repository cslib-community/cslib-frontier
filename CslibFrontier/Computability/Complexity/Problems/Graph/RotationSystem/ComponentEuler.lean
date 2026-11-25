/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.ComponentRestriction
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.ConnectedEuler
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Equality

/-!
# Reassembling component Euler equations

Restricting the indexed graph to one declared component preserves its vertices, edge
occurrences and face orbits. These are the three counts in the numerical genus test.

## Main results

* `componentGraph_preconnected` gives walks within the restricted graph.
* `RotationSystem.componentFaceEquiv` identifies its faces with the original component faces.
* `RotationSystem.numericalGenusZero_component` restricts numerical genus zero.
* `RotationSystem.numericalGenusZero_of_components` reassembles the Euler equations.
* `RotationSystem.exists_numericalGenusZero_agreeing_on_of_components` combines independent
  choices of genus-zero component rotations with prescribed successors.
-/

public section

namespace Cslib.Complexity.Graph

open Equiv RotationCertificate

private theorem mem_componentGraph_edges_of_endpoint {G : Graph} (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) {p : ℕ × ℕ} (hp : p ∈ G.edges)
    (b : Bool) (hv : (if b then p.2 else p.1) ∈ G.componentVertexSet root) :
    p ∈ (G.componentGraph root).edges := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
  change G.edges[i] = p at hi
  have hvertex : Dart.vertex (G := G) (i, b) ∈ G.componentVertexSet root := by
    rw [← hi, Dart.edge_eq_vertices] at hv
    cases b <;> exact hv
  have hm := (G.mem_componentEdgeSet_iff root hG i b).mpr hvertex
  obtain ⟨j, hj⟩ := (G.componentEdgeEquiv root).surjective ⟨i, hm⟩
  have he : G.edges.get (G.componentEdgeEquiv root j).val = p := by rwa [hj]
  exact List.mem_iff_get.mpr ⟨j, (G.edge_componentEdgeEquiv root j).trans he⟩

/-- Any two declared vertices of the restricted graph are connected within that graph. -/
theorem componentGraph_preconnected {G : Graph} (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) :
    (G.componentGraph root).induced.Preconnected := by
  classical
  intro u v
  let K := G.componentGraph root
  obtain ⟨hr, -, -⟩ : SameComponent G root u.val :=
    (Finset.mem_filter.mp ((G.mem_componentGraph_vertices root u.val).mp u.property)).2
  let C := G.induced.connectedComponentMk ⟨root, hr⟩
  have hvertex (z : {w // w ∈ G.vertices}) : z ∈ C.supp ↔ z.val ∈ K.vertices := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, G.mem_componentGraph_vertices]
    refine ⟨fun h => Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr z.property,
      ⟨hr, z.property, SimpleGraph.ConnectedComponent.exact h.symm⟩⟩, fun h => ?_⟩
    obtain ⟨_, _, hreach⟩ := (Finset.mem_filter.mp h).2
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  let f : C.toSimpleGraph →g K.induced :=
    { toFun := fun z => ⟨z.val.val, (hvertex z.val).mp z.property⟩
      map_rel' := by
        intro x y h
        change G.induced.Adj x.val y.val at h
        rw [G.induced_adj, Graph.toSimpleGraph_adj] at h
        rw [Graph.induced_adj, Graph.toSimpleGraph_adj]
        have hx := (G.mem_componentGraph_vertices root x.val.val).mp
          ((hvertex x.val).mp x.property)
        exact ⟨h.1, h.2.imp
          (fun he => mem_componentGraph_edges_of_endpoint root hG he false hx)
          (fun he => mem_componentGraph_edges_of_endpoint root hG he true hx)⟩ }
  have lift (z : {w // w ∈ K.vertices}) : ∃ t : C.supp, f t = z := by
    have hm := (G.mem_componentGraph_vertices root z.val).mp z.property
    let old : {w // w ∈ G.vertices} := ⟨z.val, List.mem_toFinset.mp (Finset.mem_filter.mp hm).1⟩
    exact ⟨⟨old, (hvertex old).mpr z.property⟩, rfl⟩
  obtain ⟨x, rfl⟩ := lift u
  obtain ⟨y, rfl⟩ := lift v
  exact (C.reachable_toSimpleGraph x.property y.property).map f

namespace RotationSystem

private theorem componentDartEquiv_sameFace {G : Graph} (r : RotationSystem G) (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d f : Dart (G.componentGraph root)) :
    (r.component root hG).faceNext.SameCycle d f ↔
      r.faceNext.SameCycle (G.componentDartEquiv root hG d).val
        (G.componentDartEquiv root hG f).val := by
  let e := G.componentDartEquiv root hG
  let σ := r.faceNext.subtypePerm (p := fun d => SameComponent G root d.vertex)
    (r.component_faceNext_iff hG root)
  have hsemi (a : Dart (G.componentGraph root)) :
      e ((r.component root hG).faceNext a) = σ (e a) :=
    Subtype.ext (r.componentDartEquiv_faceNext root hG a)
  exact (Perm.sameCycle_equiv_iff e _ σ hsemi d f).symm.trans Perm.sameCycle_subtypePerm

/-- The faces of the restricted rotation are exactly the original faces of that component. -/
noncomputable def componentFaceEquiv {G : Graph} (r : RotationSystem G) (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) :
    (r.component root hG).Face ≃ ComponentFace r root :=
  let e := G.componentDartEquiv root hG
  let mapFace : (r.component root hG).Face → ComponentFace r root := fun q =>
    Quotient.liftOn q (fun d => ⟨Quotient.mk _ (e d).val, (e d).val, (e d).property, rfl⟩)
      (fun d f h => Subtype.ext (Quotient.sound ((r.componentDartEquiv_sameFace root hG d f).mp h)))
  Equiv.ofBijective mapFace ⟨by
    intro x y
    refine Quotient.inductionOn₂ x y (fun d f h => ?_)
    exact Quotient.sound ((r.componentDartEquiv_sameFace root hG d f).mpr
      (Quotient.exact (congrArg Subtype.val h))), by
    rintro ⟨q, d, hd, rfl⟩
    obtain ⟨a, ha⟩ := e.surjective ⟨d, hd⟩
    refine ⟨Quotient.mk _ a, Subtype.ext ?_⟩
    exact congrArg (fun x => (Quotient.mk _ x.val : r.Face)) ha⟩

private theorem numericalGenusZero_component_iff_cards {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (root : ℕ) (d : Dart G)
    (hd : SameComponent G root d.vertex) :
    (r.component root hG).NumericalGenusZero ↔
      (G.componentVertexSet d.vertex).card + (r.componentFaceIndices d.vertex).card =
        (G.componentEdgeSet d.vertex).card + 2 := by
  classical
  let K := G.componentGraph root
  let s := r.component root hG
  let e := G.componentDartEquiv root hG
  have hK := G.componentGraph_endpoints_declared root hG
  obtain ⟨a, -⟩ := e.surjective ⟨d, hd⟩
  have hconn (x : ℕ) (hx : x ∈ K.vertices) (y : ℕ) (hy : y ∈ K.vertices) : SameComponent K x y :=
    ⟨hx, hy, componentGraph_preconnected root hG ⟨x, hx⟩ ⟨y, hy⟩⟩
  have hV : K.vertices.toFinset = G.componentVertexSet root := by
    ext x
    rw [List.mem_toFinset, G.mem_componentGraph_vertices]
  have hE : K.edges.length = (G.componentEdgeSet root).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_congr (G.componentEdgeEquiv root)
  have hF : Nat.card s.Face = (r.componentFaceIndices root).card := by
    rw [r.card_componentFaceIndices, r.count_faceRepresentatives_eq_card_componentFace hG]
    exact Nat.card_congr (r.componentFaceEquiv root hG)
  have hroot (v : ℕ) : SameComponent G d.vertex v ↔ SameComponent G root v :=
    ⟨hd.trans, hd.symm.trans⟩
  have hv : G.componentVertexSet d.vertex = G.componentVertexSet root :=
    Finset.filter_congr fun v _ => hroot v
  have he' : G.componentEdgeSet d.vertex = G.componentEdgeSet root :=
    Finset.filter_congr fun _ _ => hroot _
  have hf : r.componentFaceIndices d.vertex = r.componentFaceIndices root :=
    Finset.filter_congr fun _ _ => and_congr (hroot _) Iff.rfl
  rw [s.numericalGenusZero_iff_connected_euler hK hconn a, hv, he', hf, hV, hE, hF]

private theorem numericalGenusZero_of_component_cover {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices)
    (hs : ∀ d : Dart G, ∃ root, SameComponent G root d.vertex ∧
      (r.component root hG).NumericalGenusZero) : r.NumericalGenusZero := by
  apply (r.numericalGenusZero_iff_component_cards hG).mpr
  intro d
  obtain ⟨root, hd, hz⟩ := hs d
  exact (r.numericalGenusZero_component_iff_cards hG root d hd).mp hz

/-- Restricting a genus-zero rotation to a declared component preserves numerical genus zero. -/
theorem numericalGenusZero_component {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hr : r.NumericalGenusZero) (root : ℕ) :
    (r.component root hG).NumericalGenusZero := by
  cases isEmpty_or_nonempty (Dart (G.componentGraph root)) with
  | inl h =>
    exact ((r.component root hG).numericalGenusZero_iff_component_cards
      (G.componentGraph_endpoints_declared root hG)).mpr (fun d => (h.false d).elim)
  | inr h =>
    obtain ⟨a⟩ := h
    let d := G.componentDartEquiv root hG a
    exact (r.numericalGenusZero_component_iff_cards hG root d.val d.property).mpr
      ((r.numericalGenusZero_iff_component_cards hG).mp hr d.val)

/-- Componentwise numerical genus zero follows from the Euler equation on each restricted
rotation. This includes isolated vertices, whose Euler equation is automatic. -/
theorem numericalGenusZero_of_components {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices)
    (hs : ∀ root ∈ G.vertices, (r.component root hG).NumericalGenusZero) : r.NumericalGenusZero :=
  r.numericalGenusZero_of_component_cover hG fun d =>
    ⟨d.vertex, .refl (vertex_mem hG d), hs d.vertex (vertex_mem hG d)⟩

/-- Independently chosen genus-zero rotations of the components give a genus-zero rotation of
the whole graph. A successor prescribed by `r` at a marked vertex is retained when each
component choice agrees there with the restriction of `r`. -/
theorem exists_numericalGenusZero_agreeing_on_of_components {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (marked : ℕ → Prop)
    (hs : ∀ root ∈ G.vertices, ∃ t : RotationSystem (G.componentGraph root), t.NumericalGenusZero ∧
      ∀ d, marked d.vertex → t.rotate d = (r.component root hG).rotate d) :
    ∃ s : RotationSystem G, s.NumericalGenusZero ∧
      ∀ d, marked d.vertex → s.rotate d = r.rotate d := by
  classical
  choose rotations ht hagree using hs
  let key (d : Dart G) := G.induced.connectedComponentMk ⟨d.vertex, vertex_mem hG d⟩
  let root (c : G.induced.ConnectedComponent) : ℕ := (Quot.out c).val
  let t (c : G.induced.ConnectedComponent) := rotations (root c) (Quot.out c).property
  have hkey (c : G.induced.ConnectedComponent) (d : Dart G) :
      key d = c ↔ SameComponent G (root c) d.vertex := by
    have hc : G.induced.connectedComponentMk (Quot.out c) = c := Quot.out_eq c
    exact ⟨fun h => ⟨(Quot.out c).property, vertex_mem hG d,
      (SimpleGraph.ConnectedComponent.exact (h.trans hc.symm)).symm⟩,
      fun ⟨_, _, h⟩ => (SimpleGraph.ConnectedComponent.sound h.symm).trans hc⟩
  let coord (c : G.induced.ConnectedComponent) :
      Dart (G.componentGraph (root c)) ≃ {d : Dart G // key d = c} :=
    (G.componentDartEquiv (root c) hG).trans (Equiv.subtypeEquivRight fun d => (hkey c d).symm)
  let e := (Equiv.sigmaCongrRight coord).trans (Equiv.sigmaFiberEquiv key)
  let p : Equiv.Perm (Σ c : G.induced.ConnectedComponent, Dart (G.componentGraph (root c))) :=
    Equiv.sigmaCongrRight fun c => (t c).rotate
  let f := e.permCongr p
  have hstep (c : G.induced.ConnectedComponent) :
      Function.Semiconj (fun a => (coord c a).val) (t c).rotate f := by
    intro a
    change e (p ⟨c, a⟩) = e.permCongr p (e ⟨c, a⟩)
    rw [permCongr_apply, symm_apply_apply]
  have hv (c : G.induced.ConnectedComponent) (a : Dart (G.componentGraph (root c))) :
      (coord c a).val.vertex = a.vertex := G.vertex_componentDartEquiv (root c) hG a
  have hvf (d : Dart G) : (f d).vertex = d.vertex := by
    obtain ⟨a, ha⟩ := (coord (key d)).surjective ⟨d, rfl⟩
    have hda := congrArg Subtype.val ha
    calc
      (f d).vertex = (f ((coord (key d) a).val)).vertex := congrArg (Dart.vertex ∘ f) hda.symm
      _ = a.vertex := by rw [← hstep _ a, hv, (t _).vertex_rotate]
      _ = d.vertex := (hv _ a).symm.trans (congrArg Dart.vertex hda)
  let s : RotationSystem G := ⟨f, fun d g => by
    constructor
    · intro h
      obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
      have hp (k : ℕ) : ((f ^ k) d).vertex = d.vertex := by
        induction k with
        | zero => rfl
        | succ k ih => rw [pow_succ', Perm.mul_apply, hvf, ih]
      exact (hp n).symm.trans (congrArg Dart.vertex hn)
    · intro h
      have hkg : key g = key d := congrArg G.induced.connectedComponentMk (Subtype.ext h.symm)
      obtain ⟨a, hda⟩ := (coord (key d)).surjective ⟨d, rfl⟩
      obtain ⟨b, hgb⟩ := (coord (key d)).surjective ⟨g, hkg⟩
      have heq : a.vertex = b.vertex := by rwa [← hv (key d) a, ← hv (key d) b, hda, hgb]
      have hs := ((t _).sameCycle_iff a b).mpr heq
      have hm := hs.map_of_semiconj (hstep (key d))
      simpa only [hda, hgb] using hm⟩
  have hrestrict (c : G.induced.ConnectedComponent) : s.component (root c) hG = t c :=
    ext_rotate <| Equiv.ext fun a => (coord c).injective <| Subtype.ext <|
      (s.componentDartEquiv_rotate (root c) hG a).trans (hstep c a).symm
  refine ⟨s, s.numericalGenusZero_of_component_cover hG (fun d => ?_), fun d hd => ?_⟩
  · exact ⟨root (key d), (hkey _ _).mp rfl, hrestrict (key d) ▸ ht _ (Quot.out (key d)).property⟩
  · let c := key d
    obtain ⟨a, ha⟩ := (coord c).surjective ⟨d, rfl⟩
    have hda : (coord c a).val = d := congrArg Subtype.val ha
    have hma : marked a.vertex := by rwa [← hv c a, hda]
    rw [← hda]
    have h := hagree (root c) (Quot.out c).property a hma
    exact (hstep c a).symm.trans ((congrArg (fun d => (coord c d).val) h).trans
      (r.componentDartEquiv_rotate (root c) hG a))

end RotationSystem
end Cslib.Complexity.Graph
