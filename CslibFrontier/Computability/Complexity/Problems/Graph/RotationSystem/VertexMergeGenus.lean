/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexMerge
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Transport
public import CslibFrontier.Foundations.GroupTheory.Perm.SelectedOrbits

/-!
# Component and face counts for vertex identification

These facts use the literal successor swap and endpoint update of `mergeVertices`. The
cofacial premise is needed for the face-splitting count; distinct endpoint names are needed
for the two old vertex cycles to merge. Unchanged components retain their indexed faces.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv RotationCertificate Perm.SelectedOrbits

/-- Original declared endpoints remain declared under the actual name update. -/
theorem mergeGraph_endpoints_declared {G : Graph} (h k : Dart G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) :
    ∀ v ∈ (mergeGraph h k).incidenceVertices, v ∈ (mergeGraph h k).vertices :=
  G.endpoints_declared_relabel (Function.update id k.vertex h.vertex) hG

private theorem sameComponent_of_merge_vertex_eq {G : Graph} (h k a b : Dart G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hc : SameComponent G h.vertex k.vertex)
    (he : (mergeDartEquiv h k a).vertex = (mergeDartEquiv h k b).vertex) :
    SameComponent G a.vertex b.vertex := by
  rw [vertex_mergeDartEquiv, vertex_mergeDartEquiv] at he
  by_cases ha : a.vertex = k.vertex <;> by_cases hb : b.vertex = k.vertex
  · rw [ha, hb]
    exact .refl (vertex_mem hG k)
  · simp only [ha, Function.update_self, Function.update_of_ne hb, id_eq] at he
    rw [ha, ← he]
    exact hc.symm
  · simp only [hb, Function.update_self, Function.update_of_ne ha, id_eq] at he
    rw [hb, he]
    exact hc
  · simp only [Function.update_of_ne ha, Function.update_of_ne hb, id_eq] at he
    rw [he]
    exact .refl (vertex_mem hG b)

/-- Identifying two vertices already in one old component preserves exactly its edge
components. This statement uses actual old and new dart endpoints, not an injective name map. -/
theorem sameComponent_mergeGraph_iff {G : Graph} (h k : Dart G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hc : SameComponent G h.vertex k.vertex)
    (a b : Dart G) :
    SameComponent (mergeGraph h k) (mergeDartEquiv h k a).vertex
      (mergeDartEquiv h k b).vertex ↔ SameComponent G a.vertex b.vertex := by
  let e := mergeDartEquiv h k
  refine ⟨fun hab => ?_, sameComponent_map_darts e
    (fun a b he => by simp only [e, vertex_mergeDartEquiv, he])
    (mergeDartEquiv_reverse h k) (mergeGraph_endpoints_declared h k hG)⟩
  let src (d : Dart (mergeGraph h k)) := G.induced.connectedComponentMk
    ⟨(e.symm d).vertex, vertex_mem hG (e.symm d)⟩
  have hv (d f : Dart (mergeGraph h k)) (he : d.vertex = f.vertex) : src d = src f :=
    SimpleGraph.ConnectedComponent.sound <|
      (sameComponent_of_merge_vertex_eq h k (e.symm d) (e.symm f) hG hc
        (by simpa only [e, Equiv.apply_symm_apply] using he)).2.2
  have he (d : Dart (mergeGraph h k)) : src d = src d.reverse := by
    obtain ⟨d, rfl⟩ := e.surjective d
    simpa only [src, e, ← mergeDartEquiv_reverse, Equiv.symm_apply_apply] using
      SimpleGraph.ConnectedComponent.sound (sameComponent_reverse hG d).2.2
  refine ⟨vertex_mem hG a, vertex_mem hG b, SimpleGraph.ConnectedComponent.exact ?_⟩
  simpa only [src, e, Equiv.symm_apply_apply] using Dart.eq_of_sameComponent src hv he hab

/-- Literal incoming-face swap caused by the outgoing vertex-corner swap. -/
theorem faceNext_mergeVertices {G : Graph} (r : RotationSystem G) (h k : Dart G)
    (hk : h.vertex ≠ k.vertex) (d : Dart G) :
    (r.mergeVertices h k hk).faceNext (mergeDartEquiv h k d) =
      mergeDartEquiv h k ((swap h k * r.faceNext) d) := by
  let s := r.mergeVertices h k hk
  let e := mergeDartEquiv h k
  have hr (a : Dart G) : s.rotate (e a) = e (r.rotate (swap h k a)) := by simp [s, e]
  apply s.rotate.injective
  change s.rotate (s.rotate.symm (e d).reverse) = s.rotate (e ((swap h k * r.faceNext) d))
  rw [Equiv.apply_symm_apply, hr]
  simp only [Perm.coe_mul, Function.comp_apply, swap_apply_self]
  change (e d).reverse = e (r.rotate (r.rotate.symm d.reverse))
  simp only [Equiv.apply_symm_apply, e, mergeDartEquiv_reverse]

open Classical in
/-- A cofacial identification adds one actual face in its component, retaining every other
component's face quotient. The selected corners are distinct vertices but may revisit a face. -/
theorem card_componentFace_mergeVertices {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (h k : Dart G) (hk : h.vertex ≠ k.vertex)
    (hf : r.faceNext.SameCycle h k) (a : Dart G) :
    Nat.card (ComponentFace (r.mergeVertices h k hk) (mergeDartEquiv h k a).vertex) =
      Nat.card (ComponentFace r a.vertex) + if SameComponent G a.vertex h.vertex then 1 else 0 := by
  let e := mergeDartEquiv h k
  have hc := r.sameComponent_of_sameFace hG hf
  rw [← Nat.card_congr (orbitOnEquiv e (swap h k * r.faceNext) (r.mergeVertices h k hk).faceNext
    (fun d => (r.faceNext_mergeVertices h k hk d).symm)
    (fun d => SameComponent G a.vertex d.vertex)
    (fun d => SameComponent (mergeGraph h k) (e a).vertex d.vertex)
    fun d => (sameComponent_mergeGraph_iff h k hG hc a d).symm)]
  exact card_orbitOn_swap_mul r.faceNext _ (r.component_faceNext_iff hG a.vertex) h k
    (fun he => hk (congrArg Dart.vertex he)) hf

/-- The actual component vertex set is the image of its old set under the one-name update. -/
theorem componentVertexSet_mergeGraph {G : Graph} (h k : Dart G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hc : SameComponent G h.vertex k.vertex)
    (a : Dart G) :
    (mergeGraph h k).componentVertexSet (mergeDartEquiv h k a).vertex =
      (G.componentVertexSet a.vertex).image (Function.update id k.vertex h.vertex) := by
  classical
  let e := mergeDartEquiv h k
  refine Finset.ext fun v => ⟨fun hv => ?_, fun hv => ?_⟩
  · have ht := (Finset.mem_filter.mp hv).2
    obtain ⟨d, hd⟩ := Dart.exists_of_sameComponent (e a) v ht
    obtain ⟨b, rfl⟩ := e.surjective d
    exact Finset.mem_image.mpr ⟨b.vertex, (Graph.mem_componentVertexSet_dart _ hG b).mpr
      ((sameComponent_mergeGraph_iff h k hG hc a b).mp (by simpa only [e, hd] using ht)),
      (vertex_mergeDartEquiv h k b).symm.trans hd⟩
  · obtain ⟨v, hv, hv'⟩ := Finset.mem_image.mp hv
    have ht := (Finset.mem_filter.mp hv).2
    obtain ⟨b, hb⟩ := Dart.exists_of_sameComponent a v ht
    have he : (e b).vertex = _ := (vertex_mergeDartEquiv h k b).trans
      ((congrArg (Function.update id k.vertex h.vertex) hb).trans hv')
    exact he ▸ (Graph.mem_componentVertexSet_dart _ (mergeGraph_endpoints_declared h k hG)
      (e b)).mpr ((sameComponent_mergeGraph_iff h k hG hc a b).mpr (by simpa only [hb] using ht))

private theorem image_update_id_eq_erase (s : Finset ℕ) (u v : ℕ) (hu : u ∈ s) (hne : u ≠ v) :
    s.image (Function.update id v u) = s.erase v := by
  classical
  refine Finset.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rcases eq_or_ne y v with rfl | hv
    · simpa only [Function.update_self] using Finset.mem_erase.mpr ⟨hne, hu⟩
    · simpa only [Function.update_of_ne hv, id_eq] using Finset.mem_erase.mpr ⟨hv, hy⟩
  · obtain ⟨hxv, hx⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_image.mpr ⟨x, hx, by rw [Function.update_of_ne hxv]; rfl⟩

open Classical in
/-- The selected component loses exactly the second old vertex name. Other components retain
all their distinct declared names, including declared points. -/
theorem card_componentVertexSet_mergeGraph {G : Graph} (h k : Dart G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hc : SameComponent G h.vertex k.vertex)
    (hk : h.vertex ≠ k.vertex) (a : Dart G) :
    ((mergeGraph h k).componentVertexSet (mergeDartEquiv h k a).vertex).card +
      (if SameComponent G a.vertex h.vertex then 1 else 0) =
        (G.componentVertexSet a.vertex).card := by
  rw [componentVertexSet_mergeGraph h k hG hc]
  by_cases ha : SameComponent G a.vertex h.vertex
  · rw [image_update_id_eq_erase _ _ _ ((Graph.mem_componentVertexSet_dart _ hG h).mpr ha) hk]
    simpa only [ha, ite_true] using
      Finset.card_erase_add_one ((Graph.mem_componentVertexSet_dart _ hG k).mpr (ha.trans hc))
  · have hv : k.vertex ∉ G.componentVertexSet a.vertex := fun hv =>
      ha (((Graph.mem_componentVertexSet_dart _ hG k).mp hv).trans hc.symm)
    rw [Finset.image_congr (g := id) fun x hx =>
      Function.update_of_ne (show x ≠ k.vertex from fun he => hv (he ▸ hx)) h.vertex id,
      Finset.image_id]
    simp only [ha, ite_false, Nat.add_zero]

/-- No indexed edge occurrence is removed or identified by the vertex-name update. -/
theorem card_componentEdgeSet_mergeGraph {G : Graph} (h k : Dart G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hc : SameComponent G h.vertex k.vertex)
    (a : Dart G) :
    ((mergeGraph h k).componentEdgeSet (mergeDartEquiv h k a).vertex).card =
      (G.componentEdgeSet a.vertex).card := by
  let e := mergeDartEquiv h k
  have h₁ := Nat.card_congr (edgeOrbitEquiv G hG a)
  have h₂ := Nat.card_congr (edgeOrbitEquiv (mergeGraph h k)
    (mergeGraph_endpoints_declared h k hG) (e a))
  simp only [Nat.card_eq_finsetCard] at h₁ h₂
  exact h₂.symm.trans ((Nat.card_congr (orbitOnEquiv e (Dart.reversal G)
    (Dart.reversal (mergeGraph h k)) (mergeDartEquiv_reverse h k) _ _
    fun d => (sameComponent_mergeGraph_iff h k hG hc a d).symm)).symm.trans h₁)

/-- Identifying two distinct incident vertices at cofacial corners preserves the existing
componentwise numerical genus-zero predicate. Closed and point components outside the selected
component retain their old counts. No injective map on boundary variable labels is assumed. -/
theorem numericalGenusZero_mergeVertices {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hr : r.NumericalGenusZero)
    (h k : Dart G) (hk : h.vertex ≠ k.vertex) (hf : r.faceNext.SameCycle h k) :
    (r.mergeVertices h k hk).NumericalGenusZero := by
  classical
  have hH := mergeGraph_endpoints_declared h k hG
  have hc := r.sameComponent_of_sameFace hG hf
  apply ((r.mergeVertices h k hk).numericalGenusZero_iff_component_cards hH).mpr
  intro d
  obtain ⟨a, rfl⟩ := (mergeDartEquiv h k).surjective d
  have hV := card_componentVertexSet_mergeGraph h k hG hc hk a
  have hE := card_componentEdgeSet_mergeGraph h k hG hc a
  have hF := r.card_componentFace_mergeVertices hG h k hk hf a
  have hEuler := (r.numericalGenusZero_iff_component_cards hG).mp hr a
  rw [card_componentFaceIndices, r.count_faceRepresentatives_eq_card_componentFace hG] at hEuler
  rw [card_componentFaceIndices,
    (r.mergeVertices h k hk).count_faceRepresentatives_eq_card_componentFace hH]
  omega

end Cslib.Complexity.Graph.RotationSystem
