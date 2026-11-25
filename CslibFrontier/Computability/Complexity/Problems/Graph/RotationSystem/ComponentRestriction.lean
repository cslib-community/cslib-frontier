/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.ComponentCounts
import Mathlib.Data.Finset.Sort

/-!
# Restricting a listed rotation to one graph component

The component graph retains exactly the declared vertices and indexed edge occurrences of
the chosen component. Its rotation follows the same successors on those ends, using the
explicit bijection from the smaller graph's darts to the original component darts.

## Main definitions and results

* `componentGraph` and `componentDartEquiv` retain the original edge indices and end tags.
* `RotationSystem.component` restricts the rotation. `componentDartEquiv_reverse`,
  `RotationSystem.componentDartEquiv_rotate` and `RotationSystem.componentDartEquiv_faceNext`
  relate reversal, vertex rotation and face traversal to their original coordinates.
-/

public section

namespace Cslib.Complexity.Graph

open Equiv RotationCertificate

/-- The listed graph of one existing component, retaining edge order and both end tags. -/
@[expose] noncomputable def componentGraph (G : Graph) (root : ℕ) : Graph :=
  let S := G.componentEdgeSet root
  ⟨(G.componentVertexSet root).sort, List.ofFn fun i : Fin S.card => G.edges[S.orderEmbOfFin rfl i]⟩

/-- The actual vertex names of the component graph are the component vertex set. -/
theorem mem_componentGraph_vertices (G : Graph) (root v : ℕ) :
    v ∈ (G.componentGraph root).vertices ↔ v ∈ G.componentVertexSet root := by
  change v ∈ (G.componentVertexSet root).sort (· ≤ ·) ↔ v ∈ G.componentVertexSet root
  exact Finset.mem_sort _

/-- If two darts lie in different components, restricting to any component loses at least
one indexed edge occurrence. -/
theorem componentGraph_edges_length_lt {G : Graph}
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) {a b : Dart G}
    (hsep : ¬SameComponent G a.vertex b.vertex) (root : ℕ) :
    (G.componentGraph root).edges.length < G.edges.length := by
  have hmiss : ∃ d : Dart G, ¬SameComponent G root d.vertex := by
    by_cases ha : SameComponent G root a.vertex
    · exact ⟨b, fun hb => hsep (ha.symm.trans hb)⟩
    · exact ⟨a, ha⟩
  obtain ⟨d, hd⟩ := hmiss
  have hnot : d.1 ∉ G.componentEdgeSet root := fun h =>
    hd ((G.mem_componentVertexSet_dart root hG d).mp
      ((G.mem_componentEdgeSet_iff root hG d.1 d.2).mp h))
  have hproper : G.componentEdgeSet root ⊂ Finset.univ :=
    Finset.ssubset_univ_iff.mpr (fun h => hnot (h ▸ Finset.mem_univ d.1))
  change (List.ofFn fun i : Fin (G.componentEdgeSet root).card =>
    G.edges[(G.componentEdgeSet root).orderEmbOfFin rfl i]).length < G.edges.length
  simpa only [List.length_ofFn, Finset.card_univ, Fintype.card_fin] using
    Finset.card_lt_card hproper

/-- Each position in the component edge list is the corresponding original occurrence. -/
@[expose] noncomputable def componentEdgeEquiv (G : Graph) (root : ℕ) :
    Fin (G.componentGraph root).edges.length ≃ ↥(G.componentEdgeSet root) :=
  ((G.componentEdgeSet root).orderIsoOfFin List.length_ofFn.symm).toEquiv

/-- Each component edge keeps the two labels of its original listed occurrence. -/
theorem edge_componentEdgeEquiv (G : Graph) (root : ℕ)
    (i : Fin (G.componentGraph root).edges.length) :
    (G.componentGraph root).edges[i] = G.edges[(G.componentEdgeEquiv root i).val] := by
  change (List.ofFn fun j : Fin (G.componentEdgeSet root).card =>
    G.edges[(G.componentEdgeSet root).orderEmbOfFin rfl j])[i.val] = _
  rw [List.getElem_ofFn]
  rfl

/-- Restricting a graph to a component preserves the endpoint at each indexed end. -/
theorem vertex_componentEdgeEquiv (G : Graph) (root : ℕ)
    (i : Fin (G.componentGraph root).edges.length) (b : Bool) :
    Dart.vertex (G := G.componentGraph root) (i, b) =
      Dart.vertex (G := G) ((G.componentEdgeEquiv root i).val, b) := by
  have he := G.edge_componentEdgeEquiv root i
  rw [Dart.edge_eq_vertices, Dart.edge_eq_vertices] at he
  cases b
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

/-- The actual component graph declares every endpoint when the original graph does. -/
theorem componentGraph_endpoints_declared (G : Graph) (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) :
    ∀ v ∈ (G.componentGraph root).incidenceVertices, v ∈ (G.componentGraph root).vertices := by
  have hend (d : Dart (G.componentGraph root)) : d.vertex ∈ (G.componentGraph root).vertices := by
    rw [G.mem_componentGraph_vertices, G.vertex_componentEdgeEquiv root d.1 d.2]
    exact (G.mem_componentEdgeSet_iff root hG _ d.2).mp (G.componentEdgeEquiv root d.1).property
  intro v hv
  change v ∈ (G.componentGraph root).edges.flatMap (fun p => [p.1, p.2]) at hv
  obtain ⟨p, hp, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
  change (G.componentGraph root).edges[i] = p at hi
  subst p
  rw [Dart.edge_eq_vertices] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  exact hv.elim (fun h => h.symm ▸ hend (i, false)) (fun h => h.symm ▸ hend (i, true))

private theorem mem_componentEdgeSet_iff_component {G : Graph} (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart G) :
    d.1 ∈ G.componentEdgeSet root ↔ SameComponent G root d.vertex :=
  (G.mem_componentEdgeSet_iff root hG d.1 d.2).trans (G.mem_componentVertexSet_dart root hG d)

/-- Component darts are exactly the original darts at vertices of that component. -/
noncomputable def componentDartEquiv (G : Graph) (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) :
    Dart (G.componentGraph root) ≃ {d : Dart G // SameComponent G root d.vertex} where
  toFun d := ⟨((G.componentEdgeEquiv root d.1).val, d.2),
    (mem_componentEdgeSet_iff_component root hG _).mp (G.componentEdgeEquiv root d.1).property⟩
  invFun d := ((G.componentEdgeEquiv root).symm
    ⟨d.val.1, (mem_componentEdgeSet_iff_component root hG d.val).mpr d.property⟩, d.val.2)
  left_inv d := by
    apply Prod.ext
    · exact (G.componentEdgeEquiv root).symm_apply_apply d.1
    · rfl
  right_inv d := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val ((G.componentEdgeEquiv root).apply_symm_apply
        ⟨d.val.1, (mem_componentEdgeSet_iff_component root hG d.val).mpr d.property⟩)
    · rfl

/-- The dart correspondence preserves the endpoint label. -/
theorem vertex_componentDartEquiv (G : Graph) (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart (G.componentGraph root)) :
    (G.componentDartEquiv root hG d).val.vertex = d.vertex :=
  (G.vertex_componentEdgeEquiv root d.1 d.2).symm

/-- The dart correspondence uses the selected edge occurrence and the original end tag. -/
@[simp] theorem val_componentDartEquiv (G : Graph) (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart (G.componentGraph root)) :
    (G.componentDartEquiv root hG d).val = ((G.componentEdgeEquiv root d.1).val, d.2) := by
  unfold componentDartEquiv
  rfl

/-- The correspondence sends opposite ends of a retained edge to opposite original ends. -/
theorem componentDartEquiv_reverse (G : Graph) (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart (G.componentGraph root)) :
    (G.componentDartEquiv root hG d.reverse).val =
      (G.componentDartEquiv root hG d).val.reverse := by
  simp only [val_componentDartEquiv, Dart.reverse]

namespace RotationSystem

/-- Restrict a rotation to a component, keeping its original successor at each retained dart. -/
noncomputable def component {G : Graph} (r : RotationSystem G) (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) : RotationSystem (G.componentGraph root) where
  rotate := (G.componentDartEquiv root hG).symm.permCongr
    (r.rotate.subtypePerm (p := fun d => SameComponent G root d.vertex)
      (fun d => by rw [r.vertex_rotate]))
  sameCycle_iff a b := by
    let e := G.componentDartEquiv root hG
    let f := r.rotate.subtypePerm (p := fun d => SameComponent G root d.vertex)
      (fun d => by rw [r.vertex_rotate])
    change (e.symm.permCongr f).SameCycle a b ↔ _
    have h := Perm.sameCycle_equiv_iff e.symm f (e.symm.permCongr f)
      (fun d => by simp only [permCongr_apply, Equiv.symm_symm, e.apply_symm_apply]) (e a) (e b)
    rw [e.symm_apply_apply, e.symm_apply_apply] at h
    have hsub : f.SameCycle (e a) (e b) ↔ r.rotate.SameCycle (e a).val (e b).val :=
      Perm.sameCycle_subtypePerm
    rw [h, hsub, r.sameCycle_iff]
    rw [G.vertex_componentDartEquiv root hG a, G.vertex_componentDartEquiv root hG b]

/-- In the original indexed coordinates, the restricted successor is literally the old one. -/
theorem componentDartEquiv_rotate {G : Graph} (r : RotationSystem G) (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart (G.componentGraph root)) :
    (G.componentDartEquiv root hG ((r.component root hG).rotate d)).val =
      r.rotate (G.componentDartEquiv root hG d).val := by
  dsimp only [component]
  simp only [permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

/-- The restricted face successor is the original face successor on the retained darts. -/
theorem componentDartEquiv_faceNext {G : Graph} (r : RotationSystem G) (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (d : Dart (G.componentGraph root)) :
    (G.componentDartEquiv root hG ((r.component root hG).faceNext d)).val =
      r.faceNext (G.componentDartEquiv root hG d).val := by
  change (G.componentDartEquiv root hG ((r.component root hG).rotate.symm d.reverse)).val =
    r.rotate.symm (G.componentDartEquiv root hG d).val.reverse
  apply r.rotate.injective
  rw [r.rotate.apply_symm_apply, ← r.componentDartEquiv_rotate root hG,
    (r.component root hG).rotate.apply_symm_apply, G.componentDartEquiv_reverse]

end RotationSystem
end Cslib.Complexity.Graph
