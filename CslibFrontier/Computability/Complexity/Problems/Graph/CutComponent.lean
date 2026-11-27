/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.ComponentRestriction
import Mathlib.Data.List.GetD

/-!
# Splitting a vertex along a component

Moving the darts into a component of the vertex-deleted graph separates the two copies
of the cut vertex and decreases the number of edges in each resulting component.
`split_darts_endpoints_declared` preserves endpoint declarations, and
`vertex_preimage_split_darts` identifies each redirected end with its original vertex.
-/

public section

namespace Cslib.Complexity.Graph

open Equiv RotationCertificate

/-- Redirecting the darts into one component of the vertex-deleted graph separates the two
copies of the vertex and leaves strictly fewer edges in every component. The selected ends
may have any cyclic order. -/
theorem split_component_separates {G H : Graph} (a b : Dart G) (hb : b.vertex = a.vertex)
    (w : ℕ) (hfresh : ∀ d : Dart G, d.vertex ≠ w)
    (hloop : ∀ d : Dart G, d.vertex = a.vertex → d.reverse.vertex ≠ a.vertex)
    (selected : Dart G → Prop) [DecidablePred selected] (hbOutside : ¬ selected b)
    (hcut : ∀ d, selected d → d.vertex = a.vertex)
    (hclass : ∀ (d : Dart G) (hd : d.vertex = a.vertex), selected d ↔
      (G.toSimpleGraph.induce {u | u ≠ a.vertex}).Reachable
        ⟨a.reverse.vertex, hloop a rfl⟩ ⟨d.reverse.vertex, hloop d hd⟩)
    (E : Fin G.edges.length ≃ Fin H.edges.length)
    (hEnds : ∀ d : Dart G, Dart.vertex (G := H) (E d.1, d.2) =
      if selected d then w else d.vertex)
    (hH : ∀ u ∈ H.incidenceVertices, u ∈ H.vertices) :
    ¬SameComponent H w a.vertex ∧
      (∀ root, (H.componentGraph root).edges.length < G.edges.length) := by
  classical
  let e : Dart G ≃ Dart H := E.prodCongr (Equiv.refl Bool)
  let K := G.toSimpleGraph.induce {u | u ≠ a.vertex}
  let inClass (u : ℕ) : Prop := ∃ hu : u ≠ a.vertex,
    K.Reachable ⟨a.reverse.vertex, hloop a rfl⟩ ⟨u, hu⟩
  let marked (u : ℕ) : Prop := u = w ∨ inClass u
  have hend (d : Dart G) : (e d).vertex = _ := hEnds d
  have markNew : marked w := Or.inl rfl
  have markOld : ¬marked a.vertex := fun h => h.elim (hfresh a) fun ⟨ha, _⟩ => ha rfl
  have markAway (d : Dart G) (hd : d.vertex ≠ a.vertex) :
      marked (e d).vertex ↔ inClass d.vertex := by
    rw [hend, ite_eq_right (fun h => hd (hcut d h))]
    exact or_iff_right (hfresh d)
  have markCut (d : Dart G) (hd : d.vertex = a.vertex) :
      marked (e d).vertex ↔ inClass d.reverse.vertex := by
    by_cases h : selected d
    · rw [hend, ite_eq_left h]
      exact iff_of_true markNew ⟨hloop d hd, (hclass d hd).mp h⟩
    · rw [hend, ite_eq_right h, hd]
      exact iff_of_false markOld fun ⟨_, hr⟩ => h ((hclass d hd).mpr hr)
  have markReverse (d : Dart H) : marked d.vertex = marked d.reverse.vertex := by
    obtain ⟨d, rfl⟩ := e.surjective d
    change marked (e d).vertex = marked (e d.reverse).vertex
    apply propext
    by_cases hd : d.vertex = a.vertex
    · exact (markCut d hd).trans (markAway d.reverse (hloop d hd)).symm
    by_cases hrev : d.reverse.vertex = a.vertex
    · rw [markAway d hd, markCut d.reverse hrev, Dart.reverse_reverse]
    have hreach : K.Reachable ⟨d.vertex, hd⟩ ⟨d.reverse.vertex, hrev⟩ :=
      if he : d.vertex = d.reverse.vertex then
        (Subtype.ext he : (⟨d.vertex, hd⟩ : {u | u ≠ a.vertex}) = ⟨d.reverse.vertex, hrev⟩) ▸ .rfl
      else SimpleGraph.Adj.reachable (G := K) (d.adj_vertex_reverse he)
    rw [markAway d hd, markAway d.reverse hrev]
    exact ⟨fun ⟨_, h⟩ => ⟨hrev, h.trans hreach⟩, fun ⟨_, h⟩ => ⟨hd, h.trans hreach.symm⟩⟩
  have ha' : (e a).vertex = w := by rw [hend, ite_eq_left ((hclass a rfl).mpr .rfl)]
  have hb' : (e b).vertex = a.vertex := by rw [hend, ite_eq_right hbOutside, hb]
  have hsep : ¬SameComponent H w a.vertex := fun h => by
    have hm := Dart.eq_of_sameComponent (fun d : Dart H => marked d.vertex)
      (fun _ _ h => congrArg marked h) markReverse (d := e a) (e := e b) (by rwa [ha', hb'])
    rw [ha', hb'] at hm
    exact markOld (hm ▸ markNew)
  refine ⟨hsep, fun root => ?_⟩
  rw [← Fintype.card_fin G.edges.length, Fintype.card_congr E, Fintype.card_fin]
  exact componentGraph_edges_length_lt hH (a := e a) (b := e b) (by rwa [ha', hb']) root

/-- Redirecting selected indexed ends to a prepended vertex preserves endpoint declarations. -/
theorem split_darts_endpoints_declared {G H : Graph}
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices)
    (w : ℕ) (selected : Dart G → Prop) [DecidablePred selected]
    (E : Fin G.edges.length ≃ Fin H.edges.length)
    (hvertices : H.vertices = w :: G.vertices)
    (hEnds : ∀ d : Dart G, Dart.vertex (G := H) (E d.1, d.2) =
      if selected d then w else d.vertex) :
    ∀ v ∈ H.incidenceVertices, v ∈ H.vertices := by
  let e : Dart G ≃ Dart H := E.prodCongr (Equiv.refl Bool)
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
  let j : Fin (2 * H.edges.length) := ⟨i, hi.trans_eq (incidenceVertices_length H)⟩
  obtain ⟨d, hd⟩ := e.surjective ((Dart.indexEquiv H).symm j)
  have heq : (e d).index = i :=
    congrArg Fin.val ((congrArg (Dart.indexEquiv H) hd).trans
      ((Dart.indexEquiv H).apply_symm_apply j))
  rw [← List.getD_eq_getElem _ _ hi, ← heq, Dart.vertex_index,
    show (e d).vertex = _ from hEnds d, hvertices]
  split
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (RotationSystem.vertex_mem hG d)

/-- If redirected darts were all at one vertex, identifying the fresh split label with
that vertex recovers each original indexed endpoint. -/
theorem vertex_preimage_split_darts {G H : Graph} (v w : ℕ)
    (hfresh : ∀ d : Dart G, d.vertex ≠ w)
    (selected : Dart G → Prop) [DecidablePred selected]
    (hselected : ∀ d, selected d → d.vertex = v)
    (E : Fin G.edges.length ≃ Fin H.edges.length)
    (hEnds : ∀ d : Dart G, Dart.vertex (G := H) (E d.1, d.2) =
      if selected d then w else d.vertex) (i : Fin H.edges.length) (b : Bool) :
    Dart.vertex (G := G) (E.symm i, b) =
      Function.update id w v (Dart.vertex (G := H) (i, b)) := by
  have hd := hEnds (E.symm i, b)
  rw [E.apply_symm_apply] at hd
  rw [hd]
  split_ifs with h
  · rw [Function.update_self, hselected _ h]
  · rw [Function.update_of_ne (hfresh _), id_eq]

end Cslib.Complexity.Graph
