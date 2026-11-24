/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.ComponentRestriction

/-!
# Splitting a vertex along a component

Moving the darts into a component of the vertex-deleted graph separates the two copies
of the cut vertex and decreases the number of edges in each resulting component.
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
  have markOld : ¬marked a.vertex := by
    rintro (h | ⟨h, _⟩)
    · exact hfresh a h
    · exact h rfl
  have markAway (d : Dart G) (hd : d.vertex ≠ a.vertex) :
      marked (e d).vertex ↔ inClass d.vertex := by
    rw [hend, ite_eq_right (fun h => hd (hcut d h))]
    exact or_iff_right (hfresh d)
  have markCut (d : Dart G) (hd : d.vertex = a.vertex) :
      marked (e d).vertex ↔ inClass d.reverse.vertex := by
    have hclass' : inClass d.reverse.vertex ↔ selected d :=
      ⟨fun ⟨_, h⟩ => (hclass d hd).mpr h, fun h => ⟨hloop d hd, (hclass d hd).mp h⟩⟩
    rw [hend, hclass']
    by_cases h : selected d
    · rw [ite_eq_left h]
      exact iff_of_true markNew h
    · rw [ite_eq_right h, hd]
      exact iff_of_false markOld h
  have markReverse (d : Dart H) : marked d.vertex = marked d.reverse.vertex := by
    obtain ⟨d, rfl⟩ := e.surjective d
    change marked (e d).vertex = marked (e d.reverse).vertex
    apply propext
    by_cases hd : d.vertex = a.vertex
    · exact (markCut d hd).trans (markAway d.reverse (hloop d hd)).symm
    by_cases hrev : d.reverse.vertex = a.vertex
    · rw [markAway d hd, markCut d.reverse hrev, Dart.reverse_reverse]
    have hreach : K.Reachable ⟨d.vertex, hd⟩ ⟨d.reverse.vertex, hrev⟩ := by
      by_cases he : d.vertex = d.reverse.vertex
      · have heq : (⟨d.vertex, hd⟩ : {u : ℕ // u ≠ a.vertex}) = ⟨d.reverse.vertex, hrev⟩ :=
          Subtype.ext he
        rw [heq]
      apply SimpleGraph.Adj.reachable
      exact d.adj_vertex_reverse he
    rw [markAway d hd, markAway d.reverse hrev]
    exact ⟨fun ⟨_, h⟩ => ⟨hrev, h.trans hreach⟩, fun ⟨_, h⟩ => ⟨hd, h.trans hreach.symm⟩⟩
  have ha' : (e a).vertex = w := by rw [hend, ite_eq_left ((hclass a rfl).mpr .rfl)]
  have hb' : (e b).vertex = a.vertex := by rw [hend, ite_eq_right hbOutside, hb]
  have hsep : ¬SameComponent H w a.vertex := by
    intro h
    have hm := Dart.eq_of_sameComponent (fun d : Dart H => marked d.vertex)
      (fun d g h => congrArg marked h) markReverse (d := e a) (e := e b) (by rwa [ha', hb'])
    rw [ha', hb'] at hm
    exact markOld (hm ▸ markNew)
  refine ⟨hsep, fun root => ?_⟩
  rw [← Fintype.card_fin G.edges.length, Fintype.card_congr E, Fintype.card_fin]
  exact componentGraph_edges_length_lt hH (a := e a) (b := e b) (by rwa [ha', hb']) root

end Cslib.Complexity.Graph
