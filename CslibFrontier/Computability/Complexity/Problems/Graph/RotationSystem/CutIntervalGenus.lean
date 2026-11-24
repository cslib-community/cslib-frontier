/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CutInterval
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexJoinGenus

/-!
# Rejoining a separated component at a cut vertex

When the darts into one component of the vertex-deleted graph form a proper interval,
cutting that interval puts the two copies of the vertex in different components.
Rejoining these copies at the original corners preserves numerical genus zero.
This is the rotation-system gluing step for [issue #3091](https://github.com/cslib-community/cslib-frontier/issues/3091).
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv RotationCertificate

/-- If a proper interval consists of exactly the darts into one component after deleting
its vertex, the split separates the copies of the vertex. The split rotation's genus-zero
equations then imply those of the original rotation. The split uses the endpoint relocation
and literal successor swap from `exists_split_cutInterval`. -/
theorem numericalGenusZero_of_component_cutInterval {G H : Graph} (r : RotationSystem G)
    (s : RotationSystem H) (a b : Dart G) (hab : a.vertex = b.vertex) (hproper : r.rotate b ≠ a)
    (w : ℕ) (hfresh : ∀ d : Dart G, d.vertex ≠ w)
    (hloop : ∀ d : Dart G, d.vertex = a.vertex → d.reverse.vertex ≠ a.vertex)
    (hinterval : ∀ (d : Dart G) (hd : d.vertex = a.vertex),
      (G.toSimpleGraph.induce {u | u ≠ a.vertex}).Reachable
        ⟨a.reverse.vertex, hloop a rfl⟩ ⟨d.reverse.vertex, hloop d hd⟩ ↔
        r.rotationDistance a d ≤ r.rotationDistance a b)
    (E : Fin G.edges.length ≃ Fin H.edges.length)
    (hEnds : ∀ d : Dart G, Dart.vertex (G := H) (E d.1, d.2) =
      if d.vertex = a.vertex ∧ r.rotationDistance a d ≤ r.rotationDistance a b
      then w else d.vertex)
    (hrotate : s.rotate = (E.prodCongr (Equiv.refl Bool)).permCongr
      (r.rotate * swap b (r.rotate.symm a)))
    (hG : ∀ u ∈ G.incidenceVertices, u ∈ G.vertices)
    (hH : ∀ u ∈ H.incidenceVertices, u ∈ H.vertices) :
    ¬SameComponent H w a.vertex ∧ (s.NumericalGenusZero → r.NumericalGenusZero) := by
  classical
  let e : Dart G ≃ Dart H := E.prodCongr (Equiv.refl Bool)
  let c := r.rotate.symm a
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
    rw [hend, ite_eq_right (fun h => hd h.1)]
    exact or_iff_right (hfresh d)
  have markCut (d : Dart G) (hd : d.vertex = a.vertex) :
      marked (e d).vertex ↔ inClass d.reverse.vertex := by
    have hclass : inClass d.reverse.vertex ↔ r.rotationDistance a d ≤ r.rotationDistance a b :=
      ⟨fun ⟨_, h⟩ => (hinterval d hd).mp h,
        fun h => ⟨hloop d hd, (hinterval d hd).mpr h⟩⟩
    rw [hend, hclass]
    by_cases hdist : r.rotationDistance a d ≤ r.rotationDistance a b
    · rw [ite_eq_left ⟨hd, hdist⟩]
      exact iff_of_true markNew hdist
    · rw [ite_eq_right (fun h => hdist h.2), hd]
      exact iff_of_false markOld hdist
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
      change G.toSimpleGraph.Adj d.vertex d.reverse.vertex
      rw [toSimpleGraph_adj]
      refine ⟨he, ?_⟩
      rcases d with ⟨i, side⟩
      have hm : G.edges[i] ∈ G.edges := List.getElem_mem _
      rw [Dart.edge_eq_vertices] at hm
      cases side
      · exact Or.inl hm
      · exact Or.inr hm
    rw [markAway d hd, markAway d.reverse hrev]
    exact ⟨fun ⟨_, h⟩ => ⟨hrev, h.trans hreach⟩, fun ⟨_, h⟩ => ⟨hd, h.trans hreach.symm⟩⟩
  have hrot (d : Dart G) : s.rotate (e d) = e ((r.rotate * swap b c) d) := by
    rw [hrotate, permCongr_apply, symm_apply_apply]
  have hb : (e b).vertex = w := by rw [hend, ite_eq_left ⟨hab.symm, le_rfl⟩]
  have hnext : (e (r.rotate b)).vertex = a.vertex := by
    rw [hend, r.rotationDistance_rotate_of_ne a b hab hproper,
      ite_eq_right (fun h => by omega), r.vertex_rotate, hab]
  have hc : (e c).vertex = a.vertex := by
    have h := s.vertex_rotate (e c)
    rw [hrot, Perm.mul_apply, swap_apply_right, hnext] at h
    exact h.symm
  have hsep : ¬SameComponent H w a.vertex := by
    intro h
    have hm := Dart.eq_of_sameComponent (fun d : Dart H => marked d.vertex)
      (fun d g h => congrArg marked h) markReverse (d := e b) (e := e c) (by rwa [hb, hc])
    rw [hb, hc] at hm
    exact markOld (hm ▸ markNew)
  refine ⟨hsep, fun hz => s.numericalGenusZero_of_join_swap r hH hG hz (e b) (e c)
    (by rwa [hb, hc]) e.symm (fun _ => rfl) ?_⟩
  intro d
  obtain ⟨d, rfl⟩ := e.surjective d
  rw [Perm.mul_apply, e.injective.swap_apply, hrot, Perm.mul_apply, swap_apply_self,
    symm_apply_apply, symm_apply_apply]

end Cslib.Complexity.Graph.RotationSystem
