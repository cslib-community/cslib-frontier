/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.CutComponent
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

namespace Cslib.Complexity.Graph

open Equiv RotationCertificate RotationSystem

namespace RotationSystem

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
  let selected (d : Dart G) := d.vertex = a.vertex ∧
    r.rotationDistance a d ≤ r.rotationDistance a b
  have hend (d : Dart G) : (e d).vertex = if selected d then w else d.vertex := hEnds d
  have hnextOutside : ¬selected (r.rotate b) := by
    rintro ⟨_, h⟩
    rw [r.rotationDistance_rotate_of_ne a b hab hproper] at h
    omega
  obtain ⟨hsep, _⟩ := split_component_separates a (r.rotate b)
    ((r.vertex_rotate b).trans hab.symm) w hfresh hloop selected hnextOutside
    (fun _ h => h.1) (fun d hd => (and_iff_right hd).trans (hinterval d hd).symm) E hEnds hH
  have hrot (d : Dart G) : s.rotate (e d) = e ((r.rotate * swap b c) d) := by
    rw [hrotate, permCongr_apply, symm_apply_apply]
  have hb : (e b).vertex = w := by rw [hend, ite_eq_left ⟨hab.symm, le_rfl⟩]
  have hnext : (e (r.rotate b)).vertex = a.vertex := by
    rw [hend, ite_eq_right hnextOutside, r.vertex_rotate, hab]
  have hc : (e c).vertex = a.vertex := by
    have h := s.vertex_rotate (e c)
    rw [hrot, Perm.mul_apply, swap_apply_right, hnext] at h
    exact h.symm
  refine ⟨hsep, fun hz => s.numericalGenusZero_of_join_swap r hH hG hz (e b) (e c)
    (by rwa [hb, hc]) e.symm (fun _ => rfl) ?_⟩
  intro d
  obtain ⟨d, rfl⟩ := e.surjective d
  rw [Perm.mul_apply, e.injective.swap_apply, hrot, Perm.mul_apply, swap_apply_self,
    symm_apply_apply, symm_apply_apply]

end RotationSystem
end Cslib.Complexity.Graph
