/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntervalOrder
import CslibFrontier.Foundations.GroupTheory.Perm.CycleSurgery
import Mathlib.Data.List.GetD

/-!
# Cutting an interval out of a vertex rotation

Swapping the outgoing successors at the end of a proper interval and before its beginning
closes the interval and its complement into separate cycles. The orbit relation remembers
the original vertex and which side of the interval each dart lies on.

## Main results

* `Cslib.Complexity.Graph.RotationSystem.sameCycle_swap_cutInterval_iff` identifies those orbits.
* `Cslib.Complexity.Graph.RotationSystem.exists_split_cutInterval` realizes the swap as a rotation
  system on the graph with the selected ends moved to the new vertex label.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv

variable {G : Graph} (r : RotationSystem G)

/-- The outgoing swap at the last dart of a proper directed interval and at the predecessor
of its first dart preserves the original vertex fibers and divides the selected fiber into
exactly two orbits, the inclusive interval and its complement. -/
theorem sameCycle_swap_cutInterval_iff (a b : Dart G) (hab : a.vertex = b.vertex)
    (hproper : r.rotate b ≠ a) (d e : Dart G) :
    (r.rotate * swap b (r.rotate.symm a)).SameCycle d e ↔ d.vertex = e.vertex ∧
      ((d.vertex = a.vertex ∧ r.rotationDistance a d ≤ r.rotationDistance a b) ↔
        (e.vertex = a.vertex ∧ r.rotationDistance a e ≤ r.rotationDistance a b)) := by
  let c := r.rotate.symm a
  let selected (x : Dart G) := x.vertex = a.vertex ∧
    r.rotationDistance a x ≤ r.rotationDistance a b
  have hca : r.rotate c = a := r.rotate.apply_symm_apply a
  have hc : a.vertex = c.vertex := hca ▸ r.vertex_rotate c
  have hnext := r.rotationDistance_rotate_of_ne a b hab hproper
  have hnextVertex : a.vertex = (r.rotate b).vertex := hab.trans (r.vertex_rotate b).symm
  have hlast := r.rotationDistance_of_rotate_eq a c hc hca
  have hperiod := r.rotationDistance_lt_period hnextVertex
  have hb : selected b := ⟨hab.symm, le_rfl⟩
  have hcOut : ¬ selected c := by
    rintro ⟨_, h⟩
    omega
  have hnextOut : ¬ selected (r.rotate b) := by
    rintro ⟨_, h⟩
    omega
  have hstable (x : Dart G) : selected ((r.rotate * swap b c) x) ↔ selected x := by
    by_cases hxb : x = b
    · subst x
      rw [Perm.mul_apply, swap_apply_left, hca]
      exact iff_of_true ⟨rfl, by rw [r.rotationDistance_self]; omega⟩ hb
    by_cases hxc : x = c
    · subst x
      rw [Perm.mul_apply, swap_apply_right]
      exact iff_of_false hnextOut hcOut
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxb hxc]
    by_cases hv : x.vertex = a.vertex
    · have hxnext : r.rotate x ≠ a := fun h => hxc (r.rotate.injective (h.trans hca.symm))
      have hdist := r.rotationDistance_rotate_of_ne a x hv.symm hxnext
      have hdiff : r.rotationDistance a x ≠ r.rotationDistance a b := by
        intro h
        exact hxb ((r.pow_rotationDistance a x hv.symm).symm.trans
          (h ▸ r.pow_rotationDistance a b hab))
      simp only [selected, r.vertex_rotate, hv, true_and, hdist]
      omega
    · simp [selected, hv, r.vertex_rotate]
  change (r.rotate * swap b c).SameCycle d e ↔ d.vertex = e.vertex ∧ (selected d ↔ selected e)
  rw [Perm.CycleSurgery.sameCycle_mul_swap_iff_of_separating
    ((r.sameCycle_iff b c).mpr (hab.symm.trans hc)) selected hb hcOut hstable,
    r.sameCycle_iff]

/-- Move a proper directed interval to a vertex label distinct from all original incident
vertices. The split retains every edge occurrence and end tag, and its rotation in these
coordinates is the literal outgoing swap at the two ends of the cut. -/
theorem exists_split_cutInterval (a b : Dart G) (hab : a.vertex = b.vertex)
    (hproper : r.rotate b ≠ a) (w : ℕ) (hfresh : ∀ d : Dart G, d.vertex ≠ w) :
    ∃ (H : Graph) (E : Fin G.edges.length ≃ Fin H.edges.length) (s : RotationSystem H),
      H.vertices = w :: G.vertices ∧
      (∀ d : Dart G, Dart.vertex (G := H) (E d.1, d.2) =
        if d.vertex = a.vertex ∧ r.rotationDistance a d ≤ r.rotationDistance a b
        then w else d.vertex) ∧
      s.rotate = (Equiv.prodCongr E (Equiv.refl Bool)).permCongr
        (r.rotate * swap b (r.rotate.symm a)) := by
  classical
  let selected (d : Dart G) := d.vertex = a.vertex ∧
    r.rotationDistance a d ≤ r.rotationDistance a b
  let endpoint (d : Dart G) := if selected d then w else d.vertex
  let H : Graph := ⟨w :: G.vertices,
    List.ofFn fun i : Fin G.edges.length => (endpoint (i, false), endpoint (i, true))⟩
  have hlen : H.edges.length = G.edges.length := List.length_ofFn
  let E : Fin G.edges.length ≃ Fin H.edges.length := finCongr hlen.symm
  let D : Dart G ≃ Dart H := Equiv.prodCongr E (Equiv.refl Bool)
  have hvertex (d : Dart G) : (D d).vertex = endpoint d := by
    rcases d with ⟨i, b⟩
    have hi : i.val < H.edges.length := hlen.symm ▸ i.isLt
    change (if b then (H.edges.getD i.val (0, 0)).2 else (H.edges.getD i.val (0, 0)).1) = _
    rw [List.getD_eq_getElem _ _ hi]
    change (if b then ((List.ofFn fun j => (endpoint (j, false), endpoint (j, true)))[i.val]).2
      else ((List.ofFn fun j => (endpoint (j, false), endpoint (j, true)))[i.val]).1) = _
    rw [List.getElem_ofFn]
    cases b <;> rfl
  let f := r.rotate * swap b (r.rotate.symm a)
  let s : RotationSystem H :=
    { rotate := D.permCongr f
      sameCycle_iff := by
        intro d e
        obtain ⟨d, rfl⟩ := D.surjective d
        obtain ⟨e, rfl⟩ := D.surjective e
        rw [Perm.sameCycle_equiv_iff D f _ (fun x => by
          rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]),
          r.sameCycle_swap_cutInterval_iff a b hab hproper, hvertex, hvertex]
        change d.vertex = e.vertex ∧ (selected d ↔ selected e) ↔
          (if selected d then w else d.vertex) = (if selected e then w else e.vertex)
        by_cases hd : selected d <;> by_cases he : selected e
        · simp [hd, he, hd.1.trans he.1.symm]
        · simp [hd, he, Ne.symm (hfresh e)]
        · simp [hd, he, hfresh d]
        · simp [hd, he] }
  exact ⟨H, E, s, rfl, hvertex, rfl⟩

end Cslib.Complexity.Graph.RotationSystem
