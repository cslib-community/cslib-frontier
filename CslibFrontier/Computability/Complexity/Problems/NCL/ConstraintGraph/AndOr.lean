/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Basic
import Mathlib.Data.List.Permutation

/-!
# Checking the AND/OR vertex shapes

Check minimum inflow and the three port weights directly. The edge names and directions are
retained as witnesses for `Vertex.IsAndOr`. Mapping edge names preserves the property.

## Main definitions

* `Cslib.Complexity.NCL.Vertex.checkAndOr`: the four accepted port-weight orders.

## Main results

* `Cslib.Complexity.NCL.Vertex.checkAndOr_eq_true_iff`: every permitted permutation is accepted.
* `Cslib.Complexity.NCL.Vertex.IsAndOr.map`: renaming edges preserves the vertex kind.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Vertex

variable {E E' : Type*}

/-- A standard AND/OR vertex has three ports and minimum inflow two. -/
theorem IsAndOr.shape {v : Vertex E} (h : v.IsAndOr) :
    v.ports.length = 3 ∧ v.minInflow = 2 := by
  rcases h with ⟨a, b, c, hm, hp⟩ | ⟨a, b, c, hm, hp⟩
  all_goals exact ⟨hp.length_eq, hm⟩

/-- Check the minimum inflow and port weights of an AND or OR vertex. -/
@[expose] def checkAndOr (v : Vertex E) : Bool :=
  v.minInflow == 2 &&
    ([[1, 1, 2], [1, 2, 1], [2, 1, 1], [2, 2, 2]] : List (List ℕ)).contains
      (v.ports.map WeightedPort.weight)

private theorem ports_of_map_weights {ps : List (WeightedPort E)} {x y z : ℕ}
    (h : ps.map WeightedPort.weight = [x, y, z]) : ∃ a b c, ps = [⟨a, x⟩, ⟨b, y⟩, ⟨c, z⟩] := by
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at h
  rcases h with ⟨⟨a, _⟩, _, rfl, rfl, ⟨⟨b, _⟩, _, rfl, rfl,
    ⟨⟨c, _⟩, _, rfl, rfl, rfl⟩⟩⟩
  exact ⟨a, b, c, rfl⟩

private theorem isAndOr_of_check {v : Vertex E} (h : v.checkAndOr = true) : v.IsAndOr := by
  simp only [checkAndOr, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, List.mem_cons,
    List.not_mem_nil, or_false] at h
  rcases h with ⟨hm, hp | hp | hp | hp⟩
  all_goals obtain ⟨a, b, c, hp⟩ := ports_of_map_weights hp
  · exact .inl ⟨a, b, c, hm, hp ▸ List.Perm.refl _⟩
  · exact .inl ⟨a, c, b, hm, hp ▸ List.Perm.cons _ (List.Perm.swap _ _ [])⟩
  · exact .inl ⟨b, c, a, hm, hp ▸
      (List.Perm.swap _ _ [_]).trans (List.Perm.cons _ (List.Perm.swap _ _ []))⟩
  · exact .inr ⟨a, b, c, hm, hp ▸ List.Perm.refl _⟩

private theorem check_of_isAndOr {v : Vertex E} (h : v.IsAndOr) : v.checkAndOr = true := by
  have hperm : ∀ x y z : WeightedPort E, [x, y, z].permutations =
      [[x, y, z], [y, x, z], [z, y, x], [y, z, x], [z, x, y], [x, z, y]] := by
    intro x y z
    cbv
  rcases h with ⟨a, b, c, hm, hp⟩ | ⟨a, b, c, hm, hp⟩
  all_goals
    have hh := List.mem_permutations.2 hp
    simp only [and, or] at hh
    rw [hperm] at hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with hh | hh | hh | hh | hh | hh <;> simp [checkAndOr, hh, hm]

/-- The shape checker recognizes all port permutations of AND and OR vertices. -/
theorem checkAndOr_eq_true_iff (v : Vertex E) : v.checkAndOr = true ↔ v.IsAndOr :=
  ⟨isAndOr_of_check, check_of_isAndOr⟩

/-- Edge renaming leaves the shape check unchanged. -/
theorem checkAndOr_map (v : Vertex E) (f : E → E') :
    (v.map f).checkAndOr = v.checkAndOr := by
  simp only [checkAndOr, Vertex.map, List.map_map]
  rfl

/-- Renaming edges preserves the kind of an AND/OR vertex. -/
theorem IsAndOr.map {v : Vertex E} (h : v.IsAndOr) (f : E → E') : (v.map f).IsAndOr := by
  rcases h with ⟨a, b, c, hm, hp⟩ | ⟨a, b, c, hm, hp⟩
  · exact .inl ⟨a.map f, b.map f, c.map f, hm,
      hp.map (WeightedPort.map f)⟩
  · exact .inr ⟨a.map f, b.map f, c.map f, hm,
      hp.map (WeightedPort.map f)⟩

end Cslib.Complexity.NCL.Vertex
