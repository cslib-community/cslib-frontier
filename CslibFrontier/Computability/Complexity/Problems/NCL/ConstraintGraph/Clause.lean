/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.Group.Nat

/-!
# Disjunctive inflow constraints

## Main results

* `Vertex.sat_clause_iff`: a unit-weight clause requires at least one inward port.
* `Vertex.sat_one_iff`: minimum inflow one requires an inward port of positive weight.
-/

public section

namespace Cslib.Complexity.NCL.Vertex

/-- Inflow one is supplied exactly when an inward port has positive weight. -/
theorem sat_one_iff {E : Type*} (ps : List (WeightedPort E)) (s : E → Bool) :
    (⟨ps, 1⟩ : Vertex E).Sat s ↔ ∃ p ∈ ps, p.port.In s ∧ 0 < p.weight := by
  constructor
  · intro hs
    change 1 ≤ (ps.map fun p => if p.port.In s then p.weight else 0).sum at hs
    obtain ⟨_, hx, hpos⟩ := List.exists_mem_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hs)
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hi, hpos⟩ := ite_ne_right_iff.mp hpos
    exact ⟨p, hp, hi, Nat.pos_of_ne_zero hpos⟩
  · rintro ⟨p, hp, hi, hpos⟩
    change 1 ≤ (ps.map fun p => if p.port.In s then p.weight else 0).sum
    exact (Nat.succ_le_iff.mpr hpos).trans
      (List.le_sum_of_mem (List.mem_map.mpr ⟨p, hp, ite_eq_left hi⟩))

/-- A clause is satisfied exactly when one of its ports points in. -/
theorem sat_clause_iff {E : Type*} (ps : List (Port E)) (s : E → Bool) :
    (clause ps).Sat s ↔ ∃ p ∈ ps, p.In s := by
  induction ps with
  | nil => simp [clause, Sat, inflow]
  | cons p ps ih =>
    by_cases hp : p.In s
    · exact ⟨fun _ => ⟨p, List.mem_cons_self, hp⟩, fun _ => sat_clause List.mem_cons_self hp⟩
    · simpa [clause, Sat, inflow, hp] using ih

end Cslib.Complexity.NCL.Vertex
