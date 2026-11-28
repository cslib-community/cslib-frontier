/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Orthogonal.Simple
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Zip

/-!
# Orientation independence of orthogonal incidence routes

Reversing a route preserves its full real support, proper orthogonality, continuous simplicity,
Manhattan wire length, and segment count. This normalizes supplied incidence routes without
changing their drawing.

## Main results

* `support_reverse`, `isOrthogonal_reverse_iff`, `isSimple_reverse_iff`.
* `wireLength_reverse`, `consecutivePairs_length_reverse`.

## References

These finite-route reversal lemmas and proofs are original.
-/

public section

namespace Cslib.Orthogonal


private theorem consecutivePairs_append_singleton (r : Route) (a : Point) :
    (r ++ [a]).consecutivePairs =
      r.consecutivePairs ++ r.getLast?.toList.map (fun b => (b, a)) := by
  induction r with
  | nil => rfl
  | cons b r ih =>
    cases r with
    | nil => rfl
    | cons c r =>
      simp only [List.cons_append, List.consecutivePairs, List.tail_cons,
        List.zip_cons_cons, List.getLast?_cons_cons, List.cons_append] at ih ⊢
      exact congrArg ((b, c) :: ·) ih

/-- Reversal reverses segment order and swaps each segment's endpoints. -/
theorem consecutivePairs_reverse (r : Route) :
    r.reverse.consecutivePairs = r.consecutivePairs.reverse.map Prod.swap := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b r =>
      rw [List.reverse_cons, consecutivePairs_append_singleton, ih]
      simp [List.consecutivePairs, List.getLast?_reverse]

/-- Reversal preserves the number of listed segments. -/
theorem consecutivePairs_length_reverse (r : Route) :
    r.reverse.consecutivePairs.length = r.consecutivePairs.length := by
  rw [consecutivePairs_reverse, List.length_map, List.length_reverse]

/-- Reversal preserves the entire continuous support. -/
theorem support_reverse (r : Route) : support r.reverse = support r := by
  ext p
  simp only [support, Set.mem_ofPred_eq, consecutivePairs_reverse, List.mem_reverse,
    List.mem_map, exists_exists_and_eq_and, Prod.swap]
  exact or_congr_right (exists_congr fun e => and_congr_right fun _ => by
    change p ∈ _root_.segment ℝ _ _ ↔ p ∈ _root_.segment ℝ _ _
    rw [_root_.segment_symm])

private theorem axisAligned_swap_iff (a b : Point) : AxisAligned b a ↔ AxisAligned a b := by
  simp [AxisAligned, eq_comm]

/-- Reversal preserves proper orthogonality. -/
theorem isOrthogonal_reverse_iff (r : Route) : IsOrthogonal r.reverse ↔ IsOrthogonal r := by
  simp only [IsOrthogonal, consecutivePairs_reverse, List.mem_map, List.mem_reverse,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Prod.swap, axisAligned_swap_iff]

private theorem isSimple_reverse {r : Route} (h : IsSimple r) : IsSimple r.reverse := by
  refine ⟨by simpa only [List.nodup_reverse] using h.1, fun e he f hf hne => ?_⟩
  simp only [consecutivePairs_reverse, List.mem_map, List.mem_reverse] at he hf
  obtain ⟨e, he, rfl⟩ := he
  obtain ⟨f, hf, rfl⟩ := hf
  exact (h.2 e he f hf fun heq => hne (congrArg Prod.swap heq)).reverse_left.reverse_right

/-- Reversal preserves continuous simplicity. -/
theorem isSimple_reverse_iff (r : Route) : IsSimple r.reverse ↔ IsSimple r :=
  ⟨fun h => by simpa only [List.reverse_reverse] using isSimple_reverse h, isSimple_reverse⟩

private theorem length_swap (a b : Point) : length b a = length a b := by
  unfold length
  rw [← Int.natAbs_neg (a.1 - b.1), ← Int.natAbs_neg (a.2 - b.2), neg_sub, neg_sub]

/-- Reversal preserves total Manhattan wire length. -/
theorem wireLength_reverse (r : Route) : wireLength r.reverse = wireLength r := by
  simp only [wireLength, consecutivePairs_reverse, List.map_map, Function.comp_def,
    Prod.swap, length_swap, List.map_reverse, List.sum_reverse]

end Cslib.Orthogonal
