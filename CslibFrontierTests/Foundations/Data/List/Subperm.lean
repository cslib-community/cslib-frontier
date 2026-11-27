/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.Data.List.Subperm
public import Mathlib.Data.List.Forall2

/-! Tests for generic `List.Subperm` structural lemmas. -/

public section

namespace CslibFrontierTests.ListSubperm

open List

-- Empty-list edge cases.
example : ∃ zs : List ℕ, zs <+~ ([] : List ℕ) ∧ zs.map (· * 2) = [] :=
  Subperm.exists_map (xs := []) (l := []) nil_subperm

example : ([] : List ℕ) ++ ([] : List ℕ) <+~ [1, 2] :=
  Subperm.append_of_disjoint nil_subperm nil_subperm (fun _ h => by simp at h)

example : ([[], []] : List (List ℕ)).flatten <+~ [1] :=
  Subperm.flatten_of_pairwise_disjoint
    (by
      unfold List.Disjoint
      simp [pairwise_cons])
    fun l hl => by
      simp only [mem_cons, not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> exact nil_subperm

-- Duplicate handling and both directions of `cons_subperm_iff_subperm_erase`.
example : 1 ∈ ([2, 1, 2, 1] : List ℕ) ∧ [1] <+~ ([2, 1, 2, 1] : List ℕ).erase 1 :=
  cons_subperm_iff_subperm_erase.mp (by decide : [1, 1] <+~ [2, 1, 2, 1])

example : [1, 1] <+~ ([2, 1, 2, 1] : List ℕ) :=
  cons_subperm_iff_subperm_erase.mpr ⟨by decide, by decide⟩

example : ¬ ([1, 1] <+~ ([2, 1, 2] : List ℕ)) := by
  rw [cons_subperm_iff_subperm_erase]
  decide

example : [1, 1] ++ [2, 2] <+~ ([2, 1, 2, 1] : List ℕ) :=
  Subperm.append_of_disjoint (by decide) (by decide) fun _ h₁ h₂ => by
    simp only [mem_cons, not_mem_nil, or_false] at h₁ h₂
    omega

example : ([[1, 1], [], [2, 2], [3]] : List (List ℕ)).flatten <+~ [3, 2, 1, 2, 1] := by
  refine Subperm.flatten_of_pairwise_disjoint ?_ ?_
  · unfold List.Disjoint
    simp [pairwise_cons]
  · intro l hl
    simp only [mem_cons, not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;> decide

-- Non-injective mapping and preimage lifting.
example : ([1, 2] : List ℕ).map (· % 2) <+~ ([4, 1, 3, 2] : List ℕ).map (· % 2) :=
  subperm_map (· % 2) (by decide : [1, 2] <+~ [4, 1, 3, 2])

example : ∃ zs : List ℕ, zs <+~ [2, 3, 4] ∧ zs.map (· % 2) = [0, 1] :=
  Subperm.exists_map (by decide : [0, 1] <+~ ([2, 3, 4] : List ℕ).map (· % 2))

-- `Nodup` preservation and `Forall₂` flatten (direct and via `List.forall₂_of_length_eq_of_get`).
example : ([1, 3] : List ℕ).Nodup :=
  Subperm.nodup (by decide : [1, 3] <+~ [3, 2, 1]) (by decide)

example : ([[2], [3, 4]] : List (List ℕ)).flatten <+~ [[1, 2], [4, 5, 3]].flatten :=
  Subperm.flatten_of_forall₂ (.cons (by decide) (.cons (by decide) .nil))

example : ([[2], [3, 4]] : List (List ℕ)).flatten <+~ [[1, 2], [4, 5, 3]].flatten := by
  refine Subperm.flatten_of_forall₂ (forall₂_of_length_eq_of_get rfl fun i h₁ h₂ => ?_)
  match i, h₁, h₂ with
  | 0, _, _ => exact (by decide : [2] <+~ [1, 2])
  | 1, _, _ => exact (by decide : [3, 4] <+~ [4, 5, 3])

end CslibFrontierTests.ListSubperm
