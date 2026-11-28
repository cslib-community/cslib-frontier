/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import CslibFrontier.Foundations.GroupTheory.Perm.SelectedOrbits
import CslibFrontier.Foundations.GroupTheory.Perm.InvariantPredicate
import CslibFrontier.Foundations.GroupTheory.Perm.ListSplice
import Mathlib.GroupTheory.Perm.Cycle.Factors

/-! Ordinary permutation-surgery clients, with no graph import in their transitive closure. -/

open Equiv Perm.SelectedOrbits

-- The swapped elements are distinct and both satisfy a genuinely nonconstant predicate.
example (x : Fin 4) : (Equiv.swap (0 : Fin 4) 1 x).val < 2 ↔ x.val < 2 :=
  Equiv.predicate_swap (fun x : Fin 4 => x.val < 2) 0 1 (by decide) x

example : Equiv.swap (0 : Fin 4) 1 0 = 1 ∧ ¬ (2 : Fin 4).val < 2 := by decide

example : Nat.card (OrbitOn (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 0 1)
      (fun x : Fin 4 => x.val < 2)) =
    Nat.card (OrbitOn (Equiv.swap (0 : Fin 4) 1) (fun x : Fin 4 => x.val < 2)) + 1 := by
  simpa using card_orbitOn_swap_mul (Equiv.swap (0 : Fin 4) 1) (fun x => x.val < 2)
    (by decide +kernel) 0 1 (by decide) (by decide +kernel)

example : Equiv.Perm.Insertion.insertAfter (Equiv.refl (Fin 1)) 0 none = some 0 := by decide

-- The two cuts give opposite block orders after erasing marker 3.
example : ([0, 1, 2, 4, 5] : List (Fin 6)).formPerm 2 = 4 ∧
    ([0, 4, 5, 1, 2] : List (Fin 6)).formPerm 5 = 1 := by
  exact ⟨(List.formPerm_join_skip_marker_iff [1, 2] [4, 5] (0 : Fin 6) 3 2 4
      (by decide) (by decide) (by decide)).1.mpr (Or.inr ⟨by decide, by decide⟩),
    (List.formPerm_join_skip_marker_iff [1, 2] [4, 5] (0 : Fin 6) 3 5 1
      (by decide) (by decide) (by decide)).2.mpr (Or.inr ⟨by decide, by decide⟩)⟩

-- A singleton second cycle contributes an empty block in either order.
example : ([0, 1, 2] : List (Fin 4)).formPerm 2 = 0 :=
  (List.formPerm_join_skip_marker_iff [1, 2] [] (0 : Fin 4) 3 2 0
    (by decide) (by decide) (by decide)).1.mpr (Or.inr ⟨by decide, by decide⟩)

open Lean Elab Command in
run_cmd do
  let graphPrefix := `CslibFrontier.Computability.Complexity.Problems.Graph
  for name in (← getEnv).header.moduleNames do
    if graphPrefix.isPrefixOf name then
      throwError "generic permutation client unexpectedly imports graph module {name}"
