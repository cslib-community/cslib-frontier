/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.AndOr

/-!
# Explicit local boundary lists

Local source ports are listed by inputs followed by outputs. This gives a direct list form of
the dependent finite boundary map, for portable natural-coordinate emission.

## Main definitions

* `SelectorNetwork.AndOr.boundaryList`: shared names in local boundary-reference order.

## Main results

* `SelectorNetwork.AndOr.ofFn_map_port`: agreement with the actual finite boundary map.
-/

public section

namespace Cslib.Complexity.NCL.SelectorNetwork.AndOr

variable {U C R : Type*} [DecidableEq U] [DecidableEq C]
variable (N : SelectorNetwork U C R) (A : RowSection N)

/-- Shared names in top-then-bottom boundary-reference order. -/
@[expose] def boundaryList : Vert U C R → List (Edge C R)
  | .inl u => (rowInputs N A u).map Sum.inl ++ [.inl (A.character u)]
  | .inr (.inl c) => (N.incident c).map Sum.inr ++ [.inl c]
  | .inr (.inr r) => [.inr (r, false), .inr (r, true)]

private theorem ofFn_get_cast {α β : Type*} (xs : List α) {n : ℕ} (h : n = xs.length)
    (f : α → β) : List.ofFn (fun i : Fin n => f (xs.get (i.cast h))) = xs.map f := by
  subst n
  simpa only [Fin.cast_refl, id_eq] using
    (List.ofFn_comp' xs.get f).trans (congrArg (List.map f) (List.ofFn_get xs))

/-- The explicit boundary list is exactly the actual dependent boundary map's enumeration. -/
private theorem ofFn_port (v : Vert U C R) :
    List.ofFn (fun i : Fin ((cell N A v).top.length + (cell N A v).bottom.length) =>
      port N A v (finSumFinEquiv.symm i)) = boundaryList N A v := by
  rcases v with u | (c | r)
  · rw [List.ofFn_add]
    have hcast (i : Fin (cell N A (.inl u)).top.length) :
        i.castLE (Nat.le_add_right _ _) = i.castAdd (cell N A (.inl u)).bottom.length := rfl
    simp only [hcast, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, port, ofFn_get_cast]
    rfl
  · rw [List.ofFn_add]
    have hcast (i : Fin (cell N A (.inr (.inl c))).top.length) :
        i.castLE (Nat.le_add_right _ _) =
          i.castAdd (cell N A (.inr (.inl c))).bottom.length := rfl
    simp only [hcast, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, port, ofFn_get_cast]
    rfl
  · rfl

/-- Applying a shared-wire interpretation to the finite boundary map gives the same list. -/
theorem ofFn_map_port {α : Type*} (f : Edge C R → α) (v : Vert U C R) :
    List.ofFn (fun i : Fin ((cell N A v).top.length + (cell N A v).bottom.length) =>
      f (port N A v (finSumFinEquiv.symm i))) = (boundaryList N A v).map f := by
  simpa only [List.map_ofFn, Function.comp_def] using
    congrArg (List.map f) (ofFn_port N A v)

end Cslib.Complexity.NCL.SelectorNetwork.AndOr
