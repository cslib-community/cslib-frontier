/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Endpoints
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Clause
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Simulation
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Prod

/-!
# Weighted networks implementing nonempty compatible selections

Each character belongs to one row. A relation joins two characters and, when required, forbids
selecting both. A selector edge supplies its character vertex whenever that character is absent;
selecting it forces every incident unit-weight relation edge to point towards the character.

## Main definitions

* `SelectorNetwork`: row assignment, relation endpoints, and explicit finite enumerations.
* `SelectorNetwork.graph`: the finite weighted port graph.

## Main results

* `SelectorNetwork.wellFormed`: the network has one equally weighted port per edge direction.

## References

* The character and relation mechanism follows [VanDerZanden2015, Theorem 6].
-/

public section

namespace Cslib.Complexity.NCL

/-- Explicit finite row and binary-exclusion data for a selector network. -/
structure SelectorNetwork (U C R : Type*) where
  /-- The row containing a character. -/
  row : C → U
  /-- The two characters joined by a relation. -/
  endpoint : R → Bool → C
  /-- Whether the relation forbids simultaneous selection. -/
  required : R → Bool
  /-- A concrete enumeration of the characters. -/
  characters : List C
  /-- Each character occurs once. -/
  characters_nodup : characters.Nodup
  /-- Every character is enumerated. -/
  characters_complete : ∀ c, c ∈ characters
  /-- A concrete enumeration of the relations. -/
  relations : List R
  /-- Each relation occurs once. -/
  relations_nodup : relations.Nodup
  /-- Every relation is enumerated. -/
  relations_complete : ∀ r, r ∈ relations

namespace SelectorNetwork

/-- Character selector edges and the two unit edges of each relation. -/
abbrev Edge (C R : Type*) := C ⊕ (R × Bool)

/-- Row, character, and relation vertices. -/
abbrev Vert (U C R : Type*) := U ⊕ C ⊕ R

variable {U C R : Type*} (N : SelectorNetwork U C R)

/-- The two unit-weight edges adjacent to each relation. -/
@[expose] def branches : List (R × Bool) := N.relations.product [false, true]

/-- The incident unit edges of a character. -/
@[expose] def incident [DecidableEq C] (c : C) : List (R × Bool) :=
  N.branches.filter fun e => decide (N.endpoint e.1 e.2 = c)

/-- A selector supplies strictly more than its character's entire unit-edge demand. -/
@[expose] def selectorWeight [DecidableEq C] (c : C) : ℕ := (N.incident c).length + 1

/-- Every selector, followed by every unit edge, in the supplied enumeration orders. -/
@[expose] def edges : List (Edge C R) :=
  N.characters.map Sum.inl ++ N.branches.map Sum.inr

/-- A selector joins its row and character; unit edges join characters and relations. -/
@[expose] def endpoints [DecidableEq C] : EndpointGraph (Vert U C R) (Edge C R) where
  endpoint
    | .inl c, false => .inr (.inl c)
    | .inl c, true => .inl (N.row c)
    | .inr e, false => .inr (.inr e.1)
    | .inr e, true => .inr (.inl (N.endpoint e.1 e.2))
  weight
    | .inl c => N.selectorWeight c
    | .inr _ => 1
  demand
    | .inl _ => 1
    | .inr (.inl c) => (N.incident c).length
    | .inr (.inr r) => if N.required r then 1 else 0

/-- The concrete weighted graph generated from the network's endpoints. -/
@[expose] def graph [DecidableEq U] [DecidableEq C] [DecidableEq R] :
    ConstraintGraph (Vert U C R) (Edge C R) :=
  N.endpoints.graph N.edges

/-- Every relation-side pair appears exactly once. -/
theorem branches_nodup : N.branches.Nodup := by
  exact N.relations_nodup.product (by decide +kernel)

/-- Every selector and unit edge is listed exactly once. -/
theorem edges_nodup : N.edges.Nodup := by
  apply List.nodup_append.mpr
  refine ⟨N.characters_nodup.map Sum.inl_injective,
    (branches_nodup N).map Sum.inr_injective, ?_⟩
  intro e he f hf hef
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp he
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hf
  cases hef

/-- Every selector and relation edge occurs in the explicit enumeration. -/
theorem mem_edges (e : Edge C R) : e ∈ N.edges := by
  rcases e with c | ⟨r, b⟩
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨c, N.characters_complete c, rfl⟩)
  · apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨(r, b), ?_, rfl⟩
    cases b <;> simp [branches, N.relations_complete r]

/-- Every network edge has exactly two opposite ports carrying its declared weight. -/
theorem wellFormed [Fintype U] [Fintype C] [Fintype R]
    [DecidableEq U] [DecidableEq C] [DecidableEq R] : N.graph.WellFormed :=
  N.endpoints.wellFormed N.edges (edges_nodup N) (mem_edges N)

end SelectorNetwork
end Cslib.Complexity.NCL
