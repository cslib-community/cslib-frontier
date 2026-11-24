/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat

/-!
# Legality of weighted selector networks

## Main definitions

* `SelectorNetwork.TargetLegal`: nonempty rows, the character demands, and binary exclusions.

## Main results

* `SelectorNetwork.legal_iff`: these local conditions exactly characterize the weighted graph.
-/

public section

namespace Cslib.Complexity.NCL.SelectorNetwork

variable {U C R : Type*} [DecidableEq U] [DecidableEq C] [DecidableEq R]
  (N : SelectorNetwork U C R)

/-- The row, character, and relation conditions on a physical network orientation. -/
structure TargetLegal (s : Edge C R → Bool) : Prop where
  /-- At least one character is selected in each row. -/
  nonempty : ∀ u, ∃ c, N.row c = u ∧ s (.inl c) = true
  /-- A selected character receives all its incident unit edges. -/
  forced : ∀ r b, s (.inl (N.endpoint r b)) = true → s (.inr (r, b)) = true
  /-- A required relation receives at least one unit edge. -/
  relation : ∀ r, N.required r = true →
    s (.inr (r, false)) = false ∨ s (.inr (r, true)) = false

/-- A row receives a selected character. -/
theorem sat_row_iff (s : Edge C R → Bool) (u : U) :
    (N.graph (.inl u)).Sat s ↔ ∃ c, N.row c = u ∧ s (.inl c) = true := by
  change (⟨(N.graph (.inl u)).ports, 1⟩ : Vertex (Edge C R)).Sat s ↔ _
  rw [Vertex.sat_one_iff]
  constructor
  · rintro ⟨⟨⟨e, d⟩, w⟩, hp, hi, _⟩
    have he := ((N.endpoints.mem_ports N.edges (.inl u) ⟨e, d⟩ w).mp hp).2.2
    rcases e with c | ⟨r, b⟩ <;> cases d
    · cases he
    · exact ⟨c, Sum.inl.inj he, hi⟩
    · cases he
    · cases he
  · rintro ⟨c, hc, hs⟩
    refine ⟨⟨⟨.inl c, true⟩, N.selectorWeight c⟩, ?_, hs, ?_⟩
    · exact (N.endpoints.mem_ports _ _ _ _).mpr ⟨N.mem_edges _, rfl,
        by simp [endpoints, hc]⟩
    · exact Nat.zero_lt_succ _

/-- A required relation receives at least one of its two branches. -/
theorem sat_relation_iff (s : Edge C R → Bool) (r : R) :
    (N.graph (.inr (.inr r))).Sat s ↔
      N.required r = true →
        s (.inr (r, false)) = false ∨ s (.inr (r, true)) = false := by
  change (if N.required r then 1 else 0) ≤
    (N.graph (.inr (.inr r))).inflow s ↔ _
  cases hreq : N.required r with
  | false => simp
  | true =>
    change (⟨(N.graph (.inr (.inr r))).ports, 1⟩ : Vertex (Edge C R)).Sat s ↔ _
    rw [Vertex.sat_one_iff]
    simp only [true_implies]
    constructor
    · rintro ⟨⟨⟨e, d⟩, w⟩, hp, hi, _⟩
      have he := ((N.endpoints.mem_ports N.edges (.inr (.inr r)) ⟨e, d⟩ w).mp hp).2.2
      rcases e with c | ⟨r', b⟩ <;> cases d
      · cases he
      · cases he
      · have hr : r' = r := Sum.inr.inj (Sum.inr.inj he)
        subst r'
        cases b
        · exact Or.inl hi
        · exact Or.inr hi
      · cases he
    · intro hs
      rcases hs with hs | hs
      · exact ⟨⟨⟨.inr (r, false), false⟩, 1⟩,
          (N.endpoints.mem_ports _ _ _ _).mpr ⟨N.mem_edges _, rfl, rfl⟩, hs, Nat.zero_lt_one⟩
      · exact ⟨⟨⟨.inr (r, true), false⟩, 1⟩,
          (N.endpoints.mem_ports _ _ _ _).mpr ⟨N.mem_edges _, rfl, rfl⟩, hs, Nat.zero_lt_one⟩

private theorem sum_flags {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map fun x => if f x then 1 else 0).sum = xs.countP f := by
  rw [List.sum_map_ite]
  simp [List.countP_eq_length_filter]

private theorem inflow_character (s : Edge C R → Bool) (c : C) :
    (N.graph (.inr (.inl c))).inflow s =
      (if s (.inl c) = false then N.selectorWeight c else 0) +
        (N.incident c).countP (fun e => s (.inr e)) := by
  change (N.endpoints.graph N.edges _).inflow s = _
  rw [EndpointGraph.inflow]
  simp only [edges, List.map_append, List.sum_append, List.map_map, Function.comp_def]
  have hsel (d : C) :
      (if N.endpoints.endpoint (.inl d) (s (.inl d)) = .inr (.inl c) then
        N.endpoints.weight (.inl d) else 0) =
      if d = c then (if s (.inl c) = false then N.selectorWeight c else 0) else 0 := by
    by_cases hd : d = c
    · subst d
      cases s (.inl c) <;> simp [endpoints]
    · cases s (.inl d) <;> simp [endpoints, hd]
  have hbranch (e : R × Bool) :
      (if N.endpoints.endpoint (.inr e) (s (.inr e)) = .inr (.inl c) then
        N.endpoints.weight (.inr e) else 0) =
      if N.endpoint e.1 e.2 = c then (if s (.inr e) then 1 else 0) else 0 := by
    cases s (.inr e) <;> simp [endpoints]
  simp_rw [hsel, hbranch]
  have hc : N.characters.filter (fun d => decide (d = c)) = [c] := by
    rw [List.filter_eq, List.count_eq_one_of_mem N.characters_nodup (N.characters_complete c)]
    rfl
  have hsc : (N.characters.map fun d => if d = c then
      (if s (.inl c) = false then N.selectorWeight c else 0) else 0).sum =
      if s (.inl c) = false then N.selectorWeight c else 0 := by
    rw [List.sum_map_ite]
    simp [hc]
  have hbr : (N.branches.map fun e => if N.endpoint e.1 e.2 = c then
      (if s (.inr e) then 1 else 0) else 0).sum =
      (N.incident c).countP (fun e => s (.inr e)) := by
    rw [List.sum_map_ite]
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_zero, add_zero]
    exact sum_flags (N.incident c) _
  rw [hsc, hbr]

/-- Selecting a character forces every incident branch toward it. -/
theorem sat_character_iff (s : Edge C R → Bool) (c : C) :
    (N.graph (.inr (.inl c))).Sat s ↔
      s (.inl c) = true → ∀ e ∈ N.incident c, s (.inr e) = true := by
  change (N.incident c).length ≤ (N.graph (.inr (.inl c))).inflow s ↔ _
  rw [inflow_character]
  cases hs : s (.inl c) with
  | false =>
    simp only [selectorWeight, ite_true, Bool.false_eq_true, false_implies, iff_true]
    omega
  | true =>
    have hle := List.countP_le_length (p := fun e => s (.inr e)) (l := N.incident c)
    simp only [Bool.true_eq_false, ite_false, Nat.zero_add, true_implies]
    rw [show (N.incident c).length ≤ (N.incident c).countP (fun e => s (.inr e)) ↔
      (N.incident c).countP (fun e => s (.inr e)) = (N.incident c).length from
      ⟨fun h => Nat.le_antisymm hle h, fun h => h.ge⟩, List.countP_eq_length]

/-- The finite weighted graph enforces exactly the row, character, and exclusion conditions. -/
theorem legal_iff (s : Edge C R → Bool) : N.graph.Legal s ↔ N.TargetLegal s := by
  constructor
  · intro hs
    constructor
    · exact fun u => (sat_row_iff N s u).mp (hs (.inl u))
    · intro r b hc
      apply (sat_character_iff N s (N.endpoint r b)).mp (hs (.inr (.inl _))) hc (r, b)
      simp [incident, branches, N.relations_complete r]
    · exact fun r => (sat_relation_iff N s r).mp (hs (.inr (.inr r)))
  · intro hs v
    rcases v with u | (c | r)
    · exact (sat_row_iff N s u).mpr (hs.nonempty u)
    · apply (sat_character_iff N s c).mpr
      intro hc e he
      have hec : N.endpoint e.1 e.2 = c := of_decide_eq_true (List.mem_filter.mp he).2
      exact hs.forced e.1 e.2 (hec.symm ▸ hc)
    · exact (sat_relation_iff N s r).mpr (hs.relation r)

end Cslib.Complexity.NCL.SelectorNetwork
