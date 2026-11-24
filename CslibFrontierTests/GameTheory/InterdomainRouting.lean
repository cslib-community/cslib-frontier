/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.InterdomainRouting.GaoRexford
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Interdomain Routing (BGP): Checked Witnesses and Boundary Cases

Kernel-checked witnesses (using ordinary `module` imports and zero `native_decide`) exercising
`StablePaths` and `GaoRexford`:

1. **`BAD GADGET` (4-node, 3-cycle):** explicit dispute wheel of size `3` and absence of any stable
   path assignment.
2. **`DISAGREE` (3-node, 2-cycle):** explicit dispute wheel of size `2`, two distinct stable path
   assignments, and extraction of a dispute wheel from their disagreement.
3. **Commercial 5-node Gao–Rexford network:** two tier-1 peers (`3, 4`), two regional peers
   (`1, 2`), and destination customer (`0`), checking `IsValleyFree` (both positive and valley
   negative witnesses), `NoCustomerProviderCycle`, `PreferCustomer` (`customer ≻ peer ≻ provider`),
   unique stable convergence, and fair round-robin convergence.
4. **Boundary cases:** trivial 1-node destination graph, disconnected AS receiving `none`,
   non-suffix-closed permitted paths (node `1` permits `[1, 2, 0]` while `2` does not permit
   `[2, 0]`), and a dispute-wheel-free instance that violates Gao–Rexford `PreferCustomer`
   ([FeigenbaumSchapiraShenker2007], Chapter 14, Exercise 14.7).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.InterdomainRouting

open Cslib.GameTheory.InterdomainRouting

/-! ### 1. `BAD GADGET` and `DISAGREE` -/

example : badGadgetDisputeWheel.size = 3 := by simp
example : Nonempty (DisputeWheel badGadget) := ⟨badGadgetDisputeWheel⟩
example : 2 ≤ badGadgetDisputeWheel.size := badGadgetDisputeWheel.two_le_size
example : ¬ ∃ π, badGadget.IsStable π := not_exists_isStable_badGadget

example : disagreeDisputeWheel.size = 2 := by simp
example : ∃ π₁ π₂, disagree.IsStable π₁ ∧ disagree.IsStable π₂ ∧ π₁ ≠ π₂ :=
  exists_two_isStable_disagree

example : Nonempty (DisputeWheel disagree) := by
  obtain ⟨π₁, π₂, h₁, h₂, hne⟩ := exists_two_isStable_disagree
  exact disagree.nonempty_disputeWheel_of_isStable_ne h₁ h₂ hne

/-! ### 2. Concrete 5-node Gao–Rexford commercial network -/

/-- Edges of the 5-node commercial topology:
`0` is a customer of `1` and `2`; `1` and `2` are peers; `1` is a customer of `3`;
`2` is a customer of `4`; `3` and `4` are peers. -/
private def commAdj (u v : Fin 5) : Prop :=
  (u = 0 ∧ (v = 1 ∨ v = 2)) ∨
  (u = 1 ∧ (v = 0 ∨ v = 2 ∨ v = 3)) ∨
  (u = 2 ∧ (v = 0 ∨ v = 1 ∨ v = 4)) ∨
  (u = 3 ∧ (v = 1 ∨ v = 4)) ∨
  (u = 4 ∧ (v = 2 ∨ v = 3))

private def commGraph : SimpleGraph (Fin 5) where
  Adj := commAdj
  symm := ⟨fun u v h => by fin_cases u <;> fin_cases v <;> simp_all [commAdj]⟩
  loopless := ⟨fun u h => by fin_cases u <;> simp [commAdj] at h⟩

/-- Commercial relationships on `commGraph`:
`1, 2` are providers of `0`; `3` is a provider of `1`; `4` is a provider of `2`;
`(1, 2)` and `(3, 4)` are peer links. -/
private def commRel (u v : Fin 5) : CommercialRel :=
  match u.val, v.val with
  | 1, 0 => .customer
  | 2, 0 => .customer
  | 3, 1 => .customer
  | 4, 2 => .customer
  | 0, 1 => .provider
  | 0, 2 => .provider
  | 1, 3 => .provider
  | 2, 4 => .provider
  | _, _ => .peer

/-- Valley-free check: `[1, 3, 4, 2, 0]` (`provider → peer → customer → customer`) is valley-free,
while `[3, 1, 2, 0]` (`customer → peer → customer`) and `[1, 0, 2]` (`customer → provider`) are
not. -/
example : IsValleyFree commRel ([1, 3, 4, 2, 0] : List (Fin 5)) := by decide
example : ¬ IsValleyFree commRel ([3, 1, 2, 0] : List (Fin 5)) := by decide
example : ¬ IsValleyFree commRel ([1, 0, 2] : List (Fin 5)) := by decide

/-- A 5-node commercial `SPP` with valley-free permitted paths and strict
`customer ≻ peer ≻ provider` preferences. -/
private def commercialNet : SPP (Fin 5) where
  graph := commGraph
  dest := 0
  permitted u p :=
    (u = 0 ∧ p = [0]) ∨
    (u = 1 ∧ (p = [1, 0] ∨ p = [1, 2, 0] ∨ p = [1, 3, 4, 2, 0])) ∨
    (u = 2 ∧ (p = [2, 0] ∨ p = [2, 1, 0] ∨ p = [2, 4, 3, 1, 0])) ∨
    (u = 3 ∧ (p = [3, 1, 0] ∨ p = [3, 4, 2, 0])) ∨
    (u = 4 ∧ (p = [4, 2, 0] ∨ p = [4, 3, 1, 0]))
  permitted_isSimplePath := by
    intro u p hp
    rcases hp with ⟨rfl, rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl⟩ |
      ⟨rfl, rfl | rfl⟩ <;>
      refine ⟨rfl, rfl, ?_, by decide⟩ <;>
      simp [commGraph, commAdj]
  permitted_dest := Or.inl ⟨rfl, rfl⟩
  rank _ o :=
    match o with
    | none => 0
    | some p =>
      match p with
      | [0] => 1
      | [1, 0] => 3
      | [1, 2, 0] => 2
      | [1, 3, 4, 2, 0] => 1
      | [2, 0] => 3
      | [2, 1, 0] => 2
      | [2, 4, 3, 1, 0] => 1
      | [3, 1, 0] => 2
      | [3, 4, 2, 0] => 1
      | [4, 2, 0] => 2
      | [4, 3, 1, 0] => 1
      | _ => 1
  rank_none _ := rfl
  rank_pos := by
    intro u p hp
    rcases hp with ⟨rfl, rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl⟩ |
      ⟨rfl, rfl | rfl⟩ <;> decide
  strict := by
    intro u p₁ p₂ h₁ h₂ hr
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
    rcases h₂ with ⟨h, rfl⟩ | ⟨h, rfl | rfl | rfl⟩ | ⟨h, rfl | rfl | rfl⟩ |
      ⟨h, rfl | rfl⟩ | ⟨h, rfl | rfl⟩ <;>
    simp_all

/-- Tier level strictly decreases along every provider-to-customer edge in `commercialNet`. -/
private def commLevel : Fin 5 → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 2

private def commercialNet_gaoRexford : GaoRexfordConditions commercialNet where
  rel := commRel
  rel_symm := by
    intro u v hadj
    fin_cases u <;> fin_cases v <;> simp_all [commercialNet, commGraph, commAdj, commRel,
      CommercialRel.flip]
  noCustomerProviderCycle := by
    have hdec : ∀ u v, IsProviderOf commercialNet.graph commRel u v →
        commLevel v < commLevel u := by
      intro u v ⟨hadj, hrel⟩
      fin_cases u <;> fin_cases v <;>
        simp_all [commercialNet, commGraph, commAdj, commRel, commLevel]
    have htrans : ∀ u v, Relation.TransGen (IsProviderOf commercialNet.graph commRel) u v →
        commLevel v < commLevel u := by
      intro u v h
      induction h with
      | single h1 => exact hdec _ _ h1
      | tail _ h2 ih => exact lt_trans (hdec _ _ h2) ih
    intro u hcyc
    exact Nat.lt_irrefl _ (htrans u u hcyc)
  valleyFree := by
    intro u p hp
    rcases hp with ⟨rfl, rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl⟩ |
      ⟨rfl, rfl | rfl⟩ <;> decide
  preferCustomer := by
    intro u v₁ v₂ t₁ t₂ h₁ h₂ hc₁ hc₂
    rcases h₁ with ⟨rfl, h⟩ | ⟨rfl, h | h | h⟩ | ⟨rfl, h | h | h⟩ |
      ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩ <;>
    cases h <;>
    rcases h₂ with ⟨hu, h'⟩ | ⟨hu, h' | h' | h'⟩ | ⟨hu, h' | h' | h'⟩ |
      ⟨hu, h' | h'⟩ | ⟨hu, h' | h'⟩ <;>
    first | contradiction | (cases h'; simp_all [commercialNet, commRel])

/-- By Gao–Rexford, `commercialNet` has no dispute wheel and a unique stable assignment. -/
example : IsEmpty (DisputeWheel commercialNet) := commercialNet_gaoRexford.isEmpty_disputeWheel

private def commExpected : Fin 5 → Option (List (Fin 5)) :=
  ![some [0], some [1, 0], some [2, 0], some [3, 1, 0], some [4, 2, 0]]

private theorem commExpected_isStable : commercialNet.IsStable commExpected := by
  refine ⟨rfl, fun u hu => ?_⟩
  fin_cases u
  · exact (hu rfl).elim
  · refine ⟨Or.inr ⟨[1, 0], rfl, by simp [commercialNet], 0, [0],
      by simp [commercialNet, commGraph, commAdj], rfl, rfl⟩, fun o ho => ?_⟩
    rcases ho with rfl | ⟨p, rfl, hp, _⟩
    · decide
    · rcases hp with ⟨h, _⟩ | ⟨_, rfl | rfl | rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;>
        first | (exfalso; revert h; decide) | decide
  · refine ⟨Or.inr ⟨[2, 0], rfl, by simp [commercialNet], 0, [0],
      by simp [commercialNet, commGraph, commAdj], rfl, rfl⟩, fun o ho => ?_⟩
    rcases ho with rfl | ⟨p, rfl, hp, _⟩
    · decide
    · rcases hp with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl | rfl | rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;>
        first | (exfalso; revert h; decide) | decide
  · refine ⟨Or.inr ⟨[3, 1, 0], rfl, by simp [commercialNet], 1, [1, 0],
      by simp [commercialNet, commGraph, commAdj], rfl, rfl⟩, fun o ho => ?_⟩
    rcases ho with rfl | ⟨p, rfl, hp, _⟩
    · decide
    · rcases hp with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl | rfl⟩ | ⟨h, _⟩ <;>
        first | (exfalso; revert h; decide) | decide
  · refine ⟨Or.inr ⟨[4, 2, 0], rfl, by simp [commercialNet], 2, [2, 0],
      by simp [commercialNet, commGraph, commAdj], rfl, rfl⟩, fun o ho => ?_⟩
    rcases ho with rfl | ⟨p, rfl, hp, _⟩
    · decide
    · rcases hp with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl | rfl⟩ <;>
        first | (exfalso; revert h; decide) | decide

/-- Round-robin activation on `commercialNet` converges in finite time to `commExpected`. -/
example : ∃ T, ∀ t ≥ T,
    commercialNet.run (fun n => ⟨n % 5, Nat.mod_lt _ (by decide)⟩)
      commercialNet.initAssignment t = commExpected := by
  have hfair : SPP.IsFair (fun n : ℕ => (⟨n % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5)) := by
    intro v t
    refine ⟨5 * t + v.val, by omega, ?_⟩
    apply Fin.ext
    simp [Nat.add_mod, Nat.mod_eq_of_lt v.isLt]
  obtain ⟨π, hπ, T, hconv⟩ := commercialNet_gaoRexford.exists_converges _ hfair
  obtain ⟨_, _, huniq⟩ := commercialNet_gaoRexford.existsUnique_isStable
  have hEq : π = commExpected := (huniq π hπ).trans (huniq commExpected commExpected_isStable).symm
  exact ⟨T, fun t ht => (hconv t ht).trans hEq⟩

/-! ### 3. Edge cases and boundaries -/

/-- Trivial 1-node destination-only SPP. -/
private def trivialSPP : SPP (Fin 1) where
  graph := ⊥
  dest := 0
  permitted _ p := p = [0]
  permitted_isSimplePath := by
    intro u p hp
    fin_cases u
    subst hp
    exact ⟨rfl, rfl, by simp, by decide⟩
  permitted_dest := rfl
  rank _ o := if o.isSome then 1 else 0
  rank_none _ := rfl
  rank_pos _ _ _ := by simp
  strict := by
    intro u p₁ p₂ h₁ h₂ _
    subst h₁; subst h₂; rfl

example : IsEmpty (DisputeWheel trivialSPP) :=
  ⟨fun W => W.node_ne_dest ⟨0, W.size_pos⟩ (Subsingleton.elim _ _)⟩

example : ∃! π, trivialSPP.IsStable π :=
  trivialSPP.existsUnique_isStable_of_isEmpty_disputeWheel
    ⟨fun W => W.node_ne_dest ⟨0, W.size_pos⟩ (Subsingleton.elim _ _)⟩

/-- Disconnected AS (`2`) with no edges to `{0, 1}` receives `none` in the unique stable
assignment. -/
private def disconnectedSPP : SPP (Fin 3) where
  graph := SimpleGraph.fromRel fun u v => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)
  dest := 0
  permitted u p := (u = 0 ∧ p = [0]) ∨ (u = 1 ∧ p = [1, 0])
  permitted_isSimplePath := by
    intro u p hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl, by simp, by decide⟩
    · refine ⟨rfl, rfl, ?_, by decide⟩
      simp [SimpleGraph.fromRel]
  permitted_dest := Or.inl ⟨rfl, rfl⟩
  rank _ o := if o.isSome then 1 else 0
  rank_none _ := rfl
  rank_pos _ _ _ := by simp
  strict := by
    intro u p₁ p₂ h₁ h₂ _
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases h₂ with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> simp_all

example : ∀ π, disconnectedSPP.IsStable π → π 2 = none := by
  intro π hπ
  rcases (hπ.2 2 (by decide)).1 with hnone | ⟨p, _, hp, _⟩
  · exact hnone
  · rcases hp with ⟨h, _⟩ | ⟨h, _⟩ <;> exfalso <;> revert h <;> decide

/-- Boundary test for non-suffix-closed permitted sets: node `1` permits `[1, 2, 0]`, while node
`2` permits nothing. In any stable assignment both `1` and `2` receive `none`. -/
private def unpermittedSuffixSPP : SPP (Fin 3) where
  graph := ⊤
  dest := 0
  permitted u p := (u = 0 ∧ p = [0]) ∨ (u = 1 ∧ p = [1, 2, 0])
  permitted_isSimplePath := by
    intro u p hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> refine ⟨rfl, rfl, by simp, by decide⟩
  permitted_dest := Or.inl ⟨rfl, rfl⟩
  rank _ o := if o.isSome then 1 else 0
  rank_none _ := rfl
  rank_pos _ _ _ := by simp
  strict := by
    intro u p₁ p₂ h₁ h₂ _
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases h₂ with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> simp_all

example : ∀ π, unpermittedSuffixSPP.IsStable π → π 1 = none ∧ π 2 = none := by
  intro π hπ
  have h2 : π 2 = none := by
    rcases (hπ.2 2 (by decide)).1 with hnone | ⟨p, _, hp, _⟩
    · exact hnone
    · rcases hp with ⟨h, _⟩ | ⟨h, _⟩ <;> exfalso <;> revert h <;> decide
  have h1 : π 1 = none := by
    rcases (hπ.2 1 (by decide)).1 with hnone | ⟨p, hp, hperm, w, q, _, hqw, rfl⟩
    · exact hnone
    · rcases hperm with ⟨h, _⟩ | ⟨_, hEq⟩
      · exfalso; revert h; decide
      · have hq : q = [2, 0] := (List.cons.inj hEq).2
        subst hq
        have hw : w = 2 := by
          have hpw := hπ.permitted_of_eq_some hqw
          have hhd := (unpermittedSuffixSPP.permitted_isSimplePath w [2, 0] hpw).1
          exact (Option.some.inj hhd).symm
        subst hw
        rw [h2] at hqw
        cases hqw
  exact ⟨h1, h2⟩

/-- Witness that Gao–Rexford is sufficient but not necessary for dispute-wheel freeness
([FeigenbaumSchapiraShenker2007], Chapter 14, Exercise 14.7): node `1` prefers a peer detour
`[1, 2, 0]` over its customer path `[1, 0]` (violating `PreferCustomer`), yet node `2` permits only
`[2, 0]`, so no dispute wheel exists and a unique stable assignment exists. -/
private def nonGaoRexfordSafe : SPP (Fin 3) where
  graph := ⊤
  dest := 0
  permitted u p :=
    (u = 0 ∧ p = [0]) ∨
    (u = 1 ∧ (p = [1, 2, 0] ∨ p = [1, 0])) ∨
    (u = 2 ∧ p = [2, 0])
  permitted_isSimplePath := by
    intro u p hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;>
      refine ⟨rfl, rfl, by simp, by decide⟩
  permitted_dest := Or.inl ⟨rfl, rfl⟩
  rank _ o :=
    match o with
    | none => 0
    | some p => p.length
  rank_none _ := rfl
  rank_pos := by
    intro u p hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  strict := by
    intro u p₁ p₂ h₁ h₂ hr
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases h₂ with ⟨h, rfl⟩ | ⟨h, rfl | rfl⟩ | ⟨h, rfl⟩ <;> simp_all

example : IsEmpty (DisputeWheel nonGaoRexfordSafe) := by
  refine ⟨fun W => ?_⟩
  have h1 : ∀ i : Fin W.size, W.node i = 1 := by
    intro i
    have hne0 := W.node_ne_dest i
    have hpref := W.prefers i
    have hp := W.pivot_permitted i
    have hrp := W.rim_pivot_permitted i
    rcases hp with ⟨h0, _⟩ | ⟨h1, _⟩ | ⟨h2, hp2⟩
    · exact (hne0 h0).elim
    · exact h1
    · rw [h2] at hrp hpref
      rcases hrp with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hrp2⟩
      · exfalso; revert h; decide
      · exfalso; revert h; decide
      · rw [hp2, hrp2] at hpref
        omega
  exact W.node_ne_next ⟨0, W.size_pos⟩ ((h1 _).trans (h1 _).symm)

example : ¬ PreferCustomer nonGaoRexfordSafe (fun u v =>
    match u.val, v.val with
    | 1, 0 => .customer
    | 2, 0 => .customer
    | 0, 1 => .provider
    | 0, 2 => .provider
    | _, _ => .peer) := by
  intro hpc
  have hlt := hpc 1 0 2 [] [0] (by simp [nonGaoRexfordSafe]) (by simp [nonGaoRexfordSafe]) rfl
    (by decide)
  simp [nonGaoRexfordSafe] at hlt

end CslibFrontierTests.GameTheory.InterdomainRouting
