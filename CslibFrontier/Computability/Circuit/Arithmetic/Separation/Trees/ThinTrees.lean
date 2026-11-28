/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.SlpCost
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Groups
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Moves
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Accel
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Laws
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Thin trees

Theorem H.2 of [AnthropicVPVNP2026] (pp. 45–46) writes the value of a network on at most `M`
nodes, with units of `ℓ` bits and at most `N` units at a node, as a sum, over sequences of good
outcomes of moves, of the values of networks whose nodes form a tree of small depth (Section
H.3). A network is a starting position of the play (`Play.value` on the initial units): the
given nodes are the `A` base parties, with tables `init` that read their initial units. The moves
(`Cut.Moves`) are relays and laws of a fixed list, and the plan (`Cut.Plan`) says which units they
use. `ThinTrees` collects them with the tree (the stages, the root, and the parent of every party
for the numbers `n` of initial units and the outcomes `o`), the units `units` between the parties
and their parents that a program computes, the dead units, and the bounds of the theorem:

* (a) the depth is at most `Λ = lg M ^ C`, the given nodes are of stage `0`, every node but the
  root has its parent in the next stage and at most `b` children, and the root at most `C`;
* (b) at most `M ^ C` dead units; every other unit in the end joins a node and its parent, and
  their number is at most `units` (`card_filter_holds_le` bounds those at a node);
* (c) the value, the tests of the relays and the laws of the list, no law move at a node of the
  stage `0`, and the layers of the law moves at a node against the units that it ever holds;
* (d) a straight-line program with `(M N) ^ C` steps over the numbers below `(M N) ^ C`
  (`TreeProgram`), and the numbers of parties, moves, outcomes and units;
* (e) the bounds of `units` at a node and its children and in all, and the units that a party
  ever holds and reads.

The units from a node to itself are allowed here; they stay at their node, which sums over them.

## Main definitions

* `Trees.TreeProgram`: a program that computes the tree, the units and the numbers of the moves
  of a plan from the numbers of initial units and the outcomes.
* `Trees.ThinTrees`: the moves, the plan and the trees of Theorem H.2.

## Main results

* `Trees.ThinTrees.card_filter_holds_le`: Theorem H.2(b) for the units at a node, its children
  included.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Section H.2 (packets, networks and the two moves, p. 45) and Theorem H.2 (pp. 45–46); module
  `Paper.Tree`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Trees

open Finset Cut Interpreter TowerPlan

variable {R : Type*} [CommSemiring R] {A A' E U0 U1 : ℕ}

/-- A straight-line program with `steps` gates over the letters `Fin K`, whose inputs are the pairs
`(n, o)` of the numbers `n` of initial units and the outcomes `o` of a plan `P`, and which computes
the parents `parent`, the units `units` between the parties and their parents, the current units
after all moves, the units given at the slots, the numbers of units of the moves and the good
outcomes (Theorem H.2(d), (e)). A property is computed by its indicator. -/
structure TreeProgram {M : Moves R (A + A') E} (P : Plan M U0 U1)
    (parent : (Fin A → Fin A → Fin (U0 + 1)) → (M.Channel → Fin U1) → Fin (A + A') →
      Fin (A + A'))
    (units : (Fin A → Fin A → Fin (U0 + 1)) → (M.Channel → Fin U1) → Fin (A + A') → ℕ)
    (K steps : ℕ) where
  /-- The number of inputs. -/
  numInputs : ℕ
  /-- The inputs of the program. -/
  input : Fin numInputs → (Fin A → Fin A → Fin (U0 + 1)) × (M.Channel → Fin U1) → Fin K
  /-- The functions that the program computes. -/
  computed : Set ((Fin A → Fin A → Fin (U0 + 1)) × (M.Channel → Fin U1) → ℕ)
  slpN : SlpN input steps computed
  /-- Every input is a number of initial units or an outcome. -/
  input_eq : ∀ i, (∃ a c, ∀ n o, (input i (n, o) : ℕ) = n a c) ∨
    ∃ ν, ∀ n o, (input i (n, o) : ℕ) = o ν
  initial_mem : ∀ a c, (fun (n, _) => (n a c : ℕ)) ∈ computed
  outcome_mem : ∀ ν, (fun (_, o) => (o ν : ℕ)) ∈ computed
  parent_mem : ∀ p q, {(n, o) : _ × _ | parent n o p = q}.indicator 1 ∈ computed
  units_mem : ∀ p, (fun (n, o) => units n o p) ∈ computed
  cur_mem : ∀ u, {(n, o) : _ × _ | u ∈ P.cur n o E}.indicator 1 ∈ computed
  given_mem : ∀ z u, {(n, o) : _ × _ | u ∈ P.given n o z}.indicator 1 ∈ computed
  count_mem : ∀ y, (fun (n, o) => P.count n o y) ∈ computed
  good_mem : ∀ y, {(n, o) : _ × _ | P.Good n o y}.indicator 1 ∈ computed

/-- **Thin trees** (Theorem H.2 of [AnthropicVPVNP2026], pp. 45–46) for networks on `A` given
nodes, with at most `N` units at a node, units of `ℓ` bits and at most `M` nodes: moves of the
relay and of the laws `laws` on the `A + A'` parties, with a plan that obeys the rules, the tree of
every choice of numbers `n` of initial units and outcomes `o` (stages, root and parents), the units
`units` between the parties and their parents, and the dead units, with the bounds (a)–(e) of the
theorem for the bound `b` of the children, the integer `G` of the test of the law moves, the
exponent `C` and the gain `γ`. The bounds on the units hold for good outcomes and at most `N`
initial units at every base party. -/
structure ThinTrees (laws : List (Law R)) (A N ℓ M b G C : ℕ) (γ : ℝ) where
  /-- The number of parties that are not given nodes. -/
  A' : ℕ
  /-- The number of moves. -/
  E : ℕ
  /-- The outcomes are below `U1`. -/
  U1 : ℕ
  U1_pos : 0 < U1
  /-- The moves. -/
  moves : Moves R (A + A') E
  /-- The plan: the units given in the moves, their numbers, and the good outcomes. -/
  plan : Plan moves N U1
  [decidableGood : ∀ n o x, Decidable (plan.Good n o x)]
  /-- The bound for the units of a move. -/
  cap : ℕ
  /-- The plan obeys the rules. -/
  ok : plan.Ok cap
  /-- The law moves; the other moves are relays. -/
  isLaw : Fin E → Bool
  law_mem : ∀ x, isLaw x = true → moves.law x ∈ laws
  law_eq_relay : ∀ x, isLaw x = false → moves.law x = relayLaw R
  /-- The good outcomes: short, with at least as many units on every channel as the move uses,
  at a law move, and as many as it uses at a relay. -/
  good_iff : ∀ n o x, plan.Good n o x ↔ if isLaw x then
      b * ∑ ν, (o ⟨x, ν⟩ : ℕ) ^ 2 ≤ G * plan.count n o x ^ 2 ∧ ∀ ν, plan.count n o x ≤ o ⟨x, ν⟩
    else ∀ ν, (o ⟨x, ν⟩ : ℕ) = plan.count n o x
  /-- Every possible outcome is good. -/
  good_of_possible : ∀ n o x, plan.Possible n o ℓ x → plan.Good n o x
  /-- (c) The value: for tables `init` of the parties at the beginning that read the initial
  units only and vanish unless the initial units that the party holds are present, the value of
  the position at the beginning is the sum, over the good outcomes, of the values of the positions
  after all moves, where the table of a party is its table at the beginning times the tables of
  its roles. -/
  value : ∀ (n : Fin A → Fin A → Fin (N + 1))
    (init : Fin (A + A') → (UnitId A N moves.Channel U1 → UnitContent ℓ) → R),
    (∀ a y y', (∀ b c k, y (.init b c k) = y' (.init b c k)) → init a y = init a y') →
    (∀ a y, init a y ≠ 0 → ∀ id ∈ initialUnits n,
      Play.Holds (UnitId.holder moves.channelParty) a id → y id ≠ none) →
    Play.value (UnitId.holder moves.channelParty) (none : UnitContent ℓ) (initialUnits n)
        (initialUnits n) (fun y => ∏ a, init a (y a)) =
      ∑ o : moves.Channel → Fin U1, if ∀ x, plan.Good n o x then
        Play.value (UnitId.holder moves.channelParty) none (Plan.seenAt n o E) (plan.cur n o E)
          (fun y => ∏ a, partyTable plan n o (init a) a (y a)) else 0
  /-- The stage of a party. -/
  stage : Fin (A + A') → ℕ
  /-- The depth of the tree. -/
  depth : ℕ
  /-- The root. -/
  root : Fin (A + A')
  /-- The parent of a party. -/
  parent : (Fin A → Fin A → Fin (N + 1)) → (moves.Channel → Fin U1) → Fin (A + A') →
    Fin (A + A')
  /-- The bound for the units between a party and its parent that the program computes. -/
  units : (Fin A → Fin A → Fin (N + 1)) → (moves.Channel → Fin U1) → Fin (A + A') → ℕ
  /-- The dead units. -/
  dead : (moves.Channel → Fin U1) → Finset (UnitId A N moves.Channel U1)
  depth_le : depth ≤ lg M ^ C
  stage_le : ∀ p, stage p ≤ depth
  stage_base : ∀ a, stage (Fin.castAdd A' a) = 0
  stage_eq_depth_iff : ∀ p, stage p = depth ↔ p = root
  stage_parent : ∀ n o p, p ≠ root → stage (parent n o p) = stage p + 1
  card_children_le : ∀ n o p, p ≠ root →
    (univ.filter fun q => q ≠ root ∧ parent n o q = p).card ≤ b
  card_children_root_le : ∀ n o, (univ.filter fun q => q ≠ root ∧ parent n o q = root).card ≤ C
  card_dead_le : ∀ o, (dead o).card ≤ M ^ C
  /-- No law move is at a node of the stage `0`. -/
  stage_pos : ∀ r : moves.Role, isLaw r.1 = true → 0 < stage (moves.roleParty r)
  /-- (b) The units in the end that are not dead and join two parties join a party and its
  parent. -/
  exists_parent : ∀ n, (∀ a, ∑ c, ((n a c : ℕ) + n c a) ≤ N) → ∀ o, (∀ x, plan.Good n o x) →
    ∀ u ∈ Play.cutUnits (UnitId.holder moves.channelParty) id (plan.cur n o E \ dead o),
      ∃ p, p ≠ root ∧ s(UnitId.holder moves.channelParty u false,
        UnitId.holder moves.channelParty u true) = s(p, parent n o p)
  /-- (e) The units between a party and its parent are at most `units`. -/
  card_between_le : ∀ n, (∀ a, ∑ c, ((n a c : ℕ) + n c a) ≤ N) → ∀ o,
    (∀ x, plan.Good n o x) → ∀ p, p ≠ root →
      ((Play.cutUnits (UnitId.holder moves.channelParty) id (plan.cur n o E \ dead o)).filter
        fun u => s(UnitId.holder moves.channelParty u false,
          UnitId.holder moves.channelParty u true) = s(p, parent n o p)).card ≤ units n o p
  /-- (e) The units between a party and its parent, and between its children and the party. -/
  units_add_sum_le : ∀ n o p, ((units n o p +
      ∑ q ∈ univ.filter (fun q => q ≠ root ∧ parent n o q = p), units n o q : ℕ) : ℝ) ≤
    (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - γ) * (N + (M : ℝ) ^ 2)
  /-- (e) All units between the parties and their parents. -/
  sum_units_le : ∀ n o, ∑ p, units n o p ≤ lg M ^ C * M * (N + M ^ 2)
  /-- (c) The numbers of units of the law moves at a party, against the units that it ever
  holds. -/
  sum_count_le : ∀ n o, (∀ x, plan.Good n o x) → ∀ p,
    ∑ r ∈ univ.filter (fun r : moves.Role => moves.roleParty r = p ∧ isLaw r.1 = true),
      plan.count n o r.1 ≤
    ((Plan.seenAt n o E).filter (Play.Holds (UnitId.holder moves.channelParty) p)).card
  /-- (e) The units that a party ever holds, and the units that its roles read, zeros in slots
  included. -/
  card_held_add_le : ∀ n, (∀ a, ∑ c, ((n a c : ℕ) + n c a) ≤ N) → ∀ o,
    (∀ x, plan.Good n o x) → ∀ p,
      ((Plan.seenAt n o E).filter (Play.Holds (UnitId.holder moves.channelParty) p)).card +
          ∑ r ∈ univ.filter (fun r : moves.Role => moves.roleParty r = p),
            (1 + Fintype.card ((moves.law r.1).SlotAt r.2)) * plan.count n o r.1 ≤
        C * (units n o p + ∑ q ∈ univ.filter (fun q => q ≠ root ∧ parent n o q = p),
          units n o q) + (if (p : ℕ) < A then lg M ^ C * N else 0) +
        C * ((dead o).filter (Play.Holds (UnitId.holder moves.channelParty) p)).card
  /-- (d) The program. -/
  program : TreeProgram plan parent units ((M * N) ^ C) ((M * N) ^ C)
  parties_le : A + A' ≤ (M * N) ^ C
  moves_le : E ≤ (M * N) ^ C
  U1_le : U1 ≤ (M * N) ^ C
  card_unit_le : Fintype.card (UnitId A N moves.Channel U1) ≤ (M * N) ^ C

attribute [instance] ThinTrees.decidableGood

namespace ThinTrees

variable {laws : List (Law R)} {A N ℓ M b G C : ℕ} {γ : ℝ} (TT : ThinTrees laws A N ℓ M b G C γ)
  {n : Fin A → Fin A → Fin (N + 1)} {o : TT.moves.Channel → Fin TT.U1}

/-- The units in the end that are not dead, join two parties and have an end at the party `p` are
units between `p` and its parent or between a child of `p` and `p`. -/
private theorem card_filter_holds_le_units (hn : ∀ a, ∑ c, ((n a c : ℕ) + n c a) ≤ N)
    (hg : ∀ x, TT.plan.Good n o x) (p : Fin (A + TT.A')) :
    ((Play.cutUnits (UnitId.holder TT.moves.channelParty) id
        (TT.plan.cur n o TT.E \ TT.dead o)).filter
      (Play.Holds (UnitId.holder TT.moves.channelParty) p)).card ≤
    TT.units n o p + ∑ q ∈ univ.filter (fun q => q ≠ TT.root ∧ TT.parent n o q = p),
      TT.units n o q := by
  set S := Play.cutUnits (UnitId.holder TT.moves.channelParty) id (TT.plan.cur n o TT.E \ TT.dead o)
  set B := fun q => S.filter fun u => s(UnitId.holder TT.moves.channelParty u false,
    UnitId.holder TT.moves.channelParty u true) = s(q, TT.parent n o q)
  have hsub : S.filter (Play.Holds (UnitId.holder TT.moves.channelParty) p) ⊆
      (univ.filter fun q => q ≠ TT.root ∧ (q = p ∨ TT.parent n o q = p)).biUnion B := by
    intro u hu
    obtain ⟨hu, d, hd⟩ := mem_filter.1 hu
    obtain ⟨q, hq, he⟩ := TT.exists_parent n hn o hg u hu
    have hp : p ∈ s(q, TT.parent n o q) := he ▸ hd ▸ by cases d <;> simp
    exact mem_biUnion.2 ⟨q, mem_filter.2 ⟨mem_univ _, hq, (Sym2.mem_iff.1 hp).imp Eq.symm
      Eq.symm⟩, mem_filter.2 ⟨hu, he⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  refine (sum_le_sum fun q hq => TT.card_between_le n hn o hg q (mem_filter.1 hq).2.1).trans ?_
  rw [← sum_filter_add_sum_filter_not _ (· = p)]
  refine add_le_add ((sum_le_sum_of_subset (t := {p}) fun q hq => ?_).trans_eq
    (sum_singleton _ _)) (sum_le_sum_of_subset fun q hq => ?_)
  · exact mem_singleton.2 (mem_filter.1 hq).2
  · simp only [mem_filter, mem_univ, true_and] at hq ⊢
    exact ⟨hq.1.1, hq.1.2.resolve_left hq.2⟩

/-- **The units at a node** (Theorem H.2(b) of [AnthropicVPVNP2026], p. 46): the units in the end
that are not dead, join two parties and have an end at a party are at most
`Λ M ^ (1 - γ) (N + M ^ 2)`. -/
theorem card_filter_holds_le (hn : ∀ a, ∑ c, ((n a c : ℕ) + n c a) ≤ N)
    (hg : ∀ x, TT.plan.Good n o x) (p : Fin (A + TT.A')) :
    (((Play.cutUnits (UnitId.holder TT.moves.channelParty) id
        (TT.plan.cur n o TT.E \ TT.dead o)).filter
      (Play.Holds (UnitId.holder TT.moves.channelParty) p)).card : ℝ) ≤
    (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - γ) * (N + (M : ℝ) ^ 2) :=
  (Nat.cast_le.2 (TT.card_filter_holds_le_units hn hg p)).trans (TT.units_add_sum_le n o p)

end ThinTrees

end Cslib.Circuits.Arithmetic.Separation.Trees
