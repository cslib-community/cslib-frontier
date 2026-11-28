/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Search.GraphSearch
import CslibFrontierTests.Algorithms.Lean.Search.AStar

/-!
# Tests for best-first graph search and A* graph search

On the road problem of the A* tree search tests (cheapest solution `a, b, c, g` of cost `7`):

* A* graph search returns the cheapest solution with the consistent heuristics `h₁` and `hStar`,
  and so does uniform-cost graph search.
* With the admissible but inconsistent `h₂`, A* graph search returns the costlier `b, c, g`: it
  expands `b` by the road `s–b` before the cheaper route through `a` is known, and never reopens
  it. A* tree search finds the cheapest solution with the same heuristic. Consistency cannot be
  weakened to admissibility in `aStarGraphSearch_isOptimalSolution`.
* Instances of soundness, optimality and completeness.
* The query program evaluates to the pure algorithm. Exact expansion counts: with `h₁`, A* graph
  search expands each of `s, a, b, c` once and `g` never; uniform-cost graph search also expands
  each state at most once, where uniform-cost tree search expands `b` eleven times. With the goal
  removed, graph search expands each of the five states once and stops, where tree search spends
  all its fuel.
* Instances of the two expansion bounds, for A*'s priority, showing that their hypotheses are
  satisfiable.
-/

namespace CslibFrontierTests.Algorithms.Lean.Search.GraphSearch

open Cslib Cslib.Algorithms.Lean.Search CslibFrontierTests.Algorithms.Lean.Search.AStar

/-! ### Runs of A* graph search -/

example : aStarGraphSearch roads h₁ F 50 = some ⟨.g, [.a, .b, .c, .g], 7⟩ := by decide

example : aStarGraphSearch roads hStar F 50 = some ⟨.g, [.a, .b, .c, .g], 7⟩ := by decide

/-- Uniform-cost graph search finds the cheapest solution. -/
example : bestFirstGraphSearch roads F (·.cost) 50 = some ⟨.g, [.a, .b, .c, .g], 7⟩ := by decide

/-- With the admissible but inconsistent `h₂`, A* graph search returns a costlier solution. -/
example : aStarGraphSearch roads h₂ F 50 = some ⟨.g, [.b, .c, .g], 8⟩ := by decide

/-- Without fuel the search returns nothing. -/
example : aStarGraphSearch roads h₁ F 0 = none := by decide

/-- With no goal state, the frontier empties: every state is explored. -/
example : bestFirstGraphSearch { roads with isGoal := fun _ => false } F (·.cost) 50 = none := by
  decide

/-! ### Soundness and optimality -/

example {x : Node V V} (h : aStarGraphSearch roads h₂ F 50 = some x) :
    roads.IsSolution x.path ∧ roads.pathCost roads.initial x.path = x.cost :=
  have h' := bestFirstGraphSearch_sound Frontier.lawful_sortedList roads _ 50 h
  ⟨⟨x.state, h'.1, h'.2.1⟩, h'.2.2⟩

example (fuel : ℕ) {x : Node V V} (hx : aStarGraphSearch roads h₁ F fuel = some x) :
    roads.IsOptimalSolution x.path :=
  aStarGraphSearch_isOptimalSolution Frontier.lawful_sortedList consistent_h₁ fuel hx

example (fuel : ℕ) {x : Node V V} (hx : bestFirstGraphSearch roads F (·.cost) fuel = some x) :
    roads.IsOptimalSolution x.path :=
  uniformCostGraphSearch_isOptimalSolution Frontier.lawful_sortedList fuel hx

/-- Completeness: every place has at most three roads, so `3 * 5 + 1 = 16` iterations suffice
for A* graph search with `h₁` to return an optimal solution. -/
example : ∃ x, aStarGraphSearch roads h₁ F 16 = some x ∧ roads.IsOptimalSolution x.path :=
  aStarGraphSearch_complete Frontier.lawful_sortedList consistent_h₁ (Finset.mem_univ _)
    (fun _ _ _ _ => Finset.mem_univ _) (b := 3) (fun v _ => by cases v <;> decide)
    isOptimalSolution_abcg.1 (by decide)

/-- Completeness holds for every priority, here a constant one. -/
example : ∃ x, bestFirstGraphSearch roads F (fun _ => 0) 16 = some x ∧ roads.IsSolution x.path :=
  bestFirstGraphSearch_complete Frontier.lawful_sortedList _ (Finset.mem_univ _)
    (fun _ _ _ _ => Finset.mem_univ _) (b := 3) (fun v _ => by cases v <;> decide)
    isOptimalSolution_abcg.1 (by decide)

/-- The solution found with `h₂` is not optimal, although `h₂` is admissible. -/
example : roads.Admissible h₂ ∧ ¬ roads.IsOptimalSolution [.b, .c, .g] :=
  ⟨admissible_h₂, fun h => absurd (h.2 _ isOptimalSolution_abcg.1) (by decide)⟩

/-! ### The query program -/

/-- Evaluated against the oracle of `roads` with heuristic `h`, the query program of A* graph
search is A* graph search with `h`. -/
example (h : V → ℕ) (fuel : ℕ) :
    (bestFirstGraphSearchQ F aStarPrio fuel roads.initial).eval (roads.oracle h) =
      aStarGraphSearch roads h F fuel := by
  simp

/-- With `h₁`, A* graph search expands four nodes. -/
example : (bestFirstGraphSearchQ F aStarPrio 50 .s).cost (roads.oracle h₁)
    SearchQuery.expansionWeight = 4 := by
  decide

/-- With `h₁`, A* graph search expands each of `s, a, b, c` exactly once and `g` never. -/
example : [V.s, .a, .b, .c, .g].map (fun v => (bestFirstGraphSearchQ F aStarPrio 50 .s).cost
    (roads.oracle h₁) (SearchQuery.expansionWeightAt v)) = [1, 1, 1, 1, 0] := by
  decide

/-- Uniform-cost graph search expands every state at most once; uniform-cost tree search expands
`s, a, b, c` six, nine, eleven and seven times. -/
example (v : V) : (bestFirstGraphSearchQ F (fun x => pure x.cost) 50 .s).cost (roads.oracle h₁)
    (SearchQuery.expansionWeightAt v) ≤ 1 := by
  cases v <;> decide

example : [V.s, .a, .b, .c, .g].map (fun v => (bestFirstTreeSearchQ F (fun x => pure x.cost) 50
    .s).cost (roads.oracle h₁) (SearchQuery.expansionWeightAt v)) = [6, 9, 11, 7, 0] := by
  decide +kernel

/-- With no goal state, graph search expands each of the five states once; tree search expands a
node in every one of its `50` iterations. -/
example : (bestFirstGraphSearchQ F aStarPrio 50 .s).cost
    (({ roads with isGoal := fun _ => false } : Problem V V).oracle h₁)
    SearchQuery.expansionWeight = 5 := by
  decide

example : (bestFirstTreeSearchQ F aStarPrio 50 .s).cost
    (({ roads with isGoal := fun _ => false } : Problem V V).oracle h₁)
    SearchQuery.expansionWeight = 50 := by
  decide +kernel

/-! ### The expansion bounds -/

/-- A*'s priority asks only for the heuristic, so it expands nothing. -/
theorem cost_aStarPrio {w : {ι : Type} → SearchQuery V V ι → ℕ}
    (hw : ∀ v, w (.heuristic v) = 0) (oracle : {ι : Type} → SearchQuery V V ι → ι) (x : Node V V) :
    (aStarPrio x).cost oracle w = 0 := by
  simp [hw]

/-- For every oracle, A* graph search expands every state at most once. -/
example (oracle : {ι : Type} → SearchQuery V V ι → ι) (v : V) (fuel : ℕ) (init : V) :
    (bestFirstGraphSearchQ F aStarPrio fuel init).cost oracle (SearchQuery.expansionWeightAt v) ≤
      1 :=
  cost_expansionWeightAt_bestFirstGraphSearchQ_le_one oracle v aStarPrio
    (cost_aStarPrio (fun _ => rfl) oracle) fuel init

/-- For every oracle, A* graph search expands at most `5 = Fintype.card V` nodes. -/
example (oracle : {ι : Type} → SearchQuery V V ι → ι) (fuel : ℕ) (init : V) :
    (bestFirstGraphSearchQ F aStarPrio fuel init).cost oracle SearchQuery.expansionWeight ≤ 5 :=
  cost_expansionWeight_bestFirstGraphSearchQ_le_card oracle Frontier.lawful_sortedList aStarPrio
    (cost_aStarPrio (fun _ => rfl) oracle) Finset.univ (Finset.mem_univ init)
    (fun _ _ _ _ => Finset.mem_univ _) fuel

/-- The road problem from `c` with no goal state and the roads into `s` closed: the states
`a, b, c, g` form a closed set containing `c`, and `s` is unreachable. -/
def noReturn : Problem V V :=
  { roads with
    initial := .c
    isGoal := fun _ => false
    actions
      | .s => [.a, .b]
      | .a => [.b, .c]
      | .b => [.a, .c]
      | .c => [.a, .b, .g]
      | .g => [.c] }

/-- The bound for the closed set `{a, b, c, g}`: at most four expansions, fewer than the five
states. -/
theorem cost_noReturn_le (fuel : ℕ) :
    (bestFirstGraphSearchQ F aStarPrio fuel .c).cost (noReturn.oracle h₁)
      SearchQuery.expansionWeight ≤ 4 :=
  cost_expansionWeight_bestFirstGraphSearchQ_le_card _ Frontier.lawful_sortedList aStarPrio
    (cost_aStarPrio (fun _ => rfl) _) {.a, .b, .c, .g} (by decide) (by decide) fuel

/-- The bound is attained. -/
example : (bestFirstGraphSearchQ F aStarPrio 50 .c).cost (noReturn.oracle h₁)
    SearchQuery.expansionWeight = 4 := by
  decide

end CslibFrontierTests.Algorithms.Lean.Search.GraphSearch
