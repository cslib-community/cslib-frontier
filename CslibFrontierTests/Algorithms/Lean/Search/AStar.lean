/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Search.AStar

/-!
# Tests for heuristics and A* tree search

A weighted road problem on five places `s, a, b, c, g` with two-way roads
`s–a` (cost `1`), `s–b` (`4`), `a–b` (`2`), `a–c` (`5`), `b–c` (`1`) and `c–g` (`3`): from `s`,
reach `g`. An action is the place driven to. The cheapest solution is `a, b, c, g` of cost `7`;
`b, c, g` costs `8`.

* Heuristics: a consistent heuristic `h₁`; the optimal cost-to-go `hStar`, which is consistent and
  equals `Problem.costToGo`; an admissible but inconsistent heuristic `h₂`; an inadmissible
  heuristic `h₃`. These witness that the hypotheses of the optimality theorems are satisfiable,
  and that consistency is strictly stronger than admissibility.
* A* tree search returns the cheapest solution with `h₁` and with `h₂`, and the costlier `b, c, g`
  with `h₃`, which is therefore not optimal: admissibility cannot be dropped.
* Instances of the optimality theorems, including the derived fact that `a, b, c, g` is an
  optimal solution.
* The query program of A* evaluates to the pure algorithm; with `h₁` it expands four nodes, where
  uniform-cost tree search expands `33`.
-/

namespace CslibFrontierTests.Algorithms.Lean.Search.AStar

open Cslib Cslib.Algorithms.Lean.Search

/-- The places of the road problem. -/
inductive V
  | s
  | a
  | b
  | c
  | g
  deriving DecidableEq, Repr

instance : Fintype V where
  elems := {.s, .a, .b, .c, .g}
  complete x := by cases x <;> decide

/-- The cost of the road between two places (`0` where there is none). -/
def roadCost : V → V → ℕ
  | .s, .a | .a, .s => 1
  | .s, .b | .b, .s => 4
  | .a, .b | .b, .a => 2
  | .a, .c | .c, .a => 5
  | .b, .c | .c, .b => 1
  | .c, .g | .g, .c => 3
  | _, _ => 0

/-- From `s`, reach `g` along the roads; an action is the place driven to. -/
def roads : Problem V V where
  initial := .s
  actions
    | .s => [.a, .b]
    | .a => [.s, .b, .c]
    | .b => [.s, .a, .c]
    | .c => [.a, .b, .g]
    | .g => [.c]
  result _ v := v
  isGoal v := v == .g
  stepCost := roadCost

/-- A consistent heuristic. -/
def h₁ : V → ℕ
  | .s => 5 | .a => 4 | .b => 3 | .c => 2 | .g => 0

/-- The optimal cost-to-go. -/
def hStar : V → ℕ
  | .s => 7 | .a => 6 | .b => 4 | .c => 3 | .g => 0

/-- An admissible heuristic that is not consistent: it overestimates nothing, but `h₂ a = 6`
exceeds the cost `2` of the road from `a` to `b` plus `h₂ b = 0`. -/
def h₂ : V → ℕ
  | .s => 0 | .a => 6 | .b => 0 | .c => 1 | .g => 0

/-- An inadmissible heuristic: `h₃ a = 100` overestimates the cost `6` from `a` to `g`. -/
def h₃ : V → ℕ
  | .s => 0 | .a => 100 | .b => 0 | .c => 0 | .g => 0

/-- The sorted-list frontier of the road problem's nodes, keyed by `ℕ`. -/
abbrev F : Frontier (SortedListFrontier ℕ (Node V V)) ℕ (Node V V) := Frontier.sortedList

/-! ### Solutions -/

example : roads.IsSolution [.a, .b, .c, .g] := ⟨.g, by simp [roads], rfl⟩

example : roads.pathCost roads.initial [.a, .b, .c, .g] = 7 := by decide

example : roads.pathCost roads.initial [.b, .c, .g] = 8 := by decide

/-! ### Heuristics -/

theorem consistent_h₁ : roads.Consistent h₁ := ⟨by decide, by decide⟩

theorem consistent_hStar : roads.Consistent hStar := ⟨by decide, by decide⟩

/-- `hStar` is the optimal cost-to-go at the initial state: it is admissible, and a solution
attains it. -/
example : roads.costToGo roads.initial = 7 :=
  le_antisymm (iInf₂_le_of_le [.a, .b, .c, .g] .g (iInf_le_of_le ⟨by simp [roads], rfl⟩ le_rfl))
    (consistent_hStar.admissible roads.initial)

/-- With no goal state, the optimal cost-to-go is `⊤`. -/
example : ({ roads with isGoal := fun _ => false } : Problem V V).costToGo .s = ⊤ := by
  simp [Problem.costToGo]

/-- `h₂` is admissible: it is below the consistent `hStar`. -/
theorem admissible_h₂ : roads.Admissible h₂ := fun v =>
  le_trans (by cases v <;> decide) (consistent_hStar.admissible v)

theorem not_consistent_h₂ : ¬ roads.Consistent h₂ := fun hc =>
  absurd (hc.le_stepCost_add .a .b (by decide)) (by decide)

theorem not_admissible_h₃ : ¬ roads.Admissible h₃ := fun hadm =>
  absurd (Problem.admissible_iff.1 hadm .a [.b, .c, .g] .g (by simp [roads]) rfl) (by decide)

/-! ### Runs of A* tree search -/

theorem aStarTreeSearch_h₁ : aStarTreeSearch roads h₁ F 50 = some ⟨.g, [.a, .b, .c, .g], 7⟩ := by
  decide

/-- An admissible but inconsistent heuristic still leads A* tree search to the cheapest
solution. -/
example : aStarTreeSearch roads h₂ F 50 = some ⟨.g, [.a, .b, .c, .g], 7⟩ := by decide

/-- An inadmissible heuristic leads A* tree search to a costlier solution. -/
example : aStarTreeSearch roads h₃ F 50 = some ⟨.g, [.b, .c, .g], 8⟩ := by decide

/-- Uniform-cost tree search finds the cheapest solution. -/
example : bestFirstTreeSearch roads F (·.cost) 50 = some ⟨.g, [.a, .b, .c, .g], 7⟩ := by decide

/-! ### Optimality -/

/-- The optimality theorem applies to every run of A* tree search with `h₁`. -/
example (fuel : ℕ) {x : Node V V} (hx : aStarTreeSearch roads h₁ F fuel = some x) :
    roads.IsOptimalSolution x.path :=
  aStarTreeSearch_isOptimalSolution Frontier.lawful_sortedList consistent_h₁.admissible fuel hx

/-- From the run and the optimality theorem: `a, b, c, g` is an optimal solution. -/
theorem isOptimalSolution_abcg : roads.IsOptimalSolution [.a, .b, .c, .g] :=
  aStarTreeSearch_isOptimalSolution Frontier.lawful_sortedList consistent_h₁.admissible 50
    aStarTreeSearch_h₁

/-- The solution found with the inadmissible `h₃` is not optimal. -/
example : ¬ roads.IsOptimalSolution [.b, .c, .g] := fun h =>
  absurd (h.2 _ isOptimalSolution_abcg.1) (by decide)

/-- Uniform-cost tree search returns optimal solutions. -/
example (fuel : ℕ) {x : Node V V} (hx : bestFirstTreeSearch roads F (·.cost) fuel = some x) :
    roads.IsOptimalSolution x.path :=
  uniformCostTreeSearch_isOptimalSolution Frontier.lawful_sortedList fuel hx

/-! ### The query program -/

/-- A*'s priority `g + h`, asking for the heuristic. -/
abbrev aStarPrio (x : Node V V) : FreeM (SearchQuery V V) ℕ :=
  (x.cost + ·) <$> FreeM.lift (.heuristic x.state)

/-- Evaluated against the oracle of `roads` with heuristic `h`, the query program of A* is A*
tree search with `h`. -/
example (h : V → ℕ) (fuel : ℕ) :
    (bestFirstTreeSearchQ F aStarPrio fuel roads.initial).eval (roads.oracle h) =
      aStarTreeSearch roads h F fuel := by
  simp

/-- With `h₁`, A* tree search expands four nodes, those of `s, a, b, c`; uniform-cost tree search
expands `33`. -/
example : (bestFirstTreeSearchQ F aStarPrio 50 .s).cost (roads.oracle h₁)
    SearchQuery.expansionWeight = 4 := by
  decide

example : (bestFirstTreeSearchQ F (fun x => pure x.cost) 50 .s).cost (roads.oracle h₁)
    SearchQuery.expansionWeight = 33 := by
  decide +kernel

end CslibFrontierTests.Algorithms.Lean.Search.AStar
