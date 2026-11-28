/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Search.Uninformed

/-!
# Tests for uninformed search

Two problems:

* a graph on `ℕ` whose actions are target states, `0 → 4, 1` and `1 → 2 → 3 → 4`, with goal `4`:
  depth-first search follows the long branch `1, 2, 3, 4` first, while breadth-first search and
  iterative deepening find the one-action solution;
* the infinite number problem: from `1`, reach `6` by `inc` (`s ↦ s + 1`) and `dbl`
  (`s ↦ 2 * s`). Its shortest solutions have three actions.

Checked by `decide`:

* breadth-first search and iterative deepening find a shortest solution and agree on its length;
  depth-limited search with a generous limit returns a longer one, with a small limit cuts the
  long branch off, and with limit `0` returns nothing;
* the query programs evaluate to the pure algorithms;
* exact expansion counts, below the bounds `∑ i < ℓ, b ^ i`.

Instances of the completeness, soundness and cost theorems show their hypotheses are satisfiable;
combining depth-limited completeness with a run that returns `none` proves that the number
problem has no solution of two actions or fewer.
-/

namespace CslibFrontierTests.Algorithms.Lean.Search.Uninformed

open Cslib Cslib.Algorithms.Lean.Search

/-- A graph on `ℕ` whose actions are the target states: `0 → 4, 1`, `1 → 2 → 3 → 4`, goal `4`. -/
def graphProblem : Problem ℕ ℕ where
  initial := 0
  actions s := if s = 0 then [4, 1] else if s < 4 then [s + 1] else []
  result _ t := t
  isGoal s := s == 4
  stepCost _ _ := 1

/-- The two moves of the number problem. -/
inductive Move
  | inc
  | dbl
  deriving DecidableEq

/-- From `1`, reach `6` by `s ↦ s + 1` (cost `1`) and `s ↦ 2 * s` (cost `2`). -/
def numberProblem : Problem ℕ Move where
  initial := 1
  actions _ := [.inc, .dbl]
  result s
    | .inc => s + 1
    | .dbl => 2 * s
  isGoal s := s == 6
  stepCost _
    | .inc => 1
    | .dbl => 2

/-- The sorted-list frontier for breadth-first search, keyed by depth. -/
abbrev FB (S A : Type) : Frontier (SortedListFrontier ℕ (Node S A)) ℕ (Node S A) :=
  Frontier.sortedList

/-- The sorted-list frontier for depth-limited search, keyed by negative depth. -/
abbrev FD (S A : Type) :
    Frontier (SortedListFrontier ℕᵒᵈ (Node (S × ℕ) A)) ℕᵒᵈ (Node (S × ℕ) A) :=
  Frontier.sortedList

theorem graphProblem_actions_length_le (s : ℕ) : (graphProblem.actions s).length ≤ 2 := by
  simp only [graphProblem]
  split_ifs <;> simp

/-! ### The depth-limited problem -/

/-- At the depth limit there are no actions. -/
example : (graphProblem.depthLimited 2).actions (1, 2) = [] := by decide

example : (graphProblem.depthLimited 2).actions (1, 1) = [2] := by decide

/-- The long branch is a solution, but not one of at most three actions. -/
example : graphProblem.IsSolution [1, 2, 3, 4] := ⟨4, by simp [graphProblem], rfl⟩

example : ¬ (graphProblem.depthLimited 3).IsSolution [1, 2, 3, 4] := by
  simp [Problem.depthLimited_isSolution_iff]

/-! ### Runs on the graph -/

/-- Breadth-first search finds the one-action solution. -/
example : (breadthFirstTreeSearch graphProblem (FB _ _) 10).map (·.path) = some [4] := by decide

/-- Depth-limited search with a generous limit follows the long branch first. -/
example : (depthLimitedSearch graphProblem (FD _ _) 5 20).map (·.path) = some [1, 2, 3, 4] := by
  decide

/-- With limit `3` the long branch is cut off at state `3`, and the search backtracks to `4`. -/
example : (depthLimitedSearch graphProblem (FD _ _) 3 20).map (·.path) = some [4] := by decide

/-- With limit `0` only the root is tested. -/
example : depthLimitedSearch graphProblem (FD _ _) 0 20 = none := by decide

/-- Iterative deepening agrees with breadth-first search. -/
example : (iterativeDeepeningSearch graphProblem (FD _ _) 5 20).map (·.path) = some [4] := by
  decide

/-! ### Runs on the infinite number problem -/

/-- Breadth-first search and iterative deepening find three-action solutions. -/
example : (breadthFirstTreeSearch numberProblem (FB _ _) 50).map (·.path) =
    some [.dbl, .inc, .dbl] := by
  decide

example : (iterativeDeepeningSearch numberProblem (FD _ _) 5 50).map (·.path) =
    some [.dbl, .inc, .dbl] := by
  decide

/-- Depth-limited search with limit `4` returns a four-action solution: it is not optimal. -/
example : (depthLimitedSearch numberProblem (FD _ _) 4 50).map (·.path) =
    some [.dbl, .dbl, .inc, .inc] := by
  decide

/-- Depth-limited search with limit `2` exhausts the depth-limited tree within its fuel. -/
theorem depthLimitedSearch_numberProblem_two :
    depthLimitedSearch numberProblem (FD _ _) 2 7 = none := by
  decide

/-- **No solution of two actions or fewer**, from depth-limited completeness with branching
factor `2` and fuel `1 + 2 + 4`, and the run above. -/
example {sol : List Move} (h : numberProblem.IsSolution sol) : 3 ≤ sol.length := by
  by_contra hlt
  obtain ⟨x, hx, -⟩ := depthLimitedSearch_complete (F := FD _ _) Frontier.lawful_sortedList
    (b := 2) (fun _ => le_rfl) h (ℓ := 2) (by omega) (fuel := 7) (by decide)
  rw [depthLimitedSearch_numberProblem_two] at hx
  cases hx

/-! ### Completeness, optimality and soundness instances -/

example : ∃ x, breadthFirstTreeSearch numberProblem (FB _ _) 15 = some x ∧
    numberProblem.IsSolution x.path ∧
      ∀ sol', numberProblem.IsSolution sol' → x.path.length ≤ sol'.length :=
  breadthFirstTreeSearch_complete Frontier.lawful_sortedList (b := 2) (fun _ => le_rfl)
    (sol := [.inc, .inc, .dbl]) ⟨6, by simp [numberProblem], rfl⟩ (by decide)

example : ∃ x, iterativeDeepeningSearch numberProblem (FD _ _) 3 15 = some x ∧
    numberProblem.IsSolution x.path ∧
      ∀ sol', numberProblem.IsSolution sol' → x.path.length ≤ sol'.length :=
  iterativeDeepeningSearch_complete Frontier.lawful_sortedList (b := 2) (fun _ => le_rfl)
    (sol := [.inc, .inc, .dbl]) ⟨6, by simp [numberProblem], rfl⟩ le_rfl (by decide)

example : ∃ x, depthLimitedSearch graphProblem (FD _ _) 3 15 = some x ∧
    graphProblem.IsSolution x.path ∧ x.path.length ≤ 3 :=
  depthLimitedSearch_complete Frontier.lawful_sortedList graphProblem_actions_length_le
    (sol := [4]) ⟨4, by simp [graphProblem], rfl⟩ (by decide) (by decide)

/-- Breadth-first search's answer on the graph is at most as long as the long branch. -/
example {x : Node ℕ ℕ} (h : breadthFirstTreeSearch graphProblem (FB _ _) 10 = some x) :
    x.path.length ≤ 4 :=
  breadthFirstTreeSearch_length_le Frontier.lawful_sortedList graphProblem 10 h
    (sol := [1, 2, 3, 4]) ⟨4, by simp [graphProblem], rfl⟩

example {x : Node ℕ ℕ} (h : depthLimitedSearch graphProblem (FD _ _) 5 20 = some x) :
    graphProblem.IsSolution x.path ∧ x.path.length ≤ 5 :=
  have h' := depthLimitedSearch_sound Frontier.lawful_sortedList graphProblem 5 20 h
  ⟨⟨x.state, h'.1, h'.2.1⟩, h'.2.2.2⟩

example {x : Node ℕ Move} (h : iterativeDeepeningSearch numberProblem (FD _ _) 5 50 = some x) :
    numberProblem.pathCost numberProblem.initial x.path = x.cost :=
  (iterativeDeepeningSearch_sound Frontier.lawful_sortedList numberProblem 5 50 h).2.2.1

/-! ### The query programs -/

/-- The oracle of the number problem, with the heuristic `6 - s`. -/
abbrev oracle : {ι : Type} → SearchQuery ℕ Move ι → ι := numberProblem.oracle fun s => 6 - s

example (fuel : ℕ) :
    (breadthFirstTreeSearchQ (FB _ _) fuel numberProblem.initial).eval oracle =
      breadthFirstTreeSearch numberProblem (FB _ _) fuel := by
  simp

example (ℓ fuel : ℕ) :
    (depthLimitedSearchQ (FD _ _) ℓ fuel numberProblem.initial).eval oracle =
      depthLimitedSearch numberProblem (FD _ _) ℓ fuel := by
  simp

example (maxDepth fuel : ℕ) :
    (iterativeDeepeningSearchQ (FD _ _) maxDepth fuel numberProblem.initial).eval oracle =
      iterativeDeepeningSearch numberProblem (FD _ _) maxDepth fuel := by
  simp

/-! ### Expansion counts -/

/-- Depth-limited search on the graph expands `0, 1, 2, 3` and tests `4`. -/
example : (depthLimitedSearchQ (FD _ _) 5 20 graphProblem.initial).cost (graphProblem.oracle 0)
    SearchQuery.expansionWeight = 4 := by
  decide

/-- Iterative deepening expands nothing at limit `0` and only the root at limit `1`. -/
example : (iterativeDeepeningSearchQ (FD _ _) 5 20 graphProblem.initial).cost
    (graphProblem.oracle 0) SearchQuery.expansionWeight = 1 := by
  decide

/-- On the number problem, depth-limited search with limit `2` expands the `3` nodes of depth
less than `2`, and with limit `4` it expands `5` nodes before finding a solution. -/
example : (depthLimitedSearchQ (FD _ _) 2 100 numberProblem.initial).cost oracle
    SearchQuery.expansionWeight = 3 := by
  decide

example : (depthLimitedSearchQ (FD _ _) 4 100 numberProblem.initial).cost oracle
    SearchQuery.expansionWeight = 5 := by
  decide

/-- The expansion bound for depth-limited search with branching factor `2`. -/
example (ℓ fuel : ℕ) :
    (depthLimitedSearchQ (FD _ _) ℓ fuel numberProblem.initial).cost oracle
      SearchQuery.expansionWeight ≤ ∑ i ∈ Finset.range ℓ, 2 ^ i :=
  cost_expansionWeight_depthLimitedSearchQ_le Frontier.lawful_sortedList numberProblem _
    (fun _ => le_rfl) ℓ fuel

/-- The expansion bound for iterative deepening search with branching factor `2`. -/
example (maxDepth fuel : ℕ) :
    (iterativeDeepeningSearchQ (FD _ _) maxDepth fuel graphProblem.initial).cost
      (graphProblem.oracle 0) SearchQuery.expansionWeight ≤
      ∑ ℓ ∈ Finset.range (maxDepth + 1), ∑ i ∈ Finset.range ℓ, 2 ^ i :=
  cost_expansionWeight_iterativeDeepeningSearchQ_le Frontier.lawful_sortedList graphProblem _
    graphProblem_actions_length_le maxDepth fuel

/-- Breadth-first search inherits the expansion bound of best-first search. -/
example (fuel : ℕ) :
    (breadthFirstTreeSearchQ (FB _ _) fuel numberProblem.initial).cost oracle
      SearchQuery.expansionWeight ≤ fuel :=
  cost_expansionWeight_bestFirstTreeSearchQ_le oracle _ (fun _ => rfl) fuel _

end CslibFrontierTests.Algorithms.Lean.Search.Uninformed
