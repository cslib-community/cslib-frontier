/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Search.BestFirst

/-!
# Tests for best-first tree search

A problem on the infinite state space `ℕ`: from `1`, reach `6` by the actions `inc` (`s ↦ s + 1`,
cost `1`) and `dbl` (`s ↦ 2 * s`, cost `2`). Its cheapest solution is `inc, inc, dbl` of cost
`4`; its shortest solutions have three actions.

* Paths, applicability, solutions, successors and reachability on the problem and on a problem
  whose actions depend on the state, so that an inapplicable action is rejected.
* Uniform-cost priority (`g`) finds the cost-`4` solution; depth priority finds a three-action
  solution; constant priority with the sorted-list frontier's tie-breaking is depth-first and
  follows `dbl` forever, returning `none` within the fuel.
* Boundary runs: no fuel; a goal at the root; a frontier that empties.
* The query program agrees with the pure algorithm (`eval_bestFirstTreeSearchQ`), including an
  A*-style priority that asks for the heuristic.
* Exact expansion and generation counts on a run, and instances of the expansion and generation
  bounds and of soundness, showing their hypotheses are satisfiable.
-/

namespace CslibFrontierTests.Algorithms.Lean.Search.BestFirst

open Cslib Cslib.Algorithms.Lean.Search

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

/-- The sorted-list frontier of the number problem's nodes, keyed by `ℕ`. -/
abbrev F : Frontier (SortedListFrontier ℕ (Node ℕ Move)) ℕ (Node ℕ Move) := Frontier.sortedList

/-! ### Paths and solutions -/

example : numberProblem.IsSolution [.inc, .inc, .dbl] := ⟨6, by simp [numberProblem], rfl⟩

example : numberProblem.pathCost numberProblem.initial [.inc, .inc, .dbl] = 4 := by decide

example : ¬ numberProblem.IsSolution [.dbl, .dbl] := by
  simp [Problem.IsSolution, numberProblem]

/-- Only `inc` is applicable, and only below `3`. -/
def boundedProblem : Problem ℕ Move where
  initial := 0
  actions s := if s < 3 then [.inc] else []
  result s
    | .inc => s + 1
    | .dbl => 2 * s
  isGoal s := s == 3
  stepCost _ _ := 1

/-- `dbl` would lead from `0` to `0`, but it is not applicable. -/
example : ¬ boundedProblem.toLTS.MTr 0 [.dbl] 0 := by simp [boundedProblem]

example : boundedProblem.IsSolution [.inc, .inc, .inc] := ⟨3, by simp [boundedProblem], rfl⟩

/-- `inc` stops being applicable at `3`. -/
example : ¬ boundedProblem.toLTS.MTr 0 [.inc, .inc, .inc, .inc] 4 := by simp [boundedProblem]

/-- The successor relation and reachability are those of the problem's transition system. -/
example : boundedProblem.toLTS.UnlabelledTr 2 3 := ⟨.inc, by simp [boundedProblem]⟩

example : numberProblem.toLTS.CanReach 1 6 := ⟨[.inc, .inc, .dbl], by simp [numberProblem]⟩

/-! ### Runs of the pure algorithm -/

/-- Uniform-cost priority finds the cheapest solution. -/
example : (bestFirstTreeSearch numberProblem F (·.cost) 50).map (fun x => (x.path, x.cost)) =
    some ([.inc, .inc, .dbl], 4) := by
  decide

/-- Depth priority finds a three-action solution. -/
example : (bestFirstTreeSearch numberProblem F (·.path.length) 50).map (fun x => (x.path, x.cost)) =
    some ([.dbl, .inc, .dbl], 5) := by
  decide

/-- Constant priority pops the newest child first, so the search is depth-first; it follows `dbl`
through `1, 2, 4, 8, …` and never reaches `6`. -/
example : bestFirstTreeSearch numberProblem F (fun _ => 0) 50 = none := by decide

/-- Without fuel the search returns nothing. -/
example : bestFirstTreeSearch numberProblem F (·.cost) 0 = none := by decide

/-- A goal at the root is returned with the empty path at cost `0`. -/
example : bestFirstTreeSearch { boundedProblem with initial := 3 } F (·.cost) 1 =
    some ⟨3, [], 0⟩ := by
  decide

/-- With an unreachable goal, the frontier empties after the four states `0, …, 3` are expanded. -/
example : bestFirstTreeSearch { boundedProblem with isGoal := fun _ => false } F (·.cost) 50 =
    none := by
  decide

/-! ### Soundness -/

/-- The search's answer is a solution, at the reported cost. -/
example {x : Node ℕ Move} (h : bestFirstTreeSearch numberProblem F (·.cost) 50 = some x) :
    numberProblem.IsSolution x.path ∧
      numberProblem.pathCost numberProblem.initial x.path = x.cost :=
  have h' := bestFirstTreeSearch_sound Frontier.lawful_sortedList numberProblem _ 50 h
  ⟨⟨x.state, h'.1, h'.2.1⟩, h'.2.2⟩

/-! ### The query program -/

/-- The oracle of the number problem, with the heuristic `6 - s`. -/
abbrev oracle : {ι : Type} → SearchQuery ℕ Move ι → ι := numberProblem.oracle fun s => 6 - s

/-- The query program with a pure priority evaluates to the pure algorithm. -/
example (fuel : ℕ) :
    (bestFirstTreeSearchQ F (fun x => pure x.cost) fuel numberProblem.initial).eval oracle =
      bestFirstTreeSearch numberProblem F (·.cost) fuel := by
  simp

/-- A priority asking for the heuristic, `g + h`, evaluates to the pure priority `g + h`. -/
example (fuel : ℕ) :
    (bestFirstTreeSearchQ F (fun x => (x.cost + ·) <$> FreeM.lift (.heuristic x.state)) fuel
        numberProblem.initial).eval oracle =
      bestFirstTreeSearch numberProblem F (fun x => x.cost + (6 - x.state)) fuel := by
  simp [oracle]

/-- The uniform-cost run expands `11` nodes and generates `22`. -/
example :
    (bestFirstTreeSearchQ F (fun x => pure x.cost) 50 1).cost oracle
      SearchQuery.expansionWeight = 11 := by
  decide

example :
    (bestFirstTreeSearchQ F (fun x => pure x.cost) 50 1).cost oracle
      SearchQuery.generationWeight = 22 := by
  decide

/-- The expansion bound applies to a pure priority. -/
example (fuel init : ℕ) :
    (bestFirstTreeSearchQ F (fun x => pure x.cost) fuel init).cost oracle
      SearchQuery.expansionWeight ≤ fuel :=
  cost_expansionWeight_bestFirstTreeSearchQ_le oracle _ (fun _ => rfl) fuel init

/-- The expansion bound applies to a priority asking for the heuristic. -/
example (fuel init : ℕ) :
    (bestFirstTreeSearchQ F (fun x => (x.cost + ·) <$> FreeM.lift (.heuristic x.state)) fuel
        init).cost oracle SearchQuery.expansionWeight ≤ fuel :=
  cost_expansionWeight_bestFirstTreeSearchQ_le oracle _
    (fun _ => by simp [SearchQuery.expansionWeight]) fuel init

/-- Every state has two actions, so the search generates at most `2 * fuel` nodes. -/
example (fuel init : ℕ) :
    (bestFirstTreeSearchQ F (fun x => pure x.cost) fuel init).cost oracle
      SearchQuery.generationWeight ≤ fuel * 2 :=
  cost_generationWeight_bestFirstTreeSearchQ_le oracle _ (fun _ => rfl) (fun _ => le_rfl) fuel
    init

end CslibFrontierTests.Algorithms.Lean.Search.BestFirst
