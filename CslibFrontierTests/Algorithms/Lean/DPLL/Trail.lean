/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

import CslibFrontier.Algorithms.Lean.DPLL.Trail

/-! The DPLL search with an explicit trail: on small formulas the run of the steps ends with the
answer of the search without skipping, which is the solver's answer and model. -/

namespace CslibFrontierTests.Algorithms.Lean.DPLL.Trail

open Cslib.Logic.PL Cslib.Algorithms.Lean.DPLL

/-- Every clause over two variables: unsatisfiable. -/
def full : CNF ℕ :=
  [[(0, true), (1, true)], [(0, true), (1, false)], [(0, false), (1, true)],
    [(0, false), (1, false)]]

/-- `x2 ∨ x0`, `¬x0`: the unit clause `¬x0` forces `x2`. -/
def unitFirst : CNF ℕ := [[(2, true), (0, true)], [(0, false)]]

example : Trail.answer full = .unsat := by decide

example : Trail.run full 8 [] = some (Trail.answer full) := by decide

-- On `unitFirst` the search first propagates `¬x0`, then `x2`.
example : Trail.answer unitFirst = .sat [(2, true), (0, false)] := by decide

example : Trail.run unitFirst 8 [] = some (Trail.answer unitFirst) := by decide

/-- `x0 ∨ x1 ∨ ¬x0`: its variables occur in the order `0, 1, 0`. -/
def firstOccurrence : CNF ℕ := [[(0, true), (1, true), (0, false)]]

-- Without a unit clause the search branches on the variable that occurs first, `x0`, although
-- its last occurrence comes after that of `x1`.
example : nextLiteral firstOccurrence [] = (0, true) := by decide

example : Trail.answer firstOccurrence = .sat [(0, true)] := by decide

-- The run of the steps ends within `2 ^ (N + 1)` steps.
example : depth full = 2 ∧ (Trail.run full 7 []).isSome = true := by decide

-- The model of the solver is that of the partial assignment found.
example : (solve unitFirst).isSat = true ∧ (dfs unitFirst (depth unitFirst) []).isSome = true := by
  decide

end CslibFrontierTests.Algorithms.Lean.DPLL.Trail
