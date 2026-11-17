/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.Approximation.AssignmentGraph

/-! Checked instances of the assignment graph of Arora–Barak, Lemma 18.16: a clause with three
distinct variables has seven local satisfying assignments, a clause with a repeated variable has
fewer, and on the formula `x ∧ ¬x` the graph has fourteen vertices and independence number
`val · 14 / 7 = 1`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.AssignmentGraph

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.SAT

/-- `x₁ ∨ ¬x₂ ∨ x₃` has the seven local satisfying assignments of three distinct variables. -/
example : (clauseAssignments [(1, true), (2, false), (3, true)]).length = 7 := by decide

/-- `x₁ ∨ x₁ ∨ ¬x₂` has three: the satisfying assignments of its two variables. -/
example : (clauseAssignments [(1, true), (1, true), (2, false)]).length = 3 := by decide

/-- The tautology `x₁ ∨ ¬x₁` has two local satisfying assignments, each listed twice: the values
are drawn for three positions and the clause reads only two of them. -/
example : (clauseAssignments [(1, true), (1, false)]) =
    [[(1, false), (1, false)], [(1, true), (1, true)],
      [(1, false), (1, false)], [(1, true), (1, true)]] := by decide

/-- The formula `x₀ ∧ ¬x₀` gives a graph with fourteen vertices. -/
example : (assignmentGraph [[(0, true)], [(0, false)]]).vertices.toFinset.card = 14 :=
  (card_toFinset_vertices_assignmentGraph (by decide)).trans rfl

/-- The independence number of the graph of `x₀ ∧ ¬x₀` is `val · n / 7`, with the value `1 / 2`
of the formula: at most one of its two clauses holds. -/
example : ((assignmentGraph [[(0, true)], [(0, false)]]).indepNum : ℝ) =
    (1 - CNF.unsatVal [[(0, true)], [(0, false)]]) *
      (assignmentGraph [[(0, true)], [(0, false)]]).vertices.toFinset.card / 7 :=
  indepNum_assignmentGraph (by decide)

end CslibFrontierTests.AssignmentGraph
