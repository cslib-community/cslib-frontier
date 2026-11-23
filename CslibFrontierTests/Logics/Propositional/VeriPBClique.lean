/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.Clique
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! Maximum clique under the ordinary imports of its API.

* `DimacsGraph.graph`: adjacency is decided, a listed loop is dropped and an edge counts in both
  directions.
* `encodeClique`, `chosen` and the correctness theorems `forall_holds_cliqueConstraints_iff`,
  `exists_chosen_eq` and `eval_cliqueObjective`, applied to the 5-cycle.
* `convConcl` on the boundary cases of CakePB's `conv_concl`: distinct bounds, `INF` on either
  side, `lb ≤ 0` (giving `u = n`), the empty graph, and a conclusion other than `BOUNDS`.
* The end-to-end theorems, applied to the acceptance of the proofs below.

The DIMACS reader, `printOPB` and the checkers have no exposed bodies;
`CslibFrontierTests.Logics.Propositional.VeriPBCliqueDecide` evaluates them in the kernel and
discharges the acceptance hypotheses here.
-/

@[expose] public section

namespace CslibFrontierTests.Logics.Propositional.VeriPBClique

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Graph

/-! ### DIMACS graphs -/

/-- The 5-cycle `1 - 2 - 3 - 4 - 5 - 1`. -/
def c5Text : String := "c the 5-cycle\np edge 5 5\ne 1 2\ne 2 3\ne 3 4\ne 4 5\ne 5 1\n"

/-- The 5-cycle as read: the vertex `u` of the file is `u - 1`. -/
def c5 : DimacsGraph := ⟨5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]⟩

/-- A triangle `1 2 3` with the pendant vertex `4` on `3`. -/
def k3pText : String := "p edge 4 4\ne 1 2\ne 2 3\ne 1 3\ne 3 4\n"

/-- The graph with no vertices. -/
def emptyText : String := "p edge 0 0\n"

-- An edge is adjacent in both directions, a loop is dropped, and a non-edge is not adjacent.
example : c5.graph.Adj ⟨0, by decide⟩ ⟨1, by decide⟩ ∧ c5.graph.Adj ⟨1, by decide⟩ ⟨0, by decide⟩ ∧
    ¬ c5.graph.Adj ⟨0, by decide⟩ ⟨2, by decide⟩ := by
  decide
example : ¬ (⟨3, [(0, 0)]⟩ : DimacsGraph).graph.Adj 0 0 := by decide
example : (⟨3, [(1, 0)]⟩ : DimacsGraph).graph.Adj 0 1 := by simp

/-! ### The encoding and its correctness -/

-- The 5-cycle read from DIMACS has the same constraints as Mathlib's: its five non-edges.
example : (encodeClique c5.graph).constraints =
    (encodeClique (SimpleGraph.cycleGraph 5)).constraints := by
  decide +kernel
example : (encodeClique c5.graph).constraints.length = 5 := by decide +kernel
example : (encodeClique c5.graph).objective = some (cliqueObjective 5) := rfl
-- The empty graph has no constraints, and the objective `0`.
example : (encodeClique (⊥ : SimpleGraph (Fin 0))).constraints = [] := by decide +kernel
example : cliqueObjective 0 = ⟨[], 0⟩ := rfl

/-- The assignment choosing the vertices `0` and `1` of the 5-cycle. -/
def σ01 (v : ℕ) : Bool := v < 2

example : chosen 5 σ01 = {0, 1} := by decide

-- It satisfies the encoding, so `{0, 1}` is a clique; its objective value is `5 - 2`.
example : c5.graph.IsClique (chosen 5 σ01 : Set (Fin 5)) :=
  (forall_holds_cliqueConstraints_iff _ σ01).1 (by decide +kernel)
example : (cliqueObjective 5).eval σ01 = 3 := by rw [eval_cliqueObjective]; decide
example : ∃ σ, chosen 5 σ = {1, 3} := exists_chosen_eq _

/-! ### Bounds from conclusions -/

-- `BOUNDS 3 : q 4` on 5 vertices: some clique has `1` vertex, none has more than `2`.
example : convConcl 5 (.bounds (some 3) 0 (some 4) none) = some (1, 2) := rfl
-- `INF` as the upper bound of the objective gives no clique, `INF` as the lower bound gives `0`.
example : convConcl 5 (.bounds (some 3) 0 none none) = some (0, 2) := rfl
example : convConcl 5 (.bounds none 0 none none) = some (0, 0) := rfl
-- A lower bound `lb ≤ 0` gives the trivial bound `u = n`.
example : convConcl 5 (.bounds (some (-2)) 0 (some 1) none) = some (4, 5) := rfl
example : convConcl 5 (.bounds (some 0) 0 (some 5) none) = some (0, 5) := rfl
-- The empty graph, and conclusions other than `BOUNDS`.
example : convConcl 0 (.bounds (some 0) 0 (some 0) none) = some (0, 0) := rfl
example : convConcl 5 (.unsat 0) = none := rfl
example : convConcl 5 .noClaim = none := rfl

/-! ### The end-to-end theorems -/

example {pbp : String} (h : checkCliqueGraph (SimpleGraph.cycleGraph 5) pbp = some (2, 2)) :
    (SimpleGraph.cycleGraph 5).cliqueNum = 2 :=
  cliqueNum_eq_of_checkCliqueGraph h

example {pbp : String} (h : checkClique c5Text pbp = some (1, 2)) :
    ∃ g, parseDIMACSGraph c5Text = some g ∧
      (∀ s : Finset (Fin g.n), g.graph.IsClique (s : Set (Fin g.n)) → s.card ≤ 2) ∧
      ∃ s : Finset (Fin g.n), g.graph.IsClique (s : Set (Fin g.n)) ∧ 1 ≤ s.card :=
  clique_bounds_of_checkClique h

example {pbp : String} (h : checkClique k3pText pbp = some (3, 3)) :
    ∃ g, parseDIMACSGraph k3pText = some g ∧ g.graph.cliqueNum = 3 :=
  cliqueNum_eq_of_checkClique h

end CslibFrontierTests.Logics.Propositional.VeriPBClique

end
