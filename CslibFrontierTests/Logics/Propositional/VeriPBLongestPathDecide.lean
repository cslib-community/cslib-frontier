/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

-- `import all`: the kernel evaluates `stepTop` and `runTop`, and the dynamic program `certify` with
-- its private helpers (`visit`, `live`, `dead`, `longest`, …), the proof log and the topological
-- sort, whose bodies are not exposed.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.DynamicProgramming
import all CslibFrontier.Logics.Propositional.PseudoBoolean.LongestPath
import all CslibFrontier.Algorithms.Lean.DFS.Basic
import all CslibFrontier.Algorithms.Lean.DFS.TopologicalSort
import Mathlib.Data.Fin.VecNotation

/-! A kernel-checked client of certified longest paths: the kernel runs the dynamic program and
the checker on a five-vertex DAG whose numbering is not a topological order, and the end-to-end
theorem turns the acceptance into the statement that the longest walk from `3` to `0` has length
`8`; for a target with no walk, it shows that there is none. -/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBLongestPathDecide

open Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.LongestPath

/-- The sources of the edges `3 → 1`, `1 → 0`, `3 → 2`, `2 → 0`, `1 → 2`, `0 → 4` and `4 → 2`. -/
def src : Fin 7 → Fin 5 := ![3, 1, 3, 2, 1, 0, 4]

/-- The targets of the edges. -/
def dst : Fin 7 → Fin 5 := ![1, 0, 2, 0, 2, 4, 2]

/-- The lengths of the edges. -/
def c : Fin 7 → ℕ := ![2, 3, 4, 1, 5, 2, 7]

/-- The graph is acyclic: positions in the order `3, 1, 0, 4, 2` increase along every edge. -/
theorem acyclic : Cslib.Relation.Acyclic fun u v => ∃ e, src e = u ∧ dst e = v := by
  have key : ∀ u v, Relation.TransGen (fun u v => ∃ e, src e = u ∧ dst e = v) u v →
      ![2, 1, 4, 0, 3] u < (![2, 1, 4, 0, 3] v : ℕ) := by
    intro u v h
    induction h with
    | single h => obtain ⟨e, rfl, rfl⟩ := h; revert e; decide
    | tail _ h ih => obtain ⟨e, rfl, rfl⟩ := h; exact ih.trans (by revert e; decide)
  exact ⟨fun v h => lt_irrefl _ (key v v h)⟩

/-- The checker accepts the proof of the dynamic program from `3` to `0`. -/
theorem accepted :
    checkRed (formula src dst 3 0) (some (negProfit c)) (certify src dst c 3 0).proof = true := by
  decide +kernel

theorem optimum_eq : (certify src dst c 3 0).optimum = some 8 := by decide +kernel

/-- **The longest walk from `3` to `0` has length `8`**: `3 → 1 → 2 → 0`. -/
theorem isGreatest :
    IsGreatest ((fun l => (l.map c).sum) '' {l | IsWalk src dst 3 l 0}) 8 :=
  (isGreatest_of_checkRed_certify acyclic accepted).1 8 optimum_eq

/-- **There is no walk from `4` to `1`.** -/
theorem no_walk (l : List (Fin 7)) : ¬ IsWalk src dst 4 l 1 :=
  (isGreatest_of_checkRed_certify acyclic (by decide +kernel)).2 (by decide +kernel) l

end CslibFrontierTests.Logics.Propositional.VeriPBLongestPathDecide
