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
fewer, and on the formula `x ∧ ¬x` the contract of the lemma gives fourteen vertices and
independence number `val · 14 / 7 = 1`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.AssignmentGraph

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.SAT Turing.MultiTapeTM

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

/-- Every assignment falsifies exactly one clause of `x₀ ∧ ¬x₀`, so its value is `1 / 2`. -/
private theorem unsatVal_x_and_not_x : CNF.unsatVal [[(0, true)], [(0, false)]] = 1 / 2 := by
  have hcount (σ : ℕ → Bool) : CNF.countUnsat σ [[(0, true)], [(0, false)]] = 1 := by
    cases h : σ 0 <;> simp [CNF.countUnsat, Clause.eval, Literal.eval, h]
  refine le_antisymm ?_ (CNF.le_unsatVal_iff _ |>.2 fun σ => ?_)
  · have := CNF.unsatVal_le [[(0, true)], [(0, false)]] (fun _ => true)
    rw [hcount] at this
    norm_num at this ⊢
    exact this
  · rw [hcount]
    norm_num

/-- **The contract of Lemma 18.16 fixes the independence number.** Any transformation with the
properties of `exists_computableInPolyTime_indepNum_eq` maps `x₀ ∧ ¬x₀` to a graph on
`7 · 2 = 14` vertices whose largest independent set has `val · 14 / 7 = 1` vertex. -/
example : ∃ f : CNF ℕ → Graph, ComputableInPolyTime f encCNF encGraph ∧
    (f [[(0, true)], [(0, false)]]).vertices.toFinset.card = 14 ∧
    (f [[(0, true)], [(0, false)]]).indepNum = 1 := by
  obtain ⟨f, hf, h⟩ := exists_computableInPolyTime_indepNum_eq
  obtain ⟨hcard, -, hval⟩ := h [[(0, true)], [(0, false)]] (by decide)
  have hn := hcard ⟨[(0, true)], by simp, by simp⟩
  refine ⟨f, hf, hn, ?_⟩
  rw [hn, unsatVal_x_and_not_x] at hval
  norm_num at hval
  exact_mod_cast hval

end CslibFrontierTests.AssignmentGraph
