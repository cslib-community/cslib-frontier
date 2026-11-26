/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

import CslibFrontier.Logics.Propositional.CuttingPlanes.Completeness
import CslibFrontier.Logics.Propositional.PseudoBoolean.CuttingPlanes

/-!
# Tests: refutation completeness of cutting planes

A `module` client of the public API. It refutes a system with a fractional solution but no 0/1
solution, an infinite system, and the unsatisfiable cardinality constraints
`x₀ + x₁ + x₂ ≥ 2` and `¬x₀ + ¬x₁ + ¬x₂ ≥ 2`; and it shows that a satisfiable list of
constraints is not refutable.
-/

-- A test client exports nothing: its declarations are examples and a private fixture.
set_option linter.privateModule false

namespace CslibFrontierTests.ProofComplexity.CuttingPlanesCompleteness

open Cslib.Logic.PL Cslib.Logic.PL.CuttingPlanes

/-! ### Systems of inequalities -/

/-- `2 x ≥ 1` and `-2 x ≥ -1` over one variable: `x = 1/2` satisfies both, but no 0/1 point
does, so cutting planes refute them. -/
example : ∃ s, RefutableInSize
    {(⟨Finsupp.single () 2, 1⟩ : Ineq Unit), ⟨Finsupp.single () (-2), -1⟩} s := by
  refine exists_refutableInSize_of_not_exists_holds fun ⟨σ, hσ⟩ => ?_
  have h₁ := hσ _ (Set.mem_insert _ _)
  have h₂ := hσ _ (Set.mem_insert_of_mem _ rfl)
  simp only [Ineq.Holds, Ineq.lhs_mk_single] at h₁ h₂
  revert h₁ h₂
  cases σ () <;> decide

/-- The infinite system of all `xₙ ≥ 1` together with `-x₀ ≥ 0` is refutable. -/
example : ∃ s, RefutableInSize
    ({I | ∃ n : ℕ, I = ⟨Finsupp.single n 1, 1⟩} ∪ {⟨Finsupp.single 0 (-1), 0⟩}) s := by
  refine exists_refutableInSize_of_not_exists_holds fun ⟨σ, hσ⟩ => ?_
  have h₁ := hσ _ (Or.inl ⟨0, rfl⟩)
  have h₂ := hσ _ (Or.inr rfl)
  simp only [Ineq.Holds, Ineq.lhs_mk_single] at h₁ h₂
  revert h₁ h₂
  cases σ 0 <;> decide

/-! ### Pseudo-Boolean constraints -/

/-- `x₀ + x₁ + x₂ ≥ 2` and `¬x₀ + ¬x₁ + ¬x₂ ≥ 2`. -/
private def card : List PBConstr :=
  [⟨[(1, (0, true)), (1, (1, true)), (1, (2, true))], 2⟩,
    ⟨[(1, (0, false)), (1, (1, false)), (1, (2, false))], 2⟩]

/-- No 0/1 assignment satisfies both cardinality constraints, so their inequalities are
refutable. -/
example : ∃ s, RefutableInSize {I | ∃ c ∈ card, c.toIneq = I} s := by
  refine PBConstr.exists_refutableInSize_toIneq_iff.2 fun ⟨σ, hσ⟩ => ?_
  have h₁ := hσ _ List.mem_cons_self
  have h₂ := hσ _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [PBConstr.Holds, PBConstr.lhs, PBConstr.termVal, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Literal.eval_mk, one_mul] at h₁ h₂
  revert h₁ h₂
  cases σ 0 <;> cases σ 1 <;> cases σ 2 <;> decide

/-- `x₀ + x₁ ≥ 1` alone is satisfiable, so its inequality has no cutting planes refutation. -/
example : ¬ ∃ s, RefutableInSize
    {I | ∃ c ∈ [(⟨[(1, (0, true)), (1, (1, true))], 1⟩ : PBConstr)], c.toIneq = I} s := by
  rw [PBConstr.exists_refutableInSize_toIneq_iff, not_not]
  exact ⟨fun _ => true, fun c hc => by
    rw [List.mem_singleton.1 hc]
    decide⟩

end CslibFrontierTests.ProofComplexity.CuttingPlanesCompleteness
