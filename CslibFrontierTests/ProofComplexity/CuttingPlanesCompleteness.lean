/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

import CslibFrontier.Logics.Propositional.CuttingPlanes.Completeness
import CslibFrontier.Logics.Propositional.PseudoBoolean.CuttingPlanes
import Mathlib.Algebra.BigOperators.Fin

/-!
# Tests: completeness of cutting planes

A `module` client of the public API. It refutes a system with a fractional solution but no 0/1
solution, an infinite system, and the unsatisfiable cardinality constraints
`x₀ + x₁ + x₂ ≥ 2` and `¬x₀ + ¬x₁ + ¬x₂ ≥ 2`; and it shows that a satisfiable list of
constraints is not refutable. For implicational completeness, it derives `x₁ ≥ 1` from
`x₀ + x₁ ≥ 1` and `¬x₀ + x₁ ≥ 1`, the non-unit `3 x₀ + 2 x₁ + x₂ ≥ 3` from "two of three", and a
pseudo-Boolean consequence; and it checks that over no variables the empty system does not
derive the implied `0 ≥ 0`, so the hypothesis `Nonempty V` is needed.
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

/-! ### Implicational completeness -/

/-- Resolution as a derivation: `x₀ + x₁ ≥ 1` and `¬x₀ + x₁ ≥ 1` (that is `-x₀ + x₁ ≥ 0`) derive
`x₁ ≥ 1`. -/
example : ∃ s, DerivableInSize
    {(⟨Finsupp.single 0 1 + Finsupp.single 1 1, 1⟩ : Ineq (Fin 2)),
      ⟨Finsupp.single 0 (-1) + Finsupp.single 1 1, 0⟩}
    ⟨Finsupp.single 1 1, 1⟩ s := by
  refine exists_derivableInSize_of_forall_holds fun σ hσ => ?_
  have h₁ := hσ _ (Set.mem_insert _ _)
  have h₂ := hσ _ (Set.mem_insert_of_mem _ rfl)
  simp only [Ineq.Holds, Ineq.lhs_eq_sum, Fin.sum_univ_two, Finsupp.add_apply,
    Finsupp.single_apply] at h₁ h₂ ⊢
  revert h₁ h₂
  cases σ 0 <;> cases σ 1 <;> decide

/-- A non-unit consequence: if two of `x₀, x₁, x₂` hold, then `3 x₀ + 2 x₁ + x₂ ≥ 3`. -/
example : ∃ s, DerivableInSize
    {(⟨Finsupp.single 0 1 + Finsupp.single 1 1, 1⟩ : Ineq (Fin 3)),
      ⟨Finsupp.single 1 1 + Finsupp.single 2 1, 1⟩, ⟨Finsupp.single 0 1 + Finsupp.single 2 1, 1⟩}
    ⟨Finsupp.single 0 3 + Finsupp.single 1 2 + Finsupp.single 2 1, 3⟩ s := by
  refine exists_derivableInSize_of_forall_holds fun σ hσ => ?_
  have h₁ := hσ _ (Set.mem_insert _ _)
  have h₂ := hσ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have h₃ := hσ _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  simp only [Ineq.Holds, Ineq.lhs_eq_sum, Fin.sum_univ_three, Finsupp.add_apply,
    Finsupp.single_apply] at h₁ h₂ h₃ ⊢
  revert h₁ h₂ h₃
  cases σ 0 <;> cases σ 1 <;> cases σ 2 <;> decide

/-- Pseudo-Boolean constraints: `x₀ + x₁ ≥ 1` and `¬x₀ ≥ 1` derive `2 x₁ ≥ 1`. -/
example : ∃ s, DerivableInSize
    {I | ∃ c ∈ [(⟨[(1, (0, true)), (1, (1, true))], 1⟩ : PBConstr), ⟨[(1, (0, false))], 1⟩],
      c.toIneq = I}
    (⟨[(2, (1, true))], 1⟩ : PBConstr).toIneq s := by
  refine PBConstr.exists_derivableInSize_toIneq_iff.2 fun σ hσ => ?_
  have h₁ := hσ _ List.mem_cons_self
  have h₂ := hσ _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [PBConstr.Holds, PBConstr.lhs, PBConstr.termVal, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Literal.eval_mk] at h₁ h₂ ⊢
  revert h₁ h₂
  cases σ 0 <;> cases σ 1 <;> decide

/-- Over no variables, the empty system derives nothing, not even the implied `0 ≥ 0`: the
hypothesis `Nonempty V` of implicational completeness cannot be dropped. -/
example : ¬ ∃ s, DerivableInSize (∅ : Set (Ineq Empty)) 0 s := by
  rintro ⟨s, ls, h, hI, -⟩
  have hnil (ls : List (Ineq Empty)) (h : IsProof ∅ ls) : ls = [] := by
    induction h with
    | nil => rfl
    | hyp _ hJ => exact absurd hJ (Set.notMem_empty _)
    | nonneg _ v => exact v.elim
    | leOne _ v => exact v.elim
    | add _ hJ _ ih => simp [ih] at hJ
    | smul _ _ _ hJ ih => simp [ih] at hJ
    | div _ _ _ _ hJ ih => simp [ih] at hJ
  simp [hnil ls h] at hI

end CslibFrontierTests.ProofComplexity.CuttingPlanesCompleteness
