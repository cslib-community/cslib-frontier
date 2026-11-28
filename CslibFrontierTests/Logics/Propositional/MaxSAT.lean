/-
Copyright (c) 2026 Matthew Doty, Nick L. Leppelmeier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Nick L. Leppelmeier
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.FineGrained.MaxSAT.Reduction
import CslibFrontier.Computability.Complexity.Problems.MaxTwoSAT
import CslibFrontier.Logics.Propositional.MaxSAT

/-!
# Weighted partial MaxSAT tests and checked clients

Checked clients covering:

1. A small weighted partial clausal MaxSAT instance with its optimum (`3`) computed by `decide`.
2. An infeasible clausal instance with unsatisfiable hard clauses (`optimum = ⊤`,
   `maxSatisfiedWeight = ⊥`).
3. A propositional MaxSAT instance containing a non-clause soft proposition `(a ∧ b) → c` of
   weight `2`, translated via both `PropMaxSAT.toTseitin` and `PropMaxSAT.toPlaistedGreenbaum`,
   confirming equal optima (`2`), clause size/width bounds, and a concrete Plaisted–Greenbaum
   feasible assignment whose cost strictly exceeds that of its atom restriction.
4. Smoke checks on the complexity bridges (`FineGrained.MaxSAT`, `ThresholdLanguage`,
   `MaxTwoSAT`), including an out-of-range variable boundary test for `toLogicMaxSAT`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.MaxSAT

open Cslib.Logic.PL Cslib.Logic.PL.Proposition Cslib.Logic.PL.MaxSAT

/-! ### Clausal weighted partial instances -/

/-- Hard clause `x₀ ∨ x₁`, soft unit clauses `¬x₀` (weight `5`), `¬x₁` (weight `3`), and
`x₁` (weight `2`). Minimizing cost forces `x₀ = false, x₁ = true` for cost `3`. -/
private def sampleClausal : MaxSAT (Fin 2) where
  hard := [[(0, true), (1, true)]]
  soft := [([(0, false)], 5), ([(1, false)], 3), ([(1, true)], 2)]

example : sampleClausal.computeOptimum = ((3 : ℕ) : WithTop ℕ) := by decide

example : sampleClausal.optimum = ((3 : ℕ) : WithTop ℕ) := by
  rw [← sampleClausal.computeOptimum_eq_optimum]
  decide

example : sampleClausal.maxSatisfiedWeight = ((7 : ℕ) : WithBot ℕ) := by
  refine (maxSatisfiedWeight_eq_coe_iff (t := 7)).2 ⟨⟨fun i => decide (i = 1), ?_, ?_⟩, ?_⟩
  · unfold feasible; decide
  · decide
  · intro σ hσ
    have hle : sampleClausal.optimum ≤ (sampleClausal.cost σ : WithTop ℕ) :=
      optimum_le_cost hσ
    have hopt : sampleClausal.optimum = ((3 : ℕ) : WithTop ℕ) := by
      rw [← sampleClausal.computeOptimum_eq_optimum]
      decide
    rw [hopt] at hle
    have hc : 3 ≤ sampleClausal.cost σ := WithTop.coe_le_coe.1 hle
    have hsum := sampleClausal.cost_add_satisfiedWeight σ
    have htot : sampleClausal.totalWeight = 10 := rfl
    omega

/-- An infeasible weighted partial instance (`hard := [x₀, ¬x₀]`). -/
private def infeasibleClausal : MaxSAT (Fin 1) where
  hard := [[(0, true)], [(0, false)]]
  soft := [([(0, true)], 4)]

example : infeasibleClausal.computeOptimum = ⊤ := by decide

example : infeasibleClausal.optimum = ⊤ := by
  rw [← infeasibleClausal.computeOptimum_eq_optimum]
  decide

example : infeasibleClausal.maxSatisfiedWeight = ⊥ :=
  infeasibleClausal.maxSatisfiedWeight_eq_bot_iff.2 (by
    rw [← infeasibleClausal.optimum_eq_top_iff, ← infeasibleClausal.computeOptimum_eq_optimum]
    decide)

/-! ### Propositional MaxSAT with a non-clause soft proposition -/

private abbrev a : Proposition (Fin 3) := .atom 0
private abbrev b : Proposition (Fin 3) := .atom 1
private abbrev c : Proposition (Fin 3) := .atom 2

/-- Hard constraints force `a = true` and `b = true`; soft propositions are the non-clause
implication `(a ∧ b) → c` with weight `2`, and `¬c` with weight `5`. The optimum falsifies
`(a ∧ b) → c` and pays `2`. -/
private def sampleProp : PropMaxSAT (Fin 3) where
  hard := [a, b]
  soft := [(.imp (.and a b) c, 2), (.neg c, 5)]

example : sampleProp.computeOptimum = ((2 : ℕ) : WithTop ℕ) := by decide

example : sampleProp.toTseitin.computeOptimum = ((2 : ℕ) : WithTop ℕ) := by decide

example : sampleProp.toPlaistedGreenbaum.computeOptimum = ((2 : ℕ) : WithTop ℕ) := by decide

example : sampleProp.optimum = ((2 : ℕ) : WithTop ℕ) := by
  rw [← sampleProp.computeOptimum_eq_optimum]
  decide

example : sampleProp.toTseitin.optimum = ((2 : ℕ) : WithTop ℕ) := by
  rw [sampleProp.optimum_toTseitin, ← sampleProp.computeOptimum_eq_optimum]
  decide

example : sampleProp.toPlaistedGreenbaum.optimum = ((2 : ℕ) : WithTop ℕ) := by
  rw [sampleProp.optimum_toPlaistedGreenbaum, ← sampleProp.computeOptimum_eq_optimum]
  decide

-- Plaisted–Greenbaum has strictly fewer hard clauses than Tseitin while preserving the optimum.
example : sampleProp.toPlaistedGreenbaum.hard.length < sampleProp.toTseitin.hard.length := by
  decide

example : ∀ cl ∈ sampleProp.toTseitin.hard, cl.length ≤ 3 :=
  fun _ hcl => sampleProp.length_le_three_of_mem_toTseitin_hard hcl

example : ∀ cl ∈ sampleProp.toPlaistedGreenbaum.hard, cl.length ≤ 3 :=
  fun _ hcl => sampleProp.length_le_three_of_mem_toPlaistedGreenbaum_hard hcl

-- In Plaisted–Greenbaum, setting auxiliary subformula variables artificially false can make the
-- translation's cost strictly exceed the atom restriction's cost.
private def extraCostPGAssignment : Fin 3 ⊕ Proposition (Fin 3) → Bool
  | .inl 0 => true
  | .inl 1 => true
  | .inl 2 => false
  | .inr (.and (.atom 0) (.atom 1)) => true
  | .inr (.imp (.atom 2) .falsum) => false
  | .inr _ => false

example : sampleProp.toPlaistedGreenbaum.feasible extraCostPGAssignment := by
  unfold feasible
  decide

example : sampleProp.cost (extraCostPGAssignment ∘ Sum.inl) <
    sampleProp.toPlaistedGreenbaum.cost extraCostPGAssignment := by
  decide

/-! ### Complexity bridges -/

private def sampleFG : Cslib.Complexity.MaxSAT.Instance :=
  (2, [[(0, true)], [(0, false)], [(1, true)]])

example : Cslib.Complexity.MaxSAT.optimum sampleFG = 2 := by decide

example : (Cslib.Logic.PL.MaxSAT.unweighted sampleFG.2).optimum = ((1 : ℕ) : WithTop ℕ) := by
  rw [Cslib.Complexity.MaxSAT.logic_optimum_unweighted_eq sampleFG (by decide)]
  decide

private def sampleOutOfRangeFG : Cslib.Complexity.MaxSAT.Instance :=
  (1, [[(1, true)]])

example : (Cslib.Complexity.MaxSAT.toLogicMaxSAT sampleOutOfRangeFG).computeOptimum = 1 := by
  decide

example : (Cslib.Logic.PL.MaxSAT.unweighted sampleOutOfRangeFG.2).computeOptimum = 0 := by
  decide

private def sampleStruct : Cslib.Complexity.MaxSAT.StructInstance :=
  ⟨2, [[(0, true), (1, false)], [(0, false)], [(1, true)]]⟩

example : (⟨sampleStruct, 2⟩ : Cslib.Complexity.MaxSAT.ThresholdQuery) ∈
    Cslib.Complexity.MaxSAT.ThresholdLanguage := by
  rw [Cslib.Complexity.MaxSAT.mem_thresholdLanguage_iff_hasCostAtMost _ (by decide)]
  refine ⟨by decide, fun _ => true, feasible_unweighted _ _, by decide⟩

private def sampleTwoSAT : Cslib.Complexity.MaxTwoSATInstance :=
  ⟨[[(0, true)], [(0, false), (1, true)]], 2⟩

example : sampleTwoSAT ∈ Cslib.Complexity.MaxTwoSAT := by
  rw [Cslib.Complexity.mem_maxTwoSAT_iff_optimum]
  refine ⟨by decide, by decide, ?_⟩
  rw [← (unweighted sampleTwoSAT.formula).computeOptimum_eq_optimum]
  decide

end CslibFrontierTests.Logics.Propositional.MaxSAT
