/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

-- `import all`: the `decide +kernel` checks below evaluate `stepTop`, whose body is not exposed.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import CslibFrontier.Logics.Propositional.PseudoBoolean.Completeness

/-! Checked clients of the completeness of the VeriPB kernel checker, each a proof of the shape
that the completeness constructions build, accepted by `decide +kernel`: a refutation of the
unsatisfiable cardinality constraints `x1 + x2 + x3 ≥ 2` and `¬x1 + ¬x2 + ¬x3 ≥ 2`; the optimum of
a two-variable knapsack, by `soli` of the full assignment of an optimal solution and a cutting
planes refutation; and a complete enumeration of the three solutions of `x1 + x2 ≥ 1`, by one
`solx` per projection and a refutation. The soundness theorems turn each into its claim, and the
completeness theorems state that such a proof exists for every instance. -/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBCompleteness

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB

/-! ### `UNSAT` -/

/-- `x1 + x2 + x3 ≥ 2` and `¬x1 + ¬x2 + ¬x3 ≥ 2`: their sum is `3 ≥ 4`. -/
def card : List PBConstr :=
  [⟨[(1, (1, true)), (1, (2, true)), (1, (3, true))], 2⟩,
    ⟨[(1, (1, false)), (1, (2, false)), (1, (3, false))], 2⟩]

/-- One `pol` step adds the two constraints, which normalizes to the contradiction `0 ≥ 1`,
numbered `3`. -/
def cardProof : Proof := ⟨[.pol [.id 1, .id 2, .add]], 3⟩

theorem cardProof_ok : check card cardProof = true ∧ cardProof.steps.all Step.IsCP := by
  decide +kernel

example : checkRed card none ⟨cardProof.steps.map .step, .unsat 3⟩ = true := by decide +kernel

example : ¬ ∃ σ, ∀ c ∈ card, c.Holds σ :=
  not_satisfiable_iff_exists_check.2.2 ⟨_, cardProof_ok⟩

/-! ### `BOUNDS` -/

/-- The knapsack constraint `2 x1 + 3 x2 ≤ 4`, as `2 ¬x1 + 3 ¬x2 ≥ 1`: the items of weights `2` and
`3` do not both fit. -/
def knap : List PBConstr := [⟨[(2, (1, false)), (3, (2, false))], 1⟩]

/-- Maximize the value `3 x1 + 4 x2`: minimize `-3 x1 - 4 x2`. -/
def knapObj : Objective := ⟨[(1, -3), (2, -4)], 0⟩

/-- The optimal solution: the second item alone, of value `-4`. -/
def knapOpt : ℕ → Bool := fun v => v == 2

/-- The proof that the completeness construction builds: `soli` logs the full assignment of
`knapOpt` to `x1, x2`, adding the improving constraint `3 x1 + 4 x2 ≥ 5` as `2`. Adding the literal
axioms `3 ¬x1` and `4 ¬x2` to it and dividing gives `x2 ≥ 1` (`3`) and `x1 ≥ 1` (`4`), and
`1 + 2 · 4 + 3 · 3` is the contradiction `5`. -/
def knapProof : RedProof :=
  ⟨[.soli (solutionOf [1, 2] knapOpt),
    .step (.pol [.id 2, .lit (1, false), .mul 3, .add, .div 4]),
    .step (.pol [.id 2, .lit (2, false), .mul 4, .add, .div 3]),
    .step (.pol [.id 1, .id 4, .mul 2, .add, .id 3, .mul 3, .add])],
    .bounds (some (-4)) 5 (some (-4)) none⟩

example : knapObj.eval knapOpt = -4 := by decide +kernel

theorem knapProof_ok : checkRed knap (some knapObj) knapProof = true := by decide +kernel

/-- The optimum is `-4`. -/
example : IsLeast (knapObj.eval '' {σ | ∀ c ∈ knap, c.Holds σ}) (-4) :=
  isLeast_iff_exists_checkRed_bounds.2 ⟨_, 5, rfl, knapProof_ok⟩

/-- Without the improving constraint the database is satisfiable, so `BOUNDS INF` is rejected. -/
example : checkRed knap (some knapObj) ⟨[], .bounds none 1 none none⟩ = false := by decide +kernel

/-! ### `ENUMERATION_COMPLETE` -/

/-- `x1 + x2 ≥ 1`, with the three solutions `10`, `01` and `11` on the preserved set `x1, x2`. -/
def enumF : List PBConstr := [⟨[(1, (1, true)), (1, (2, true))], 1⟩]

/-- The proof that the completeness construction builds: one `solx` per projection, of the full
assignment of a solution, adding the solution-excluding constraints `2`, `3` and `4`. The four
clauses on `x1, x2` give `x2 ≥ 1` (`5`) and `¬x2 ≥ 1` (`6`), whose sum is the contradiction `7`. -/
def enumProof : RedProof :=
  ⟨[.solx (solutionOf [1, 2] fun v => v == 1), .solx (solutionOf [1, 2] fun v => v == 2),
    .solx (solutionOf [1, 2] fun _ => true),
    .step (.pol [.id 1, .id 2, .add, .div 2]), .step (.pol [.id 3, .id 4, .add, .div 2]),
    .step (.pol [.id 5, .id 6, .add])],
    .enumComplete 3 7⟩

theorem enumProof_ok : checkRed enumF none enumProof (some [1, 2]) = true := by decide +kernel

/-- `x1 + x2 ≥ 1` has exactly three solutions on `x1, x2`. -/
example : (projections enumF [1, 2]).encard = 3 :=
  encard_eq_iff_exists_checkRed_enumComplete.2 ⟨_, 7, rfl, enumProof_ok⟩

/-- Two of the three projections are not a complete enumeration: the database stays
satisfiable. -/
example : checkRed enumF none
    ⟨[.solx (solutionOf [1, 2] fun v => v == 1), .solx (solutionOf [1, 2] fun v => v == 2)],
      .enumComplete 2 3⟩ (some [1, 2]) = false := by decide +kernel

/-! ### `SAT` -/

example : checkRed enumF none ⟨[], .sat (some (solutionOf [1, 2] fun v => v == 1))⟩ = true := by
  decide +kernel

end CslibFrontierTests.Logics.Propositional.VeriPBCompleteness
