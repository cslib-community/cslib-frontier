/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

-- `import all`: the kernel evaluates `stepTop` and `runTop`, whose bodies are not exposed.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import CslibFrontier.Logics.Propositional.PseudoBoolean.MaxSAT
import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
import CslibFrontierTests.Logics.Propositional.VeriPBProofText
-- `#guard` runs the text front end at compile time.
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.MaxSAT
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
public meta import CslibFrontierTests.Logics.Propositional.VeriPBProofText

/-! Checked clients of the pseudo-Boolean encoding of weighted partial MaxSAT
(`CslibFrontier.Logics.Propositional.PseudoBoolean.MaxSAT`): hand-written VeriPB proofs, accepted
by `decide +kernel`, of the optimum of a weighted partial instance with unit and non-unit soft
clauses, and of the unsatisfiability of the hard clauses of another instance; the soundness
theorems turn the acceptances into statements about the MaxSAT instances. The text front end
accepts the same proofs, printed by the test-only printer
`CslibFrontierTests.Logics.Propositional.VeriPBProofText.pbpText`, against the encodings printed
as OPB by `Cslib.Logic.PL.VeriPB.Text.printOPB`; VeriPB 3.0.2 and CakePB (cakepb `438b8f8`)
verify both printed texts and reject the printed proof claiming the optimum `7`. -/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.Logics.Propositional.VeriPBMaxSAT

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.MaxSAT
open CslibFrontierTests.Logics.Propositional.VeriPBProofText

/-! ### An optimum

The hard clauses `x₀ ∨ x₁` and `¬x₁ ∨ ¬x₂`; the soft clauses `¬x₀` of weight `5`, `¬x₁` of
weight `3`, `x₁` of weight `2` and `x₀ ∨ x₂` of weight `3`. The optimum `6` is attained by
`x₀ = x₂ = false`, `x₁ = true`, which falsifies `¬x₁` and `x₀ ∨ x₂`; every assignment with
`x₀ = true` costs at least `5 + 2`. -/

/-- The instance. -/
def inst : MaxSAT ℕ where
  hard := [[(0, true), (1, true)], [(1, false), (2, false)]]
  soft := [([(0, false)], 5), ([(1, false)], 3), ([(1, true)], 2), ([(0, true), (2, true)], 3)]

-- The encoding: the three unit soft clauses go into the objective, and the soft clause
-- `x₀ ∨ x₂` at index `3` gets the relaxation variable `3 + 3`.
example : inst.relaxBase = 3 ∧
    inst.toPBConstrs = [⟨[(1, 0, true), (1, 1, true)], 1⟩, ⟨[(1, 1, false), (1, 2, false)], 1⟩,
      ⟨[(1, 0, true), (1, 2, true), (1, 6, true)], 1⟩] ∧
    inst.toObjective = ⟨[(0, 5), (1, 3), (1, -2), (6, 3)], 2⟩ := by
  decide +kernel

/-- The proof: log the optimal solution, adding the improving constraint
`5 x₀ + x₁ + 3 x₆ + 2 ≤ 5`, normalized to `5 ¬x₀ + ¬x₁ + 3 ¬x₆ ≥ 6` (constraint `4`), and refute
it by cutting planes: `x₀ + ¬x₂ ≥ 1` (`5`), `2 x₀ + x₆ ≥ 1` (`6`), `4 ¬x₀ + 3 ¬x₆ ≥ 5` (`7`),
`2 x₀ ≥ 1` (`8`), `x₀ ≥ 1` (`9`) and `¬x₁ + 3 ¬x₆ ≥ 6` (`10`), a contradiction. -/
def proof : RedProof where
  steps := [.soli [(0, false), (1, true), (2, false), (6, true)],
    .step (.pol [.id 1, .id 2, .add]),
    .step (.pol [.id 5, .id 3, .add]),
    .step (.pol [.id 4, .id 1, .add]),
    .step (.pol [.id 7, .id 6, .mul 3, .add]),
    .step (.pol [.id 8, .div 2]),
    .step (.pol [.id 4, .id 9, .mul 5, .add])]
  conclusion := .bounds (some 6) 10 (some 6) none

/-- The checker accepts the proof for the encoding. -/
theorem accepted : checkRed inst.toPBConstrs (some inst.toObjective) proof = true := by
  decide +kernel

/-- **The optimum is `6`.** -/
theorem isLeast_cost : IsLeast ((fun σ => (inst.cost σ : ℤ)) '' {σ | inst.feasible σ}) 6 :=
  isLeast_cost_of_checkRed accepted rfl

/-- A proof claiming the optimum `7`, with the same steps, is rejected. -/
example : checkRed inst.toPBConstrs (some inst.toObjective)
    ⟨proof.steps, .bounds (some 7) 10 (some 7) none⟩ = false := by
  decide +kernel

/-! ### Unsatisfiable hard clauses -/

/-- The hard clauses `x₀` and `¬x₀`, with the soft unit clause `x₀` of weight `4`. -/
def infeasible : MaxSAT ℕ where
  hard := [[(0, true)], [(0, false)]]
  soft := [([(0, true)], 4)]

/-- The proof: the sum of the two hard clauses, `0 ≥ 1`, is a contradiction. -/
def infeasibleProof : RedProof where
  steps := [.step (.pol [.id 1, .id 2, .add])]
  conclusion := .bounds none 3 none none

theorem infeasible_accepted :
    checkRed infeasible.toPBConstrs (some infeasible.toObjective) infeasibleProof = true := by
  decide +kernel

/-- **The hard clauses are unsatisfiable.** -/
theorem not_satisfiable : ¬ infeasible.hard.Satisfiable :=
  not_satisfiable_of_checkRed_bounds infeasible_accepted rfl

/-! ### Text

The encoding of `inst`, printed by `Text.printOPB`, and its proof, printed by `pbpText 3`:

```
* #variable= 7 #constraint= 3
min: 5 x1 3 x2 -2 x2 3 x7 2 ;
1 x1 1 x2 >= 1 ;
1 ~x2 1 ~x3 >= 1 ;
1 x1 1 x3 1 x7 >= 1 ;
```

```
pseudo-Boolean proof version 3.0
f 3 ;
soli ~x1 x2 ~x3 x7 ;
pol 1 2 + ;
pol 5 3 + ;
pol 4 1 + ;
pol 7 6 3 * + ;
pol 8 2 d ;
pol 4 9 5 * + ;
output NONE ;
conclusion BOUNDS 6 : 10 6 ;
end pseudo-Boolean proof ;
```

On these files VeriPB 3.0.2 and CakePB report `s VERIFIED BOUNDS 6 <= obj <= 6`, and on the
printed texts of `infeasible` and `infeasibleProof` `s VERIFIED BOUNDS INF <= obj <= INF`. -/

/-- The text front end accepts the printed proof against the printed encoding. -/
def textAccepts (φ : MaxSAT ℕ) (P : RedProof) : Bool :=
  Text.checkOPB (Text.printOPB ⟨φ.toPBConstrs, some φ.toObjective, none⟩)
    (pbpText φ.toPBConstrs.length P) == some P.conclusion

#guard textAccepts inst proof
#guard textAccepts infeasible infeasibleProof

end CslibFrontierTests.Logics.Propositional.VeriPBMaxSAT
