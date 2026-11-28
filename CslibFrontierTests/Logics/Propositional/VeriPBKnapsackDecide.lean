/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

-- `import all`: the kernel evaluates `stepTop` and `runTop`, the dynamic program `certify` with its
-- private `optSteps` and `optInst`, and the emitter's `Inst.forward`, `Inst.fwd`, `Inst.mkLayer`,
-- `Inst.trans`, …, whose bodies are not exposed.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Knapsack
import all CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackDP
import CslibFrontier.Algorithms.Lean.Knapsack.ProfitDP
import Mathlib.Data.Fin.VecNotation

/-! A kernel-checked client of certified knapsack: the kernel runs the dynamic program and the
checker on a six-item instance, and the end-to-end theorem turns the acceptance into the
statement that its optimum is `130`, which is also the profit of the selection of
`Cslib.Algorithms.Lean.Knapsack.profitDP`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBKnapsackDecide

open Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Knapsack

/-- The weights. -/
def w : Fin 6 → ℕ := ![5, 4, 6, 3, 7, 2]

/-- The profits. -/
def p : Fin 6 → ℕ := ![10, 40, 30, 50, 35, 40]

/-- The checker accepts the proof of the dynamic program for the capacity `10`. -/
theorem accepted : checkRed (formula w 10) (some (negProfit p)) (certify w p 10).proof = true := by
  decide +kernel

theorem optimum_eq : (certify w p 10).optimum = 130 := by decide +kernel

/-- **The optimum is `130`**: items `1`, `3` and `5`, of weight `9`, and no better set fits. -/
theorem isGreatest :
    IsGreatest ((fun S : Finset (Fin 6) => ∑ i ∈ S, p i) '' {S | ∑ i ∈ S, w i ≤ 10}) 130 :=
  optimum_eq ▸ isGreatest_of_checkRed_certify accepted

/-- The certified optimum is the profit of `profitDP`'s selection. -/
example : (certify w p 10).optimum =
    ((Cslib.Algorithms.Lean.Knapsack.profitDP w p 10 (List.finRange 6)).map p).sum := by
  decide +kernel

/-- With no items, the optimum is `0`. -/
example : checkRed (formula ![] 3) (some (negProfit ![])) (certify ![] ![] 3).proof = true ∧
    (certify ![] ![] 3).optimum = 0 := by
  decide +kernel

end CslibFrontierTests.Logics.Propositional.VeriPBKnapsackDecide
