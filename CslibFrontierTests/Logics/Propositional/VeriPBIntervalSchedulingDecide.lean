/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

-- `import all`: the kernel evaluates `stepTop` and `runTop`, and the dynamic program `certify` with
-- its private helpers (`order`, `step`, `bound`, …), the proof log, the clique encoding and
-- Mathlib's `List.insertionSort`, whose bodies are not exposed.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.DynamicProgramming
import all CslibFrontier.Logics.Propositional.PseudoBoolean.IntervalScheduling
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.Clique
import all Mathlib.Data.List.Sort
import Mathlib.Data.Fin.VecNotation

/-! A kernel-checked client of certified weighted interval scheduling: the kernel runs the dynamic
program and the checker on a five-interval instance, and the end-to-end theorem turns the
acceptance into the statement that its optimum is `13`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBIntervalSchedulingDecide

open Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Graph
  Cslib.Logic.PL.VeriPB.IntervalScheduling

/-- The starts. -/
def a : Fin 5 → ℕ := ![0, 1, 3, 2, 4]

/-- The finishes: `[0, 3)`, `[1, 4)`, `[3, 6)`, `[2, 5)` and the empty `[4, 4)`. -/
def f : Fin 5 → ℕ := ![3, 4, 6, 5, 4]

/-- The values. -/
def v : Fin 5 → ℕ := ![5, 1, 8, 4, 0]

/-- The checker accepts the proof of the dynamic program. -/
theorem accepted :
    checkRed (cliqueConstraints (compat a f)) (some (negProfit v)) (certify a f v).proof =
      true := by
  decide +kernel

theorem optimum_eq : (certify a f v).optimum = 13 := by decide +kernel

/-- **The optimum is `13`**: `[0, 3)` and `[3, 6)`, and no better set of disjoint intervals. -/
theorem isGreatest :
    IsGreatest ((fun S : Finset (Fin 5) => ∑ i ∈ S, v i) ''
      {S : Finset (Fin 5) |
        (S : Set (Fin 5)).Pairwise fun i j => min (f i) (f j) ≤ max (a i) (a j)}) 13 :=
  optimum_eq ▸ isGreatest_of_checkRed_certify accepted

/-- With no intervals, the optimum is `0`. -/
example : checkRed (cliqueConstraints (compat ![] ![])) (some (negProfit ![]))
    (certify ![] ![] ![]).proof = true ∧ (certify ![] ![] ![]).optimum = 0 := by
  decide +kernel

end CslibFrontierTests.Logics.Propositional.VeriPBIntervalSchedulingDecide
