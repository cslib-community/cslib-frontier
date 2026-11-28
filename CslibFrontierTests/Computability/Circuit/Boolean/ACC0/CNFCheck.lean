/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Boolean.ACC0.CNFCheck

/-!
# Tests for the CNF violation-check circuit

Concrete checks for `Cslib.Circuits.Boolean.Unbounded.cnfCheck`:

* the one-clause formula `(x₀ ∨ ¬x₁)` is reported violated on `(false, true)` and not on
  `(true, true)`, and the output agrees with `eval_cnfCheck`;
* boundary witness: for the satisfiable formula `x₅` the range hypothesis of `eval_cnfCheck` fails
  at `n = 1` (the circuit drops the out-of-range literal) and holds at `n = 6`, where the
  satisfying input is accepted. The circuit itself is opaque outside its file, so the dropped
  literal cannot be evaluated directly here.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Circuit.Boolean.ACC0.CNFCheck

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded

/-- The clause `x₀ ∨ ¬x₁`: literals `(variable, sign)`. -/
def phi : Cslib.Logic.PL.CNF ℕ := [[(0, true), (1, false)]]

/-- The clause is falsified by `x₀ = false, x₁ = true`, so a violation is reported. -/
example : (cnfCheck 2 phi).eval (extInterpretation (modGate 2)) ![false, true] 0 = true := by
  rw [eval_cnfCheck 2 2 phi (by decide)]
  decide

/-- The clause is satisfied by `x₀ = true`, so no violation is reported. -/
example : (cnfCheck 2 phi).eval (extInterpretation (modGate 3)) ![true, true] 0 = false := by
  rw [eval_cnfCheck 3 2 phi (by decide)]
  decide

/-- Boundary witness: for `Φ = x₅` and `n = 1` the range hypothesis of `eval_cnfCheck` fails
(the literal is dropped by the circuit, which then reports a violation on every input although
`Φ` is satisfiable), while for `n = 6` it holds and the satisfying input is accepted. -/
example : ¬ ∀ c ∈ ([[(5, true)]] : Cslib.Logic.PL.CNF ℕ), ∀ l ∈ c, l.1 < 1 := by decide

example : (cnfCheck 6 [[(5, true)]]).eval (extInterpretation (modGate 2))
    ![false, false, false, false, false, true] 0 = false := by
  rw [eval_cnfCheck 2 6 _ (by decide)]
  decide

end CslibFrontierTests.Computability.Circuit.Boolean.ACC0.CNFCheck
