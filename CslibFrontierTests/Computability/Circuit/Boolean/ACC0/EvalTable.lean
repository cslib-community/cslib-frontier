/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Boolean.ACC0.EvalTable

/-!
# Tests for `evalTable`

Concrete checks for `Cslib.Circuits.Boolean.Unbounded.evalTable` and `eval_evalTable`, with
`G` the `AND` of two inputs (one hardwired prefix bit, one live input) and the prefix table
`![![true], ![false]]`: output `0` is the live input, output `1` is constantly `false`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Circuit.Boolean.ACC0.EvalTable

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded

/-- The `AND` of its two inputs: the hardwired prefix bit and the live bit. -/
def andTwo : Circuit extSignature (1 + 1) 1 :=
  Circuit.oneGate (σ := extSignature) (.ac (.and 2)) id

/-- The table of two prefixes. -/
def table : Fin 2 → BitString 1 := ![![true], ![false]]

example (x : BitString 1) (p : Fin 2) :
    (evalTable andTwo 2 table).eval (extInterpretation (modGate 2)) x p =
      andTwo.eval (extInterpretation (modGate 2)) (Fin.append (table p) x) 0 :=
  eval_evalTable 2 andTwo 2 table x p

/-- Prefix `true`: the `AND` returns the live input. -/
example : (evalTable andTwo 2 table).eval (extInterpretation (modGate 2)) ![true] 0 = true ∧
    (evalTable andTwo 2 table).eval (extInterpretation (modGate 2)) ![false] 0 = false := by
  rw [eval_evalTable, eval_evalTable]
  decide +kernel

/-- Prefix `false`: the `AND` is `false` whatever the live input. -/
example : (evalTable andTwo 2 table).eval (extInterpretation (modGate 2)) ![true] 1 = false ∧
    (evalTable andTwo 2 table).eval (extInterpretation (modGate 2)) ![false] 1 = false := by
  rw [eval_evalTable, eval_evalTable]
  decide +kernel

end CslibFrontierTests.Computability.Circuit.Boolean.ACC0.EvalTable
