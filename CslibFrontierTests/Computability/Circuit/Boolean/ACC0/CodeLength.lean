/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Boolean.ACC0.CodeLength

/-!
# Tests for the fan-in normalization of `AC⁰[q]` circuits

Concrete checks for `CslibFrontier.Computability.Circuit.Boolean.ACC0.CodeLength`: a one-gate
circuit whose `MOD_2` gate reads its input four times reads it no times after normalization, and
with five reads it keeps one live read. The transformed arity and the evaluation are inspected
through the circuit interface.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Circuit.Boolean.ACC0.CodeLength

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded

/-- The extra gate of `k` arguments reading the single input `k` times. -/
private def repeated (k : ℕ) : Circuit extSignature 1 1 :=
  Circuit.oneGate (σ := extSignature) (ExtOp.gate k) fun _ => 0

/-- Four reads of the input have multiplicity `0` modulo two: the normalized gate reads nothing. -/
example : extSignature.Arity ((modCircuit 2 (repeated 4)).program.lines
    (Fin.cast (size_modCircuit 2 _).symm (Fin.last 0))).op = 0 :=
  (arity_lines_modCircuit_last 2 .empty _ (repeated 4).outputs rfl).trans (by simp)

/-- Five reads have multiplicity `1` modulo two: the normalized gate keeps one live read. -/
example : extSignature.Arity ((modCircuit 2 (repeated 5)).program.lines
    (Fin.cast (size_modCircuit 2 _).symm (Fin.last 0))).op = 1 :=
  (arity_lines_modCircuit_last 2 .empty _ (repeated 5).outputs rfl).trans (by simp)

/-- Normalization keeps the function: four reads of an input bit are an even count, so the output
is false for both inputs. -/
example (x : BitString 1) :
    (modCircuit 2 (repeated 4)).eval (extInterpretation (modGate 2)) x 0 = false := by
  rw [eval_modCircuit]
  cases h : x 0 <;> simp [repeated, modGate, h]

/-- With five reads the normalized circuit outputs the input bit. -/
example (x : BitString 1) :
    (modCircuit 2 (repeated 5)).eval (extInterpretation (modGate 2)) x 0 = x 0 := by
  rw [eval_modCircuit]
  cases h : x 0 <;> simp [repeated, modGate, h]

end CslibFrontierTests.Computability.Circuit.Boolean.ACC0.CodeLength
