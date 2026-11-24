/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Complexity.Problems.MonotoneCircuitValue.Completeness

/-! Clients of monotone circuit value: encoded words match the `CircuitValue` encoding of the De
Morgan reading by `rfl`, both answers occur, dual rails preserve negation, empty inputs are
supported, and the generic writer has a concrete zero-chunk instance. -/

set_option linter.privateModule false

namespace CslibFrontierTests.MonotoneCircuitValue

open Cslib Cslib.Complexity Cslib.Circuits Turing Turing.MultiTapeTM

/-- Encoded words of `MonotoneCircuitValueInstance` are unchanged from the `CircuitValue` encoding
of its De Morgan reading. -/
example (x : MonotoneCircuitValueInstance) :
    encMonotoneCircuitValue x =
      encCircuitValue ⟨x.arity, x.circuit.mapOp Monotone.toDeMorgan, x.input⟩ :=
  rfl

example (n : ℕ) (c : Circuit Monotone.signature n 1) (x : BitString n) :
    encMonotoneCircuitValue { arity := n, circuit := c, input := x } =
      encCircuitValue ⟨n, c.mapOp Monotone.toDeMorgan, x⟩ :=
  rfl

/-- Yes- and no-instances with no gates. -/
example :
    { arity := 1, circuit := Circuit.id Monotone.signature 1, input := fun _ => true } ∈
      MonotoneCircuitValue ∧
    { arity := 1, circuit := Circuit.id Monotone.signature 1, input := fun _ => false } ∉
      MonotoneCircuitValue :=
  ⟨rfl, by change false ≠ true; decide⟩

private def notGate : Circuit Boolean.signature 1 1 := Circuit.oneGate .not (fun _ => 0)

/-- The negative input rail implements negation without a monotone NOT gate, doubling the gate
count (`(Monotone.dualRail notGate).size = 2`) and mapping `[]` to `[true]`. -/
example (b : Bool) :
    (Monotone.dualRail notGate).eval Monotone.interpretation
      (Monotone.railBitString fun _ => b) 0 = !b ∧
    (Monotone.dualRail notGate).size = 2 ∧
    Monotone.railBits [] = [true] := by
  refine ⟨?_, (Monotone.size_dualRail notGate).trans rfl, rfl⟩
  rw [Monotone.eval_dualRail]
  rfl

/-- A writer with no chunks or prefix copies the input unchanged. -/
private def copySpec : CircuitValue.WriterSpec where
  countUnit := []
  countEnd := []
  numChunks _ := 0
  chunk _ _ := []
  trailer _ := []
  copyBit b := [b]

example (w : List Bool) : copySpec.machine.run (frame w) (copySpec.rounds w.length) =
    ⟨(3, w.length, 0), w⟩ := by
  simpa [CircuitValue.WriterSpec.output, copySpec] using copySpec.run_machine w

/-- The generic writer's space hypotheses are realized by this concrete instance. -/
example : ComputableInLogSpace id (encFramed encBits) encBits := by
  refine copySpec.computableInLogSpace (fun w => by
    simp [CircuitValue.WriterSpec.output, copySpec])
    (ComputableInSpace.budget_const (encB := encNat) 0)
    (ComputableInSpace.budget_const (encB := encBits) [])
    (ComputableInSpace.budget_const (encB := encBits) []) ?_
  change PolynomiallyBounded fun _ : ℕ => 0
  fun_prop

/-- Composing the mutual logspace reductions between `CircuitValue` and `MonotoneCircuitValue`,
reducing `CircuitValueᶜ` via `P`-completeness of `MonotoneCircuitValue`, and collapsing
`CircuitValue` into `L` when `MonotoneCircuitValue ∈ L`. -/
example :
    LogSpaceReducible encCircuitValue encCircuitValue CircuitValue CircuitValue ∧
    PolyTimeReducible encCircuitValue encMonotoneCircuitValue
      CircuitValueᶜ MonotoneCircuitValue :=
  ⟨MonotoneCircuitValue.circuitValue_logSpaceReducible.trans
      MonotoneCircuitValue.logSpaceReducible_circuitValue,
    MonotoneCircuitValue.logSpaceComplete.polyTimeComplete.2 _ _
      (compl_mem_P CircuitValue.mem_P)⟩

example (h : MonotoneCircuitValue ∈ L encMonotoneCircuitValue) :
    CircuitValue ∈ L encCircuitValue :=
  MonotoneCircuitValue.mem_L_iff_forall_P_eq_L.1 h encCircuitValue ▸ CircuitValue.mem_P

end CslibFrontierTests.MonotoneCircuitValue
