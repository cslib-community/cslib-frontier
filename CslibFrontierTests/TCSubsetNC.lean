/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Boolean.IntThreshold
public import CslibFrontier.Computability.Circuit.Boolean.TCSubsetNC

/-!
# Signed thresholds and majority with repeated wires

The signed gate uses a strict cutoff. The repeated-wire majority uses the inclusive cutoff of
the circuit class, including a tie that would be lost by ignoring the repeated input.
-/

public section

namespace CslibFrontierTests.TCSubsetNC

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

private abbrev signed (bias : ℤ) : IntThreshold.Op := ⟨2, ![2, -1], bias⟩

example : (signed 1).deMorganCircuit.eval interpretation ![true, false] 0 = true ∧
    (signed 1).deMorganCircuit.eval interpretation ![true, true] 0 = false := by
  simp only [IntThreshold.Op.eval_deMorganCircuit]
  decide

-- Negative literal mass makes the first target zero. The other target exceeds every literal sum.
example : (signed (-2)).deMorganCircuit.eval interpretation ![false, true] 0 = true ∧
    (signed 2).deMorganCircuit.eval interpretation ![true, false] 0 = false := by
  simp only [IntThreshold.Op.eval_deMorganCircuit]
  decide

private abbrev emptyGate (bias : ℤ) : IntThreshold.Op := ⟨0, Fin.elim0, bias⟩

example : (emptyGate (-1)).deMorganCircuit.eval interpretation Fin.elim0 0 = true ∧
    (emptyGate 0).deMorganCircuit.eval interpretation Fin.elim0 0 = false := by
  simp only [IntThreshold.Op.eval_deMorganCircuit]
  decide

private def repeated : Circuit Unbounded.extSignature 3 1 :=
  Circuit.oneGate (.gate 4) ![0, 0, 1, 2]

/-- A De Morgan simulation preserves multiplicity at the tie and below it. -/
theorem exists_bounded_repeated_majority : ∃ D : Circuit Boolean.signature 3 1,
    D.eval interpretation ![true, false, false] 0 = true ∧
    D.eval interpretation ![false, true, false] 0 = false ∧
    D.size ≤ 70 * 5 * (6 ^ 2 + 2) ^ 2 := by
  obtain ⟨D, hD, hs, _⟩ := Unbounded.exists_deMorgan_simulation_tc repeated
  refine ⟨D, ?_, ?_, hs⟩ <;> rw [hD] <;> decide

end CslibFrontierTests.TCSubsetNC
