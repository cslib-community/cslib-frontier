/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Circuit.Boolean.ExtendedConnection

/-! # Checked extended connection queries -/

set_option linter.privateModule false

namespace CslibFrontierTests.ExtendedConnection

open Cslib.Circuits Cslib.Circuits.Boolean

/-- Two negation gates on a single input. -/
private def doubleNot : Circuit signature 1 1 :=
  ⟨.gate (.gate .empty ⟨.not, fun _ => .input 0⟩) ⟨.not, fun _ => .gate 0⟩,
    fun _ => .gate 1⟩

/-- Assign names in reverse topological order, with the output named zero. -/
private def names : Wire 1 doubleNot.size ↪ ℕ :=
  ⟨(fun w => (Fin.rev (Wire.equivFin 1 doubleNot.size w)).val),
    fun _ _ h => (Wire.equivFin 1 doubleNot.size).injective (Fin.rev_injective (Fin.ext h))⟩

example : names (doubleNot.outputs 0) = 0 := rfl

example : followInputs doubleNot (doubleNot.outputs 0) [false, false] = some (.input 0) := rfl

example : followInputs doubleNot (doubleNot.outputs 0) [false, true] = none := rfl

example : ⟨1, 0, [], .inl (.inr .not)⟩ ∈
    extendedConnectionLanguage (fun _ => doubleNot) (fun _ => 4) (fun _ => names) :=
  ⟨by decide, doubleNot.outputs 0, rfl, rfl⟩

example : ⟨1, 0, [false, false], .inr 2⟩ ∈
    extendedConnectionLanguage (fun _ => doubleNot) (fun _ => 4) (fun _ => names) :=
  ⟨by decide, doubleNot.outputs 0, rfl, .input 0, rfl, rfl⟩

end CslibFrontierTests.ExtendedConnection
