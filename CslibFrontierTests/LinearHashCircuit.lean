/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Boolean.LinearHash

/-! The shared matrix construction is interpreted over XOR, and its native gate bounds include
nullary gates. Empty output families remain free. -/

-- This ordinary-import client deliberately exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.LinearHashCircuit

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

private def repeatedRow : Fin 3 → BitString 2 := fun _ _ => true

/-- Two true inputs cancel in the binary linear map, even with repeated output rows. -/
example : BitString.LinearHash.hash repeatedRow (fun _ => true) = fun _ => false := by
  funext j
  simp only [BitString.LinearHash.hash, repeatedRow, dotProduct, Fin.sum_univ_two]
  rfl

/-- The blocked bound supplies an actual native circuit computing the shared parity outputs. -/
example : ∃ c : Circuit signature 2 3,
    c.Computes interpretation (BitString.LinearHash.hash repeatedRow) ∧ c.size ≤ 51 := by
  apply complexity_le_iff.mp
  exact complexity_linearHash_le_blocked repeatedRow (s := 2) (by decide)

/-- With no inputs the output gates compute zero, and their constants are charged. -/
example (rows : Fin 3 → BitString 0) :
    complexity interpretation (BitString.LinearHash.hash rows) ≤ 3 := by
  simpa using complexity_linearHash_le rows

/-- No designated outputs require no gates, regardless of the number of inputs. -/
example {n : ℕ} (rows : Fin 0 → BitString n) :
    complexity interpretation (BitString.LinearHash.hash rows) = 0 := by
  exact Nat.eq_zero_of_le_zero (by simpa using complexity_linearHash_le rows)

end CslibFrontierTests.LinearHashCircuit
