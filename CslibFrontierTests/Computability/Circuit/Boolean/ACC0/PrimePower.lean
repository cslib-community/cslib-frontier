/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

import CslibFrontier.Computability.Circuit.Boolean.ACC0.PrimePower

open Cslib.Circuits.Boolean

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

example : AC0Mod 4 = AC0Mod 2 := AC0Mod_prime_power_eq 2 (k := 2) (by decide)

-- Weights two and four agree mod two and differ mod four.
example : modGate 4 4 (fun i => decide (i.val < 2)) = true := by decide
example : modGate 4 4 (fun _ => true) = false := by decide

#print axioms AC0Mod_prime_power_eq
#print axioms primePowerGateCircuit_correct
#print axioms primePowerGateCircuit_depth
#print axioms primePowerGateCircuit_size
