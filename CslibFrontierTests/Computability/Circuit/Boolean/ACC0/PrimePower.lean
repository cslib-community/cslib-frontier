/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Boolean.ACC0.PrimePower

/-! # Regression tests for the prime-power MOD simulation -/

public section

open Cslib.Circuits.Boolean Unbounded

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

example : AC0Mod 4 = AC0Mod 2 := AC0Mod_prime_power_eq 2 (k := 2) (by decide)
/-- The prime-power equality specializes to modulus nine across the module boundary. -/
theorem modNine_eq_modThree : AC0Mod 9 = AC0Mod 3 := AC0Mod_prime_power_eq 3 (k := 2) (by decide)

example : (primePowerGateCircuit 2 2 4).eval (extInterpretation (modGate 2))
    ![true, true, false, false] 0 = true := by
  rw [computes_primePowerGateCircuit]
  decide

example : (primePowerGateCircuit 2 2 4).eval (extInterpretation (modGate 2))
    ![true, true, true, true] 0 = false := by
  rw [computes_primePowerGateCircuit]
  decide

example : (primePowerGateCircuit 2 2 4).depth ≤ 3 := depth_primePowerGateCircuit_le 2 2 4

example : (primePowerGateCircuit 2 2 4).size ≤ 1253 :=
  size_primePowerGateCircuit_le 2 2 4 (by decide)
