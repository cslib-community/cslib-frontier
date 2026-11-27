/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.SAT.SingleTape

set_option linter.privateModule false

open Cslib.Complexity Cslib.Turing

private def haltMachine : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ s := (⟨s, none⟩, none)

example : satEqualityFamilyLength 0 = 0 := by
  simpa only [Nat.mul_zero, zero_mul, Nat.le_zero] using satEqualityFamilyLength_le 0

example : ¬ haltMachine.DecidesByHeadInTime id (encCNF '' SAT) true (fun n => n + 1) := by
  simpa only [one_mul] using
    (singleTape_sat_no_linear (tm := haltMachine) (ι := id) (yes := true) (C := 1))

/-- At this family length the quadratic bound excludes a one-step clock for the one-state
machine, even if the clock is unrestricted at other lengths. -/
example {T : ℕ → ℕ} (decides : haltMachine.DecidesByHeadInTime id (encCNF '' SAT) true T) :
    1 < T (satEqualityFamilyLength 26753) := by
  let N := satEqualityFamilyLength 26753
  have hN : 26753 ≤ N := le_satEqualityFamilyLength _
  have bound := singleTape_sat_quadratic_log_lower decides 26753 (by decide)
  change N ^ 2 ≤ 13376 * (Nat.log2 N + 1) * T N at bound
  by_contra! time
  have hlog : Nat.log2 N + 1 ≤ 2 * N := by
    have := Nat.log2_le_self N
    omega
  have hsmall : N ^ 2 ≤ 26752 * N := by
    calc
      _ ≤ 13376 * (Nat.log2 N + 1) * T N := bound
      _ ≤ 13376 * (2 * N) * 1 := Nat.mul_le_mul (Nat.mul_le_mul_left _ hlog) time
      _ = _ := by omega
  rw [pow_two] at hsmall
  have := Nat.le_of_mul_le_mul_right hsmall (by omega)
  omega
