/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.NonExplicitPRG

/-! Checked clients of Arora and Barak's Exercise 16.2
(`Cslib.Complexity.exists_generator_advantage_lt`) and of the failure of its printed form at
`ℓ = 1` (`Cslib.Complexity.exists_isCircuitTest_le_advantage_one`). -/

set_option linter.privateModule false

open Cslib Cslib.Crypto Cslib.Crypto.PRG Cslib.Complexity

/-- At seed length `60` the generator expands to `⌈2 ^ 6⌉ = 64` bits and fools every circuit
with at most `64 ^ 3` gates. -/
example : ∃ S : ℕ → ℕ, ∃ G : List Bool → List Bool, S 60 = 64 ∧
    ∀ adversary, IsCircuitTest (S 60 ^ 3) adversary →
      (PRG.wordFamily G S 60).advantage adversary < 1 / 10 := by
  obtain ⟨S, G, hS, -, -, -, hG⟩ := exists_generator_advantage_lt
  refine ⟨S, G, ?_, hG 60⟩
  rw [hS 60 (by norm_num)]
  norm_num

/-- With the hint's `ε = 1 / 10` and the draft's rounding, no generator at all is pseudorandom at
seed length one. -/
example (G : List Bool → List Bool) :
    ∃ adversary, IsCircuitTest (⌈(2 : ℝ) ^ ((1 / 10 : ℝ) * ((1 : ℕ) : ℝ))⌉₊ ^ 3) adversary ∧
      1 / 10 ≤ (PRG.wordFamily G (fun ℓ => ⌈(2 : ℝ) ^ ((1 / 10 : ℝ) * ℓ)⌉₊) 1).advantage
        adversary :=
  exists_isCircuitTest_le_advantage_one (by norm_num) G
