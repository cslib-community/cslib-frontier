/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Circuit.Boolean.Rectifier.Asymptotic
import Mathlib.Analysis.SpecificLimits.Basic

/-! A rectangular family satisfying Lupanov's growth conditions: `p = 2 ^ n`, `q = n ^ 2`.
Its normalized column count is `q / log₂ p = n`, and the wire budget becomes
`(1 + ε) * n * 2 ^ n`. This also checks conversion from natural powers to the real logarithm. -/

set_option linter.privateModule false

open Filter Cslib.Circuits Cslib.Circuits.Boolean.Rectifier

example (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Matrix (Fin (2 ^ n)) (Fin (n ^ 2)) Bool,
      ∃ c : Circuit signature (2 ^ n) (n ^ 2),
        IsTwoLayer c ∧ c.Computes interpretation (matrixAction A) ∧
          (c.program.cost id : ℝ) ≤ (1 + ε) * (2 : ℝ) ^ n * n := by
  have hp : Tendsto (fun n : ℕ => 2 ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have hq : Tendsto (fun n : ℕ => ((n ^ 2 : ℕ) : ℝ) / Real.logb 2 (2 ^ n : ℕ))
      atTop atTop := by
    refine tendsto_natCast_atTop_atTop.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
    field_simp
  filter_upwards [exists_depth_two_eventually hp hq ε hε, eventually_ge_atTop 1] with n hn hn1
  intro A
  obtain ⟨c, hl, hc, hw⟩ := hn A
  refine ⟨c, hl, hc, ?_⟩
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  convert hw using 1
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  field_simp
