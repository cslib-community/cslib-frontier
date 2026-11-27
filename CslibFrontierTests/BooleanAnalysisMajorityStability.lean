/-
Copyright (c) 2026 Vincent Liew, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.MajorityStability

/-! # Limits of the spectrum and noise stability of majority

The degree-one weight of majority tends to `2/π` and the degree-three weight to `1/(3π)`, the
first two coefficients of `(2/π) arcsin ρ = (2/π)(ρ + ρ³/6 + ⋯)`. Majority of three bits has
degree-one weight `3/4`, above its limit `2/π`. At `ρ = 1/2` the noise stability of majority tends
to `(2/π) arcsin(1/2) = 1/3`, and at `δ = 1/2` its noise sensitivity tends to `1/2`.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisMajorityStability

open Cslib Cslib.BitString Filter Topology Real

/-- The degree-one weight of majority tends to `2/π`. -/
theorem tendsto_levelWeight_one :
    Tendsto (fun m : ℕ => levelWeight 1 (fun x => signVal (majority (2 * m + 1) x))) atTop
      (𝓝 (2 / π)) := by
  simpa using tendsto_levelWeight_signVal_majority 0

/-- The degree-three weight of majority tends to `1/(3π)`. -/
theorem tendsto_levelWeight_three :
    Tendsto (fun m : ℕ => levelWeight 3 (fun x => signVal (majority (2 * m + 1) x))) atTop
      (𝓝 (1 / (3 * π))) := by
  have h := tendsto_levelWeight_signVal_majority 1
  convert h using 2
  simp [Nat.centralBinom, Nat.choose]
  field_simp
  norm_num

/-- Majority of three bits has degree-one weight at least `2/π`. -/
example : 2 / π ≤ levelWeight 1 (fun x => signVal (majority 3 x)) := by
  simpa using le_levelWeight_signVal_majority (m := 1) (j := 0) (by norm_num)

/-- At `ρ = 1/2` the noise stability of majority tends to `1/3`. -/
theorem tendsto_noiseStability_half :
    Tendsto (fun m : ℕ => noiseStability (1 / 2) (fun x => signVal (majority (2 * m + 1) x)))
      atTop (𝓝 (1 / 3)) := by
  have h := tendsto_noiseStability_signVal_majority (ρ := 1 / 2) (by norm_num) (by norm_num)
  convert h using 2
  rw [show (1 / 2 : ℝ) = sin (π / 6) by rw [sin_pi_div_six],
    arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])]
  field_simp
  norm_num

/-- At `δ = 1/2` the noise sensitivity of majority tends to `1/2`. -/
theorem tendsto_noiseSensitivity_half :
    Tendsto (fun m : ℕ => noiseSensitivity (1 / 2) (majority (2 * m + 1))) atTop
      (𝓝 (1 / 2)) := by
  have h := tendsto_noiseSensitivity_majority (δ := 1 / 2) (by norm_num) (by norm_num)
  convert h using 2
  norm_num [arccos_zero]
  field_simp

end CslibFrontierTests.BooleanAnalysisMajorityStability
