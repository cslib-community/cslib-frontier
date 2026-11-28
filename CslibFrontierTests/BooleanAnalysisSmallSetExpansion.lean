/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.SmallSetExpansion
public import CslibFrontierTests.BooleanAnalysisReverseHypercontractivity
import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity.TwoPoint
import CslibFrontier.Foundations.Data.Finset.Expect

/-! # Small-set expansion on small cubes

On one bit, the subcube `{x | x () = true}` (the fixture of the Reverse Small-Set Expansion
clients) has volume `α = 1 / 2`, and a uniform point and a `ρ`-correlated point both lie in it
with probability `Stab_ρ[1_A] = (1 + ρ) / 4`. The Small-Set Expansion Theorem bounds this at
`ρ = 1 / 2` by `(1 / 2) ^ (4 / 3)`, and its bound is attained at `ρ = 1`. Corollary 9.8 bounds
the true value `1 / 3` at `ρ = 1 / 3` by `(1 / 2) ^ (3 / 2) ≈ 0.354`. On three bits, the point
`{x | ∀ i, x i = true}` has volume `1 / 8`, and Corollary 9.8 bounds its noise stability at
`ρ = 1 / 3` by `(1 / 8) ^ (3 / 2)`. At `ρ = 0` the bound `α ^ 2` is attained by every set.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisSmallSetExpansion

open Cslib Cslib.BitString Finset
open CslibFrontierTests.BooleanAnalysisReverseHypercontractivity (subcube mem_subcube
  expect_indicator_subcube)
open scoped BigOperators

/-- A uniform point and a `ρ`-correlated point both lie in the subcube with probability
`(1 + ρ) / 4`. -/
theorem noiseStability_indicator_subcube (ρ : ℝ) :
    noiseStability ρ ((subcube true).indicator 1) = (1 + ρ) / 4 := by
  rw [noiseStability, Fintype.expect_unique_bool, noiseOp_unit, noiseOp_unit]
  simp [mem_subcube, Set.indicator]
  ring

-- The Small-Set Expansion Theorem at `ρ = 1 / 2`: `Stab_{1/2}[1_A] = 3 / 8 ≤ (1 / 2) ^ (4 / 3)`.
example : noiseStability (1 / 2) ((subcube true).indicator 1) ≤ (1 / 2 : ℝ) ^ (4 / 3 : ℝ) := by
  have h := noiseStability_indicator_le (ρ := 1 / 2) (by norm_num) (by norm_num) (subcube true)
  rw [expect_indicator_subcube true] at h
  convert h using 2
  norm_num

-- At `ρ = 1` the bound `α ^ (2 / (1 + ρ)) = α` is attained: `Stab_1[1_A] = 1 / 2`.
example : noiseStability 1 ((subcube true).indicator 1) =
    (𝔼 x, (subcube true).indicator (1 : (Unit → Bool) → ℝ) x) ^ (2 / (1 + 1) : ℝ) := by
  rw [noiseStability_indicator_subcube, expect_indicator_subcube true]
  norm_num

-- Corollary 9.8 on the subcube: `Stab_{1/3}[1_A] ≤ (1 / 2) ^ (3 / 2) ≈ 0.354`, with true value
-- `Stab_{1/3}[1_A] = 1 / 3`.
example : noiseStability (1 / 3) ((subcube true).indicator 1) ≤ (1 / 2 : ℝ) ^ (3 / 2 : ℝ) ∧
    noiseStability (1 / 3) ((subcube true).indicator 1) = 1 / 3 := by
  have h := noiseStability_one_third_indicator_le (subcube true)
  rw [expect_indicator_subcube true] at h
  refine ⟨h, ?_⟩
  rw [noiseStability_indicator_subcube]
  norm_num

/-- The all-`true` point of the three-bit cube. -/
def top₃ : Set (Fin 3 → Bool) := {x | ∀ i, x i = true}

/-- The all-`true` point has volume `1 / 8`. -/
theorem expect_indicator_top₃ : 𝔼 x, top₃.indicator (1 : (Fin 3 → Bool) → ℝ) x = 1 / 8 := by
  simp only [Fintype.expect_eq_sum_div_card, top₃, Set.indicator_apply, Set.mem_ofPred_eq,
    Pi.one_apply, Finset.sum_boole]
  rw [show (univ.filter fun x : Fin 3 → Bool => ∀ i, x i = true).card = 1 by decide,
    show Fintype.card (Fin 3 → Bool) = 8 by decide]
  norm_num

-- Corollary 9.8 on three bits: `Stab_{1/3}[1_A] ≤ (1 / 8) ^ (3 / 2)`.
example : noiseStability (1 / 3) (top₃.indicator 1) ≤ (1 / 8 : ℝ) ^ (3 / 2 : ℝ) := by
  simpa only [expect_indicator_top₃] using noiseStability_one_third_indicator_le top₃

-- At `ρ = 0` the bound `α ^ (2 / (1 + ρ)) = α ^ 2` is attained by every set.
example (A : Set (Fin 3 → Bool)) : noiseStability 0 (A.indicator 1) =
    (𝔼 x, A.indicator (1 : (Fin 3 → Bool) → ℝ) x) ^ (2 / (1 + 0) : ℝ) := by
  rw [noiseStability_zero]
  norm_num

end CslibFrontierTests.BooleanAnalysisSmallSetExpansion
