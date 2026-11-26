/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Coefficient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The `3`-way planar Gaussian mismatch coefficient and its rational bounds

Defines `threeWayCapCoefficient` and proves positivity (`threeWayCapCoefficient_pos`), the rational
upper bound `21773 / 100000` (`threeWayCapCoefficient_le_21773`), and the resulting `3.041n`
fan-in-`2` circuit lower-bound threshold (`circuitThreshold_gt_3041`).

## Main definitions

* `Cslib.Circuits.Frontier.TensorRank.threeWayCapCoefficient`: the `3`-way planar Gaussian
  half-edge mismatch coefficient `(3 / 2) p + (1 / 2) (1 - √((1 + 2√2 / 3) / 2))`.

## Main results

* `Cslib.Circuits.Frontier.TensorRank.threeWayCapCoefficient_pos`: `0 < threeWayCapCoefficient`.
* `Cslib.Circuits.Frontier.TensorRank.threeWayCapCoefficient_le_21773`:
  `threeWayCapCoefficient ≤ 21773 / 100000`.
* `Cslib.Circuits.Frontier.TensorRank.circuitThreshold_gt_3041`:
  `3041 / 1000 < 1 + 4 / (9 * threeWayCapCoefficient)`.
-/

public section

open Real

namespace Cslib.Circuits.Frontier.TensorRank

open Cslib.Circuits.Frontier.Gaussian

/-! ### The `3`-way planar Gaussian coefficient and its rational bounds -/

/-- The `3`-way planar Gaussian half-edge mismatch coefficient on cubic blocks:
`(3 / 2) * gaussianCoefficient + (1 / 2) * (1 - √((1 + 2√2 / 3) / 2)) ≈ 0.217728`. -/
noncomputable def threeWayCapCoefficient : ℝ :=
  3 / 2 * gaussianCoefficient + 1 / 2 * (1 - √((1 + 2 * √2 / 3) / 2))

/-- The parametric `3`-way mismatch bound at adjacent kernel correlation `ρ₀`. -/
private noncomputable def capAt (ρ₀ : ℝ) : ℝ :=
  3 / 2 * straddleBound ρ₀ + 1 / 2 * (1 - √((1 + ρ₀) / 2))

private theorem capAt_limit : capAt (2 * √2 / 3) = threeWayCapCoefficient := by
  rw [capAt, threeWayCapCoefficient, gaussianCoefficient_eq]

private theorem capAt_le_three (ρ₀ : ℝ) : capAt ρ₀ ≤ 3 := by
  have hpi : 0 < π := pi_pos
  have harc : arccos ((1 + 3 * ρ₀) / 4) ≤ π := arccos_le_pi _
  have hstrad : straddleBound ρ₀ ≤ 3 / 2 := by
    rw [straddleBound, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [harc, hpi]
  have hsqrt : 0 ≤ √((1 + ρ₀) / 2) := sqrt_nonneg _
  unfold capAt
  linarith only [hstrad, hsqrt]

/-- `threeWayCapCoefficient` is strictly positive. -/
theorem threeWayCapCoefficient_pos : 0 < threeWayCapCoefficient := by
  have hp : 0 < gaussianCoefficient := gaussianCoefficient_pos
  have hsqrt2 : √2 < 3 / 2 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hcap : √((1 + 2 * √2 / 3) / 2) ≤ 1 := sqrt_le_one.mpr (by linarith)
  unfold threeWayCapCoefficient
  linarith only [hp, hcap]

/-- Rational upper bound `threeWayCapCoefficient ≤ 21773 / 100000 = 0.21773`. -/
theorem threeWayCapCoefficient_le_21773 :
    threeWayCapCoefficient ≤ 21773 / 100000 := by
  have hp_pos : 0 < gaussianCoefficient := gaussianCoefficient_pos
  have hcc : (456249 / 100000 : ℝ) ≤ 1 + 1 / (2 * gaussianCoefficient) := by
    rw [one_add_inv_two_mul_gaussianCoefficient]
    exact circuitCoefficient_ge_456249
  have hdiv : (356249 / 100000 : ℝ) ≤ 1 / (2 * gaussianCoefficient) := by linarith only [hcc]
  have hp_le : gaussianCoefficient ≤ 100000 / 712498 := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 2 * gaussianCoefficient)).mp hdiv
    linarith only [hmul]
  have hsqrt2 : (141421356 / 100000000 : ℝ) < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  have hκ_ge : (9855985 / 10000000 : ℝ) ≤ √((1 + 2 * √2 / 3) / 2) :=
    (le_sqrt (by norm_num) (by positivity)).mpr (by linarith only [hsqrt2])
  unfold threeWayCapCoefficient
  linarith only [hp_le, hκ_ge]

/-- Combining `threeWayCapCoefficient ≤ 21773 / 100000` with `ω ≤ 9 / 4` exceeds `3.041`:
`3041 / 1000 < 1 + 4 / (9 * threeWayCapCoefficient)`. -/
theorem circuitThreshold_gt_3041 :
    (3041 / 1000 : ℝ) < 1 + 4 / (9 * threeWayCapCoefficient) := by
  have hpos : 0 < threeWayCapCoefficient := threeWayCapCoefficient_pos
  have hle : threeWayCapCoefficient ≤ 21773 / 100000 := threeWayCapCoefficient_le_21773
  have hlt : (2041 / 1000 : ℝ) < 4 / (9 * threeWayCapCoefficient) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith only [hle]
  linarith only [hlt]


end Cslib.Circuits.Frontier.TensorRank
