/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Coefficient
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The switched Gaussian coefficient and its numerical bounds

The cubic layout coefficient of the median-switched Gaussian vertex sweep [Gaspers2026] is

`c₃ = (3 / (4π)) arccos (5 / 6) ≈ 0.1398221240`,

strictly smaller than the median edge-score Gaussian coefficient
`p = (3 / (2π)) arccos ((1 + 2√2) / 4) ≈ 0.1403509686`. The comparison follows directly from
the double-angle formula: `cos (2 arccos ((1 + 2√2) / 4)) = (1 + 4√2) / 8 < 5 / 6`, since
`12 √2 < 17` (`288 < 289`).

The resulting circuit coefficient `1 + 1 / (2 c₃) = 1 + 2π / (3 arccos (5 / 6)) ≈ 4.575972`
exceeds `457597 / 100000 = 4.57597` (and `183 / 40 = 4.575`), and the resulting correlation
threshold `(1 + L) / 2 = 1 + π / (3 arccos (5 / 6)) ≈ 2.787986` exceeds `278798 / 100000`.

## Main definitions

* `Cslib.Circuits.Frontier.Switched.switchedCoefficient`: the coefficient `c₃`.
* `Cslib.Circuits.Frontier.Switched.pairCorr`: the ideal-star neighbor-pair correlation
  `b(r) = (3 r ^ 2 - 1) / 2`.
* `Cslib.Circuits.Frontier.Switched.kappa`: the ideal-star level-zero bound
  `κ(r) = (3 / (4π)) arccos (b(r))`.

## Main results

* `Cslib.Circuits.Frontier.Switched.switchedCoefficient_pos`: `0 < c₃`.
* `Cslib.Circuits.Frontier.Switched.switchedCoefficient_lt_gaussianCoefficient`: `c₃ < p`.
* `Cslib.Circuits.Frontier.Switched.one_add_inv_two_mul_switchedCoefficient`:
  `1 + 1 / (2 c₃) = 1 + 2π / (3 arccos (5 / 6))`.
* `Cslib.Circuits.Frontier.Switched.circuitCoefficient_ge_457597`:
  `457597 / 100000 ≤ 1 + 2π / (3 arccos (5 / 6))`.
* `Cslib.Circuits.Frontier.Switched.circuitCoefficient_ge_183_div_40`:
  `183 / 40 ≤ 1 + 2π / (3 arccos (5 / 6))`.
* `Cslib.Circuits.Frontier.Switched.correlationThreshold_ge`:
  `278798 / 100000 ≤ 1 + π / (3 arccos (5 / 6))`.

## References

* [S. Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster
  Exponential Algorithms*][Gaspers2026]
-/

@[expose] public section

open Real Filter

namespace Cslib.Circuits.Frontier.Switched

/-- The ideal-star neighbor-pair correlation `b(r) = (3 r ^ 2 - 1) / 2`. -/
noncomputable def pairCorr (r : ℝ) : ℝ := (3 * r ^ 2 - 1) / 2

/-- The ideal-star level-zero probability `κ(r) = (3 / (4π)) arccos ((3 r ^ 2 - 1) / 2)`. -/
noncomputable def kappa (r : ℝ) : ℝ := 3 / (4 * π) * arccos (pairCorr r)

/-- The limiting edge correlation `r* = 2√2 / 3` of the degree-3 distance kernel. -/
noncomputable def rStar : ℝ := 2 * √2 / 3

/-- The cubic layout coefficient of the median-switched Gaussian sweep,
`c₃ = (3 / (4π)) arccos (5 / 6) ≈ 0.139822`. -/
noncomputable def switchedCoefficient : ℝ :=
  3 / (4 * π) * arccos (5 / 6)

/-- At `r* = 2√2 / 3`, the ideal-star neighbor-pair correlation is `5 / 6`. -/
theorem pairCorr_rStar : pairCorr rStar = 5 / 6 := by
  have hsq : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  rw [pairCorr, rStar]
  linear_combination (2 / 3 : ℝ) * hsq

/-- `κ(2√2 / 3) = c₃`. -/
theorem kappa_rStar : kappa rStar = switchedCoefficient := by
  rw [kappa, pairCorr_rStar, switchedCoefficient]

/-- The function `κ` is continuous everywhere. -/
theorem continuous_kappa : Continuous kappa := by
  unfold kappa pairCorr
  exact continuous_const.mul (continuous_arccos.comp (by fun_prop))

/-- `r* ∈ (0, 1)`. -/
theorem rStar_pos : 0 < rStar := by
  unfold rStar
  positivity

/-- `r* < 1`. -/
theorem rStar_lt_one : rStar < 1 := by
  unfold rStar
  nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sqrt_nonneg 2]

/-- The switched cubic layout coefficient is strictly positive. -/
theorem switchedCoefficient_pos : 0 < switchedCoefficient := by
  unfold switchedCoefficient
  exact mul_pos (div_pos (by norm_num) (by positivity)) (arccos_pos.mpr (by norm_num))

/-- The circuit coefficient `1 + 1 / (2 c₃)` of the switched cubic coefficient `c₃`. -/
theorem one_add_inv_two_mul_switchedCoefficient :
    1 + 1 / (2 * switchedCoefficient) = 1 + 2 * π / (3 * arccos (5 / 6)) := by
  have h : 0 < arccos (5 / 6) := arccos_pos.mpr (by norm_num)
  unfold switchedCoefficient
  field_simp
  ring

/-- The exact strict comparison `c₃ < p`: the switched Gaussian sweep coefficient
`(3 / (4π)) arccos (5 / 6) ≈ 0.139822` is strictly below the edge-score median Gaussian
coefficient `(3 / (2π)) arccos ((1 + 2√2) / 4) ≈ 0.140351`, because
`cos (2 arccos ((1 + 2√2) / 4)) = (1 + 4√2) / 8 < 5 / 6` (equivalently `288 < 289`). -/
theorem switchedCoefficient_lt_gaussianCoefficient :
    switchedCoefficient < Gaussian.gaussianCoefficient := by
  set α := arccos ((1 + 2 * √2) / 4)
  have hsq2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have hcos_lt : (1 + 4 * √2) / 8 < 5 / 6 := by
    have : (12 * √2) ^ 2 < 17 ^ 2 := by linear_combination 144 * hsq2
    nlinarith [sqrt_nonneg 2]
  have hlo : (0 : ℝ) ≤ (1 + 2 * √2) / 4 := by positivity
  have hhi : (1 + 2 * √2) / 4 ≤ 1 := by
    have : √2 < 3 / 2 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
    linarith
  have hα_le : α ≤ π / 2 := arccos_le_pi_div_two.mpr hlo
  have hcos_double : cos (2 * α) = (1 + 4 * √2) / 8 := by
    rw [cos_two_mul, cos_arccos (by linarith) hhi]
    linear_combination (1 / 2 : ℝ) * hsq2
  have hangle : arccos (5 / 6) < 2 * α := by
    have hlt := arccos_lt_arccos (neg_one_le_cos (2 * α)) (hcos_double.symm ▸ hcos_lt)
      (by norm_num)
    rwa [arccos_cos (mul_nonneg zero_le_two (arccos_nonneg _)) (by linarith)] at hlt
  unfold switchedCoefficient Gaussian.gaussianCoefficient
  have : 3 / (4 * π) * arccos (5 / 6) < 3 / (4 * π) * (2 * α) := by
    have := pi_pos
    gcongr
  linarith [show 3 / (4 * π) * (2 * α) = 3 / (2 * π) * α by ring]

/-- Sharp upper bound on `arccos (5 / 6) ≈ 0.58568554`: by `cos_bound` at
`5856858 / (256 * 10^7)` and eight doublings, `cos (5856858 / 10^7) ≤ 5 / 6`. -/
theorem arccos_five_sixths_le : arccos (5 / 6) ≤ 5856858 / 10000000 := by
  have hcos : cos (5856858 / 10000000) ≤ 5 / 6 := by
    have hb := cos_bound (x := 5856858 / 2560000000) (by norm_num)
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 5856858 / 2560000000)] at hb
    have h0 : cos (5856858 / 2560000000) ≤ 49999869145329 / 50000000000000 := by
      linarith [(abs_le.mp hb).2]
    have h1 := Gaussian.cos_two_mul_le (by norm_num) h0
      (v := 49999476582001 / 50000000000000) (by norm_num)
    have h2 := Gaussian.cos_two_mul_le (by norm_num) h1
      (v := 49997906338963 / 50000000000000) (by norm_num)
    have h3 := Gaussian.cos_two_mul_le (by norm_num) h2
      (v := 49991625531189 / 50000000000000) (by norm_num)
    have h4 := Gaussian.cos_two_mul_le (by norm_num) h3
      (v := 99933009860051 / 100000000000000) (by norm_num)
    have h5 := Gaussian.cos_two_mul_le (by norm_num) h4
      (v := 49866064596891 / 50000000000000) (by norm_num)
    have h6 := Gaussian.cos_two_mul_le (by norm_num) h5
      (v := 19785990374101 / 20000000000000) (by norm_num)
    have h7 := Gaussian.cos_two_mul_le (by norm_num) h6
      (v := 95742707542009 / 100000000000000) (by norm_num)
    have h8 := Gaussian.cos_two_mul_le (by norm_num) h7
      (v := 41666660474747 / 50000000000000) (by norm_num)
    have hval : (5856858 / 10000000 : ℝ) =
        2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (5856858 / 2560000000)))))))) := by norm_num
    rw [hval]
    exact h8.trans (by norm_num)
  have hle : cos (5856858 / 10000000) ≤ 5 / 6 := hcos
  exact (arccos_le_arccos hle).trans_eq (arccos_cos (by norm_num) (by linarith [pi_gt_d20]))

/-- **The sharpened numerical bound.** The circuit coefficient
`1 + 2π / (3 arccos (5 / 6)) ≈ 4.575972` is at least `457597 / 100000 = 4.57597`. -/
theorem circuitCoefficient_ge_457597 :
    (457597 / 100000 : ℝ) ≤ 1 + 2 * π / (3 * arccos (5 / 6)) := by
  have ha : 0 < arccos (5 / 6) := arccos_pos.mpr (by norm_num)
  have hdiv : (357597 / 100000 : ℝ) ≤ 2 * π / (3 * arccos (5 / 6)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [pi_gt_d20, arccos_five_sixths_le]
  linarith

/-- **The clean rational lower bound `183 / 40 = 4.575`.** -/
theorem circuitCoefficient_ge_183_div_40 :
    (183 / 40 : ℝ) ≤ 1 + 2 * π / (3 * arccos (5 / 6)) :=
  le_trans (by norm_num) circuitCoefficient_ge_457597

/-- **The quadratic-form correlation threshold** `1 + π / (3 arccos (5 / 6)) ≈ 2.787986` is at
least `278798 / 100000 = 2.78798`. -/
theorem correlationThreshold_ge :
    (278798 / 100000 : ℝ) ≤ 1 + π / (3 * arccos (5 / 6)) := by
  linarith [circuitCoefficient_ge_457597,
    show 2 * π / (3 * arccos (5 / 6)) = 2 * (π / (3 * arccos (5 / 6))) by ring]

end Cslib.Circuits.Frontier.Switched
