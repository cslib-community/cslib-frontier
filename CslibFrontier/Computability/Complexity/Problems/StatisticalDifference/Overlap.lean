/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.StatisticalDifference
public import CslibFrontier.Probability.BitString.AffineHash.Overlap
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic.Linarith

/-!
# Estimating the overlap of two circuit samplers

The smaller preimage fiber at each output contributes its cardinality to the statistical overlap
of the two uniform-output laws, normalized by the number of input words. Weighting pairs of affine
hash seeds as in `commonHashHits_overlap_bounds` estimates this overlap by counting objects with
short witnesses. For the polarized Statistical Difference thresholds `1/2048` and `2047/2048`,
the count, multiplied by `64`, has a factor-two gap around a power of two.

## Main definitions

* `Cslib.Complexity.SDInstance.affineOverlapCount` counts pairs of successful affine hash seeds
  for the two circuit output fibers, weighted by the size of the hash range.

## Main results

* `Cslib.Complexity.SDInstance.le_mul_affineOverlapCount_of_close` lower-bounds the count
  when the output distributions are close.
* `Cslib.Complexity.SDInstance.mul_affineOverlapCount_le_of_far` upper-bounds the count
  when the output distributions are far apart.
-/

public section

namespace Cslib.Complexity.SDInstance

open Finset BitString.LinearHash Circuits Circuits.Boolean
open scoped Cslib.Probability.PMF

/-- Count pairs of full affine hash seeds hitting both input fibers at an output `y`, with
`2 ^ j` possible tags when the digest has width `j`. -/
@[expose] def affineOverlapCount (x : SDInstance) : ℕ :=
  ∑ y : BitString x.outputs, ∑ j ∈ range (x.inputs + 1), 2 ^ j *
    #(commonHashHits j {r | x.left.eval interpretation r = y}
      {r | x.right.eval interpretation r = y}) ^ 2

private theorem affineOverlapCount_bounds (x : SDInstance) :
    2 ^ (x.inputs + (x.inputs * x.inputs + x.inputs) + (x.inputs * x.inputs + x.inputs)) *
        (1 - x.distance) ≤ 32 * (x.affineOverlapCount : ℝ) ∧
      (x.affineOverlapCount : ℝ) ≤
        4 * 2 ^ (x.inputs + (x.inputs * x.inputs + x.inputs) + (x.inputs * x.inputs + x.inputs)) *
          (1 - x.distance) := by
  classical
  let n := x.inputs
  let H := n * n + n
  let F (c : Circuit signature x.inputs x.outputs) (y : BitString x.outputs) :=
    univ.filter fun r => c.eval interpretation r = y
  let a (y : BitString x.outputs) := min #(F x.left y) #(F x.right y)
  let w (y : BitString x.outputs) := ∑ j ∈ range (n + 1),
    2 ^ j * #(commonHashHits j (F x.left y) (F x.right y)) ^ 2
  have pointwise (y : BitString x.outputs) :
      (2 ^ H) ^ 2 * a y ≤ 32 * w y ∧ w y ≤ 4 * (2 ^ H) ^ 2 * a y :=
    commonHashHits_overlap_bounds (F x.left y) (F x.right y)
  have hlo : ((2 : ℝ) ^ H) ^ 2 * ↑(∑ y, a y) ≤ 32 * (x.affineOverlapCount : ℝ) := by
    exact_mod_cast (show (2 ^ H) ^ 2 * (∑ y, a y) ≤ 32 * ∑ y, w y by
      simp only [mul_sum]
      exact sum_le_sum fun y _ => (pointwise y).1)
  have hhi : (x.affineOverlapCount : ℝ) ≤ 4 * ((2 : ℝ) ^ H) ^ 2 * ↑(∑ y, a y) := by
    exact_mod_cast (show (∑ y, w y) ≤ 4 * (2 ^ H) ^ 2 * ∑ y, a y by
      simp only [mul_sum]
      exact sum_le_sum fun y _ => (pointwise y).2)
  have hdist := Probability.PMF.sum_min_toReal
    (x.left.outputDist interpretation) (x.right.outputDist interpretation)
  have hm (c : Circuit signature x.inputs x.outputs) (y : BitString x.outputs) :
      (c.outputDist interpretation y).toReal = (#(F c y) : ℝ) / 2 ^ n := by
    rw [Circuit.outputDist, Probability.PMF.toReal_uniformOfFintype_map_apply,
      dens_eq_card_div_card, BitString.card]
    push_cast
    rfl
  simp only [hm, min_div_div_right (by positivity : (0 : ℝ) ≤ 2 ^ n), ← Nat.cast_min,
    ← sum_div, ← Nat.cast_sum] at hdist
  change (↑(∑ y, a y) : ℝ) / 2 ^ n = 1 - x.distance at hdist
  rw [div_eq_iff (by positivity)] at hdist
  rw [hdist] at hlo hhi
  change 2 ^ (n + H + H) * _ ≤ _ ∧ _ ≤ 4 * 2 ^ (n + H + H) * _
  simp only [pow_add]
  constructor <;> linarith

/-- Close circuit samplers admit at least the threshold number of tagged pairs after multiplying
the count by the number of six-bit strings. -/
theorem le_mul_affineOverlapCount_of_close {x : SDInstance} (h : x.distance ≤ 1 / 2048) :
    2 ^ (x.inputs + (x.inputs * x.inputs + x.inputs) + (x.inputs * x.inputs + x.inputs)) ≤
      64 * x.affineOverlapCount := by
  have hl := (affineOverlapCount_bounds x).1
  have hp : 0 ≤ (2 : ℝ) ^
      (x.inputs + (x.inputs * x.inputs + x.inputs) + (x.inputs * x.inputs + x.inputs)) := by
    positivity
  exact_mod_cast (by nlinarith [mul_nonneg hp (sub_nonneg.mpr h)] :
    (2 : ℝ) ^ (x.inputs + (x.inputs * x.inputs + x.inputs) + (x.inputs * x.inputs + x.inputs)) ≤
      64 * (x.affineOverlapCount : ℝ))

/-- For far circuit samplers, twice the count multiplied by the number of six-bit strings lies
below the same threshold. -/
theorem mul_affineOverlapCount_le_of_far {x : SDInstance} (h : 2047 / 2048 ≤ x.distance) :
    2 * (64 * x.affineOverlapCount) ≤
      2 ^ (x.inputs + (x.inputs * x.inputs + x.inputs) + (x.inputs * x.inputs + x.inputs)) := by
  have hu := (affineOverlapCount_bounds x).2
  have hp : 0 ≤ (2 : ℝ) ^
      (x.inputs + (x.inputs * x.inputs + x.inputs) + (x.inputs * x.inputs + x.inputs)) := by
    positivity
  exact_mod_cast (by nlinarith [mul_nonneg hp (sub_nonneg.mpr h)] :
    2 * (64 * (x.affineOverlapCount : ℝ)) ≤ (2 : ℝ) ^
      (x.inputs + (x.inputs * x.inputs + x.inputs) + (x.inputs * x.inputs + x.inputs)))

end Cslib.Complexity.SDInstance
