/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Probability.SmallBias.Pointwise

/-! Both bounds of [Goldreich2007DraftR4], Exercise 8.34, in the printed form: an `ε`-biased
distribution `X` on `t` bits has every point probability within `ε` of `2⁻ᵗ`, and lies within
statistical distance `2 ^ (t / 2) ε` of uniform. A point mass on one bit is `1`-biased, and its
point probability `1` is exactly `1 / 2` from `2⁻¹`, so the pointwise bound
`|2ᵗ Pr[X = x] - 1| ≤ (2ᵗ - 1) ε` of `IsSmallBias.abs_mul_mass_sub_one_le` is attained. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SmallBiasPointwise

open Cslib.BitString Cslib.Probability.PMF

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ε : ℝ} {X : PMF (ι → Bool)}

-- Exercise 8.34, pointwise bound, as printed (`ε ≥ 0`, which holds whenever `t ≥ 1`).
example (hX : IsSmallBias ε X) (hε : 0 ≤ ε) (x : ι → Bool) :
    |(X x).toReal - 1 / 2 ^ Fintype.card ι| ≤ ε := by
  have h := hX.abs_mul_mass_sub_one_le x
  have hpos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have heq : (X x).toReal - 1 / 2 ^ Fintype.card ι =
      (2 ^ Fintype.card ι * (X x).toReal - 1) / 2 ^ Fintype.card ι := by
    field_simp
  rw [heq, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  nlinarith

-- Exercise 8.34, statistical-distance bound, as printed.
example (hX : IsSmallBias ε X) (hε : 0 ≤ ε) :
    dist X (uniformOfFintype (ι → Bool)) ≤ Real.sqrt (2 ^ Fintype.card ι) * ε := by
  refine hX.dist_uniform_le.trans ?_
  have h : Real.sqrt (2 ^ Fintype.card ι - 1) ≤ Real.sqrt (2 ^ Fintype.card ι) :=
    Real.sqrt_le_sqrt (by linarith)
  have h0 : 0 ≤ Real.sqrt (2 ^ Fintype.card ι - 1) * ε := by positivity
  nlinarith

-- The pointwise bound is attained by a point mass on one bit.
example : |2 ^ Fintype.card Unit * ((PMF.pure (fun _ : Unit => true)) (fun _ => true)).toReal - 1|
    = (2 ^ Fintype.card Unit - 1) * 1 := by
  norm_num

example : IsSmallBias 1 (PMF.pure (fun _ : Unit => true)) :=
  isSmallBias_one _

end CslibFrontierTests.SmallBiasPointwise
