/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Probability.IID.Birthday

/-!
# Tests for the birthday collision bounds

Checks for `CslibFrontier/Probability/IID/Birthday.lean` as a `module` client with an ordinary
import: the exact collision probability of two fair coins, three samples from a two-point set
(where the hypothesis of the Theorem B.1(ii) bound is necessary), the lower bound for a
non-uniform law, the lower bound with a smaller exponent for every law on a four-point set, the
Theorem B.1(ii) bound on a four-point set, and the value `0` of the lower bound for `k ≤ 1`.

Outside `namespace Cslib.Probability.PMF` the uniform law is written
`Cslib.Probability.PMF.uniformOfFintype`: there the bare `PMF.uniformOfFintype` is a deprecated
Mathlib name with a different argument.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.ProbabilityBirthday

open Cslib.Probability.PMF

/-- Two fair coins collide with probability exactly `1 / 2`. -/
example : ((iid (Cslib.Probability.PMF.uniformOfFintype Bool) 2).toOuterMeasure
    {x | ¬ Function.Injective x}).toReal = 1 / 2 := by
  have hc := toOuterMeasure_toReal_add_compl (iid (Cslib.Probability.PMF.uniformOfFintype Bool) 2)
    {x | Function.Injective x}
  change _ + ((iid (Cslib.Probability.PMF.uniformOfFintype Bool) 2).toOuterMeasure
    {x | ¬ Function.Injective x}).toReal = 1 at hc
  have h2 : ((2 : ℕ).descFactorial 2 : ℝ) / ((2 : ℕ) : ℝ) ^ 2 = 1 / 2 := by
    norm_num [Nat.descFactorial]
  rw [iid_uniformOfFintype_injective, Fintype.card_bool, h2] at hc
  linarith

/-- Three samples from a two-point set are never distinct. -/
theorem iid_bool_three_injective :
    ((iid (Cslib.Probability.PMF.uniformOfFintype Bool) 3).toOuterMeasure
      {x | Function.Injective x}).toReal = 0 := by
  rw [iid_uniformOfFintype_injective]
  norm_num [Fintype.card_bool, Nat.descFactorial]

/-- The hypothesis `2 k ≤ n + 2` of the Theorem B.1(ii) bound is needed: for three samples from a
two-point set (`2 * 3 > 2 + 2`) the collision probability is `1`, above `1 - exp (-3)`. -/
example : ¬ ((iid (Cslib.Probability.PMF.uniformOfFintype Bool) 3).toOuterMeasure
    {x | ¬ Function.Injective x}).toReal ≤
      1 - Real.exp (-(((3 : ℕ) : ℝ) * ((3 : ℕ) - 1) / Fintype.card Bool)) := by
  have hc := toOuterMeasure_toReal_add_compl (iid (Cslib.Probability.PMF.uniformOfFintype Bool) 3)
    {x | Function.Injective x}
  change _ + ((iid (Cslib.Probability.PMF.uniformOfFintype Bool) 3).toOuterMeasure
    {x | ¬ Function.Injective x}).toReal = 1 at hc
  rw [iid_bool_three_injective] at hc
  have := Real.exp_pos (-(((3 : ℕ) : ℝ) * ((3 : ℕ) - 1) / Fintype.card Bool))
  intro h
  linarith

/-- The second lower bound for a non-uniform law: a point mass on a two-point set, `k = 2`. -/
example : min ((2 : ℝ) * (2 - 1) / (4 * 2)) 0.63 ≤
    ((iid (PMF.pure true) 2).toOuterMeasure {x | ¬ Function.Injective x}).toReal := by
  simpa [Fintype.card_bool] using min_le_iid_not_injective (PMF.pure true) 2

/-- Five samples of any law on a four-point set contain two equal samples with probability at
least `1 - exp (-2)`. -/
example (μ : PMF (Fin 4)) : 1 - Real.exp (-2) ≤
    ((iid μ 5).toOuterMeasure {x | ¬ Function.Injective x}).toReal :=
  one_sub_exp_neg_le_iid_not_injective_of_le μ (by norm_num [Fintype.card_fin])

/-- The Theorem B.1(ii) bound for two uniform samples from a four-point set. -/
example : ((iid (Cslib.Probability.PMF.uniformOfFintype (Fin 4)) 2).toOuterMeasure
    {x | ¬ Function.Injective x}).toReal ≤
      1 - Real.exp (-(((2 : ℕ) : ℝ) * ((2 : ℕ) - 1) / 4)) := by
  simpa [Fintype.card_fin] using
    iid_uniformOfFintype_not_injective_le_one_sub_exp_neg (α := Fin 4) (k := 2) (by simp)

/-- For `k = 0` and `k = 1` the first lower bound is `0`. -/
example : (1 : ℝ) - Real.exp (-(((0 : ℕ) : ℝ) * ((0 : ℕ) - 1) / (2 * Fintype.card Bool))) = 0 := by
  simp

example : (1 : ℝ) - Real.exp (-(((1 : ℕ) : ℝ) * ((1 : ℕ) - 1) / (2 * Fintype.card Bool))) = 0 := by
  simp

end CslibFrontierTests.ProbabilityBirthday
