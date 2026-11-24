/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Multilinear.Bonami
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.Probability.LevyDistance
import CslibFrontier.Foundations.Probability.Multilinear.Invariance

/-!
# The Lévy distance in the Basic Invariance Principle

**Corollary 11.70**, first statement, of [O'Donnell][ODonnell2014] (Exercise 11.44): in the
setting of Corollary 11.67 (`F` of degree at most `k` with `Var[F] ≤ 1` and every influence at
most `ε`, and independent variables `x`, `y` whose laws satisfy Hypothesis 11.65), `F(x)` and
`F(y)` have Lévy distance at most `δ = 4 · 2ᵏ · ε^(1/5)`:
`Pr[F(y) ≤ u - δ] - δ ≤ Pr[F(x) ≤ u] ≤ Pr[F(y) ≤ u + δ] + δ` for every `u`.

The proof smooths the step `1_{s ≤ u}` by the four-fold moving average of a ramp
(`Real.stepSmoothing`), which is `1` on `(-∞, u]`, `0` on `[u + η, ∞)` and has
`|φ⁗| ≤ 5000 / η⁴`. Corollary 11.67 bounds `|E[φ(F(x))] - E[φ(F(y))]|` by
`5000 / η⁴ · k 9ᵏ ε / 12`, so `Pr[F(x) ≤ u] ≤ Pr[F(y) ≤ u + η] + 1250 k 9ᵏ ε / (3 η⁴)`
(`ProbabilityTheory.measureReal_le_le_add_div_pow_of_forall_contDiff`). Taking `η = δ` makes the
error at most `δ` (`ProbabilityTheory.measureReal_le_le_add_of_forall_contDiff`), since
`1250 k 9ᵏ ε / 3 ≤ 1024 · 32ᵏ ε = δ⁵` by `k 9ᵏ ≤ 18ᵏ ≤ 32ᵏ`.

The second statement of Corollary 11.70, the bound `(1/ρ)^O(k) ε^(1/8)` in the setting of
[O'Donnell, Remark 11.66][ODonnell2014] (`(2, 3, ρ)`-hypercontractive variables), is not
formalized, since the Invariance Principle of Remark 11.66 is not.

## Main results

* `ProbabilityTheory.measureReal_multilinearEval_le_le_add`,
  `ProbabilityTheory.measureReal_multilinearEval_le_sub_le`: Corollary 11.70, first statement.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 11.6.
-/

public section

open MeasureTheory Finset Real

namespace ProbabilityTheory

/-- The arithmetic of Corollary 11.70: `2³ · 5⁴ · k 9ᵏ ε / 12 ≤ (4 · 2ᵏ · ε^(1/5))⁵`, since
`k 9ᵏ ≤ 18ᵏ ≤ 32ᵏ`. -/
private theorem pow_mul_mul_nine_pow_le (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    2 ^ (4 - 1) * ((4 : ℕ) + 1 : ℝ) ^ 4 * (k * 9 ^ k * ε / 12) ≤
      (4 * 2 ^ k * ε ^ (1 / 5 : ℝ)) ^ (4 + 1) := by
  have hk : (k : ℝ) * 9 ^ k ≤ 32 ^ k := by
    have h2 : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast k.lt_two_pow_self.le
    calc (k : ℝ) * 9 ^ k ≤ 2 ^ k * 9 ^ k := by gcongr
      _ = 18 ^ k := by rw [← mul_pow]; norm_num
      _ ≤ 32 ^ k := by gcongr; norm_num
  have he : (ε ^ (1 / 5 : ℝ)) ^ 5 = ε := by
    simpa using Real.rpow_inv_natCast_pow hε (n := 5) (by norm_num)
  rw [mul_pow, mul_pow, he, ← pow_mul, mul_comm k 5, pow_mul]
  norm_num
  have h0 : 0 ≤ (k : ℝ) * 9 ^ k * ε := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hk hε]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (μ ν : ι → Measure ℝ)
  [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]

/-- **Corollary 11.70**, first statement, upper bound
[O'Donnell, Corollary 11.70][ODonnell2014]: in the setting of
`abs_integral_comp_multilinearEval_sub_le_of_influence_le` (Corollary 11.67: `F` of degree at
most `k`, `Var[F] = ∑_{S ≠ ∅} F̂(S) ^ 2 ≤ 1`, `Inf_t[F] ≤ ε` for every `t`, and laws satisfying
Hypothesis 11.65), `Pr[F(x) ≤ u] ≤ Pr[F(y) ≤ u + δ] + δ` for every `u`, with
`δ = 4 · 2ᵏ · ε^(1/5)`. The second statement, in the setting of Remark 11.66, is not
formalized. -/
theorem measureReal_multilinearEval_le_le_add (hμ : ∀ i, HasInvarianceMoments (μ i))
    (hν : ∀ i, HasInvarianceMoments (ν i)) {k : ℕ} {c : Finset ι → ℝ}
    (hc : ∀ S, k < #S → c S = 0) (hvar : ∑ S with S ≠ ∅, c S ^ 2 ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ t, multilinearInfluence c t ≤ ε) (u : ℝ) :
    (Measure.pi μ).real {z | multilinearEval c z ≤ u} ≤
      (Measure.pi ν).real {z | multilinearEval c z ≤ u + 4 * 2 ^ k * ε ^ (1 / 5 : ℝ)} +
        4 * 2 ^ k * ε ^ (1 / 5 : ℝ) :=
  measureReal_le_le_add_of_forall_contDiff (m := 4)
    (B := k * 9 ^ k * ε / 12) (continuous_multilinearEval c).aemeasurable
    (continuous_multilinearEval c).aemeasurable (fun φ C hφ hC =>
      (abs_integral_comp_multilinearEval_sub_le_of_influence_le μ ν hμ hν hc hvar hε0 hε hφ
        hC).trans_eq (by ring)) (by positivity) (pow_mul_mul_nine_pow_le k hε0) u

/-- **Corollary 11.70**, first statement, lower bound
[O'Donnell, Corollary 11.70][ODonnell2014]: in the setting of
`measureReal_multilinearEval_le_le_add`, `Pr[F(y) ≤ u - δ] - δ ≤ Pr[F(x) ≤ u]` for every `u`, with
`δ = 4 · 2ᵏ · ε^(1/5)`. Together, the two bound the Lévy distance between `F(x)` and `F(y)` by
`δ = O(2ᵏ ε^(1/5))`. -/
theorem measureReal_multilinearEval_le_sub_le (hμ : ∀ i, HasInvarianceMoments (μ i))
    (hν : ∀ i, HasInvarianceMoments (ν i)) {k : ℕ} {c : Finset ι → ℝ}
    (hc : ∀ S, k < #S → c S = 0) (hvar : ∑ S with S ≠ ∅, c S ^ 2 ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ t, multilinearInfluence c t ≤ ε) (u : ℝ) :
    (Measure.pi ν).real {z | multilinearEval c z ≤ u - 4 * 2 ^ k * ε ^ (1 / 5 : ℝ)} -
        4 * 2 ^ k * ε ^ (1 / 5 : ℝ) ≤
      (Measure.pi μ).real {z | multilinearEval c z ≤ u} :=
  measureReal_le_sub_le_of_forall_contDiff (m := 4)
    (B := k * 9 ^ k * ε / 12) (continuous_multilinearEval c).aemeasurable
    (continuous_multilinearEval c).aemeasurable (fun φ C hφ hC =>
      (abs_integral_comp_multilinearEval_sub_le_of_influence_le μ ν hμ hν hc hvar hε0 hε hφ
        hC).trans_eq (by ring)) (by positivity) (pow_mul_mul_nine_pow_le k hε0) u

end ProbabilityTheory
