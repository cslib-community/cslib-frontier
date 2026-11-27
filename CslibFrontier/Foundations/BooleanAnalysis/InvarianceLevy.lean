/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Invariance
import CslibFrontier.Foundations.Probability.Multilinear.InvarianceLevy

/-!
# The Lévy distance in the Basic Invariance Principle on the cube

**Corollary 11.70**, first statement, of [O'Donnell][ODonnell2014] for functions on the cube: if
`f : (ι → Bool) → ℝ` has degree at most `k`, `Var[f] ≤ 1` and every influence at most `ε`, and
the `y i` are independent with laws `μ i` satisfying Hypothesis 11.65 (for instance standard
Gaussians), then the distribution function of `f` at uniformly random bits and that of the Fourier
expansion of `f` at `y` are within Lévy distance `δ = 4 · 2ᵏ · ε^(1/5)`:
`Pr[f(y) ≤ u - δ] - δ ≤ Pr_x[f(x) ≤ u] ≤ Pr[f(y) ≤ u + δ] + δ` for every `u`, where
`Pr_x[f(x) ≤ u]` is the density `dens {x | f x ≤ u}`. This is
`ProbabilityTheory.measureReal_multilinearEval_le_le_add` for uniform random signs, translated by
`measureReal_pi_rademacher_multilinearEval_le`.

## Main results

* `Cslib.BitString.dens_le_le_measureReal_multilinearEval_le_add`,
  `Cslib.BitString.measureReal_multilinearEval_le_sub_le_dens`: Corollary 11.70, first statement,
  on the cube.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 11.6.
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

namespace Cslib.BitString

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Measure ℝ)
  [∀ i, IsProbabilityMeasure (μ i)]

/-- **Corollary 11.70 on the cube**, first statement, upper bound
[O'Donnell, Corollary 11.70][ODonnell2014]: if `f` on the cube has degree at most `k`, variance at
most `1` and every influence at most `ε ≥ 0`, then
`Pr_x[f(x) ≤ u] ≤ Pr[f(y) ≤ u + δ] + δ` for every `u`, with `δ = 4 · 2ᵏ · ε^(1/5)`, where `x` is
uniform on the cube and `f(y)` is the Fourier expansion of `f` at independent `y i` with laws
`μ i` satisfying Hypothesis 11.65. -/
theorem dens_le_le_measureReal_multilinearEval_le_add (hμ : ∀ i, HasInvarianceMoments (μ i))
    {f : (ι → Bool) → ℝ} {k : ℕ} (hf : totalDegree f ≤ k)
    (hvar : 𝔼 x, (f x - 𝔼 y, f y) ^ 2 ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ i, influence i f ≤ ε)
    (u : ℝ) :
    (dens {x | f x ≤ u} : ℝ) ≤ (Measure.pi μ).real
        {y | multilinearEval (fourierCoeff f) y ≤ u + 4 * 2 ^ k * ε ^ (1 / 5 : ℝ)} +
      4 * 2 ^ k * ε ^ (1 / 5 : ℝ) := by
  rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq] at hvar
  rw [← measureReal_pi_rademacher_multilinearEval_le]
  exact measureReal_multilinearEval_le_le_add (fun _ => rademacher) μ
    (fun _ => hasInvarianceMoments_rademacher) hμ (totalDegree_le_iff_fourierCoeff_eq_zero.1 hf)
    hvar hε0 (fun i => (multilinearInfluence_fourierCoeff f i).trans_le (hε i)) u

/-- **Corollary 11.70 on the cube**, first statement, lower bound
[O'Donnell, Corollary 11.70][ODonnell2014]: in the setting of
`dens_le_le_measureReal_multilinearEval_le_add`, `Pr[f(y) ≤ u - δ] - δ ≤ Pr_x[f(x) ≤ u]` for every
`u`, with `δ = 4 · 2ᵏ · ε^(1/5)`. Together, the two bound the Lévy distance between `f(x)` and
`f(y)` by `δ = O(2ᵏ ε^(1/5))`. -/
theorem measureReal_multilinearEval_le_sub_le_dens (hμ : ∀ i, HasInvarianceMoments (μ i))
    {f : (ι → Bool) → ℝ} {k : ℕ} (hf : totalDegree f ≤ k)
    (hvar : 𝔼 x, (f x - 𝔼 y, f y) ^ 2 ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ i, influence i f ≤ ε)
    (u : ℝ) :
    (Measure.pi μ).real
        {y | multilinearEval (fourierCoeff f) y ≤ u - 4 * 2 ^ k * ε ^ (1 / 5 : ℝ)} -
        4 * 2 ^ k * ε ^ (1 / 5 : ℝ) ≤ (dens {x | f x ≤ u} : ℝ) := by
  rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq] at hvar
  rw [← measureReal_pi_rademacher_multilinearEval_le]
  exact measureReal_multilinearEval_le_sub_le (fun _ => rademacher) μ
    (fun _ => hasInvarianceMoments_rademacher) hμ (totalDegree_le_iff_fourierCoeff_eq_zero.1 hf)
    hvar hε0 (fun i => (multilinearInfluence_fourierCoeff f i).trans_le (hε i)) u

end Cslib.BitString
