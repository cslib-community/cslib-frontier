/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.StochasticBlockModel.RandomMatrix
public import CslibFrontier.Probability.StochasticBlockModel.Concentration
public import Mathlib.Topology.Instances.ENNReal.Lemmas
import CslibFrontier.Probability.PMF.Event
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Recovery from the stochastic block model's noise and margin events

The same two events support different recovery algorithms: the centered noise has operator
norm at most `(5/2) √n`, and every true-label row margin exceeds `gap * n / 2`. An event that is
excluded whenever both conditions hold has probability at most
`2 exp (-n) + 2 n exp (-gap² n / 2)`.

For any family of graph-only solvers that succeeds on these events for all sufficiently large
dimensions, the actual distributional-search failure tends to zero under every sequence of
label priors. This implication concerns probability, independently of a solver's computational
model. Algorithms supply their deterministic correctness argument and, separately, any native
efficiency certificate.
-/

public section

namespace Cslib.Probability.StochasticBlockModel

open Filter Real BitString
open scoped Topology unitInterval

variable {n : ℕ}

/-- A failure event excluded by the noise and true-label margin conditions has the displayed
finite bound. The estimate is uniform in the fixed hidden labeling. -/
theorem coinLaw_failure_le_of_noise_margin (p q : I) (g : Fin n → Bool)
    (failure : Set (Coins n)) (hgap : 0 ≤ gap p q)
    (hcorrect : ∀ ω,
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise p q g ω)‖ ≤ (5 / 2) * sqrt n →
      (∀ i, gap p q * n / 2 <
        signVal (g i) * ∑ j, shiftedCenteredAdjacency p q (sample ω) i j * signVal (g j)) →
      ω ∉ failure) :
    ((coinLaw p q g).toOuterMeasure failure).toReal ≤
      2 * exp (-(n : ℝ)) + 2 * n * exp (-(gap p q) ^ 2 * n / 2) := by
  let N : Set (Coins n) := {ω |
    (5 / 2) * sqrt n < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise p q g ω)‖}
  let D : Set (Coins n) := {ω | ∃ i : Fin n,
    signVal (g i) * ∑ j, shiftedCenteredAdjacency p q (sample ω) i j * signVal (g j) ≤
      gap p q * n / 2}
  have hsub : failure ⊆ N ∪ D := by
    intro ω hω
    by_cases hN : ω ∈ N
    · exact Or.inl hN
    by_cases hD : ω ∈ D
    · exact Or.inr hD
    exact (hcorrect ω (le_of_not_gt hN)
      (fun i => lt_of_not_ge (fun h => hD ⟨i, h⟩)) hω).elim
  have hprob := ENNReal.toReal_le_add
    (((coinLaw p q g).toOuterMeasure.mono hsub).trans
      (MeasureTheory.measure_union_le (μ := (coinLaw p q g).toOuterMeasure) N D))
    (PMF.toOuterMeasure_ne_top (coinLaw p q g) N)
    (PMF.toOuterMeasure_ne_top (coinLaw p q g) D)
  exact hprob.trans (add_le_add (noise_opNorm_gt_le p q g)
    (coinLaw_exists_low_margin_le p q g hgap))

private theorem tendsto_dense_error {d : ℝ} (hd : 0 < d) :
    Tendsto (fun n : ℕ => 2 * exp (-(n : ℝ)) +
      2 * (n : ℝ) * exp (-d ^ 2 * n / 2)) atTop (𝓝 0) := by
  have hfirst : Tendsto (fun n : ℕ => 2 * exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 2
  have hsecond : Tendsto (fun n : ℕ => 2 * (n : ℝ) * exp (-d ^ 2 * n / 2))
      atTop (𝓝 0) := by
    have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (d ^ 2 / 2)
      (by positivity)).comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 2
    simpa only [Function.comp_def, rpow_one, mul_zero, ← mul_assoc,
      ← neg_div, div_mul_eq_mul_div] using h
  simpa only [zero_add] using hfirst.add hsecond

/-- A graph-only solver family that eventually succeeds on the noise and true-label margin
events has vanishing actual failure under every sequence of label priors. No balance condition
or independence between the solver's estimate and its cleanup votes is assumed. -/
theorem tendsto_searchProblem_failure_of_eventually_noise_margin (p q : I)
    (solve : ∀ n, SimpleGraph (Fin n) → Fin n → Bool)
    (prior : ∀ n, PMF (Fin n → Bool)) (hpq : (q : ℝ) < p)
    (hcorrect : ∀ᶠ n : ℕ in atTop, ∀ (g : Fin n → Bool) (ω : Coins n),
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise p q g ω)‖ ≤ (5 / 2) * sqrt n →
      (∀ i, gap p q * n / 2 <
        signVal (g i) * ∑ j, shiftedCenteredAdjacency p q (sample ω) i j * signVal (g j)) →
      solve n (sample ω) = g ∨ solve n (sample ω) = fun i => !g i) :
    Tendsto (fun n => (searchProblem p q (prior n)).experiment
      (fun G => PMF.pure (solve n G)) false) atTop (𝓝 0) := by
  apply (ENNReal.tendsto_toReal_zero_iff (fun n =>
    ((searchProblem p q (prior n)).experiment
      (fun G => PMF.pure (solve n G))).apply_ne_top false)).mp
  have hd : 0 < gap p q := by dsimp [gap]; linarith
  refine squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_
    (tendsto_dense_error hd)
  filter_upwards [hcorrect] with n hn
  apply searchProblem_failure_le_of_fixedLabels p q (prior n) (solve n) (by positivity)
  intro g
  exact coinLaw_failure_le_of_noise_margin p q g _ hd.le
    (fun ω hnoise hmargin hfail => hfail (hn g ω hnoise hmargin))

end Cslib.Probability.StochasticBlockModel
