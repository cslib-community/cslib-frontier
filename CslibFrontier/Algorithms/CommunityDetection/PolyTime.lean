/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.CommunityDetection.Program
public import CslibFrontier.Algorithms.CommunityDetection.PowerAnalysis
public import CslibFrontier.Probability.StochasticBlockModel.Recovery
public import CslibFrontier.Computability.Probabilistic.PPT
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Native polynomial-time exact recovery for dense community detection

For every fixed real pair of probabilities `p > q`, there are two fixed natural parameters
such that one native polynomial-time program recovers the hidden labels up to global swap,
with failure tending to zero under every sequence of label priors. Neither the graph size nor
the prior selects the program. The probabilities need not be rational or have computable real
representations: the machine contains only its two finite integer constants.

Put `d = (p-q)/2`. Choose a positive natural `D` with `32 ≤ D*d` and take
`c = floor(D²*(p+q)/2)`. The program forms `D²*A-c*(J-I)`, searches integer power columns at
threshold `D*n`, rounds signs, and performs one weighted vote. For `2*D²+25*D³ ≤ n`, the
failure probability is at most `2 exp(-n) + 2 n exp(-d²*n/2)`. The squared residual estimate
allows a fraction of incorrect signs proportional to the gap before cleanup. Together with the
`(5/2) √n` noise bound, this gives a cubic rather than quartic size condition in `D`.

The input encoding is a framed unary vertex count followed by the full row-major adjacency
word, of length `n²+2n+1` on canonical graphs. The output uses `encList encBool` and contains
one label per vertex. The presentation `DenseGraphInput.ofGraph` and indexed output reads
specify the meanings of these representations; they are not uncharged primitives of the
program. Every matrix operation and integer comparison belongs to `recoverInput` and its
unconditional native certificate from `Program`.

This is an original dense-regime computational theorem for the exact integer-power algorithm.
It does not claim to compute an exact real eigenvector or to attain sparse recovery thresholds.
-/

public section

namespace Cslib.Algorithms.CommunityDetection

open Filter Real BitString Probability Probability.StochasticBlockModel Turing.MultiTapeTM
open scoped Topology unitInterval

private theorem choose_integer_parameters (p q : I) (hpq : (q : ℝ) < p) :
    ∃ D c : ℕ, 32 ≤ (D : ℝ) * gap p q ∧ c ≤ D ^ 2 ∧
      |(D : ℝ) ^ 2 * midpoint p q - c| ≤ 1 := by
  have hd : 0 < gap p q := by dsimp [gap]; linarith
  obtain ⟨D, hD⟩ := exists_nat_gt (32 / gap p q)
  have hlarge : 32 < (D : ℝ) * gap p q := (div_lt_iff₀ hd).mp hD
  have hm₀ : 0 ≤ midpoint p q := by
    have hp := p.2.1
    have hq := q.2.1
    dsimp [Cslib.Probability.StochasticBlockModel.midpoint]
    linarith
  have hm₁ : midpoint p q ≤ 1 := by
    have hp := p.2.2
    have hq := q.2.2
    dsimp [Cslib.Probability.StochasticBlockModel.midpoint]
    linarith
  refine ⟨D, ⌊(D : ℝ) ^ 2 * midpoint p q⌋₊, hlarge.le, ?_, ?_⟩
  · apply Nat.floor_le_of_le
    simpa only [Nat.cast_pow, mul_one] using
      mul_le_mul_of_nonneg_left hm₁ (sq_nonneg (D : ℝ))
  · exact Nat.abs_sub_floor_le (mul_nonneg (sq_nonneg (D : ℝ)) hm₀)

private theorem power_size_parameters {D n : ℕ} {d : ℝ}
    (hD : 0 < D) (hgap : 32 ≤ (D : ℝ) * d) (hd : d ≤ 1 / 2)
    (hsize : 2 * D ^ 2 + 25 * D ^ 3 ≤ n) :
    0 < n ∧ 64 * ((D : ℝ) ^ 2 * ((5 / 2) * sqrt n) + n + D ^ 2) ^ 2 ≤
      d * (D * n) ^ 2 := by
  have hDsq : 0 < D ^ 2 := pow_pos hD _
  have hn : 0 < n := by omega
  have hD64 : (64 : ℝ) ≤ D := by
    have h := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
    linarith only [hgap, h]
  have hscale : 2 * (D : ℝ) ^ 2 ≤ n := by
    exact_mod_cast (show 2 * D ^ 2 ≤ n by omega)
  have hlarge : 25 * (D : ℝ) ^ 3 ≤ n := by
    exact_mod_cast (show 25 * D ^ 3 ≤ n by omega)
  let noiseBudget : ℝ := (D : ℝ) ^ 2 * ((5 / 2) * sqrt n)
  let centeringBudget : ℝ := n + (D : ℝ) ^ 2
  have hnoise : noiseBudget ^ 2 ≤ (D : ℝ) / 4 * (n : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hlarge
      (by positivity : 0 ≤ (D : ℝ) * (n : ℝ))
    dsimp only [noiseBudget]
    rw [mul_pow, mul_pow, sq_sqrt (Nat.cast_nonneg n)]
    nlinarith only [h]
  have hcentering : centeringBudget ^ 2 ≤ 9 / 4 * (n : ℝ) ^ 2 := by
    have h : centeringBudget ≤ 3 * (n : ℝ) / 2 := by
      dsimp only [centeringBudget]
      linarith only [hscale]
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ centeringBudget)
      (by positivity : 0 ≤ 3 * (n : ℝ) / 2)).mpr h
    nlinarith only [hs]
  have hreserve : 54 * (n : ℝ) ^ 2 ≤ (D : ℝ) * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith only [hD64] : (54 : ℝ) ≤ D) (sq_nonneg _)
  have hresidual : (noiseBudget + centeringBudget) ^ 2 ≤
      (D : ℝ) / 2 * (n : ℝ) ^ 2 := by
    nlinarith only [hnoise, hcentering, hreserve, sq_nonneg (noiseBudget - 2 * centeringBudget)]
  refine ⟨hn, ?_⟩
  have h := mul_le_mul_of_nonneg_right hgap
    (by positivity : 0 ≤ (D : ℝ) * (n : ℝ) ^ 2)
  change 64 * (noiseBudget + (n : ℝ) + (D : ℝ) ^ 2) ^ 2 ≤ _
  change (noiseBudget + ((n : ℝ) + (D : ℝ) ^ 2)) ^ 2 ≤ _ at hresidual
  nlinarith only [hresidual, h]

open scoped Classical in
private theorem recoverInput_correct_on_good_events {n : ℕ}
    (params : PowerParameters) (p q : I) (g : Fin n → Bool) (ω : Coins n)
    (hpq : (q : ℝ) < p) (hresolution : 32 ≤ (params.resolution : ℝ) * gap p q)
    (hcenter_le : params.center ≤ params.resolution ^ 2)
    (hcenter : |(params.resolution : ℝ) ^ 2 * midpoint p q - params.center| ≤ 1)
    (hsize : 2 * params.resolution ^ 2 + 25 * params.resolution ^ 3 ≤ n)
    (hnoise : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise p q g ω)‖ ≤ (5 / 2) * sqrt n)
    (hmargin : ∀ i, gap p q * n / 2 <
      signVal (g i) * ∑ j, shiftedCenteredAdjacency p q (sample ω) i j * signVal (g j)) :
    (fun i : Fin n =>
      (recoverInput params (DenseGraphInput.ofGraph (sample ω))).getD i.val false) = g ∨
    (fun i : Fin n =>
      (recoverInput params (DenseGraphInput.ofGraph (sample ω))).getD i.val false) =
        fun i => !g i := by
  have hD : 0 < params.resolution := by
    by_contra h
    have hz : params.resolution = 0 := Nat.eq_zero_of_not_pos h
    norm_num [hz] at hresolution
  have hd : gap p q ≤ 1 / 2 := by dsimp [gap]; linarith [p.2.2, q.2.1]
  obtain ⟨hn, hbudget⟩ := power_size_parameters hD hresolution hd hsize
  simp only [recoverInput_ofGraph, List.getD_ofFn]
  have hrecover :
      @recoverPower n params (sample ω) (fun _ _ => Classical.propDecidable _) =
        recoverPower params (sample ω) :=
    congrArg (fun d : DecidableRel (sample ω).Adj => @recoverPower n params (sample ω) d)
      (Subsingleton.elim _ _)
  simp only [hrecover]
  exact recoverPower_sample_eq_or_not_of_bounds params p q g ω hn hpq hD hcenter_le hcenter
    ((5 / 2) * sqrt n) (by positivity) hnoise (by linarith) hbudget hmargin

open scoped Classical in
/-- The actual finite integer program recovers the SBM labels up to swap with the stated
failure bound whenever its fixed centering parameters and the graph size satisfy these explicit
sufficient inequalities. Its runtime certificate is unconditional and supplied by `Program`. -/
theorem recoverInput_failure_le {n : ℕ} (params : PowerParameters) (p q : I)
    (prior : PMF (Fin n → Bool)) (hpq : (q : ℝ) < p)
    (hresolution : 32 ≤ (params.resolution : ℝ) * gap p q)
    (hcenter_le : params.center ≤ params.resolution ^ 2)
    (hcenter : |(params.resolution : ℝ) ^ 2 * midpoint p q - params.center| ≤ 1)
    (hsize : 2 * params.resolution ^ 2 + 25 * params.resolution ^ 3 ≤ n) :
    ((searchProblem p q prior).experiment
      (fun G => PMF.pure (fun i : Fin n =>
        (recoverInput params (DenseGraphInput.ofGraph G)).getD i.val false)) false).toReal ≤
      2 * exp (-(n : ℝ)) + 2 * n * exp (-(gap p q) ^ 2 * n / 2) := by
  apply searchProblem_failure_le_of_fixedLabels p q prior
    (fun G i => (recoverInput params (DenseGraphInput.ofGraph G)).getD i.val false)
    (by positivity)
  intro g
  apply coinLaw_failure_le_of_noise_margin p q g _ (by dsimp [gap]; linarith)
  intro ω hnoise hmargin hfail
  exact hfail (recoverInput_correct_on_good_events params p q g ω hpq hresolution
    hcenter_le hcenter hsize hnoise hmargin)

open scoped Classical in
/-- For each fixed real pair `p > q`, one native strict PPT program with two finite integer
constants has vanishing actual recovery failure under every sequence of label priors. The
constants and machine are fixed before the size and prior vary; the program observes only the
dense graph and its dimension, and returns labels up to global swap. -/
theorem exists_recoverInput_ppt_tendsto_failure (p q : I) (hpq : (q : ℝ) < p) :
    ∃ params : PowerParameters,
      IsPPTOn encDenseGraphInput (encList encBool) (fun x => pure (recoverInput params x)) ∧
      ∀ prior : ∀ n, PMF (Fin n → Bool),
        Tendsto (fun n => (searchProblem p q (prior n)).experiment
          (fun G => PMF.pure (fun i : Fin n =>
            (recoverInput params (DenseGraphInput.ofGraph G)).getD i.val false)) false)
          atTop (𝓝 0) := by
  obtain ⟨D, c, hresolution, hcenter_le, hcenter⟩ := choose_integer_parameters p q hpq
  let params : PowerParameters := ⟨D, c⟩
  refine ⟨params, (computableInPolyTime_recoverInput params).isPPTOn, ?_⟩
  intro prior
  apply tendsto_searchProblem_failure_of_eventually_noise_margin p q
    (fun n G i => (recoverInput params (DenseGraphInput.ofGraph G)).getD i.val false) prior hpq
  filter_upwards [eventually_ge_atTop (2 * D ^ 2 + 25 * D ^ 3)] with n hn
  intro g ω hnoise hmargin
  exact recoverInput_correct_on_good_events params p q g ω hpq hresolution
    hcenter_le hcenter hn hnoise hmargin

end Cslib.Algorithms.CommunityDetection
