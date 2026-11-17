/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.CommunityDetection.Spectral
public import CslibFrontier.Probability.StochasticBlockModel.Recovery
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact spectral recovery in the dense two-community stochastic block model

The centered leading-eigenvector algorithm with one weighted cleanup step recovers the hidden
labels, up to global swap, with failure probability at most
`2 exp (-n) + 2 n exp (-d² n / 2)` when `d = (p-q)/2 > 0` and `200 < d³ n`.
The guarantee is uniform over labelings and hence over every prior on labels. Neither balance
nor independence between the spectral estimate and the cleanup votes is assumed.

These are complete probability guarantees for the exact mathematical eigenvector specification.
They do not assert a native running-time certificate or a sharp sparse recovery threshold.
The finite condition uses the shared symmetric quadratic-net bound `‖N‖ ≤ (5/2) √n`,
followed by sign rounding and a deterministic cleanup margin. The constants are sufficient,
not claimed optimal.
-/

public section

namespace Cslib.Algorithms.CommunityDetection

open Finset Real BitString Probability.StochasticBlockModel
open scoped unitInterval

variable {n : ℕ}

private theorem dense_parameters {d : ℝ} (hd : 0 < d) (hd₁ : d ≤ 1)
    (hsize : 200 < d ^ 3 * (n : ℝ)) :
    0 < n ∧ 2 * ((5 / 2) * sqrt n) ≤ d * n ∧
      16 * n * ((5 / 2) * sqrt n / (d * n)) ^ 2 < d * n / 2 := by
  have hn : 0 < n := by
    by_contra h
    have hz : n = 0 := Nat.eq_zero_of_not_pos h
    norm_num [hz] at hsize
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlarge : 25 ≤ d ^ 2 * (n : ℝ) := by
    have hmono := mul_nonneg (sub_nonneg.mpr hd₁)
      (mul_nonneg (sq_nonneg d) hnR.le)
    nlinarith only [hsize, hmono]
  have hsmall : 5 * sqrt n ≤ d * n := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith only [mul_le_mul_of_nonneg_right hlarge hnR.le,
      Real.sq_sqrt (Nat.cast_nonneg n)]
  have hbudget : 16 * n * ((5 / 2) * sqrt n / (d * n)) ^ 2 = 100 / d ^ 2 := by
    simp only [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    field_simp
    ring
  refine ⟨hn, by nlinarith only [hsmall], ?_⟩
  rw [hbudget]
  apply (div_lt_iff₀ (sq_pos_of_pos hd)).mpr
  nlinarith only [hsize]

/-- On the high-probability noise and row-margin events, the explicit dense-size condition
makes one spectral rounding step and one cleanup step recover the hidden labels up to swap. -/
theorem recoverSpectral_sample_eq_or_not (p q : I) (g : Fin n → Bool) (ω : Coins n)
    (hpq : (q : ℝ) < p) (hsize : 200 < (gap p q) ^ 3 * (n : ℝ))
    (hnoise : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise p q g ω)‖ ≤ (5 / 2) * sqrt n)
    (hmargin : ∀ i, gap p q * n / 2 <
      signVal (g i) * ∑ j, shiftedCenteredAdjacency p q (sample ω) i j * signVal (g j)) :
    recoverSpectral p q (sample ω) = g ∨
      recoverSpectral p q (sample ω) = fun i => !g i := by
  have hd : 0 < gap p q := by dsimp [gap]; linarith
  have hd₁ : gap p q ≤ 1 := by
    have hp := p.2.2
    have hq := q.2.1
    dsimp [gap]
    linarith
  obtain ⟨hn, hsmall, hbudget⟩ := dense_parameters hd hd₁ hsize
  apply recoverSpectral_eq_or_not_of_opNorm_le p q (sample ω) g hn hd
    (show 0 ≤ (5 / 2) * sqrt n by positivity) hsmall
  · simpa only [shiftedCenteredAdjacency_sample p q g ω, add_sub_cancel_left] using hnoise
  · exact fun i => hbudget.trans (hmargin i)

/-- The actual conditional SBM law satisfies the finite exact-recovery bound, uniformly over
all hidden labelings. The output is compared with the labels modulo a global swap. -/
theorem coinLaw_recoverSpectral_failure_le (p q : I) (g : Fin n → Bool)
    (hpq : (q : ℝ) < p) (hsize : 200 < (gap p q) ^ 3 * (n : ℝ)) :
    ((coinLaw p q g).toOuterMeasure {ω |
      ¬ (recoverSpectral p q (sample ω) = g ∨
        recoverSpectral p q (sample ω) = fun i => !g i)}).toReal ≤
      2 * exp (-(n : ℝ)) + 2 * n * exp (-(gap p q) ^ 2 * n / 2) := by
  apply coinLaw_failure_le_of_noise_margin p q g _ (by dsimp [gap]; linarith)
  intro ω hnoise hmargin hfail
  exact hfail (recoverSpectral_sample_eq_or_not p q g ω hpq hsize hnoise hmargin)

open scoped Classical in
/-- The exact spectral solver recovers the hidden labels under any prior, with the displayed
finite failure bound. Only the graph is observed; `p` and `q` are fixed public parameters.
This is a distributional-search probability guarantee, not a computational-model certificate. -/
theorem searchProblem_recoverSpectral_failure_le (p q : I)
    (prior : PMF (Fin n → Bool)) (hpq : (q : ℝ) < p)
    (hsize : 200 < (gap p q) ^ 3 * (n : ℝ)) :
    ((searchProblem p q prior).experiment (fun G => PMF.pure (recoverSpectral p q G))
      false).toReal ≤
        2 * exp (-(n : ℝ)) + 2 * n * exp (-(gap p q) ^ 2 * n / 2) := by
  apply searchProblem_failure_le_of_fixedLabels p q prior
    (fun G => recoverSpectral p q G) (by positivity)
  intro g
  have hrecover (ω : Coins n) :
      @recoverSpectral n p q (sample ω) (fun _ _ => Classical.propDecidable _) =
        recoverSpectral p q (sample ω) :=
    congrArg (fun d : DecidableRel (sample ω).Adj => @recoverSpectral n p q (sample ω) d)
      (Subsingleton.elim _ _)
  simp only [hrecover]
  exact coinLaw_recoverSpectral_failure_le p q g hpq hsize

end Cslib.Algorithms.CommunityDetection
