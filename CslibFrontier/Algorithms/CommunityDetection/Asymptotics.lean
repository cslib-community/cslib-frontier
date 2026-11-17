/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.CommunityDetection.Final
import Mathlib.Tactic.Linarith

/-!
# Vanishing failure probability for dense spectral community recovery

For fixed within-community and between-community probabilities `p > q`, the exact spectral
solver recovers all labels up to global swap with probability tending to one. The statement
holds for every sequence of priors on the hidden labels, with no balance assumption. It concerns
the actual distributional-search experiment, whose input to the solver is only the graph.

The finite bound is `2 exp (-n) + 2 n exp (-d² n / 2)`, where `d = (p-q)/2`. For fixed `d > 0`,
the size condition `200 < d³ n` eventually holds and both error terms tend to zero. This is
the dense regime: the probabilities are fixed as the number of vertices increases.

The solver uses an exact mathematical eigenvector. The result is a probability guarantee and
does not assert a native polynomial-time certificate for computing that eigenvector.

## Main results

* `Cslib.Algorithms.CommunityDetection.tendsto_searchProblem_recoverSpectral_failure`:
  vanishing actual failure under every sequence of label priors.
-/

public section

namespace Cslib.Algorithms.CommunityDetection

open Filter Real Probability.StochasticBlockModel
open scoped Topology unitInterval

open scoped Classical in
/-- For every fixed `p > q` and every sequence of priors on the hidden labels, the actual
failure probability of the exact centered spectral solver with cleanup tends to zero. Recovery
is modulo global label swap, and only the graph is observed. -/
theorem tendsto_searchProblem_recoverSpectral_failure (p q : I)
    (prior : ∀ n, PMF (Fin n → Bool)) (hpq : (q : ℝ) < p) :
    Tendsto (fun n => (searchProblem p q (prior n)).experiment
      (fun G => PMF.pure (recoverSpectral p q G)) false) atTop (𝓝 0) := by
  have hd : 0 < gap p q := by dsimp [gap]; linarith
  have hsize : ∀ᶠ n : ℕ in atTop, 200 < (gap p q) ^ 3 * (n : ℝ) :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (pow_pos hd 3)).eventually
      (eventually_gt_atTop 200)
  apply tendsto_searchProblem_failure_of_eventually_noise_margin p q
    (fun _ G => recoverSpectral p q G) prior hpq
  filter_upwards [hsize] with n hn
  intro g ω hnoise hmargin
  have hrecover :
      @recoverSpectral n p q (sample ω) (fun _ _ => Classical.propDecidable _) =
        recoverSpectral p q (sample ω) :=
    congrArg (fun d : DecidableRel (sample ω).Adj => @recoverSpectral n p q (sample ω) d)
      (Subsingleton.elim _ _)
  simp only [hrecover]
  exact recoverSpectral_sample_eq_or_not p q g ω hpq hn hnoise hmargin

end Cslib.Algorithms.CommunityDetection
