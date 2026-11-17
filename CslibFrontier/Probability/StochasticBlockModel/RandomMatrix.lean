/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.StochasticBlockModel.Model
public import Mathlib.Analysis.CStarAlgebra.Matrix
import CslibFrontier.Probability.RandomMatrix.Independent
import Mathlib.Tactic.Linarith

/-!
# Spectral norm of stochastic-block noise

Conditioned on any hidden labeling, the upper-triangular centered edge indicators are
independent, have mean zero, and have oscillation one. The general independent-entry bound
therefore controls the stochastic block model's noise uniformly over its labels and parameters.

## Main results

* `noise_opNorm_gt_le`: the noise norm exceeds `(5 / 2) √n` with probability at most `2 exp (-n)`.
-/

public section

open Finset Real
open scoped unitInterval

namespace Cslib.Probability.StochasticBlockModel

/-- Under the actual stochastic-block edge law, the centered adjacency noise has norm at most
`(5 / 2) √n` with failure probability at most `2 exp (-n)`. The bound is uniform over all labels and
both edge probabilities; it does not require balanced communities or a positive signal gap. -/
theorem noise_opNorm_gt_le {n : ℕ} (p q : I) (g : Fin n → Bool) :
    ((coinLaw p q g).toOuterMeasure {ω |
      (5 / 2) * sqrt n < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise p q g ω)‖}).toReal
      ≤ 2 * exp (-(n : ℝ)) := by
  let score (e : Fin n × Fin n) (b : Bool) : ℝ :=
    BitString.bitVal ℝ b - edgeProbability p q g e.1 e.2
  have hmean (e : Fin n × Fin n) :
      ∑ b, (PMF.coin (edgeProbability p q g e.1 e.2) b).toReal * score e b = 0 := by
    simp only [Fintype.sum_bool, PMF.coin_apply_toReal, score, BitString.bitVal_false,
      BitString.bitVal_true, Bool.false_eq_true, ite_false, ite_true]
    ring
  have hosc (e : Fin n × Fin n) (a b : Bool) : |score e a - score e b| ≤ 1 := by
    simp only [score, sub_sub_sub_cancel_right]
    cases a <;> cases b <;> norm_num
  have h := PMF.pi_opNorm_symmetric_gt_le
    (fun e => PMF.coin (edgeProbability p q g e.1 e.2)) score hmean
    (by norm_num : (0 : ℝ) < 1) hosc (noise p q g) (fun _ _ _ => rfl)
    (by norm_num : (0 : ℝ) ≤ 5 / 2)
  apply h.trans
  gcongr
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

end Cslib.Probability.StochasticBlockModel
