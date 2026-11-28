/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Gaussian.ShiftBounds
public import CslibFrontier.Foundations.Probability.Gaussian.CenteredTail

import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Width criteria for small nonzero dual Gaussian mass

Discreteness of the dual lattice supplies a positive norm gap, so the quantitative width criterion
`ZLattice.gaussianMass_dual_sub_one_le_of_gap` (proved in `Gaussian.CenteredTail` and re-exported
here) implies that every positive error tolerance is attained at all sufficiently large widths.
No minimum smoothing parameter or small-tail assumption is introduced as a definition here.

## Main results

* `ZLattice.eventually_gaussianMass_dual_sub_one_le`: the dual-gap criterion is eventually
  satisfiable for every full-rank discrete lattice and every positive error tolerance.

## References

These are supporting consequences of the centered Gaussian tail estimate for the explicit
dual-tail condition in [Regev2009], Claim 3.8, printed page 22 of the May 2, 2009 author version.
The numerical width criterion is proved in `Gaussian.CenteredTail`; uniform shifted mass estimates
are in `Gaussian.ShiftBounds`.
-/

public section

noncomputable section

open Module Filter
open scoped RealInnerProductSpace Topology

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- Every positive error tolerance eventually bounds the actual nonzero dual mass at
reciprocal width. The conclusion includes positivity of the original width, and dimension zero
is covered without a separate nontriviality hypothesis. -/
theorem eventually_gaussianMass_dual_sub_one_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, 0 < s ∧
      gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ≤ ε := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp (isOpen_discrete ({0} : Set D)) 0 (by simp)
  have hgap (w : D) (hw : w ≠ 0) : a ≤ ‖(w : E)‖ :=
    le_of_not_gt fun hnorm => hw (hball (by simpa [Metric.mem_ball, dist_zero_right] using hnorm))
  have hc : -3 * Real.pi * a ^ 2 / 4 < 0 := by
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) (sq_pos_of_pos ha)) (by norm_num)
  have hexp : Tendsto (fun s : ℝ ↦ -3 * Real.pi * s ^ 2 * a ^ 2 / 4) atTop atBot := by
    convert (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg hc using 1
    ext s
    ring
  have hlimit : Tendsto
      (fun s : ℝ ↦ 2 ^ finrank ℝ E * Real.exp (-3 * Real.pi * s ^ 2 * a ^ 2 / 4))
      atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hexp).const_mul (2 ^ finrank ℝ E)
  have hevent := hlimit.eventually (gt_mem_nhds (by positivity : 0 < ε / (1 + ε)))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hevent] with s hs hwidth
  exact ⟨hs, gaussianMass_dual_sub_one_le_of_gap L s hs a ha hgap ε hε hwidth.le⟩

end ZLattice
