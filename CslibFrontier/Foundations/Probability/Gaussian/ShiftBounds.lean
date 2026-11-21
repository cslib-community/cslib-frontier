/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Gaussian.Poisson
public import CslibFrontier.Foundations.Probability.Gaussian.SmoothingParameter

/-!
# Uniform bounds on shifted lattice Gaussian mass

## Main results

* `ZLattice.abs_gaussianMass_normalized_sub_one_le`: normalized mass at every center differs
  from one by at most the nonzero reciprocal-width dual mass.
* `ZLattice.gaussianMass_mem_Icc_of_dual_mass_le`: a bound on that actual dual mass gives
  the two-sided shifted-mass interval.
* `ZLattice.gaussianMass_mem_Icc_of_smoothingParameter_le`: smoothing-parameter conversion of
  `gaussianMass_mem_Icc_of_dual_mass_le` via `smoothingParameter_le_iff`.

## References

The uniform estimate is the explicit dual-tail form of [Regev2009], Claim 3.8, printed
page 22 of the May 2, 2009 author version. The source's translate `L + c` corresponds to
center `-c` here. The proof uses the proved Poisson formula, not a flatness assumption.
The smoothing-parameter conversion unpacks `ZLattice.smoothingParameter` ([MicciancioRegev2007],
Definition 3.1, p. 10 of the December 27, 2005 author's copy) via `smoothingParameter_le_iff`.
Quotient-distribution statements are separate results.
-/

public section

noncomputable section

open Module ProbabilityTheory MeasureTheory
open scoped RealInnerProductSpace

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The normalized shifted mass is uniformly close to one, with the actual nonzero dual
Gaussian mass as error. This statement has no assumed small-tail or flatness premise. -/
theorem abs_gaussianMass_normalized_sub_one_le (s : ℝ) (hs : 0 < s) (c : E) :
    |covolume L / s ^ finrank ℝ E * gaussianMass L s c - 1| ≤
      gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 := by
  classical
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  let f : D → ℂ := fun w ↦ (gaussianWeight (1 / s) (w : E) : ℂ) *
    (Real.fourierChar (-⟪c, (w : E)⟫) : ℂ)
  have hnorm (w : D) : ‖f w‖ = gaussianWeight (1 / s) (w : E) := by
    simp [f, Real.norm_of_nonneg (gaussianWeight_pos _ _).le]
  have hsum : Summable f := by
    apply summable_norm_iff.mp
    simpa only [hnorm, sub_zero] using summable_gaussianWeight D (1 / s) (one_div_pos.mpr hs) 0
  have hsplit : (∑' w : D, f w) = 1 + ∑' w : ↥{w : D | w ≠ 0}, f w := by
    have h := hsum.sum_add_tsum_compl (s := {0})
    have hset : (↑({0} : Finset D) : Set D)ᶜ = {w | w ≠ 0} := by ext w; simp
    rw [hset] at h
    simpa [f, gaussianWeight] using h.symm
  have hcancel : (covolume L : ℂ) / (s : ℂ) ^ finrank ℝ E *
      ((s : ℂ) ^ finrank ℝ E / (covolume L : ℂ)) = 1 := by
    have hc : (covolume L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (covolume_pos L volume).ne'
    have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    field_simp
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  push_cast
  rw [gaussianMass_eq_tsum_dual L s hs c, ← mul_assoc, hcancel, one_mul]
  change ‖(∑' w : D, f w) - 1‖ ≤ gaussianMass D (1 / s) 0 - 1
  rw [hsplit, add_sub_cancel_left, gaussianMass_zero_sub_one_eq_tsum D (1 / s)
    (one_div_pos.mpr hs)]
  have hn : Summable (fun w : ↥{w : D | w ≠ 0} ↦ ‖f w‖) := hsum.norm.subtype _
  simpa only [hnorm] using norm_tsum_le_tsum_norm hn

/-- A bound on the actual nonzero dual mass gives the Gaussian mass interval uniformly over
all centers. For the source's translate `L + c`, use center `-c`. -/
theorem gaussianMass_mem_Icc_of_dual_mass_le (s : ℝ) (hs : 0 < s) (ε : ℝ)
    (hε : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ≤ ε)
    (c : E) :
    gaussianMass L s c ∈ Set.Icc
      (s ^ finrank ℝ E / covolume L * (1 - ε))
      (s ^ finrank ℝ E / covolume L * (1 + ε)) := by
  have h := abs_le.mp ((abs_gaussianMass_normalized_sub_one_le L s hs c).trans hε)
  have hc := covolume_pos L volume
  have hp : 0 < s ^ finrank ℝ E := pow_pos hs _
  have heq : s ^ finrank ℝ E / covolume L *
      (covolume L / s ^ finrank ℝ E * gaussianMass L s c) = gaussianMass L s c := by
    field_simp
  constructor
  · have hh : 1 - ε ≤ covolume L / s ^ finrank ℝ E * gaussianMass L s c := by linarith [h.1]
    simpa only [heq] using mul_le_mul_of_nonneg_left hh (div_pos hp hc).le
  · have hh : covolume L / s ^ finrank ℝ E * gaussianMass L s c ≤ 1 + ε := by linarith [h.2]
    simpa only [heq] using mul_le_mul_of_nonneg_left hh (div_pos hp hc).le

/-- Smoothing-parameter conversion of `gaussianMass_mem_Icc_of_dual_mass_le`: shifted lattice
Gaussian mass interval above the smoothing parameter ([Regev2009], Claim 3.8, p. 22). For the
source's translate `L + c`, use center `-c`. -/
theorem gaussianMass_mem_Icc_of_smoothingParameter_le (s : ℝ) (hs : 0 < s)
    (ε : ℝ) (hε : 0 < ε) (hη : smoothingParameter L ε ≤ s) (c : E) :
    gaussianMass L s c ∈ Set.Icc
      (s ^ finrank ℝ E / covolume L * (1 - ε))
      (s ^ finrank ℝ E / covolume L * (1 + ε)) :=
  gaussianMass_mem_Icc_of_dual_mass_le L s hs ε ((smoothingParameter_le_iff L hs hε).mp hη) c

end ZLattice
