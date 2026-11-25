/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Gaussian.Poisson
public import CslibFrontier.Foundations.Probability.Gaussian.SmoothingParameter
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Uniform bounds on shifted lattice Gaussian mass

## Main results

* `ZLattice.abs_gaussianMass_normalized_sub_one_le`: normalized mass at every center differs
  from one by at most the nonzero reciprocal-width dual mass.
* `ZLattice.gaussianMass_mem_Icc_of_dual_mass_le`: a bound on that actual dual mass gives
  the two-sided shifted-mass interval.
* `ZLattice.gaussianMass_le_gaussianMass_zero`: shifted lattice Gaussian mass is maximized at
  the origin for every discrete `ℤ`-submodule.
* `ZLattice.gaussianMass_mem_Icc_of_smoothingParameter_le`: smoothing-parameter conversion of
  `gaussianMass_mem_Icc_of_dual_mass_le` via `smoothingParameter_le_iff`.

## References

The uniform estimate is the explicit dual-tail form of [Regev2009], Claim 3.8, printed
page 22 of the May 2, 2009 author version. The source's translate `L + c` corresponds to
center `-c` here. The proof uses the proved Poisson formula, not a flatness assumption.
The shifted-mass maximum (`ZLattice.gaussianMass_le_gaussianMass_zero`) is [MicciancioRegev2007],
Lemma 2.9 (p. 9 of the December 27, 2005 author's copy), extended to arbitrary discrete
`ℤ`-submodules by orthogonal projection onto the real span.
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
  have hsum : Summable f := summable_norm_iff.mp <| by
    simpa only [hnorm, sub_zero] using summable_gaussianWeight D (1 / s) (one_div_pos.mpr hs) 0
  have hsplit : (∑' w : D, f w) = 1 + ∑' w : ↥{w : D | w ≠ 0}, f w := by
    have h := hsum.sum_add_tsum_compl (s := {0})
    rw [show (↑({0} : Finset D) : Set D)ᶜ = {w | w ≠ 0} by ext; simp] at h
    simpa [f, gaussianWeight] using h.symm
  have hcancel : (covolume L : ℂ) / (s : ℂ) ^ finrank ℝ E *
      ((s : ℂ) ^ finrank ℝ E / (covolume L : ℂ)) = 1 := by
    have : (covolume L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (covolume_pos L volume).ne'
    have : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    field_simp
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  push_cast
  rw [gaussianMass_eq_tsum_dual L s hs c, ← mul_assoc, hcancel, one_mul]
  change ‖(∑' w : D, f w) - 1‖ ≤ gaussianMass D (1 / s) 0 - 1
  rw [hsplit, add_sub_cancel_left, gaussianMass_zero_sub_one_eq_tsum D (1 / s) (one_div_pos.mpr hs)]
  simpa only [hnorm] using
    norm_tsum_le_tsum_norm (hsum.norm.subtype _ : Summable fun w : ↥{w : D | w ≠ 0} ↦ ‖f w‖)

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
      (covolume L / s ^ finrank ℝ E * gaussianMass L s c) = gaussianMass L s c := by field_simp
  refine ⟨?_, ?_⟩
  · rw [← heq]
    exact mul_le_mul_of_nonneg_left (by linarith [h.1]) (div_pos hp hc).le
  · rw [← heq]
    exact mul_le_mul_of_nonneg_left (by linarith [h.2]) (div_pos hp hc).le

/-- Smoothing-parameter conversion of `gaussianMass_mem_Icc_of_dual_mass_le`: shifted lattice
Gaussian mass interval above the smoothing parameter ([Regev2009], Claim 3.8, p. 22). For the
source's translate `L + c`, use center `-c`. -/
theorem gaussianMass_mem_Icc_of_smoothingParameter_le (s : ℝ) (hs : 0 < s)
    (ε : ℝ) (hε : 0 < ε) (hη : smoothingParameter L ε ≤ s) (c : E) :
    gaussianMass L s c ∈ Set.Icc
      (s ^ finrank ℝ E / covolume L * (1 - ε))
      (s ^ finrank ℝ E / covolume L * (1 + ε)) :=
  gaussianMass_mem_Icc_of_dual_mass_le L s hs ε ((smoothingParameter_le_iff L hs hε).mp hη) c

section ShiftedMassMax

private theorem gaussianMass_le_gaussianMass_zero_of_isZLattice
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : ℝ) (hs : 0 < s) (c : E) :
    gaussianMass L s c ≤ gaussianMass L s 0 := by
  have h0 : gaussianMass L s 0 = s ^ finrank ℝ E / covolume L *
      gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 := by
    apply Complex.ofReal_injective
    simpa only [inner_zero_left, neg_zero, Real.fourierChar.map_zero_eq_one, Circle.coe_one,
      one_mul, mul_one, gaussianMass, sub_zero, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_tsum] using gaussianMass_eq_tsum_dual L s hs 0
  simpa [h0] using (gaussianMass_mem_Icc_of_dual_mass_le L s hs _ le_rfl c).2

/-- Shifted lattice Gaussian mass is maximized at the origin ([MicciancioRegev2007], Lemma 2.9,
p. 9 of the December 27, 2005 author's copy). Holds for every discrete `ℤ`-submodule `L` of a
finite-dimensional real inner product space (not necessarily full-rank) without requiring
`MeasurableSpace E`. -/
theorem gaussianMass_le_gaussianMass_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) (c : E) :
    gaussianMass L s c ≤ gaussianMass L s 0 := by
  let V : Submodule ℝ E := Submodule.span ℝ (L : Set E)
  let cPar : V := V.orthogonalProjectionOnto c
  have hproj : gaussianMass L s c ≤ gaussianMass L s (cPar : E) := by
    refine Summable.tsum_le_tsum (fun z : L ↦ ?_)
      (summable_gaussianWeight L s hs c) (summable_gaussianWeight L s hs (cPar : E))
    have hinner : ⟪(z : E) - (cPar : E), c - (cPar : E)⟫ = 0 :=
      (Submodule.mem_orthogonal V _).mp (V.sub_starProjection_mem_orthogonal c) _
        (V.sub_mem (Submodule.subset_span z.2) cPar.2)
    have hsq : ‖(z : E) - (cPar : E)‖ ^ 2 ≤ ‖(z : E) - c‖ ^ 2 := by
      have hsub : ‖(z : E) - c‖ ^ 2 =
          ‖(z : E) - (cPar : E)‖ ^ 2 + ‖c - (cPar : E)‖ ^ 2 := by
        rw [← sub_sub_sub_cancel_right (z : E) c (cPar : E), norm_sub_sq_real, hinner]
        ring
      nlinarith [sq_nonneg ‖c - (cPar : E)‖]
    refine Real.exp_le_exp.mpr ?_
    simp only [neg_mul, neg_div]
    gcongr
  let LV : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let e : LV ≃ₜ L := {
    toFun := fun x ↦ ⟨(x.1 : E), x.2⟩
    invFun := fun z ↦ ⟨⟨(z : E), Submodule.subset_span z.2⟩, z.2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  }
  have hLV_disc : DiscreteTopology LV := e.discreteTopology_iff.mpr inferInstance
  have hLV_lat : IsZLattice ℝ LV := ⟨by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
      show (V.subtype '' (LV : Set V)) = (L : Set E) by
        ext y
        exact ⟨by rintro ⟨_, hx, rfl⟩; exact hx,
          fun hy ↦ ⟨⟨y, Submodule.subset_span hy⟩, hy, rfl⟩⟩]⟩
  have hmass_eq (y : V) : gaussianMass LV s y = gaussianMass L s (y : E) := by
    unfold gaussianMass
    rw [← e.toEquiv.tsum_eq (fun z : L ↦ gaussianWeight s ((z : E) - (y : E)))]
    exact tsum_congr fun _ ↦ rfl
  have hborel : @BorelSpace V _ (borel V) := @BorelSpace.mk V _ (borel V) rfl
  exact hproj.trans <| (hmass_eq cPar).symm.trans_le <|
    (@gaussianMass_le_gaussianMass_zero_of_isZLattice V _ _ _ (borel V) hborel
      LV hLV_disc hLV_lat s hs cPar).trans_eq (hmass_eq 0)

end ShiftedMassMax

end ZLattice
