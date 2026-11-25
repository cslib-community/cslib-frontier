/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Independence/Integration.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Probability.Independence.Integration

/-!
# Expected squared norm of linear combinations of independent random vectors

This module establishes the second-moment bound for real linear combinations of mutually
independent square-integrable random vectors in a real Hilbert space.

## Main results

* `ProbabilityTheory.integral_norm_sum_smul_sq_le_of_iIndepFun`: [MicciancioRegev2007],
  Lemma 2.11 (p. 10), bounding `𝔼[‖∑ z_i • X_i‖²]` for independent square-integrable vectors.

## References

* [MicciancioRegev2007], Lemma 2.11 (p. 10 of the December 27, 2005 author version).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbabilityTheory

/-- **Expected squared norm of a linear combination of independent random vectors**
([MicciancioRegev2007], Lemma 2.11, p. 10 of the December 27, 2005 author version):
if `X : ι → Ω → E` are mutually independent square-integrable random vectors in a real Hilbert
space with `𝔼[‖X i‖²] ≤ l` and `‖𝔼[X i]‖² ≤ ε` for every `i`, then for any real coefficients
`z : ι → ℝ`, `𝔼[‖∑ i, z i • X i‖²] ≤ (l + ε * card ι) * ∑ i, z i ^ 2`.
Holds for empty index types `ι` as well. -/
theorem integral_norm_sum_smul_sq_le_of_iIndepFun
    {Ω E ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    {X : ι → Ω → E} (hind : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    {l ε : ℝ} (hsq : ∀ i, ∫ ω, ‖X i ω‖ ^ 2 ∂μ ≤ l)
    (hmean : ∀ i, ‖∫ ω, X i ω ∂μ‖ ^ 2 ≤ ε) (z : ι → ℝ) :
    ∫ ω, ‖∑ i : ι, z i • X i ω‖ ^ 2 ∂μ ≤
      (l + ε * Fintype.card ι) * ∑ i : ι, z i ^ 2 := by
  classical
  have hInt (i : ι) : Integrable (X i) μ := (hL2 i).integrable one_le_two
  have hIntSq (i : ι) : Integrable (fun ω ↦ ‖X i ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hL2 i).aestronglyMeasurable).mp (hL2 i)
  have hIntInner (i j : ι) : Integrable (fun ω ↦ ⟪X i ω, X j ω⟫) μ := by
    refine ((hIntSq i).add (hIntSq j)).mono'
      ((hL2 i).aestronglyMeasurable.inner (hL2 j).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    change |⟪X i ω, X j ω⟫| ≤ ‖X i ω‖ ^ 2 + ‖X j ω‖ ^ 2
    nlinarith [abs_real_inner_le_norm (X i ω) (X j ω), sq_nonneg (‖X i ω‖ - ‖X j ω‖),
      norm_nonneg (X i ω), norm_nonneg (X j ω)]
  -- expand the square and integrate term by term; independence splits the off-diagonal terms
  have hexpand (ω : Ω) :
      ‖∑ i : ι, z i • X i ω‖ ^ 2 = ∑ i : ι, ∑ j : ι, (z i * z j) * ⟪X i ω, X j ω⟫ := by
    simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right, mul_assoc]
  simp_rw [hexpand]
  rw [integral_finsetSum _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦ (hIntInner i j).const_mul (z i * z j)]
  have hsplit (i : ι) :
      (∫ ω, ∑ j : ι, (z i * z j) * ⟪X i ω, X j ω⟫ ∂μ) =
        z i ^ 2 * (∫ ω, ‖X i ω‖ ^ 2 ∂μ) +
          ∑ j ∈ Finset.univ.erase i, (z i * z j) * ⟪∫ ω, X i ω ∂μ, ∫ ω, X j ω ∂μ⟫ := by
    rw [integral_finsetSum _ fun j _ ↦ (hIntInner i j).const_mul (z i * z j),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp_rw [integral_const_mul, sq, real_inner_self_eq_norm_mul_norm]
    · refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [integral_const_mul]
      exact congrArg _ <| (hind.indepFun (Finset.ne_of_mem_erase hj).symm).integral_bilin
        (hInt i) (hInt j) (innerSL ℝ)
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have hdiag : (∑ i : ι, z i ^ 2 * ∫ ω, ‖X i ω‖ ^ 2 ∂μ) ≤ l * ∑ i : ι, z i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ by nlinarith [hsq i, sq_nonneg (z i)]
  have hoff_term (i j : ι) :
      (z i * z j) * ⟪∫ ω, X i ω ∂μ, ∫ ω, X j ω ∂μ⟫ ≤ ε * (|z i| * |z j|) := by
    have hcs : |⟪∫ ω, X i ω ∂μ, ∫ ω, X j ω ∂μ⟫| ≤ ε := by
      nlinarith [abs_real_inner_le_norm (∫ ω, X i ω ∂μ) (∫ ω, X j ω ∂μ), hmean i, hmean j,
        sq_nonneg (‖∫ ω, X i ω ∂μ‖ - ‖∫ ω, X j ω ∂μ‖)]
    refine (le_abs_self _).trans ?_
    rw [abs_mul, abs_mul, mul_comm ε]
    gcongr
  have hoff :
      (∑ i : ι, ∑ j ∈ Finset.univ.erase i, (z i * z j) * ⟪∫ ω, X i ω ∂μ, ∫ ω, X j ω ∂μ⟫) ≤
        ε * Fintype.card ι * ∑ i : ι, z i ^ 2 := by
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
    · simp
    have hε0 : 0 ≤ ε := (sq_nonneg _).trans (hmean i₀)
    have hcs : (∑ i : ι, |z i|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i : ι, z i ^ 2 := by
      simpa only [Finset.card_univ, sq_abs] using
        sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i ↦ |z i|)
    calc _ ≤ ∑ i : ι, ∑ j : ι, ε * (|z i| * |z j|) :=
          Finset.sum_le_sum fun i _ ↦ (Finset.sum_le_sum fun j _ ↦ hoff_term i j).trans <|
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i _)
              fun j _ _ ↦ by positivity
      _ = ε * (∑ i : ι, |z i|) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          simp only [Finset.mul_sum]
      _ ≤ ε * ((Fintype.card ι : ℝ) * ∑ i : ι, z i ^ 2) := mul_le_mul_of_nonneg_left hcs hε0
      _ = ε * Fintype.card ι * ∑ i : ι, z i ^ 2 := by ring
  linarith

end ProbabilityTheory
