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
    have hmeas : AEStronglyMeasurable (fun ω ↦ ⟪X i ω, X j ω⟫) μ :=
      (hL2 i).aestronglyMeasurable.inner (hL2 j).aestronglyMeasurable
    refine ((hIntSq i).add (hIntSq j)).mono' hmeas (Filter.Eventually.of_forall fun ω ↦ ?_)
    change |⟪X i ω, X j ω⟫| ≤ ‖X i ω‖ ^ 2 + ‖X j ω‖ ^ 2
    have h1 := abs_real_inner_le_norm (X i ω) (X j ω)
    have h2 : 0 ≤ (‖X i ω‖ - ‖X j ω‖) ^ 2 := sq_nonneg _
    nlinarith [norm_nonneg (X i ω), norm_nonneg (X j ω)]
  have hexpand (ω : Ω) :
      ‖∑ i : ι, z i • X i ω‖ ^ 2 =
        ∑ i : ι, ∑ j : ι, (z i * z j) * ⟪X i ω, X j ω⟫ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    ring
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
    · rw [integral_const_mul, sq]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ real_inner_self_eq_norm_sq (X i ω)
    · apply Finset.sum_congr rfl
      intro j hj
      have hne : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      rw [integral_const_mul]
      congr 1
      have hbil := (hind.indepFun hne).integral_bilin (hInt i) (hInt j) (innerSL ℝ)
      have hfun : (fun ω ↦ (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) (X i ω) (X j ω)) =
          fun ω ↦ ⟪X i ω, X j ω⟫ := by
        funext ω
        rfl
      rw [hfun] at hbil
      exact hbil
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have hdiag :
      (∑ i : ι, z i ^ 2 * ∫ ω, ‖X i ω‖ ^ 2 ∂μ) ≤ l * ∑ i : ι, z i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [mul_comm l]
    exact mul_le_mul_of_nonneg_left (hsq i) (sq_nonneg _)
  have hoff_term (i j : ι) :
      (z i * z j) * ⟪∫ ω, X i ω ∂μ, ∫ ω, X j ω ∂μ⟫ ≤ |z i| * |z j| * ε := by
    have hcs : |⟪∫ ω, X i ω ∂μ, ∫ ω, X j ω ∂μ⟫| ≤ ε := by
      have h1 := abs_real_inner_le_norm (∫ ω, X i ω ∂μ) (∫ ω, X j ω ∂μ)
      have h2 : ‖∫ ω, X i ω ∂μ‖ * ‖∫ ω, X j ω ∂μ‖ ≤ ε := by
        have hmi := hmean i
        have hmj := hmean j
        have hε0 : 0 ≤ ε := (sq_nonneg _).trans hmi
        have hsq_prod : (‖∫ ω, X i ω ∂μ‖ * ‖∫ ω, X j ω ∂μ‖) ^ 2 ≤ ε ^ 2 := by
          rw [mul_pow, sq ε]
          exact mul_le_mul hmi hmj (sq_nonneg _) hε0
        exact le_of_sq_le_sq hsq_prod hε0
      exact h1.trans h2
    have hmul :
        (z i * z j) * ⟪∫ ω, X i ω ∂μ, ∫ ω, X j ω ∂μ⟫ ≤
          |z i * z j| * |⟪∫ ω, X i ω ∂μ, ∫ ω, X j ω ∂μ⟫| := by
      rw [← abs_mul]
      exact le_abs_self _
    calc
      (z i * z j) * ⟪∫ ω, X i ω ∂μ, ∫ ω, X j ω ∂μ⟫ ≤
          |z i * z j| * |⟪∫ ω, X i ω ∂μ, ∫ ω, X j ω ∂μ⟫| := hmul
      _ = |z i| * |z j| * |⟪∫ ω, X i ω ∂μ, ∫ ω, X j ω ∂μ⟫| := by rw [abs_mul]
      _ ≤ |z i| * |z j| * ε :=
        mul_le_mul_of_nonneg_left hcs (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hoff :
      (∑ i : ι, ∑ j ∈ Finset.univ.erase i, (z i * z j) * ⟪∫ ω, X i ω ∂μ, ∫ ω, X j ω ∂μ⟫) ≤
        ε * Fintype.card ι * ∑ i : ι, z i ^ 2 := by
    by_cases hne : Nonempty ι
    · obtain ⟨i₀⟩ := hne
      have hε0 : 0 ≤ ε := (sq_nonneg _).trans (hmean i₀)
      have h1 :
          (∑ i : ι, ∑ j ∈ Finset.univ.erase i, (z i * z j) * ⟪∫ ω, X i ω ∂μ, ∫ ω, X j ω ∂μ⟫) ≤
            ∑ i : ι, ∑ j ∈ Finset.univ.erase i, |z i| * |z j| * ε :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hoff_term i j
      have h2 :
          (∑ i : ι, ∑ j ∈ Finset.univ.erase i, |z i| * |z j| * ε) ≤
            ∑ i : ι, ∑ j : ι, |z i| * |z j| * ε :=
        Finset.sum_le_sum fun i _ ↦
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i Finset.univ)
            fun j _ _ ↦ by positivity
      have h3 :
          (∑ i : ι, ∑ j : ι, |z i| * |z j| * ε) = ε * (∑ i : ι, |z i|) ^ 2 := by
        rw [sq, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have h4 : (∑ i : ι, |z i|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i : ι, z i ^ 2 := by
        simpa only [Finset.card_univ, sq_abs] using
          sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i ↦ |z i|)
      calc
        (∑ i : ι, ∑ j ∈ Finset.univ.erase i, (z i * z j) * ⟪∫ ω, X i ω ∂μ, ∫ ω, X j ω ∂μ⟫) ≤
            ε * (∑ i : ι, |z i|) ^ 2 := (h1.trans h2).trans_eq h3
        _ ≤ ε * ((Fintype.card ι : ℝ) * ∑ i : ι, z i ^ 2) :=
          mul_le_mul_of_nonneg_left h4 hε0
        _ = ε * Fintype.card ι * ∑ i : ι, z i ^ 2 := by ring
    · have _ : IsEmpty ι := not_nonempty_iff.mp hne
      simp
  linarith

end ProbabilityTheory
