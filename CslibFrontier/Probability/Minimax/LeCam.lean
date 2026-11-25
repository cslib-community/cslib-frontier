/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.ChiSquare
public import CslibFrontier.Probability.Divergence.Pi
public import CslibFrontier.Probability.PMF.Coin
public import CslibFrontier.Probability.Pinsker
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Le Cam's two-point minimax lower-bound method

**Le Cam's two-point method** lowers minimax estimation risk to binary hypothesis testing between
two distributions whose target parameters are separated under the loss function ([LeCam1973];
[Tsybakov2009], Sections 2.2–2.4).

This file develops the method at two levels of generality:

1. **General probability measures (`Measure α`)**: via a Hahn decomposition of `(μ, ν)`,
   * **Neyman–Pearson total-variation identity**
     (`Cslib.Probability.neymanPearson_measureReal_compl_add_ge`,
     `Cslib.Probability.exists_measurableSet_measureReal_compl_add_eq`):
     every measurable test `A` satisfies `1 - tvDist μ ν / 2 ≤ μ.real Aᶜ + ν.real A`, and the Hahn
     set attains equality.
   * **Exact measure-theoretic Le Cam inequality**
     (`Cslib.Probability.leCam_measure_add_ge`, `Cslib.Probability.leCam_measure_max_ge`,
     `Cslib.Probability.leCam_measure_max_ge_of_klDiv`): if nonnegative losses satisfy
     `∀ x, sep ≤ L₀ x + L₁ x`, then
     `sep · (1 - tvDist μ ν / 2) ≤ ∫ L₀ ∂μ + ∫ L₁ ∂ν`, so the worst-case risk is at least
     `(sep / 2) · (1 - tvDist μ ν / 2) ≥ (sep / 2) · (1 - √(KL(μ ‖ ν) / 2))`.
2. **Finite distributions (`PMF X`), randomized estimators, and i.i.d. rates**:
   * **Overlap proof on `PMF`** (`Cslib.Probability.PMF.leCam_add_ge`,
     `Cslib.Probability.PMF.leCam_max_ge`, `Cslib.Probability.PMF.leCam_randomized_max_ge`):
     holds with the sharp factor `sep / 2` for both deterministic (`X → T`) and randomized
     (`X → PMF T`) estimators, with KL-Pinsker, `χ²`, and `n`-sample i.i.d. corollaries.
   * **Minimax rate for Bernoulli mean estimation**
     (`Cslib.Probability.PMF.bernoulli_mean_minimax_sq_lower_bound`,
     `Cslib.Probability.PMF.bernoulli_mean_minimax_abs_lower_bound`): from `n ≥ 1` i.i.d. flips of
     `coin p`, every estimator incurs worst-case squared error `≥ 1 / (72 n)` and absolute error
     `≥ 1 / (12 √n)`.

## Main results

* `Cslib.Probability.leCam_measure_add_ge`, `Cslib.Probability.leCam_measure_max_ge`,
  `Cslib.Probability.leCam_measure_max_ge_of_klDiv`: measure-theoretic Le Cam inequalities.
* `Cslib.Probability.neymanPearson_measureReal_compl_add_ge`,
  `Cslib.Probability.exists_measurableSet_measureReal_compl_add_eq`: Neyman–Pearson identity.
* `Cslib.Probability.PMF.leCam_add_ge`, `Cslib.Probability.PMF.leCam_max_ge`,
  `Cslib.Probability.PMF.leCam_randomized_max_ge`: finite-`PMF` Le Cam bounds.
* `Cslib.Probability.PMF.leCam_max_ge_of_klDiv`, `Cslib.Probability.PMF.leCam_iid_max_ge_of_klDiv`,
  `Cslib.Probability.PMF.leCam_max_ge_of_chiSquare`: divergence and i.i.d. forms.
* `Cslib.Probability.PMF.bernoulli_mean_minimax_sq_lower_bound`,
  `Cslib.Probability.PMF.bernoulli_mean_minimax_abs_lower_bound`: `Ω(1 / n)` and `Ω(1 / √n)` minimax
  lower bounds for Bernoulli mean estimation.

## References

* [L. Le Cam, *Convergence of estimates under dimensionality restrictions*][LeCam1973]
* [A. B. Tsybakov, *Introduction to Nonparametric Estimation*][Tsybakov2009], Sections 2.2–2.4.
-/

public section

namespace Cslib.Probability

open MeasureTheory ProbabilityTheory InformationTheory Finset Set
open scoped BigOperators ENNReal unitInterval

/-! ### Measure-theoretic Neyman–Pearson identity and Le Cam two-point bound -/

section Measure

variable {α : Type*} {mα : MeasurableSpace α}

private theorem hahn_overlap_eq (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set α} (hs : IsHahnDecomposition μ ν s) :
    μ.real s + ν.real sᶜ = 1 - tvDist μ ν / 2 := by
  have htv := hs.tvDist_eq
  have hμ := probReal_compl_eq_one_sub (μ := μ) hs.measurableSet
  have hν := probReal_compl_eq_one_sub (μ := ν) hs.measurableSet
  linarith

/-- **Measure-theoretic Le Cam sum inequality**: if `L₀, L₁ ≥ 0` are integrable under probability
measures `μ, ν` and satisfy `∀ x, sep ≤ L₀ x + L₁ x`, then
`sep · (1 - tvDist μ ν / 2) ≤ ∫ L₀ ∂μ + ∫ L₁ ∂ν`. -/
theorem leCam_measure_add_ge (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L₀ L₁ : α → ℝ} {sep : ℝ}
    (hL₀ : ∀ x, 0 ≤ L₀ x) (hL₁ : ∀ x, 0 ≤ L₁ x)
    (hint₀ : Integrable L₀ μ) (hint₁ : Integrable L₁ ν)
    (hsep : ∀ x, sep ≤ L₀ x + L₁ x) :
    sep * (1 - tvDist μ ν / 2) ≤ (∫ x, L₀ x ∂μ) + ∫ x, L₁ x ∂ν := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have h_on_s : ∫ x in s, L₁ x ∂μ ≤ ∫ x in s, L₁ x ∂ν :=
    integral_mono_measure hs.le_on (ae_of_all _ hL₁) hint₁.integrableOn
  have h_on_sc : ∫ x in sᶜ, L₀ x ∂ν ≤ ∫ x in sᶜ, L₀ x ∂μ :=
    integral_mono_measure hs.ge_on_compl (ae_of_all _ hL₀) hint₀.integrableOn
  have hint₁_μs : IntegrableOn L₁ s μ := Integrable.mono_measure hint₁.integrableOn hs.le_on
  have hint₀_νsc : IntegrableOn L₀ sᶜ ν := Integrable.mono_measure hint₀.integrableOn hs.ge_on_compl
  have hsplit₀ : (∫ x in s, L₀ x ∂μ) + ∫ x in sᶜ, L₀ x ∂μ = ∫ x, L₀ x ∂μ :=
    integral_add_compl hs.measurableSet hint₀
  have hsplit₁ : (∫ x in s, L₁ x ∂ν) + ∫ x in sᶜ, L₁ x ∂ν = ∫ x, L₁ x ∂ν :=
    integral_add_compl hs.measurableSet hint₁
  have hsep_on {κ : Measure α} [IsProbabilityMeasure κ] {t : Set α}
      (h0 : IntegrableOn L₀ t κ) (h1 : IntegrableOn L₁ t κ) :
      sep * κ.real t ≤ (∫ x in t, L₀ x ∂κ) + ∫ x in t, L₁ x ∂κ := by
    rw [← integral_add h0 h1, show sep * κ.real t = ∫ _ in t, sep ∂κ by
      rw [setIntegral_const, smul_eq_mul, mul_comm]]
    exact integral_mono (integrable_const sep) (h0.add h1) hsep
  have hover := hahn_overlap_eq μ ν hs
  calc sep * (1 - tvDist μ ν / 2)
      = sep * μ.real s + sep * ν.real sᶜ := by rw [← hover]; ring
    _ ≤ ((∫ x in s, L₀ x ∂μ) + ∫ x in s, L₁ x ∂μ) +
          ((∫ x in sᶜ, L₀ x ∂ν) + ∫ x in sᶜ, L₁ x ∂ν) :=
        add_le_add (hsep_on hint₀.integrableOn hint₁_μs) (hsep_on hint₀_νsc hint₁.integrableOn)
    _ ≤ ((∫ x in s, L₀ x ∂μ) + ∫ x in s, L₁ x ∂ν) +
          ((∫ x in sᶜ, L₀ x ∂μ) + ∫ x in sᶜ, L₁ x ∂ν) := by linarith
    _ = (∫ x, L₀ x ∂μ) + ∫ x, L₁ x ∂ν := by linarith

/-- **Measure-theoretic Le Cam minimax bound**: under the hypotheses of `leCam_measure_add_ge`,
`(sep / 2) · (1 - tvDist μ ν / 2) ≤ max (∫ L₀ ∂μ) (∫ L₁ ∂ν)`. -/
theorem leCam_measure_max_ge (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L₀ L₁ : α → ℝ} {sep : ℝ}
    (hL₀ : ∀ x, 0 ≤ L₀ x) (hL₁ : ∀ x, 0 ≤ L₁ x)
    (hint₀ : Integrable L₀ μ) (hint₁ : Integrable L₁ ν)
    (hsep : ∀ x, sep ≤ L₀ x + L₁ x) :
    (sep / 2) * (1 - tvDist μ ν / 2) ≤ max (∫ x, L₀ x ∂μ) (∫ x, L₁ x ∂ν) := by
  have hsum := leCam_measure_add_ge μ ν hL₀ hL₁ hint₀ hint₁ hsep
  have h0 := le_max_left (∫ x, L₀ x ∂μ) (∫ x, L₁ x ∂ν)
  have h1 := le_max_right (∫ x, L₀ x ∂μ) (∫ x, L₁ x ∂ν)
  linarith

/-- **Measure-theoretic Le Cam–Pinsker bound**: when `0 ≤ sep` and `klDiv μ ν ≠ ⊤`,
`(sep / 2) · (1 - √(KL(μ ‖ ν) / 2)) ≤ max (∫ L₀ ∂μ) (∫ L₁ ∂ν)`. -/
theorem leCam_measure_max_ge_of_klDiv (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {L₀ L₁ : α → ℝ} {sep : ℝ}
    (hsep0 : 0 ≤ sep) (hkl : klDiv μ ν ≠ ⊤)
    (hL₀ : ∀ x, 0 ≤ L₀ x) (hL₁ : ∀ x, 0 ≤ L₁ x)
    (hint₀ : Integrable L₀ μ) (hint₁ : Integrable L₁ ν)
    (hsep : ∀ x, sep ≤ L₀ x + L₁ x) :
    (sep / 2) * (1 - Real.sqrt ((klDiv μ ν).toReal / 2)) ≤
      max (∫ x, L₀ x ∂μ) (∫ x, L₁ x ∂ν) := by
  have hpinsker : tvDist μ ν ^ 2 / 2 ≤ (klDiv μ ν).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hkl).mp (ofReal_tvDist_sq_div_two_le_klDiv μ ν)
  have htv_le : tvDist μ ν / 2 ≤ Real.sqrt ((klDiv μ ν).toReal / 2) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have hmono : (sep / 2) * (1 - Real.sqrt ((klDiv μ ν).toReal / 2)) ≤
      (sep / 2) * (1 - tvDist μ ν / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact hmono.trans (leCam_measure_max_ge μ ν hL₀ hL₁ hint₀ hint₁ hsep)

/-- **Neyman–Pearson testing lower bound**: for every measurable acceptance region `A`, the sum of
type-I and type-II error probabilities satisfies `1 - tvDist μ ν / 2 ≤ μ.real Aᶜ + ν.real A`. -/
theorem neymanPearson_measureReal_compl_add_ge (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {A : Set α} (hA : MeasurableSet A) :
    1 - tvDist μ ν / 2 ≤ μ.real Aᶜ + ν.real A := by
  have h := leCam_measure_add_ge μ ν
    (L₀ := Aᶜ.indicator fun _ => (1 : ℝ)) (L₁ := A.indicator fun _ => (1 : ℝ)) (sep := 1)
    (fun x => by by_cases hx : x ∈ Aᶜ <;> simp [hx])
    (fun x => by by_cases hx : x ∈ A <;> simp [hx])
    ((integrable_const (1 : ℝ)).indicator hA.compl)
    ((integrable_const (1 : ℝ)).indicator hA)
    (fun x => by by_cases hx : x ∈ A <;> simp [hx])
  rw [integral_indicator_const (1 : ℝ) hA.compl, integral_indicator_const (1 : ℝ) hA,
    smul_eq_mul, smul_eq_mul, mul_one, mul_one, one_mul] at h
  exact h

/-- **Neyman–Pearson testing optimality**: there exists a measurable acceptance region `A` attaining
`μ.real Aᶜ + ν.real A = 1 - tvDist μ ν / 2`. -/
theorem exists_measurableSet_measureReal_compl_add_eq (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    ∃ A : Set α, MeasurableSet A ∧ μ.real Aᶜ + ν.real A = 1 - tvDist μ ν / 2 := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  refine ⟨sᶜ, hs.measurableSet.compl, ?_⟩
  rw [compl_compl]
  exact hahn_overlap_eq μ ν hs

end Measure

/-! ### Finite-distribution (`PMF`) Le Cam bounds and Bernoulli minimax estimation rates -/

namespace PMF

section Finite

variable {X T Θ : Type*} [Fintype X]

/-- **Le Cam sum inequality for `PMF`**: if `L₀, L₁ ≥ 0` satisfy `∀ x, sep ≤ L₀ x + L₁ x`, then
`sep · (1 - dist p₀ p₁) ≤ ∑ x, p₀ x · L₀ x + ∑ x, p₁ x · L₁ x`. -/
theorem leCam_add_ge (p₀ p₁ : PMF X) {L₀ L₁ : X → ℝ} {sep : ℝ}
    (hL₀ : ∀ x, 0 ≤ L₀ x) (hL₁ : ∀ x, 0 ≤ L₁ x)
    (hsep : ∀ x, sep ≤ L₀ x + L₁ x) :
    sep * (1 - dist p₀ p₁) ≤
      (∑ x, (p₀ x).toReal * L₀ x) + ∑ x, (p₁ x).toReal * L₁ x := by
  rw [← sum_min_toReal p₀ p₁, mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  have hmin₀ : min (p₀ x).toReal (p₁ x).toReal ≤ (p₀ x).toReal := min_le_left _ _
  have hmin₁ : min (p₀ x).toReal (p₁ x).toReal ≤ (p₁ x).toReal := min_le_right _ _
  have hmin_nn : 0 ≤ min (p₀ x).toReal (p₁ x).toReal :=
    le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  calc sep * min (p₀ x).toReal (p₁ x).toReal
      ≤ (L₀ x + L₁ x) * min (p₀ x).toReal (p₁ x).toReal :=
        mul_le_mul_of_nonneg_right (hsep x) hmin_nn
    _ = min (p₀ x).toReal (p₁ x).toReal * L₀ x + min (p₀ x).toReal (p₁ x).toReal * L₁ x := by ring
    _ ≤ (p₀ x).toReal * L₀ x + (p₁ x).toReal * L₁ x :=
        add_le_add (mul_le_mul_of_nonneg_right hmin₀ (hL₀ x))
          (mul_le_mul_of_nonneg_right hmin₁ (hL₁ x))

/-- **Le Cam two-point minimax bound** for deterministic estimators `est : X → T`: if
`∀ t, sep ≤ loss t θ₀ + loss t θ₁`, then worst-case expected loss over `{θ₀, θ₁}` is at least
`(sep / 2) · (1 - dist p₀ p₁)`. -/
theorem leCam_max_ge (p₀ p₁ : PMF X) {loss : T → Θ → ℝ} {θ₀ θ₁ : Θ} {sep : ℝ}
    (hloss₀ : ∀ t, 0 ≤ loss t θ₀) (hloss₁ : ∀ t, 0 ≤ loss t θ₁)
    (hsep : ∀ t, sep ≤ loss t θ₀ + loss t θ₁) (est : X → T) :
    (sep / 2) * (1 - dist p₀ p₁) ≤
      max (∑ x, (p₀ x).toReal * loss (est x) θ₀) (∑ x, (p₁ x).toReal * loss (est x) θ₁) := by
  have hsum := leCam_add_ge p₀ p₁ (fun x => hloss₀ (est x)) (fun x => hloss₁ (est x))
    fun x => hsep (est x)
  linarith [le_max_left (∑ x, (p₀ x).toReal * loss (est x) θ₀)
      (∑ x, (p₁ x).toReal * loss (est x) θ₁),
    le_max_right (∑ x, (p₀ x).toReal * loss (est x) θ₀)
      (∑ x, (p₁ x).toReal * loss (est x) θ₁)]

/-- **Le Cam two-point minimax bound for randomized estimators** `est : X → PMF T`. -/
theorem leCam_randomized_max_ge [Fintype T] (p₀ p₁ : PMF X) {loss : T → Θ → ℝ} {θ₀ θ₁ : Θ}
    {sep : ℝ} (hloss₀ : ∀ t, 0 ≤ loss t θ₀) (hloss₁ : ∀ t, 0 ≤ loss t θ₁)
    (hsep : ∀ t, sep ≤ loss t θ₀ + loss t θ₁) (est : X → PMF T) :
    (sep / 2) * (1 - dist p₀ p₁) ≤
      max (∑ x, (p₀ x).toReal * ∑ t, (est x t).toReal * loss t θ₀)
        (∑ x, (p₁ x).toReal * ∑ t, (est x t).toReal * loss t θ₁) := by
  refine leCam_max_ge p₀ p₁ (loss := fun (q : PMF T) θ => ∑ t, (q t).toReal * loss t θ)
    (fun q => Finset.sum_nonneg fun t _ => mul_nonneg ENNReal.toReal_nonneg (hloss₀ t))
    (fun q => Finset.sum_nonneg fun t _ => mul_nonneg ENNReal.toReal_nonneg (hloss₁ t))
    (fun q => ?_) est
  rw [← Finset.sum_add_distrib]
  calc sep = ∑ t, (q t).toReal * sep := by rw [← Finset.sum_mul, sum_toReal, one_mul]
    _ ≤ ∑ t, ((q t).toReal * loss t θ₀ + (q t).toReal * loss t θ₁) := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (hsep t) ENNReal.toReal_nonneg

/-- **Le Cam–Pinsker minimax bound** on `PMF`: when `p₀.support ⊆ p₁.support` and `0 ≤ sep`,
worst-case expected loss is at least `(sep / 2) · (1 - √(D(p₀ ‖ p₁) / 2))`. -/
theorem leCam_max_ge_of_klDiv [MeasurableSpace X] [MeasurableSingletonClass X]
    {p₀ p₁ : PMF X} (hsupp : p₀.support ⊆ p₁.support) {loss : T → Θ → ℝ} {θ₀ θ₁ : Θ} {sep : ℝ}
    (hsep0 : 0 ≤ sep) (hloss₀ : ∀ t, 0 ≤ loss t θ₀) (hloss₁ : ∀ t, 0 ≤ loss t θ₁)
    (hsep : ∀ t, sep ≤ loss t θ₀ + loss t θ₁) (est : X → T) :
    (sep / 2) * (1 - Real.sqrt ((klDiv p₀.toMeasure p₁.toMeasure).toReal / 2)) ≤
      max (∑ x, (p₀ x).toReal * loss (est x) θ₀) (∑ x, (p₁ x).toReal * loss (est x) θ₁) :=
  (mul_le_mul_of_nonneg_left (sub_le_sub_left (dist_le_sqrt_toReal_klDiv_div_two hsupp) 1)
    (by positivity)).trans (leCam_max_ge p₀ p₁ hloss₀ hloss₁ hsep est)

/-- **I.i.d. Le Cam–Pinsker minimax bound**: from `n` i.i.d. observations under `p₀` or `p₁`
(`p₀.support ⊆ p₁.support`), worst-case expected loss is at least
`(sep / 2) · (1 - √(n · D(p₀ ‖ p₁) / 2))`. -/
theorem leCam_iid_max_ge_of_klDiv [MeasurableSpace X] [MeasurableSingletonClass X]
    {p₀ p₁ : PMF X} (hsupp : p₀.support ⊆ p₁.support) (n : ℕ) {loss : T → Θ → ℝ} {θ₀ θ₁ : Θ}
    {sep : ℝ} (hsep0 : 0 ≤ sep) (hloss₀ : ∀ t, 0 ≤ loss t θ₀) (hloss₁ : ∀ t, 0 ≤ loss t θ₁)
    (hsep : ∀ t, sep ≤ loss t θ₀ + loss t θ₁) (est : (Fin n → X) → T) :
    (sep / 2) * (1 - Real.sqrt (n * (klDiv p₀.toMeasure p₁.toMeasure).toReal / 2)) ≤
      max (∑ x, (iid p₀ n x).toReal * loss (est x) θ₀)
        (∑ x, (iid p₁ n x).toReal * loss (est x) θ₁) :=
  (mul_le_mul_of_nonneg_left (sub_le_sub_left (dist_iid_le_sqrt_mul_klDiv_div_two hsupp n) 1)
    (by positivity)).trans (leCam_max_ge (iid p₀ n) (iid p₁ n) hloss₀ hloss₁ hsep est)

/-- **Le Cam–`χ²` minimax bound** on `PMF`: when `p₀.support ⊆ p₁.support` and `0 ≤ sep`,
worst-case expected loss is at least `(sep / 2) · (1 - √(χ²(p₀ ‖ p₁)) / 2)`. -/
theorem leCam_max_ge_of_chiSquare {p₀ p₁ : PMF X} (hsupp : p₀.support ⊆ p₁.support)
    {loss : T → Θ → ℝ} {θ₀ θ₁ : Θ} {sep : ℝ} (hsep0 : 0 ≤ sep)
    (hloss₀ : ∀ t, 0 ≤ loss t θ₀) (hloss₁ : ∀ t, 0 ≤ loss t θ₁)
    (hsep : ∀ t, sep ≤ loss t θ₀ + loss t θ₁) (est : X → T) :
    (sep / 2) * (1 - Real.sqrt (chiSquare p₀ p₁) / 2) ≤
      max (∑ x, (p₀ x).toReal * loss (est x) θ₀) (∑ x, (p₁ x).toReal * loss (est x) θ₁) :=
  (mul_le_mul_of_nonneg_left (sub_le_sub_left (dist_le_sqrt_chiSquare_div_two hsupp) 1)
    (by positivity)).trans (leCam_max_ge p₀ p₁ hloss₀ hloss₁ hsep est)

end Finite

/-! ### Perturbed symmetric coins and Bernoulli mean minimax lower bounds -/

section BernoulliMinimax

/-- Support of `coin p` is all of `Bool` whenever `0 < p` and `p < 1`. -/
theorem mem_support_coin_of_Ioo {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (b : Bool) :
    b ∈ (coin p).support := by
  rw [PMF.mem_support_iff, coin_apply]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  · linarith
  · exact hp0

/-- KL divergence between symmetric `δ`-perturbed fair coins `1/2 ± δ` (`|δ| ≤ 1/6`) is at most
`18 · δ²` nats, proved via `KL ≤ χ²`. Shared by Le Cam and `d`-dimensional Assouad rates. -/
theorem toReal_klDiv_coin_perturbed_le {δ : ℝ} (hδ : |δ| ≤ 1 / 6)
    (p₀ p₁ : I) (hp₀ : (p₀ : ℝ) = 1 / 2 - δ) (hp₁ : (p₁ : ℝ) = 1 / 2 + δ) :
    (klDiv (coin p₀).toMeasure (coin p₁).toMeasure).toReal ≤ 18 * δ ^ 2 := by
  have habs := abs_le.mp hδ
  have hsupp : (coin p₀).support ⊆ (coin p₁).support := fun b _ =>
    mem_support_coin_of_Ioo (by rw [hp₁]; linarith) (by rw [hp₁]; linarith) b
  refine (toReal_klDiv_le_chiSquare hsupp).trans ?_
  rw [chiSquare_eq_sum hsupp, Fintype.sum_bool]
  simp only [coin_apply_toReal, ↓reduceIte, Bool.false_eq_true]
  rw [hp₀, hp₁]
  have hden1 : (0 : ℝ) < 1 / 2 + δ := by linarith
  have hden2 : (0 : ℝ) < 1 / 2 - δ := by linarith
  have h1sub : (1 : ℝ) - (1 / 2 + δ) = 1 / 2 - δ := by ring
  rw [h1sub]
  have hcomb : ((1 / 2 - δ - (1 / 2 + δ)) ^ 2) / (1 / 2 + δ) +
      ((1 - (1 / 2 - δ) - (1 / 2 - δ)) ^ 2) / (1 / 2 - δ) =
      4 * δ ^ 2 / ((1 / 2 + δ) * (1 / 2 - δ)) := by
    rw [div_add_div _ _ hden1.ne' hden2.ne']
    congr 1
    ring
  rw [hcomb, div_le_iff₀ (by positivity)]
  have hsq : δ ^ 2 ≤ 1 / 36 := by
    rw [← sq_abs]
    calc |δ| ^ 2 ≤ (1 / 6) ^ 2 := by gcongr
      _ = 1 / 36 := by norm_num
  have hprod : 2 / 9 ≤ (1 / 2 + δ) * (1 / 2 - δ) := by
    linarith [show (1 / 2 + δ) * (1 / 2 - δ) = 1 / 4 - δ ^ 2 by ring]
  calc 4 * δ ^ 2 = 18 * δ ^ 2 * (2 / 9) := by ring
    _ ≤ 18 * δ ^ 2 * ((1 / 2 + δ) * (1 / 2 - δ)) := by gcongr

/-- Symmetric `1 / (6 √n)`-perturbed fair coins `pBit : Bool → I` for sample size `n ≥ 1`, with
full `Bool` support and single-flip divergence `D(coin (pBit b) ‖ coin (pBit (!b))) ≤ 1 / (2 n)`. -/
theorem exists_coin_perturbed_klDiv_le {n : ℕ} (hn : 0 < n) :
    let δ : ℝ := 1 / (6 * Real.sqrt n)
    ∃ pBit : Bool → I,
      (pBit false : ℝ) = 1 / 2 - δ ∧
      (pBit true : ℝ) = 1 / 2 + δ ∧
      (∀ b₁ b₂ : Bool, (coin (pBit b₁)).support ⊆ (coin (pBit b₂)).support) ∧
      ∀ b : Bool,
        (klDiv (coin (pBit b)).toMeasure (coin (pBit (!b))).toMeasure).toReal ≤
          1 / (2 * (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsqrt_ge_one : 1 ≤ Real.sqrt n := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  set δ : ℝ := 1 / (6 * Real.sqrt n)
  have hδ_pos : 0 < δ := by positivity
  have hδ_le : δ ≤ 1 / 6 := by
    rw [one_div_le_one_div (by positivity) (by positivity)]
    linarith
  let pF : I := ⟨1 / 2 - δ, by constructor <;> linarith⟩
  let pT : I := ⟨1 / 2 + δ, by constructor <;> linarith⟩
  let pBit : Bool → I := fun b => if b then pT else pF
  have hpBit_oo (b : Bool) : 0 < (pBit b : ℝ) ∧ (pBit b : ℝ) < 1 := by
    cases b <;> simp only [pBit, pT, pF, ↓reduceIte, Bool.false_eq_true] <;>
      constructor <;> linarith
  have hsupp (b₁ b₂ : Bool) : (coin (pBit b₁)).support ⊆ (coin (pBit b₂)).support :=
    fun c _ => mem_support_coin_of_Ioo (hpBit_oo b₂).1 (hpBit_oo b₂).2 c
  have h18 : 18 * δ ^ 2 = 1 / (2 * (n : ℝ)) := by
    simp only [δ]
    field_simp
    rw [Real.sq_sqrt hn_pos.le]
    ring
  refine ⟨pBit, rfl, rfl, hsupp, fun b => ?_⟩
  rw [← h18]
  cases b
  · exact toReal_klDiv_coin_perturbed_le (by rwa [abs_of_pos hδ_pos]) pF pT rfl rfl
  · have h := toReal_klDiv_coin_perturbed_le (δ := -δ)
      (by rw [abs_neg, abs_of_pos hδ_pos]; exact hδ_le) pT pF
      (by change (1 / 2 + δ : ℝ) = 1 / 2 - -δ; ring)
      (by change (1 / 2 - δ : ℝ) = 1 / 2 + -δ; ring)
    simpa only [pBit, Bool.not_true, ↓reduceIte, Bool.false_eq_true, even_two.neg_pow] using h

private theorem leCam_perturbed_coin_factor_ge {n : ℕ} (hn : 0 < n) {kl : ℝ}
    (hkl : kl ≤ 1 / (2 * (n : ℝ))) :
    (1 / 2 : ℝ) ≤ 1 - Real.sqrt ((n : ℝ) * kl / 2) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hprod : (n : ℝ) * kl / 2 ≤ 1 / 4 := by
    calc (n : ℝ) * kl / 2 ≤ (n : ℝ) * (1 / (2 * (n : ℝ))) / 2 := by gcongr
      _ = 1 / 4 := by field_simp; ring
  have hsqrt : Real.sqrt ((n : ℝ) * kl / 2) ≤ 1 / 2 :=
    (Real.sqrt_le_sqrt hprod).trans_eq
      (by rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)])
  linarith

private theorem bernoulli_perturbed_minimax_lower_bound {n : ℕ} (hn : 0 < n)
    {loss : ℝ → I → ℝ} {sep : ℝ} (hsep0 : 0 ≤ sep)
    (hloss : ∀ q t, 0 ≤ loss t q)
    (hsep : ∀ p₀ p₁ : I, (p₀ : ℝ) = 1 / 2 - 1 / (6 * Real.sqrt n) →
      (p₁ : ℝ) = 1 / 2 + 1 / (6 * Real.sqrt n) → ∀ t, sep ≤ loss t p₀ + loss t p₁)
    (est : (Fin n → Bool) → ℝ) :
    ∃ p : I, sep / 4 ≤ ∑ x : Fin n → Bool, (iid (coin p) n x).toReal * loss (est x) p := by
  obtain ⟨pBit, hpF, hpT, hsupp, hkl⟩ := exists_coin_perturbed_klDiv_le hn
  set R : Bool → ℝ := fun b =>
    ∑ x : Fin n → Bool, (iid (coin (pBit b)) n x).toReal * loss (est x) (pBit b)
  have hbound : sep / 4 ≤ max (R false) (R true) := by
    calc sep / 4 = (sep / 2) * (1 / 2) := by ring
      _ ≤ (sep / 2) * (1 - Real.sqrt ((n : ℝ) *
            (klDiv (coin (pBit false)).toMeasure (coin (pBit true)).toMeasure).toReal / 2)) :=
          mul_le_mul_of_nonneg_left (leCam_perturbed_coin_factor_ge hn (hkl false)) (by positivity)
      _ ≤ max (R false) (R true) :=
          leCam_iid_max_ge_of_klDiv (hsupp false true) n (loss := loss)
            (θ₀ := pBit false) (θ₁ := pBit true) (sep := sep) hsep0
            (hloss (pBit false)) (hloss (pBit true)) (hsep _ _ hpF hpT) est
  rcases max_choice (R false) (R true) with h0 | h1
  · exact ⟨pBit false, hbound.trans_eq h0⟩
  · exact ⟨pBit true, hbound.trans_eq h1⟩

/-- **`Ω(1 / n)` minimax lower bound for Bernoulli mean estimation under squared error**: for every
sample size `n ≥ 1` and every estimator `est : (Fin n → Bool) → ℝ`, some bias `p ∈ [0, 1]` has
expected squared error at least `1 / (72 n)`. -/
theorem bernoulli_mean_minimax_sq_lower_bound {n : ℕ} (hn : 0 < n)
    (est : (Fin n → Bool) → ℝ) :
    ∃ p : I, 1 / (72 * (n : ℝ)) ≤
      ∑ x : Fin n → Bool, (iid (coin p) n x).toReal * (est x - (p : ℝ)) ^ 2 := by
  set δ : ℝ := 1 / (6 * Real.sqrt n)
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsep_eq : 2 * δ ^ 2 / 4 = 1 / (72 * (n : ℝ)) := by
    simp only [δ]
    field_simp
    rw [Real.sq_sqrt hn_pos.le]
    ring
  rw [← hsep_eq]
  exact bernoulli_perturbed_minimax_lower_bound hn
    (loss := fun t (q : I) => (t - (q : ℝ)) ^ 2) (sep := 2 * δ ^ 2) (by positivity)
    (fun _ _ => sq_nonneg _)
    (fun p₀ p₁ hp₀ hp₁ t => by
      rw [hp₀, hp₁]
      linarith [sq_nonneg (t - 1 / 2),
        show (t - (1 / 2 - δ)) ^ 2 + (t - (1 / 2 + δ)) ^ 2 =
          2 * (t - 1 / 2) ^ 2 + 2 * δ ^ 2 by ring])
    est

/-- **`Ω(1 / √n)` minimax lower bound for Bernoulli mean estimation under absolute error**: for
every sample size `n ≥ 1` and every estimator `est : (Fin n → Bool) → ℝ`, some bias `p ∈ [0, 1]` has
expected absolute error at least `1 / (12 √n)`. -/
theorem bernoulli_mean_minimax_abs_lower_bound {n : ℕ} (hn : 0 < n)
    (est : (Fin n → Bool) → ℝ) :
    ∃ p : I, 1 / (12 * Real.sqrt n) ≤
      ∑ x : Fin n → Bool, (iid (coin p) n x).toReal * |est x - (p : ℝ)| := by
  set δ : ℝ := 1 / (6 * Real.sqrt n)
  have hsep_eq : 2 * δ / 4 = 1 / (12 * Real.sqrt n) := by simp only [δ]; ring
  rw [← hsep_eq]
  exact bernoulli_perturbed_minimax_lower_bound hn
    (loss := fun t (q : I) => |t - (q : ℝ)|) (sep := 2 * δ) (by positivity)
    (fun _ _ => abs_nonneg _)
    (fun p₀ p₁ hp₀ hp₁ t => by
      rw [hp₀, hp₁]
      have htri := abs_sub_le (1 / 2 + δ) t (1 / 2 - δ)
      rw [abs_sub_comm (1 / 2 + δ) t] at htri
      have hsub : |(1 / 2 + δ) - (1 / 2 - δ)| = 2 * δ := by
        rw [show (1 / 2 + δ) - (1 / 2 - δ) = 2 * δ by ring, abs_of_pos (by positivity)]
      linarith)
    est

end BernoulliMinimax

end PMF

end Cslib.Probability
