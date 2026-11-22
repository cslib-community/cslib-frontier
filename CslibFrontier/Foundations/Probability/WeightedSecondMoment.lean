/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Moments/Variance.lean`)

public import CslibFrontier.Foundations.Probability.SecondMoment
import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Weighted second-moment concentration for locally dependent random variables

`CslibFrontier/Foundations/Probability/SecondMoment.lean` proves Chebyshev concentration for sums
of unweighted indicators of locally dependent events in a product probability space. This module
proves the corresponding bound for sums of bounded nonnegative local random variables
`X k : (Π i, Ω i) → ℝ` (`0 ≤ X k ω ≤ W`, such as `w k * (A k).indicator 1 ω`): if each `X k`
depends only on coordinates in `S k` and each `S k` meets at most `D` other `S l` (`l ∈ F`), then
`Var[∑ k ∈ F, X k] ≤ #F * W ^ 2 * D`, so the sum deviates from its mean by at least `c > 0` with
probability at most `#F * W ^ 2 * D / c ^ 2`.

## Main results

* `ProbabilityTheory.variance_pi_sum_bounded_le`: variance bound `#F * W ^ 2 * D` for bounded
  nonnegative local functions on a product probability space.
* `ProbabilityTheory.measureReal_pi_le_abs_sum_bounded_sub_le`: Chebyshev deviation bound
  `#F * W ^ 2 * D / c ^ 2` for bounded nonnegative local functions.
* `ProbabilityTheory.measureReal_pi_le_abs_sum_weighted_indicator_sub_le`: specialization to
  weighted indicators `w k * (A k).indicator 1 ω` with `0 ≤ w k ≤ W`.
-/

public section

open MeasureTheory Finset

namespace ProbabilityTheory

section General

variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {P : Measure Ω₀} [IsProbabilityMeasure P]

private theorem memLp_of_nonneg_le {f : Ω₀ → ℝ} (hf : Measurable f) {W : ℝ}
    (h0 : ∀ ω, 0 ≤ f ω) (hW : ∀ ω, f ω ≤ W) : MemLp f 2 P := by
  refine MemLp.of_bound hf.aestronglyMeasurable W (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (h0 ω)]
  exact hW ω

private theorem covariance_le_sq_of_nonneg_le {f g : Ω₀ → ℝ} (hf : Measurable f)
    (hg : Measurable g) {W : ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hfW : ∀ ω, f ω ≤ W)
    (hg0 : ∀ ω, 0 ≤ g ω) (hgW : ∀ ω, g ω ≤ W) :
    cov[f, g; P] ≤ W ^ 2 := by
  have hmf := memLp_of_nonneg_le (P := P) hf hf0 hfW
  have hmg := memLp_of_nonneg_le (P := P) hg hg0 hgW
  rw [covariance_eq_sub hmf hmg]
  simp only [Pi.mul_apply]
  have hint_prod : Integrable (fun ω => f ω * g ω) P := hmf.integrable_mul hmg
  have hconst : Integrable (fun _ : Ω₀ => W ^ 2) P := integrable_const (W ^ 2)
  have hprod_le : ∫ ω, f ω * g ω ∂P ≤ W ^ 2 := by
    calc ∫ ω, f ω * g ω ∂P ≤ ∫ _, W ^ 2 ∂P :=
          integral_mono hint_prod hconst fun ω => by
            have hW0 : 0 ≤ W := (hf0 ω).trans (hfW ω)
            calc f ω * g ω ≤ W * W := mul_le_mul (hfW ω) (hgW ω) (hg0 ω) hW0
              _ = W ^ 2 := (sq W).symm
      _ = W ^ 2 := by simp
  have hint_f : 0 ≤ ∫ ω, f ω ∂P := integral_nonneg hf0
  have hint_g : 0 ≤ ∫ ω, g ω ∂P := integral_nonneg hg0
  nlinarith [mul_nonneg hint_f hint_g]

end General

variable {ι κ : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  {μ : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]

/-- **Variance of a sum of bounded nonnegative local random variables.** -/
theorem variance_pi_sum_bounded_le (F : Finset κ) {X : κ → (Π i, Ω i) → ℝ}
    (hX : ∀ k ∈ F, Measurable (X k)) {W : ℝ}
    (h0 : ∀ k ∈ F, ∀ ω, 0 ≤ X k ω) (hle : ∀ k ∈ F, ∀ ω, X k ω ≤ W)
    (S : κ → Set ι) (hXS : ∀ k ∈ F, DependsOn (X k) (S k))
    (G : κ → κ → Prop) [DecidableRel G]
    (hG : ∀ k ∈ F, ∀ l ∈ F, ¬ G k l → Disjoint (S k) (S l)) {D : ℕ}
    (hD : ∀ k ∈ F, #{l ∈ F | G k l} ≤ D) :
    Var[fun ω => ∑ k ∈ F, X k ω; Measure.pi μ] ≤ #F * W ^ 2 * D := by
  set P := Measure.pi μ
  have hm (k : κ) (hk : k ∈ F) : MemLp (X k) 2 P :=
    memLp_of_nonneg_le (hX k hk) (h0 k hk) (hle k hk)
  rw [variance_fun_sum' hm]
  calc ∑ k ∈ F, ∑ l ∈ F, cov[X k, X l; P]
      ≤ ∑ k ∈ F, ∑ l ∈ F, if G k l then W ^ 2 else 0 := by
        refine sum_le_sum fun k hk => sum_le_sum fun l hl => ?_
        split_ifs with hkl
        · exact covariance_le_sq_of_nonneg_le (hX k hk) (hX l hl) (h0 k hk) (hle k hk)
            (h0 l hl) (hle l hl)
        · exact ((indepFun_pi_of_dependsOn (hXS k hk) (hXS l hl)
            (hG k hk l hl hkl)).covariance_eq_zero (hm k hk) (hm l hl)).le
    _ = ∑ k ∈ F, (#{l ∈ F | G k l} : ℝ) * W ^ 2 := by
        refine sum_congr rfl fun k _ => ?_
        rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
    _ ≤ ∑ _k ∈ F, (D : ℝ) * W ^ 2 :=
        sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (by exact_mod_cast hD k hk) (sq_nonneg W)
    _ = #F * W ^ 2 * D := by
        rw [sum_const, nsmul_eq_mul]
        ring

/-- **Chebyshev concentration for bounded nonnegative local random variables.** -/
theorem measureReal_pi_le_abs_sum_bounded_sub_le (F : Finset κ) {X : κ → (Π i, Ω i) → ℝ}
    (hX : ∀ k ∈ F, Measurable (X k)) {W : ℝ}
    (h0 : ∀ k ∈ F, ∀ ω, 0 ≤ X k ω) (hle : ∀ k ∈ F, ∀ ω, X k ω ≤ W)
    (S : κ → Set ι) (hXS : ∀ k ∈ F, DependsOn (X k) (S k))
    (G : κ → κ → Prop) [DecidableRel G]
    (hG : ∀ k ∈ F, ∀ l ∈ F, ¬ G k l → Disjoint (S k) (S l)) {D : ℕ}
    (hD : ∀ k ∈ F, #{l ∈ F | G k l} ≤ D) {c : ℝ} (hc : 0 < c) :
    (Measure.pi μ).real
      {ω | c ≤ |∑ k ∈ F, X k ω - ∑ k ∈ F, ∫ ω', X k ω' ∂Measure.pi μ|} ≤
        #F * W ^ 2 * D / c ^ 2 := by
  set P := Measure.pi μ
  have hm (k : κ) (hk : k ∈ F) : MemLp (X k) 2 P :=
    memLp_of_nonneg_le (hX k hk) (h0 k hk) (hle k hk)
  have hY : MemLp (fun ω => ∑ k ∈ F, X k ω) 2 P := memLp_finsetSum F hm
  have hmean : ∫ ω, ∑ k ∈ F, X k ω ∂P = ∑ k ∈ F, ∫ ω', X k ω' ∂P :=
    integral_finsetSum F fun k hk => (hm k hk).integrable one_le_two
  have cheb := meas_ge_le_variance_div_sq hY hc
  rw [hmean] at cheb
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (cheb.trans ?_)
  exact ENNReal.ofReal_le_ofReal
    (by gcongr; exact variance_pi_sum_bounded_le F hX h0 hle S hXS G hG hD)

/-- **Weighted indicator concentration** for locally dependent events in a product probability
space: when `0 ≤ w k ≤ W` on `F`, `∑ k ∈ F, w k * 1_{A k}` deviates from `∑ k ∈ F, w k * P(A k)`
by at least `c > 0` with probability at most `#F * W ^ 2 * D / c ^ 2`. -/
theorem measureReal_pi_le_abs_sum_weighted_indicator_sub_le (F : Finset κ)
    {A : κ → Set (Π i, Ω i)} (hA : ∀ k ∈ F, MeasurableSet (A k))
    {w : κ → ℝ} {W : ℝ} (hW0 : 0 ≤ W) (hw0 : ∀ k ∈ F, 0 ≤ w k) (hwW : ∀ k ∈ F, w k ≤ W)
    (S : κ → Set ι) (hAS : ∀ k ∈ F, DependsOn (· ∈ A k) (S k))
    (G : κ → κ → Prop) [DecidableRel G]
    (hG : ∀ k ∈ F, ∀ l ∈ F, ¬ G k l → Disjoint (S k) (S l)) {D : ℕ}
    (hD : ∀ k ∈ F, #{l ∈ F | G k l} ≤ D) {c : ℝ} (hc : 0 < c) :
    (Measure.pi μ).real
      {ω | c ≤ |∑ k ∈ F, w k * (A k).indicator (1 : (Π i, Ω i) → ℝ) ω -
        ∑ k ∈ F, w k * (Measure.pi μ).real (A k)|} ≤
        #F * W ^ 2 * D / c ^ 2 := by
  set P := Measure.pi μ
  let X : κ → (Π i, Ω i) → ℝ := fun k ω => w k * (A k).indicator (1 : (Π i, Ω i) → ℝ) ω
  have hXm (k : κ) (hk : k ∈ F) : Measurable (X k) :=
    measurable_const.mul (measurable_const.indicator (hA k hk))
  have hX0 (k : κ) (hk : k ∈ F) (ω : Π i, Ω i) : 0 ≤ X k ω := by
    dsimp only [X]
    exact mul_nonneg (hw0 k hk) (Set.indicator_apply_nonneg fun _ => zero_le_one)
  have hXW (k : κ) (hk : k ∈ F) (ω : Π i, Ω i) : X k ω ≤ W := by
    dsimp only [X]
    by_cases hω : ω ∈ A k
    · simp [hω, hwW k hk]
    · simp [hω, hW0]
  have hXdep (k : κ) (hk : k ∈ F) : DependsOn (X k) (S k) := by
    intro ω₁ ω₂ h12
    dsimp only [X]
    congr 1
    by_cases h1 : ω₁ ∈ A k
    · have h2 : ω₂ ∈ A k := Eq.mp (hAS k hk h12) h1
      simp [h1, h2]
    · have h2 : ω₂ ∉ A k := fun h => h1 (Eq.mpr (hAS k hk h12) h)
      simp [h1, h2]
  have hmean (k : κ) (hk : k ∈ F) : ∫ ω, X k ω ∂P = w k * P.real (A k) := by
    dsimp only [X]
    rw [integral_const_mul, integral_indicator_one (hA k hk)]
  have h := measureReal_pi_le_abs_sum_bounded_sub_le (μ := μ) F hXm hX0 hXW S hXdep G hG hD hc
  have hsum : ∑ k ∈ F, ∫ ω', X k ω' ∂P = ∑ k ∈ F, w k * P.real (A k) :=
    sum_congr rfl hmean
  rwa [hsum] at h

end ProbabilityTheory
