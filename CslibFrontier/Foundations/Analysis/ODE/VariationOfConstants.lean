/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Analysis/ODE/VariationOfConstants.lean`)

public import CslibFrontier.Foundations.Analysis.ODE.LinearFlow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Variation of constants for forced linear ODEs

For a bounded linear operator `A : E →L[ℝ] E` on a real Banach space `E` and a forcing term
`f : ℝ → E`, the curve
`t ↦ exp (t • A) x₀ + ∫ s in 0..t, exp ((t - s) • A) (f s)`
solves `ẋ = A x + f` with `x 0 = x₀`, and it is the only solution, on every finite interval
`[0, T]` and on `[0, ∞)`. The forcing is only required to be continuous on the time set; it need
not be bounded on `[0, ∞)`. No stability, spectral or diagonalizability assumption is made.

Derivatives are taken within the time set, as in `ContinuousLinearMap.IsTrajectoryOn`: on
`Set.Icc 0 T` a solution has a right derivative at `0` and a left derivative at `T`, and on
`Set.Ici 0` a right derivative at `0`. Uniqueness is reduced to that of the homogeneous equation:
the difference of two solutions is a trajectory of `ẋ = A x` starting at `0`, which vanishes by
`ContinuousLinearMap.IsTrajectoryOn.eqOn_exp_smul_apply_Icc`.

## Main results

* `ContinuousLinearMap.hasDerivAt_exp_smul_apply_add_integral`: the variation-of-constants curve
  of a continuous forcing term on `ℝ` solves `ẋ = A x + f` at every time.
* `ContinuousLinearMap.hasDerivWithinAt_exp_smul_apply_add_integral_Icc` and
  `ContinuousLinearMap.hasDerivWithinAt_exp_smul_apply_add_integral_Ici`: existence on `[0, T]`
  and on `[0, ∞)` for a forcing term continuous there.
* `ContinuousLinearMap.eqOn_exp_smul_apply_add_integral_Icc` and
  `ContinuousLinearMap.eqOn_exp_smul_apply_add_integral_Ici`: uniqueness, every solution of
  `ẋ = A x + f` on `[0, T]` or on `[0, ∞)` is the variation-of-constants curve of `x 0`.
-/

public section

open Set NormedSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem commute_smul_smul (A : E →L[ℝ] E) (t s : ℝ) : Commute (t • A) (s • A) :=
  ((Commute.refl A).smul_left t).smul_right s

private theorem exp_add_smul (A : E →L[ℝ] E) (t s : ℝ) :
    exp ((t + s) • A) = exp (t • A) * exp (s • A) := by
  rw [add_smul]
  exact exp_add_of_commute_of_mem_ball (𝕂 := ℝ) (commute_smul_smul A t s)
    ((expSeries_radius_eq_top ℝ (E →L[ℝ] E)).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ (E →L[ℝ] E)).symm ▸ edist_lt_top _ _)

private theorem exp_smul_apply_exp_neg_smul_apply (A : E →L[ℝ] E) (t : ℝ) (y : E) :
    exp (t • A) (exp ((-t) • A) y) = y := by
  rw [← mul_apply_eq_comp, ← exp_add_smul, add_neg_cancel, zero_smul, exp_zero,
    one_apply_eq_self]

/-- **Variation of constants, continuous forcing on `ℝ`.** For continuous `f`, the curve
`t ↦ exp (t • A) x₀ + ∫ s in 0..t, exp ((t - s) • A) (f s)` has derivative `A (x t) + f t` at
every time `t`. -/
theorem hasDerivAt_exp_smul_apply_add_integral (A : E →L[ℝ] E) (x₀ : E) {f : ℝ → E}
    (hf : Continuous f) (t : ℝ) :
    HasDerivAt (fun τ => exp (τ • A) x₀ + ∫ s in 0..τ, exp ((τ - s) • A) (f s))
      (A (exp (t • A) x₀ + ∫ s in 0..t, exp ((t - s) • A) (f s)) + f t) t := by
  have hc : Continuous fun τ : ℝ => exp (τ • A) := (differentiable_exp_smul_const ℝ A).continuous
  have hk : Continuous fun s : ℝ => exp ((-s) • A) (f s) := (hc.comp continuous_neg).clm_apply hf
  -- `exp ((τ - s) • A) = exp (τ • A) * exp (-s • A)` pulls the `τ`-dependence out of the integral.
  have key : ∀ τ : ℝ, exp (τ • A) x₀ + ∫ s in 0..τ, exp ((τ - s) • A) (f s) =
      exp (τ • A) (x₀ + ∫ s in 0..τ, exp ((-s) • A) (f s)) := fun τ => by
    rw [map_add, ← (exp (τ • A)).intervalIntegral_comp_comm (hk.intervalIntegrable _ _)]
    simp only [sub_eq_add_neg, exp_add_smul A τ, mul_apply_eq_comp]
  simp only [key]
  have h := HasDerivAt.clm_apply (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t)
    ((hasDerivAt_const t x₀).add (hk.integral_hasStrictDerivAt 0 t).hasDerivAt)
  convert h using 1
  rw [zero_add, mul_apply_eq_comp, exp_smul_apply_exp_neg_smul_apply]
  rfl

variable {A : E →L[ℝ] E} {f : ℝ → E}

omit [CompleteSpace E] in
/-- The variation-of-constants integral up to time `t ≥ 0` only depends on the forcing on
`[0, t]`. -/
private theorem integral_congr_Icc {f g : ℝ → E} {t : ℝ} (ht : 0 ≤ t) (h : EqOn f g (Icc 0 t)) :
    ∫ s in 0..t, exp ((t - s) • A) (f s) = ∫ s in 0..t, exp ((t - s) • A) (g s) :=
  intervalIntegral.integral_congr fun s hs => by
    rw [uIcc_of_le ht] at hs
    rw [h hs]

/-- Existence of a solution on a time set `S ⊆ [0, ∞)` that contains `[0, t]` with each of its
points `t`, for a forcing term that agrees on `S` with a continuous function `g`. -/
private theorem hasDerivWithinAt_of_eqOn {S : Set ℝ} (hS₀ : S ⊆ Ici 0)
    (hS : ∀ t ∈ S, Icc 0 t ⊆ S) (A : E →L[ℝ] E) (x₀ : E) {g : ℝ → E} (hg : Continuous g)
    (hfg : EqOn f g S) {t : ℝ} (ht : t ∈ S) :
    HasDerivWithinAt (fun τ => exp (τ • A) x₀ + ∫ s in 0..τ, exp ((τ - s) • A) (f s))
      (A (exp (t • A) x₀ + ∫ s in 0..t, exp ((t - s) • A) (f s)) + f t) S t := by
  have hcongr : ∀ τ ∈ S, exp (τ • A) x₀ + ∫ s in 0..τ, exp ((τ - s) • A) (f s) =
      exp (τ • A) x₀ + ∫ s in 0..τ, exp ((τ - s) • A) (g s) := fun τ hτ => by
    rw [integral_congr_Icc (hS₀ hτ) (hfg.mono (hS τ hτ))]
  rw [hcongr t ht, hfg ht]
  exact (hasDerivAt_exp_smul_apply_add_integral A x₀ hg t).hasDerivWithinAt.congr hcongr
    (hcongr t ht)

/-- **Existence on `[0, T]`.** For a forcing term continuous on `[0, T]`, the
variation-of-constants curve solves `ẋ = A x + f` on `[0, T]`, with one-sided derivatives at the
endpoints. -/
theorem hasDerivWithinAt_exp_smul_apply_add_integral_Icc (A : E →L[ℝ] E) (x₀ : E) {T : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun τ => exp (τ • A) x₀ + ∫ s in 0..τ, exp ((τ - s) • A) (f s))
      (A (exp (t • A) x₀ + ∫ s in 0..t, exp ((t - s) • A) (f s)) + f t) (Icc 0 T) t := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  refine hasDerivWithinAt_of_eqOn (S := Icc 0 T) (fun τ hτ => hτ.1)
    (fun τ hτ => Icc_subset_Icc_right hτ.2) A x₀
    (g := fun s => f (max 0 (min T s)))
    (hf.comp_continuous (by fun_prop) fun s => ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩)
    (fun s hs => ?_) ht
  simp [min_eq_right hs.2, max_eq_right hs.1]

/-- **Existence on `[0, ∞)`.** For a forcing term continuous on `[0, ∞)`, the
variation-of-constants curve solves `ẋ = A x + f` on `[0, ∞)`, with a right derivative at `0`. -/
theorem hasDerivWithinAt_exp_smul_apply_add_integral_Ici (A : E →L[ℝ] E) (x₀ : E)
    (hf : ContinuousOn f (Ici 0)) {t : ℝ} (ht : t ∈ Ici 0) :
    HasDerivWithinAt (fun τ => exp (τ • A) x₀ + ∫ s in 0..τ, exp ((τ - s) • A) (f s))
      (A (exp (t • A) x₀ + ∫ s in 0..t, exp ((t - s) • A) (f s)) + f t) (Ici 0) t := by
  refine hasDerivWithinAt_of_eqOn subset_rfl (fun τ _ => Icc_subset_Ici_self) A x₀
    (g := fun s => f (max 0 s)) (hf.comp_continuous (by fun_prop) fun s => le_max_left _ _)
    (fun s hs => ?_) ht
  simp [max_eq_right (show (0 : ℝ) ≤ s from hs)]

/-- **Uniqueness on `[0, T]`.** For a forcing term continuous on `[0, T]`, every solution of
`ẋ = A x + f` on `[0, T]` is the variation-of-constants curve of its initial value there. -/
theorem eqOn_exp_smul_apply_add_integral_Icc {x : ℝ → E} {T : ℝ} (hf : ContinuousOn f (Icc 0 T))
    (hx : ∀ t ∈ Icc 0 T, HasDerivWithinAt x (A (x t) + f t) (Icc 0 T) t) :
    EqOn x (fun t => exp (t • A) (x 0) + ∫ s in 0..t, exp ((t - s) • A) (f s)) (Icc 0 T) := by
  intro t ht
  set z := fun t => exp (t • A) (x 0) + ∫ s in 0..t, exp ((t - s) • A) (f s)
  -- The difference of two solutions solves the homogeneous equation and starts at `0`.
  have hd : A.IsTrajectoryOn (x - z) (Icc 0 T) := fun τ hτ => by
    have := (hx τ hτ).sub (hasDerivWithinAt_exp_smul_apply_add_integral_Icc A (x 0) hf hτ)
    simpa [z, map_sub] using this
  have h := hd.eqOn_exp_smul_apply_Icc ht
  simp only [Pi.sub_apply, z, zero_smul, exp_zero, one_apply_eq_self,
    intervalIntegral.integral_same, add_zero, sub_self, map_zero] at h
  exact sub_eq_zero.1 h

/-- **Uniqueness on `[0, ∞)`.** For a forcing term continuous on `[0, ∞)`, every solution of
`ẋ = A x + f` on `[0, ∞)` is the variation-of-constants curve of its initial value there. -/
theorem eqOn_exp_smul_apply_add_integral_Ici {x : ℝ → E} (hf : ContinuousOn f (Ici 0))
    (hx : ∀ t ∈ Ici 0, HasDerivWithinAt x (A (x t) + f t) (Ici 0) t) :
    EqOn x (fun t => exp (t • A) (x 0) + ∫ s in 0..t, exp ((t - s) • A) (f s)) (Ici 0) :=
  fun t ht => eqOn_exp_smul_apply_add_integral_Icc (T := t) (hf.mono Icc_subset_Ici_self)
    (fun τ hτ => (hx τ (Icc_subset_Ici_self hτ)).mono Icc_subset_Ici_self) ⟨ht, le_rfl⟩

end ContinuousLinearMap
