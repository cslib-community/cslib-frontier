/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Convolution.lean`)

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Window integrals of a convolution with a past-supported input

Let `g p : ℝ → ℝ`, with `p` integrable and `p s = 0` for `s > a`, and put
`y t = ∫ s, g (t - s) * p s` (Mathlib's convolution `p ⋆ g` for the multiplication pairing). For
`t` in a window `[a + T, a + T + W]`, only the values of `g` on `(T, ∞)` enter `y t`, since
`t - s > T` whenever `s ≤ a` and `t > a + T`. If `g` is square integrable on `(T, ∞)` with
`∫_T^∞ g² ≤ E`, then (`MeasureTheory.intervalIntegrable_and_integral_abs_le_of_tail`)

`∫_{a+T}^{a+T+W} |y| ≤ ‖p‖₁ √(W E)`,

and `y` is integrable on the window; the signed bound `|∫_{a+T}^{a+T+W} y| ≤ ‖p‖₁ √(W E)` follows
by `intervalIntegral.abs_integral_le_integral_abs`. The proof is Tonelli's theorem, which
exchanges the window integral with the integral over `s`, followed by the Cauchy–Schwarz
inequality on each shifted window `[a + T - s, a + T + W - s] ⊆ (T, ∞)`, of length `W`:
`∫_{window - s} |g| ≤ √W (∫_T^∞ g²)^{1/2}`. No integrability of `g` itself is assumed, so `g`
may be a kernel that is only square integrable away from the origin.

The intended reading is a causal linear filter with impulse response `g` (zero on `(-∞, 0)`),
driven by an input `p` that ends at time `a`: the bound controls how much of the input still
reaches a measurement window that opens `T` after the input stops.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {g p : ℝ → ℝ} {a T W E : ℝ}

/-- **Cauchy–Schwarz on a shifted window.** If `∫_T^∞ g² ≤ E` and `s ≤ a`, then
`∫_{(a + T, a + T + W]} |g (t - s)| dt ≤ √(W E)`, in `ℝ≥0∞`. -/
private theorem lintegral_Ioc_enorm_comp_sub_le (hg : AEStronglyMeasurable g)
    (hg2 : IntegrableOn (fun t => g t ^ 2) (Ioi T)) (hE : ∫ t in Ioi T, g t ^ 2 ≤ E)
    (hW : 0 ≤ W) {s : ℝ} (hs : s ≤ a) :
    ∫⁻ t in Ioc (a + T) (a + T + W), ‖g (t - s)‖ₑ ≤ ENNReal.ofReal √(W * E) := by
  set I := Ioc (a + T) (a + T + W)
  have hE0 : 0 ≤ E :=
    (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _).trans hE
  have hgs : AEMeasurable (fun t => ‖g (t - s)‖ₑ ^ (2 : ℝ)) (volume.restrict I) :=
    ((hg.comp_measurePreserving (measurePreserving_sub_right volume s)).eNorm.pow_const
      _).restrict
  have hcs := ENNReal.lintegral_mul_norm_pow_le hgs (aemeasurable_const (b := (1 : ℝ≥0∞)))
    (p := 1 / 2) (q := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hl : ∀ t, (‖g (t - s)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (1 : ℝ≥0∞) ^ (1 / 2 : ℝ) =
      ‖g (t - s)‖ₑ := fun t => by
    rw [ENNReal.one_rpow, mul_one, ← ENNReal.rpow_mul]
    norm_num
  simp only [hl] at hcs
  have h2 : ∫⁻ t in I, ‖g (t - s)‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal E := by
    calc ∫⁻ t in I, ‖g (t - s)‖ₑ ^ (2 : ℝ)
        = ∫⁻ t in I, (Ioi T).indicator (fun u => ‖g u‖ₑ ^ (2 : ℝ)) (t - s) := by
          refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
          rw [indicator_of_mem (by simp only [mem_Ioi]; linarith [ht.1])]
      _ ≤ ∫⁻ t, (Ioi T).indicator (fun u => ‖g u‖ₑ ^ (2 : ℝ)) (t - s) :=
          setLIntegral_le_lintegral _ _
      _ = ∫⁻ u in Ioi T, ‖g u‖ₑ ^ (2 : ℝ) := by
          rw [lintegral_sub_right_eq_self (fun u => (Ioi T).indicator _ u) s,
            lintegral_indicator measurableSet_Ioi]
      _ = ENNReal.ofReal (∫ u in Ioi T, g u ^ 2) := by
          rw [ofReal_integral_eq_lintegral_ofReal hg2 (ae_of_all _ fun u => sq_nonneg _)]
          refine lintegral_congr fun u => ?_
          rw [Real.eNorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
          norm_num [sq_abs]
      _ ≤ ENNReal.ofReal E := ENNReal.ofReal_le_ofReal hE
  have h1 : ∫⁻ _ in I, (1 : ℝ≥0∞) = ENNReal.ofReal W := by
    simp only [lintegral_const, Measure.restrict_apply_univ, one_mul, I, Real.volume_Ioc]
    ring_nf
  calc ∫⁻ t in I, ‖g (t - s)‖ₑ
      ≤ ENNReal.ofReal E ^ (1 / 2 : ℝ) * ENNReal.ofReal W ^ (1 / 2 : ℝ) := by
        refine hcs.trans ?_
        rw [h1]
        gcongr
    _ = ENNReal.ofReal √(W * E) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hE0 (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hW (by norm_num), ← ENNReal.ofReal_mul (by positivity),
          Real.sqrt_eq_rpow, Real.mul_rpow hW hE0, mul_comm]

/-- **Window bound for a convolution with a past-supported input.** Let `p` be integrable with
`p s = 0` for `s > a`, let `g` be a.e. strongly measurable and square integrable on `(T, ∞)` with
`∫_T^∞ g² ≤ E`, and let `y t = ∫ s, g (t - s) * p s`. Then for `W ≥ 0`, `y` is integrable on the
window `[a + T, a + T + W]` and `∫_{a+T}^{a+T+W} |y| ≤ ‖p‖₁ √(W E)`, where
`‖p‖₁ = ∫ s, |p s|`. -/
theorem intervalIntegrable_and_integral_abs_le_of_tail (hg : AEStronglyMeasurable g)
    (hg2 : IntegrableOn (fun t => g t ^ 2) (Ioi T)) (hE : ∫ t in Ioi T, g t ^ 2 ≤ E)
    (hp : Integrable p) (hpa : ∀ s, a < s → p s = 0) (hW : 0 ≤ W) :
    IntervalIntegrable (fun t => ∫ s, g (t - s) * p s) volume (a + T) (a + T + W) ∧
      ∫ t in (a + T)..(a + T + W), |∫ s, g (t - s) * p s| ≤ (∫ s, |p s|) * √(W * E) := by
  set I := Ioc (a + T) (a + T + W)
  set y := fun t => ∫ s, g (t - s) * p s
  have hle : a + T ≤ a + T + W := by linarith
  have hjoint : AEStronglyMeasurable (fun z : ℝ × ℝ => g (z.1 - z.2) * p z.2)
      (volume.prod volume) := by
    simpa [mul_comm] using
      hp.aestronglyMeasurable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hg
  have hy : AEStronglyMeasurable y volume := AEStronglyMeasurable.integral_prod_right' hjoint
  have hprod : (volume.restrict I).prod (volume : Measure ℝ) =
      (volume.prod volume).restrict (I ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hunc : (Function.uncurry fun t s => ‖g (t - s)‖ₑ * ‖p s‖ₑ) =
      fun z : ℝ × ℝ => ‖g (z.1 - z.2) * p z.2‖ₑ := by
    funext z
    simp [Function.uncurry, eNorm_mul]
  have hlin : ∫⁻ t in I, ‖y t‖ₑ ≤ ENNReal.ofReal ((∫ s, |p s|) * √(W * E)) := by
    calc ∫⁻ t in I, ‖y t‖ₑ ≤ ∫⁻ t in I, ∫⁻ s, ‖g (t - s)‖ₑ * ‖p s‖ₑ :=
          lintegral_mono fun t => (eNorm_integral_le_lintegral_eNorm _).trans_eq
            (by simp only [eNorm_mul])
      _ = ∫⁻ s, ∫⁻ t in I, ‖g (t - s)‖ₑ * ‖p s‖ₑ := by
          refine lintegral_lintegral_swap ?_
          rw [hprod, hunc]
          exact hjoint.eNorm.restrict
      _ ≤ ∫⁻ s, ENNReal.ofReal √(W * E) * ‖p s‖ₑ := by
          refine lintegral_mono fun s => ?_
          rw [lintegral_mul_const' _ _ eNorm_ne_top, mul_comm]
          rcases le_or_gt s a with hs | hs
          · rw [mul_comm]
            gcongr
            exact lintegral_Ioc_enorm_comp_sub_le hg hg2 hE hW hs
          · simp [hpa s hs]
      _ = ENNReal.ofReal ((∫ s, |p s|) * √(W * E)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            ← ofReal_integral_norm_eq_lintegral_eNorm hp,
            ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_comm]
          simp only [Real.norm_eq_abs]
  have hint : IntegrableOn y I := ⟨hy.restrict, hlin.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hle).2 hint, ?_⟩
  rw [intervalIntegral.integral_of_le hle]
  have hn : ∫ t in I, |y t| = (∫⁻ t in I, ‖y t‖ₑ).toReal := by
    simpa only [Real.norm_eq_abs] using integral_norm_eq_lintegral_eNorm hy.restrict
  rw [hn]
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (integral_nonneg fun _ => abs_nonneg _) (Real.sqrt_nonneg _)) hlin

end MeasureTheory
