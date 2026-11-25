/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.StateCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Estimates for the crossing inequality

For Proposition B.3 (prop:crossing) of *VP ≠ VNP over every field* [AnthropicVPVNP2026]: logarithms
are eventually small against square roots (`eventually_log_le_mul_sqrt`), and the number of states
of energy about `p² n` (`eventually_le_logLowStates_floor`).

## Main results

* `eventually_log_le_mul_sqrt`, `sqrt_floor_le`, `eventually_le_logLowStates_floor`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition B.3 of the paper; module `Nc.Cross.Data`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Curvature

open Finset Filter

/-- `log (A n + 1) ≤ η √n` for all large `n`, for every `A ≥ 0` and `η > 0`. -/
theorem eventually_log_le_mul_sqrt {A : ℝ} (hA : 0 ≤ A) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, Real.log (A * n + 1) ≤ η * Real.sqrt n := by
  have h1 : (fun x : ℝ => Real.log x) =o[atTop] fun x => x ^ (1 / 2 : ℝ) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have h2 := tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually (h1.bound (half_pos hη))
  have h3 : ∀ᶠ n : ℕ in atTop, Real.log (A + 1) / (η / 2) ≤ Real.sqrt n :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop _
  filter_upwards [h2, h3, eventually_ge_atTop 1] with n h2 h3 hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_iff₀ (half_pos hη)] at h3
  rw [← Real.sqrt_eq_rpow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      at h2
  have h4 := (le_abs_self _).trans h2
  calc Real.log (A * n + 1) ≤ Real.log ((A + 1) * n) :=
        Real.log_le_log (by positivity) (by nlinarith)
    _ = Real.log (A + 1) + Real.log n := Real.log_mul (by positivity) (by positivity)
    _ ≤ _ := by linarith

private theorem floor_sq_mul_le {p : ℝ} (n : ℕ) : ((⌊p ^ 2 * n⌋₊ : ℕ) : ℝ) ≤ p ^ 2 * n :=
    Nat.floor_le (by positivity)

/-- `√⌊p² n⌋ ≤ p √n` for `p ≥ 0`. -/
theorem sqrt_floor_le {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    Real.sqrt (⌊p ^ 2 * n⌋₊ : ℕ) ≤ p * Real.sqrt n := by
  rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact floor_sq_mul_le n

/-- If `log P(E) ≥ (c - ε) √E` for all large `E`, then the states of energy at most `⌊p² n⌋`
satisfy `log P(⌊p² n⌋) - 2 log (⌊p² n⌋ + 1) ≥ c p √n - η √n` for all large `n`. -/
theorem eventually_le_logLowStates_floor {c : ℝ} (hc : 0 < c)
    (hl : ∀ ε > 0, ∃ E₀ : ℕ, ∀ E, E₀ ≤ E → (c - ε) * Real.sqrt E ≤ logLowStates E)
        {p : ℝ} (hp : 0 ≤ p)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, c * p * Real.sqrt n - η * Real.sqrt n ≤
      logLowStates ⌊p ^ 2 * n⌋₊ - 2 * Real.log ((⌊p ^ 2 * n⌋₊ : ℕ) + 1) := by
  rcases hp.eq_or_lt with rfl | hp
  · refine Eventually.of_forall fun n => ?_
    have : 0 ≤ η * Real.sqrt n := by positivity
    simp [logLowStates_zero, this]
  set ε : ℝ := min (η / (4 * (p + 1))) c with hε
  have hε0 : 0 < ε := lt_min (by positivity) hc
  have hεc : ε ≤ c := min_le_right _ _
  have hεp : ε * p ≤ η / 4 := by
    have h1 : ε ≤ η / (4 * (p + 1)) := min_le_left _ _
    calc ε * p ≤ η / (4 * (p + 1)) * p := mul_le_mul_of_nonneg_right h1 hp.le
      _ ≤ η / (4 * (p + 1)) * (p + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = η / 4 := by field_simp
  obtain ⟨E₀, hE₀⟩ := hl ε hε0
  have a1 := eventually_log_le_mul_sqrt (A := p ^ 2) (by positivity) (η := η / 8) (by positivity)
  have hsq := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have a2 : ∀ᶠ n : ℕ in atTop, 1 / p ≤ Real.sqrt n := hsq.eventually_ge_atTop _
  have a3 : ∀ᶠ n : ℕ in atTop, c / (η / 4) ≤ Real.sqrt n := hsq.eventually_ge_atTop _
  have a4 : ∀ᶠ n : ℕ in atTop, (E₀ : ℝ) / p ^ 2 ≤ n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  filter_upwards [a1, a2, a3, a4] with n a1 a2 a3 a4
  set E := ⌊p ^ 2 * n⌋₊ with hE
  have hp2 : 0 < p ^ 2 := by positivity
  rw [div_le_iff₀ hp] at a2
  rw [div_le_iff₀ (by positivity)] at a3
  rw [div_le_iff₀ hp2] at a4
  have b2 := hE₀ E (Nat.le_floor (by linarith))
  have b3 : p ^ 2 * n - 1 ≤ E := by
    have := Nat.lt_floor_add_one (p ^ 2 * (n : ℝ))
    linarith
  have b4 : p * Real.sqrt n - 1 ≤ Real.sqrt E := by
    refine Real.le_sqrt_of_sq_le ?_
    have : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
    nlinarith
  have b5 : Real.log ((E : ℝ) + 1) ≤ η / 8 * Real.sqrt n :=
    (Real.log_le_log (by positivity) (by linarith [floor_sq_mul_le (p := p) n])).trans a1
  nlinarith [Real.sqrt_nonneg n]

end Cslib.Circuits.Arithmetic.Separation.Curvature
