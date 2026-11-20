/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to Cslib/Crypto/Game.lean)

public import CslibFrontier.Crypto.Game
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.ToReal

/-!
# Comparing success probabilities

A bound on the mass of `true` in one experiment transfers to its success probability, without
unfolding `succProbability` or discharging the finiteness of a probability mass by hand. A bound on
the distinguishing advantage of two experiments bounds one success probability by the other.

## Main results

* `Cslib.Crypto.Game.succProbability_mono`: success probability is monotone in the mass of
  `true`.
* `Cslib.Crypto.Game.succProbability_le_add_of_advantage_le`,
  `Cslib.Crypto.Game.coe_succProbability_le_add_of_advantage_le`: bound a game's success probability
  by another game's success probability plus their distinguishing advantage.
* `Cslib.Crypto.Game.apply_true_le_of_advantage_le`: an `ℝ≥0` advantage bound between two games
  implies mutual `ℝ≥0∞` upper bounds on their acceptance probabilities.
* `Cslib.Crypto.Game.sq_sub_mul_le_bind`: pointwise quadratic bounds
  `ε(a) ^ 2 - κ * ε(a) ≤ ε'(a)` survive averaging over `a ← ν` by Jensen's inequality.
-/

public section

namespace Cslib.Crypto.Game

open scoped ENNReal NNReal

/-- Success probability is monotone in the mass of `true`. -/
theorem succProbability_mono {g₁ g₂ : Game} (h : g₁ true ≤ g₂ true) :
    g₁.succProbability ≤ g₂.succProbability :=
  ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) h

/-- Bounding `advantage g₀ g₁ ≤ B` bounds `succProbability g₀ ≤ succProbability g₁ + B`. -/
theorem succProbability_le_add_of_advantage_le {g₀ g₁ : Game} {B : ℝ≥0}
    (h : advantage g₀ g₁ ≤ B) :
    succProbability g₀ ≤ succProbability g₁ + B := by
  have htri := advantage_triangle g₀ g₁ (PMF.pure false)
  rw [advantage_pure_false, advantage_pure_false, add_comm] at htri
  exact htri.trans (add_le_add le_rfl h)

/-- Real-valued version of `succProbability_le_add_of_advantage_le`. -/
theorem coe_succProbability_le_add_of_advantage_le {g₀ g₁ : Game} {B : ℝ}
    (h : (advantage g₀ g₁ : ℝ) ≤ B) :
    (succProbability g₀ : ℝ) ≤ (succProbability g₁ : ℝ) + B := by
  have htri := NNReal.coe_le_coe.mpr
    (succProbability_le_add_of_advantage_le (g₀ := g₀) (g₁ := g₁) le_rfl)
  rw [NNReal.coe_add] at htri
  exact htri.trans (add_le_add le_rfl h)

/-- An `ℝ≥0` advantage bound between two games implies mutual `ℝ≥0∞` upper bounds on their
acceptance probabilities. -/
theorem apply_true_le_of_advantage_le {g₁ g₂ : Game} {c : ℝ≥0}
    (h : advantage g₁ g₂ ≤ c) :
    g₁ true ≤ g₂ true + (c : ℝ≥0∞) ∧ g₂ true ≤ g₁ true + (c : ℝ≥0∞) := by
  have hle {a b : Game} (hab : advantage a b ≤ c) : a true ≤ b true + (c : ℝ≥0∞) := by
    have hsucc := ENNReal.coe_le_coe.mpr (succProbability_le_add_of_advantage_le hab)
    rwa [ENNReal.coe_add, ENNReal.coe_toNNReal (PMF.apply_ne_top a true),
      ENNReal.coe_toNNReal (PMF.apply_ne_top b true)] at hsucc
  exact ⟨hle h, hle (advantage_comm g₂ g₁ ▸ h)⟩

/-- Pointwise quadratic bounds `ε(a) ^ 2 - κ * ε(a) ≤ ε'(a)` on game success probabilities survive
averaging over `a ← ν` by Jensen's inequality (`Probability.PMF.sq_tsum_le_tsum_sq`). -/
theorem sq_sub_mul_le_bind {α : Type*} (ν : PMF α) (G H : α → Game) {κ : ℝ}
    (h : ∀ a ∈ ν.support,
      (succProbability (G a) : ℝ) ^ 2 - κ * succProbability (G a) ≤ succProbability (H a)) :
    (succProbability (ν.bind G) : ℝ) ^ 2 - κ * succProbability (ν.bind G) ≤
      succProbability (ν.bind H) := by
  simp only [succProbability, ENNReal.coe_toNNReal_eq_toReal] at h ⊢
  set g : α → ℝ := fun a => (G a true).toReal
  set f : α → ℝ := fun a => (H a true).toReal
  have hg0 (a : α) : 0 ≤ g a := ENNReal.toReal_nonneg
  have hg1 (a : α) : g a ≤ 1 := Probability.PMF.toReal_apply_le_one (G a) true
  have hf0 (a : α) : 0 ≤ f a := ENNReal.toReal_nonneg
  have hf1 (a : α) : f a ≤ 1 := Probability.PMF.toReal_apply_le_one (H a) true
  have hm : Summable fun a => (ν a).toReal := Probability.PMF.summable_toReal ν
  have hsum {k : α → ℝ} (k0 : ∀ a, 0 ≤ k a) (k1 : ∀ a, k a ≤ 1) :
      Summable fun a => (ν a).toReal * k a :=
    hm.of_nonneg_of_le (fun a => mul_nonneg ENNReal.toReal_nonneg (k0 a))
      fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (k1 a)
  have hsumg := hsum hg0 hg1
  have hsumg2 := hsum (fun a => sq_nonneg (g a)) fun a => pow_le_one₀ (hg0 a) (hg1 a)
  have hsumf := hsum hf0 hf1
  have hpoint (a : α) :
      (ν a).toReal * g a ^ 2 - κ * ((ν a).toReal * g a) ≤ (ν a).toReal * f a := by
    by_cases ha : a ∈ ν.support
    · calc _ = (ν a).toReal * (g a ^ 2 - κ * g a) := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg
    · simp [(PMF.apply_eq_zero_iff ν a).mpr ha]
  rw [Probability.PMF.bind_apply_toReal_tsum, Probability.PMF.bind_apply_toReal_tsum]
  calc (∑' a, (ν a).toReal * g a) ^ 2 - κ * (∑' a, (ν a).toReal * g a)
      ≤ ∑' a, (ν a).toReal * g a ^ 2 - κ * (∑' a, (ν a).toReal * g a) := by
        gcongr
        exact Probability.PMF.sq_tsum_le_tsum_sq ν hg0 hg1
    _ = ∑' a, ((ν a).toReal * g a ^ 2 - κ * ((ν a).toReal * g a)) := by
        rw [hsumg2.tsum_sub (hsumg.mul_left κ), tsum_mul_left]
    _ ≤ ∑' a, (ν a).toReal * f a :=
        (hsumg2.sub (hsumg.mul_left κ)).tsum_le_tsum hpoint hsumf

end Cslib.Crypto.Game
