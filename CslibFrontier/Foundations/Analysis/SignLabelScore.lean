/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, sign approximation)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Sign.Basic
import Mathlib.Tactic.Linarith

/-!
# Squared-error scores for finite sign tests

Approximate values within `1 / (4 * (m + 1))` of their true signs give a score
separated from zero by at least one half. The score is positive exactly when
all `m` target signs agree with the true signs. The empty family is included.

For weighted signs, a separate score tests equality with the integer fingerprint and
positivity of a qualifying test. Its tolerance is `1 / (4 * (M + 1))` for total weight at
most `M`, and `1 / 4` for the qualifying test.

Adapted from `RootLabelScore` and `RationalSignMargin` in lean-canny at commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. The larger tolerance still gives
the same score margin and permits fewer repetitions of the dyadic product.
The weighted score adapts `FingerprintLabelScore` at the same commit.
-/

public section

namespace SignType

/-- Subtract four times the total squared distance from the target signs from one. -/
@[expose] noncomputable def labelScore {m : ℕ} (a : Fin m → ℝ) (target : Fin m → SignType) : ℝ :=
  1 - 4 * ∑ i, (a i - (target i : ℝ)) ^ 2

private theorem one_le_abs_sub_of_ne (s t : SignType) (h : s ≠ t) :
    (1 : ℝ) ≤ |(s : ℝ) - (t : ℝ)| := by
  cases s <;> cases t <;> norm_num at *

private theorem mul_inv_four_mul_succ_le (m : ℕ) :
    (m : ℝ) * (4 * ((m : ℝ) + 1))⁻¹ ≤ 1 / 4 := by
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  linarith

private theorem three_quarters_sq_le_sq_sub {a actual target : ℝ}
    (ha : |a - actual| ≤ (1 : ℝ) / 4) (hgap : 1 ≤ |actual - target|) :
    ((3 : ℝ) / 4) ^ 2 ≤ (a - target) ^ 2 := by
  have htri := abs_sub_le actual a target
  rw [abs_sub_comm actual a] at htri
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (show (3 : ℝ) / 4 ≤ |a - target| by linarith) 2
  rwa [sq_abs] at h

/-- With uniformly accurate approximations, the score is at least one half
on agreement and at most minus one half on mismatch. Its sign characterizes agreement. -/
theorem labelScore_margin {m : ℕ} (a : Fin m → ℝ) (s target : Fin m → SignType)
    (ha : ∀ i, |a i - (s i : ℝ)| ≤ (4 * ((m : ℝ) + 1))⁻¹) :
    ((1 : ℝ) / 2 ≤ labelScore a target ∨ labelScore a target ≤ -(1 : ℝ) / 2) ∧
      (0 < labelScore a target ↔ ∀ i, s i = target i) := by
  let δ : ℝ := (4 * ((m : ℝ) + 1))⁻¹
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hm : 0 ≤ (m : ℝ) := by positivity
  have hδ₁ : δ ≤ (1 : ℝ) / 4 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) (show (4 : ℝ) ≤ 4 * ((m : ℝ) + 1) by linarith)
  by_cases hmatch : ∀ i, s i = target i
  · have hmul : (m : ℝ) * δ ≤ (1 : ℝ) / 4 := mul_inv_four_mul_succ_le m
    have hsum : (∑ i, (a i - (target i : ℝ)) ^ 2) ≤ (1 : ℝ) / 16 := by
      calc
        _ ≤ ∑ _i : Fin m, δ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hi := pow_le_pow_left₀ (abs_nonneg _) (ha i) 2
          simpa only [hmatch i, sq_abs, δ] using hi
        _ = ((m : ℝ) * δ) * δ := by simp [pow_two, mul_assoc]
        _ ≤ (1 : ℝ) / 4 * (1 / 4) := mul_le_mul hmul hδ₁ hδ (by norm_num)
        _ = _ := by norm_num
    have hscore : (1 : ℝ) / 2 ≤ labelScore a target := by
      unfold labelScore
      linarith
    exact ⟨Or.inl hscore, ⟨fun _ => hmatch, fun _ => by linarith⟩⟩
  · obtain ⟨i, hi⟩ := not_forall.mp hmatch
    have hsq := three_quarters_sq_le_sq_sub ((ha i).trans hδ₁)
      (one_le_abs_sub_of_ne (s i) (target i) hi)
    have hsum : (a i - (target i : ℝ)) ^ 2 ≤ ∑ j, (a j - (target j : ℝ)) ^ 2 :=
      Finset.single_le_sum (f := fun j : Fin m => (a j - (target j : ℝ)) ^ 2)
        (fun j _ => sq_nonneg (a j - (target j : ℝ))) (Finset.mem_univ i)
    have hscore : labelScore a target ≤ -(1 : ℝ) / 2 := by
      unfold labelScore
      linarith
    exact ⟨Or.inr hscore, ⟨fun h => by linarith, fun h => (hmatch h).elim⟩⟩

/-- Subtract four times the squared errors from the integer fingerprint target and the
qualifying target `1`. The inputs are the approximate weighted sum and qualifying sign. -/
@[expose] noncomputable def fingerprintScore (A b : ℝ) (target : ℤ) : ℝ :=
  1 - 4 * ((A - target) ^ 2 + (b - 1) ^ 2)

private theorem abs_weightedSignError_le {m : ℕ} (w : Fin m → ℕ) (a : Fin m → ℝ)
    (s : Fin m → SignType) {M : ℕ} (hw : ∑ i, w i ≤ M)
    (ha : ∀ i, |a i - (s i : ℝ)| ≤ (4 * ((M : ℝ) + 1))⁻¹) :
    |(∑ i, (w i : ℝ) * a i) - ((∑ i, (w i : ℤ) * (s i : ℤ) : ℤ) : ℝ)| ≤
      (1 : ℝ) / 4 := by
  have hweight : (∑ i, (w i : ℝ)) ≤ M := by exact_mod_cast hw
  let δ : ℝ := (4 * ((M : ℝ) + 1))⁻¹
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, SignType.intCast_cast]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(w i : ℝ) * a i - (w i : ℝ) * (s i : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, (w i : ℝ) * |a i - (s i : ℝ)| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ∑ i, (w i : ℝ) * δ :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ha i) (Nat.cast_nonneg _)
    _ = (∑ i, (w i : ℝ)) * δ := (Finset.sum_mul _ _ _).symm
    _ ≤ M * δ := mul_le_mul_of_nonneg_right hweight (by dsimp only [δ]; positivity)
    _ ≤ (1 : ℝ) / 4 := mul_inv_four_mul_succ_le M

/-- With approximations accurate to the total-weight tolerance, the fingerprint score has
margin at least one half. It is positive exactly when the weighted integer signs match
the target and the qualifying sign is positive. -/
theorem fingerprintScore_margin {m : ℕ} (w : Fin m → ℕ) (a : Fin m → ℝ)
    (s : Fin m → SignType) (b : ℝ) (sigma : SignType) (target : ℤ)
    {M : ℕ} (hw : ∑ i, w i ≤ M)
    (ha : ∀ i, |a i - (s i : ℝ)| ≤ (4 * ((M : ℝ) + 1))⁻¹)
    (hb : |b - (sigma : ℝ)| ≤ (1 : ℝ) / 4) :
    let actual := ∑ i, (w i : ℤ) * (s i : ℤ)
    let score := fingerprintScore (∑ i, (w i : ℝ) * a i) b target
    ((1 : ℝ) / 2 ≤ score ∨ score ≤ -(1 : ℝ) / 2) ∧
      (0 < score ↔ actual = target ∧ sigma = 1) := by
  intro actual score
  let A := ∑ i, (w i : ℝ) * a i
  have hA : |A - (actual : ℝ)| ≤ (1 : ℝ) / 4 := abs_weightedSignError_le w a s hw ha
  by_cases hmatch : actual = target ∧ sigma = 1
  · have hAsq := pow_le_pow_left₀ (abs_nonneg _) hA 2
    have hbsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
    simp only [sq_abs, hmatch.1, hmatch.2, SignType.coe_one] at hAsq hbsq
    have hp : (1 : ℝ) / 2 ≤ score := by
      change (1 : ℝ) / 2 ≤ fingerprintScore A b target
      unfold fingerprintScore
      nlinarith
    exact ⟨Or.inl hp, ⟨fun _ => hmatch, fun _ => by linarith⟩⟩
  · have hn : score ≤ -(1 : ℝ) / 2 := by
      change fingerprintScore A b target ≤ -(1 : ℝ) / 2
      unfold fingerprintScore
      by_cases he : actual = target
      · have hgap := one_le_abs_sub_of_ne sigma 1 (fun hs => hmatch ⟨he, hs⟩)
        rw [SignType.coe_one] at hgap
        nlinarith [three_quarters_sq_le_sq_sub hb hgap, sq_nonneg (A - (target : ℝ))]
      · have hgap : (1 : ℝ) ≤ |(actual : ℝ) - (target : ℝ)| := by
          exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr he)
        nlinarith [three_quarters_sq_le_sq_sub hA hgap, sq_nonneg (b - 1)]
    exact ⟨Or.inr hn, ⟨fun hp => by linarith, fun h => (hmatch h).elim⟩⟩

end SignType
