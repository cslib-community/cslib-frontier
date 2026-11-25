/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.SliceSelfImprovement
import CslibFrontier.Foundations.Data.Finset.Holder
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Error budget for the low-individual-degree induction

The one-step pasting bound has a term proportional to the mean input error,
an exponential term from sampling, and additive terms depending on the ambient
verifier. This module bounds the additive terms by one common fractional power.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Finset
open scoped BigOperators Real

/-- Sum of the fractional powers of the three branch losses and the degree-to-field-size ratio. -/
@[expose] noncomputable def inductionLossTerm (ε δ γ r : ℝ) : ℝ :=
  ε ^ (1 / 128 : ℝ) + δ ^ (1 / 128 : ℝ) + γ ^ (1 / 128 : ℝ) + r ^ (1 / 128 : ℝ)

private theorem inductionLossTerm_nonneg {ε δ γ r : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hr : 0 ≤ r) :
    0 ≤ inductionLossTerm ε δ γ r := by
  unfold inductionLossTerm
  positivity

private theorem rpow_le_fourth_power {x t : ℝ} (hx : 0 ≤ x)
    (h : x ^ (1 / 128 : ℝ) ≤ t) : x ^ (1 / 32 : ℝ) ≤ t ^ 4 := by
  rw [show (1 / 32 : ℝ) = (1 / 128) * 4 by norm_num, Real.rpow_mul hx, ←
    Real.rpow_natCast _ 4]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hx _) h (by norm_num)

private theorem sqrt_le_scaled_power {x m t : ℝ} {j : ℕ} {a b : ℝ}
    (hm : 1 ≤ m) (ht : 0 ≤ t) (hb : 0 ≤ b) (hab : a ≤ b ^ 2)
    (hx : x ≤ a * m * t ^ (2 * j)) :
    √x ≤ b * m * t ^ j := by
  have hm₀ : 0 ≤ m := by linarith
  rw [Real.sqrt_le_left (by positivity)]
  calc
    x ≤ a * m * t ^ (2 * j) := hx
    _ ≤ b ^ 2 * m ^ 2 * t ^ (2 * j) := by
      gcongr
      nlinarith only [mul_nonneg hm₀ (sub_nonneg.mpr hm)]
    _ = _ := by rw [Nat.mul_comm, pow_mul]; ring

/-- The additive pasting terms are controlled uniformly for positive degree. -/
theorem slicePastingError_le (m : ℝ) (k : ℕ) (q ε δ γ r σ θ : ℝ)
    (hm : 1 ≤ m) (hk : 0 < k) (hq : 0 < q) (hrq : 1 / q ≤ r)
    (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hθ : θ ≤ 1 / 2) :
    slicePastingError m k q ε δ γ r σ θ ≤
      σ / (1 - θ) + Real.exp (-(θ ^ 2 * k) / 2) +
        100000 * (k : ℝ) ^ 2 * m * inductionLossTerm ε δ γ r := by
  let s := max (max ε δ) (max γ r)
  have hs : s ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hε.1.trans ((le_max_left ε δ).trans (le_max_left _ _)),
      max_le (max_le hε.2 hδ.2) (max_le hγ.2 hr.2)⟩
  let t := s ^ (1 / 128 : ℝ)
  have ht₀ : 0 ≤ t := Real.rpow_nonneg hs.1 _
  have ht₁ : t ≤ 1 := Real.rpow_le_one hs.1 hs.2 (by norm_num)
  have hεs : ε ≤ s := (le_max_left _ _).trans (le_max_left _ _)
  have hδs : δ ≤ s := (le_max_right _ _).trans (le_max_left _ _)
  have hγs : γ ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  have hrs : r ≤ s := (le_max_right _ _).trans (le_max_right _ _)
  have hs_pow : s = t ^ 128 := by
    dsimp only [t]
    rw [← Real.rpow_natCast _ 128, ← Real.rpow_mul hs.1]
    norm_num
  have hpow (a b : ℕ) (h : a ≤ b) : t ^ b ≤ t ^ a :=
    pow_le_pow_of_le_one ht₀ ht₁ h
  have hsum : t ≤ inductionLossTerm ε δ γ r := by
    dsimp only [t, s, inductionLossTerm]
    simp only [Real.rpow_max hε.1 hδ.1 (by norm_num : 0 ≤ (1 / 128 : ℝ)),
      Real.rpow_max hγ.1 hr.1 (by norm_num : 0 ≤ (1 / 128 : ℝ)),
      Real.rpow_max (le_max_of_le_left hε.1) (le_max_of_le_left hγ.1)
        (by norm_num : 0 ≤ (1 / 128 : ℝ))]
    have h₁ := Real.rpow_nonneg hε.1 (1 / 128 : ℝ)
    have h₂ := Real.rpow_nonneg hδ.1 (1 / 128 : ℝ)
    have h₃ := Real.rpow_nonneg hγ.1 (1 / 128 : ℝ)
    have h₄ := Real.rpow_nonneg hr.1 (1 / 128 : ℝ)
    exact max_le (max_le (by linarith) (by linarith)) (max_le (by linarith) (by linarith))
  let ζ := 3000 * m * (ε ^ (1 / 32 : ℝ) + δ ^ (1 / 32 : ℝ) + r ^ (1 / 32 : ℝ))
  let v := √(8 * m * ε + 4 * δ)
  let c := 32 * (4 * √(2 * ζ) + 2 * √(64 * m * γ) + 2 * √ζ + 2 * √ζ) +
    30 * ζ + 20 * ((m - 1) * r)
  let e := √(162 * c + 176 * ζ)
  have hm₀ : 0 ≤ m := by linarith
  have hζ₀ : 0 ≤ ζ :=
    mul_nonneg (mul_nonneg (by norm_num) hm₀)
      (add_nonneg (add_nonneg (Real.rpow_nonneg hε.1 _) (Real.rpow_nonneg hδ.1 _))
        (Real.rpow_nonneg hr.1 _))
  have hz4 : ζ ≤ 9000 * m * t ^ 4 := by
    have h₁ := rpow_le_fourth_power hε.1 (Real.rpow_le_rpow hε.1 hεs (by norm_num))
    have h₂ := rpow_le_fourth_power hδ.1 (Real.rpow_le_rpow hδ.1 hδs (by norm_num))
    have h₃ := rpow_le_fourth_power hr.1 (Real.rpow_le_rpow hr.1 hrs (by norm_num))
    dsimp only [ζ]
    linarith only [mul_le_mul_of_nonneg_left (add_le_add (add_le_add h₁ h₂) h₃) hm₀]
  have hs4 : s ≤ t ^ 4 := hs_pow.trans_le (hpow 4 128 (by norm_num))
  have hm2 : 0 ≤ m - 1 := by linarith
  have hqterm : (m - 1) * r ≤ m * t ^ 4 :=
    mul_le_mul (by linarith : m - 1 ≤ m) (hrs.trans hs4) hr.1 hm₀
  have hsqrtZ : √ζ ≤ 100 * m * t ^ 2 :=
    sqrt_le_scaled_power hm ht₀ (by norm_num) (by norm_num) hz4
  have hsqrt2Z : √(2 * ζ) ≤ 140 * m * t ^ 2 := by
    apply sqrt_le_scaled_power (a := 18000) hm ht₀ (by norm_num) (by norm_num)
    norm_num
    linarith only [hz4]
  have hγsqrt : √(64 * m * γ) ≤ 8 * m * t ^ 2 := by
    apply sqrt_le_scaled_power (a := 64) hm ht₀ (by norm_num) (by norm_num)
    gcongr
    exact hγs.trans hs4
  have hv : v ≤ 4 * m * t ^ 2 := by
    apply sqrt_le_scaled_power (a := 12) hm ht₀ (by norm_num) (by norm_num)
    have h₁ := mul_le_mul_of_nonneg_left (hεs.trans hs4) hm₀
    have h₂ := mul_le_mul_of_nonneg_left (hδs.trans hs4) hm₀
    have h₃ := le_mul_of_one_le_left (pow_nonneg ht₀ 4) hm
    norm_num
    linarith only [h₁, (hδs.trans hs4).trans h₃]
  have hmt (a b : ℕ) (h : a ≤ b) : m * t ^ b ≤ m * t ^ a :=
    mul_le_mul_of_nonneg_left (hpow a b h) hm₀
  have hc : c ≤ 310000 * m * t ^ 2 := by
    dsimp only [c]
    linarith only [hsqrt2Z, hγsqrt, hsqrtZ, hz4, hqterm, hmt 2 4 (by norm_num),
      show 0 ≤ m * t ^ 2 by positivity]
  have he : e ≤ 8000 * m * t := by
    dsimp only [e]
    rw [← pow_one t]
    apply sqrt_le_scaled_power (a := 52000000) (j := 1) hm ht₀ (by norm_num) (by norm_num)
    norm_num
    linarith only [hc, hz4, hmt 2 4 (by norm_num), show 0 ≤ m * t ^ 2 by positivity]
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk₀ : (0 : ℝ) ≤ k := by positivity
  have hk₂ : (k : ℝ) ≤ (k : ℝ) ^ 2 := le_self_pow₀ hk₁ two_ne_zero
  have hk₂₁ : (1 : ℝ) ≤ (k : ℝ) ^ 2 := hk₁.trans hk₂
  have hk₃ : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hzθ : ζ / (1 - θ) ≤ 18000 * m * t := by
    have hp : 0 < 1 - θ := by linarith
    rw [div_le_iff₀ hp]
    have h := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ 1 - θ by linarith)
      (show 0 ≤ 18000 * m * t by positivity)
    linarith only [h, hz4, hmt 1 4 (by norm_num)]
  have hchoose : ((k.choose 2 : ℝ) / q) ≤ (k : ℝ) ^ 2 * m * t := by
    have h : (k.choose 2 : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast Nat.choose_le_pow k 2
    have hqt : 1 / q ≤ m * t :=
      hrq.trans ((hrs.trans (hs_pow.trans_le (hpow 1 128 (by norm_num)))).trans
        (by simpa only [pow_one] using le_mul_of_one_le_left ht₀ hm))
    rw [mul_assoc, div_eq_mul_one_div]
    gcongr
  have hsqrt2 : √(2 : ℝ) ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hz' : ζ ≤ 9000 * m * t := by
    linarith only [hz4, hmt 1 4 (by norm_num)]
  have hv' : v ≤ 4 * m * t := by
    linarith only [hv, hmt 1 2 (by norm_num)]
  have hq' : (m - 1) * r ≤ m * t := by
    linarith only [hqterm, hmt 1 4 (by norm_num)]
  have hsz' : √(2 * ζ) ≤ 140 * m * t := by
    linarith only [hsqrt2Z, hmt 1 2 (by norm_num)]
  suffices h :
      slicePastingError m k q ε δ γ r σ θ ≤
        σ / (1 - θ) + Real.exp (-(θ ^ 2 * k) / 2) + 100000 * (k : ℝ) ^ 2 * m * t by
    exact h.trans (by gcongr)
  change ((σ + ζ) / (1 - θ) + Real.exp (-(θ ^ 2 * k) / 2) +
      (1 + √2) * (k * √(2 * ζ) + (k : ℝ) ^ 2 * e) +
      3 * ((k.choose 2 : ℝ) / q) + (m - 1) * r + 2 * k * ζ + (2 * k + 1 : ℝ) * v +
      2 * k * ((k - 1 : ℕ) : ℝ) * e) ≤ _
  rw [add_div]
  calc
    _ ≤ σ / (1 - θ) + 18000 * m * t + Real.exp (-(θ ^ 2 * k) / 2) +
        3 * ((k : ℝ) ^ 2 * (140 * m * t) + (k : ℝ) ^ 2 * (8000 * m * t)) +
        3 * ((k : ℝ) ^ 2 * m * t) + m * t + 2 * (k : ℝ) ^ 2 * (9000 * m * t) +
        (3 * (k : ℝ) ^ 2) * (4 * m * t) + 2 * k * k * (8000 * m * t) := by
      gcongr
      · linarith only [hsqrt2]
      · linarith only [hk₂₁, hk₂]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (k : ℝ) ^ 2 by linarith)
        (show 0 ≤ m * t by positivity)
      nlinarith only [h, show 0 ≤ (k : ℝ) ^ 2 * m * t by positivity]

/-- A closed error bound for the induction in dimension `m`. -/
@[expose] noncomputable def dimensionInductionError
    (m : ℝ) (k : ℕ) (ε δ γ r : ℝ) : ℝ :=
  m ^ 2 * (100000 * (k : ℝ) ^ 2 * m * inductionLossTerm ε δ γ r +
    Real.exp (-(k : ℝ) / (80000 * m ^ 2)))

/-- The induction budget covers the errors in the one-coordinate and degree-zero cases. -/
theorem baseError_le_dimensionInductionError {m ε δ γ r : ℝ} {k : ℕ}
    (hm : 1 ≤ m) (hk : 0 < k) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (hγ : 0 ≤ γ) (hr : 0 ≤ r) :
    8 * m * ε + 2 * δ ≤ dimensionInductionError m k ε δ γ r := by
  let R := inductionLossTerm ε δ γ r
  have hsmall {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : x ≤ x ^ (1 / 128 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge' hx.1 hx.2
        (by norm_num : 0 ≤ (1 / 128 : ℝ)) (by norm_num : (1 / 128 : ℝ) ≤ 1)
  have hp₁ := Real.rpow_nonneg hε.1 (1 / 128 : ℝ)
  have hp₂ := Real.rpow_nonneg hδ.1 (1 / 128 : ℝ)
  have hp₃ := Real.rpow_nonneg hγ (1 / 128 : ℝ)
  have hp₄ := Real.rpow_nonneg hr (1 / 128 : ℝ)
  have he : ε ≤ R := by dsimp only [R, inductionLossTerm]; linarith only [hsmall hε, hp₂, hp₃, hp₄]
  have hd : δ ≤ R := by dsimp only [R, inductionLossTerm]; linarith only [hsmall hδ, hp₁, hp₃, hp₄]
  have hR : 0 ≤ R := hε.1.trans he
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcoeff : 8 * m + 2 ≤ m ^ 2 * (100000 * (k : ℝ) ^ 2 * m) := by
    calc
      _ ≤ 100000 * (k : ℝ) ^ 2 * m := by nlinarith only [one_le_pow₀ hk₁ (n := 2), hm]
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hm)
  change _ ≤ m ^ 2 * (100000 * (k : ℝ) ^ 2 * m * R + _)
  nlinarith only [mul_le_mul_of_nonneg_right hcoeff hR,
    mul_le_mul_of_nonneg_left he (show 0 ≤ 8 * m by positivity),
    mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 2),
    mul_nonneg (sq_nonneg m) (Real.exp_pos (-(k : ℝ) / (80000 * m ^ 2))).le]

/-- The factor from averaging restricted losses is absorbed by the ambient dimension. -/
theorem mul_expect_inductionLossTerm_le {X : Type*} [Fintype X] [Nonempty X]
    {m M ε δ γ r : ℝ} {e f g : X → ℝ}
    (hm : 0 < m) (hmM : m ≤ M) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hr : 0 ≤ r)
    (he : ∀ x, 0 ≤ e x) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (h₁ : m * (𝔼 x, e x) ≤ M * ε) (h₂ : 𝔼 x, f x ≤ δ)
    (h₃ : m * (𝔼 x, g x) ≤ M * γ) :
    m * (𝔼 x, inductionLossTerm (e x) (f x) (g x) r) ≤
      M * inductionLossTerm ε δ γ r := by
  have hδ' : m * (𝔼 x, f x) ≤ M * δ :=
    (mul_le_mul_of_nonneg_left h₂ hm.le).trans (mul_le_mul_of_nonneg_right hmM hδ)
  have he' := Fintype.mul_expect_rpow_le_of_mul_expect_le he hm hmM hε
    (p := 1 / 128) (by norm_num) (by norm_num) h₁
  have hf' := Fintype.mul_expect_rpow_le_of_mul_expect_le hf hm hmM hδ
    (p := 1 / 128) (by norm_num) (by norm_num) hδ'
  have hg' := Fintype.mul_expect_rpow_le_of_mul_expect_le hg hm hmM hγ
    (p := 1 / 128) (by norm_num) (by norm_num) h₃
  have hr' := mul_le_mul_of_nonneg_right hmM (Real.rpow_nonneg hr (1 / 128 : ℝ))
  simp only [inductionLossTerm, expect_add_distrib, Fintype.expect_const]
  linarith only [he', hf', hg', hr']

/-- One recurrence step with the pasting threshold chosen for the ambient dimension. -/
theorem slicePastingError_le_dimensionInductionError {m q ε δ γ r σ : ℝ} {k : ℕ}
    (hm : 1 ≤ m) (hk : 0 < k) (hq : 0 < q) (hrq : 1 / q ≤ r)
    (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hσ : σ ≤ m ^ 2 * (100000 * (k : ℝ) ^ 2 * (m + 1) * inductionLossTerm ε δ γ r +
      Real.exp (-(k : ℝ) / (80000 * m ^ 2)))) :
    slicePastingError (m + 1) k q ε δ γ r σ (1 / (200 * (m + 1))) ≤
      dimensionInductionError (m + 1) k ε δ γ r := by
  let M := m + 1
  let θ : ℝ := 1 / (200 * M)
  let b := 100000 * (k : ℝ) ^ 2 * M * inductionLossTerm ε δ γ r
  let E := Real.exp (-(k : ℝ) / (80000 * M ^ 2))
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hM₀ : 0 < M := by linarith
  have hθM : θ * M = 1 / 200 := by dsimp only [θ]; field_simp
  have hθ : θ ≤ 1 / 2 := by dsimp only [θ]; rw [div_le_iff₀ (by positivity)]; linarith
  have hθ' : 0 < 1 - θ := by linarith
  have hsampling : Real.exp (-(θ ^ 2 * k) / 2) = E := by
    unfold θ E
    congr 1
    field_simp
    ring
  have hb : 0 ≤ b :=
    mul_nonneg (mul_nonneg (by positivity) hM₀.le)
      (inductionLossTerm_nonneg hε.1 hδ.1 hγ.1 hr.1)
  have hE : Real.exp (-(k : ℝ) / (80000 * m ^ 2)) ≤ E := by
    dsimp only [E, M]; rw [neg_div, neg_div]; gcongr; linarith
  have hσ' : σ ≤ m ^ 2 * (b + E) :=
    hσ.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl b) hE) (sq_nonneg m))
  have hscale : m ^ 2 / (1 - θ) + 1 ≤ M ^ 2 := by
    have h : m ^ 2 / (1 - θ) ≤ m * M := by
      rw [div_le_iff₀ hθ', mul_sub, mul_one, mul_assoc m M θ, mul_comm M θ, hθM]
      dsimp only [M]
      linarith only [hm]
    dsimp only [M] at h ⊢
    linarith only [h, hm]
  change slicePastingError M k q ε δ γ r σ θ ≤ M ^ 2 * (b + E)
  calc
    _ ≤ σ / (1 - θ) + Real.exp (-(θ ^ 2 * k) / 2) + b :=
      slicePastingError_le M k q ε δ γ r σ θ hM hk hq hrq hε hδ hγ hr hθ
    _ ≤ (m ^ 2 / (1 - θ) + 1) * (b + E) := by
      rw [hsampling]
      have hh := div_le_div_of_nonneg_right hσ' hθ'.le
      rw [mul_div_right_comm] at hh
      linarith only [hh]
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale (add_nonneg hb (Real.exp_pos _).le)

/-- Increasing the sample count by at most a factor of 400 increases the
induction bound by at most the square of that factor. -/
theorem dimensionInductionError_pad {m ε δ γ r : ℝ} {k K : ℕ}
    (hm : 0 ≤ m) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hr : 0 ≤ r)
    (hk : k ≤ K) (hK : K ≤ 400 * k) :
    dimensionInductionError m K ε δ γ r ≤ 160000 * dimensionInductionError m k ε δ γ r := by
  have hk' : (k : ℝ) ≤ K := by exact_mod_cast hk
  have hK' : (K : ℝ) ≤ 400 * (k : ℝ) := by exact_mod_cast hK
  have hs : (K : ℝ) ^ 2 ≤ 160000 * (k : ℝ) ^ 2 :=
    (pow_le_pow_left₀ (by positivity) hK' 2).trans_eq (by ring)
  have he : Real.exp (-(K : ℝ) / (80000 * m ^ 2)) ≤
      Real.exp (-(k : ℝ) / (80000 * m ^ 2)) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hk') (by positivity))
  let R := inductionLossTerm ε δ γ r
  have hR : 0 ≤ R := inductionLossTerm_nonneg hε hδ hγ hr
  have hpoly := mul_le_mul_of_nonneg_right hs (show 0 ≤ 100000 * m * R by positivity)
  change m ^ 2 * (100000 * (K : ℝ) ^ 2 * m * R + _) ≤
    160000 * (m ^ 2 * (100000 * (k : ℝ) ^ 2 * m * R + _))
  rw [mul_left_comm (160000 : ℝ)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg m)
  linarith only [hpoly, he, Real.exp_pos (-(k : ℝ) / (80000 * m ^ 2))]

/-- If the field is too small for the padded sample count, the degree ratio
already makes the stated error bound at least one. -/
theorem one_le_dimensionInductionError_of_large_ratio {m ε δ γ r : ℝ} {k : ℕ}
    (hm : 1 ≤ m) (hk : 0 < k) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hr : 1 / (400 * (k : ℝ)) ≤ r) :
    1 ≤ dimensionInductionError m k ε δ γ r := by
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq₀ : (0 : ℝ) < 400 * (k : ℝ) := by linarith
  have h₀ : 0 ≤ 1 / (400 * (k : ℝ)) := by positivity
  have hsmall : 1 / (400 * (k : ℝ)) ≤ r ^ (1 / 128 : ℝ) := by
    refine le_trans ?_ (Real.rpow_le_rpow h₀ hr (by norm_num))
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge' h₀ ((div_le_one hq₀).2 (by linarith))
        (by norm_num : 0 ≤ (1 / 128 : ℝ))
        (by norm_num : (1 / 128 : ℝ) ≤ 1)
  let R := inductionLossTerm ε δ γ r
  have hR : 1 / (400 * (k : ℝ)) ≤ R := by
    dsimp only [R, inductionLossTerm]
    linarith only [hsmall, Real.rpow_nonneg hε (1 / 128 : ℝ),
      Real.rpow_nonneg hδ (1 / 128 : ℝ), Real.rpow_nonneg hγ (1 / 128 : ℝ)]
  have hkR : (1 : ℝ) ≤ 400 * (k : ℝ) * R := (div_le_iff₀' hq₀).mp hR
  have hR₀ : 0 ≤ R := h₀.trans hR
  calc
    _ ≤ 400 * (k : ℝ) * R := hkR
    _ ≤ 100000 * (k : ℝ) ^ 2 * m * R := by
      apply mul_le_mul_of_nonneg_right _ hR₀
      nlinarith only [le_self_pow₀ hk₁ two_ne_zero, le_mul_of_one_le_right (sq_nonneg (k : ℝ)) hm,
        hk₁]
    _ ≤ 100000 * (k : ℝ) ^ 2 * m * R + Real.exp (-(k : ℝ) / (80000 * m ^ 2)) :=
      le_add_of_nonneg_right (Real.exp_pos _).le
    _ ≤ dimensionInductionError m k ε δ γ r :=
      le_mul_of_one_le_left (by positivity) (one_le_pow₀ hm)

end Cslib.PCP.LowIndividualDegree
