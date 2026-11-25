/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Gaussian
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Verified rational dual-LP certificates for bounded-fan-in hypergraphs

This module constructs six explicit `HyperDualCert` witnesses for bounded-fan-in circuits across
`r ∈ {3, 4, 8, 16, 64}`, combining all four straddling-probability regimes of
`CslibFrontier/Computability/Circuit/Frontier/Compiler/Hypergraph/Gaussian.lean`:

1. `cert_r3_sheppard` (`r = 3`, pure Sheppard + star-cone): `hyperCoeff > 44011 / 10000`, with
   `b < 0` (worst-case, average-case, and nondeterministic).
2. `cert_r3_slepian` (`r = 3`, Slepian + star-cone): `hyperCoeff > 44199 / 10000`, with `b < 0`
   (worst-case, average-case, and nondeterministic).
3. `cert_r4_sheppard` (`r = 4`, Sheppard + star-cone): `hyperCoeff > 44792 / 10000`, with `b < 0`
   (worst-case, average-case, and nondeterministic).
4. `cert_r8_slepian` (`r = 8`, Slepian + star-cone): `hyperCoeff > 46666 / 10000`, with `b = 0`
   (worst-case, average-case, and nondeterministic).
5. `cert_r16_slepian` (`r = 16`, Slepian + star-cone): `hyperCoeff > 49798 / 10000`
   (worst-case and average-case).
6. `cert_r64_slepian` (`r = 64`, Slepian): `hyperCoeff > 60012 / 10000`
   (worst-case and average-case).

Every numerical inequality is proved over `ℚ` and `ℝ` from `Real.cos_bound_ten`, `Real.pi_gt_d20`,
`Real.pi_lt_d20`, and `ProbabilityTheory.equicorrStraddle_le_of_poly` without `native_decide`.

## Main results

* `Cslib.Circuits.Frontier.Hypergraph.cert_r3_sheppard`, `cert_r3_slepian`, `cert_r4_sheppard`,
  `cert_r8_slepian`, `cert_r16_slepian`, `cert_r64_slepian`: verified `HyperDualCert` witnesses.
-/

public section

namespace Cslib.Circuits.Frontier.Hypergraph

open ProbabilityTheory Real Set

/-! ### Rational `π`, `cos`, and `arccos / π` upper bounds -/

private abbrev piLo : ℚ := 314159265358979323846 / 10 ^ 20

private abbrev sqrtTwoPiHi : ℚ := 25066282747 / 10 ^ 10

private theorem piLo_lt_pi : (piLo : ℝ) < π := by
  have h := Real.pi_gt_d20
  push_cast [piLo]
  norm_num at h ⊢
  linarith

private theorem two_mul_pi_le_sq_sqrtTwoPiHi : 2 * π ≤ (sqrtTwoPiHi : ℝ) ^ 2 := by
  have h := Real.pi_lt_d20
  push_cast [sqrtTwoPiHi]
  norm_num at h ⊢
  linarith

private def qCosPoly (x : ℚ) : ℚ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320

private def qCosErr (x : ℚ) : ℚ :=
  x ^ 10 * (11 / 36288000)

private def qCosUpper (θ : ℚ) : ℚ :=
  if θ ≤ 7 / 10 then qCosPoly θ + qCosErr θ
  else 2 * (qCosPoly (θ / 2) + qCosErr (θ / 2)) ^ 2 - 1

private theorem cos_bounds_of_rat {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ((qCosPoly x - qCosErr x : ℚ) : ℝ) ≤ cos (x : ℝ) ∧
      cos (x : ℝ) ≤ ((qCosPoly x + qCosErr x : ℚ) : ℝ) := by
  have hx0R : 0 ≤ (x : ℝ) := Rat.cast_nonneg.mpr hx0
  have habs : |(x : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg hx0R]
    exact_mod_cast hx1
  have hb := Real.cos_bound_ten habs
  rw [abs_of_nonneg hx0R, abs_le] at hb
  push_cast [qCosPoly, qCosErr]
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

private theorem cos_le_qCosUpper {θ : ℚ} (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2)
    (hpos : 0 ≤ qCosPoly (θ / 2) - qCosErr (θ / 2)) :
    cos (θ : ℝ) ≤ (qCosUpper θ : ℝ) := by
  unfold qCosUpper
  split_ifs with h7
  · exact (cos_bounds_of_rat hθ0 (h7.trans (by norm_num))).2
  · have hh0 : 0 ≤ θ / 2 := by linarith
    have hh1 : θ / 2 ≤ 1 := by linarith
    obtain ⟨hlo, hhi⟩ := cos_bounds_of_rat hh0 hh1
    have hcos_nn : 0 ≤ cos ((θ / 2 : ℚ) : ℝ) := (Rat.cast_nonneg.mpr hpos).trans hlo
    have hsq : cos ((θ / 2 : ℚ) : ℝ) ^ 2 ≤
        ((qCosPoly (θ / 2) + qCosErr (θ / 2) : ℚ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ hcos_nn hhi 2
    have h2mul : cos (θ : ℝ) = 2 * cos ((θ / 2 : ℚ) : ℝ) ^ 2 - 1 := by
      rw [show (θ : ℝ) = 2 * ((θ / 2 : ℚ) : ℝ) by push_cast; ring, Real.cos_two_mul]
    push_cast at h2mul hsq ⊢
    linarith

private theorem arccos_div_pi_le_of_qCosUpper {θ ρ_lo : ℚ} {ρ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2)
    (hpos : 0 ≤ qCosPoly (θ / 2) - qCosErr (θ / 2))
    (hcu : qCosUpper θ ≤ ρ_lo) (hρ_m1 : -1 ≤ ρ_lo)
    (hρ_lo : (ρ_lo : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1) :
    arccos ρ / π ≤ ((θ / piLo : ℚ) : ℝ) := by
  have hcos_le : cos (θ : ℝ) ≤ ρ :=
    (cos_le_qCosUpper hθ0 hθ2 hpos).trans ((Rat.cast_le.mpr hcu).trans hρ_lo)
  have hρ_ge : -1 ≤ ρ := (by exact_mod_cast hρ_m1 : (-1 : ℝ) ≤ ρ_lo).trans hρ_lo
  rw [← cos_arccos hρ_ge hρ1] at hcos_le
  have hθ_pi : (θ : ℝ) ≤ π := ((Rat.cast_le.mpr hθ2).trans (by norm_num)).trans Real.two_le_pi
  have hθ_mem : (θ : ℝ) ∈ Icc 0 π := ⟨Rat.cast_nonneg.mpr hθ0, hθ_pi⟩
  have harc_mem : arccos ρ ∈ Icc 0 π := ⟨arccos_nonneg ρ, arccos_le_pi ρ⟩
  have harc_le : arccos ρ ≤ (θ : ℝ) := by
    by_contra! hlt
    exact absurd (strictAntiOn_cos hθ_mem harc_mem hlt) (not_lt.mpr hcos_le)
  have hpiLo_pos : 0 < (piLo : ℝ) := by norm_num [piLo]
  calc arccos ρ / π ≤ (θ : ℝ) / π := div_le_div_of_nonneg_right harc_le pi_pos.le
    _ ≤ (θ : ℝ) / (piLo : ℝ) :=
        div_le_div_of_nonneg_left (Rat.cast_nonneg.mpr hθ0) hpiLo_pos piLo_lt_pi.le
    _ = ((θ / piLo : ℚ) : ℝ) := by push_cast; rfl

/-! ### Algebraic bridges for `HyperEdgeBound` constructors -/

private theorem cast_mul_pred_eq {r k : ℕ} (hk : 1 ≤ k) :
    (r : ℝ) * ((k : ℝ) - 1) = ((r * (k - 1) : ℕ) : ℝ) := by
  rw [Nat.cast_mul, Nat.cast_sub hk, Nat.cast_one]

private theorem rat_cast_linear_le {k : ℕ} {q a b : ℚ} (hp : q ≤ a * (k : ℕ) + b) :
    (q : ℝ) ≤ (a : ℝ) * (k : ℕ) + (b : ℝ) := by
  have hR : (q : ℝ) ≤ ((a * (k : ℕ) + b : ℚ) : ℝ) := Rat.cast_le.mpr hp
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast] using hR

private theorem twoStepCorr_eq {r k : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k) :
    twoStepCorr r k = 2 * √((r * (k - 1) : ℕ) : ℝ) / (((r * (k - 1) : ℕ) : ℝ) + 1) := by
  set m : ℕ := r * (k - 1)
  have hm_eq : (r : ℝ) * ((k : ℝ) - 1) = (m : ℝ) := cast_mul_pred_eq (by omega)
  have hm_pos : 0 < (m : ℝ) := by
    dsimp only [m]
    exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hsq_ne : √(m : ℝ) ≠ 0 := (sqrt_pos.mpr hm_pos).ne'
  unfold twoStepCorr
  rw [hm_eq]
  field_simp [hsq_ne]
  rw [sq_sqrt hm_pos.le]

private theorem le_twoStepCorr_and_lt_one {r k : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k) {s_lo : ℚ}
    (hs0 : 0 ≤ s_lo) (hsq : s_lo ^ 2 ≤ ((r * (k - 1) : ℕ) : ℚ)) :
    ((2 * s_lo / ((r * (k - 1) : ℕ) + 1) : ℚ) : ℝ) ≤ twoStepCorr r k ∧
      twoStepCorr r k < 1 := by
  rw [twoStepCorr_eq hr hk]
  set m : ℕ := r * (k - 1)
  have hm2 : 2 ≤ m :=
    le_trans (by decide : 2 ≤ 2 * 1) (Nat.mul_le_mul hr (by omega))
  have hs_le : (s_lo : ℝ) ≤ √(m : ℝ) := by
    rw [← sq_le_sq₀ (Rat.cast_nonneg.mpr hs0) (sqrt_nonneg _), sq_sqrt (Nat.cast_nonneg m)]
    exact_mod_cast hsq
  refine ⟨?_, ?_⟩
  · push_cast
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · rw [div_lt_one (by positivity)]
    have hmR : (2 : ℝ) ≤ m := Nat.ofNat_le_cast.mpr hm2
    have h1 : 1 < √(m : ℝ) := (lt_sqrt zero_le_one).mpr (by linarith)
    nlinarith [sq_pos_of_pos (sub_pos.mpr h1), sq_sqrt (Nat.cast_nonneg (α := ℝ) m)]

private theorem coneMeanSq_and_coneCorr_eq {r k : ℕ} (hr : 2 ≤ r) (hk : 3 ≤ k) :
    coneMeanSq r k = (((r + 1 : ℚ) / (r * k) : ℚ) : ℝ) ∧
      coneCorr r k =
        (2 * √((r * (k - 1) : ℕ) : ℝ) + ((k : ℝ) - 2)) /
          (((r * (k - 1) : ℕ) : ℝ) + (k : ℝ) - 1) := by
  set m : ℕ := r * (k - 1)
  have hm_eq : (r : ℝ) * ((k : ℝ) - 1) = (m : ℝ) := cast_mul_pred_eq (by omega)
  have hm_pos : 0 < (m : ℝ) := by
    dsimp only [m]
    exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hsq_ne : √(m : ℝ) ≠ 0 := (sqrt_pos.mpr hm_pos).ne'
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk1_ne : ((k : ℝ) - 1) ≠ 0 := by
    have : (3 : ℝ) ≤ k := Nat.ofNat_le_cast.mpr hk
    linarith
  refine ⟨?_, ?_⟩
  · unfold coneMeanSq
    rw [hm_eq, div_pow, one_pow, sq_sqrt hm_pos.le, ← hm_eq]
    push_cast
    field_simp [hr_ne, hk_ne, hk1_ne]
  · unfold coneCorr
    dsimp only
    rw [hm_eq]
    field_simp [hsq_ne]
    rw [sq_sqrt hm_pos.le]
    ring

private theorem hyperEdgeBound_pairwise_three_two {a b : ℚ} (hp : 1 / 6 ≤ a * (2 : ℕ) + b) :
    HyperEdgeBound 3 2 ((a : ℝ) * (2 : ℕ) + (b : ℝ)) := by
  refine HyperEdgeBound.pairwise ?_
  have hcorr : twoStepCorr 3 2 = cos (π / 6) := by
    rw [twoStepCorr_eq (by decide) (by decide), cos_pi_div_six]
    norm_num
    ring
  rw [hcorr, arccos_cos (by positivity) (by linarith [pi_pos])]
  have hsimp : ((2 : ℕ) : ℝ) / (2 * π) * (π / 6) = ((1 / 6 : ℚ) : ℝ) := by
    have hpi : π ≠ 0 := pi_ne_zero
    push_cast
    field_simp [hpi]
  rw [hsimp]
  exact rat_cast_linear_le hp

private theorem hyperEdgeBound_pairwise_of_rat {r k : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k)
    {s_lo θ a b : ℚ} (hs0 : 0 ≤ s_lo) (hsq : s_lo ^ 2 ≤ ((r * (k - 1) : ℕ) : ℚ))
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2) (hpos : 0 ≤ qCosPoly (θ / 2) - qCosErr (θ / 2))
    (hcu : qCosUpper θ ≤ 2 * s_lo / ((r * (k - 1) : ℕ) + 1))
    (hp : (k : ℚ) / 2 * (θ / piLo) ≤ a * (k : ℕ) + b) :
    HyperEdgeBound r k ((a : ℝ) * (k : ℕ) + (b : ℝ)) := by
  obtain ⟨hρ_lo, hρ_lt⟩ := le_twoStepCorr_and_lt_one hr hk hs0 hsq
  have hρ_m1 : (-1 : ℚ) ≤ 2 * s_lo / ((r * (k - 1) : ℕ) + 1) :=
    le_trans (b := 0) (by norm_num) (by positivity)
  have harc := arccos_div_pi_le_of_qCosUpper hθ0 hθ2 hpos hcu hρ_m1 hρ_lo hρ_lt.le
  refine HyperEdgeBound.pairwise ?_
  calc (k : ℝ) / (2 * π) * arccos (twoStepCorr r k)
      = ((k : ℝ) / 2) * (arccos (twoStepCorr r k) / π) := by ring
    _ ≤ ((k : ℝ) / 2) * ((θ / piLo : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left harc (by positivity)
    _ = (((k : ℚ) / 2 * (θ / piLo) : ℚ) : ℝ) := by
        push_cast
        ring
    _ ≤ (a : ℝ) * (k : ℕ) + (b : ℝ) := rat_cast_linear_le hp

private theorem hyperEdgeBound_starCone_of_rat {r k : ℕ} (hr : 2 ≤ r) (hk : 3 ≤ k)
    {s_lo s_hi θ a b : ℚ} (hs0 : 0 ≤ s_lo) (hsq_lo : s_lo ^ 2 ≤ ((r * (k - 1) : ℕ) : ℚ))
    (hshi0 : 0 < s_hi) (hsq_hi : ((r * (k - 1) : ℕ) : ℚ) ≤ s_hi ^ 2)
    (hcone_lo : 1 < ((r + 1 : ℚ) / (r * k)) ^ 2 * ((r * (k - 1) : ℕ) : ℚ))
    (hcone_hi : max 0 (((r + 1 : ℚ) / (r * k)) * s_hi - 1) ^ 2 <
      4 * ((r + 1 : ℚ) / (r * k)))
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2) (hpos : 0 ≤ qCosPoly (θ / 2) - qCosErr (θ / 2))
    (hcu : qCosUpper θ ≤ (2 * s_lo + ((k : ℚ) - 2)) / (((r * (k - 1) : ℕ) : ℚ) + k - 1))
    (hp : (k : ℚ) / 2 * (θ / piLo) ≤ a * (k : ℕ) + b) :
    HyperEdgeBound r k ((a : ℝ) * (k : ℕ) + (b : ℝ)) := by
  obtain ⟨hQ_eq, hC_eq⟩ := coneMeanSq_and_coneCorr_eq hr hk
  set m : ℕ := r * (k - 1)
  have hm_eq : (r : ℝ) * ((k : ℝ) - 1) = (m : ℝ) := cast_mul_pred_eq (by omega)
  have hm2 : 2 ≤ m :=
    le_trans (by decide : 2 ≤ 2 * 1) (Nat.mul_le_mul hr (by omega))
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  set Q₀ : ℚ := (r + 1 : ℚ) / (r * k)
  have hQ₀_pos : 0 < Q₀ := by
    dsimp only [Q₀]
    positivity
  refine HyperEdgeBound.starCone hk ?_ ?_ ?_
  · rw [hm_eq, hQ_eq]
    have h1 : 1 < (Q₀ : ℝ) ^ 2 * (m : ℝ) := by exact_mod_cast hcone_lo
    have hsq_pos : 0 < √(m : ℝ) := sqrt_pos.mpr hm_pos
    rw [div_lt_iff₀ hsq_pos]
    have h2 : 1 ^ 2 < ((Q₀ : ℝ) * √(m : ℝ)) ^ 2 := by
      rw [mul_pow, sq_sqrt hm_pos.le]
      linarith [h1]
    nlinarith [mul_pos (Rat.cast_pos.mpr hQ₀_pos) hsq_pos]
  · rw [hm_eq, hQ_eq]
    have hsm_le : √(m : ℝ) ≤ (s_hi : ℝ) := by
      rw [← sq_le_sq₀ (sqrt_nonneg _) (Rat.cast_nonneg.mpr hshi0.le), sq_sqrt hm_pos.le]
      exact_mod_cast hsq_hi
    have hq_ge : 1 / (s_hi : ℝ) ≤ 1 / √(m : ℝ) :=
      one_div_le_one_div_of_le (sqrt_pos.mpr hm_pos) hsm_le
    have hstep : (Q₀ : ℝ) - 1 / (s_hi : ℝ) < 2 * (1 / (s_hi : ℝ)) * √(Q₀ : ℝ) := by
      have hshiR : 0 < (s_hi : ℝ) := Rat.cast_pos.mpr hshi0
      have hmul_lt : (Q₀ : ℝ) * (s_hi : ℝ) - 1 < 2 * √(Q₀ : ℝ) := by
        by_cases hneg : (Q₀ : ℝ) * (s_hi : ℝ) - 1 ≤ 0
        · exact hneg.trans_lt (mul_pos two_pos (sqrt_pos.mpr (Rat.cast_pos.mpr hQ₀_pos)))
        · push Not at hneg
          have hsq : ((Q₀ : ℝ) * (s_hi : ℝ) - 1) ^ 2 < (2 * √(Q₀ : ℝ)) ^ 2 := by
            rw [mul_pow, sq_sqrt (Rat.cast_nonneg.mpr hQ₀_pos.le)]
            have hq : (Q₀ * s_hi - 1) ^ 2 < 4 * Q₀ := by
              have hmax : Q₀ * s_hi - 1 ≤ max 0 (Q₀ * s_hi - 1) := le_max_right _ _
              have h0 : 0 < Q₀ * s_hi - 1 := by exact_mod_cast hneg
              exact (pow_le_pow_left₀ h0.le hmax 2).trans_lt hcone_hi
            exact_mod_cast hq
          nlinarith [sqrt_nonneg (Q₀ : ℝ)]
      have hdiv := div_lt_div_of_pos_right hmul_lt hshiR
      have hlhs : ((Q₀ : ℝ) * (s_hi : ℝ) - 1) / (s_hi : ℝ) = (Q₀ : ℝ) - 1 / (s_hi : ℝ) := by
        field_simp [hshiR.ne']
      have hrhs : 2 * √(Q₀ : ℝ) / (s_hi : ℝ) = 2 * (1 / (s_hi : ℝ)) * √(Q₀ : ℝ) := by ring
      linarith
    have hsqrt_nn : 0 ≤ √(Q₀ : ℝ) := sqrt_nonneg _
    linarith [mul_le_mul_of_nonneg_right hq_ge hsqrt_nn]
  · have hs_le : (s_lo : ℝ) ≤ √(m : ℝ) := by
      rw [← sq_le_sq₀ (Rat.cast_nonneg.mpr hs0) (sqrt_nonneg _), sq_sqrt hm_pos.le]
      exact_mod_cast hsq_lo
    have hρ_lo : (((2 * s_lo + ((k : ℚ) - 2)) / ((m : ℚ) + k - 1) : ℚ) : ℝ) ≤ coneCorr r k := by
      rw [hC_eq]
      push_cast
      exact div_le_div_of_nonneg_right (by linarith) (by
        have : (3 : ℝ) ≤ k := Nat.ofNat_le_cast.mpr hk
        linarith)
    have hρ_le1 : coneCorr r k ≤ 1 := by
      rw [hC_eq, div_le_one (by
        have : (3 : ℝ) ≤ k := Nat.ofNat_le_cast.mpr hk
        linarith)]
      nlinarith [sq_nonneg (√(m : ℝ) - 1), sq_sqrt hm_pos.le]
    have hρ_m1 : (-1 : ℚ) ≤ (2 * s_lo + ((k : ℚ) - 2)) / ((m : ℚ) + k - 1) := by
      have : (3 : ℚ) ≤ k := Nat.ofNat_le_cast.mpr hk
      have : (0 : ℚ) ≤ m := Nat.cast_nonneg m
      exact le_trans (by norm_num) (div_nonneg (by linarith) (by linarith))
    have harc := arccos_div_pi_le_of_qCosUpper hθ0 hθ2 hpos hcu hρ_m1 hρ_lo hρ_le1
    calc (k : ℝ) / (2 * π) * arccos (coneCorr r k)
        = ((k : ℝ) / 2) * (arccos (coneCorr r k) / π) := by ring
      _ ≤ ((k : ℝ) / 2) * ((θ / piLo : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left harc (by positivity)
      _ = (((k : ℚ) / 2 * (θ / piLo) : ℚ) : ℝ) := by
          push_cast
          ring
      _ ≤ (a : ℝ) * (k : ℕ) + (b : ℝ) := rat_cast_linear_le hp

private theorem hyperEdgeBound_cap_of_rat {r k : ℕ} (hr : 2 ≤ r) (hk : 3 ≤ k)
    {s_hi θ a b : ℚ} (hshi1 : 1 ≤ s_hi) (hsq_hi : ((r * (k - 1) : ℕ) : ℚ) ≤ s_hi ^ 2)
    (hcap_gt : 1 / 2 < 4 * s_hi / (s_hi + 1) ^ 2)
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2) (hpos : 0 ≤ qCosPoly (θ / 2) - qCosErr (θ / 2))
    (hcu : qCosUpper θ ≤ ((k : ℚ) * (4 * s_hi / (s_hi + 1) ^ 2) - 1) / ((k : ℚ) - 1))
    (hp : (k : ℚ) / 2 * (θ / piLo) ≤ a * (k : ℕ) + b) :
    HyperEdgeBound r k ((a : ℝ) * (k : ℕ) + (b : ℝ)) := by
  set m : ℕ := r * (k - 1)
  have hm_eq : (r : ℝ) * ((k : ℝ) - 1) = (m : ℝ) := cast_mul_pred_eq (by omega)
  have hm2 : 2 ≤ m :=
    le_trans (by decide : 2 ≤ 2 * 1) (Nat.mul_le_mul hr (by omega))
  have hm1 : (1 : ℝ) ≤ √(m : ℝ) :=
    (le_sqrt zero_le_one (Nat.cast_nonneg m)).mpr (by
      have : (2 : ℝ) ≤ m := Nat.ofNat_le_cast.mpr hm2
      linarith)
  have hshiR1 : 1 ≤ (s_hi : ℝ) := by exact_mod_cast hshi1
  have hsm_le : √(m : ℝ) ≤ (s_hi : ℝ) := by
    rw [← sq_le_sq₀ (sqrt_nonneg _) (by linarith), sq_sqrt (Nat.cast_nonneg m)]
    exact_mod_cast hsq_hi
  have hcap_ge : ((4 * s_hi / (s_hi + 1) ^ 2 : ℚ) : ℝ) ≤ capSq r k := by
    unfold capSq
    rw [hm_eq]
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hid : 4 * √(m : ℝ) * ((s_hi : ℝ) + 1) ^ 2 - 4 * (s_hi : ℝ) * (√(m : ℝ) + 1) ^ 2 =
        4 * ((s_hi : ℝ) - √(m : ℝ)) * (√(m : ℝ) * (s_hi : ℝ) - 1) := by ring
    have hprod : 0 ≤ ((s_hi : ℝ) - √(m : ℝ)) * (√(m : ℝ) * (s_hi : ℝ) - 1) :=
      mul_nonneg (sub_nonneg.mpr hsm_le) (by nlinarith)
    linarith
  have hcap_le1 : capSq r k ≤ 1 := by
    unfold capSq
    rw [hm_eq, div_le_one (by positivity)]
    nlinarith [sq_nonneg (√(m : ℝ) - 1)]
  have hcap_half : 1 / 2 < capSq r k := by
    have h12 : (1 / 2 : ℝ) < ((4 * s_hi / (s_hi + 1) ^ 2 : ℚ) : ℝ) := by
      have hq : ((1 / 2 : ℚ) : ℝ) < ((4 * s_hi / (s_hi + 1) ^ 2 : ℚ) : ℝ) :=
        Rat.cast_lt.mpr hcap_gt
      norm_num at hq ⊢
      exact hq
    exact h12.trans_le hcap_ge
  refine HyperEdgeBound.cap hcap_half ?_
  have hk3R : (3 : ℝ) ≤ k := Nat.ofNat_le_cast.mpr hk
  have hρ_lo : ((((k : ℚ) * (4 * s_hi / (s_hi + 1) ^ 2) - 1) / ((k : ℚ) - 1) : ℚ) : ℝ) ≤
      capCorr r k := by
    unfold capCorr
    push_cast at hcap_ge ⊢
    exact div_le_div_of_nonneg_right (by nlinarith) (by linarith)
  have hρ_le1 : capCorr r k ≤ 1 := by
    unfold capCorr
    rw [div_le_one (by linarith)]
    nlinarith
  have hρ_m1 : (-1 : ℚ) ≤ ((k : ℚ) * (4 * s_hi / (s_hi + 1) ^ 2) - 1) / ((k : ℚ) - 1) := by
    have hk3Q : (3 : ℚ) ≤ k := Nat.ofNat_le_cast.mpr hk
    exact le_trans (by norm_num) (div_nonneg (by nlinarith) (by linarith))
  have harc := arccos_div_pi_le_of_qCosUpper hθ0 hθ2 hpos hcu hρ_m1 hρ_lo hρ_le1
  calc (k : ℝ) / (2 * π) * arccos (capCorr r k)
      = ((k : ℝ) / 2) * (arccos (capCorr r k) / π) := by ring
    _ ≤ ((k : ℝ) / 2) * ((θ / piLo : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left harc (by positivity)
    _ = (((k : ℚ) / 2 * (θ / piLo) : ℚ) : ℝ) := by
        push_cast
        ring
    _ ≤ (a : ℝ) * (k : ℕ) + (b : ℝ) := rat_cast_linear_le hp

private theorem hyperEdgeBound_slepian_three_of_rat {r : ℕ} (hr : 2 ≤ r)
    {s_lo θ a b : ℚ} (hs0 : 0 ≤ s_lo) (hsq : s_lo ^ 2 ≤ ((r * 2 : ℕ) : ℚ))
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2) (hpos : 0 ≤ qCosPoly (θ / 2) - qCosErr (θ / 2))
    (hcu : qCosUpper θ ≤ 2 * s_lo / ((r * 2 : ℕ) + 1))
    (hp : 3 / 2 * (θ / piLo) ≤ a * (3 : ℕ) + b) :
    HyperEdgeBound r 3 ((a : ℝ) * (3 : ℕ) + (b : ℝ)) := by
  obtain ⟨hρ_lo, hρ_lt⟩ := le_twoStepCorr_and_lt_one hr (k := 3) (by decide) hs0 hsq
  have hρ0 : 0 ≤ twoStepCorr r 3 :=
    le_trans (by positivity) hρ_lo
  have hρ_m1 : (-1 : ℚ) ≤ 2 * s_lo / ((r * 2 : ℕ) + 1) :=
    le_trans (b := 0) (by norm_num) (by positivity)
  have harc := arccos_div_pi_le_of_qCosUpper hθ0 hθ2 hpos hcu hρ_m1 hρ_lo hρ_lt.le
  refine HyperEdgeBound.slepian ?_
  rw [equicorrStraddle_three hρ0 hρ_lt]
  calc 3 / (2 * π) * arccos (twoStepCorr r 3)
      = (3 / 2 : ℝ) * (arccos (twoStepCorr r 3) / π) := by ring
    _ ≤ (3 / 2 : ℝ) * ((θ / piLo : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left harc (by positivity)
    _ = ((3 / 2 * (θ / piLo) : ℚ) : ℝ) := by
        push_cast
        ring
    _ ≤ (a : ℝ) * (3 : ℕ) + (b : ℝ) := rat_cast_linear_le hp

private theorem hyperEdgeBound_slepian_of_rat {r k m_in m_out S_out : ℕ}
    (hr : 2 ≤ r) (hk4 : 4 ≤ k) (hk7 : k ≤ 7) (hS : 1 ≤ S_out)
    {s_lo θ γ_lo B I4_lo I6_lo a b : ℚ}
    (hs0 : 0 < s_lo) (hsq : s_lo ^ 2 ≤ ((r * (k - 1) : ℕ) : ℚ))
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2) (hpos : 0 ≤ qCosPoly (θ / 2) - qCosErr (θ / 2))
    (hcu : qCosUpper θ ≤ 2 * s_lo / ((r * (k - 1) : ℕ) + 1))
    (hγ0 : 0 ≤ γ_lo)
    (hγ : γ_lo ^ 2 * (1 - 2 * s_lo / ((r * (k - 1) : ℕ) + 1)) ≤
      2 * s_lo / ((r * (k - 1) : ℕ) + 1))
    (hB : 0 < B)
    (hin_pos : 0 ≤ qEval (qExpOddPoly m_in (γ_lo ^ 2 / 2)) (B ^ 2))
    (hout_pos : 0 ≤ qEval (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) (B ^ 2))
    (hI4 : I4_lo ≤ qMomentLower 4 m_in m_out S_out γ_lo B sqrtTwoPiHi)
    (hI6 : 6 ≤ k → I6_lo ≤ qMomentLower 6 m_in m_out S_out γ_lo B sqrtTwoPiHi)
    (hp : 1 - (1 / 2 ^ (k - 1) +
      2 * (k.choose 2 : ℚ) / 2 ^ (k - 2) * (1 / 4 - (θ / piLo) / 2) +
      2 * (k.choose 4 : ℚ) / 2 ^ (k - 4) * I4_lo +
      (if 6 ≤ k then 2 * (k.choose 6 : ℚ) / 2 ^ (k - 6) * I6_lo else 0)) ≤
        a * (k : ℕ) + b) :
    HyperEdgeBound r k ((a : ℝ) * (k : ℕ) + (b : ℝ)) := by
  have hk2 : 2 ≤ k := by omega
  obtain ⟨hρ_lo, hρ_lt⟩ := le_twoStepCorr_and_lt_one hr hk2 hs0.le hsq
  set ρ_lo_q : ℚ := 2 * s_lo / ((r * (k - 1) : ℕ) + 1)
  have hρ_lo_pos : 0 < (ρ_lo_q : ℝ) := by
    dsimp only [ρ_lo_q]
    have : 0 < (s_lo : ℝ) := Rat.cast_pos.mpr hs0
    push_cast
    positivity
  have hρ_pos : 0 < twoStepCorr r k := hρ_lo_pos.trans_le hρ_lo
  have hρ_m1 : (-1 : ℚ) ≤ ρ_lo_q := le_trans (by norm_num) (Rat.cast_nonneg.mp hρ_lo_pos.le)
  have harc := arccos_div_pi_le_of_qCosUpper hθ0 hθ2 hpos hcu hρ_m1 hρ_lo hρ_lt.le
  have hγR : (γ_lo : ℝ) ^ 2 * (1 - twoStepCorr r k) ≤ twoStepCorr r k := by
    have hγ_q : (γ_lo : ℝ) ^ 2 * (1 - (ρ_lo_q : ℝ)) ≤ (ρ_lo_q : ℝ) := by exact_mod_cast hγ
    have hsq_nn : 0 ≤ (γ_lo : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have hsl := equicorrStraddle_le_of_poly hk4 hk7 hS hρ_pos hρ_lt harc hγ0 hγR hB
    (by norm_num [sqrtTwoPiHi]) two_mul_pi_le_sq_sqrtTwoPiHi hin_pos hout_pos
  have hcert_le :
      qEquicorrUpperCert k m_in m_out S_out (θ / piLo) γ_lo B sqrtTwoPiHi ≤ a * (k : ℕ) + b := by
    unfold qEquicorrUpperCert
    dsimp only
    have hc4 : 0 ≤ 2 * (k.choose 4 : ℚ) / 2 ^ (k - 4) := by positivity
    have hm4 := mul_le_mul_of_nonneg_left hI4 hc4
    by_cases hk6 : 6 ≤ k
    · simp only [hk6, ↓reduceIte] at hp ⊢
      have hc6 : 0 ≤ 2 * (k.choose 6 : ℚ) / 2 ^ (k - 6) := by positivity
      have hm6 := mul_le_mul_of_nonneg_left (hI6 hk6) hc6
      linarith
    · simp only [hk6, ↓reduceIte] at hp ⊢
      linarith
  exact HyperEdgeBound.slepian (hsl.trans (rat_cast_linear_le hcert_le))

private theorem qIntOdd_qPolyAdd (a b : List ℚ) (d : ℕ) (B : ℚ) :
    qIntOdd (qPolyAdd a b) d B = qIntOdd a d B + qIntOdd b d B := by
  induction a generalizing b d with
  | nil => simp [qPolyAdd, qIntOdd]
  | cons x xs ih =>
    cases b with
    | nil => simp [qPolyAdd, qIntOdd]
    | cons y ys =>
      simp only [qPolyAdd, qIntOdd, ih]
      ring

private theorem qIntOdd_qPolyMul_take_add_drop (k : ℕ) :
    ∀ (p q : List ℚ) (d : ℕ) (B : ℚ),
      qIntOdd (qPolyMul p q) d B =
        qIntOdd (qPolyMul (p.take k) q) d B +
          qIntOdd (qPolyMul (p.drop k) q) (d + 2 * k) B := by
  induction k with
  | zero => intro p q d B; simp [qPolyMul, qIntOdd]
  | succ k ih =>
    intro p q d B
    cases p with
    | nil => simp [qPolyMul, qIntOdd]
    | cons c cs =>
      simp only [List.take_succ_cons, List.drop_succ_cons, qPolyMul, qIntOdd_qPolyAdd, qIntOdd,
        zero_mul, zero_div, zero_add]
      rw [ih cs q (d + 2) B, show d + 2 + 2 * k = d + 2 * (k + 1) by omega]
      ring

private theorem le_qMomentLower_of_split17 {d m_in m_out S_out : ℕ} {γ_lo B j1 j2 j3 lo : ℚ}
    (hj1 : j1 ≤ qIntOdd
      (qPolyMul ((qPolyPow (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) S_out).take 17)
        (qPolyPow (qInnerPoly m_in γ_lo) d)) d B)
    (hj2 : j2 ≤ qIntOdd
      (qPolyMul (((qPolyPow (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) S_out).drop 17).take 17)
        (qPolyPow (qInnerPoly m_in γ_lo) d)) (d + 34) B)
    (hj3 : j3 ≤ qIntOdd
      (qPolyMul (((qPolyPow (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) S_out).drop 17).drop 17)
        (qPolyPow (qInnerPoly m_in γ_lo) d)) (d + 68) B)
    (hlo : lo ≤ 2 * ((j1 + j2 + j3) / sqrtTwoPiHi ^ (d + 1) +
      ((B * qEval (qInnerPoly m_in γ_lo) (B ^ 2)) ^ d / sqrtTwoPiHi ^ d) *
        ((B / (B ^ 2 + 1)) *
          (qEval (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) (B ^ 2) ^ S_out / sqrtTwoPiHi)))) :
    lo ≤ qMomentLower d m_in m_out S_out γ_lo B sqrtTwoPiHi := by
  unfold qMomentLower
  dsimp only
  set P := qPolyPow (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) S_out
  set Q := qPolyPow (qInnerPoly m_in γ_lo) d
  rw [qIntOdd_qPolyMul_take_add_drop 17 P Q d B,
    qIntOdd_qPolyMul_take_add_drop 17 (P.drop 17) Q (d + 2 * 17) B]
  rw [show d + 2 * 17 + 2 * 17 = d + 68 by omega, show d + 2 * 17 = d + 34 by omega]
  have hs : 0 ≤ sqrtTwoPiHi ^ (d + 1) := pow_nonneg (by norm_num [sqrtTwoPiHi]) (d + 1)
  have hsum : j1 + j2 + j3 ≤
      qIntOdd (qPolyMul (P.take 17) Q) d B +
        (qIntOdd (qPolyMul ((P.drop 17).take 17) Q) (d + 34) B +
          qIntOdd (qPolyMul ((P.drop 17).drop 17) Q) (d + 68) B) := by linarith
  have hdiv := div_le_div_of_nonneg_right hsum hs
  linarith

private theorem take_17 {α : Type*}
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : α) (xs : List α) :
    (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 ::
      x14 :: x15 :: x16 :: xs).take 17 =
    [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16] := rfl

private theorem drop_17 {α : Type*}
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : α) (xs : List α) :
    (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 ::
      x14 :: x15 :: x16 :: xs).drop 17 = xs := rfl

private theorem qPolyPow_one (p : List ℚ) : qPolyPow p 1 = qPolyMul p [1] := rfl
private theorem qPolyPow_two (p : List ℚ) : qPolyPow p 2 = qPolyMul p (qPolyPow p 1) := rfl
private theorem qPolyPow_three (p : List ℚ) : qPolyPow p 3 = qPolyMul p (qPolyPow p 2) := rfl
private theorem qPolyPow_four (p : List ℚ) : qPolyPow p 4 = qPolyMul p (qPolyPow p 3) := rfl
private theorem qPolyPow_five (p : List ℚ) : qPolyPow p 5 = qPolyMul p (qPolyPow p 4) := rfl
private theorem qPolyPow_six (p : List ℚ) : qPolyPow p 6 = qPolyMul p (qPolyPow p 5) := rfl
private theorem qPolyPow_seven (p : List ℚ) : qPolyPow p 7 = qPolyMul p (qPolyPow p 6) := rfl

/-! ### The six verified `HyperDualCert` theorems -/

private theorem hedge_six {r : ℕ} {a b : ℚ}
    (h2 : HyperEdgeBound r 2 ((a : ℝ) * (2 : ℕ) + (b : ℝ)))
    (h3 : HyperEdgeBound r 3 ((a : ℝ) * (3 : ℕ) + (b : ℝ)))
    (h4 : HyperEdgeBound r 4 ((a : ℝ) * (4 : ℕ) + (b : ℝ)))
    (h5 : HyperEdgeBound r 5 ((a : ℝ) * (5 : ℕ) + (b : ℝ)))
    (h6 : HyperEdgeBound r 6 ((a : ℝ) * (6 : ℕ) + (b : ℝ))) :
    ∀ k ∈ Finset.Icc 2 6, HyperEdgeBound r k ((a : ℝ) * (k : ℕ) + (b : ℝ)) := by
  intro k hk
  rcases Finset.mem_Icc.mp hk with ⟨hk2, hkK⟩
  interval_cases k
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

private theorem edge_sheppard_r3_k2 :
    HyperEdgeBound 3 2
      (((18389141 / 100000000 : ℚ) : ℝ) * (2 : ℕ) + ((-19757453 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_pairwise_three_two (by norm_num)

private theorem edge_sheppard_r3_k3 :
    HyperEdgeBound 3 3
      (((18389141 / 100000000 : ℚ) : ℝ) * (3 : ℕ) + ((-19757453 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_starCone_of_rat (by decide) (by decide)
    (s_lo := (122474487139 / 50000000000))
    (s_hi := (244948974279 / 100000000000))
    (θ := (9270307 / 12500000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])

private theorem edge_sheppard_r3_k4 :
    HyperEdgeBound 3 4
      (((18389141 / 100000000 : ℚ) : ℝ) * (4 : ℕ) + ((-19757453 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_cap_of_rat (by decide) (by decide)
    (s_hi := 3)
    (θ := (21026727 / 25000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])

private theorem edge_sheppard_r3_k5 :
    HyperEdgeBound 3 5
      (((18389141 / 100000000 : ℚ) : ℝ) * (5 : ℕ) + ((-19757453 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_cap_of_rat (by decide) (by decide)
    (s_hi := (173205080757 / 50000000000))
    (θ := (18062853 / 20000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])

private theorem edge_sheppard_r3_k6 :
    HyperEdgeBound 3 6
      (((18389141 / 100000000 : ℚ) : ℝ) * (6 : ℕ) + ((-19757453 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_cap_of_rat (by decide) (by decide)
    (s_hi := (387298334621 / 100000000000))
    (θ := (47426207 / 50000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])

/-- Verified dual-LP certificate at `r = 3` (`K₀ = 6`). -/
theorem cert_r3_sheppard :
    HyperDualCert 3 6 (18389141 / 100000000 : ℚ) (-19757453 / 100000000 : ℚ) where
  hr := by decide
  hK₀ := by decide
  ha := by norm_num
  h2 := by norm_num
  htail := by norm_num
  hdenom := by norm_num
  hnum := by norm_num
  hedge := hedge_six edge_sheppard_r3_k2 edge_sheppard_r3_k3 edge_sheppard_r3_k4
    edge_sheppard_r3_k5 edge_sheppard_r3_k6

private theorem edge_slepian_r3_k2 :
    HyperEdgeBound 3 2
      (((17970677 / 100000000 : ℚ) : ℝ) * (2 : ℕ) + ((-18502061 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_pairwise_three_two (by norm_num)

private theorem edge_slepian_r3_k3 :
    HyperEdgeBound 3 3
      (((17970677 / 100000000 : ℚ) : ℝ) * (3 : ℕ) + ((-18502061 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_starCone_of_rat (by decide) (by decide)
    (s_lo := (122474487139 / 50000000000))
    (s_hi := (244948974279 / 100000000000))
    (θ := (9270307 / 12500000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])

private theorem mom4_slepian_r3_k4 :
    ((42647757861 / 2500000000000) : ℚ) ≤
      qMomentLower 4 4 2 2 (61237 / 50000) 2 sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem edge_slepian_r3_k4 :
    HyperEdgeBound 3 4
      (((17970677 / 100000000 : ℚ) : ℝ) * (4 : ℕ) + ((-18502061 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 4) (m_out := 2) (S_out := 2)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := 3)
    (θ := (46364781 / 50000000))
    (γ_lo := (61237 / 50000)) (B := 2)
    (I4_lo := (42647757861 / 2500000000000))
    (I6_lo := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    mom4_slepian_r3_k4
    (by omega)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r3_k5 :
    ((12611397757 / 10000000000000) : ℚ) ≤
      qMomentLower 4 1 1 1 (106819 / 100000) (3 / 5) sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem edge_slepian_r3_k5 :
    HyperEdgeBound 3 5
      (((17970677 / 100000000 : ℚ) : ℝ) * (5 : ℕ) + ((-18502061 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 1) (m_out := 1) (S_out := 1)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (346410161513 / 100000000000))
    (θ := (100872693 / 100000000))
    (γ_lo := (106819 / 100000)) (B := (3 / 5))
    (I4_lo := (12611397757 / 10000000000000))
    (I6_lo := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    mom4_slepian_r3_k5
    (by omega)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r3_k6 :
    ((8905614613 / 10000000000000) : ℚ) ≤
      qMomentLower 4 1 1 1 (96873 / 100000) (3 / 5) sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem mom6_slepian_r3_k6 :
    ((400160759 / 10000000000000) : ℚ) ≤
      qMomentLower 6 1 1 1 (96873 / 100000) (3 / 5) sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem edge_slepian_r3_k6 :
    HyperEdgeBound 3 6
      (((17970677 / 100000000 : ℚ) : ℝ) * (6 : ℕ) + ((-18502061 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 1) (m_out := 1) (S_out := 1)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (19364916731 / 5000000000))
    (θ := (53271811 / 50000000))
    (γ_lo := (96873 / 100000)) (B := (3 / 5))
    (I4_lo := (8905614613 / 10000000000000))
    (I6_lo := (400160759 / 10000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    mom4_slepian_r3_k6
    (fun _ => mom6_slepian_r3_k6)
    (by norm_num [Nat.choose, piLo])

/-- Verified dual-LP certificate at `r = 3` (`K₀ = 6`). -/
theorem cert_r3_slepian :
    HyperDualCert 3 6 (17970677 / 100000000 : ℚ) (-18502061 / 100000000 : ℚ) where
  hr := by decide
  hK₀ := by decide
  ha := by norm_num
  h2 := by norm_num
  htail := by norm_num
  hdenom := by norm_num
  hnum := by norm_num
  hedge := hedge_six edge_slepian_r3_k2 edge_slepian_r3_k3 edge_slepian_r3_k4
    edge_slepian_r3_k5 edge_slepian_r3_k6

private theorem edge_sheppard_r4_k2 :
    HyperEdgeBound 4 2
      (((19737623 / 100000000 : ℚ) : ℝ) * (2 : ℕ) + ((-18991953 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_pairwise_of_rat (by decide) (by decide)
    (s_lo := 2)
    (θ := (64350151 / 100000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])

private theorem edge_sheppard_r4_k3 :
    HyperEdgeBound 4 3
      (((19737623 / 100000000 : ℚ) : ℝ) * (3 : ℕ) + ((-18991953 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_starCone_of_rat (by decide) (by decide)
    (s_lo := (141421356237 / 50000000000))
    (s_hi := (11313708499 / 4000000000))
    (θ := (42119239 / 50000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])

private theorem edge_sheppard_r4_k4 :
    HyperEdgeBound 4 4
      (((19737623 / 100000000 : ℚ) : ℝ) * (4 : ℕ) + ((-18991953 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_starCone_of_rat (by decide) (by decide)
    (s_lo := (346410161513 / 100000000000))
    (s_hi := (173205080757 / 50000000000))
    (θ := (11665817 / 12500000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])

private theorem edge_sheppard_r4_k5 :
    HyperEdgeBound 4 5
      (((19737623 / 100000000 : ℚ) : ℝ) * (5 : ℕ) + ((-18991953 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_cap_of_rat (by decide) (by decide)
    (s_hi := 4)
    (θ := (98843249 / 100000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])

private theorem edge_sheppard_r4_k6 :
    HyperEdgeBound 4 6
      (((19737623 / 100000000 : ℚ) : ℝ) * (6 : ℕ) + ((-18991953 / 100000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_cap_of_rat (by decide) (by decide)
    (s_hi := (894427191 / 200000000))
    (θ := (102760211 / 100000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])

/-- Verified dual-LP certificate at `r = 4` (`K₀ = 6`). -/
theorem cert_r4_sheppard :
    HyperDualCert 4 6 (19737623 / 100000000 : ℚ) (-18991953 / 100000000 : ℚ) where
  hr := by decide
  hK₀ := by decide
  ha := by norm_num
  h2 := by norm_num
  htail := by norm_num
  hdenom := by norm_num
  hnum := by norm_num
  hedge := hedge_six edge_sheppard_r4_k2 edge_sheppard_r4_k3 edge_sheppard_r4_k4
    edge_sheppard_r4_k5 edge_sheppard_r4_k6

private theorem edge_slepian_r8_k2 :
    HyperEdgeBound 8 2
      (((666667 / 4000000 : ℚ) : ℝ) * (2 : ℕ) + ((0 : ℚ) : ℝ)) :=
  hyperEdgeBound_pairwise_of_rat (by decide) (by decide)
    (s_lo := (141421356237 / 50000000000))
    (θ := (89112291 / 100000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])

private theorem edge_slepian_r8_k3 :
    HyperEdgeBound 8 3
      (((666667 / 4000000 : ℚ) : ℝ) * (3 : ℕ) + ((0 : ℚ) : ℝ)) :=
  hyperEdgeBound_starCone_of_rat (by decide) (by decide)
    (s_lo := 4)
    (s_hi := 4)
    (θ := (26179949 / 25000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])

private theorem mom4_slepian_r8_k4 :
    ((40268530757 / 5000000000000) : ℚ) ≤
      qMomentLower 4 3 3 2 (80281 / 100000) (5 / 2) sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem edge_slepian_r8_k4 :
    HyperEdgeBound 8 4
      (((666667 / 4000000 : ℚ) : ℝ) * (4 : ℕ) + ((0 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 3) (m_out := 3) (S_out := 2)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (122474487139 / 25000000000))
    (θ := (116808089 / 100000000))
    (γ_lo := (80281 / 100000)) (B := (5 / 2))
    (I4_lo := (40268530757 / 5000000000000))
    (I6_lo := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    mom4_slepian_r8_k4
    (by omega)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r8_k5 :
    ((3011188201 / 10000000000000) : ℚ) ≤
      qMomentLower 4 1 1 1 (18057 / 25000) (3 / 5) sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem edge_slepian_r8_k5 :
    HyperEdgeBound 8 5
      (((666667 / 4000000 : ℚ) : ℝ) * (5 : ℕ) + ((0 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 1) (m_out := 1) (S_out := 1)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (565685424949 / 100000000000))
    (θ := (15260733 / 12500000))
    (γ_lo := (18057 / 25000)) (B := (3 / 5))
    (I4_lo := (3011188201 / 10000000000000))
    (I6_lo := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    mom4_slepian_r8_k5
    (by omega)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r8_k6 :
    ((2239046637 / 10000000000000) : ℚ) ≤
      qMomentLower 4 1 1 1 (13359 / 20000) (3 / 5) sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem mom6_slepian_r8_k6 :
    ((50687217 / 10000000000000) : ℚ) ≤
      qMomentLower 6 1 1 1 (13359 / 20000) (3 / 5) sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem edge_slepian_r8_k6 :
    HyperEdgeBound 8 6
      (((666667 / 4000000 : ℚ) : ℝ) * (6 : ℕ) + ((0 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 1) (m_out := 1) (S_out := 1)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (632455532033 / 100000000000))
    (θ := (15714567 / 12500000))
    (γ_lo := (13359 / 20000)) (B := (3 / 5))
    (I4_lo := (2239046637 / 10000000000000))
    (I6_lo := (50687217 / 10000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    mom4_slepian_r8_k6
    (fun _ => mom6_slepian_r8_k6)
    (by norm_num [Nat.choose, piLo])

/-- Verified dual-LP certificate at `r = 8` (`K₀ = 6`). -/
theorem cert_r8_slepian :
    HyperDualCert 8 6 (666667 / 4000000 : ℚ) (0 : ℚ) where
  hr := by decide
  hK₀ := by decide
  ha := by norm_num
  h2 := by norm_num
  htail := by norm_num
  hdenom := by norm_num
  hnum := by norm_num
  hedge := hedge_six edge_slepian_r8_k2 edge_slepian_r8_k3 edge_slepian_r8_k4
    edge_slepian_r8_k5 edge_slepian_r8_k6

private theorem edge_slepian_r16_k2 :
    HyperEdgeBound 16 2
      (((4588373 / 50000000 : ℚ) : ℝ) * (2 : ℕ) + ((18096309 / 50000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_pairwise_of_rat (by decide) (by decide)
    (s_lo := 4)
    (θ := (108083941 / 100000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])

private theorem edge_slepian_r16_k3 :
    HyperEdgeBound 16 3
      (((4588373 / 50000000 : ℚ) : ℝ) * (3 : ℕ) + ((18096309 / 50000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_starCone_of_rat (by decide) (by decide)
    (s_lo := (565685424949 / 100000000000))
    (s_hi := (11313708499 / 2000000000))
    (θ := (12002041 / 10000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])

private theorem mom4_slepian_r16_k4 :
    ((22793381879 / 5000000000000) : ℚ) ≤
      qMomentLower 4 4 3 5 (1480 / 2357) (39 / 10) sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem edge_slepian_r16_k4 :
    HyperEdgeBound 16 4
      (((4588373 / 50000000 : ℚ) : ℝ) * (4 : ℕ) + ((18096309 / 50000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 4) (m_out := 3) (S_out := 5)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (692820323027 / 100000000000))
    (θ := (128410129 / 100000000))
    (γ_lo := (1480 / 2357)) (B := (39 / 10))
    (I4_lo := (22793381879 / 5000000000000))
    (I6_lo := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    mom4_slepian_r16_k4
    (by omega)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r16_k5 :
    ((35556367833 / 10000000000000) : ℚ) ≤
      qMomentLower 4 4 3 6 (4 / 7) (21 / 5) sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem edge_slepian_r16_k5 :
    HyperEdgeBound 16 5
      (((4588373 / 50000000 : ℚ) : ℝ) * (5 : ℕ) + ((18096309 / 50000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 4) (m_out := 3) (S_out := 6)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := 8)
    (θ := (33052161 / 25000000))
    (γ_lo := (4 / 7)) (B := (21 / 5))
    (I4_lo := (35556367833 / 10000000000000))
    (I6_lo := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    mom4_slepian_r16_k5
    (by omega)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r16_k6 :
    ((468300427 / 5000000000000) : ℚ) ≤
      qMomentLower 4 1 1 1 (53239 / 100000) (3 / 5) sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem mom6_slepian_r16_k6 :
    ((6867393 / 5000000000000) : ℚ) ≤
      qMomentLower 6 1 1 1 (53239 / 100000) (3 / 5) sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem edge_slepian_r16_k6 :
    HyperEdgeBound 16 6
      (((4588373 / 50000000 : ℚ) : ℝ) * (6 : ℕ) + ((18096309 / 50000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 1) (m_out := 1) (S_out := 1)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (894427190999 / 100000000000))
    (θ := (13481147 / 10000000))
    (γ_lo := (53239 / 100000)) (B := (3 / 5))
    (I4_lo := (468300427 / 5000000000000))
    (I6_lo := (6867393 / 5000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    mom4_slepian_r16_k6
    (fun _ => mom6_slepian_r16_k6)
    (by norm_num [Nat.choose, piLo])

/-- Verified dual-LP certificate at `r = 16` (`K₀ = 6`). -/
theorem cert_r16_slepian :
    HyperDualCert 16 6 (4588373 / 50000000 : ℚ) (18096309 / 50000000 : ℚ) where
  hr := by decide
  hK₀ := by decide
  ha := by norm_num
  h2 := by norm_num
  htail := by norm_num
  hdenom := by norm_num
  hnum := by norm_num
  hedge := hedge_six edge_slepian_r16_k2 edge_slepian_r16_k3 edge_slepian_r16_k4
    edge_slepian_r16_k5 edge_slepian_r16_k6

private theorem edge_slepian_r64_k2 :
    HyperEdgeBound 64 2
      (((2318347 / 50000000 : ℚ) : ℝ) * (2 : ℕ) + ((16272637 / 25000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_pairwise_of_rat (by decide) (by decide)
    (s_lo := 8)
    (θ := (66104337 / 50000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])

private theorem edge_slepian_r64_k3 :
    HyperEdgeBound 64 3
      (((2318347 / 50000000 : ℚ) : ℝ) * (3 : ℕ) + ((16272637 / 25000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_three_of_rat (by decide)
    (s_lo := (565685424949 / 50000000000))
    (θ := (5577913 / 4000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])

private theorem mom4_slepian_r64_k4 :
    ((67244281 / 2000000000000) : ℚ) ≤
      qMomentLower 4 1 1 1 (20473 / 50000) (3 / 5) sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem edge_slepian_r64_k4 :
    HyperEdgeBound 64 4
      (((2318347 / 50000000 : ℚ) : ℝ) * (4 : ℕ) + ((16272637 / 25000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 1) (m_out := 1) (S_out := 1)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (277128129211 / 20000000000))
    (θ := (142670897 / 100000000))
    (γ_lo := (20473 / 50000)) (B := (3 / 5))
    (I4_lo := (67244281 / 2000000000000))
    (I6_lo := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    mom4_slepian_r64_k4
    (by omega)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r64_k5 :
    ((2035466543 / 2000000000000) : ℚ) ≤
      qMomentLower 4 2 3 7 (333 / 883) (47 / 10) sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem edge_slepian_r64_k5 :
    HyperEdgeBound 64 5
      (((2318347 / 50000000 : ℚ) : ℝ) * (5 : ℕ) + ((16272637 / 25000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 2) (m_out := 3) (S_out := 7)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := 16)
    (θ := (144595881 / 100000000))
    (γ_lo := (333 / 883)) (B := (47 / 10))
    (I4_lo := (2035466543 / 2000000000000))
    (I6_lo := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    mom4_slepian_r64_k5
    (by omega)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r64_k6 :
    ((4133382621 / 5000000000000) : ℚ) ≤
      qMomentLower 4 2 3 7 (17 / 48) (23 / 5) sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem mom6_j1_slepian_r64_k6 :
    ((5727557332543357 / 50000000000000) : ℚ) ≤ qIntOdd
      (qPolyMul ((qPolyPow (qExpOddPoly 3 (1 / (2 * (7 : ℚ)))) 7).take 17)
        (qPolyPow (qInnerPoly 2 (17 / 48)) 6)) 6 (23 / 5) := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem mom6_j2_slepian_r64_k6 :
    ((-11453349731907279 / 100000000000000) : ℚ) ≤ qIntOdd
      (qPolyMul
        (((qPolyPow (qExpOddPoly 3 (1 / (2 * (7 : ℚ)))) 7).drop 17).take 17)
        (qPolyPow (qInnerPoly 2 (17 / 48)) 6)) 40 (23 / 5) := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem mom6_j3_slepian_r64_k6 :
    ((921794251 / 100000000000000) : ℚ) ≤ qIntOdd
      (qPolyMul
        (((qPolyPow (qExpOddPoly 3 (1 / (2 * (7 : ℚ)))) 7).drop 17).drop 17)
        (qPolyPow (qInnerPoly 2 (17 / 48)) 6)) 74 (23 / 5) := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem mom6_slepian_r64_k6 :
    ((56834371 / 1000000000000) : ℚ) ≤
      qMomentLower 6 2 3 7 (17 / 48) (23 / 5) sqrtTwoPiHi :=
  le_qMomentLower_of_split17 mom6_j1_slepian_r64_k6 mom6_j2_slepian_r64_k6 mom6_j3_slepian_r64_k6
    (by norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi])

private theorem edge_slepian_r64_k6 :
    HyperEdgeBound 64 6
      (((2318347 / 50000000 : ℚ) : ℝ) * (6 : ℕ) + ((16272637 / 25000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 2) (m_out := 3) (S_out := 7)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (1788854381999 / 100000000000))
    (θ := (9119433 / 6250000))
    (γ_lo := (17 / 48)) (B := (23 / 5))
    (I4_lo := (4133382621 / 5000000000000))
    (I6_lo := (56834371 / 1000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    mom4_slepian_r64_k6
    (fun _ => mom6_slepian_r64_k6)
    (by norm_num [Nat.choose, piLo])

private theorem mom4_slepian_r64_k7 :
    ((155505707 / 10000000000000) : ℚ) ≤
      qMomentLower 4 1 1 1 (6733 / 20000) (3 / 5) sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem mom6_slepian_r64_k7 :
    ((930741 / 10000000000000) : ℚ) ≤
      qMomentLower 6 1 1 1 (6733 / 20000) (3 / 5) sqrtTwoPiHi := by
  norm_num [qMomentLower, take_17, drop_17, qPolyPow_seven, qPolyPow_six,
      qPolyPow_five, qPolyPow_four, qPolyPow_three, qPolyPow_two, qPolyPow_one,
      qPolyMul, qPolyScale, qPolyAdd, qInnerPoly, qExpOddPoly, qIntOdd, qEval,
      List.range, List.range.loop, List.map, Nat.factorial, sqrtTwoPiHi]

private theorem edge_slepian_r64_k7 :
    HyperEdgeBound 64 7
      (((2318347 / 50000000 : ℚ) : ℝ) * (7 : ℕ) + ((16272637 / 25000000 : ℚ) : ℝ)) :=
  hyperEdgeBound_slepian_of_rat (m_in := 1) (m_out := 1) (S_out := 1)
    (by decide) (by decide) (by decide) (by decide)
    (s_lo := (979795897113 / 50000000000))
    (θ := (18360289 / 12500000))
    (γ_lo := (6733 / 20000)) (B := (3 / 5))
    (I4_lo := (155505707 / 10000000000000))
    (I6_lo := (930741 / 10000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num [qCosUpper, qCosPoly, qCosErr, piLo])
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    (by norm_num [qEval, qExpOddPoly, List.range, List.range.loop, List.map, Nat.factorial])
    mom4_slepian_r64_k7
    (fun _ => mom6_slepian_r64_k7)
    (by norm_num [Nat.choose, piLo])

/-- Verified dual-LP certificate at `r = 64` (`K₀ = 7`). -/
theorem cert_r64_slepian :
    HyperDualCert 64 7 (2318347 / 50000000 : ℚ) (16272637 / 25000000 : ℚ) where
  hr := by decide
  hK₀ := by decide
  ha := by norm_num
  h2 := by norm_num
  htail := by norm_num
  hdenom := by norm_num
  hnum := by norm_num
  hedge := by
    intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk2, hkK⟩
    interval_cases k
    · exact edge_slepian_r64_k2
    · exact edge_slepian_r64_k3
    · exact edge_slepian_r64_k4
    · exact edge_slepian_r64_k5
    · exact edge_slepian_r64_k6
    · exact edge_slepian_r64_k7

end Cslib.Circuits.Frontier.Hypergraph
