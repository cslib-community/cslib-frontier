/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.Bounds
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity

/-!
# Explicit Parameter Bounds for Johnson-Bound Proximity Gaps

Analytic `(m, D)` parameter selection bridging real Johnson-bound error gaps
`1 - √ρ - η` to the explicit natural-number `johnsonCurveBound` and `Sudan.monomials`
interpolation inequality.

## Main results

* `Cslib.Code.ProximityGap.johnsonCurveBound_mul_le`: affine weight-scaling inequality.
* `Cslib.Code.ProximityGap.johnson_curve_params_bound`: explicit curve multiplicity bound.
* `Cslib.Code.ProximityGap.johnson_line_params_bound`: specialization to affine lines (`r = 1`).
* `Cslib.Code.ProximityGap.exists_multiplicity_of_eta`: converts a real gap `η > 0` to `m ≥ 1`.
-/

namespace Cslib.Code.ProximityGap

open Cslib.Code Finset

section ParameterHelpers

private theorem card_monomials_zero (D : ℕ) : #(Sudan.monomials 0 D) = (D + 1) ^ 2 := by
  have heq : Sudan.monomials 0 D = range (D + 1) ×ˢ range (D + 1) := by
    ext ⟨a, b⟩
    simp only [Sudan.mem_monomials, mem_product, mem_range, Nat.lt_succ_iff, zero_mul, add_zero]
    tauto
  rw [heq, card_product, card_range, sq]

private theorem maxYDeg_zero_le (D : ℕ) : maxYDeg 0 D ≤ D :=
  Finset.sup_le fun _ hab => (Sudan.mem_monomials.1 hab).2.1

private theorem mul_maxYDeg_le (d D : ℕ) : d * maxYDeg d D ≤ D := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · refine (Nat.mul_le_mul_left d (Finset.sup_le fun ab hab => ?_)).trans (Nat.mul_div_le D d)
    exact (Nat.le_div_iff_mul_le hd).2 (by linarith [(Sudan.mem_monomials.1 hab).2.2])

private theorem two_mul_cast_mul_div_two_le (n a : ℕ) :
    2 * ((n * (a * (a + 1) / 2) : ℕ) : ℝ) ≤ (n : ℝ) * ((a : ℝ) * (a + 1)) := by
  have : 2 * (n * (a * (a + 1) / 2)) ≤ n * (a * (a + 1)) := by
    rw [Nat.mul_left_comm]; exact Nat.mul_le_mul_left n (Nat.mul_div_le _ 2)
  exact_mod_cast this

private theorem sqrt_rate_bounds {n k : ℕ} {ρ : ℝ} (hρ : ρ = (k : ℝ) / (n : ℝ))
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    0 < ρ ∧ ρ ≤ 1 ∧ 0 < Real.sqrt ρ ∧ Real.sqrt ρ ≤ 1 ∧ Real.sqrt ρ ^ 2 = ρ ∧
    (1 : ℝ) ≤ 1 / Real.sqrt ρ ∧ 1 / Real.sqrt ρ ≤ 1 / ρ ∧ 1 / Real.sqrt ρ ≤ (n : ℝ) := by
  subst hρ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hρ_pos : 0 < (k : ℝ) / n := by positivity
  have hρ_le_one : (k : ℝ) / n ≤ 1 := (div_le_one hnR).2 (by exact_mod_cast hkn)
  have hsq_pos : 0 < Real.sqrt ((k : ℝ) / n) := Real.sqrt_pos.2 hρ_pos
  have hsq_le : Real.sqrt ((k : ℝ) / n) ≤ 1 := Real.sqrt_le_one.2 hρ_le_one
  have hsq_sq : Real.sqrt ((k : ℝ) / n) ^ 2 = (k : ℝ) / n := Real.sq_sqrt hρ_pos.le
  refine ⟨hρ_pos, hρ_le_one, hsq_pos, hsq_le, hsq_sq, (one_le_div hsq_pos).2 hsq_le, ?_, ?_⟩
  · rw [div_le_div_iff₀ hsq_pos hρ_pos, one_mul, one_mul]
    calc (k : ℝ) / n = Real.sqrt ((k : ℝ) / n) * Real.sqrt ((k : ℝ) / n) := by rw [← sq, hsq_sq]
      _ ≤ Real.sqrt ((k : ℝ) / n) := mul_le_of_le_one_right hsq_pos.le hsq_le
  · refine le_of_sq_le_sq ?_ hnR.le
    rw [div_pow, one_pow, hsq_sq, one_div_div, div_le_iff₀ hkR, sq, mul_assoc]
    exact le_mul_of_one_le_right hnR.le
      (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hk.trans hkn) (by exact_mod_cast hk))

private theorem johnson_monomial_gap {n k m : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hm : 1 ≤ m) :
    let m' := m + 1
    let t₀ := ⌈(1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * k)⌉₊
    let D := m' * t₀ - 1
    n * (m' * (m' + 1) / 2) < #(Sudan.monomials (k - 1) D) ∧
      (5 / 8) * (n : ℝ) < ((#(Sudan.monomials (k - 1) D) - n * (m' * (m' + 1) / 2) : ℕ) : ℝ) := by
  set m' := m + 1
  set t₀ := ⌈(1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * k)⌉₊
  set D := m' * t₀ - 1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm'R : (0 : ℝ) < m' := by positivity
  have h1_le_t₀ : 1 ≤ t₀ := Nat.one_le_ceil_iff.2 (by positivity)
  have hD_succ : D + 1 = m' * t₀ := by
    have : 1 ≤ m' * t₀ := Nat.mul_pos (by omega) h1_le_t₀; omega
  have hmt_sq_lower :
      ((m' : ℝ) * (m' + 1) + 5 / 4) * ((n : ℝ) * k) < ((m' : ℝ) * t₀) ^ 2 := by
    have hmul : (m' : ℝ) * (1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * k) ≤
        (m' : ℝ) * t₀ := by
      have := mul_le_mul_of_nonneg_left (Nat.le_ceil _ : _ ≤ (t₀ : ℝ)) hm'R.le; linarith
    have hsq := pow_le_pow_left₀ (by positivity) hmul 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
    have hcoeff : (m' : ℝ) * (m' + 1) + 5 / 4 < ((m' : ℝ) * (1 + 1 / (2 * (m : ℝ)))) ^ 2 := by
      have hm'_cast : (m' : ℝ) = (m : ℝ) + 1 := by exact_mod_cast rfl
      rw [hm'_cast, mul_pow]
      have hdiff : ((m : ℝ) + 1) ^ 2 * (1 + 1 / (2 * m)) ^ 2 -
          (((m : ℝ) + 1) * (m + 1 + 1) + 5 / 4) = (6 * m + 1) / (4 * m ^ 2) := by
        field_simp; ring
      linarith [show (0 : ℝ) < (6 * m + 1) / (4 * m ^ 2) by positivity]
    exact (mul_lt_mul_of_pos_right hcoeff (by positivity)).trans_le hsq
  set R_eq := n * (m' * (m' + 1) / 2); set C_mon := #(Sudan.monomials (k - 1) D)
  have h2Req : 2 * (R_eq : ℝ) ≤ (n : ℝ) * ((m' : ℝ) * (m' + 1)) :=
    two_mul_cast_mul_div_two_le n m'
  have hgap : (R_eq : ℝ) + (5 / 8) * n < C_mon := by
    rcases Nat.eq_or_lt_of_le hk with rfl | hk2
    · have hC : (C_mon : ℝ) = ((m' : ℝ) * t₀) ^ 2 := by
        exact_mod_cast (by rw [show C_mon = #(Sudan.monomials 0 D) from rfl,
          card_monomials_zero, hD_succ] : C_mon = (m' * t₀) ^ 2)
      rw [hC]; simp only [Nat.cast_one, mul_one] at hmt_sq_lower; linarith
    · have hsq_lt : (m' * t₀) ^ 2 < 2 * (k - 1) * C_mon := calc
        (m' * t₀) ^ 2 = (D + 1) * (D + 1) := by rw [sq, hD_succ]
        _ < (D + 1) * (D + 2) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        _ ≤ 2 * (k - 1) * C_mon :=
          Sudan.add_one_mul_add_two_le_two_mul_mul_card_monomials (by omega) D
      have hdR_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < k - 1 by omega)
      have hd_le_k : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      have hstep : (2 * (R_eq : ℝ) + (5 / 4) * n) * ((k - 1 : ℕ) : ℝ) <
          (2 * (C_mon : ℝ)) * ((k - 1 : ℕ) : ℝ) := calc
        _ ≤ (((m' : ℝ) * (m' + 1) + 5 / 4) * n) * ((k - 1 : ℕ) : ℝ) := by gcongr; linarith
        _ ≤ (((m' : ℝ) * (m' + 1) + 5 / 4) * n) * k := by gcongr
        _ = ((m' : ℝ) * (m' + 1) + 5 / 4) * ((n : ℝ) * k) := by ring
        _ < ((m' : ℝ) * t₀) ^ 2 := hmt_sq_lower
        _ < 2 * ((k - 1 : ℕ) : ℝ) * C_mon := by exact_mod_cast hsq_lt
        _ = (2 * (C_mon : ℝ)) * ((k - 1 : ℕ) : ℝ) := by ring
      linarith [lt_of_mul_lt_mul_right hstep hdR_pos.le]
  have hinterp : R_eq < C_mon := by exact_mod_cast (show (R_eq : ℝ) < C_mon by linarith)
  exact ⟨hinterp, by rw [Nat.cast_sub hinterp.le]; linarith⟩

/-- Quantitative gap and degree bounds for `johnson_curve_params_bound`. -/
private theorem johnson_curve_params_gap {n k e m r : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hm : 1 ≤ m)
    (he : (e : ℝ) / (n : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (n : ℝ)) -
        Real.sqrt ((k : ℝ) / (n : ℝ)) / (2 * (m : ℝ))) :
    let ρ := (k : ℝ) / (n : ℝ)
    let m' := m + 1
    let t₀ := ⌈(1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * (k : ℝ))⌉₊
    let D := m' * t₀ - 1
    k ≤ n - e ∧
    n * (m' * (m' + 1) / 2) < #(Sudan.monomials (k - 1) D) ∧
    D < m' * (n - e) ∧
    (D : ℝ) ≤ (5 / 2) * (m' : ℝ) * (n : ℝ) * Real.sqrt ρ ∧
    (maxYDeg (k - 1) D : ℝ) ≤ 5 * (m' : ℝ) / Real.sqrt ρ ∧
    (siegelZDeg n m' (k - 1) D r : ℝ) ≤ 6 * (r : ℝ) * (m' : ℝ) ^ 3 / Real.sqrt ρ := by
  intro ρ m' t₀ D
  obtain ⟨hρ_pos, _, hsqρ_pos, _, hsqρ_sq, _⟩ :=
    sqrt_rate_bounds (rfl : ρ = (k : ℝ) / n) hk hkn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm'R : (0 : ℝ) < m' := by positivity
  have hsqnk_eq : Real.sqrt ((n : ℝ) * k) = (n : ℝ) * Real.sqrt ρ := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), mul_pow, hsqρ_sq]
    dsimp only [ρ]; field_simp
  have hmul_he : (e : ℝ) ≤ n - (1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * k) := by
    have h1 := (div_le_iff₀ hnR).1 he
    rw [hsqnk_eq]
    linarith [show (1 - Real.sqrt ρ - Real.sqrt ρ / (2 * m)) * n =
      n - (1 + 1 / (2 * m)) * (n * Real.sqrt ρ) by field_simp; ring]
  have he_le_n : e ≤ n := (Nat.cast_le (α := ℝ)).1 (by
    linarith [show (0 : ℝ) < (1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * k) by positivity])
  have ht₀_le_sub : t₀ ≤ n - e :=
    Nat.ceil_le.2 (by rw [Nat.cast_sub he_le_n]; linarith)
  have hk_sqrt : (k : ℝ) ≤ Real.sqrt ((n : ℝ) * k) :=
    Real.le_sqrt_of_sq_le (by rw [sq]; gcongr)
  have hk_le_t₀ : k ≤ t₀ := by
    have : Real.sqrt ((n : ℝ) * k) ≤ (1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * k) :=
      le_mul_of_one_le_left (Real.sqrt_nonneg _) (le_add_of_nonneg_right (by positivity))
    exact Nat.cast_le.1 ((hk_sqrt.trans this).trans (Nat.le_ceil _))
  have hroot : D < m' * (n - e) := by
    have : 1 ≤ m' * t₀ := Nat.mul_pos (by omega) (hk.trans hk_le_t₀)
    have := Nat.mul_le_mul_left m' ht₀_le_sub; omega
  obtain ⟨hinterp, hdiff_lower⟩ := johnson_monomial_gap hk hkn hm
  have hD_upper : (D : ℝ) ≤ (5 / 2) * (m' : ℝ) * n * Real.sqrt ρ := by
    have hsq1 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) * k) :=
      (by exact_mod_cast hk : (1 : ℝ) ≤ k).trans hk_sqrt
    have hlt := Nat.ceil_lt_add_one (a := (1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * k))
      (by positivity)
    have hhalf : 1 + 1 / (2 * (m : ℝ)) ≤ 3 / 2 := by
      have : 1 / (2 * (m : ℝ)) ≤ 1 / 2 := by gcongr; linarith [(by exact_mod_cast hm : (1 : ℝ) ≤ m)]
      linarith
    have ht_up : (t₀ : ℝ) ≤ (5 / 2) * Real.sqrt ((n : ℝ) * k) := by
      linarith [mul_le_mul_of_nonneg_right hhalf (Real.sqrt_nonneg ((n : ℝ) * k))]
    have hD_le : (D : ℝ) ≤ (m' : ℝ) * t₀ := by exact_mod_cast (show D ≤ m' * t₀ by omega)
    have := mul_le_mul_of_nonneg_left ht_up hm'R.le
    rw [hsqnk_eq] at this; linarith
  have hDY_upper : (maxYDeg (k - 1) D : ℝ) ≤ 5 * (m' : ℝ) / Real.sqrt ρ := by
    rcases Nat.eq_or_lt_of_le hk with rfl | hk2
    · have hle : (maxYDeg (1 - 1) D : ℝ) ≤ D := by exact_mod_cast maxYDeg_zero_le D
      have hρ1 : (n : ℝ) * Real.sqrt ρ = 1 / Real.sqrt ρ := by
        rw [eq_div_iff hsqρ_pos.ne', mul_assoc, ← sq, hsqρ_sq]
        dsimp only [ρ]; push_cast; field_simp
      refine (hle.trans hD_upper).trans ?_
      rw [mul_assoc ((5 / 2) * (m' : ℝ)), hρ1, ← div_eq_mul_one_div]
      exact div_le_div_of_nonneg_right (by linarith) hsqρ_pos.le
    · have hmulR : ((k - 1 : ℕ) : ℝ) * (maxYDeg (k - 1) D : ℝ) ≤ D := by
        exact_mod_cast mul_maxYDeg_le (k - 1) D
      have hk_half : (k : ℝ) / 2 ≤ ((k - 1 : ℕ) : ℝ) := by
        have : (k : ℝ) ≤ 2 * ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show k ≤ 2 * (k - 1) by omega)
        linarith
      have h1 : (k : ℝ) / 2 * (maxYDeg (k - 1) D : ℝ) ≤ (5 / 2) * m' * n * Real.sqrt ρ :=
        (mul_le_mul_of_nonneg_right hk_half (by positivity)).trans (hmulR.trans hD_upper)
      rw [le_div_iff₀ hsqρ_pos]
      have h2 := mul_le_mul_of_nonneg_right h1 hsqρ_pos.le
      have hsqeq : (5 / 2) * (m' : ℝ) * n * Real.sqrt ρ * Real.sqrt ρ = (5 / 2) * m' * k := by
        calc (5 / 2) * (m' : ℝ) * n * Real.sqrt ρ * Real.sqrt ρ
            = (5 / 2) * (m' : ℝ) * n * (Real.sqrt ρ ^ 2) := by ring
          _ = (5 / 2) * m' * k := by rw [hsqρ_sq]; dsimp only [ρ]; field_simp
      exact le_of_mul_le_mul_left (by linarith) hkR
  have hBZ_upper :
      (siegelZDeg n m' (k - 1) D r : ℝ) ≤ 6 * (r : ℝ) * (m' : ℝ) ^ 3 / Real.sqrt ρ := by
    set R_eq := n * (m' * (m' + 1) / 2); set C_mon := #(Sudan.monomials (k - 1) D)
    have hdiff_pos : (0 : ℝ) < ((C_mon - R_eq : ℕ) : ℝ) := by linarith
    have hdiv_le : (siegelZDeg n m' (k - 1) D r : ℝ) ≤
        (r : ℝ) * ((R_eq : ℝ) * (maxYDeg (k - 1) D : ℝ)) / ((C_mon - R_eq : ℕ) : ℝ) := by
      rw [le_div_iff₀ hdiff_pos]
      have hcast : ((siegelZDeg n m' (k - 1) D r * (C_mon - R_eq) : ℕ) : ℝ) ≤
          ((R_eq * r * maxYDeg (k - 1) D : ℕ) : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self (R_eq * r * maxYDeg (k - 1) D) (C_mon - R_eq)
      push_cast at hcast; linarith
    have hReq_up : (R_eq : ℝ) ≤ (3 / 4) * (n : ℝ) * (m' : ℝ) ^ 2 := by
      have h2Req : 2 * (R_eq : ℝ) ≤ (n : ℝ) * ((m' : ℝ) * (m' + 1)) :=
        two_mul_cast_mul_div_two_le n m'
      have hm2 : (2 : ℝ) ≤ m' := by exact_mod_cast (show 2 ≤ m' by omega)
      linarith [mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by linarith : (m' : ℝ) + 1 ≤ 3 / 2 * m') hm'R.le) hnR.le,
        show (n : ℝ) * ((m' : ℝ) * (3 / 2 * m')) = 2 * ((3 / 4) * n * m' ^ 2) by ring]
    have hfrac : (r : ℝ) * ((R_eq : ℝ) * (maxYDeg (k - 1) D : ℝ)) / ((C_mon - R_eq : ℕ) : ℝ) ≤
        (r : ℝ) * ((3 / 4 * n * (m' : ℝ) ^ 2) * (5 * m' / Real.sqrt ρ)) / (5 / 8 * n) :=
      div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left (mul_le_mul hReq_up hDY_upper (by positivity) (by positivity))
          (by positivity)) (by positivity) hdiff_lower.le
    exact hdiv_le.trans (hfrac.trans_eq (by field_simp; ring))
  exact ⟨hk_le_t₀.trans ht₀_le_sub, hinterp, hroot, hD_upper, hDY_upper, hBZ_upper⟩

end ParameterHelpers

public section

/-- Weight scaling for `johnsonCurveBound`: since `johnsonCurveBound` is affine in `W_tot` with
nonnegative coefficients, increasing the weight budget from `n` to `W_tot ≥ n` scales the bound by
at most `W_tot / n`. -/
theorem johnsonCurveBound_mul_le {n m d D r W_tot : ℕ} (hW : n ≤ W_tot) :
    johnsonCurveBound n m d D r W_tot * n ≤ johnsonCurveBound n m d D r n * W_tot := by
  dsimp only [johnsonCurveBound]
  have hA : (siegelZDeg n m d D r + 2 * maxYDeg d D * (D + siegelZDeg n m d D r)) * n ≤
      (siegelZDeg n m d D r + 2 * maxYDeg d D * (D + siegelZDeg n m d D r)) * W_tot :=
    Nat.mul_le_mul_left _ hW
  linarith

/-- Quantitative Guruswami–Sudan parameter packaging for degree-`r` curves (`1 ≤ r`): given
`1 ≤ k ≤ n`, `1 ≤ m`, and `(e : ℝ) / n ≤ 1 - √ρ - √ρ / (2 * m)` with `ρ = k / n`, the choice
`m' = m + 1`, `t₀ = ⌈(1 + 1 / (2 * m)) * √(n * k)⌉₊`, `D = m' * t₀ - 1` satisfies all hypotheses of
`Cslib.Code.exists_correlatedAgreement_curve_johnson` and yields
`(johnsonCurveBound n m' (k - 1) D r n : ℝ) ≤ 1800 * r * (m + 1) ^ 6 * n ^ 2 / ρ`. -/
theorem johnson_curve_params_bound {n k e m r : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hm : 1 ≤ m) (hr : 1 ≤ r)
    (he : (e : ℝ) / (n : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (n : ℝ)) -
        Real.sqrt ((k : ℝ) / (n : ℝ)) / (2 * (m : ℝ))) :
    let m' := m + 1
    let t₀ := ⌈(1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * (k : ℝ))⌉₊
    let D := m' * t₀ - 1
    k ≤ n - e ∧
    n * (m' * (m' + 1) / 2) < #(Sudan.monomials (k - 1) D) ∧
    D < m' * (n - e) ∧
    (johnsonCurveBound n m' (k - 1) D r n : ℝ) ≤
      1800 * (r : ℝ) * ((m + 1 : ℝ) ^ 6) * ((n : ℝ) ^ 2) / ((k : ℝ) / (n : ℝ)) := by
  intro m' t₀ D
  obtain ⟨hk_le_sub, hinterp, hroot, hD_upper, hDY_upper, hBZ_upper⟩ :=
    johnson_curve_params_gap (r := r) hk hkn hm he
  set ρ := (k : ℝ) / n
  obtain ⟨hρ_pos, _, hsqρ_pos, _, hsqρ_sq, h1_le_invsq, hinvsq_le_invρ, hinvsq_le_n⟩ :=
    sqrt_rate_bounds (rfl : ρ = (k : ℝ) / n) hk hkn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have h1_le_n : (1 : ℝ) ≤ n := by exact_mod_cast hk.trans hkn
  have h1_le_r : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h1_le_m' : (1 : ℝ) ≤ (m' : ℝ) := by exact_mod_cast (show 1 ≤ m' by omega)
  have h1_le_invρ : (1 : ℝ) ≤ 1 / ρ := h1_le_invsq.trans hinvsq_le_invρ
  have h1_le_n2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ h1_le_n
  have hn_le_n2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := le_self_pow₀ h1_le_n two_ne_zero
  have hm'p (a : ℕ) (ha : a ≤ 6) : (m' : ℝ) ^ a ≤ (m' : ℝ) ^ 6 := pow_le_pow_right₀ h1_le_m' ha
  set D_Y := maxYDeg (k - 1) D; set B_Z := siegelZDeg n m' (k - 1) D r
  set U := (m' : ℝ) ^ 6 * (n : ℝ) ^ 2 * (1 / ρ)
  have hm'2 := hm'p 2 (by norm_num); have hm'3 := hm'p 3 (by norm_num)
  have hm'4 := hm'p 4 (by norm_num)
  have ht1 : (B_Z : ℝ) ≤ 6 * r * U := calc
    _ ≤ 6 * r * ((m' : ℝ) ^ 3 * (1 * (1 / Real.sqrt ρ))) := by
        linarith [hBZ_upper, show 6 * (r : ℝ) * ((m' : ℝ) ^ 3 * (1 * (1 / Real.sqrt ρ))) =
          6 * r * (m' : ℝ) ^ 3 / Real.sqrt ρ by ring]
    _ ≤ 6 * r * ((m' : ℝ) ^ 6 * ((n : ℝ) ^ 2 * (1 / ρ))) := by gcongr
    _ = 6 * r * U := by ring
  have ht2 : 2 * (D_Y : ℝ) * D ≤ 25 * r * U := by
    have hprod := mul_le_mul hDY_upper hD_upper (by positivity) (by positivity)
    rw [show (5 * (m' : ℝ) / Real.sqrt ρ) * ((5 / 2) * m' * n * Real.sqrt ρ) =
      (25 / 2) * (m' : ℝ) ^ 2 * (n * 1) by field_simp; ring] at hprod
    have hmono : (m' : ℝ) ^ 2 * ((n : ℝ) * 1) ≤ (m' : ℝ) ^ 6 * ((n : ℝ) ^ 2 * (1 / ρ)) := by gcongr
    calc 2 * (D_Y : ℝ) * D ≤ 25 * 1 * U := by linarith
      _ ≤ 25 * (r : ℝ) * U := by gcongr
  have ht3 : 2 * (D_Y : ℝ) * B_Z ≤ 60 * r * U := by
    have hprod := mul_le_mul hDY_upper hBZ_upper (by positivity) (by positivity)
    rw [div_mul_div_comm, show Real.sqrt ρ * Real.sqrt ρ = ρ from by rw [← sq, hsqρ_sq]] at hprod
    have hmono : (m' : ℝ) ^ 4 * (1 * (1 / ρ)) ≤ (m' : ℝ) ^ 6 * ((n : ℝ) ^ 2 * (1 / ρ)) := by gcongr
    have hmono' : 60 * (r : ℝ) * ((m' : ℝ) ^ 4 * (1 * (1 / ρ))) ≤
        60 * (r : ℝ) * ((m' : ℝ) ^ 6 * ((n : ℝ) ^ 2 * (1 / ρ))) := by gcongr
    calc 2 * (D_Y : ℝ) * B_Z ≤ 60 * r * ((m' : ℝ) ^ 4 * (1 * (1 / ρ))) := by
          linarith [show 2 * ((5 * (m' : ℝ) * (6 * r * m' ^ 3)) / ρ) =
            60 * r * (m' ^ 4 * (1 * (1 / ρ))) by ring]
      _ ≤ 60 * r * U := hmono'.trans_eq (by dsimp only [U]; ring)
  have ht4 : 4 * (n : ℝ) * (D_Y : ℝ) ^ 2 * D * B_Z ≤ 1500 * r * U := by
    have hmul := mul_le_mul_of_nonneg_left
      (mul_le_mul (pow_le_pow_left₀ (by positivity) hDY_upper 2)
        (mul_le_mul hD_upper hBZ_upper (by positivity) (by positivity))
        (by positivity) (by positivity))
      (show (0 : ℝ) ≤ 4 * n by positivity)
    have hrhs : 4 * (n : ℝ) * ((5 * m' / Real.sqrt ρ) ^ 2 * (((5 / 2) * m' * n * Real.sqrt ρ) *
        (6 * r * m' ^ 3 / Real.sqrt ρ))) = 1500 * r * U := by
      dsimp only [U]; rw [div_pow, hsqρ_sq]; field_simp; ring
    linarith
  have ht5 : (n : ℝ) * (D_Y : ℝ) ^ 2 * ((r : ℝ) * D_Y) ≤ 125 * r * U := by
    have hDY3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hDY_upper 3) hnR.le
    rw [div_pow, show Real.sqrt ρ ^ 3 = ρ * Real.sqrt ρ by rw [pow_succ, hsqρ_sq]] at hDY3
    have hn_inv : (n : ℝ) * (1 / Real.sqrt ρ) ≤ (n : ℝ) ^ 2 :=
      (mul_le_mul_of_nonneg_left hinvsq_le_n hnR.le).trans_eq (sq _).symm
    have hbase : (n : ℝ) * (D_Y : ℝ) ^ 3 ≤ 125 * U := by
      have hmono : (m' : ℝ) ^ 3 * (n * (1 / Real.sqrt ρ)) * (1 / ρ) ≤
          (m' : ℝ) ^ 6 * (n : ℝ) ^ 2 * (1 / ρ) := by gcongr
      linarith [show (n : ℝ) * ((5 * m') ^ 3 / (ρ * Real.sqrt ρ)) =
        125 * ((m' : ℝ) ^ 3 * (n * (1 / Real.sqrt ρ)) * (1 / ρ)) by field_simp; ring]
    linarith [mul_le_mul_of_nonneg_left hbase (show (0 : ℝ) ≤ r by positivity)]
  refine ⟨hk_le_sub, hinterp, hroot, ?_⟩
  have hcast : (johnsonCurveBound n m' (k - 1) D r n : ℝ) =
      (B_Z : ℝ) + 2 * D_Y * D + 2 * D_Y * B_Z + 4 * n * D_Y ^ 2 * D * B_Z +
        n * D_Y ^ 2 * (r * D_Y) := by
    simp only [johnsonCurveBound, D_Y, B_Z]; push_cast; ring
  rw [hcast, show 1800 * (r : ℝ) * ((m + 1 : ℝ) ^ 6) * ((n : ℝ) ^ 2) / ((k : ℝ) / n) =
    1800 * r * U by dsimp only [U, m', ρ]; push_cast; ring]
  have : 0 ≤ (r : ℝ) * U := by positivity
  linarith only [ht1, ht2, ht3, ht4, ht5, this]

/-- Quantitative Guruswami–Sudan parameter packaging for affine lines (`r = 1`), specializing
`johnson_curve_params_bound`. -/
theorem johnson_line_params_bound {n k e m : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hm : 1 ≤ m)
    (he : (e : ℝ) / (n : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (n : ℝ)) -
        Real.sqrt ((k : ℝ) / (n : ℝ)) / (2 * (m : ℝ))) :
    let m' := m + 1
    let t₀ := ⌈(1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * (k : ℝ))⌉₊
    let D := m' * t₀ - 1
    k ≤ n - e ∧
    n * (m' * (m' + 1) / 2) < #(Sudan.monomials (k - 1) D) ∧
    D < m' * (n - e) ∧
    (johnsonCurveBound n m' (k - 1) D 1 n : ℝ) ≤
      1800 * ((m + 1 : ℝ) ^ 6) * ((n : ℝ) ^ 2) / ((k : ℝ) / (n : ℝ)) := by
  simpa only [Nat.cast_one, mul_one] using
    johnson_curve_params_bound (r := 1) hk hkn hm le_rfl he

/-- Multiplicity selection for an arbitrary gap `η > 0` below the Johnson bound `1 - √ρ`: given
`1 ≤ k ≤ n`, `0 < η`, and `(e : ℝ) / n ≤ 1 - √(k / n) - η`, choosing
`m = ⌈√ρ / (2 * min η (√ρ / 2))⌉₊` yields `1 ≤ m`,
`(e : ℝ) / n ≤ 1 - √(k / n) - √(k / n) / (2 * m)`, and `(m + 1 : ℝ) ^ 6 ≤ 64 / η ^ 6`. -/
theorem exists_multiplicity_of_eta {n k e : ℕ} {η : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hη : 0 < η)
    (he : (e : ℝ) / (n : ℝ) ≤ 1 - Real.sqrt ((k : ℝ) / (n : ℝ)) - η) :
    ∃ m : ℕ, 1 ≤ m ∧
      (e : ℝ) / (n : ℝ) ≤
        1 - Real.sqrt ((k : ℝ) / (n : ℝ)) -
          Real.sqrt ((k : ℝ) / (n : ℝ)) / (2 * (m : ℝ)) ∧
      ((m + 1 : ℝ) ^ 6) ≤ 64 / (η ^ 6) := by
  set ρ := (k : ℝ) / n
  obtain ⟨_, _, hsqρ_pos, hsqρ_le_one, _⟩ := sqrt_rate_bounds (rfl : ρ = (k : ℝ) / n) hk hkn
  set η' := min η (Real.sqrt ρ / 2)
  have hη'_pos : 0 < η' := lt_min hη (by positivity)
  set m := ⌈Real.sqrt ρ / (2 * η')⌉₊
  have hx1 : (1 : ℝ) ≤ Real.sqrt ρ / (2 * η') :=
    (one_le_div (by positivity)).2 (by linarith [min_le_right η (Real.sqrt ρ / 2)])
  have hm : 1 ≤ m := by exact_mod_cast hx1.trans (Nat.le_ceil _)
  have hfrac : Real.sqrt ρ / (2 * m) ≤ η := by
    have hceil : Real.sqrt ρ / (2 * η') ≤ (m : ℝ) := Nat.le_ceil _
    have : Real.sqrt ρ / (2 * m) ≤ η' :=
      (div_le_iff₀ (by positivity)).2 (by linarith [(div_le_iff₀ (by positivity)).1 hceil])
    exact this.trans (min_le_left _ _)
  have hm1_le : (m : ℝ) + 1 ≤ 2 / η := by
    by_cases hle : η ≤ Real.sqrt ρ / 2
    · have hη'_eq : η' = η := min_eq_left hle
      have hlt : (m : ℝ) < Real.sqrt ρ / (2 * η) + 1 := by
        have h0 := Nat.ceil_lt_add_one (a := Real.sqrt ρ / (2 * η')) (by positivity)
        change (m : ℝ) < _ at h0; rwa [hη'_eq] at h0
      have hx1' : (1 : ℝ) ≤ Real.sqrt ρ / (2 * η) := by rwa [hη'_eq] at hx1
      have : 3 * (Real.sqrt ρ / (2 * η)) ≤ 2 / η := by
        rw [show 3 * (Real.sqrt ρ / (2 * η)) = (3 / 2 * Real.sqrt ρ) / η by ring]
        exact div_le_div_of_nonneg_right (by linarith) hη.le
      linarith
    · have hη'_eq : η' = Real.sqrt ρ / 2 := min_eq_right (le_of_not_ge hle)
      have hm1 : m = 1 := by
        dsimp only [m]; rw [hη'_eq, show Real.sqrt ρ / (2 * (Real.sqrt ρ / 2)) = 1 by field_simp]
        norm_num
      rw [hm1, Nat.cast_one, le_div_iff₀ hη]
      linarith [show (0 : ℝ) ≤ (e : ℝ) / n by positivity]
  refine ⟨m, hm, by linarith, (pow_le_pow_left₀ (by positivity) hm1_le 6).trans_eq ?_⟩
  rw [div_pow]; norm_num

end

end Cslib.Code.ProximityGap
