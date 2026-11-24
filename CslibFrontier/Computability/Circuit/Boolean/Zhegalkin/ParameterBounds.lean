/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Log
import Cslib.Foundations.Data.Nat.Asymptotics
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Internal logarithmic parameter estimates for asymptotic bounds

Internal parameter selection and remainder estimates (`exists_log_threshold`, `log_param_props`,
`div_two_sub_add_rem_le`, `Additive.matrixRem_mul_sq_le`, `Boolean.Zhegalkin.zhegRem_mul_sq_le`)
consumed by `AdditiveBound` and `UpperBound`; never re-exported through `Zhegalkin`.

## Main results

* `Cslib.Circuits.exists_log_threshold`, `log_param_props`, `div_two_sub_add_rem_le`,
  `Cslib.Circuits.Additive.matrixRem_mul_sq_le`,
  `Cslib.Circuits.Boolean.Zhegalkin.zhegRem_mul_sq_le`: logarithmic parameter bounds and
  remainder estimates.
-/

public section

namespace Cslib.Circuits

section ParameterBounds

private theorem ceilDiv_div_sq_add_one_le (k : ℕ) {L : ℕ} (hL : 0 < L) :
    k ⌈/⌉ (k / L ^ 2 + 1) ≤ L ^ 2 := by
  have hp : 0 < k / L ^ 2 + 1 := Nat.succ_pos _
  rw [ceilDiv_le_iff_le_smul hp, smul_eq_mul]
  have hmod : k % L ^ 2 < L ^ 2 := Nat.mod_lt k (by positivity)
  have hdiv := Nat.div_add_mod k (L ^ 2)
  have hexp : (k / L ^ 2 + 1) * L ^ 2 = L ^ 2 * (k / L ^ 2) + L ^ 2 := by ring
  linarith

private theorem mul_ceilDiv_le_add (N : ℕ) {s : ℕ} (hs : 0 < s) :
    s * (N ⌈/⌉ s) ≤ N + s := by
  have hceil : N ⌈/⌉ s ≤ N / s + 1 := by
    rw [ceilDiv_le_iff_le_smul hs, smul_eq_mul]
    have hmod : N % s < s := Nat.mod_lt N hs
    have hdiv := Nat.div_add_mod N s
    have hexp : s * (N / s + 1) = s * (N / s) + s := by ring
    linarith
  calc s * (N ⌈/⌉ s) ≤ s * (N / s + 1) := Nat.mul_le_mul_left s hceil
    _ = s * (N / s) + s := by ring
    _ ≤ N + s := Nat.add_le_add_right (Nat.mul_div_le N s) s

theorem exists_log_threshold (C : ℕ) :
    ∃ L₁ : ℕ, 8 ≤ L₁ ∧ C ≤ L₁ ∧
      ∀ {L : ℕ}, L₁ ≤ L → C * Nat.log 2 L ≤ L ∧ 6 * Nat.log 2 L ≤ L ∧ L ^ 2 ≤ 2 ^ L := by
  have hev := (Filter.eventually_ge_atTop (max 8 C)).and
    ((Nat.eventually_mul_log_le (max C 6) one_lt_two).and
      (Nat.eventually_mul_pow_le_pow 1 2 one_lt_two))
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨hge₀, _, _⟩ := hL₁ L₁ le_rfl
  refine ⟨L₁, le_trans (le_max_left 8 C) hge₀, le_trans (le_max_right 8 C) hge₀,
    fun {L} hL => ?_⟩
  obtain ⟨_, hlog, hpow⟩ := hL₁ L hL
  refine ⟨?_, ?_, by simpa only [one_mul] using hpow⟩
  · exact (Nat.mul_le_mul_right _ (le_max_left C 6)).trans hlog
  · exact (Nat.mul_le_mul_right _ (le_max_right C 6)).trans hlog

theorem log_param_props {M : ℕ} (hL8 : 8 ≤ Nat.log 2 M)
    (hlog6 : 6 * Nat.log 2 (Nat.log 2 M) ≤ Nat.log 2 M)
    (hpow2 : (Nat.log 2 M) ^ 2 ≤ 2 ^ Nat.log 2 M) :
    let L := Nat.log 2 M
    let s := L - 3 * Nat.log 2 L
    0 < s ∧ s ≤ L ∧ L ≤ 2 * s ∧ 1 ≤ Nat.log 2 L ∧ L ^ 2 ≤ M ∧ L ^ 3 * 2 ^ s ≤ 8 * M := by
  dsimp only
  set L := Nat.log 2 M
  set s := L - 3 * Nat.log 2 L
  have hM0 : M ≠ 0 := by
    intro h0
    subst h0
    simp [L] at hL8
  have hpowM : 2 ^ L ≤ M := Nat.pow_log_le_self 2 hM0
  have hs_pos : 0 < s := by omega
  have hs_le : s ≤ L := Nat.sub_le _ _
  have hL_2s : L ≤ 2 * s := by omega
  have hlogL1 : 1 ≤ Nat.log 2 L :=
    Nat.le_log_of_pow_le one_lt_two (by omega : 2 ^ 1 ≤ L)
  have hL2M : L ^ 2 ≤ M := hpow2.trans hpowM
  have hL_lt : L ≤ 2 * 2 ^ Nat.log 2 L := by
    have h := Nat.lt_pow_succ_log_self one_lt_two L
    rw [pow_succ'] at h
    exact h.le
  have hcubes : (2 * 2 ^ Nat.log 2 L) ^ 3 = 8 * 2 ^ (3 * Nat.log 2 L) := by
    rw [mul_pow, ← pow_mul, mul_comm (Nat.log 2 L) 3]
    norm_num
  have hL3 : L ^ 3 * 2 ^ s ≤ 8 * M := by
    calc L ^ 3 * 2 ^ s
        ≤ (2 * 2 ^ Nat.log 2 L) ^ 3 * 2 ^ s :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hL_lt 3)
      _ = 8 * (2 ^ (3 * Nat.log 2 L) * 2 ^ s) := by
          rw [hcubes]
          ring
      _ = 8 * 2 ^ (3 * Nat.log 2 L + s) := by rw [← pow_add]
      _ = 8 * 2 ^ L := by
          congr 2
          omega
      _ ≤ 8 * M := Nat.mul_le_mul_left 8 hpowM
  exact ⟨hs_pos, hs_le, hL_2s, hlogL1, hL2M, hL3⟩

private theorem natLog_le_logb {m : ℕ} (hm : 1 ≤ m) :
    (Nat.log 2 m : ℝ) ≤ Real.logb 2 m := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
  exact_mod_cast Nat.pow_log_le_self 2 (by omega)

private theorem logb_le_natLog_add_one {m : ℕ} (hm : 1 ≤ m) :
    Real.logb 2 m ≤ (Nat.log 2 m : ℝ) + 1 := by
  have h := Nat.lt_pow_succ_log_self one_lt_two m
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity)]
  have hcast : ((Nat.log 2 m + 1 : ℕ) : ℝ) = (Nat.log 2 m : ℝ) + 1 := by push_cast; ring
  rw [← hcast, Real.rpow_natCast]
  exact_mod_cast h.le

theorem logb_two_ge_one {m : ℕ} (hm : 2 ≤ m) :
    1 ≤ Real.logb 2 m := by
  have h1 : 1 ≤ Nat.log 2 m := Nat.le_log_of_pow_le one_lt_two hm
  exact le_trans (by exact_mod_cast h1) (natLog_le_logb (by omega))

theorem div_two_sub_add_rem_le {M S U rem K : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hL8 : 8 ≤ Nat.log 2 M)
    (h6log : 6 * Nat.log 2 (Nat.log 2 M) ≤ Nat.log 2 M)
    (hpow2 : (Nat.log 2 M) ^ 2 ≤ 2 ^ Nat.log 2 M)
    (hClog : (⌈((4 + 2 * K : ℕ) : ℝ) / ε⌉₊ + 10) * Nat.log 2 (Nat.log 2 M) ≤ Nat.log 2 M)
    (hSU : S ≤ U)
    (hrem : (Nat.log 2 M) ^ 2 * rem ≤ K * U) :
    ((S / (2 * (Nat.log 2 M - 3 * Nat.log 2 (Nat.log 2 M))) : ℕ) : ℝ) + (rem : ℝ) ≤
      (S : ℝ) / (2 * Real.logb 2 M) + ε * ((U : ℝ) / Real.logb 2 M) := by
  have hM_ge2 : 2 ≤ M := by
    have hpow := Nat.pow_log_le_self 2 (x := M) (by rintro rfl; simp at hL8)
    have h2 : 2 ^ 1 ≤ 2 ^ Nat.log 2 M := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨hs_pos, hs_le, hL_2s, hlogL1, _, _⟩ := log_param_props hL8 h6log hpow2
  set L := Nat.log 2 M
  set s := L - 3 * Nat.log 2 L
  set logM := Real.logb 2 M
  have hlogM_pos : 0 < logM := lt_of_lt_of_le zero_lt_one (logb_two_ge_one hM_ge2)
  have hLR_pos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hsR_pos : (0 : ℝ) < s := by exact_mod_cast hs_pos
  have hlogM_hi : logM ≤ 2 * (L : ℝ) := by
    have h1 := logb_le_natLog_add_one (m := M) (by omega)
    have h2 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    linarith
  have hSU_R : (S : ℝ) ≤ (U : ℝ) := Nat.cast_le.mpr hSU
  have hmain_part :
      ((S / (2 * s) : ℕ) : ℝ) ≤
        (S : ℝ) / (2 * logM) + (4 * (Nat.log 2 L : ℝ) / L) * ((U : ℝ) / logM) := by
    have hdiv_le : ((S / (2 * s) : ℕ) : ℝ) ≤ (S : ℝ) / (2 * s) := by
      exact_mod_cast Nat.cast_div_le (m := S) (n := 2 * s) (α := ℝ)
    have hdiff_eq :
        (S : ℝ) / (2 * s) =
          (S : ℝ) / (2 * logM) + (S : ℝ) * (logM - s) / (2 * s * logM) := by
      field_simp
      ring
    have hsR_eq : (s : ℝ) = (L : ℝ) - 3 * (Nat.log 2 L : ℝ) := by
      have hle3 : 3 * Nat.log 2 L ≤ L := by omega
      exact_mod_cast Nat.cast_sub (R := ℝ) hle3
    have hgap_nonneg : 0 ≤ logM - (s : ℝ) := by
      have hsL : (s : ℝ) ≤ L := by exact_mod_cast hs_le
      have hL_le_logM : (L : ℝ) ≤ logM := natLog_le_logb (by omega)
      linarith
    have hgap_le : logM - (s : ℝ) ≤ 4 * (Nat.log 2 L : ℝ) := by
      have h1 := logb_le_natLog_add_one (m := M) (by omega)
      have hlogL1R : (1 : ℝ) ≤ Nat.log 2 L := by exact_mod_cast hlogL1
      linarith
    have h2s_ge : (L : ℝ) ≤ 2 * (s : ℝ) := by exact_mod_cast hL_2s
    have hnum : (S : ℝ) * (logM - s) ≤ (U : ℝ) * (4 * (Nat.log 2 L : ℝ)) :=
      mul_le_mul hSU_R hgap_le hgap_nonneg (by positivity)
    have hden : (L : ℝ) * logM ≤ 2 * (s : ℝ) * logM :=
      mul_le_mul_of_nonneg_right h2s_ge hlogM_pos.le
    have hfrac :
        (S : ℝ) * (logM - s) / (2 * s * logM) ≤
          (4 * (Nat.log 2 L : ℝ) / L) * ((U : ℝ) / logM) := by
      calc (S : ℝ) * (logM - s) / (2 * s * logM)
          ≤ (U : ℝ) * (4 * (Nat.log 2 L : ℝ)) / (2 * s * logM) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ (U : ℝ) * (4 * (Nat.log 2 L : ℝ)) / ((L : ℝ) * logM) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        _ = (4 * (Nat.log 2 L : ℝ) / L) * ((U : ℝ) / logM) := by ring
    linarith
  have hrem_part :
      (rem : ℝ) ≤ ((2 * (K : ℝ)) * (Nat.log 2 L : ℝ) / L) * ((U : ℝ) / logM) := by
    have hrem_R : (L : ℝ) ^ 2 * (rem : ℝ) ≤ (K : ℝ) * (U : ℝ) := by
      have hcast : ((L ^ 2 * rem : ℕ) : ℝ) ≤ ((K * U : ℕ) : ℝ) := Nat.cast_le.mpr hrem
      push_cast at hcast
      exact hcast
    have hrem_div : (rem : ℝ) ≤ (K : ℝ) * (U : ℝ) / (L : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hlogL1R : (1 : ℝ) ≤ Nat.log 2 L := by exact_mod_cast hlogL1
    have hstep :
        (K : ℝ) * (U : ℝ) / (L : ℝ) ^ 2 ≤
          ((2 * (K : ℝ)) * (Nat.log 2 L : ℝ) / L) * ((U : ℝ) / logM) := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      calc ((K : ℝ) * (U : ℝ)) * ((L : ℝ) * logM)
          = (L : ℝ) * (logM * ((K : ℝ) * (U : ℝ))) := by ring
        _ ≤ (L : ℝ) * ((2 * (L : ℝ)) * ((K : ℝ) * (U : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hlogM_hi (by positivity)) (by positivity)
        _ = 1 * ((L : ℝ) ^ 2 * (2 * (K : ℝ) * (U : ℝ))) := by ring
        _ ≤ (Nat.log 2 L : ℝ) * ((L : ℝ) ^ 2 * (2 * (K : ℝ) * (U : ℝ))) :=
            mul_le_mul_of_nonneg_right hlogL1R (by positivity)
        _ = ((2 * (K : ℝ)) * (Nat.log 2 L : ℝ) * (U : ℝ)) * (L : ℝ) ^ 2 := by ring
    exact hrem_div.trans hstep
  set C : ℕ := ⌈((4 + 2 * K : ℕ) : ℝ) / ε⌉₊ + 10
  have hcoeff : (4 + 2 * (K : ℝ)) * (Nat.log 2 L : ℝ) / L ≤ ε := by
    have hCL_R : (C : ℝ) * (Nat.log 2 L : ℝ) ≤ L := by exact_mod_cast hClog
    have h42K_cast : ((4 + 2 * K : ℕ) : ℝ) = 4 + 2 * (K : ℝ) := by push_cast; ring
    have hC_ge : (4 + 2 * (K : ℝ)) / ε ≤ (C : ℝ) := by
      have hceil : ((4 + 2 * K : ℕ) : ℝ) / ε ≤ (⌈((4 + 2 * K : ℕ) : ℝ) / ε⌉₊ : ℝ) :=
        Nat.le_ceil _
      have hcast : (C : ℝ) = (⌈((4 + 2 * K : ℕ) : ℝ) / ε⌉₊ : ℝ) + 10 := by
        exact_mod_cast rfl
      have hle : ((4 + 2 * K : ℕ) : ℝ) / ε ≤ (C : ℝ) := by linarith
      rwa [h42K_cast] at hle
    have h42K : 4 + 2 * (K : ℝ) ≤ ε * C := by
      have hmul := (div_le_iff₀ hε).mp hC_ge
      linarith
    rw [div_le_iff₀ hLR_pos]
    calc (4 + 2 * (K : ℝ)) * (Nat.log 2 L : ℝ)
        ≤ (ε * C) * (Nat.log 2 L : ℝ) :=
          mul_le_mul_of_nonneg_right h42K (Nat.cast_nonneg _)
      _ = ε * ((C : ℝ) * (Nat.log 2 L : ℝ)) := by ring
      _ ≤ ε * L := mul_le_mul_of_nonneg_left hCL_R hε.le
  have herr := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ (U : ℝ) / logM by positivity)
  have hsum :
      (4 * (Nat.log 2 L : ℝ) / L) * ((U : ℝ) / logM) +
        ((2 * (K : ℝ)) * (Nat.log 2 L : ℝ) / L) * ((U : ℝ) / logM) =
        ((4 + 2 * (K : ℝ)) * (Nat.log 2 L : ℝ) / L) * ((U : ℝ) / logM) := by ring
  linarith

end ParameterBounds

namespace Additive

theorem matrixRem_mul_sq_le (m n : ℕ)
    (hL8 : 8 ≤ Nat.log 2 m)
    (hlog6 : 6 * Nat.log 2 (Nat.log 2 m) ≤ Nat.log 2 m)
    (hpow2 : (Nat.log 2 m) ^ 2 ≤ 2 ^ Nat.log 2 m) :
    let L := Nat.log 2 m
    let s := L - 3 * Nat.log 2 L
    let p := m / L ^ 2 + 1
    L ^ 2 * ((n * 2 ^ s) / s + m * p + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)) ≤
      34 * (m + n) ^ 2 := by
  dsimp only
  obtain ⟨hs_pos, hs_le, hL_2s, _, hL2m, hL3⟩ := log_param_props hL8 hlog6 hpow2
  set L := Nat.log 2 m
  set s := L - 3 * Nat.log 2 L
  set p := m / L ^ 2 + 1
  have hs_le_m : s ≤ m := by
    have hLL2 : L ≤ L ^ 2 := by nlinarith
    exact hs_le.trans (hLL2.trans hL2m)
  have ht1 : L ^ 2 * ((n * 2 ^ s) / s) ≤ 16 * (m + n) ^ 2 := by
    have hdiv : L * ((n * 2 ^ s) / s) ≤ 2 * (n * 2 ^ s) := by
      calc L * ((n * 2 ^ s) / s)
          ≤ (2 * s) * ((n * 2 ^ s) / s) := Nat.mul_le_mul_right _ hL_2s
        _ = 2 * (s * ((n * 2 ^ s) / s)) := by ring
        _ ≤ 2 * (n * 2 ^ s) := Nat.mul_le_mul_left 2 (Nat.mul_div_le _ s)
    calc L ^ 2 * ((n * 2 ^ s) / s)
        ≤ L ^ 3 * ((n * 2 ^ s) / s) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))
      _ = L ^ 2 * (L * ((n * 2 ^ s) / s)) := by ring
      _ ≤ L ^ 2 * (2 * (n * 2 ^ s)) := Nat.mul_le_mul_left _ hdiv
      _ ≤ L ^ 3 * (2 * (n * 2 ^ s)) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))
      _ = 2 * n * (L ^ 3 * 2 ^ s) := by ring
      _ ≤ 2 * n * (8 * m) := Nat.mul_le_mul_left _ hL3
      _ ≤ 16 * (m + n) ^ 2 := by nlinarith
  have ht2 : L ^ 2 * (m * p) ≤ 2 * (m + n) ^ 2 := by
    have hsq : 2 * (m + n) ^ 2 = m * m + m * m + 4 * m * n + 2 * n * n := by ring
    calc L ^ 2 * (m * (m / L ^ 2 + 1))
        = m * (L ^ 2 * (m / L ^ 2)) + m * L ^ 2 := by ring
      _ ≤ m * m + m * m :=
          Nat.add_le_add (Nat.mul_le_mul_left m (Nat.mul_div_le m (L ^ 2)))
            (Nat.mul_le_mul_left m hL2m)
      _ ≤ 2 * (m + n) ^ 2 := by rw [hsq]; omega
  have ht3 : L ^ 2 * ((m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)) ≤ 16 * (m + n) ^ 2 := by
    have hmp : m ⌈/⌉ p ≤ L ^ 2 := ceilDiv_div_sq_add_one_le m (by omega)
    have hns : s * (n ⌈/⌉ s) ≤ n + s := mul_ceilDiv_le_add n hs_pos
    have hL2_le : L ^ 2 ≤ 2 * s * L := by nlinarith
    calc L ^ 2 * ((m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s))
        ≤ (2 * s * L) * ((m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)) :=
          Nat.mul_le_mul_right _ hL2_le
      _ = 2 * ((m ⌈/⌉ p) * (L * 2 ^ s)) * (s * (n ⌈/⌉ s)) := by ring
      _ ≤ 2 * (L ^ 2 * (L * 2 ^ s)) * (n + s) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hmp)) hns
      _ = 2 * (L ^ 3 * 2 ^ s) * (n + s) := by ring
      _ ≤ 2 * (8 * m) * (n + m) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hL3) (Nat.add_le_add_left hs_le_m n)
      _ ≤ 16 * (m + n) ^ 2 := by nlinarith
  calc L ^ 2 * ((n * 2 ^ s) / s + m * p + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s))
      = L ^ 2 * ((n * 2 ^ s) / s) + L ^ 2 * (m * p) +
          L ^ 2 * ((m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)) := by ring
    _ ≤ 16 * (m + n) ^ 2 + 2 * (m + n) ^ 2 + 16 * (m + n) ^ 2 :=
        Nat.add_le_add (Nat.add_le_add ht1 ht2) ht3
    _ = 34 * (m + n) ^ 2 := by ring


end Additive

namespace Boolean.Zhegalkin

theorem zhegRem_mul_sq_le (n M : ℕ)
    (hL8 : 8 ≤ Nat.log 2 M)
    (hlog6 : 6 * Nat.log 2 (Nat.log 2 M) ≤ Nat.log 2 M)
    (hpow2 : (Nat.log 2 M) ^ 2 ≤ 2 ^ Nat.log 2 M) :
    let L := Nat.log 2 M
    let s := L - 3 * Nat.log 2 L
    let p := (2 * M) / L ^ 2 + 1
    L ^ 2 * (((n + M) * 2 ^ s) / s + 2 * M * (p + s + 1) +
        ((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s) + n + M + 2) ≤
      88 * (M * (M + 2 * n)) := by
  dsimp only
  obtain ⟨hs_pos, hs_le, hL_2s, _, hL2M, hL3⟩ := log_param_props hL8 hlog6 hpow2
  set L := Nat.log 2 M
  set s := L - 3 * Nat.log 2 L
  set p := (2 * M) / L ^ 2 + 1
  have hM_ge2 : 2 ≤ M := by
    have : 8 ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left hL8 2
    omega
  have hs_le_M : s ≤ M := by
    have hLL2 : L ≤ L ^ 2 := by nlinarith
    exact hs_le.trans (hLL2.trans hL2M)
  have ht1 : L ^ 2 * (((n + M) * 2 ^ s) / s) ≤ 16 * (M * (M + 2 * n)) := by
    have hdiv : L * (((n + M) * 2 ^ s) / s) ≤ 2 * ((n + M) * 2 ^ s) := by
      calc L * (((n + M) * 2 ^ s) / s)
          ≤ (2 * s) * (((n + M) * 2 ^ s) / s) := Nat.mul_le_mul_right _ hL_2s
        _ = 2 * (s * (((n + M) * 2 ^ s) / s)) := by ring
        _ ≤ 2 * ((n + M) * 2 ^ s) := Nat.mul_le_mul_left 2 (Nat.mul_div_le _ s)
    calc L ^ 2 * (((n + M) * 2 ^ s) / s)
        ≤ L ^ 4 * (((n + M) * 2 ^ s) / s) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))
      _ = L ^ 3 * (L * (((n + M) * 2 ^ s) / s)) := by ring
      _ ≤ L ^ 3 * (2 * ((n + M) * 2 ^ s)) := Nat.mul_le_mul_left _ hdiv
      _ = 2 * (n + M) * (L ^ 3 * 2 ^ s) := by ring
      _ ≤ 2 * (n + M) * (8 * M) := Nat.mul_le_mul_left _ hL3
      _ ≤ 16 * (M * (M + 2 * n)) := by nlinarith
  have ht2 : L ^ 2 * (2 * M * (p + s + 1)) ≤ 38 * (M * (M + 2 * n)) := by
    have hp_le : L ^ 2 * p ≤ 3 * M := by
      calc L ^ 2 * ((2 * M) / L ^ 2 + 1)
          = L ^ 2 * ((2 * M) / L ^ 2) + L ^ 2 := by ring
        _ ≤ 2 * M + M := Nat.add_le_add (Nat.mul_div_le _ _) hL2M
        _ = 3 * M := by ring
    have hs1_le : L ^ 2 * (s + 1) ≤ 16 * M := by
      have hs1_2L : s + 1 ≤ 2 * L := by omega
      have hL3_le : L ^ 3 ≤ L ^ 3 * 2 ^ s :=
        Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) s)
      calc L ^ 2 * (s + 1)
          ≤ L ^ 2 * (2 * L) := Nat.mul_le_mul_left _ hs1_2L
        _ = 2 * L ^ 3 := by ring
        _ ≤ 2 * (L ^ 3 * 2 ^ s) := Nat.mul_le_mul_left 2 hL3_le
        _ ≤ 2 * (8 * M) := Nat.mul_le_mul_left 2 hL3
        _ = 16 * M := by ring
    calc L ^ 2 * (2 * M * (p + s + 1))
        = 2 * M * (L ^ 2 * p + L ^ 2 * (s + 1)) := by ring
      _ ≤ 2 * M * (3 * M + 16 * M) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add hp_le hs1_le)
      _ ≤ 38 * (M * (M + 2 * n)) := by nlinarith
  have ht3 : L ^ 2 * (((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s)) ≤
      32 * (M * (M + 2 * n)) := by
    have hMp : (2 * M) ⌈/⌉ p ≤ L ^ 2 := ceilDiv_div_sq_add_one_le (2 * M) (by omega)
    have hnMs : s * ((n + M) ⌈/⌉ s) ≤ 2 * (M + 2 * n) := by
      have h1 := mul_ceilDiv_le_add (n + M) hs_pos
      omega
    have hL2_le : L ^ 2 ≤ 2 * s * L := by nlinarith
    calc L ^ 2 * (((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s))
        ≤ (2 * s * L) * (((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s)) :=
          Nat.mul_le_mul_right _ hL2_le
      _ = 2 * (((2 * M) ⌈/⌉ p) * (L * 2 ^ s)) * (s * ((n + M) ⌈/⌉ s)) := by ring
      _ ≤ 2 * (L ^ 2 * (L * 2 ^ s)) * (2 * (M + 2 * n)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hMp)) hnMs
      _ = 4 * (L ^ 3 * 2 ^ s) * (M + 2 * n) := by ring
      _ ≤ 4 * (8 * M) * (M + 2 * n) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hL3)
      _ = 32 * (M * (M + 2 * n)) := by ring
  have ht4 : L ^ 2 * (n + M + 2) ≤ 2 * (M * (M + 2 * n)) := by
    calc L ^ 2 * (n + M + 2)
        = L ^ 2 * n + L ^ 2 * M + L ^ 2 * 2 := by ring
      _ ≤ M * n + M * M + M * M :=
          Nat.add_le_add
            (Nat.add_le_add (Nat.mul_le_mul_right n hL2M) (Nat.mul_le_mul_right M hL2M))
            (Nat.mul_le_mul hL2M hM_ge2)
      _ ≤ 2 * (M * (M + 2 * n)) := by nlinarith
  calc L ^ 2 * (((n + M) * 2 ^ s) / s + 2 * M * (p + s + 1) +
          ((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s) + n + M + 2)
      = L ^ 2 * (((n + M) * 2 ^ s) / s) + L ^ 2 * (2 * M * (p + s + 1)) +
          L ^ 2 * (((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s)) + L ^ 2 * (n + M + 2) := by ring
    _ ≤ 16 * (M * (M + 2 * n)) + 38 * (M * (M + 2 * n)) +
          32 * (M * (M + 2 * n)) + 2 * (M * (M + 2 * n)) :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ht1 ht2) ht3) ht4
    _ = 88 * (M * (M + 2 * n)) := by ring


end Boolean.Zhegalkin

end Cslib.Circuits
