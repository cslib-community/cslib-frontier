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

/-- The block-count term: `L ^ 2 * (X * 2 ^ s / s) ≤ 16 * M * X` when `L ≤ 2 * s` and
`L ^ 3 * 2 ^ s ≤ 8 * M`. -/
private theorem sq_mul_div_le {L s M : ℕ} (X : ℕ) (hL_2s : L ≤ 2 * s)
    (hL3 : L ^ 3 * 2 ^ s ≤ 8 * M) : L ^ 2 * (X * 2 ^ s / s) ≤ 16 * M * X := by
  have hL : L ≤ L ^ 3 := Nat.le_self_pow (by norm_num) L
  calc L ^ 2 * (X * 2 ^ s / s) ≤ L * (2 * s) * (X * 2 ^ s / s) := by rw [sq]; gcongr
    _ = 2 * L * (s * (X * 2 ^ s / s)) := by ring
    _ ≤ 2 * L ^ 3 * (X * 2 ^ s) := Nat.mul_le_mul (by gcongr) (Nat.mul_div_le _ _)
    _ = 2 * X * (L ^ 3 * 2 ^ s) := by ring
    _ ≤ 2 * X * (8 * M) := by gcongr
    _ = 16 * M * X := by ring

/-- The block-product term: with `p = A / L ^ 2 + 1`,
`L ^ 2 * ((A ⌈/⌉ p) * 2 ^ s * (B ⌈/⌉ s)) ≤ 16 * M * (B + s)` when `L ≤ 2 * s` and
`L ^ 3 * 2 ^ s ≤ 8 * M`. -/
private theorem sq_mul_ceilDiv_le {L s M : ℕ} (A B : ℕ) (hL : 0 < L) (hs : 0 < s)
    (hL_2s : L ≤ 2 * s) (hL3 : L ^ 3 * 2 ^ s ≤ 8 * M) :
    L ^ 2 * ((A ⌈/⌉ (A / L ^ 2 + 1)) * 2 ^ s * (B ⌈/⌉ s)) ≤ 16 * M * (B + s) := by
  have hAp : A ⌈/⌉ (A / L ^ 2 + 1) ≤ L ^ 2 := by
    rw [ceilDiv_le_iff_le_smul (Nat.succ_pos _), smul_eq_mul, Nat.succ_mul]
    exact (Nat.lt_div_mul_add (by positivity)).le
  have hBs : s * (B ⌈/⌉ s) ≤ B + s := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact (Nat.mul_div_le _ _).trans (by omega)
  calc L ^ 2 * ((A ⌈/⌉ (A / L ^ 2 + 1)) * 2 ^ s * (B ⌈/⌉ s))
      ≤ 2 * s * L * ((A ⌈/⌉ (A / L ^ 2 + 1)) * 2 ^ s * (B ⌈/⌉ s)) := by rw [sq]; gcongr
    _ = 2 * ((A ⌈/⌉ (A / L ^ 2 + 1)) * (L * 2 ^ s)) * (s * (B ⌈/⌉ s)) := by ring
    _ ≤ 2 * (L ^ 2 * (L * 2 ^ s)) * (B + s) := by gcongr
    _ = 2 * (L ^ 3 * 2 ^ s) * (B + s) := by ring
    _ ≤ 2 * (8 * M) * (B + s) := by gcongr
    _ = 16 * M * (B + s) := by ring

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
  have hM0 : M ≠ 0 := fun h0 => by simp [L, h0] at hL8
  have hpowM : 2 ^ L ≤ M := Nat.pow_log_le_self 2 hM0
  have hs_pos : 0 < s := by omega
  have hs_le : s ≤ L := Nat.sub_le _ _
  have hL_2s : L ≤ 2 * s := by omega
  have hlogL1 : 1 ≤ Nat.log 2 L :=
    Nat.le_log_of_pow_le one_lt_two (by omega : 2 ^ 1 ≤ L)
  have hL2M : L ^ 2 ≤ M := hpow2.trans hpowM
  have hL_lt : L ≤ 2 * 2 ^ Nat.log 2 L :=
    (pow_succ' 2 _ ▸ Nat.lt_pow_succ_log_self one_lt_two L).le
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
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), ← Nat.cast_add_one,
    Real.rpow_natCast]
  exact_mod_cast (Nat.lt_pow_succ_log_self one_lt_two m).le

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
  obtain ⟨hs_pos, -, hL_2s, hlogL1, hL2M, -⟩ := log_param_props hL8 h6log hpow2
  set L := Nat.log 2 M
  set l := Nat.log 2 L
  set s := L - 3 * l
  have hM : 1 ≤ M := by nlinarith
  have hlo : (L : ℝ) ≤ Real.logb 2 M := natLog_le_logb hM
  have hhi : Real.logb 2 M ≤ L + 1 := logb_le_natLog_add_one hM
  set x := Real.logb 2 M
  have ha : ((S / (2 * s) : ℕ) : ℝ) * (2 * s) ≤ S := by
    exact_mod_cast Nat.div_mul_le_self S (2 * s)
  set a := ((S / (2 * s) : ℕ) : ℝ)
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have hs : (s : ℝ) = L - 3 * l := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hrem' : (L : ℝ) ^ 2 * rem ≤ K * U := by exact_mod_cast hrem
  have hSU' : (S : ℝ) ≤ U := by exact_mod_cast hSU
  have hL2s' : (L : ℝ) ≤ 2 * s := by exact_mod_cast hL_2s
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hlogL1
  have hL8' : (8 : ℝ) ≤ L := by exact_mod_cast hL8
  -- The choice of the constant in `hClog` makes `(4 + 2K) log L ≤ ε L`.
  have hcoeff : (4 + 2 * (K : ℝ)) * l ≤ ε * L := by
    have hC : ((⌈((4 + 2 * K : ℕ) : ℝ) / ε⌉₊ + 10 : ℕ) : ℝ) * l ≤ L := by exact_mod_cast hClog
    have hceil := (div_le_iff₀ hε).mp (Nat.le_ceil (((4 + 2 * K : ℕ) : ℝ) / ε))
    push_cast at hC hceil
    linarith [mul_le_mul_of_nonneg_right hceil (Nat.cast_nonneg l),
      mul_le_mul_of_nonneg_left hC hε.le, mul_nonneg hε.le (Nat.cast_nonneg l)]
  have hLa : L * a ≤ U := by linarith [mul_le_mul_of_nonneg_right hL2s' ha0]
  have hremx : L * (rem * x) ≤ 2 * K * U := by
    linarith [mul_le_mul_of_nonneg_left (by linarith : x ≤ 2 * L)
      (by positivity : (0 : ℝ) ≤ L * rem)]
  rw [show (S : ℝ) / (2 * x) + ε * ((U : ℝ) / x) = ((S : ℝ) / 2 + ε * U) / x by ring,
    le_div_iff₀ (by linarith)]
  -- Multiply by `L`: the main part costs `x - s ≤ 4 log L`, the remainder `2K`.
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < L)
  linarith [mul_le_mul_of_nonneg_left (by linarith : x ≤ s + 4 * l)
      (mul_nonneg (Nat.cast_nonneg L) ha0),
    mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg L),
    mul_le_mul_of_nonneg_left hLa (Nat.cast_nonneg l),
    mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg U),
    mul_le_mul_of_nonneg_left hl1 (by positivity : (0 : ℝ) ≤ 2 * K * U)]

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
  have hs_le_m : s ≤ m := hs_le.trans ((Nat.le_self_pow (by norm_num) L).trans hL2m)
  have ht1 := sq_mul_div_le n hL_2s hL3
  have ht2 := Nat.mul_div_le m (L ^ 2)
  have ht3 := sq_mul_ceilDiv_le m n (by omega) hs_pos hL_2s hL3
  nlinarith [Nat.mul_le_mul_left m hs_le_m, Nat.mul_le_mul_left m hL2m]


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
  have hM_ge2 : 2 ≤ M := by nlinarith
  have hs_le_M : s ≤ M := hs_le.trans ((Nat.le_self_pow (by norm_num) L).trans hL2M)
  have ht1 := sq_mul_div_le (n + M) hL_2s hL3
  have hp_le : L ^ 2 * ((2 * M) / L ^ 2 + 1) ≤ 3 * M := by
    have := Nat.mul_div_le (2 * M) (L ^ 2)
    nlinarith
  have hs1_le : L ^ 2 * (s + 1) ≤ 16 * M := by
    have : L ^ 3 ≤ L ^ 3 * 2 ^ s := Nat.le_mul_of_pos_right _ (by positivity)
    have : L ^ 2 * (s + 1) ≤ L ^ 2 * (2 * L) := by gcongr; omega
    nlinarith
  have ht3 := sq_mul_ceilDiv_le (2 * M) (n + M) (by omega) hs_pos hL_2s hL3
  nlinarith [Nat.mul_le_mul_left (2 * M) hp_le, Nat.mul_le_mul_left (2 * M) hs1_le,
    Nat.mul_le_mul_right n hL2M, Nat.mul_le_mul_right M hL2M, Nat.mul_le_mul_left M hs_le_M,
    Nat.mul_le_mul_left M hM_ge2]


end Boolean.Zhegalkin

end Cslib.Circuits
