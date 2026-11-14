/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.MasterTheorem
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.Data.Nat.LogTwoRpow

/-!
# The master theorem in asymptotic form

This module converts the explicit bounds of `CslibFrontier.Foundations.Data.Nat.MasterTheorem` into
real powers and Mathlib's `Asymptotics.IsBigO` / `Asymptotics.IsTheta`.

For upper bounds `Nat.DivideConquerBound T a b n₀ T₀ (fun n => c n ^ d)` with `a ≥ 1`, `b ≥ 2`
and `n₀ ≥ 1` (in cases 1 and 2 `a ≥ 1` follows from the case condition):

* `a > b ^ d`: `T n ≤ (T₀ + c n₀ ^ d b ^ d / (a - b ^ d)) a n ^ log_b a` for `n ≠ 0`, so
  `T = O(n ^ log_b a)`.
* `a = b ^ d`: `T = O(n ^ d log n)`.
* `a < b ^ d`: `T = O(n ^ d)`.
* General case 3: for monotone, eventually positive `f` satisfying `a f ⌈m/b⌉ ≤ ρ f m`
  eventually with `ρ < 1`, `T = O(f)`.

For lower bounds `Nat.DivideConquerLowerBound`, the dual `Ω` bounds hold (under `c ≥ 1`, or in
case 1 also under `T₀ ≥ 1 ∧ b ≤ n₀ + 1`). For equality recurrences
`Nat.DivideConquerRecurrence`, these combine into matching `Θ` bounds (`=Θ[Filter.atTop]`).

Mathlib's `Mathlib.Computability.AkraBazzi` proves the more general Akra–Bazzi `Θ` bound. It
needs an equality recurrence over `ℝ` with positive base values and polynomial growth of the
driving term. The statements here cover discrete `ℕ` recurrences (including `d = 0`, threshold-`1`
recurrences, inequality recurrences, and general monotone case-3 regularity).

The conversions to real powers and logarithms are `Nat.pow_clog_le_mul_rpow_logb`,
`Nat.rpow_logb_le_mul_pow_log`, and `Nat.clog_le_two_mul_logb`
(`CslibFrontier.Foundations.Data.Nat.LogTwoRpow`).

## Main results

* `Nat.DivideConquerBound.le_mul_rpow`: case 1 with a real power and an explicit constant.
* `Nat.DivideConquerBound.isBigO_rpow`, `Nat.DivideConquerBound.isBigO_pow_mul_log`,
  `Nat.DivideConquerBound.isBigO_pow`, `Nat.DivideConquerBound.isBigO_of_regular`: upper bounds
  as `IsBigO` statements.
* `Nat.DivideConquerLowerBound.rpow_isBigO`, `Nat.DivideConquerLowerBound.pow_mul_log_isBigO`,
  `Nat.DivideConquerLowerBound.pow_isBigO`, `Nat.DivideConquerLowerBound.driving_isBigO`:
  matching lower bounds in `IsBigO` form.
* `Nat.DivideConquerRecurrence.isTheta_rpow`, `Nat.DivideConquerRecurrence.isTheta_pow_mul_log`,
  `Nat.DivideConquerRecurrence.isTheta_pow`, `Nat.DivideConquerRecurrence.isTheta_of_regular`:
  matching `Θ` bounds for equality recurrences.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Theorem 4.1.
-/

public section

namespace Nat

open Asymptotics Filter

namespace DivideConquerBound

variable {T : ℕ → ℕ} {a b n₀ T₀ c d : ℕ}

/-- **Master theorem, case 1**, with a real power: if `b ^ d < a` and `n ≠ 0`, then
`T n ≤ (T₀ + c n₀ ^ d b ^ d / (a - b ^ d)) a n ^ log_b a`. -/
theorem le_mul_rpow (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d)
    (hb : 1 < b) (hn₀ : 1 ≤ n₀) (hlt : b ^ d < a) {n : ℕ} (hn : n ≠ 0) :
    (T n : ℝ) ≤ (T₀ + c * n₀ ^ d * b ^ d / (a - b ^ d)) * a * (n : ℝ) ^ Real.logb b a := by
  have ha : 1 ≤ a := by have := Nat.one_le_pow d b (by omega); omega
  have hmain := h.sub_mul_le_pow_clog ha hb hn₀ n
  have hpos : (0 : ℝ) < (a : ℝ) - b ^ d := by
    have : ((b ^ d : ℕ) : ℝ) < a := by exact_mod_cast hlt
    push_cast at this
    linarith
  have hcast : ((a - b ^ d : ℕ) : ℝ) = (a : ℝ) - b ^ d := by
    rw [Nat.cast_sub hlt.le]; push_cast; ring
  have hmain' : ((a : ℝ) - b ^ d) * T n ≤
      (((a : ℝ) - b ^ d) * T₀ + c * n₀ ^ d * b ^ d) * ((a ^ clog b n : ℕ) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hmain
    push_cast [hcast] at this ⊢
    exact this
  have hT : (T n : ℝ) ≤ (T₀ + c * n₀ ^ d * b ^ d / (a - b ^ d)) * ((a ^ clog b n : ℕ) : ℝ) := by
    have he : (T₀ + c * n₀ ^ d * b ^ d / (a - b ^ d)) * ((a ^ clog b n : ℕ) : ℝ) =
        (((a : ℝ) - b ^ d) * T₀ + c * n₀ ^ d * b ^ d) * ((a ^ clog b n : ℕ) : ℝ) /
          (a - b ^ d) := by
      field_simp
    rw [he, le_div_iff₀ hpos]
    linarith
  calc (T n : ℝ) ≤ _ := hT
    _ ≤ (T₀ + c * n₀ ^ d * b ^ d / (a - b ^ d)) * (a * (n : ℝ) ^ Real.logb b a) := by
        gcongr
        exact pow_clog_le_mul_rpow_logb hb ha hn
    _ = _ := by ring

/-- **Master theorem, case 1**: if `b ^ d < a`, then `T = O(n ^ log_b a)`. -/
theorem isBigO_rpow (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d)
    (hb : 1 < b) (hn₀ : 1 ≤ n₀) (hlt : b ^ d < a) :
    (fun n => (T n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ Real.logb b a := by
  refine IsBigO.of_bound ((T₀ + c * n₀ ^ d * b ^ d / (a - b ^ d)) * a) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity)]
  exact h.le_mul_rpow hb hn₀ hlt (by omega)

/-- **Master theorem, case 2**: if `a = b ^ d`, then `T = O(n ^ d log n)`. -/
theorem isBigO_pow_mul_log (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d)
    (hb : 1 < b) (hn₀ : 1 ≤ n₀) (had : a = b ^ d) :
    (fun n => (T n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ d * Real.log n := by
  have ha : 1 ≤ a := had ▸ Nat.one_le_pow d b (by omega)
  have hb' : (1 : ℝ) < b := by exact_mod_cast hb
  have hlogb : 0 < Real.log b := Real.log_pos hb'
  refine IsBigO.of_bound ((b : ℝ) ^ d * (T₀ / Real.log b + c * n₀ ^ d * 2 / Real.log b)) ?_
  filter_upwards [eventually_ge_atTop b] with n hn
  have hL : 1 ≤ Real.logb b n := by
    rw [← Real.logb_self_eq_one hb']
    exact Real.logb_le_logb_of_le hb' (by positivity) (by exact_mod_cast hn)
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity)]
  have hmain : (T n : ℝ) ≤ ((b : ℝ) * n) ^ d * (T₀ + c * n₀ ^ d * (clog b n : ℝ)) := by
    exact_mod_cast h.le_mul_pow_mul_clog ha hb hn₀ had (by omega : n ≠ 0)
  have hK := clog_le_two_mul_logb hb hn
  have hinner : (T₀ : ℝ) + c * n₀ ^ d * (clog b n : ℝ) ≤
      (T₀ / Real.log b + c * n₀ ^ d * 2 / Real.log b) * Real.log n := by
    have e : (T₀ / Real.log b + c * n₀ ^ d * 2 / Real.log b) * Real.log n =
        T₀ * Real.logb b n + c * n₀ ^ d * (2 * Real.logb b n) := by
      rw [Real.logb]; field_simp
    rw [e]
    have hT0 : (T₀ : ℝ) ≤ T₀ * Real.logb b n := le_mul_of_one_le_right (by positivity) hL
    have hc : (c : ℝ) * n₀ ^ d * (clog b n : ℝ) ≤ c * n₀ ^ d * (2 * Real.logb b n) := by gcongr
    linarith
  calc (T n : ℝ) ≤ _ := hmain
    _ ≤ ((b : ℝ) * n) ^ d * ((T₀ / Real.log b + c * n₀ ^ d * 2 / Real.log b) * Real.log n) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- **Master theorem, case 3**: if `a < b ^ d`, then `T = O(n ^ d)`. -/
theorem isBigO_pow (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d)
    (ha : 1 ≤ a) (hb : 1 < b) (hn₀ : 1 ≤ n₀) (hlt : a < b ^ d) :
    (fun n => (T n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ d := by
  set K : ℕ := (b ^ d - a) * T₀ + c * n₀ ^ d * b ^ d
  have hpos : (0 : ℝ) < ((b ^ d - a : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hlt
  refine IsBigO.of_bound ((K : ℝ) * (b : ℝ) ^ d / ((b ^ d - a : ℕ) : ℝ)) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity)]
  have hmain : ((b ^ d - a : ℕ) : ℝ) * T n ≤ K * (((b * n) ^ d : ℕ) : ℝ) := by
    exact_mod_cast h.pow_sub_mul_le_mul_pow ha hb hn₀ (by omega : n ≠ 0)
  rw [Nat.cast_pow, Nat.cast_mul, mul_pow] at hmain
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith

/-- **Master theorem, case 3 under the general regularity condition**: if `f` is monotone,
eventually positive, and `a * f ⌈m/b⌉ ≤ ρ * f m` eventually for some `ρ < 1`, then
`T = O(f)`. -/
theorem isBigO_of_regular {f : ℕ → ℕ} (h : DivideConquerBound T a b n₀ T₀ f)
    (hb : 1 < b) (hn₀ : 1 ≤ n₀) (hf : Monotone f) {ρ : ℝ} (hρ : ρ < 1)
    (hreg : ∀ᶠ m in atTop, (a : ℝ) * f ((m + b - 1) / b) ≤ ρ * f m)
    (hfpos : ∀ᶠ m in atTop, 0 < f m) :
    (fun n => (T n : ℝ)) =O[atTop] fun n => (f n : ℝ) := by
  obtain ⟨N₁, hN₁⟩ := (eventually_atTop.mp (hfpos.and hreg))
  set n₁ := max n₀ N₁
  have hn₀₁ : n₀ ≤ n₁ := le_max_left _ _
  have hN₁₁ : N₁ ≤ n₁ := le_max_right _ _
  have hn₁ : 1 ≤ n₁ := hn₀.trans hn₀₁
  have hfpos' : 0 < f (n₁ + 1) := (hN₁ (n₁ + 1) (Nat.le_succ_of_le hN₁₁)).1
  have hρ₀ : 0 ≤ ρ := by
    have hmul := (hN₁ (n₁ + 1) (Nat.le_succ_of_le hN₁₁)).2
    have hpos : (0 : ℝ) < f (n₁ + 1) := by exact_mod_cast hfpos'
    have hnonneg : (0 : ℝ) ≤ ρ * f (n₁ + 1) :=
      le_trans (mul_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg _)) hmul
    exact nonneg_of_mul_nonneg_left hnonneg hpos
  obtain ⟨r, hρr, hr1⟩ := exists_rat_btwn hρ
  have hrpos : (0 : ℚ) < r := by exact_mod_cast hρ₀.trans_lt hρr
  have hrlt : r < 1 := by exact_mod_cast hr1
  set p : ℕ := r.num.toNat
  set q : ℕ := r.den
  have hq : 0 < q := r.pos
  have hp_cast : (p : ℤ) = r.num := Int.toNat_of_nonneg (Rat.num_pos.mpr hrpos).le
  have hpq : p < q := by
    have hnum_lt : (r.num : ℚ) < r.den := by
      have := hrlt
      rwa [← Rat.num_div_den r, div_lt_one (by exact_mod_cast hq)] at this
    have hnum_int : r.num < (q : ℤ) := by exact_mod_cast hnum_lt
    omega
  have hr_eq : (r : ℝ) = (p : ℝ) / q := by
    rw [Rat.cast_def]
    push_cast [← hp_cast]
    rfl
  have hreg' : ∀ m, n₁ < m → q * (a * f ((m + b - 1) / b)) ≤ p * f m := by
    intro m hm
    have hrm := (hN₁ m (hN₁₁.trans hm.le)).2
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq
    have hreal : (q : ℝ) * ((a : ℝ) * f ((m + b - 1) / b)) ≤ (p : ℝ) * f m := by
      calc (q : ℝ) * ((a : ℝ) * f ((m + b - 1) / b))
          ≤ q * (ρ * f m) := mul_le_mul_of_nonneg_left hrm hq_pos.le
        _ ≤ q * ((r : ℝ) * f m) := by gcongr
        _ = (p : ℝ) * f m := by rw [hr_eq]; field_simp
    exact_mod_cast hreal
  set T₁ := (Finset.range (n₁ + 1)).sup T
  have hT₁ : ∀ n ≤ n₁, T n ≤ T₁ := fun n hn =>
    Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  have hmain := (h.lift_threshold hn₀₁ hT₁).le_mul_of_regular hb hn₁ hf hpq hreg' hfpos'
  have hqp : (0 : ℝ) < ((q - p : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hpq
  refine IsBigO.of_bound ((q : ℝ) * (a * T₁ + 1) / ((q - p : ℕ) : ℝ)) ?_
  filter_upwards [eventually_gt_atTop n₁] with n hn
  rw [Real.norm_natCast, Real.norm_natCast, div_mul_eq_mul_div, le_div_iff₀ hqp]
  have hnat : ((q - p : ℕ) : ℝ) * T n ≤ (q : ℝ) * (a * T₁ + 1) * f n := by
    exact_mod_cast hmain n hn
  linarith

end DivideConquerBound

namespace DivideConquerLowerBound

variable {T f : ℕ → ℕ} {a b n₀ T₀ c d : ℕ}

private theorem nat_le_two_mul_div {n n₀ : ℕ} (hn₀ : 1 ≤ n₀) (hn : n₀ ≤ n) :
    n ≤ 2 * n₀ * (n / n₀) := by
  have hdiv : 1 ≤ n / n₀ := (Nat.le_div_iff_mul_le hn₀).mpr (by simpa using hn)
  have hrem : n % n₀ < n₀ := Nat.mod_lt n hn₀
  have hdm := Nat.div_add_mod n n₀
  calc n = n₀ * (n / n₀) + n % n₀ := hdm.symm
    _ ≤ n₀ * (n / n₀) + n₀ := Nat.add_le_add_left hrem.le _
    _ = n₀ * (n / n₀ + 1) := by ring
    _ ≤ n₀ * (2 * (n / n₀)) := Nat.mul_le_mul_left n₀ (by omega)
    _ = 2 * n₀ * (n / n₀) := by ring

/-- **Master theorem lower bound, case 1**: if `b ^ d < a`, and either `T₀ ≥ 1 ∧ b ≤ n₀ + 1` or
`c ≥ 1`, then `n ^ log_b a = O(T)`. -/
theorem rpow_isBigO (h : DivideConquerLowerBound T a b n₀ T₀ fun n => c * n ^ d)
    (hb : 1 < b) (hn₀ : 1 ≤ n₀) (hlt : b ^ d < a)
    (hcond : (1 ≤ T₀ ∧ b ≤ n₀ + 1) ∨ 1 ≤ c) :
    (fun n : ℕ => (n : ℝ) ^ Real.logb b a) =O[atTop] fun n => (T n : ℝ) := by
  have ha : 1 ≤ a := by have := Nat.one_le_pow d b (by omega); omega
  have hpow_le : ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ n, n₀ * b ≤ n → (a : ℝ) ^ Nat.log b (n / n₀) ≤ C₀ * (T n : ℝ) := by
    rcases hcond with ⟨hT₀, hbn₀⟩ | hc
    · refine ⟨1, one_pos, fun n hn => ?_⟩
      have hnn₀ : n₀ ≤ n := (Nat.le_mul_of_pos_right n₀ (by omega)).trans hn
      have hmono : Monotone fun m => c * m ^ d :=
        fun x y hxy => Nat.mul_le_mul_left c (Nat.pow_le_pow_left hxy d)
      have hnat := h.pow_log_mul_le ha hb hn₀ hbn₀ hmono hnn₀
      have hnat' : a ^ Nat.log b (n / n₀) ≤ T n :=
        (Nat.le_mul_of_pos_right _ hT₀).trans hnat
      exact_mod_cast (by simpa using hnat' : a ^ Nat.log b (n / n₀) ≤ 1 * T n)
    · refine ⟨a, by exact_mod_cast ha, fun n hn => ?_⟩
      have hnat := h.pow_pred_log_mul_le ha hb hn₀ hn
      have hcoef : 1 ≤ c * (n₀ * b) ^ d :=
        Nat.mul_pos hc (Nat.pow_pos (Nat.mul_pos hn₀ (by omega)))
      have hnat1 : a ^ (Nat.log b (n / n₀) - 1) ≤ T n :=
        (Nat.le_mul_of_pos_left _ hcoef).trans hnat
      have hk : 1 ≤ Nat.log b (n / n₀) := by
        refine Nat.le_log_of_pow_le hb ?_
        rw [pow_one]
        exact (Nat.le_div_iff_mul_le hn₀).mpr (by rw [mul_comm]; exact hn)
      have hpow_eq : a ^ Nat.log b (n / n₀) = a * a ^ (Nat.log b (n / n₀) - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hk]
        rw [pow_succ']
      have hnat2 : a ^ Nat.log b (n / n₀) ≤ a * T n := by
        rw [hpow_eq]
        exact Nat.mul_le_mul_left a hnat1
      exact_mod_cast hnat2
  obtain ⟨C₀, _, hC₀⟩ := hpow_le
  have hlogb_nonneg : 0 ≤ Real.logb b (a : ℝ) :=
    Real.logb_nonneg (by exact_mod_cast hb) (by exact_mod_cast ha)
  refine IsBigO.of_bound ((2 * n₀ : ℝ) ^ Real.logb b a * a * C₀) ?_
  filter_upwards [eventually_ge_atTop (n₀ * b)] with n hn
  have hnn₀ : n₀ ≤ n := (Nat.le_mul_of_pos_right n₀ (by omega)).trans hn
  have hn_le : (n : ℝ) ≤ (2 * n₀ : ℝ) * ((n / n₀ : ℕ) : ℝ) := by
    exact_mod_cast nat_le_two_mul_div hn₀ hnn₀
  rw [Real.norm_of_nonneg (by positivity), Real.norm_natCast]
  calc (n : ℝ) ^ Real.logb b a
      ≤ ((2 * n₀ : ℝ) * ((n / n₀ : ℕ) : ℝ)) ^ Real.logb b a :=
        Real.rpow_le_rpow (by positivity) hn_le hlogb_nonneg
    _ = (2 * n₀ : ℝ) ^ Real.logb b a * ((n / n₀ : ℕ) : ℝ) ^ Real.logb b a :=
        Real.mul_rpow (by positivity) (by positivity)
    _ ≤ (2 * n₀ : ℝ) ^ Real.logb b a * ((a : ℝ) * (a : ℝ) ^ Nat.log b (n / n₀)) := by
        gcongr
        exact rpow_logb_le_mul_pow_log hb ha (n / n₀)
    _ ≤ (2 * n₀ : ℝ) ^ Real.logb b a * (a * (C₀ * T n)) := by
        gcongr
        exact hC₀ n hn
    _ = (2 * n₀ : ℝ) ^ Real.logb b a * a * C₀ * T n := by ring

/-- **Master theorem lower bound, case 2**: if `a = b ^ d` and `c ≥ 1`, then
`n ^ d log n = O(T)`. -/
theorem pow_mul_log_isBigO (h : DivideConquerLowerBound T a b n₀ T₀ fun n => c * n ^ d)
    (hb : 1 < b) (hn₀ : 1 ≤ n₀) (had : a = b ^ d) (hc : 1 ≤ c) :
    (fun n : ℕ => (n : ℝ) ^ d * Real.log n) =O[atTop] fun n => (T n : ℝ) := by
  have ha : 1 ≤ a := had ▸ Nat.one_le_pow d b (by omega)
  set M := Nat.log b n₀ + 1
  set N := n₀ * b ^ (M + 1)
  have hM : 1 ≤ M := Nat.succ_le_succ (Nat.zero_le _)
  have hN_pos : 1 ≤ N := Nat.mul_pos hn₀ (Nat.pow_pos (by omega))
  have hb' : (1 : ℝ) < b := by exact_mod_cast hb
  have hlogb : 0 < Real.log b := Real.log_pos hb'
  have hden : (0 : ℝ) < (c : ℝ) * n₀ ^ d := by
    have : 0 < c * n₀ ^ d := Nat.mul_pos hc (Nat.pow_pos hn₀)
    exact_mod_cast this
  refine IsBigO.of_bound (3 * Real.log b * ((n₀ * b : ℝ) ^ d) / ((c : ℝ) * n₀ ^ d)) ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnn₀ : n₀ ≤ n := (Nat.le_mul_of_pos_right n₀ (Nat.pow_pos (by omega))).trans hn
  have hn_pos : 1 ≤ n := hN_pos.trans hn
  set k := Nat.log b (n / n₀)
  have hk_ge : M + 1 ≤ k := by
    refine Nat.le_log_of_pow_le hb ?_
    exact (Nat.le_div_iff_mul_le hn₀).mpr (by rw [mul_comm]; exact hn)
  have hlt1 : n₀ < b ^ M := Nat.lt_pow_succ_log_self hb n₀
  have hlt2 : n / n₀ < b ^ (k + 1) := Nat.lt_pow_succ_log_self hb (n / n₀)
  have hn_ub : n ≤ n₀ * b ^ (k + 1) := by
    have hrem : n % n₀ < n₀ := Nat.mod_lt n hn₀
    have hdm := Nat.div_add_mod n n₀
    calc n = n₀ * (n / n₀) + n % n₀ := hdm.symm
      _ ≤ n₀ * (n / n₀) + n₀ := Nat.add_le_add_left hrem.le _
      _ = n₀ * (n / n₀ + 1) := by ring
      _ ≤ n₀ * b ^ (k + 1) := Nat.mul_le_mul_left n₀ hlt2
  have hlogn : Real.log n ≤ 3 * k * Real.log b := by
    have h1 : Real.log n ≤ Real.log ((n₀ : ℝ) * (b : ℝ) ^ (k + 1)) :=
      Real.log_le_log (by exact_mod_cast hn_pos) (by exact_mod_cast hn_ub)
    have h2 : Real.log (n₀ : ℝ) ≤ Real.log ((b : ℝ) ^ M) :=
      Real.log_le_log (by exact_mod_cast hn₀) (by exact_mod_cast hlt1.le)
    rw [Real.log_mul (by exact_mod_cast (by omega : n₀ ≠ 0)) (by positivity),
      Real.log_pow] at h1
    rw [Real.log_pow] at h2
    have hMk : (M : ℝ) ≤ k := by exact_mod_cast (by omega : M ≤ k)
    have hk1 : (k : ℝ) + 1 ≤ 2 * k := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      linarith
    push_cast at h1
    calc Real.log n ≤ Real.log n₀ + ((k : ℝ) + 1) * Real.log b := h1
      _ ≤ M * Real.log b + ((k : ℝ) + 1) * Real.log b := by gcongr
      _ ≤ k * Real.log b + (2 * k) * Real.log b := by gcongr
      _ = 3 * k * Real.log b := by ring
  have hnat : (c * n₀ ^ d * k * n ^ d : ℝ) ≤ ((n₀ * b : ℝ) ^ d) * T n := by
    exact_mod_cast h.mul_pow_mul_log_le ha hb hn₀ had hnn₀
  have hlog_nonneg : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [Real.norm_of_nonneg (by positivity), Real.norm_natCast]
  calc (n : ℝ) ^ d * Real.log n
      ≤ (n : ℝ) ^ d * (3 * k * Real.log b) := by gcongr
    _ = 3 * Real.log b * (c * n₀ ^ d * k * (n : ℝ) ^ d) / (c * n₀ ^ d) := by field_simp
    _ ≤ 3 * Real.log b * ((n₀ * b : ℝ) ^ d * T n) / (c * n₀ ^ d) := by gcongr
    _ = 3 * Real.log b * ((n₀ * b : ℝ) ^ d) / (c * n₀ ^ d) * T n := by ring

/-- The driving term lower-bounds `T` asymptotically: `f = O(T)`. -/
theorem driving_isBigO (h : DivideConquerLowerBound T a b n₀ T₀ f) :
    (fun n => (f n : ℝ)) =O[atTop] fun n => (T n : ℝ) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop n₀] with n hn
  rw [Real.norm_natCast, Real.norm_natCast, one_mul]
  exact_mod_cast h.driving_le hn

/-- **Master theorem lower bound, case 3**: if `c ≥ 1`, then `n ^ d = O(T)`. -/
theorem pow_isBigO (h : DivideConquerLowerBound T a b n₀ T₀ fun n => c * n ^ d) (hc : 1 ≤ c) :
    (fun n : ℕ => (n : ℝ) ^ d) =O[atTop] fun n => (T n : ℝ) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop n₀] with n hn
  rw [Real.norm_of_nonneg (by positivity), Real.norm_natCast, one_mul]
  have h1 : n ^ d ≤ c * n ^ d := Nat.le_mul_of_pos_left _ hc
  exact_mod_cast h1.trans (h.driving_le hn)

end DivideConquerLowerBound

namespace DivideConquerRecurrence

variable {T f : ℕ → ℕ} {a b n₀ T_lo T_hi c d : ℕ}

/-- **Master theorem, case 1** (`Θ`): if `b ^ d < a` and either `T_lo ≥ 1 ∧ b ≤ n₀ + 1` or
`c ≥ 1`, then `T = Θ(n ^ log_b a)`. -/
theorem isTheta_rpow (h : DivideConquerRecurrence T a b n₀ T_lo T_hi fun n => c * n ^ d)
    (hb : 1 < b) (hn₀ : 1 ≤ n₀) (hlt : b ^ d < a)
    (hcond : (1 ≤ T_lo ∧ b ≤ n₀ + 1) ∨ 1 ≤ c) :
    (fun n => (T n : ℝ)) =Θ[atTop] fun n => (n : ℝ) ^ Real.logb b a :=
  ⟨h.toBound.isBigO_rpow hb hn₀ hlt, h.toLowerBound.rpow_isBigO hb hn₀ hlt hcond⟩

/-- **Master theorem, case 2** (`Θ`): if `a = b ^ d` and `c ≥ 1`, then `T = Θ(n ^ d log n)`. -/
theorem isTheta_pow_mul_log (h : DivideConquerRecurrence T a b n₀ T_lo T_hi fun n => c * n ^ d)
    (hb : 1 < b) (hn₀ : 1 ≤ n₀) (had : a = b ^ d) (hc : 1 ≤ c) :
    (fun n => (T n : ℝ)) =Θ[atTop] fun n => (n : ℝ) ^ d * Real.log n :=
  ⟨h.toBound.isBigO_pow_mul_log hb hn₀ had, h.toLowerBound.pow_mul_log_isBigO hb hn₀ had hc⟩

/-- **Master theorem, case 3** (`Θ`): if `a < b ^ d` and `c ≥ 1`, then `T = Θ(n ^ d)`. -/
theorem isTheta_pow (h : DivideConquerRecurrence T a b n₀ T_lo T_hi fun n => c * n ^ d)
    (ha : 1 ≤ a) (hb : 1 < b) (hn₀ : 1 ≤ n₀) (hlt : a < b ^ d) (hc : 1 ≤ c) :
    (fun n => (T n : ℝ)) =Θ[atTop] fun n => (n : ℝ) ^ d :=
  ⟨h.toBound.isBigO_pow ha hb hn₀ hlt, h.toLowerBound.pow_isBigO hc⟩

/-- **Master theorem, case 3 under the general regularity condition** (`Θ`): if `f` is monotone,
eventually positive, and `a * f ⌈m/b⌉ ≤ ρ * f m` eventually for some `ρ < 1`, then
`T = Θ(f)`. -/
theorem isTheta_of_regular (h : DivideConquerRecurrence T a b n₀ T_lo T_hi f)
    (hb : 1 < b) (hn₀ : 1 ≤ n₀) (hf : Monotone f) {ρ : ℝ} (hρ : ρ < 1)
    (hreg : ∀ᶠ m in atTop, (a : ℝ) * f ((m + b - 1) / b) ≤ ρ * f m)
    (hfpos : ∀ᶠ m in atTop, 0 < f m) :
    (fun n => (T n : ℝ)) =Θ[atTop] fun n => (f n : ℝ) :=
  ⟨h.toBound.isBigO_of_regular hb hn₀ hf hρ hreg hfpos, h.toLowerBound.driving_isBigO⟩

end DivideConquerRecurrence

end Nat
