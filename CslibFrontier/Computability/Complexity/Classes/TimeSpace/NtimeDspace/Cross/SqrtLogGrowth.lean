/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.SqrtLogSublinear
public import Mathlib.Data.Nat.Log

/-!
# Growth of the `n / √log n` scale

`SqrtLog n = n / ⌊√⌊log₂ n⌋⌋ + 1` is not monotone: it drops where `⌊√⌊log₂ n⌋⌋` increases, for
example from `2 ^ 16 - 1` to `2 ^ 16`. It is monotone up to a factor `2`, and linear changes of the
argument change it by at most a constant factor. These are the regularity facts `D(2s) = O(D(s))`
and "nondecreasing" that Theorem 2.4 asks of its space bound `D`, here for `D = SqrtLog`.

## Main results

* `sqrtLog_le_two_mul_of_le`: `m ≤ m' → SqrtLog m ≤ 2 * SqrtLog m'`.
* `sqrtLog_mul_add_le`: `SqrtLog (a * m + b) ≤ (a + b + 1) * SqrtLog m` for `1 ≤ a`.
* `sqrtLog_le_of_le_mul_add`: the two combined.
* `lt_two_pow_sqrtLog`, `mul_add_le_two_pow`: the values of an argument below `2 ^ SqrtLog m`.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Cross

theorem log2_mono {m m' : ℕ} (h : m ≤ m') : m.log2 ≤ m'.log2 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono_right h

theorem sqrtLog_le_succ (m : ℕ) : SqrtLog m ≤ m + 1 :=
  Nat.add_le_add_right (Nat.div_le_self _ _) _

/-- `m < 2 ^ SqrtLog m`. -/
theorem lt_two_pow_sqrtLog (m : ℕ) : m < 2 ^ SqrtLog m :=
  Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by norm_num) (log2_add_one_le_sqrtLog m))

/-- **`SqrtLog` is monotone up to a factor `2`.** -/
theorem sqrtLog_le_two_mul_of_le {m m' : ℕ} (h : m ≤ m') : SqrtLog m ≤ 2 * SqrtLog m' := by
  unfold SqrtLog
  have hss' : Nat.sqrt m.log2 ≤ Nat.sqrt m'.log2 := Nat.sqrt_le_sqrt (log2_mono h)
  have hlogm : m.log2 + 1 ≤ (Nat.sqrt m.log2 + 1) * (Nat.sqrt m.log2 + 1) := Nat.lt_succ_sqrt _
  have hs'sq : Nat.sqrt m'.log2 * Nat.sqrt m'.log2 ≤ m'.log2 := Nat.sqrt_le _
  generalize Nat.sqrt m.log2 = s at *
  generalize Nat.sqrt m'.log2 = s' at *
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · rw [hs0, Nat.div_zero]
    generalize m' / s' = q
    omega
  by_cases hcase : s' ≤ 2 * s
  · have h1 : m / s ≤ m' / s := Nat.div_le_div_right h
    have h2 : m' / s ≤ 2 * (m' / (s * 2)) + 1 := by
      rw [← Nat.div_div_eq_div_mul]; omega
    have h3 : m' / (s * 2) ≤ m' / s' :=
      Nat.div_le_div_left (by omega) (by omega)
    omega
  · push Not at hcase
    -- here `m ≤ m' / s'`
    have hm : m < 2 ^ ((s + 1) * (s + 1)) :=
      Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by norm_num) hlogm)
    have hm'0 : m' ≠ 0 := by
      intro h0
      rw [h0] at hs'sq
      simp only [Nat.log2_zero, Nat.le_zero, mul_self_eq_zero] at hs'sq
      omega
    have hm' : 2 ^ (s' * s') ≤ m' :=
      (Nat.pow_le_pow_right (by norm_num) hs'sq).trans (Nat.log2_self_le hm'0)
    have hexp : (s + 1) * (s + 1) + s' ≤ s' * s' := by nlinarith
    have hms' : m * s' ≤ m' := by
      have h4 : m * s' ≤ 2 ^ ((s + 1) * (s + 1)) * 2 ^ s' :=
        Nat.mul_le_mul hm.le (Nat.lt_two_pow_self).le
      rw [← pow_add] at h4
      exact h4.trans ((Nat.pow_le_pow_right (by norm_num) hexp).trans hm')
    have h5 : m ≤ m' / s' := (Nat.le_div_iff_mul_le (by omega)).mpr hms'
    have h6 : m / s ≤ m := Nat.div_le_self _ _
    omega

/-- **Linear changes of the argument change `SqrtLog` by a constant factor.** -/
theorem sqrtLog_mul_add_le (a b m : ℕ) (ha : 1 ≤ a) :
    SqrtLog (a * m + b) ≤ (a + b + 1) * SqrtLog m := by
  unfold SqrtLog
  have hmle : m ≤ a * m + b := by nlinarith
  have hss' : Nat.sqrt m.log2 ≤ Nat.sqrt (a * m + b).log2 := Nat.sqrt_le_sqrt (log2_mono hmle)
  have hzero : Nat.sqrt m.log2 = 0 → m.log2 = 0 := Nat.sqrt_eq_zero.mp
  generalize Nat.sqrt m.log2 = s at *
  generalize Nat.sqrt (a * m + b).log2 = s' at *
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · have hlog : m.log2 = 0 := hzero hs0
    have hm : m < 2 := by
      have := Nat.lt_log2_self (n := m)
      rw [hlog] at this
      simpa using this
    rw [hs0, Nat.div_zero]
    have := Nat.div_le_self (a * m + b) s'
    have : a * m ≤ a := by
      calc a * m ≤ a * 1 := Nat.mul_le_mul_left _ (by omega)
        _ = a := by ring
    omega
  have h1 : (a * m + b) / s' ≤ (a * m + b) / s := Nat.div_le_div_left hss' hs0
  have h2 : (a * m + b) / s < a * (m / s) + a + b + 1 := by
    rw [Nat.div_lt_iff_lt_mul hs0]
    have hdm : m < s * (m / s) + s := by
      have := Nat.lt_div_mul_add (a := m) hs0
      rw [mul_comm] at this
      omega
    nlinarith
  have h3 : a * (m / s) + a + b + 1 ≤ (a + b + 1) * (m / s + 1) := by
    have : (a + b + 1) * (m / s + 1) = a * (m / s) + b * (m / s) + m / s + a + b + 1 := by ring
    generalize m / s = q at *
    omega
  generalize (a * m + b) / s' = q₁ at *
  generalize (a * m + b) / s = q₂ at *
  generalize m / s = q at *
  omega

/-- A value at most linear in `m` changes `SqrtLog` by a constant factor. -/
theorem sqrtLog_le_of_le_mul_add {τ m : ℕ} (a b : ℕ) (ha : 1 ≤ a) (h : τ ≤ a * m + b) :
    SqrtLog τ ≤ 2 * (a + b + 1) * SqrtLog m := by
  have := sqrtLog_le_two_mul_of_le h
  have := sqrtLog_mul_add_le a b m ha
  nlinarith

/-- A linear function of a value below `2 ^ s` is at most `2 ^ ((a + b + 1) * s)`. -/
theorem mul_add_le_two_pow {x s : ℕ} (a b : ℕ) (hx : x < 2 ^ s) (hs : 1 ≤ s) :
    a * x + b ≤ 2 ^ ((a + b + 1) * s) := by
  have hab : a + b < 2 ^ (a + b) := Nat.lt_two_pow_self
  have hpos : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  calc a * x + b ≤ a * 2 ^ s + b * 2 ^ s := by nlinarith
    _ = (a + b) * 2 ^ s := by ring
    _ ≤ 2 ^ (a + b) * 2 ^ s := Nat.mul_le_mul_right _ hab.le
    _ = 2 ^ (a + b + s) := (pow_add 2 (a + b) s).symm
    _ ≤ 2 ^ ((a + b + 1) * s) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

end Cslib.Complexity.NtimeDspace.Cross
