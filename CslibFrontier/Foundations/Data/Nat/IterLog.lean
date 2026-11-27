/-
Copyright (c) 2026 Renfei Zhou, vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.LogStar
public import CslibFrontier.Init
import CslibFrontier.Foundations.Data.Nat.Clog

/-!
# Iterated Base-2 Logarithms (`Nat.iterLog`, `Nat.iterClog`, and `Nat.iterClogBeta`)

`CslibFrontier/Foundations/Data/Nat/LogStar.lean` defines the tower of twos `Nat.twoTower` and its
ceiling-logarithm inverse `Nat.logStar` (the least `k` with `(Nat.clog 2)^[k] n ≤ 1`, equivalently
`n ≤ Nat.twoTower k`). This module supplies:

* the **iterated base-2 floor logarithm** `Nat.iterLog k n = (Nat.log 2)^[k] n` and its exact
  stopping count `Nat.floorLogStar n = Nat.logStar (n + 1) - 1` (the least `k` such that
  `Nat.iterLog k n ≤ 1`, equivalently `n < Nat.twoTower (k + 1)`);
* the **iterated base-2 ceiling logarithm** `Nat.iterClog k n = (Nat.clog 2)^[k] n`, its Galois
  adjoint **iterated base-2 exponential tower** `Nat.iterPow2 k x = (2 ^ ·)^[k] x`, and the
  generalized stopping index `Nat.iterClogBeta t n` (the least `k ≥ 1` with
  `Nat.iterClog k n ≤ max 1 t`, equivalently `n ≤ Nat.iterPow2 k (max 1 t)`).

Naming the floor stopping count `Nat.floorLogStar` avoids collision with the ceiling convention
`Nat.logStar` (whose values differ at `n = 3` and `n = 5, …, 15`), while defining it in terms of
`Nat.logStar` avoids duplicating structural fuel recursion and provides exact floor-logarithm
recurrence laws (`floorLogStar_of_gt_one : 1 < n → floorLogStar n = floorLogStar (Nat.log 2 n) + 1`
and `lt_floorLogStar_iff : k < floorLogStar n ↔ 1 < iterLog k n`).

## Main definitions

* `Nat.iterLog`: iterated base-2 floor logarithm `⌊log₂^(k) n⌋`.
* `Nat.floorLogStar`: base-2 floor iterated logarithm `Nat.logStar (n + 1) - 1`, the least `k` with
  `iterLog k n ≤ 1`.
* `Nat.iterClog`: iterated base-2 ceiling logarithm `⌈log₂^(k) n⌉`.
* `Nat.iterPow2`: iterated base-2 exponential tower `(2 ^ ·)^[k] x`.
* `Nat.iterClogBeta`: generalized stopping index, the least `k ≥ 1` with
  `iterClog k n ≤ max 1 t`.

## Main results

* `Nat.iterLog_eq_iterate`, `Nat.iterLog_succ_apply`, `Nat.iterLog_add`: iteration laws.
* `Nat.iterLog_mono`, `Nat.iterLog_anti_left`: monotonicity in `n` and antitonicity in `k`.
* `Nat.iterLog_le_one_iff_lt_twoTower`: `iterLog k n ≤ 1 ↔ n < twoTower (k + 1)`.
* `Nat.floorLogStar_of_le_one`, `Nat.floorLogStar_of_gt_one`: base and `Nat.log 2` step equations.
* `Nat.iterLog_floorLogStar_le_one`, `Nat.lt_floorLogStar_iff`, `Nat.floorLogStar_le_iff`: exact
  threshold characterizations `k < floorLogStar n ↔ 1 < iterLog k n` and
  `floorLogStar n ≤ k ↔ iterLog k n ≤ 1`.
* `Nat.floorLogStar_mono`, `Nat.floorLogStar_le_logStar`, `Nat.logStar_le_floorLogStar_add_one`:
  monotonicity and comparison within `1` of ceiling `Nat.logStar`.
* `Nat.sub_le_iterLog_of_lt_floorLogStar`, `Nat.four_le_floorLogStar_two_pow`,
  `Nat.six_mul_iterLog_two_two_pow_le`: remaining-step lower bound and dyadic threshold bounds for
  `32 ≤ m`.
* `Nat.max_iterLog_two_max_four`, `Nat.max_iterLog_two_eq`, `Nat.iterLog_two_max_four_le_clog`,
  `Nat.clog_clog_max_four_le_two_mul_iterLog`: positivity, clamping identity, and ceiling
  comparison at `k = 2`.
* `Nat.iterClog_le_iff_le_iterPow2`, `Nat.iterClog_mono`, `Nat.iterClog_anti_left`,
  `Nat.iterLog_le_iterClog`, `Nat.iterClog_le_iterLog_add_one`: Galois correspondence,
  monotonicity, and floor/ceiling comparisons for `iterClog` and `iterPow2`.
* `Nat.iterClogBeta_le_iff`, `Nat.iterClogBeta_le_iff_le_iterPow2`,
  `Nat.iterClogBeta_mono_right`, `Nat.iterClogBeta_anti_left`, `Nat.iterClogBeta_of_le_one`:
  threshold characterization, monotonicity, and `logStar` specialization for `iterClogBeta`.
* `Nat.iterClogBeta_lt_of_two_pow_le`, `Nat.iterClogBeta_div_lt_of_mul_le`,
  `Nat.mul_iterClogBeta_le_of_div_le`, `Nat.mul_iterClogBeta_div_le_iterLog`: strict phase-rank
  drop and `k`-parameterized multiplicative bounds for `t = 2 * m / n`.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*, Section 3, pp. 606–607][FredmanTarjan1987]
-/

public section

namespace Nat

/-- Iterated base-2 floor logarithm `⌊log₂^(k) n⌋`: `iterLog 0 n = n` and
`iterLog (k + 1) n = Nat.log 2 (iterLog k n)`. -/
@[expose] def iterLog : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => Nat.log 2 (iterLog k n)

@[simp]
theorem iterLog_zero (n : ℕ) : iterLog 0 n = n := rfl

@[simp]
theorem iterLog_succ (k n : ℕ) : iterLog (k + 1) n = Nat.log 2 (iterLog k n) := rfl

/-- `iterLog k` agrees with `k`-fold function iteration of `Nat.log 2`. -/
theorem iterLog_eq_iterate (k n : ℕ) : iterLog k n = (Nat.log 2)^[k] n := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterLog_succ, Function.iterate_succ_apply', ih]

/-- Applying `Nat.log 2` before `k` iterations is the same as `k + 1` iterations. -/
theorem iterLog_succ_apply (k n : ℕ) : iterLog (k + 1) n = iterLog k (Nat.log 2 n) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterLog_succ, ih, iterLog_succ]

/-- Addition of iteration counts composes `iterLog`. -/
theorem iterLog_add (j k n : ℕ) : iterLog (j + k) n = iterLog j (iterLog k n) := by
  induction j with
  | zero => simp
  | succ j ih => simp only [Nat.succ_add, iterLog_succ, ih]

@[simp]
theorem iterLog_zero_right (k : ℕ) : iterLog k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ih]

theorem iterLog_one_of_pos {k : ℕ} (hk : 1 ≤ k) : iterLog k 1 = 0 := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm, iterLog_succ_apply]
  simp

/-- `iterLog k n` never exceeds `n`. -/
theorem iterLog_le_self (k n : ℕ) : iterLog k n ≤ n := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (Nat.log_le_self 2 (iterLog k n)).trans ih

/-- `iterLog k` is monotone in its second argument. -/
theorem iterLog_mono (k : ℕ) : Monotone (iterLog k) := by
  intro m n h
  induction k with
  | zero => exact h
  | succ k ih => exact Nat.log_mono_right ih

/-- `iterLog k n` is antitone in the iteration count `k`. -/
theorem iterLog_anti_left {j k : ℕ} (n : ℕ) (h : j ≤ k) : iterLog k n ≤ iterLog j n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm, iterLog_add]
  exact iterLog_le_self d (iterLog j n)

/-- Whenever `1 < iterLog k n`, one more base-2 logarithm strictly decreases it. -/
theorem iterLog_lt_of_gt_one {k n : ℕ} (h : 1 < iterLog k n) :
    iterLog (k + 1) n < iterLog k n :=
  Nat.log_lt_self 2 (by omega)

/-- `iterLog k n ≤ 1` holds iff `n` is strictly below `twoTower (k + 1)`. -/
theorem iterLog_le_one_iff_lt_twoTower {k n : ℕ} :
    iterLog k n ≤ 1 ↔ n < twoTower (k + 1) := by
  induction k generalizing n with
  | zero => simp [iterLog, twoTower]; omega
  | succ k ih =>
    rw [iterLog_succ_apply, ih, twoTower_succ]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [twoTower_pos, Nat.two_pow_pos]
    · exact Nat.log_lt_iff_lt_pow Nat.one_lt_two hn.ne'

/-- Base-2 floor iterated logarithm: the least `k : ℕ` such that `iterLog k n ≤ 1`,
expressed via `logStar (n + 1) - 1` so it shares `logStar`'s structural kernel reduction. -/
@[expose] def floorLogStar (n : ℕ) : ℕ :=
  logStar (n + 1) - 1

/-- Threshold characterization: `floorLogStar n ≤ k` iff `iterLog k n ≤ 1`. -/
theorem floorLogStar_le_iff {k n : ℕ} : floorLogStar n ≤ k ↔ iterLog k n ≤ 1 := by
  rw [floorLogStar, Nat.sub_le_iff_le_add, logStar_le_iff, iterLog_le_one_iff_lt_twoTower]
  omega

/-- Strict threshold characterization: `k < floorLogStar n` iff `1 < iterLog k n`. -/
theorem lt_floorLogStar_iff {k n : ℕ} : k < floorLogStar n ↔ 1 < iterLog k n := by
  rw [← not_le, floorLogStar_le_iff, not_le]

/-- After `floorLogStar n` iterations, `iterLog` reaches at most `1`. -/
theorem iterLog_floorLogStar_le_one (n : ℕ) : iterLog (floorLogStar n) n ≤ 1 :=
  floorLogStar_le_iff.mp le_rfl

/-- Base equation: `floorLogStar n = 0` for `n ≤ 1`. -/
theorem floorLogStar_of_le_one {n : ℕ} (hn : n ≤ 1) : floorLogStar n = 0 :=
  Nat.le_zero.mp (floorLogStar_le_iff.mpr hn)

@[simp]
theorem floorLogStar_zero : floorLogStar 0 = 0 := rfl

@[simp]
theorem floorLogStar_one : floorLogStar 1 = 0 := rfl

/-- Step equation: for `1 < n`, `floorLogStar n = floorLogStar (Nat.log 2 n) + 1`. -/
theorem floorLogStar_of_gt_one {n : ℕ} (hn : 1 < n) :
    floorLogStar n = floorLogStar (Nat.log 2 n) + 1 := by
  apply le_antisymm
  · rw [floorLogStar_le_iff, iterLog_succ_apply]
    exact iterLog_floorLogStar_le_one (Nat.log 2 n)
  · have hpos : 0 < floorLogStar n := lt_floorLogStar_iff.mpr hn
    rw [← Nat.le_sub_iff_add_le hpos, floorLogStar_le_iff, ← iterLog_succ_apply,
      Nat.sub_add_cancel hpos]
    exact iterLog_floorLogStar_le_one n

@[simp]
theorem floorLogStar_two : floorLogStar 2 = 1 := rfl

/-- `floorLogStar` is monotone. -/
theorem floorLogStar_mono : Monotone floorLogStar := fun _ n h =>
  floorLogStar_le_iff.mpr ((iterLog_mono (floorLogStar n) h).trans (iterLog_floorLogStar_le_one n))

/-- Floor `floorLogStar` never exceeds ceiling `logStar`. -/
theorem floorLogStar_le_logStar (n : ℕ) : floorLogStar n ≤ logStar n := by
  rw [floorLogStar_le_iff, iterLog_le_one_iff_lt_twoTower]
  exact lt_of_le_of_lt (le_twoTower_logStar n) (twoTower_lt_twoTower_succ _)

/-- Ceiling `logStar` exceeds floor `floorLogStar` by at most `1`. -/
theorem logStar_le_floorLogStar_add_one (n : ℕ) : logStar n ≤ floorLogStar n + 1 := by
  rw [logStar_le_iff]
  exact (iterLog_le_one_iff_lt_twoTower.mp (iterLog_floorLogStar_le_one n)).le

/-- `floorLogStar n` never exceeds `n`. -/
theorem floorLogStar_le_self (n : ℕ) : floorLogStar n ≤ n :=
  (floorLogStar_le_logStar n).trans (logStar_le_self n)

/-- Clamping at `4` makes the two-step floor logarithm at least `1`. -/
theorem one_le_iterLog_two_max_four (n : ℕ) : 1 ≤ iterLog 2 (max n 4) :=
  Nat.le_trans (by decide) (iterLog_mono 2 (_root_.le_max_right n 4))

/-- Exact clamping bridge: `max (iterLog 2 (max n 4)) 1 = iterLog 2 (max n 4)`. -/
theorem max_iterLog_two_max_four (n : ℕ) :
    max (iterLog 2 (max n 4)) 1 = iterLog 2 (max n 4) :=
  _root_.max_eq_left (one_le_iterLog_two_max_four n)

/-- Clamping `iterLog 2 n` below at `1` agrees everywhere with `iterLog 2 (max n 4)`. -/
theorem max_iterLog_two_eq (n : ℕ) : max (iterLog 2 n) 1 = iterLog 2 (max n 4) := by
  by_cases hn : n < 4
  · match n, hn with | 0, _ => decide | 1, _ => decide | 2, _ => decide | 3, _ => decide
  · simpa [_root_.max_eq_left (Nat.not_lt.mp hn)] using max_iterLog_two_max_four n

/-- If `d < floorLogStar n` and `r ≤ d`, at least `d + 1 - r` remains in `iterLog (r + 1) n`. -/
theorem sub_le_iterLog_of_lt_floorLogStar {n d r : ℕ} (hd : d < floorLogStar n)
    (hr : r ≤ d) : d + 1 - r ≤ iterLog (r + 1) n := by
  have h1 : 1 < iterLog ((d - r) + r) n := lt_floorLogStar_iff.mp (by omega)
  rw [iterLog_add, ← not_le, iterLog_le_one_iff_lt_twoTower, not_lt, twoTower_succ] at h1
  have : twoTower (d - r) ≤ iterLog (r + 1) n :=
    (Nat.log_pow Nat.one_lt_two _).symm.trans_le (Nat.log_mono_right h1)
  have := lt_twoTower (d - r)
  omega

/-- For `32 ≤ m`, `2 ^ m` requires at least `4` floor-logarithm steps to reach `≤ 1`. -/
theorem four_le_floorLogStar_two_pow {m : ℕ} (hm : 32 ≤ m) : 4 ≤ floorLogStar (2 ^ m) :=
  Nat.succ_le_of_lt (lt_floorLogStar_iff.mpr ((show 1 < iterLog 3 (2 ^ 32) by decide).trans_le
    (iterLog_mono 3 (Nat.pow_le_pow_right (by omega) hm))))

/-- For `32 ≤ m`, `6 * iterLog 2 (2 ^ m) ≤ m`. -/
theorem six_mul_iterLog_two_two_pow_le {m : ℕ} (hm : 32 ≤ m) : 6 * iterLog 2 (2 ^ m) ≤ m := by
  have h5 : 5 ≤ Nat.log 2 m := (show 5 = Nat.log 2 32 by decide) ▸ Nat.log_mono_right hm
  have := Nat.mul_le_mul_right (2 ^ 5) (Nat.lt_two_pow_self (n := Nat.log 2 m - 5))
  rw [← Nat.pow_add, Nat.sub_add_cancel h5] at this
  have : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
  rw [show iterLog 2 (2 ^ m) = Nat.log 2 m by simp [Nat.log_pow Nat.one_lt_two]]
  omega

/-- Floor-to-ceiling lower bound: `iterLog 2 (max n 4) ≤ ⌈log₂ ⌈log₂ (max n 4)⌉⌉`. -/
theorem iterLog_two_max_four_le_clog (n : ℕ) :
    iterLog 2 (max n 4) ≤ Nat.clog 2 (Nat.clog 2 (max n 4)) :=
  (Nat.log_mono_right (Nat.log_le_clog 2 (max n 4))).trans (Nat.log_le_clog 2 _)

/-- Ceiling-to-floor upper bound: `⌈log₂ ⌈log₂ (max n 4)⌉⌉ ≤ 2 * iterLog 2 (max n 4)`. -/
theorem clog_clog_max_four_le_two_mul_iterLog (n : ℕ) :
    Nat.clog 2 (Nat.clog 2 (max n 4)) ≤ 2 * iterLog 2 (max n 4) := by
  set m := max n 4
  set k := iterLog 2 m
  have hm_lt : m < 2 ^ (2 ^ (k + 1)) :=
    calc m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two m
      _ ≤ 2 ^ (2 ^ (k + 1)) := Nat.pow_le_pow_right Nat.two_pos
          (Nat.lt_pow_succ_log_self Nat.one_lt_two (Nat.log 2 m))
  have hclog : Nat.clog 2 (Nat.clog 2 m) ≤ k + 1 := (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr
    ((Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr hm_lt.le)
  have hk : 1 ≤ k := one_le_iterLog_two_max_four n
  omega

/-! ### Iterated base-2 ceiling logarithm and exponential tower -/

/-- Iterated base-2 ceiling logarithm `⌈log₂^(k) n⌉`: `iterClog 0 n = n` and
`iterClog (k + 1) n = Nat.clog 2 (iterClog k n)`. -/
@[expose] def iterClog : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => Nat.clog 2 (iterClog k n)

/-- Zero-iteration ceiling logarithm is the identity. -/
@[simp]
theorem iterClog_zero (n : ℕ) : iterClog 0 n = n := rfl

/-- One more ceiling-logarithm step applies `Nat.clog 2` to the outside. -/
@[simp]
theorem iterClog_succ (k n : ℕ) : iterClog (k + 1) n = Nat.clog 2 (iterClog k n) := rfl

/-- `iterClog k` agrees with `k`-fold function iteration of `Nat.clog 2`. -/
theorem iterClog_eq_iterate (k n : ℕ) : iterClog k n = (Nat.clog 2)^[k] n := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterClog_succ, Function.iterate_succ_apply', ih]

/-- Applying `Nat.clog 2` before `k` iterations is the same as `k + 1` iterations. -/
theorem iterClog_succ_apply (k n : ℕ) : iterClog (k + 1) n = iterClog k (Nat.clog 2 n) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterClog_succ, ih, iterClog_succ]

/-- Addition of iteration counts composes `iterClog`. -/
theorem iterClog_add (j k n : ℕ) : iterClog (j + k) n = iterClog j (iterClog k n) := by
  induction j with
  | zero => simp
  | succ j ih => simp only [Nat.succ_add, iterClog_succ, ih]

/-- Iterated ceiling logarithm of `0` is `0`. -/
@[simp]
theorem iterClog_zero_right (k : ℕ) : iterClog k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ih]

/-- Positive-iteration ceiling logarithm of `1` is `0`. -/
theorem iterClog_one_of_pos {k : ℕ} (hk : 1 ≤ k) : iterClog k 1 = 0 := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm, iterClog_succ_apply]
  simp

/-- `iterClog k n` never exceeds `n`. -/
theorem iterClog_le_self (k n : ℕ) : iterClog k n ≤ n := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (Nat.clog_le_self 2 (iterClog k n)).trans ih

/-- `iterClog k` is monotone in its second argument. -/
theorem iterClog_mono (k : ℕ) : Monotone (iterClog k) := by
  intro m n h
  induction k with
  | zero => exact h
  | succ k ih => exact Nat.clog_mono_right 2 ih

/-- `iterClog k n` is antitone in the iteration count `k`. -/
theorem iterClog_anti_left {j k : ℕ} (n : ℕ) (h : j ≤ k) : iterClog k n ≤ iterClog j n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm, iterClog_add]
  exact iterClog_le_self d (iterClog j n)

/-- Whenever `2 ≤ iterClog k n`, one more base-2 ceiling logarithm strictly decreases it. -/
theorem iterClog_lt_of_two_le {k n : ℕ} (h : 2 ≤ iterClog k n) :
    iterClog (k + 1) n < iterClog k n := by
  have : Nat.clog 2 (iterClog k n) ≤ iterClog k n - 1 :=
    (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr
      (by have := Nat.lt_two_pow_self (n := iterClog k n - 1); omega)
  change Nat.clog 2 (iterClog k n) < iterClog k n
  omega

/-- Iterated floor logarithm never exceeds iterated ceiling logarithm. -/
theorem iterLog_le_iterClog (k n : ℕ) : iterLog k n ≤ iterClog k n := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (Nat.log_mono_right ih).trans (Nat.log_le_clog 2 _)

private theorem clog_two_succ_le_log_succ (y : ℕ) : Nat.clog 2 (y + 1) ≤ Nat.log 2 y + 1 :=
  (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr (Nat.lt_pow_succ_log_self Nat.one_lt_two y)

/-- For `k ≥ 1`, `iterClog k n ≤ iterLog k n + 1`. -/
theorem iterClog_le_iterLog_add_one {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    iterClog k n ≤ iterLog k n + 1 := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm]
  induction k' with
  | zero =>
    dsimp only [Nat.zero_add, iterClog, iterLog]
    rcases Nat.eq_zero_or_pos n with rfl | _
    · decide
    · exact (Nat.clog_mono_right 2 (Nat.le_succ n)).trans (clog_two_succ_le_log_succ n)
  | succ k' ih =>
    rw [iterClog_succ, iterLog_succ]
    exact (Nat.clog_mono_right 2 (ih (by omega))).trans (clog_two_succ_le_log_succ _)

/-- Iterated base-2 exponential tower `(2 ^ ·)^[k] x`: `iterPow2 0 x = x` and
`iterPow2 (k + 1) x = 2 ^ iterPow2 k x`. -/
@[expose] def iterPow2 : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => 2 ^ iterPow2 k x

/-- Zero-iteration exponential tower is the identity. -/
@[simp]
theorem iterPow2_zero (x : ℕ) : iterPow2 0 x = x := rfl

/-- One more tower step exponentiates with base `2`. -/
@[simp]
theorem iterPow2_succ (k x : ℕ) : iterPow2 (k + 1) x = 2 ^ iterPow2 k x := rfl

/-- `iterPow2 k` agrees with `k`-fold function iteration of `(2 ^ ·)`. -/
theorem iterPow2_eq_iterate (k x : ℕ) : iterPow2 k x = (2 ^ ·)^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterPow2_succ, Function.iterate_succ_apply', ih]

/-- Applying `(2 ^ ·)` before `k` iterations is the same as `k + 1` iterations. -/
theorem iterPow2_succ_apply (k x : ℕ) : iterPow2 (k + 1) x = iterPow2 k (2 ^ x) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterPow2_succ, ih, iterPow2_succ]

/-- Addition of iteration counts composes `iterPow2`. -/
theorem iterPow2_add (j k x : ℕ) : iterPow2 (j + k) x = iterPow2 j (iterPow2 k x) := by
  induction j with
  | zero => simp
  | succ j ih => simp only [Nat.succ_add, iterPow2_succ, ih]

/-- Starting `iterPow2` from `1` gives `twoTower`. -/
@[simp]
theorem iterPow2_one_right (k : ℕ) : iterPow2 k 1 = twoTower k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterPow2_succ, twoTower_succ, ih]

/-- `iterPow2 k` is strictly monotone in its second argument. -/
theorem iterPow2_strictMono (k : ℕ) : StrictMono (iterPow2 k) := by
  intro a b hab
  induction k with
  | zero => exact hab
  | succ k ih => exact Nat.pow_lt_pow_right Nat.one_lt_two ih

/-- `iterPow2 k` is monotone in its second argument. -/
theorem iterPow2_mono (k : ℕ) : Monotone (iterPow2 k) :=
  (iterPow2_strictMono k).monotone

/-- `iterPow2 k x` is always at least `x`. -/
theorem le_iterPow2 (k x : ℕ) : x ≤ iterPow2 k x := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans Nat.lt_two_pow_self.le

/-- `iterPow2 k x` is positive whenever `1 ≤ k`. -/
theorem iterPow2_pos_of_pos_left {k : ℕ} (hk : 1 ≤ k) (x : ℕ) : 0 < iterPow2 k x := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm, iterPow2_succ]
  exact Nat.two_pow_pos _

/-- Galois correspondence: `iterClog k n ≤ x` iff `n ≤ iterPow2 k x`. -/
theorem iterClog_le_iff_le_iterPow2 (k n x : ℕ) : iterClog k n ≤ x ↔ n ≤ iterPow2 k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [iterClog_succ, Nat.clog_le_iff_le_pow Nat.one_lt_two, ih, iterPow2_succ_apply]

/-- `iterClog k n ≤ 1` holds iff `logStar n ≤ k`. -/
theorem iterClog_le_one_iff_logStar_le (k n : ℕ) : iterClog k n ≤ 1 ↔ logStar n ≤ k := by
  rw [iterClog_le_iff_le_iterPow2, iterPow2_one_right, logStar_le_iff]

/-! ### Generalized iterated-logarithm stopping index (`iterClogBeta`) -/

/-- Bounded upward search helper for `iterClogBeta`: `iterClogBetaAux t n fuel k` scans upward
from `k` through `k + fuel` for the least `m ≥ k` satisfying `iterClog m n ≤ max 1 t`. When
`fuel = 0`, it returns `k` unconditionally even if `max 1 t < iterClog k n`; it is guaranteed to
return the least satisfying `m ≥ k` only under the precondition `iterClog (k + fuel) n ≤ max 1 t`,
and otherwise returns `k + fuel`. -/
@[expose] def iterClogBetaAux (t n : ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | fuel + 1, k =>
    if iterClog k n ≤ max 1 t then k else iterClogBetaAux t n fuel (k + 1)

/-- Generalized iterated-logarithm stopping index `β(t, n)`: the least `k ≥ 1` such that
`iterClog k n ≤ max 1 t` (equivalently `n ≤ iterPow2 k (max 1 t)`). Specializing `t = 2 * m / n`
yields the two-parameter threshold function used in dense-graph elimination rounds. -/
@[expose] def iterClogBeta (t n : ℕ) : ℕ :=
  iterClogBetaAux t n (Nat.clog 2 n) 1

private theorem iterClogBetaAux_spec {t n : ℕ} :
    ∀ (fuel k : ℕ), iterClog (k + fuel) n ≤ max 1 t →
      k ≤ iterClogBetaAux t n fuel k ∧
      iterClog (iterClogBetaAux t n fuel k) n ≤ max 1 t ∧
      ∀ m, k ≤ m → iterClog m n ≤ max 1 t → iterClogBetaAux t n fuel k ≤ m
  | 0, k, h => ⟨le_rfl, h, fun _ hm _ => hm⟩
  | fuel + 1, k, h => by
    rw [iterClogBetaAux]
    split_ifs with hle
    · exact ⟨le_rfl, hle, fun _ hm _ => hm⟩
    · have h' : iterClog ((k + 1) + fuel) n ≤ max 1 t := by rwa [Nat.add_right_comm]
      obtain ⟨hk1, htarget, hmin⟩ := iterClogBetaAux_spec fuel (k + 1) h'
      refine ⟨(Nat.le_succ k).trans hk1, htarget, fun m hm hm_le => ?_⟩
      rcases Nat.eq_or_lt_of_le hm with rfl | hkm
      · exact absurd hm_le hle
      · exact hmin m hkm hm_le

private theorem iterClogBeta_spec (t n : ℕ) :
    1 ≤ iterClogBeta t n ∧
    iterClog (iterClogBeta t n) n ≤ max 1 t ∧
    ∀ m, 1 ≤ m → iterClog m n ≤ max 1 t → iterClogBeta t n ≤ m := by
  refine iterClogBetaAux_spec (Nat.clog 2 n) 1 ?_
  rw [Nat.add_comm, iterClog_add]
  have h1 : iterClog (Nat.clog 2 n) (Nat.clog 2 n) ≤ 1 :=
    (iterClog_le_iff_le_iterPow2 _ _ 1).mpr
      (by rw [iterPow2_one_right]; exact (lt_twoTower _).le)
  exact h1.trans (Nat.le_max_left 1 t)

/-- `iterClogBeta t n` is always at least `1`. -/
theorem one_le_iterClogBeta (t n : ℕ) : 1 ≤ iterClogBeta t n :=
  (iterClogBeta_spec t n).1

/-- After `iterClogBeta t n` iterations, `iterClog` drops to at most `max 1 t`. -/
theorem iterClog_iterClogBeta_le (t n : ℕ) : iterClog (iterClogBeta t n) n ≤ max 1 t :=
  (iterClogBeta_spec t n).2.1

/-- Tower characterization of `iterClogBeta`: `n ≤ iterPow2 (iterClogBeta t n) (max 1 t)`. -/
theorem le_iterPow2_iterClogBeta (t n : ℕ) : n ≤ iterPow2 (iterClogBeta t n) (max 1 t) :=
  (iterClog_le_iff_le_iterPow2 _ n (max 1 t)).mp (iterClog_iterClogBeta_le t n)

/-- Threshold characterization for `1 ≤ k`: `iterClogBeta t n ≤ k ↔ iterClog k n ≤ max 1 t`. -/
theorem iterClogBeta_le_iff {t n k : ℕ} (hk : 1 ≤ k) :
    iterClogBeta t n ≤ k ↔ iterClog k n ≤ max 1 t :=
  ⟨fun h => (iterClog_anti_left n h).trans (iterClog_iterClogBeta_le t n),
    (iterClogBeta_spec t n).2.2 k hk⟩

/-- Tower threshold characterization for `1 ≤ k`:
`iterClogBeta t n ≤ k ↔ n ≤ iterPow2 k (max 1 t)`. -/
theorem iterClogBeta_le_iff_le_iterPow2 {t n k : ℕ} (hk : 1 ≤ k) :
    iterClogBeta t n ≤ k ↔ n ≤ iterPow2 k (max 1 t) :=
  (iterClogBeta_le_iff hk).trans (iterClog_le_iff_le_iterPow2 k n (max 1 t))

/-- Strict threshold characterization for `1 ≤ k`:
`k < iterClogBeta t n ↔ max 1 t < iterClog k n`. -/
theorem lt_iterClogBeta_iff {t n k : ℕ} (hk : 1 ≤ k) :
    k < iterClogBeta t n ↔ max 1 t < iterClog k n := by
  rw [← not_le, iterClogBeta_le_iff hk, not_le]

/-- `iterClogBeta t n = 1` iff `n ≤ 2 ^ max 1 t`. -/
theorem iterClogBeta_eq_one_iff {t n : ℕ} : iterClogBeta t n = 1 ↔ n ≤ 2 ^ max 1 t := by
  rw [le_antisymm_iff, and_iff_left (one_le_iterClogBeta t n),
    iterClogBeta_le_iff_le_iterPow2 le_rfl, iterPow2_succ, iterPow2_zero]

/-- When `t ≤ 1`, `iterClogBeta t n` equals `max 1 (logStar n)`. -/
theorem iterClogBeta_of_le_one {t : ℕ} (ht : t ≤ 1) (n : ℕ) :
    iterClogBeta t n = max 1 (logStar n) := by
  have hmax : max 1 t = 1 := Nat.max_eq_left ht
  refine le_antisymm ?_ ?_
  · rw [iterClogBeta_le_iff_le_iterPow2 (le_max_left 1 _), hmax, iterPow2_one_right]
    exact (le_twoTower_logStar n).trans (twoTower_monotone (le_max_right 1 _))
  · exact max_le (one_le_iterClogBeta t n)
      (logStar_le_iff.mpr (by simpa [hmax] using le_iterPow2_iterClogBeta t n))

/-- `iterClogBeta t` is monotone in its second argument. -/
theorem iterClogBeta_mono_right (t : ℕ) : Monotone (iterClogBeta t) := fun _ b hab =>
  (iterClogBeta_le_iff (one_le_iterClogBeta t b)).mpr
    ((iterClog_mono _ hab).trans (iterClog_iterClogBeta_le t b))

/-- `iterClogBeta` is antitone in its threshold parameter `t`. -/
theorem iterClogBeta_anti_left (n : ℕ) : Antitone (fun t => iterClogBeta t n) := fun a _ hab =>
  (iterClogBeta_le_iff (one_le_iterClogBeta a n)).mpr
    ((iterClog_iterClogBeta_le a n).trans (max_le_max_left 1 hab))

/-- `iterClogBeta t n` never exceeds `max 1 (logStar n)`. -/
theorem iterClogBeta_le_max_one_logStar (t n : ℕ) : iterClogBeta t n ≤ max 1 (logStar n) :=
  (iterClogBeta_anti_left n (Nat.zero_le t)).trans (iterClogBeta_of_le_one (Nat.zero_le 1) n).le

private theorem iterClog_add_le_of_le_add {t n : ℕ} :
    ∀ f j, iterClog j n ≤ max 1 t + f → iterClog (j + f) n ≤ max 1 t
  | 0, j, h => by simpa using h
  | f + 1, j, h => by
    by_cases hc : iterClog j n ≤ max 1 t
    · exact (iterClog_anti_left n (Nat.le_add_right j _)).trans hc
    · have hge2 : 2 ≤ iterClog j n := by
        have := le_max_left 1 t
        omega
      have hlt : iterClog (j + 1) n < iterClog j n := iterClog_lt_of_two_le hge2
      have hrec := @iterClog_add_le_of_le_add t n f (j + 1) (by omega)
      rwa [Nat.add_right_comm] at hrec

/-- For `1 ≤ k`, `iterClogBeta t n ≤ k + iterClog k n`. -/
theorem iterClogBeta_le_add_iterClog {k : ℕ} (hk : 1 ≤ k) (t n : ℕ) :
    iterClogBeta t n ≤ k + iterClog k n :=
  (iterClogBeta_le_iff (by omega : 1 ≤ k + iterClog k n)).mpr
    (iterClog_add_le_of_le_add (iterClog k n) k (Nat.le_add_left _ _))

/-- Strictly shrinking step: if `n₂ ≤ n₁`, `2 ^ max 1 t₁ < n₁`, and `2 ^ max 1 t₁ ≤ max 1 t₂`,
then `iterClogBeta t₂ n₂ < iterClogBeta t₁ n₁`. -/
theorem iterClogBeta_lt_of_two_pow_le {t₁ t₂ n₁ n₂ : ℕ} (hn : n₂ ≤ n₁)
    (hgt : 2 ^ max 1 t₁ < n₁) (hstep : 2 ^ max 1 t₁ ≤ max 1 t₂) :
    iterClogBeta t₂ n₂ < iterClogBeta t₁ n₁ := by
  have hge2 : 2 ≤ iterClogBeta t₁ n₁ :=
    Nat.lt_of_le_of_ne (one_le_iterClogBeta t₁ n₁)
      (Ne.symm (mt iterClogBeta_eq_one_iff.mp hgt.not_ge))
  have hcur : n₁ ≤ iterPow2 (iterClogBeta t₁ n₁) (max 1 t₁) := le_iterPow2_iterClogBeta t₁ n₁
  rw [← Nat.sub_add_cancel (one_le_iterClogBeta t₁ n₁), iterPow2_succ_apply] at hcur
  have hle : iterClogBeta t₂ n₂ ≤ iterClogBeta t₁ n₁ - 1 :=
    (iterClogBeta_le_iff_le_iterPow2 (by omega)).mpr
      (hn.trans (hcur.trans (iterPow2_mono (iterClogBeta t₁ n₁ - 1) hstep)))
  omega

private theorem mul_succ_le_pow {u : ℕ} (hu : 1 ≤ u) :
    u * (1 + u) ≤ 8 * 2 ^ (u - 1) := by
  induction u, hu using Nat.le_induction with
  | base => decide
  | succ j hj ih =>
    have hj_pow : j ≤ 2 ^ (j - 1) := by
      have := Nat.lt_two_pow_self (n := j - 1)
      omega
    have hmul : (j + 1) * (1 + (j + 1)) = j * (1 + j) + 2 * (j + 1) := by
      simp only [Nat.add_mul, Nat.mul_add]
      omega
    have hpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hj, Nat.pow_succ']
    rw [hmul, Nat.add_sub_cancel, hpow]
    omega

private theorem mul_add_add_le_pow (k u : ℕ) :
    u * (k + 1 + u) ≤ 4 * (k + 2) * max 1 (2 ^ (u - 1)) := by
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · simp
  · have hu_pow : u ≤ 2 ^ (u - 1) := by
      have := Nat.lt_two_pow_self (n := u - 1)
      omega
    have hsq : u * (1 + u) ≤ 8 * 2 ^ (u - 1) := mul_succ_le_pow hu
    have huk : u * k ≤ 4 * k * 2 ^ (u - 1) := by
      calc u * k ≤ 2 ^ (u - 1) * k := Nat.mul_le_mul_right k hu_pow
        _ = 1 * (k * 2 ^ (u - 1)) := by rw [Nat.one_mul, Nat.mul_comm]
        _ ≤ 4 * (k * 2 ^ (u - 1)) := Nat.mul_le_mul_right _ (by decide)
        _ = 4 * k * 2 ^ (u - 1) := (Nat.mul_assoc 4 k _).symm
    have hsum : u * (k + 1 + u) ≤ 4 * (k + 2) * 2 ^ (u - 1) := by
      calc u * (k + 1 + u) = u * k + u * (1 + u) := by
            rw [Nat.add_assoc, Nat.mul_add]
        _ ≤ 4 * k * 2 ^ (u - 1) + 8 * 2 ^ (u - 1) := Nat.add_le_add huk hsq
        _ = 4 * (k + 2) * 2 ^ (u - 1) := by
            rw [← Nat.add_mul, Nat.mul_add]
    exact hsum.trans (Nat.mul_le_mul_left (4 * (k + 2)) (le_max_right _ _))

private theorem iterClog_succ_mul_iterClogBeta_le (k t n : ℕ) :
    iterClog (k + 1) n * iterClogBeta t n ≤ 4 * (k + 2) * max 1 (iterClog k n) := by
  set u := iterClog (k + 1) n
  have hbeta : iterClogBeta t n ≤ k + 1 + u :=
    iterClogBeta_le_add_iterClog (Nat.le_add_left 1 k) t n
  rcases Nat.eq_zero_or_pos u with hu0 | hu_pos
  · rw [hu0, Nat.zero_mul]
    exact Nat.zero_le _
  · have hlt_pow : 2 ^ (u - 1) < iterClog k n :=
      (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mp
        (show u - 1 < Nat.clog 2 (iterClog k n) by change u - 1 < u; omega)
    have hpow_le : max 1 (2 ^ (u - 1)) ≤ max 1 (iterClog k n) := max_le_max_left 1 hlt_pow.le
    exact (Nat.mul_le_mul_left u hbeta).trans
      ((mul_add_add_le_pow k u).trans (Nat.mul_le_mul_left (4 * (k + 2)) hpow_le))

/-- For fixed `c`, `n ↦ iterClogBeta (c / n) n` is monotone. -/
theorem iterClogBeta_div_mono_right (c : ℕ) : Monotone (fun n => iterClogBeta (c / n) n) := by
  intro a b hab
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact (iterClogBeta_eq_one_iff.mpr (Nat.zero_le _)).trans_le (one_le_iterClogBeta _ _)
  · exact (iterClogBeta_mono_right (c / a) hab).trans
      (iterClogBeta_anti_left b (Nat.div_le_div_left hab ha))

/-- Two-parameter rank drop: if `1 ≤ n₂ ≤ n₁`, `2 ^ (c / n₁) < n₁`, and
`n₂ * (2 ^ (c / n₁) + 1) ≤ c`, then `iterClogBeta (c / n₂) n₂ < iterClogBeta (c / n₁) n₁`. -/
theorem iterClogBeta_div_lt_of_mul_le {c n₁ n₂ : ℕ} (hn₂ : 1 ≤ n₂) (hn : n₂ ≤ n₁)
    (hgt : 2 ^ (c / n₁) < n₁) (hmul : n₂ * (2 ^ (c / n₁) + 1) ≤ c) :
    iterClogBeta (c / n₂) n₂ < iterClogBeta (c / n₁) n₁ := by
  have hdiv : 2 ^ (c / n₁) + 1 ≤ c / n₂ :=
    (Nat.le_div_iff_mul_le hn₂).mpr (Nat.mul_comm n₂ _ ▸ hmul)
  rcases Nat.eq_zero_or_pos (c / n₁) with h0 | hpos
  · rw [h0, Nat.pow_zero] at hdiv hmul
    have hc_ge : 2 ≤ c := (Nat.le_mul_of_pos_left 2 hn₂).trans hmul
    have hc_lt : c < n₁ := (Nat.div_eq_zero_iff.mp h0).resolve_left (by omega)
    refine iterClogBeta_lt_of_two_pow_le hn ?_ ?_
    · rw [h0, Nat.max_eq_left (Nat.zero_le 1), Nat.pow_one]
      omega
    · rw [h0, Nat.max_eq_left (Nat.zero_le 1), Nat.pow_one]
      exact hdiv.trans (le_max_right 1 _)
  · refine iterClogBeta_lt_of_two_pow_le hn ?_ ?_
    · rwa [Nat.max_eq_right hpos]
    · rw [Nat.max_eq_right hpos]
      exact ((Nat.le_succ _).trans hdiv).trans (le_max_right 1 _)

/-- Multiplicative phase bound parameterized by `k : ℕ` whenever `2 * m / n ≤ max 1 t`:
`m * iterClogBeta t n ≤ (k + 1) * m + 2 * (k + 2) * n * max 1 (iterClog k n)`. -/
theorem mul_iterClogBeta_le_of_div_le (k m n t : ℕ) (ht : 2 * m / n ≤ max 1 t) :
    m * iterClogBeta t n ≤ (k + 1) * m + 2 * (k + 2) * n * max 1 (iterClog k n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : iterClogBeta t 0 = 1 := iterClogBeta_eq_one_iff.mpr (Nat.zero_le _)
    rw [h1, Nat.mul_one]
    exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_left m (Nat.succ_pos k))
  · by_cases hk : iterClog (k + 1) n ≤ max 1 t
    · have hb : iterClogBeta t n ≤ k + 1 := (iterClogBeta_le_iff (Nat.le_add_left 1 k)).mpr hk
      exact (Nat.mul_le_mul_left m hb).trans
        (by rw [Nat.mul_comm m (k + 1)]; exact Nat.le_add_right _ _)
    · have hlt : max 1 t < iterClog (k + 1) n := Nat.lt_of_not_ge hk
      have hd : 2 * m / n + 1 ≤ iterClog (k + 1) n := by omega
      have hdiv := Nat.lt_div_mul_add (a := 2 * m) hn
      have hmul := Nat.mul_le_mul_left n hd
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm n (2 * m / n)] at hmul
      have h2m_lt : 2 * m < n * iterClog (k + 1) n := by omega
      have h2m_beta :
          2 * (m * iterClogBeta t n) ≤ 2 * (2 * (k + 2) * n * max 1 (iterClog k n)) := by
        calc 2 * (m * iterClogBeta t n)
            = (2 * m) * iterClogBeta t n := by rw [Nat.mul_assoc]
          _ ≤ (n * iterClog (k + 1) n) * iterClogBeta t n :=
            Nat.mul_le_mul_right _ h2m_lt.le
          _ = n * (iterClog (k + 1) n * iterClogBeta t n) := Nat.mul_assoc _ _ _
          _ ≤ n * (4 * (k + 2) * max 1 (iterClog k n)) :=
            Nat.mul_le_mul_left n (iterClog_succ_mul_iterClogBeta_le k t n)
          _ = 2 * (2 * (k + 2) * n * max 1 (iterClog k n)) := by
            rw [← Nat.mul_assoc, Nat.mul_comm n (4 * (k + 2)),
              show 4 * (k + 2) * n = 2 * (2 * (k + 2) * n) by
                rw [show (4 : ℕ) = 2 * 2 by rfl]; simp only [Nat.mul_assoc]]
            simp only [Nat.mul_assoc]
      omega

/-- Multiplicative phase bound via `iterLog k n` for `1 ≤ k`:
`m * iterClogBeta (2 * m / n) n ≤ (k + 1) * m + 4 * (k + 2) * n * max 1 (iterLog k n)`. -/
theorem mul_iterClogBeta_div_le_iterLog {k : ℕ} (hk : 1 ≤ k) (m n : ℕ) :
    m * iterClogBeta (2 * m / n) n ≤ (k + 1) * m + 4 * (k + 2) * n * max 1 (iterLog k n) := by
  have h1 := mul_iterClogBeta_le_of_div_le k m n (2 * m / n) (le_max_right 1 (2 * m / n))
  have h2 := iterClog_le_iterLog_add_one hk n
  have h3 : max 1 (iterClog k n) ≤ 2 * max 1 (iterLog k n) := by
    have := le_max_left 1 (iterLog k n)
    have := le_max_right 1 (iterLog k n)
    omega
  have h4 : 2 * (k + 2) * n * max 1 (iterClog k n) ≤
      4 * (k + 2) * n * max 1 (iterLog k n) := by
    calc 2 * (k + 2) * n * max 1 (iterClog k n)
        ≤ 2 * (k + 2) * n * (2 * max 1 (iterLog k n)) := Nat.mul_le_mul_left _ h3
      _ = 2 * (2 * (k + 2) * n) * max 1 (iterLog k n) := by
        rw [Nat.mul_left_comm (2 * (k + 2) * n) 2 _, ← Nat.mul_assoc]
      _ = 4 * (k + 2) * n * max 1 (iterLog k n) := by
        rw [show (4 : ℕ) = 2 * 2 by rfl, Nat.mul_assoc 2 2 (k + 2),
          Nat.mul_assoc 2 (2 * (k + 2)) n]
  exact h1.trans (Nat.add_le_add_left h4 _)

end Nat
