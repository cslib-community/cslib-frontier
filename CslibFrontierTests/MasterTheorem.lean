/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.Nat.MasterTheoremAsymptotics
import CslibFrontier.Algorithms.Lean.Query.Arith.Karatsuba.Cost
import Cslib.Algorithms.Lean.MergeSort.MergeSort

/-!
# Tests for the master theorem

Each case of the master theorem applied to a concrete recurrence: cslib's merge-sort comparison
count (case 2), Karatsuba's multiplication count (case 1 with `d = 0`), a Strassen-shaped
recurrence (case 1, `Θ(n ^ log₂ 7)`), a binary-search recurrence (case 2 with `d = 0`), a base-`3`
recurrence (case 3), and a non-polynomial regularity recurrence
`T(n) = 2 T(⌈n/2⌉) + n² (⌊log₂ n⌋ + 1)`. Non-vacuity counterexamples verify that the hypotheses
cannot be dropped.
-/

namespace CslibFrontierTests.MasterTheorem

open Nat

/-! ### Merge sort: case 2 -/

theorem mergeSort_recurrence : DivideConquerRecurrence
    Cslib.Algorithms.Lean.TimeM.timeMergeSortRec 2 2 1 0 0 fun n => 1 * n ^ 1 where
  base_le n hn := by
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;>
      simp [Cslib.Algorithms.Lean.TimeM.timeMergeSortRec]
  le_base n h1 hn := by
    obtain rfl : n = 1 := (by omega)
    simp [Cslib.Algorithms.Lean.TimeM.timeMergeSortRec]
  step n hn := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    refine ⟨fun i => if i = 0 then (k + 2) / 2 else (k + 2 - 1) / 2 + 1, fun i _ => ?_, ?_⟩
    · dsimp only
      split_ifs <;> omega
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      dsimp only
      simp only [↓reduceIte, Nat.one_ne_zero, pow_one, one_mul]
      rw [Cslib.Algorithms.Lean.TimeM.timeMergeSortRec]

theorem mergeSort_bound : DivideConquerBound Cslib.Algorithms.Lean.TimeM.timeMergeSortRec
    2 2 1 0 fun n => 1 * n ^ 1 :=
  mergeSort_recurrence.toBound

/-- Merge sort makes at most `2 n ⌈log₂ n⌉` comparisons. cslib's `timeMergeSortRec_le` has the
sharper `n ⌈log₂ n⌉`; the generic theorem loses the factor `b` from `b ^ ⌈log_b n⌉ ≤ b n`. -/
example (n : ℕ) (hn : n ≠ 0) :
    Cslib.Algorithms.Lean.TimeM.timeMergeSortRec n ≤ 2 * n * clog 2 n := by
  have := mergeSort_bound.le_mul_pow_mul_clog (by norm_num) (by norm_num) le_rfl (by norm_num) hn
  simp only [pow_one, one_mul, zero_add] at this
  linarith

example : (fun n => (Cslib.Algorithms.Lean.TimeM.timeMergeSortRec n : ℝ)) =O[Filter.atTop]
    fun n => (n : ℝ) ^ 1 * Real.log n :=
  mergeSort_bound.isBigO_pow_mul_log (by norm_num) le_rfl (by norm_num)

example : (fun n => (Cslib.Algorithms.Lean.TimeM.timeMergeSortRec n : ℝ)) =Θ[Filter.atTop]
    fun n => (n : ℝ) ^ 1 * Real.log n :=
  mergeSort_recurrence.isTheta_pow_mul_log (by norm_num) le_rfl (by norm_num) le_rfl

/-! ### Karatsuba: case 1 with `d = 0` -/

/-- The multiplication count `M(n) = M(⌊n/2⌋) + 2 M(⌈n/2⌉)` of Karatsuba's algorithm satisfies an
exact divide-and-conquer recurrence with `a = 3`, `b = 2` and `f = 0`. -/
theorem mulCount_recurrence : DivideConquerRecurrence Cslib.Query.Karatsuba.mulCount
    3 2 1 1 1 fun n => 0 * n ^ 0 where
  base_le n hn := by
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
    · simp only [Cslib.Query.Karatsuba.mulCount_zero, Nat.zero_le]
    · simp only [Cslib.Query.Karatsuba.mulCount_one, le_refl]
  le_base n h1 hn := by
    obtain rfl : n = 1 := (by omega)
    simp only [Cslib.Query.Karatsuba.mulCount_one, le_refl]
  step n hn := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    refine ⟨fun i => if i = 0 then (k + 2) / 2 else k + 2 - (k + 2) / 2, fun i _ => ?_, ?_⟩
    · dsimp only
      split_ifs <;> omega
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add]
      dsimp only
      simp only [↓reduceIte, Nat.one_ne_zero, Nat.reduceEqDiff, zero_mul, add_zero]
      rw [Cslib.Query.Karatsuba.mulCount]
      ring

theorem mulCount_bound : DivideConquerBound Cslib.Query.Karatsuba.mulCount 3 2 1 1
    fun n => 0 * n ^ 0 :=
  mulCount_recurrence.toBound

/-- The generic theorem recovers `Karatsuba.mulCount_le_pow_clog`. -/
example (n : ℕ) : Cslib.Query.Karatsuba.mulCount n ≤ 3 ^ clog 2 n := by
  have := mulCount_bound.sub_mul_le_pow_clog (by norm_num) (by norm_num) le_rfl n
  norm_num at this
  omega

example : (fun n => (Cslib.Query.Karatsuba.mulCount n : ℝ)) =O[Filter.atTop]
    fun n => (n : ℝ) ^ Real.logb 2 3 := by
  simpa using mulCount_bound.isBigO_rpow (by norm_num) le_rfl (by norm_num)

example : (fun n => (Cslib.Query.Karatsuba.mulCount n : ℝ)) =Θ[Filter.atTop]
    fun n => (n : ℝ) ^ Real.logb 2 3 :=
  mulCount_recurrence.isTheta_rpow (by norm_num) le_rfl (by norm_num) (Or.inl ⟨le_rfl, by norm_num⟩)

/-! ### A Strassen-shaped recurrence: case 1 -/

/-- `T(n) = 7 T(⌈n/2⌉) + n²`, `T(0) = 0`, `T(1) = 1`. -/
def strassenT : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 7 * strassenT ((n + 3) / 2) + (n + 2) ^ 2
termination_by n => n
decreasing_by omega

example : strassenT 4 = 93 := by simp [strassenT]

theorem strassenT_recurrence : DivideConquerRecurrence strassenT 7 2 1 1 1 fun n => 1 * n ^ 2 :=
  DivideConquerRecurrence.of_ceil (by norm_num)
    (fun n hn => by rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp [strassenT])
    (fun n h1 hn => by obtain rfl : n = 1 := (by omega); simp [strassenT])
    (fun n hn => by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      simp [strassenT])

theorem strassenT_bound : DivideConquerBound strassenT 7 2 1 1 fun n => 1 * n ^ 2 :=
  strassenT_recurrence.toBound

/-- `3 T(n) ≤ 7 · 7 ^ ⌈log₂ n⌉`. -/
example (n : ℕ) : 3 * strassenT n ≤ 7 * 7 ^ clog 2 n := by
  have := strassenT_bound.sub_mul_le_pow_clog (by norm_num) (by norm_num) le_rfl n
  norm_num at this
  omega

/-- `T(n) ≤ (7/3) · 7 · n ^ log₂ 7` for `n ≠ 0`. -/
example (n : ℕ) (hn : n ≠ 0) :
    (strassenT n : ℝ) ≤ (1 + 4 / 3) * 7 * (n : ℝ) ^ Real.logb 2 7 := by
  have := strassenT_bound.le_mul_rpow (by norm_num) le_rfl (by norm_num) hn
  norm_num at this ⊢
  linarith

example : (fun n => (strassenT n : ℝ)) =O[Filter.atTop] fun n => (n : ℝ) ^ Real.logb 2 7 := by
  simpa using strassenT_bound.isBigO_rpow (by norm_num) le_rfl (by norm_num)

example : (fun n => (strassenT n : ℝ)) =Θ[Filter.atTop] fun n => (n : ℝ) ^ Real.logb 2 7 :=
  strassenT_recurrence.isTheta_rpow (by norm_num) le_rfl (by norm_num) (Or.inr le_rfl)

/-! ### Binary search: case 2 with `d = 0` -/

/-- `T(n) = T(⌈n/2⌉) + 1`, `T(0) = T(1) = 0`. -/
def bsT : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => bsT ((n + 3) / 2) + 1
termination_by n => n
decreasing_by omega

theorem bsT_recurrence : DivideConquerRecurrence bsT 1 2 1 0 0 fun n => 1 * n ^ 0 :=
  DivideConquerRecurrence.of_ceil (by norm_num)
    (fun n hn => by rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp [bsT])
    (fun n h1 hn => by obtain rfl : n = 1 := (by omega); simp [bsT])
    (fun n hn => by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      simp [bsT])

theorem bsT_bound : DivideConquerBound bsT 1 2 1 0 fun n => 1 * n ^ 0 :=
  bsT_recurrence.toBound

example (n : ℕ) (hn : n ≠ 0) : bsT n ≤ clog 2 n := by
  simpa using bsT_bound.le_mul_pow_mul_clog le_rfl (by norm_num) le_rfl (by norm_num) hn

example : (fun n => (bsT n : ℝ)) =Θ[Filter.atTop] fun n => (n : ℝ) ^ 0 * Real.log n :=
  bsT_recurrence.isTheta_pow_mul_log (by norm_num) le_rfl (by norm_num) le_rfl

/-! ### Base `3`: case 3 -/

/-- `T(n) = 2 T(⌈n/3⌉) + n`, `T(0) = 0`, `T(1) = 1`. -/
def t3 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * t3 ((n + 4) / 3) + (n + 2)
termination_by n => n
decreasing_by omega

theorem t3_recurrence : DivideConquerRecurrence t3 2 3 1 1 1 fun n => 1 * n ^ 1 :=
  DivideConquerRecurrence.of_ceil (by norm_num)
    (fun n hn => by rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp [t3])
    (fun n h1 hn => by obtain rfl : n = 1 := (by omega); simp [t3])
    (fun n hn => by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      simp [t3])

theorem t3_bound : DivideConquerBound t3 2 3 1 1 fun n => 1 * n ^ 1 :=
  t3_recurrence.toBound

/-- `T(n) ≤ 12 n` for `n ≠ 0`. -/
example (n : ℕ) (hn : n ≠ 0) : t3 n ≤ 12 * n := by
  have := t3_bound.pow_sub_mul_le_mul_pow (by norm_num) (by norm_num) le_rfl hn
  norm_num at this
  omega

example : (fun n => (t3 n : ℝ)) =O[Filter.atTop] fun n => (n : ℝ) ^ 1 :=
  t3_bound.isBigO_pow (by norm_num) (by norm_num) le_rfl (by norm_num)

example : (fun n => (t3 n : ℝ)) =Θ[Filter.atTop] fun n => (n : ℝ) ^ 1 :=
  t3_recurrence.isTheta_pow (by norm_num) (by norm_num) le_rfl (by norm_num) le_rfl

/-! ### Case 3 under general regularity (non-polynomial driving term) -/

/-- Non-polynomial driving term `f(n) = n² (⌊log₂ n⌋ + 1)`. -/
def regF (n : ℕ) : ℕ := n ^ 2 * (Nat.log 2 n + 1)

theorem regF_mono : Monotone regF := fun _ _ hxy =>
  Nat.mul_le_mul (Nat.pow_le_pow_left hxy 2) (Nat.succ_le_succ (Nat.log_mono_right hxy))

/-- `T(n) = 2 T(⌈n/2⌉) + n² (⌊log₂ n⌋ + 1)`, `T(0) = 0`, `T(1) = 1`, `T(2) = 10`. -/
def regT : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * regT ((n + 3) / 2) + regF (n + 2)
termination_by n => n
decreasing_by omega

theorem regT_recurrence : DivideConquerRecurrence regT 2 2 2 1 10 regF :=
  DivideConquerRecurrence.of_ceil (by norm_num)
    (fun n hn => by
      have hlog2 : Nat.log 2 2 = 1 := by rw [Nat.log_eq_iff (Or.inr (by norm_num))]; norm_num
      rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl
      · simp [regT]
      · simp [regT]
      · simp [regT, regF, hlog2])
    (fun n h1 hn => by
      have hlog2 : Nat.log 2 2 = 1 := by rw [Nat.log_eq_iff (Or.inr (by norm_num))]; norm_num
      rcases (by omega : n = 1 ∨ n = 2) with rfl | rfl
      · simp [regT]
      · simp [regT, regF, hlog2])
    (fun n hn => by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      simp [regT])

private theorem regF_step {m : ℕ} (hm : 2 < m) :
    9 * (2 * regF ((m + 2 - 1) / 2)) ≤ 8 * regF m := by
  have hdiv : 3 * ((m + 1) / 2) ≤ 2 * m := by omega
  have hsq : 9 * (2 * ((m + 1) / 2) ^ 2) ≤ 8 * m ^ 2 := by
    calc 9 * (2 * ((m + 1) / 2) ^ 2) = 2 * (3 * ((m + 1) / 2)) ^ 2 := by ring
      _ ≤ 2 * (2 * m) ^ 2 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hdiv 2)
      _ = 8 * m ^ 2 := by ring
  have hlog : Nat.log 2 ((m + 1) / 2) + 1 ≤ Nat.log 2 m + 1 :=
    Nat.succ_le_succ (Nat.log_mono_right (by omega))
  have heq : (m + 2 - 1) / 2 = (m + 1) / 2 := by omega
  rw [heq, regF, regF]
  calc 9 * (2 * (((m + 1) / 2) ^ 2 * (Nat.log 2 ((m + 1) / 2) + 1)))
      = (9 * (2 * ((m + 1) / 2) ^ 2)) * (Nat.log 2 ((m + 1) / 2) + 1) := by ring
    _ ≤ (8 * m ^ 2) * (Nat.log 2 m + 1) := Nat.mul_le_mul hsq hlog
    _ = 8 * (m ^ 2 * (Nat.log 2 m + 1)) := by ring

/-- Explicit `ℕ` regularity bound: `regT n ≤ 189 * regF n` for `n > 2`. -/
example {n : ℕ} (hn : 2 < n) : regT n ≤ 189 * regF n := by
  simpa using regT_recurrence.toBound.le_mul_of_regular (by norm_num) (by norm_num)
    regF_mono (by norm_num : 8 < 9) (fun _ => regF_step) (by simp [regF]) n hn

example : (fun n => (regT n : ℝ)) =Θ[Filter.atTop] fun n => (regF n : ℝ) := by
  refine regT_recurrence.isTheta_of_regular (by norm_num) (by norm_num) regF_mono
    (ρ := 8 / 9) (by norm_num) ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop 2] with m hm
    have hreal : (9 : ℝ) * ((2 : ℝ) * regF ((m + 2 - 1) / 2)) ≤ 8 * regF m := by
      exact_mod_cast regF_step hm
    linarith
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    simp only [regF]
    exact Nat.mul_pos (Nat.pow_pos hm) (Nat.succ_pos _)

/-! ### The hypotheses are not vacuous -/

/-- `n²` does not satisfy `T n ≤ T(⌈n/2⌉)`: at `n = 2` it would give `4 ≤ 1`. -/
example : ¬ DivideConquerBound (fun n => n ^ 2) 1 2 1 1 fun n => 0 * n ^ 0 := by
  intro h
  have := h.step 2 (by norm_num) 1 fun m hm =>
    (Nat.pow_le_pow_left (by omega : m ≤ 1) 2).trans (by norm_num)
  norm_num at this

/-- `n` does not satisfy the lower bound `3 T(⌊n/2⌋) ≤ T n`: at `n = 2` it gives `3 ≤ 2`. -/
example : ¬ DivideConquerLowerBound (fun n => n) 3 2 1 1 fun _ => 0 := by
  intro h
  have := h.step 2 (by norm_num) 1 fun m hlo hhi => by omega
  omega

/-- Constant `0` fails the positive base lower bound `T₀ = 1` at `n = 1`. -/
example : ¬ DivideConquerLowerBound (fun _ => 0) 2 2 1 1 fun _ => 0 := by
  intro h
  have := h.base 1 le_rfl le_rfl
  omega

/-- Regularity with `a = 2, b = 2` fails for linear `f(n) = n`: at `m = 2`, `2 * ⌈2/2⌉ = 2` is not
strictly bounded by `(p / q) * 2` when `p < q`. -/
example {p q : ℕ} (hpq : p < q) : ¬ (∀ m, 1 < m → q * (2 * ((m + 2 - 1) / 2)) ≤ p * m) := by
  intro h
  have := h 2 (by norm_num)
  simp only [show (2 + 2 - 1) / 2 = 1 by decide, mul_one] at this
  nlinarith

/-! ### Supporting lemmas -/

example : (clog 3 9 : ℝ) ≤ 2 * Real.logb 3 9 := clog_le_two_mul_logb (by norm_num) (by norm_num)

end CslibFrontierTests.MasterTheorem
