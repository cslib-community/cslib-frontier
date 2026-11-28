/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat

/-!
# Truncated second moments from Gaussian tails

A nonnegative integer quantity `Y` on a finite type whose upper tails are Gaussian,
`#{ω | j ≤ Y ω} ≤ M exp (-j² / c)` for every `j > R`, has truncated second moment
`∑ ω, Y ω ^ 2 [R < Y ω] ≤ M ((R + 1)² + c) exp (-(R + 1)² / c)`
(`sum_sq_ite_lt_le_of_tail`). This is the discrete counterpart of integrating the tail
`∫ 2 t exp (-t² / c) dt = c exp (-a² / c)`: the layer-cake identity
`y² [R < y] = (R + 1)² [R + 1 ≤ y] + ∑_{R + 1 < j ≤ y} (2 j - 1)` reduces the sum to the tails,
and `(2 j - 1) exp (-j² / c) ≤ c (exp (-(j - 1)² / c) - exp (-j² / c))` telescopes
(`sum_Ioc_two_mul_sub_one_mul_exp_le`).

## Main results

* `Cslib.sum_Ioc_two_mul_sub_one_mul_exp_le`: the discrete Gaussian tail sum.
* `Cslib.sum_sq_ite_lt_le_of_tail`: the truncated second moment from Gaussian tails.
-/

public section

namespace Cslib

open Finset Real

/-- **Discrete Gaussian tail sum.** For `c > 0`,
`∑_{a < j ≤ K} (2 j - 1) exp (-j² / c) ≤ c exp (-a² / c)`. -/
theorem sum_Ioc_two_mul_sub_one_mul_exp_le {c : ℝ} (hc : 0 < c) (a K : ℕ) :
    ∑ j ∈ Ioc a K, (2 * (j : ℝ) - 1) * exp (-((j : ℝ) ^ 2 / c)) ≤ c * exp (-((a : ℝ) ^ 2 / c)) := by
  -- Each term is at most the drop `c (exp (-(j - 1)² / c) - exp (-j² / c))`, which telescopes.
  have hstep (j : ℕ) (hj : 1 ≤ j) : (2 * (j : ℝ) - 1) * exp (-((j : ℝ) ^ 2 / c)) ≤
      c * (exp (-(((j - 1 : ℕ) : ℝ) ^ 2 / c)) - exp (-((j : ℝ) ^ 2 / c))) := by
    have hd : -(((j - 1 : ℕ) : ℝ) ^ 2 / c) = (2 * (j : ℝ) - 1) / c + -((j : ℝ) ^ 2 / c) := by
      rw [Nat.cast_sub hj, Nat.cast_one, ← neg_div, ← neg_div, ← add_div]
      congr 1; ring
    rw [hd, exp_add]
    calc (2 * (j : ℝ) - 1) * exp (-((j : ℝ) ^ 2 / c))
        = c * ((2 * (j : ℝ) - 1) / c) * exp (-((j : ℝ) ^ 2 / c)) := by
          rw [mul_div_cancel₀ _ hc.ne']
      _ ≤ c * (exp ((2 * (j : ℝ) - 1) / c) - 1) * exp (-((j : ℝ) ^ 2 / c)) := by
          gcongr; linarith [add_one_le_exp ((2 * (j : ℝ) - 1) / c)]
      _ = _ := by ring
  suffices h : ∀ K, a ≤ K → ∑ j ∈ Ioc a K, (2 * (j : ℝ) - 1) * exp (-((j : ℝ) ^ 2 / c)) ≤
      c * (exp (-((a : ℝ) ^ 2 / c)) - exp (-((K : ℝ) ^ 2 / c))) by
    rcases le_total a K with haK | hKa
    · exact (h K haK).trans (mul_le_mul_of_nonneg_left (sub_le_self _ (exp_pos _).le) hc.le)
    · rw [Ioc_eq_empty (by omega), sum_empty]
      positivity
  intro K haK
  induction K, haK using Nat.le_induction with
  | base => simp
  | succ K haK ih =>
    rw [sum_Ioc_succ_top (by omega)]
    have := hstep (K + 1) (by omega)
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at this ⊢
    linarith

/-- **Truncated second moment from Gaussian tails.** If `Y : Ω → ℕ` on a finite type satisfies
`#{ω | j ≤ Y ω} ≤ M exp (-j² / c)` for every `j > R`, then
`∑ ω, Y ω ^ 2 [R < Y ω] ≤ M ((R + 1)² + c) exp (-(R + 1)² / c)`. -/
theorem sum_sq_ite_lt_le_of_tail {Ω : Type*} [Fintype Ω] (Y : Ω → ℕ) (R : ℕ) {M c : ℝ}
    (hc : 0 < c)
    (htail : ∀ j : ℕ, R < j → (#{ω | j ≤ Y ω} : ℝ) ≤ M * exp (-((j : ℝ) ^ 2 / c))) :
    ∑ ω, (if R < Y ω then (Y ω : ℝ) ^ 2 else 0) ≤
      M * (((R : ℝ) + 1) ^ 2 + c) * exp (-(((R : ℝ) + 1) ^ 2 / c)) := by
  classical
  have hM : 0 ≤ M := by
    have h := (Nat.cast_nonneg _).trans (htail (R + 1) (by omega))
    exact nonneg_of_mul_nonneg_left h (exp_pos _)
  set K := univ.sup Y
  -- The layer-cake identity for a single value `y ≤ K`.
  have hodd (y : ℕ) (hy : R + 1 ≤ y) :
      ∑ j ∈ Ioc (R + 1) y, (2 * (j : ℝ) - 1) = (y : ℝ) ^ 2 - ((R : ℝ) + 1) ^ 2 := by
    induction y, hy using Nat.le_induction with
    | base => simp
    | succ y hy ih =>
      rw [sum_Ioc_succ_top (by omega), ih]
      push_cast
      ring
  have hlayer (ω : Ω) : (if R < Y ω then (Y ω : ℝ) ^ 2 else 0) =
      ((R : ℝ) + 1) ^ 2 * (if R + 1 ≤ Y ω then 1 else 0) +
        ∑ j ∈ Ioc (R + 1) K, (2 * (j : ℝ) - 1) * (if j ≤ Y ω then 1 else 0) := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [← sum_filter, show (Ioc (R + 1) K).filter (· ≤ Y ω) = Ioc (R + 1) (Y ω) by
      ext j
      simp only [mem_filter, mem_Ioc]
      have : Y ω ≤ K := le_sup (mem_univ ω)
      omega]
    by_cases hR : R < Y ω
    · rw [hodd _ (by omega)]
      simp only [hR, show R + 1 ≤ Y ω by omega, ite_true]
      ring
    · simp only [hR, show ¬R + 1 ≤ Y ω by omega, ite_false]
      rw [Ioc_eq_empty (by omega), sum_empty]
      ring
  simp_rw [hlayer]
  rw [sum_add_distrib, ← mul_sum, sum_comm]
  simp only [← mul_sum, sum_boole]
  have hfirst := htail (R + 1) (by omega)
  have hrest : ∑ j ∈ Ioc (R + 1) K, (2 * (j : ℝ) - 1) * (#{ω | j ≤ Y ω} : ℝ) ≤
      M * (c * exp (-(((R + 1 : ℕ) : ℝ) ^ 2 / c))) := by
    refine (sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
      (htail j (by have := mem_Ioc.mp hj; omega))
      (by have : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by have := mem_Ioc.mp hj; omega)
          linarith)).trans ?_
    calc ∑ j ∈ Ioc (R + 1) K, (2 * (j : ℝ) - 1) * (M * exp (-((j : ℝ) ^ 2 / c)))
        = M * ∑ j ∈ Ioc (R + 1) K, (2 * (j : ℝ) - 1) * exp (-((j : ℝ) ^ 2 / c)) := by
          rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Ioc_two_mul_sub_one_mul_exp_le hc _ _) hM
  push_cast at hfirst hrest ⊢
  calc ((R : ℝ) + 1) ^ 2 * (#{ω | R + 1 ≤ Y ω} : ℝ) +
        ∑ j ∈ Ioc (R + 1) K, (2 * (j : ℝ) - 1) * (#{ω | j ≤ Y ω} : ℝ)
      ≤ ((R : ℝ) + 1) ^ 2 * (M * exp (-(((R : ℝ) + 1) ^ 2 / c))) +
          M * (c * exp (-(((R : ℝ) + 1) ^ 2 / c))) :=
        add_le_add (mul_le_mul_of_nonneg_left hfirst (by positivity)) hrest
    _ = M * (((R : ℝ) + 1) ^ 2 + c) * exp (-(((R : ℝ) + 1) ^ 2 / c)) := by ring

end Cslib
