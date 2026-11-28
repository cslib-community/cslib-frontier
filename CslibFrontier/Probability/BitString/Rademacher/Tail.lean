/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.BitString.Rademacher
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Tail bounds for Rademacher sums

The moment-generating-function estimate for weighted independent signs gives an upper tail
`exp (-t² / (2 V))` whenever the squared weights sum to at most the positive number `V`.
The two-sided bound is used for bilinear forms of random symmetric sign matrices.

## Main results

* `Cslib.BitString.dens_sum_mul_signVal_ge_le`: the one-sided sub-Gaussian bound.
* `Cslib.BitString.dens_abs_sum_mul_signVal_ge_le`: the two-sided bound.
-/

public section

open Finset Real
open scoped BigOperators

namespace Cslib.BitString

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A weighted sum of independent uniform signs has an exponentially small upper tail. -/
theorem dens_sum_mul_signVal_ge_le (a : ι → ℝ) {V t : ℝ}
    (hV : 0 < V) (ha : ∑ i, a i ^ 2 ≤ V) (ht : 0 ≤ t) :
    (dens ({x : ι → Bool | t ≤ ∑ i, a i * signVal (x i)} : Finset _) : ℝ) ≤
      exp (-(t ^ 2) / (2 * V)) := by
  classical
  let f : (ι → Bool) → ℝ := fun x => exp ((t / V) * ∑ i, a i * signVal (x i))
  have hsub : ({x : ι → Bool | t ≤ ∑ i, a i * signVal (x i)} : Finset _) ⊆
      ({x | exp ((t / V) * t) ≤ f x} : Finset _) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact exp_le_exp.2 (mul_le_mul_of_nonneg_left hx (div_nonneg ht hV.le))
  have hmarkov := Fintype.mul_dens_filter_le_expect
    (fun x => (exp_pos _).le : ∀ x, 0 ≤ f x) (exp ((t / V) * t))
  calc
    (dens ({x : ι → Bool | t ≤ ∑ i, a i * signVal (x i)} : Finset _) : ℝ)
        ≤ dens ({x | exp ((t / V) * t) ≤ f x} : Finset _) := by
          exact_mod_cast dens_le_dens hsub
    _ ≤ (𝔼 x, f x) / exp ((t / V) * t) := by
          rw [le_div_iff₀ (exp_pos _), mul_comm]
          exact hmarkov
    _ ≤ exp ((t / V) ^ 2 * (∑ i, a i ^ 2) / 2) / exp ((t / V) * t) :=
          div_le_div_of_nonneg_right (expect_exp_mul_sum_mul_signVal_le a _) (exp_pos _).le
    _ ≤ exp ((t / V) ^ 2 * V / 2) / exp ((t / V) * t) := by
          gcongr
    _ = exp (-(t ^ 2) / (2 * V)) := by
          rw [← exp_sub]
          congr 1
          field_simp
          ring

/-- A weighted sum of independent uniform signs has a two-sided sub-Gaussian tail. -/
theorem dens_abs_sum_mul_signVal_ge_le (a : ι → ℝ) {V t : ℝ}
    (hV : 0 < V) (ha : ∑ i, a i ^ 2 ≤ V) (ht : 0 ≤ t) :
    (dens ({x : ι → Bool | t ≤ |∑ i, a i * signVal (x i)|} : Finset _) : ℝ) ≤
      2 * exp (-(t ^ 2) / (2 * V)) := by
  classical
  have hsub : ({x : ι → Bool | t ≤ |∑ i, a i * signVal (x i)|} : Finset _) ⊆
      ({x : ι → Bool | t ≤ ∑ i, a i * signVal (x i)} : Finset _) ∪
        ({x : ι → Bool | t ≤ ∑ i, (-a i) * signVal (x i)} : Finset _) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and, mem_union, le_abs, neg_mul,
      sum_neg_distrib] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by linarith)
  have hneg : ∑ i, (-a i) ^ 2 ≤ V := by simpa only [neg_sq] using ha
  calc
    (dens ({x : ι → Bool | t ≤ |∑ i, a i * signVal (x i)|} : Finset _) : ℝ)
        ≤ dens ({x : ι → Bool | t ≤ ∑ i, a i * signVal (x i)} : Finset _) +
          dens ({x : ι → Bool | t ≤ ∑ i, (-a i) * signVal (x i)} : Finset _) := by
            exact_mod_cast (dens_le_dens hsub).trans (dens_union_le _ _)
    _ ≤ _ := by
          rw [two_mul]
          exact add_le_add (dens_sum_mul_signVal_ge_le a hV ha ht)
            (dens_sum_mul_signVal_ge_le (fun i => -a i) hV hneg ht)

end Cslib.BitString
