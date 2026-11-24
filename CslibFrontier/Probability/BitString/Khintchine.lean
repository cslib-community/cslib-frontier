/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import CslibFrontier.Probability.BitString.Rademacher
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Khintchine's `L¹` lower bound for Rademacher sums

For a Rademacher sum `Y = ∑ i, a i * signVal (x i)` over a uniformly random bit string
`x : ι → Bool`, `CslibFrontier.Probability.BitString.Rademacher` computes `𝔼 Y² = ∑ a²` and bounds
`𝔼 Y⁴ ≤ 3 (∑ a²)²`. Two applications of Cauchy–Schwarz interpolate the second moment between the
first and fourth moments, `(𝔼 Y²)³ ≤ (𝔼 |Y|)² · (𝔼 Y⁴)`, yielding the unconditional `L¹` lower
bound `√((∑ i, a i²) / 3) ≤ 𝔼 |Y|` (`sqrt_sum_sq_div_three_le_expect_abs_sum_mul_signVal`) and its
unweighted specialization `√(|ι| / 3) ≤ 𝔼 |∑ i, signVal (x i)|`
(`sqrt_card_div_three_le_expect_abs_sum_signVal`).

The sharp `L¹` Khintchine constant is `1 / √2` (Szarek, 1976); the elementary fourth-moment
constant `1 / √3` proved here suffices for the `Ω(√T)` and `Ω(√(T log N))` stochastic regret lower
bounds of [BlumMansour2007AGT, Theorem 4.8 and Exercise 4.5].

## Main results

* `Cslib.BitString.sum_sq_div_three_le_sq_expect_abs_sum_mul_signVal`:
  `(∑ i, a i ^ 2) / 3 ≤ (𝔼 x, |∑ i, a i * signVal (x i)|) ^ 2`.
* `Cslib.BitString.sqrt_sum_sq_div_three_le_expect_abs_sum_mul_signVal`:
  `√((∑ i, a i ^ 2) / 3) ≤ 𝔼 x, |∑ i, a i * signVal (x i)|`.
* `Cslib.BitString.sqrt_card_div_three_le_expect_abs_sum_signVal`:
  `√(|ι| / 3) ≤ 𝔼 x, |∑ i, signVal (x i)|`.

## References

* [A. Blum and Y. Mansour, *Learning, Regret Minimization, and Equilibria*][BlumMansour2007AGT],
  Theorem 4.8 and Exercise 4.5.
-/

public section

open Finset Real
open scoped BigOperators

namespace Cslib.BitString

private theorem expect_mul_sq_le {α : Type*} [Fintype α] [Nonempty α] (f g : α → ℝ) :
    (𝔼 x, f x * g x) ^ 2 ≤ (𝔼 x, f x ^ 2) * (𝔼 x, g x ^ 2) := by
  have hN : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  simp only [Fintype.expect_eq_sum_div_card]
  have hcs := sum_mul_sq_le_sq_mul_sq univ f g
  rw [div_pow, div_mul_div_comm, ← sq]
  exact div_le_div_of_nonneg_right hcs (by positivity)

private theorem cube_expect_sq_le {α : Type*} [Fintype α] [Nonempty α] (Y : α → ℝ) :
    (𝔼 x, Y x ^ 2) ^ 3 ≤ (𝔼 x, |Y x|) ^ 2 * (𝔼 x, Y x ^ 4) := by
  have h2_nn : 0 ≤ 𝔼 x, Y x ^ 2 := expect_nonneg fun x _ => sq_nonneg (Y x)
  rcases eq_or_lt_of_le h2_nn with h0 | hpos
  · rw [← h0, zero_pow (by decide)]
    exact mul_nonneg (sq_nonneg _) (expect_nonneg fun x _ => by positivity)
  · have h1 : (𝔼 x, Y x ^ 2) ^ 2 ≤ (𝔼 x, |Y x|) * (𝔼 x, |Y x| ^ 3) := by
      have hcs := expect_mul_sq_le (fun x => √|Y x|) (fun x => |Y x| * √|Y x|)
      have hlhs : (𝔼 x, √|Y x| * (|Y x| * √|Y x|)) = 𝔼 x, Y x ^ 2 := by
        refine expect_congr rfl fun x _ => ?_
        calc √|Y x| * (|Y x| * √|Y x|) = |Y x| * (√|Y x| * √|Y x|) := by ring
          _ = |Y x| * |Y x| := by rw [mul_self_sqrt (abs_nonneg _)]
          _ = Y x ^ 2 := by rw [← sq, sq_abs]
      have hr1 : (𝔼 x, (√|Y x|) ^ 2) = 𝔼 x, |Y x| :=
        expect_congr rfl fun x _ => sq_sqrt (abs_nonneg _)
      have hr2 : (𝔼 x, (|Y x| * √|Y x|) ^ 2) = 𝔼 x, |Y x| ^ 3 := by
        refine expect_congr rfl fun x _ => ?_
        rw [mul_pow, sq_sqrt (abs_nonneg _)]
        ring
      rwa [hlhs, hr1, hr2] at hcs
    have h2 : (𝔼 x, |Y x| ^ 3) ^ 2 ≤ (𝔼 x, Y x ^ 2) * (𝔼 x, Y x ^ 4) := by
      have hcs := expect_mul_sq_le (fun x => |Y x|) (fun x => Y x ^ 2)
      have hlhs : (𝔼 x, |Y x| * Y x ^ 2) = 𝔼 x, |Y x| ^ 3 := by
        refine expect_congr rfl fun x _ => ?_
        rw [← sq_abs]
        ring
      have hr1 : (𝔼 x, |Y x| ^ 2) = 𝔼 x, Y x ^ 2 :=
        expect_congr rfl fun x _ => sq_abs (Y x)
      have hr2 : (𝔼 x, (Y x ^ 2) ^ 2) = 𝔼 x, Y x ^ 4 :=
        expect_congr rfl fun x _ => by ring
      rwa [hlhs, hr1, hr2] at hcs
    have h1_sq : (𝔼 x, Y x ^ 2) ^ 4 ≤ (𝔼 x, |Y x|) ^ 2 * (𝔼 x, |Y x| ^ 3) ^ 2 := by
      have hnn : 0 ≤ (𝔼 x, |Y x|) * (𝔼 x, |Y x| ^ 3) :=
        mul_nonneg (expect_nonneg fun x _ => abs_nonneg _)
          (expect_nonneg fun x _ => by positivity)
      calc (𝔼 x, Y x ^ 2) ^ 4 = ((𝔼 x, Y x ^ 2) ^ 2) ^ 2 := by ring
        _ ≤ ((𝔼 x, |Y x|) * (𝔼 x, |Y x| ^ 3)) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        _ = (𝔼 x, |Y x|) ^ 2 * (𝔼 x, |Y x| ^ 3) ^ 2 := by ring
    have h4 : (𝔼 x, Y x ^ 2) * (𝔼 x, Y x ^ 2) ^ 3 ≤
        (𝔼 x, Y x ^ 2) * ((𝔼 x, |Y x|) ^ 2 * (𝔼 x, Y x ^ 4)) := by
      calc (𝔼 x, Y x ^ 2) * (𝔼 x, Y x ^ 2) ^ 3 = (𝔼 x, Y x ^ 2) ^ 4 := by ring
        _ ≤ (𝔼 x, |Y x|) ^ 2 * (𝔼 x, |Y x| ^ 3) ^ 2 := h1_sq
        _ ≤ (𝔼 x, |Y x|) ^ 2 * ((𝔼 x, Y x ^ 2) * (𝔼 x, Y x ^ 4)) :=
            mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
        _ = (𝔼 x, Y x ^ 2) * ((𝔼 x, |Y x|) ^ 2 * (𝔼 x, Y x ^ 4)) := by ring
    exact le_of_mul_le_mul_left h4 hpos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Khintchine's `L¹` lower bound (squared)**: for any real weights `a : ι → ℝ`,
`(∑ i, a i ^ 2) / 3 ≤ (𝔼 x, |∑ i, a i * signVal (x i)|) ^ 2`. -/
theorem sum_sq_div_three_le_sq_expect_abs_sum_mul_signVal (a : ι → ℝ) :
    (∑ i, a i ^ 2) / 3 ≤ (𝔼 x : ι → Bool, |∑ i, a i * signVal (x i)|) ^ 2 := by
  set S := ∑ i, a i ^ 2
  have hS : 0 ≤ S := sum_nonneg fun i _ => sq_nonneg (a i)
  rcases eq_or_lt_of_le hS with h0 | hpos
  · rw [← h0, zero_div]
    exact sq_nonneg _
  · have hcube := cube_expect_sq_le (fun x : ι → Bool => ∑ i, a i * signVal (x i))
    rw [expect_sq_sum_mul_signVal] at hcube
    have h4 := expect_sum_mul_signVal_pow_four_le a
    have hcomb : S ^ 2 * S ≤ S ^ 2 * (3 * (𝔼 x : ι → Bool, |∑ i, a i * signVal (x i)|) ^ 2) := by
      calc S ^ 2 * S = S ^ 3 := by ring
        _ ≤ (𝔼 x : ι → Bool, |∑ i, a i * signVal (x i)|) ^ 2 *
              (𝔼 x : ι → Bool, (∑ i, a i * signVal (x i)) ^ 4) := hcube
        _ ≤ (𝔼 x : ι → Bool, |∑ i, a i * signVal (x i)|) ^ 2 * (3 * S ^ 2) :=
            mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
        _ = S ^ 2 * (3 * (𝔼 x : ι → Bool, |∑ i, a i * signVal (x i)|) ^ 2) := by ring
    have hle := le_of_mul_le_mul_left hcomb (sq_pos_of_pos hpos)
    linarith

/-- **Khintchine's `L¹` lower bound**: for any real weights `a : ι → ℝ`,
`√((∑ i, a i ^ 2) / 3) ≤ 𝔼 x, |∑ i, a i * signVal (x i)|`. -/
theorem sqrt_sum_sq_div_three_le_expect_abs_sum_mul_signVal (a : ι → ℝ) :
    √((∑ i, a i ^ 2) / 3) ≤ 𝔼 x : ι → Bool, |∑ i, a i * signVal (x i)| := by
  have hnn : 0 ≤ 𝔼 x : ι → Bool, |∑ i, a i * signVal (x i)| :=
    expect_nonneg fun x _ => abs_nonneg _
  rw [← sqrt_sq hnn]
  exact sqrt_le_sqrt (sum_sq_div_three_le_sq_expect_abs_sum_mul_signVal a)

/-- Unweighted specialization of `sqrt_sum_sq_div_three_le_expect_abs_sum_mul_signVal`: the
expected absolute discrepancy of `|ι|` independent fair signs is at least `√(|ι| / 3)`. -/
theorem sqrt_card_div_three_le_expect_abs_sum_signVal :
    √((Fintype.card ι : ℝ) / 3) ≤ 𝔼 x : ι → Bool, |∑ i : ι, signVal (x i)| := by
  have h := sqrt_sum_sq_div_three_le_expect_abs_sum_mul_signVal (fun _ : ι => (1 : ℝ))
  simpa only [one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, one_mul] using h

end Cslib.BitString
