/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Foundations.Data.Finset.Markov
import CslibFrontier.Tactic.LinarithCast
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Random subsets meet a fixed set in about its expected size

For a set `U` of `u` elements of an `n`-element set `s` and a uniformly random `ℓ`-subset `J` of
`s`, the size `X = #(U ∩ J)` has a hypergeometric distribution. Double counting gives its factorial
moments: `n 𝔼[X] = u ℓ` (`card_mul_sum_card_inter_powersetCard`) and
`n (n - 1) 𝔼[X (X - 1)] = u (u - 1) ℓ (ℓ - 1)` (`card_mul_sum_card_inter_mul_sub_one_powersetCard`),
so the variance of `X` is at most its mean `μ = u ℓ / n` (`sum_card_inter_sub_sq_le`). By
Chebyshev's inequality `X < m ≤ μ` with probability at most `μ / (μ - m)²`
(`card_filter_card_inter_lt_mul_sq_le`), so at most half of the `ℓ`-subsets meet `U` in fewer than
`μ / 2` elements once `μ ≥ 8` (`two_mul_card_filter_card_inter_lt_le`).

## Main results

* `Cslib.sum_card_inter_powersetCard`, `Cslib.sum_card_inter_mul_sub_one_powersetCard`: the
  first two factorial moments of `#(U ∩ J)` over the `ℓ`-subsets `J`.
* `Cslib.sum_card_inter_sub_sq_le`: the variance is at most the mean.
* `Cslib.card_filter_card_inter_lt_mul_sq_le`: Chebyshev's inequality.
* `Cslib.two_mul_card_filter_card_inter_lt_le`: most `ℓ`-subsets meet `U` in at least half the
  expected number of elements.
-/

public section

namespace Cslib

open Finset

variable {α : Type*} [DecidableEq α] {s U : Finset α} {ℓ : ℕ}

/-- Double counting: summed over the `t ∈ P`, `#(A ∩ f t)` counts every `a ∈ A` once for each `t`
with `a ∈ f t`. -/
private theorem sum_card_inter_eq_sum_card_filter {ι β : Type*} [DecidableEq β] (P : Finset ι)
    (A : Finset β) (f : ι → Finset β) :
    ∑ t ∈ P, #(A ∩ f t) = ∑ a ∈ A, #{t ∈ P | a ∈ f t} := by
  simp only [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm

/-- The `ℓ`-subsets of `s` containing `i ∈ s`. -/
private theorem card_filter_mem_powersetCard {i : α} (hi : i ∈ s) (hℓ : 1 ≤ ℓ) :
    #{J ∈ s.powersetCard ℓ | i ∈ J} = (#s - 1).choose (ℓ - 1) := by
  simpa using card_filter_powersetCard_subset {i} s ℓ (singleton_subset_iff.2 hi)
    (by simpa using hℓ)

/-- The `ℓ`-subsets of `s` containing distinct `i, j ∈ s`. -/
private theorem card_filter_mem_mem_powersetCard {i j : α} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hℓ : 2 ≤ ℓ) : #{J ∈ s.powersetCard ℓ | i ∈ J ∧ j ∈ J} = (#s - 2).choose (ℓ - 2) := by
  simpa [insert_subset_iff, card_pair hij] using card_filter_powersetCard_subset {i, j} s ℓ
    (insert_subset hi (singleton_subset_iff.2 hj)) (by rw [card_pair hij]; exact hℓ)

/-- **The first moment**: summed over the `ℓ`-subsets `J`, `#(U ∩ J)` counts every element of `U`
once for each `ℓ`-subset containing it. -/
theorem sum_card_inter_powersetCard (hU : U ⊆ s) (hℓ : 1 ≤ ℓ) :
    ∑ J ∈ s.powersetCard ℓ, #(U ∩ J) = #U * (#s - 1).choose (ℓ - 1) :=
  sum_card_inter fun _ hi => card_filter_mem_powersetCard (hU hi) hℓ

/-- **The second factorial moment**: summed over the `ℓ`-subsets `J`, `#(U ∩ J) (#(U ∩ J) - 1)`
counts every ordered pair of distinct elements of `U` once for each `ℓ`-subset containing both. -/
theorem sum_card_inter_mul_sub_one_powersetCard (hU : U ⊆ s) (hℓ : 2 ≤ ℓ) :
    ∑ J ∈ s.powersetCard ℓ, #(U ∩ J) * (#(U ∩ J) - 1) =
      #U * (#U - 1) * (#s - 2).choose (ℓ - 2) := by
  have hoff (A : Finset α) : #A * (#A - 1) = #A.offDiag := by rw [offDiag_card, Nat.mul_sub_one]
  have hpair : ∀ p ∈ U.offDiag,
      #{J ∈ s.powersetCard ℓ | p ∈ J.offDiag} = (#s - 2).choose (ℓ - 2) := fun p hp => by
    obtain ⟨hp₁, hp₂, hne⟩ := mem_offDiag.1 hp
    simpa [mem_offDiag, hne] using card_filter_mem_mem_powersetCard (hU hp₁) (hU hp₂) hne hℓ
  simp only [hoff, offDiag_inter]
  rw [sum_card_inter_eq_sum_card_filter, sum_congr rfl hpair, sum_const, smul_eq_mul]

/-- The first moment, multiplied out: `n ∑_J #(U ∩ J) = #U ℓ C(n, ℓ)` with `n = #s`. -/
theorem card_mul_sum_card_inter_powersetCard (hU : U ⊆ s) :
    #s * ∑ J ∈ s.powersetCard ℓ, #(U ∩ J) = #U * ℓ * (#s).choose ℓ := by
  rcases ℓ with _ | ℓ
  · simp
  rw [sum_card_inter_powersetCard hU (by omega), Nat.add_sub_cancel]
  rcases hs : #s with _ | n
  · simp
  calc (n + 1) * (#U * n.choose ℓ) = #U * ((n + 1) * n.choose ℓ) := by ring
    _ = #U * (ℓ + 1) * (n + 1).choose (ℓ + 1) := by rw [Nat.add_one_mul_choose_eq]; ring

/-- The second factorial moment, multiplied out:
`n (n - 1) ∑_J #(U ∩ J) (#(U ∩ J) - 1) = #U (#U - 1) ℓ (ℓ - 1) C(n, ℓ)` with `n = #s`. -/
theorem card_mul_sum_card_inter_mul_sub_one_powersetCard (hU : U ⊆ s) :
    #s * (#s - 1) * ∑ J ∈ s.powersetCard ℓ, #(U ∩ J) * (#(U ∩ J) - 1) =
      #U * (#U - 1) * (ℓ * (ℓ - 1)) * (#s).choose ℓ := by
  rcases ℓ with _ | _ | ℓ
  · simp
  · rw [sum_eq_zero fun J hJ => mul_eq_zero_of_right _ (Nat.sub_eq_zero_of_le
      ((card_le_card inter_subset_right).trans (mem_powersetCard.1 hJ).2.le))]
    simp
  rw [sum_card_inter_mul_sub_one_powersetCard hU (by omega)]
  rcases hs : #s with _ | _ | n
  · simp
  · simp [Nat.choose_eq_zero_of_lt (by omega : 1 < ℓ + 2)]
  simp only [show ∀ k, k + 2 - 1 = k + 1 from fun _ => rfl]
  calc (n + 2) * (n + 1) * (#U * (#U - 1) * n.choose ℓ)
      = #U * (#U - 1) * ((n + 2) * ((n + 1) * n.choose ℓ)) := by ring
    _ = #U * (#U - 1) * ((ℓ + 1) * ((n + 2) * (n + 1).choose (ℓ + 1))) := by
        rw [Nat.add_one_mul_choose_eq]; ring
    _ = _ := by rw [Nat.add_one_mul_choose_eq]; ring

/-- `x (x - 1)` in `ℕ` casts to `x (x - 1)` in `ℝ`, since both vanish at `x = 0`. -/
private theorem natCast_mul_natCast_sub_one (x : ℕ) :
    (x : ℝ) * ((x - 1 : ℕ) : ℝ) = x * ((x : ℝ) - 1) := by
  rcases x with _ | x
  · simp
  · push_cast [Nat.add_sub_cancel]; ring

/-- The second factorial moment of `#(U ∩ J)` is at most the square of the first moment:
`(#s)² ∑_J #(U ∩ J) (#(U ∩ J) - 1) ≤ (#U)² ℓ² C(#s, ℓ)`. -/
private theorem sq_card_mul_sum_card_inter_mul_sub_one_powersetCard_le (hU : U ⊆ s) :
    (#s : ℝ) ^ 2 * ∑ J ∈ s.powersetCard ℓ, (#(U ∩ J) : ℝ) * ((#(U ∩ J) : ℝ) - 1) ≤
      (#U : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 * (#s).choose ℓ := by
  set P := s.powersetCard ℓ
  set c : ℝ := (#s : ℝ); set a : ℝ := (#U : ℝ); set b : ℝ := (ℓ : ℝ)
  set M : ℝ := ((#s).choose ℓ : ℝ)
  have hS₂ : c * (c - 1) * ∑ J ∈ P, (#(U ∩ J) : ℝ) * (#(U ∩ J) - 1) =
      a * (a - 1) * (b * (b - 1)) * M := by
    simpa only [Nat.cast_mul, Nat.cast_sum, natCast_mul_natCast_sub_one] using
      congrArg (Nat.cast (R := ℝ)) (card_mul_sum_card_inter_mul_sub_one_powersetCard (ℓ := ℓ) hU)
  rcases Nat.lt_or_ge #s 2 with hs | hs
  · rw [sum_eq_zero fun J _ => ?_]
    · simp only [mul_zero]; positivity
    have : #(U ∩ J) ≤ 1 :=
      (card_le_card inter_subset_left).trans ((card_le_card hU).trans (by omega))
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h <;> simp [h]
  have hc : 2 ≤ c := by simp only [c]; exact_mod_cast hs
  have hac : a ≤ c := by simp only [a, c]; exact_mod_cast card_le_card hU
  have hfac : 0 ≤ M * (a * b * ((c - a) * (b - 1) + a * (c - 1))) := by
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
    · simp [b]
    have hb1 : 1 ≤ b := by simp only [b]; exact_mod_cast hℓ
    exact mul_nonneg (by positivity) <| mul_nonneg (by positivity) <|
      add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by positivity) (by linarith))
  refine le_of_mul_le_mul_left (a := c - 1) ?_ (by linarith)
  have hEq : (c - 1) * (c ^ 2 * ∑ J ∈ P, (#(U ∩ J) : ℝ) * (#(U ∩ J) - 1)) =
      c * (a * (a - 1) * (b * (b - 1)) * M) := by rw [← hS₂]; ring
  nlinarith [hEq]

/-- **The variance of `#(U ∩ J)` is at most its mean**: over the `ℓ`-subsets `J` of `s`, with
`n = #s`, `∑_J (n #(U ∩ J) - #U ℓ)² ≤ n #U ℓ C(n, ℓ)`. -/
theorem sum_card_inter_sub_sq_le (hU : U ⊆ s) :
    ∑ J ∈ s.powersetCard ℓ, ((#s : ℝ) * #(U ∩ J) - #U * ℓ) ^ 2 ≤
      #s * #U * ℓ * (#s).choose ℓ := by
  set P := s.powersetCard ℓ
  set c : ℝ := (#s : ℝ); set a : ℝ := (#U : ℝ); set b : ℝ := (ℓ : ℝ)
  set M : ℝ := ((#s).choose ℓ : ℝ)
  have hP : (#P : ℝ) = M := by simp [P, M]
  have hS₁ : c * ∑ J ∈ P, (#(U ∩ J) : ℝ) = a * b * M := by
    simpa only [Nat.cast_mul, Nat.cast_sum] using
      congrArg (Nat.cast (R := ℝ)) (card_mul_sum_card_inter_powersetCard (ℓ := ℓ) hU)
  have hexp : ∑ J ∈ P, (c * #(U ∩ J) - a * b) ^ 2 =
      c ^ 2 * ∑ J ∈ P, (#(U ∩ J) : ℝ) * (#(U ∩ J) - 1) +
        (c - 2 * a * b) * (c * ∑ J ∈ P, (#(U ∩ J) : ℝ)) + #P * (a ^ 2 * b ^ 2) := by
    rw [sum_congr rfl fun J _ => show (c * #(U ∩ J) - a * b) ^ 2 =
      c ^ 2 * ((#(U ∩ J) : ℝ) * (#(U ∩ J) - 1)) +
        (c - 2 * a * b) * (c * #(U ∩ J)) + a ^ 2 * b ^ 2 by ring]
    simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]; ring
  have hkey : c ^ 2 * ∑ J ∈ P, (#(U ∩ J) : ℝ) * (#(U ∩ J) - 1) ≤ a ^ 2 * b ^ 2 * M :=
    sq_card_mul_sum_card_inter_mul_sub_one_powersetCard_le hU
  change ∑ J ∈ P, (c * #(U ∩ J) - a * b) ^ 2 ≤ c * a * b * M
  rw [hexp, hS₁, hP]; nlinarith

/-- **Chebyshev's inequality for `#(U ∩ J)`**: with `n = #s` and `n m ≤ #U ℓ` (so `m` is at most
the mean), the `ℓ`-subsets `J` of `s` meeting `U` in fewer than `m` elements number at most
`n #U ℓ C(n, ℓ) / (#U ℓ - n m)²`. -/
theorem card_filter_card_inter_lt_mul_sq_le (hU : U ⊆ s) {m : ℕ} (hm : #s * m ≤ #U * ℓ) :
    (#{J ∈ s.powersetCard ℓ | #(U ∩ J) < m} : ℝ) * ((#U : ℝ) * ℓ - #s * m) ^ 2 ≤
      #s * #U * ℓ * (#s).choose ℓ := by
  refine (card_filter_mul_le_sum _ _ _ (fun _ _ => sq_nonneg _) fun J _ hJ => ?_).trans
    (sum_card_inter_sub_sq_le hU)
  have hcX : (#s : ℝ) * #(U ∩ J) ≤ #s * m :=
    mul_le_mul_of_nonneg_left (mod_cast hJ.le) (by positivity)
  rw [show ((#s : ℝ) * #(U ∩ J) - #U * ℓ) ^ 2 = (#U * ℓ - #s * #(U ∩ J)) ^ 2 by ring]
  exact pow_le_pow_left₀ (by cast_linarith [hm]) (by cast_linarith) 2

/-- **Most `ℓ`-subsets meet `U` in at least half the expected number of elements**: if the
expected size `μ = #U ℓ / #s` of `U ∩ J` is at least `8`, at most half of the `ℓ`-subsets `J` of
`s` meet `U` in fewer than `m ≤ μ / 2` elements. -/
theorem two_mul_card_filter_card_inter_lt_le (hU : U ⊆ s) (hs : 0 < #s)
    (hμ : 8 * #s ≤ #U * ℓ) {m : ℕ} (hm : 2 * m * #s ≤ #U * ℓ) :
    2 * #{J ∈ s.powersetCard ℓ | #(U ∩ J) < m} ≤ (#s).choose ℓ := by
  have h := card_filter_card_inter_lt_mul_sq_le (ℓ := ℓ) hU (m := m) (by nlinarith)
  suffices h' : 2 * (#{J ∈ s.powersetCard ℓ | #(U ∩ J) < m} : ℝ) ≤ (#s).choose ℓ from mod_cast h'
  have hc : (0 : ℝ) < #s := mod_cast hs
  have hμR : 8 * (#s : ℝ) ≤ #U * ℓ := mod_cast hμ
  have hmR : 2 * (m : ℝ) * #s ≤ #U * ℓ := mod_cast hm
  have hK : (0 : ℝ) ≤ #{J ∈ s.powersetCard ℓ | #(U ∩ J) < m} := by positivity
  rw [mul_assoc (#s : ℝ)] at h
  generalize (#{J ∈ s.powersetCard ℓ | #(U ∩ J) < m} : ℝ) = K at h hK ⊢
  generalize ((#U : ℝ) * ℓ) = μ at h hμR hmR
  generalize (((#s).choose ℓ : ℕ) : ℝ) = M at h ⊢
  generalize (#s : ℝ) = c at h hc hμR hmR
  have h₁ : K * (μ / 2) ^ 2 ≤ c * μ * M :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith)
      (by linarith [show 0 ≤ c * m by positivity]) 2) hK).trans h
  have h₂ : K * μ ≤ 4 * c * M :=
    le_of_mul_le_mul_right (by nlinarith : K * μ * μ ≤ 4 * c * M * μ) (by linarith)
  exact le_of_mul_le_mul_left (by nlinarith : 4 * c * (2 * K) ≤ 4 * c * M) (by linarith)

end Cslib
