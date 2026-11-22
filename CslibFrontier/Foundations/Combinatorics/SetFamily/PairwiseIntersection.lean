/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Linarith

/-!
# Unions of sets with few pairwise intersections

If the pairwise intersections of finite sets `A₁, …, Aₙ` are small compared with their sizes,
`∑_{i<j} |Aᵢ ∩ Aⱼ| ≤ C ∑ᵢ |Aᵢ|`, then their union is large: `∑ᵢ |Aᵢ| ≤ 4C |⋃ᵢ Aᵢ|`
[Arora and Barak, Claim 18.34][AroraBarak09]. The proof counts, for every element `x` of the
union, the number `kₓ` of sets containing it: `∑ᵢ |Aᵢ| = ∑ₓ kₓ` and
`∑ₓ kₓ² = ∑ᵢ |Aᵢ| + 2 ∑_{i<j} |Aᵢ ∩ Aⱼ|`, so Cauchy–Schwarz gives
`(∑ᵢ |Aᵢ|)² ≤ |⋃ᵢ Aᵢ| (2C + 1) ∑ᵢ |Aᵢ|`. The draft instead keeps a random part of the family and
applies the second Bonferroni inequality; the double count is shorter and gives the factor
`2C + 1 ≤ 4C`.

The double count holds for any family of sets inside a finite set `U`:
`(∑_c |B_c|)² ≤ |U| ∑_c ∑_{c'} |B_c ∩ B_{c'}|`
(`Finset.sq_sum_card_le_card_mul_sum_sum_card_inter`). The Johnson bound for codes
(`Cslib.Code.card_mul_sub_le_of_le_card_of_card_inter_le`) uses it with equal-size sets and a bound
on each pairwise intersection.

## Main results

* `Finset.sq_sum_card_le_card_mul_sum_sum_card_inter`: incidence counting with Cauchy–Schwarz.
* `Finset.sum_card_le_four_mul_card_biUnion`: Arora–Barak Claim 18.34.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], draft of
  2007-01-08, Claim 18.34
-/

public section

namespace Finset

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- A double sum of a symmetric function over `Fin n` is its diagonal plus twice its sum over the
pairs `i < j`. -/
private theorem sum_sum_eq_sum_add_two_mul (f : Fin n → Fin n → ℕ) (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, f i j = ∑ i, f i i + 2 * ∑ i, ∑ j ∈ Ioi i, f i j := by
  have hsplit (i : Fin n) : ∑ j, f i j = ∑ j ∈ Iio i, f i j + f i i + ∑ j ∈ Ioi i, f i j := by
    rw [← sum_filter_add_sum_filter_not univ (· < i), ← sum_filter_add_sum_filter_not
      (univ.filter fun j => ¬ j < i) (· = i), add_assoc]
    congr 1
    · congr 1; ext j; simp
    · congr 1
      · rw [sum_filter, sum_filter, sum_eq_single i (by simp +contextual) (by simp)]; simp
      · congr 1; ext j; simp; omega
  have hswap : ∑ i, ∑ j ∈ Iio i, f i j = ∑ i, ∑ j ∈ Ioi i, f i j := by
    rw [sum_comm' (t' := univ) (s' := fun j => Ioi j) fun _ _ => by simp]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => hf j i
  simp only [hsplit, sum_add_distrib, hswap]
  omega

/-- **Incidence counting.** If the sets `B c` for `c ∈ L` lie in a finite set `U`, then
`(∑_c |B c|)² ≤ |U| ∑_c ∑_{c'} |B c ∩ B c'|`. With `kₓ` the number of sets containing `x`,
`∑_c |B c| = ∑ₓ kₓ` and `∑_c ∑_{c'} |B c ∩ B c'| = ∑ₓ kₓ²`, so this is Cauchy–Schwarz over `U`. -/
theorem sq_sum_card_le_card_mul_sum_sum_card_inter {κ : Type*} (L : Finset κ) (B : κ → Finset α)
    {U : Finset α} (hB : ∀ c ∈ L, B c ⊆ U) :
    (∑ c ∈ L, #(B c)) ^ 2 ≤ #U * ∑ c ∈ L, ∑ c' ∈ L, #(B c ∩ B c') := by
  classical
  set k : α → ℕ := fun x => #{c ∈ L | x ∈ B c}
  have hcard (s : Finset α) (hs : s ⊆ U) : #s = ∑ x ∈ U, if x ∈ s then 1 else 0 := by
    rw [← sum_filter, sum_const, smul_eq_mul, mul_one, filter_mem_eq_inter, inter_eq_right.2 hs]
  have h1 : ∑ c ∈ L, #(B c) = ∑ x ∈ U, k x := by
    rw [sum_congr rfl fun c hc => hcard (B c) (hB c hc)]
    simp only [k, card_filter]
    rw [sum_comm]
  have h2 : ∑ c ∈ L, ∑ c' ∈ L, #(B c ∩ B c') = ∑ x ∈ U, k x ^ 2 := by
    rw [sum_congr rfl fun c hc => sum_congr rfl fun c' _ =>
      hcard (B c ∩ B c') (inter_subset_left.trans (hB c hc))]
    simp only [mem_inter, ite_and, k, card_filter, sq, sum_mul_sum]
    conv_lhs => enter [2, c]; rw [sum_comm]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => sum_congr rfl fun c _ => sum_congr rfl fun c' _ => ?_
    split_ifs <;> simp
  rw [h1, h2]
  exact sq_sum_le_card_mul_sum_sq

/-- **Few pairwise intersections force a large union** [Arora and Barak, Claim 18.34]. If finite
sets `A₁, …, Aₙ` satisfy `∑_{i<j} |Aᵢ ∩ Aⱼ| ≤ C ∑ᵢ |Aᵢ|` for a positive integer `C`, then
`|⋃ᵢ Aᵢ| ≥ ∑ᵢ |Aᵢ| / 4C`. The draft takes `C ∈ ℕ`; the bound needs `C > 0`, which its proof
uses. -/
theorem sum_card_le_four_mul_card_biUnion (A : Fin n → Finset α) {C : ℕ} (hC : 0 < C)
    (h : ∑ i, ∑ j ∈ Ioi i, #(A i ∩ A j) ≤ C * ∑ i, #(A i)) :
    ∑ i, #(A i) ≤ 4 * C * #(univ.biUnion A) := by
  set U := univ.biUnion A
  have hcs0 := sq_sum_card_le_card_mul_sum_sum_card_inter univ A (U := U)
    fun i _ => subset_biUnion_of_mem A (mem_univ i)
  have h3 := sum_sum_eq_sum_add_two_mul (fun i j => #(A i ∩ A j)) fun i j => by
    rw [inter_comm]
  simp only [inter_self] at h3
  set S := ∑ i, #(A i)
  -- Cauchy–Schwarz: `S² ≤ |U| ∑ᵢ ∑ⱼ |Aᵢ ∩ Aⱼ| ≤ |U| (2C + 1) S`.
  have hcs : S * S ≤ #U * ((2 * C + 1) * S) := by
    calc S * S = S ^ 2 := (sq S).symm
      _ ≤ #U * ∑ i, ∑ j, #(A i ∩ A j) := hcs0
      _ = #U * (S + 2 * ∑ i, ∑ j ∈ Ioi i, #(A i ∩ A j)) := by rw [h3]
      _ ≤ #U * ((2 * C + 1) * S) := by gcongr; nlinarith
  rcases Nat.eq_zero_or_pos S with hS | hS
  · rw [hS]; exact Nat.zero_le _
  have : S ≤ #U * (2 * C + 1) := Nat.le_of_mul_le_mul_right (by linarith) hS
  nlinarith

end Finset
