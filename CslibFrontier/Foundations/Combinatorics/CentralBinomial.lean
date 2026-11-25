/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Card
import CslibFrontier.Tactic.FinsetCard
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Most sets are not much larger than half

The middle binomial coefficient is at most `2 ^ n / sqrt (n + 1)`:
`C(n, ⌊n/2⌋)² (n + 1) ≤ 4 ^ n` (`choose_half_sq_mul_le`). So the sets of at most `n / 2 + t` of `n`
elements, which are those of fewer than `n / 2` elements (at most half of all sets, by
complementation) and those of between `n / 2` and `n / 2 + t` elements (at most `t + 1` middle
binomial coefficients), are at most `6 / 10` of all sets when `100 (t + 1)² ≤ n + 1`
(`ten_mul_card_filter_card_le_le`). This is the counting step of Smolensky's lower bound
[Smolensky1987].

## Main results

* `Nat.centralBinom_sq_mul_le`: `C(2m, m)² (2m + 1) ≤ 16 ^ m`.
* `Cslib.two_pow_succ_le_centralBinom`: `2 ^ (B + 1) ≤ B.centralBinom` for `B ≥ 3`.
* `Cslib.choose_half_sq_mul_le`: `C(n, ⌊n/2⌋)² (n + 1) ≤ 4 ^ n`.
* `Cslib.choose_le_choose_of_le_of_le_half`: `C(n, k) ≤ C(n, a)` for `k ≤ a ≤ n / 2`, binomial
  coefficients below half increase.
* `Cslib.ten_mul_card_filter_card_le_le`: few sets are much larger than half.
* `Cslib.four_mul_two_pow_le_mul_choose_sub`: `4 · 2 ^ n ≤ 5 (n + 1) C(n, ⌈n/2⌉ - s)` when
  `1 ≤ s` and `100 s² ≤ n + 1`, a binomial coefficient near the middle is large.

## References

* [R. Smolensky, *Algebraic methods in the theory of lower bounds for Boolean circuit
  complexity*][Smolensky1987]
-/

public section

namespace Cslib

open Finset

/-- `2 ^ (B + 1) ≤ B.centralBinom` for `B ≥ 3`. -/
theorem two_pow_succ_le_centralBinom {B : ℕ} (hB : 3 ≤ B) : 2 ^ (B + 1) ≤ B.centralBinom := by
  induction B, hB using Nat.le_induction with
  | base => decide
  | succ B hB ih =>
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos B)
    rw [Nat.succ_mul_centralBinom_succ, pow_succ']
    calc (B + 1) * (2 * 2 ^ (B + 1)) = (2 * B + 2) * 2 ^ (B + 1) := by ring
      _ ≤ 2 * (2 * B + 1) * B.centralBinom := Nat.mul_le_mul (by omega) ih

/-- The middle binomial coefficient satisfies `C(n, ⌊n/2⌋)² (n + 1) ≤ 4^n`. -/
theorem choose_half_sq_mul_le (n : ℕ) :
    n.choose (n / 2) ^ 2 * (n + 1) ≤ 4 ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [Nat.mul_div_right _ zero_lt_two, ← Nat.centralBinom_eq_two_mul_choose, pow_mul]
    simpa using Nat.centralBinom_sq_mul_le m
  · have hc : 2 * (2 * m + 1).choose m = (m + 1).centralBinom := by
      rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
        Nat.choose_succ_succ', Nat.choose_symm_half]; omega
    have hcentral := Nat.centralBinom_sq_mul_le (m + 1)
    rw [← hc, show (16 : ℕ) ^ (m + 1) = 4 * 4 ^ (2 * m + 1) by
      rw [pow_succ, pow_succ, pow_mul]; norm_num; ring] at hcentral
    rw [show (2 * m + 1) / 2 = m by omega]
    have hle : 4 * ((2 * m + 1).choose m ^ 2 * (2 * m + 1 + 1)) ≤
        (2 * (2 * m + 1).choose m) ^ 2 * (2 * (m + 1) + 1) :=
      calc 4 * ((2 * m + 1).choose m ^ 2 * (2 * m + 1 + 1))
          = (2 * (2 * m + 1).choose m) ^ 2 * (2 * m + 2) := by ring
        _ ≤ (2 * (2 * m + 1).choose m) ^ 2 * (2 * (m + 1) + 1) := Nat.mul_le_mul_left _ (by omega)
    exact Nat.le_of_mul_le_mul_left (hle.trans hcentral) (by decide)

/-- Complementation shows that at most half of all subsets have fewer than
`n / 2` elements. -/
theorem two_mul_card_small_le (n : ℕ) :
    2 * (univ.filter fun S : Finset (Fin n) => 2 * S.card < n).card ≤ 2 ^ n := by
  set A := univ.filter fun S : Finset (Fin n) => 2 * S.card < n
  set B := univ.filter fun S : Finset (Fin n) => n < 2 * S.card
  have hAB : A.card ≤ B.card := card_le_card_of_injOn (·ᶜ) (fun S hS => by
      simp only [A, B, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢; finset_card)
    compl_injective.injOn
  have hdisj : Disjoint A B := disjoint_filter.2 fun _ _ => by omega
  finset_card [show Fintype.card (Finset (Fin n)) = 2 ^ n by simp]

private lemma card_filter_card_eq_le {n : ℕ} (X : Finset (Finset (Fin n))) (k : ℕ) :
    (X.filter fun S => S.card = k).card ≤ n.choose k := by
  simpa [card_powersetCard] using card_le_card (t := powersetCard k (univ : Finset (Fin n)))
    fun S hS => mem_powersetCard.2 ⟨subset_univ S, (mem_filter.1 hS).2⟩

/-- Subsets of size between `n / 2` and `n / 2 + t` number at most
`(t + 1) · C(n, ⌊n/2⌋)`. -/
theorem card_middle_le (n t : ℕ) :
    (univ.filter fun S : Finset (Fin n) =>
      n ≤ 2 * S.card ∧ S.card ≤ n / 2 + t).card ≤ (t + 1) * n.choose (n / 2) := by
  classical
  refine (card_le_mul_card_image_of_maps_to (t := Icc ((n + 1) / 2) (n / 2 + t)) (f := card)
    (fun S hS => by simp only [mem_filter, mem_univ, true_and] at hS; rw [mem_Icc]; omega)
    (n.choose (n / 2)) fun b _ =>
      (card_filter_card_eq_le _ b).trans (Nat.choose_le_middle b n)).trans ?_
  rw [mul_comm]; exact Nat.mul_le_mul_right _ (by rw [Nat.card_Icc]; omega)

/-- When `100 (t + 1)² ≤ n + 1`, at most `6/10` of the subsets of `Fin n` have
at most `n / 2 + t` elements. -/
theorem ten_mul_card_filter_card_le_le (n t : ℕ) (h : 100 * (t + 1) ^ 2 ≤ n + 1) :
    10 * (univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + t).card ≤ 6 * 2 ^ n := by
  set A := univ.filter fun S : Finset (Fin n) => 2 * S.card < n
  set M := univ.filter fun S : Finset (Fin n) => n ≤ 2 * S.card ∧ S.card ≤ n / 2 + t
  have hsub : (univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + t) ⊆ A ∪ M := fun S hS => by
    simp only [A, M, mem_union, mem_filter, mem_univ, true_and] at hS ⊢; omega
  have hA : 2 * A.card ≤ 2 ^ n := two_mul_card_small_le n
  have hM : 10 * M.card ≤ 10 * ((t + 1) * n.choose (n / 2)) :=
    Nat.mul_le_mul_left 10 (card_middle_le n t)
  have hmid : 10 * ((t + 1) * n.choose (n / 2)) ≤ 2 ^ n :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp <| calc
      (10 * ((t + 1) * n.choose (n / 2))) ^ 2
        = 100 * (t + 1) ^ 2 * n.choose (n / 2) ^ 2 := by ring
      _ ≤ (n + 1) * n.choose (n / 2) ^ 2 := Nat.mul_le_mul_right _ h
      _ ≤ (2 ^ n) ^ 2 := by
        simpa only [mul_comm (n + 1), show 4 ^ n = (2 ^ n) ^ 2 by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num] using choose_half_sq_mul_le n
  have hU := Nat.mul_le_mul_left 10 ((card_le_card hsub).trans (card_union_le A M))
  omega

/-- Below `n / 2`, the binomial coefficients `C(n, k)` increase with `k`. -/
theorem choose_le_choose_of_le_of_le_half {n k a : ℕ} (hka : k ≤ a) (ha : a ≤ n / 2) :
    n.choose k ≤ n.choose a := by
  induction hka using Nat.decreasingInduction with
  | self => exact le_rfl
  | of_succ j hj ih => exact (Nat.choose_le_succ_of_lt_half_left (by omega)).trans ih

/-- **A binomial coefficient near the middle is large**: when `1 ≤ s` and
`100 s² ≤ n + 1`, the coefficient `C(n, ⌈n/2⌉ - s)` is at least `4 · 2 ^ n / (5 (n + 1))`. The
sets of at most `⌈n/2⌉ - s` elements are the complements of the sets of more than `n / 2 + s - 1`
elements, so they are at least `4 / 10` of all sets (`ten_mul_card_filter_card_le_le`), and each
of their sizes contributes at most `C(n, ⌈n/2⌉ - s)` of them. -/
theorem four_mul_two_pow_le_mul_choose_sub {n s : ℕ} (hs : 1 ≤ s) (h : 100 * s ^ 2 ≤ n + 1) :
    4 * 2 ^ n ≤ 5 * (n + 1) * n.choose ((n + 1) / 2 - s) := by
  set a := (n + 1) / 2 - s
  have hs2 : s ≤ s ^ 2 := Nat.le_self_pow two_ne_zero s
  have ha : a ≤ n / 2 := by omega
  set L := univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + (s - 1)
  set A := univ.filter fun S : Finset (Fin n) => S.card ≤ a
  have hL : 10 * L.card ≤ 6 * 2 ^ n :=
    ten_mul_card_filter_card_le_le n (s - 1) (by rwa [Nat.sub_add_cancel hs])
  have htotal : L.card + (univ.filter fun S : Finset (Fin n) => ¬S.card ≤ n / 2 + (s - 1)).card =
      2 ^ n := by
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_finset, Fintype.card_fin]
  have hcompl : (univ.filter fun S : Finset (Fin n) => ¬S.card ≤ n / 2 + (s - 1)).card ≤ A.card :=
    card_le_card_of_injOn (·ᶜ) (fun S hS => by
      simp only [A, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢; finset_card)
      compl_injective.injOn
  have hA : A.card ≤ n.choose a * (a + 1) := by
    rw [← card_range (a + 1)]
    exact card_le_mul_card_image_of_maps_to (f := card)
      (fun S hS => mem_range.2 (Nat.lt_succ_of_le (mem_filter.1 hS).2)) _ fun k hk =>
        (card_filter_card_eq_le A k).trans
          (choose_le_choose_of_le_of_le_half (Nat.lt_succ_iff.1 (mem_range.1 hk)) ha)
  have hmul : 10 * (n.choose a * (a + 1)) ≤ 5 * (n + 1) * n.choose a := by
    rw [show 10 * (n.choose a * (a + 1)) = 10 * (a + 1) * n.choose a by ring]
    exact Nat.mul_le_mul_right _ (by omega)
  omega

end Cslib
