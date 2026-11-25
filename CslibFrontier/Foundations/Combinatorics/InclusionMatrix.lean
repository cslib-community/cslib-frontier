/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, inclusion matrices of subsets)

public import CslibFrontier.Init
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination

/-!
# Inclusion matrices of subsets

The *inclusion matrix* `W_{t,s}` of a finite set `U` has its rows indexed by the `t`-element
subsets `A` of `U`, its columns by the `s`-element subsets `B`, and the entry `1` when `A ⊆ B`.
**Gottlieb's theorem** [Gottlieb1966] says that for `t ≤ s` and `t + s ≤ #U` the matrix has full
row rank over `ℚ`: a weighting `a` of the `t`-subsets whose sums `∑_{A ⊆ B, #A = t} a A` vanish for
every `s`-subset `B` is zero (`Finset.eq_zero_of_sum_powersetCard_eq_zero`).

The theorem is proved here over any field in which the integers `1, …, s` are nonzero, so in
characteristic zero and in every characteristic larger than `s`. Gottlieb states the rational
case. The proof here, by induction on `U`, divides only by integers between `2` and `s`, so this
mild generalization costs nothing. The induction splits the subsets by an element `x`
(`Finset.sum_powersetCard_succ_insert`). Double counting (`Finset.sum_sum_powersetCard_erase`)
gives the hypothesis for the weights `A ↦ a (insert x A)` of the `(t-1)`-subsets, up to the
factor `s - t + 1`, which is the only division. Both halves then reduce to weightings of the
smaller set with smaller parameters.
Impagliazzo, Pudlák and Sgall use the theorem to bound polynomial-calculus degree
[ImpagliazzoPudlakSgall1999].

## Main results

* `Finset.sum_sum_powersetCard_erase`: each `t`-subset of `B` misses `#B - t` elements of `B`.
* `Finset.sum_powersetCard_succ_insert`: the `(t+1)`-subsets of `insert x B` split by whether they
  contain `x`.
* `Finset.eq_zero_of_sum_powersetCard_eq_zero`: Gottlieb's theorem, over a field in which
  `1, …, s` are nonzero.

## References

* [D. H. Gottlieb, *A certain class of incidence matrices*][Gottlieb1966]
* [R. Impagliazzo, P. Pudlák, J. Sgall, *Lower bounds for the polynomial calculus and the Gröbner
  basis algorithm*][ImpagliazzoPudlakSgall1999]
-/

public section

open Finset

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- **Double counting `t`-subsets.** Summing over the `t`-subsets of `B.erase i` for every `i ∈ B`
counts each `t`-subset `A` of `B` once for each of the `#B - t` elements of `B \ A`. -/
theorem sum_sum_powersetCard_erase {M : Type*} [AddCommMonoid M] (a : Finset α → M) (t : ℕ)
    (B : Finset α) :
    ∑ i ∈ B, ∑ A ∈ (B.erase i).powersetCard t, a A = (#B - t) • ∑ A ∈ B.powersetCard t, a A := by
  have h1 (i : α) : ∑ A ∈ (B.erase i).powersetCard t, a A =
      ∑ A ∈ B.powersetCard t, if i ∉ A then a A else 0 := by
    rw [← sum_filter]
    exact sum_congr (by ext; simp [mem_powersetCard, subset_erase]; tauto) fun _ _ => rfl
  simp_rw [h1]
  rw [sum_comm, smul_sum]
  refine sum_congr rfl fun A hA => ?_
  rw [mem_powersetCard] at hA
  rw [← sum_filter, sum_const, ← sdiff_eq_filter, card_sdiff_of_subset hA.1, hA.2]

/-- The `(t + 1)`-subsets of `insert x B`, for `x ∉ B`, are the `(t + 1)`-subsets of `B` and the
sets `insert x A` for the `t`-subsets `A` of `B`. -/
theorem sum_powersetCard_succ_insert {M : Type*} [AddCommMonoid M] (a : Finset α → M) {x : α}
    {B : Finset α} (hxB : x ∉ B) (t : ℕ) :
    ∑ A ∈ (insert x B).powersetCard (t + 1), a A =
      ∑ A ∈ B.powersetCard (t + 1), a A + ∑ A ∈ B.powersetCard t, a (insert x A) := by
  rw [powersetCard_succ_insert hxB, sum_union (disjoint_left.2 fun A h₁ h₂ => by
      obtain ⟨A', _, rfl⟩ := mem_image.1 h₂
      exact hxB ((mem_powersetCard.1 h₁).1 (mem_insert_self x A'))),
    sum_image fun A₁ h₁ A₂ h₂ h => by
      rw [← erase_insert fun h' => hxB ((mem_powersetCard.1 (mem_coe.1 h₁)).1 h'),
        ← erase_insert fun h' => hxB ((mem_powersetCard.1 (mem_coe.1 h₂)).1 h'), h]]

variable {F : Type*} [Field F]

omit [DecidableEq α] in
/-- **Gottlieb's theorem** [Gottlieb1966]: for `t ≤ s` and `t + s ≤ #U`, the inclusion matrix of
the `t`-subsets against the `s`-subsets of `U` has full row rank. If the weights `a A` of the
`t`-subsets sum to zero inside every `s`-subset `B` of `U`, then every weight is zero.

Gottlieb proves this over `ℚ`; here the field may be any field in which the integers `1, …, s`
are nonzero. -/
theorem eq_zero_of_sum_powersetCard_eq_zero {U : Finset α} {t s : ℕ} (hts : t ≤ s)
    (hsum : t + s ≤ #U) (hU : ∀ j : ℕ, 0 < j → j ≤ s → (j : F) ≠ 0) {a : Finset α → F}
    (ha : ∀ B ∈ U.powersetCard s, ∑ A ∈ B.powersetCard t, a A = 0) :
    ∀ A ∈ U.powersetCard t, a A = 0 := by
  classical
  induction U using Finset.induction_on generalizing t s a with
  | empty =>
    intro A hA
    obtain ⟨rfl, rfl⟩ : t = 0 ∧ s = 0 := by simp at hsum; omega
    simpa [mem_singleton.1 (by simpa using hA)] using ha ∅ (by simp)
  | insert x U hx ih =>
    intro A hA
    have hcard : #(insert x U) = #U + 1 := card_insert_of_notMem hx
    rcases Nat.eq_or_lt_of_le hts with rfl | hlt
    · simpa [← (mem_powersetCard.1 hA).2] using ha A hA
    rcases t.eq_zero_or_pos with rfl | ht
    · obtain ⟨B, hB⟩ := (powersetCard_nonempty (s := insert x U) (n := s)).2 (by omega)
      simpa [card_eq_zero.1 (mem_powersetCard.1 hA).2] using ha B hB
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have eq1 : ∀ B ∈ U.powersetCard (s' + 1), ∑ A ∈ B.powersetCard (t' + 1), a A = 0 :=
      fun B hB => ha B (powersetCard_mono (subset_insert x U) hB)
    have eq2 : ∀ B ∈ U.powersetCard s', ∑ A ∈ B.powersetCard (t' + 1), a A +
        ∑ A ∈ B.powersetCard t', a (insert x A) = 0 := fun B hB => by
      obtain ⟨hBU, hBc⟩ := mem_powersetCard.1 hB
      have hxB : x ∉ B := fun h => hx (hBU h)
      rw [← sum_powersetCard_succ_insert a hxB]
      exact ha _ (mem_powersetCard.2 ⟨insert_subset_insert x hBU, by simp [hxB, hBc]⟩)
    have eq3 : ∀ B ∈ U.powersetCard (s' + 1), ∑ A ∈ B.powersetCard t', a (insert x A) = 0 := by
      intro B hB
      obtain ⟨hBU, hBc⟩ := mem_powersetCard.1 hB
      have h1 := sum_sum_powersetCard_erase a (t' + 1) B
      rw [eq1 B hB, smul_zero] at h1
      have h2 : ∑ i ∈ B, ∑ A ∈ (B.erase i).powersetCard t', a (insert x A) = 0 := by
        rw [sum_congr rfl fun i hi => eq_neg_of_add_eq_zero_right <| eq2 (B.erase i) <|
          mem_powersetCard.2 ⟨(erase_subset i B).trans hBU, by rw [card_erase_of_mem hi, hBc]; rfl⟩,
          sum_neg_distrib, h1, neg_zero]
      rw [sum_sum_powersetCard_erase (fun A => a (insert x A)) t' B, hBc, nsmul_eq_mul] at h2
      exact (mul_eq_zero.1 h2).resolve_left (hU (s' + 1 - t') (by omega) (by omega))
    have ha'' : ∀ A ∈ U.powersetCard t', a (insert x A) = 0 :=
      ih (by omega) (by omega) hU eq3
    have eq5 : ∀ B ∈ U.powersetCard s', ∑ A ∈ B.powersetCard (t' + 1), a A = 0 := fun B hB => by
      simpa [sum_eq_zero fun A hA => ha'' A (powersetCard_mono (mem_powersetCard.1 hB).1 hA)]
        using eq2 B hB
    have ha' : ∀ A ∈ U.powersetCard (t' + 1), a A = 0 :=
      ih (by omega) (by omega) (fun j hj hjs => hU j hj (by omega)) eq5
    obtain ⟨hAU, hAc⟩ := mem_powersetCard.1 hA
    by_cases hxA : x ∈ A
    · simpa [insert_erase hxA] using ha'' (A.erase x) (mem_powersetCard.2
        ⟨subset_insert_iff.1 (by simpa [insert_erase hxA] using hAU), by simp [hxA, hAc]⟩)
    · exact ha' A (mem_powersetCard.2 ⟨(subset_insert_iff_of_notMem hxA).1 hAU, hAc⟩)

end Finset
