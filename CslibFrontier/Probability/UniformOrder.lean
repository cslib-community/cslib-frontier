/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Finset.Max

/-!
# Extreme elements of uniform random orders

For any finite set `S` of size `k > 0` in `α` and any finite linear order `β`, a bijection
`σ : α ≃ β` puts each element `u ∈ S` least among `S` for exactly a `1 / k` fraction of all
bijections (`card_filter_least_mul_card`). By transposition symmetry, swapping `u` and `v`
in `α` gives a bijection between the orders putting `u` least and those putting `v` least.
Since every order has a unique minimum on the nonempty set `S`, these fibers partition `α ≃ β`.

The dual statements for greatest elements (`card_filter_greatest_mul_card`) and for permutations
(`card_filter_perm_least_mul_card`, `card_filter_perm_greatest_mul_card`,
`card_filter_perm_symm_greatest_mul_card`) follow immediately.

## Main results

* `Cslib.Probability.card_filter_least_mul_card`: each `u ∈ S` is minimal on `S` for a `1 / #S`
  fraction of the bijections `α ≃ β`.
* `Cslib.Probability.card_filter_greatest_mul_card`: each `u ∈ S` is maximal on `S` for a `1 / #S`
  fraction of the bijections `α ≃ β`.
* `Cslib.Probability.card_filter_perm_least_mul_card`,
  `Cslib.Probability.card_filter_perm_greatest_mul_card`,
  `Cslib.Probability.card_filter_perm_symm_greatest_mul_card`: permutation specializations.
-/

public section

open Finset

namespace Cslib.Probability

private theorem swap_least {α β : Type*} [DecidableEq α] [LinearOrder β]
    {S : Finset α} {a b : α} (hb : b ∈ S) {σ : α ≃ β}
    (hσ : ∀ w ∈ S, w ≠ a → σ a < σ w) :
    ∀ w ∈ S, w ≠ b → ((Equiv.swap a b).trans σ) b < ((Equiv.swap a b).trans σ) w := by
  intro w hw hwb
  simp only [Equiv.trans_apply, Equiv.swap_apply_right]
  by_cases hwa : w = a
  · rw [hwa, Equiv.swap_apply_left]
    exact hσ b hb (fun h => hwb (hwa.trans h.symm))
  · rw [Equiv.swap_apply_of_ne_of_ne hwa hwb]
    exact hσ w hw hwa

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [LinearOrder β]

/-- In a uniform random bijection `σ : α ≃ β` into a linear order `β`, each element of a nonempty
subset `S ⊆ α` is the least element of `S` for exactly a `1 / |S|` fraction of the bijections. -/
theorem card_filter_least_mul_card {S : Finset α} {u : α} (hu : u ∈ S) :
    (univ.filter fun σ : α ≃ β => ∀ w ∈ S, w ≠ u → σ u < σ w).card * S.card =
      Fintype.card (α ≃ β) := by
  set E : α → Finset (α ≃ β) := fun x => univ.filter fun σ => ∀ w ∈ S, w ≠ x → σ x < σ w
  have heq : ∀ x ∈ S, (E x).card = (E u).card := by
    intro x hx
    refine card_equiv (Equiv.equivCongr (Equiv.swap x u) (Equiv.refl _)) fun σ => ?_
    simp only [E, mem_filter, mem_univ, true_and, Equiv.equivCongr_apply_apply, Equiv.refl_apply,
      Equiv.symm_swap]
    constructor
    · exact swap_least hu
    · intro h
      simpa [Equiv.swap_comm u x] using swap_least hx (σ := (Equiv.swap x u).trans σ) h
  have hcover : (univ : Finset (α ≃ β)) = S.biUnion E := by
    ext σ
    simp only [mem_univ, mem_biUnion, true_iff]
    obtain ⟨x, hx, hmin⟩ := S.exists_min_image σ ⟨u, hu⟩
    refine ⟨x, hx, ?_⟩
    simp only [E, mem_filter, mem_univ, true_and]
    exact fun w hw hwx => lt_of_le_of_ne (hmin w hw) (fun h => hwx (σ.injective h).symm)
  have hdisj : (S : Set α).PairwiseDisjoint E := by
    intro x _ y _ hxy
    refine disjoint_left.2 fun σ hx hy => ?_
    simp only [E, mem_filter, mem_univ, true_and] at hx hy
    exact lt_asymm (hx y ‹_› (Ne.symm hxy)) (hy x ‹_› hxy)
  change (E u).card * S.card = _
  rw [← card_univ, hcover, card_biUnion hdisj, sum_congr rfl heq, sum_const, smul_eq_mul, mul_comm]

/-- In a uniform random bijection `σ : α ≃ β` into a linear order `β`, each element of a nonempty
subset `S ⊆ α` is the greatest element of `S` for exactly a `1 / |S|` fraction of the bijections. -/
theorem card_filter_greatest_mul_card {S : Finset α} {u : α} (hu : u ∈ S) :
    (univ.filter fun σ : α ≃ β => ∀ w ∈ S, w ≠ u → σ w < σ u).card * S.card =
      Fintype.card (α ≃ β) := by
  have hequiv : (univ.filter fun σ : α ≃ β => ∀ w ∈ S, w ≠ u → σ w < σ u).card =
      (univ.filter fun σ : α ≃ OrderDual β => ∀ w ∈ S, w ≠ u → σ u < σ w).card := by
    refine card_equiv (Equiv.equivCongr (Equiv.refl α) OrderDual.toDual) fun σ => ?_
    simp only [mem_filter, mem_univ, true_and, Equiv.equivCongr_apply_apply, Equiv.refl_symm,
      Equiv.refl_apply, OrderDual.toDual_lt_toDual]
  rw [hequiv, card_filter_least_mul_card (β := OrderDual β) hu]
  exact Fintype.card_congr (Equiv.equivCongr (Equiv.refl α) OrderDual.toDual)

omit [Fintype β] [DecidableEq β] [LinearOrder β] in
/-- In a uniform random permutation of a finite linear order `α`, each element of a nonempty
subset `S` is least among `S` for a `1 / |S|` fraction of the permutations. -/
theorem card_filter_perm_least_mul_card [LinearOrder α] {S : Finset α} {u : α} (hu : u ∈ S) :
    (univ.filter fun σ : Equiv.Perm α => ∀ w ∈ S, w ≠ u → σ u < σ w).card * S.card =
      (Fintype.card α).factorial := by
  simpa only [Fintype.card_perm] using card_filter_least_mul_card (β := α) hu

omit [Fintype β] [DecidableEq β] [LinearOrder β] in
/-- In a uniform random permutation of a finite linear order `α`, each element of a nonempty
subset `S` is greatest among `S` for a `1 / |S|` fraction of the permutations. -/
theorem card_filter_perm_greatest_mul_card [LinearOrder α] {S : Finset α} {u : α} (hu : u ∈ S) :
    (univ.filter fun σ : Equiv.Perm α => ∀ w ∈ S, w ≠ u → σ w < σ u).card * S.card =
      (Fintype.card α).factorial := by
  simpa only [Fintype.card_perm] using card_filter_greatest_mul_card (β := α) hu

omit [Fintype β] [DecidableEq β] [LinearOrder β] in
/-- In a uniform random permutation of a finite linear order `α`, each element of a nonempty
subset `S` is mapped to the greatest position by its inverse for a `1 / |S|` fraction of the
permutations. -/
theorem card_filter_perm_symm_greatest_mul_card [LinearOrder α] {S : Finset α} {u : α}
    (hu : u ∈ S) :
    (univ.filter fun π : Equiv.Perm α => ∀ w ∈ S, w ≠ u → π.symm w < π.symm u).card * S.card =
      (Fintype.card α).factorial := by
  have hequiv : (univ.filter fun π : Equiv.Perm α => ∀ w ∈ S, w ≠ u → π.symm w < π.symm u).card =
      (univ.filter fun σ : Equiv.Perm α => ∀ w ∈ S, w ≠ u → σ w < σ u).card := by
    refine card_equiv (Equiv.symmEquiv α α) fun π => ?_
    simp only [mem_filter, mem_univ, true_and]
    rfl
  rw [hequiv]
  exact card_filter_perm_greatest_mul_card hu

end Cslib.Probability
