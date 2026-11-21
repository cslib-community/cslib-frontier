/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, finite-set selection)

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Selecting one member of a finite set by coordinate tests

When coordinate values distinguish the members of a finite set, each test can keep
a nonempty fiber of size at most half. A logarithmic number of equalities therefore
selects one member uniquely.

Adapted from `SparseSelection` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Finset

variable {α ι β : Type*}

/-- If the coordinate function is injective on a nonempty finite set of size at most
`2 ^ N`, some member is uniquely selected by a list of at most `N` coordinate equalities. -/
theorem exists_short_coordinate_selector {S : Finset α} (hS : S.Nonempty)
    {f : α → ι → β} (hinj : Set.InjOn f (S : Set α)) {N : ℕ} (hcard : S.card ≤ 2 ^ N) :
    ∃ L : List (ι × β), L.length ≤ N ∧
      ∃ x ∈ S, ∀ y ∈ S, (∀ c ∈ L, f y c.1 = c.2) ↔ y = x := by
  classical
  induction N using Nat.strong_induction_on generalizing S with
  | ind N ih =>
    by_cases hsingle : S.card ≤ 1
    · obtain ⟨x, hx⟩ := hS
      refine ⟨[], Nat.zero_le _, x, hx, fun y hy => ?_⟩
      exact ⟨fun _ => card_le_one.mp hsingle y hy x hx, fun _ _ h => (List.not_mem_nil h).elim⟩
    have hN : N ≠ 0 := by
      rintro rfl
      exact hsingle (by simpa only [pow_zero] using hcard)
    obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
    obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (lt_of_not_ge hsingle)
    have hne : f a ≠ f b := fun he => hab (hinj ha hb he)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    let fiber (v : β) := S.filter (fun x => f x i = v)
    have hdisj : Disjoint (fiber (f a i)) (fiber (f b i)) := by
      apply disjoint_left.mpr
      intro x hxa hxb
      exact hi ((mem_filter.mp hxa).2.symm.trans (mem_filter.mp hxb).2)
    have hsum : (fiber (f a i)).card + (fiber (f b i)).card ≤ S.card := by
      rw [← card_union_of_disjoint hdisj]
      exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
    obtain ⟨v, hv, hsmall⟩ : ∃ v, (fiber v).Nonempty ∧ (fiber v).card ≤ 2 ^ N := by
      by_cases h : (fiber (f a i)).card ≤ 2 ^ N
      · exact ⟨f a i, ⟨a, mem_filter.mpr ⟨ha, rfl⟩⟩, h⟩
      · refine ⟨f b i, ⟨b, mem_filter.mpr ⟨hb, rfl⟩⟩, ?_⟩
        rw [pow_succ] at hcard
        omega
    have hsub : fiber v ⊆ S := filter_subset _ _
    obtain ⟨L, hL, x, hx, hsel⟩ := ih N (Nat.lt_succ_self _) hv (hinj.mono hsub) hsmall
    refine ⟨(i, v) :: L, Nat.succ_le_succ hL, x, hsub hx, fun y hy => ?_⟩
    simp only [List.forall_mem_cons]
    constructor
    · rintro ⟨hyi, hyL⟩
      exact (hsel y (mem_filter.mpr ⟨hy, hyi⟩)).mp hyL
    · intro hxy
      subst y
      exact ⟨(mem_filter.mp hx).2, (hsel x hx).mpr rfl⟩

end Finset
