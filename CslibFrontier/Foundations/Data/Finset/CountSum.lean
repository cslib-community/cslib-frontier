/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, Mathlib.Algebra.Order.BigOperators.Group.Finset)

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card

/-!
# Recovering a finite set and its weights from a tally

An exact count rules out missing elements in a subset. If the observed weights dominate
the expected weights pointwise, an exact sum then rules out any overestimate.
-/

public section

namespace Finset

/-- A subset with the expected cardinality and total weight has exactly the expected
elements and weights, provided every observed weight is at least its expected weight. -/
theorem eq_and_eqOn_of_card_eq_of_sum_eq {α M : Type*} [AddCommMonoid M] [PartialOrder M]
    [IsOrderedCancelAddMonoid M] {s t : Finset α} {f g : α → M}
    (hsub : s ⊆ t) (hle : ∀ a ∈ s, g a ≤ f a) (hcard : s.card = t.card)
    (hsum : ∑ a ∈ s, f a = ∑ a ∈ t, g a) :
    s = t ∧ Set.EqOn g f s := by
  have heq := eq_of_subset_of_card_le hsub hcard.ge
  exact ⟨heq, (sum_eq_sum_iff_of_le hle).mp (heq ▸ hsum.symm)⟩

end Finset
