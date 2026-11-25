/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, `Finset.exists_subset_card_eq` for two sets)

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic

/-!
# Disjoint subsets of given sizes

A finite set with at least `i + j` elements has disjoint subsets with `i` and `j` elements
(`Finset.exists_disjoint_card_eq`). The proof of Theorem D.2 and Lemma F.1 of
[AnthropicVPVNP2026] take such a pair of sets of indices for a transversal pair of matrices.

## Main results

* `Finset.exists_disjoint_card_eq`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Step 1 of the proof of Theorem D.2, p. 30; module `Paper.Alternative` (`exists_disjoint_card`)
-/

public section

namespace Finset

/-- A finite set with at least `i + j` elements has disjoint subsets with `i` and `j`
elements. -/
theorem exists_disjoint_card_eq {α : Type*} {s : Finset α} {i j : ℕ} (h : i + j ≤ #s) :
    ∃ S ⊆ s, ∃ T ⊆ s, Disjoint S T ∧ #S = i ∧ #T = j := by
  classical
  obtain ⟨S, hS, rfl⟩ := exists_subset_card_eq (s := s) (n := i) (by omega)
  obtain ⟨T, hT, rfl⟩ := exists_subset_card_eq (s := s \ S) (n := j)
    (by rw [card_sdiff_of_subset hS]; omega)
  exact ⟨S, hS, T, hT.trans sdiff_subset, disjoint_of_subset_right hT disjoint_sdiff, rfl, rfl⟩

end Finset
