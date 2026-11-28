/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.Bounds
import Mathlib.Data.Fintype.EquivFin

/-!
# Query lower bounds from distinct inputs

Selection adversaries often give an oracle for each list of distinct keys.
An infinite alphabet supplies such a list of every length.
-/

public section

namespace Cslib.Query

universe u v w

/-- A per-input adversary for lists with distinct entries gives a worst-case query lower bound
over an infinite alphabet, using an input of exactly the requested length. -/
theorem LowerBound.of_nodup {α : Type w} [Infinite α] {Q : Type u → Type v} {β : Type u}
    {prog : List α → FreeM Q β} {bound : ℕ → ℕ}
    (h : ∀ xs : List α, xs.Nodup → ∃ oracle : {ι : Type u} → Q ι → ι,
      bound xs.length ≤ (prog xs).countQueries oracle) : LowerBound prog List.length bound := by
  intro n
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α n
  have hlen : s.toList.length = n := (Finset.length_toList s).trans hs
  obtain ⟨oracle, hcount⟩ := h s.toList s.nodup_toList
  exact ⟨s.toList, hlen.le, oracle, hlen ▸ hcount⟩

end Cslib.Query
