/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Foundations.Combinatorics.SparseModeMass

open Cslib.SparseModeTuple Finset

-- One large gap is followed by a smaller gap and a high multiplicity. Cross terms use the
-- earlier gap with the later multiplicity. A reversed pair and a missing entry contribute zero.
private def entries : List Entry := [⟨4, 1⟩, ⟨0, 99⟩]

example : rowTerm entries 0 0 = 10 ∧ rowTerm entries 0 1 = 500 ∧ rowTerm entries 1 1 = 100 ∧
    rowTerm entries 1 0 = 0 ∧ rowTerm entries 0 2 = 0 ∧
    clippedTerm 3 entries 0 1 = 9 := by decide

-- Padding can enlarge each axis without changing the true mass or the strict comparison.
private def rows : List Row := [⟨7, ⟨4, 1⟩, [⟨0, 99⟩]⟩]

example : ∀ p : ℕ, (∑ c ∈ range 4, ∑ i ∈ range 4, ∑ j ∈ range 4,
    clippedTerm p (entriesAt rows c) i j) < p ↔ 610 < p := by
  intro p
  rw [sum_clipped_lt_iff p (by decide : rows.length ≤ 4) (by simp [rows])]
  rfl

-- Threshold equality and the adjacent accepting threshold both use the actual strict test.
example : ¬(∑ c ∈ range 4, ∑ i ∈ range 4, ∑ j ∈ range 4,
      clippedTerm 610 (entriesAt rows c) i j) < 610 ∧
    (∑ c ∈ range 4, ∑ i ∈ range 4, ∑ j ∈ range 4,
      clippedTerm 611 (entriesAt rows c) i j) < 611 := by
  have hw : ∀ r ∈ rows, (r.first :: r.rest).length ≤ 4 := by simp [rows]
  rw [sum_clipped_lt_iff 610 (by decide : rows.length ≤ 4) hw,
    sum_clipped_lt_iff 611 (by decide : rows.length ≤ 4) hw]
  decide
