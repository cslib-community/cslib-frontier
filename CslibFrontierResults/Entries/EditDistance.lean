/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Algorithms.Lean.EditDistance.Unit

/-! # Collected results on edit distance -/

register_result "unit-edit-distance-sequential" where
  title := "Levenshtein distance is the minimum number of sequential single-letter edits"
  topic := "string algorithms"
  sources := [
    { paper := WagnerFischer1974, theorem := "Theorem 1",
      locator := "§3, p. 171, following properties (P1) and (P2) on pp. 169–170; \
        edit sequences and the metric criterion in §2, p. 169" }
  ]
  theorems := [
    Cslib.Algorithms.Lean.EditDistance.isLeast_editDist_unit,
    Cslib.Algorithms.Lean.EditDistance.editDist_unit_comm,
    Cslib.Algorithms.Lean.EditDistance.editDist_unit_triangle,
    Cslib.Algorithms.Lean.EditDistance.editDist_unit_eq_zero_iff
  ]
  scope := "Unit-cost specialization to finite words over an alphabet with decidable equality. \
    Insertions, deletions and changes to a different letter cost one and can be performed \
    anywhere in each successive word. A free aligned match contributes zero steps."
