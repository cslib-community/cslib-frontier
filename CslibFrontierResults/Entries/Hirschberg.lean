/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Algorithms.Lean.EditDistance.Hirschberg

/-! # Hirschberg reconstruction of optimal alignments and common subsequences -/

register_result "hirschberg-reconstruction" where
  title := "Hirschberg reconstruction returns an optimal alignment and a longest common subsequence"
  topic := "string algorithms"
  sources := [
    { paper := Hirschberg1975, theorem := "Algorithm C and the minimum-trace-cost variant",
      locator := "pp. 342–343, cut, reconstruction and optimality" },
    { paper := KleinbergTardos2006, theorem := "(6.19)–(6.20) and Divide-and-Conquer-Alignment",
      locator := "§6.7, pp. 287–288" }
  ]
  theorems := [
    Cslib.Algorithms.Lean.EditDistance.hirschbergAlign_spec,
    Cslib.Algorithms.Lean.EditDistance.hirschbergLCS_spec
  ]
  scope := "Finite words and natural-valued letter-specific alignment costs. The LCS constructor \
    keeps matches from an optimal insertion–deletion alignment, using decidable letter equality. \
    Both conclusions concern the optimality of the returned witnesses."
