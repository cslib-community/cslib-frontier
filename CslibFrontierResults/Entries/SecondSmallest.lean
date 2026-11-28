/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Algorithms.Lean.Query.Select.SecondMin.LowerBound

/-!
# Optimal comparison selection of the second smallest key
-/

open Cslib.Query

register_result "second-smallest-knockout-tournament" where
  title := "Schreier's tournament finds the second smallest in at most n + ⌈log₂ n⌉ − 2 comparisons"
  topic := "comparison algorithms"
  sources := [
    { paper := Schreier1932, theorem := "Preliminary remark 2, equation (1)",
      locator := "Mathesis Polska 7, p. 156. Remark 3 on p. 157 interprets the tournament \
        as selecting weights." }
  ]
  theorems := [findSecondMin_correct, findSecondMin_upperBound]
  scope := "Order-dual of the tournament for second place on distinct keys. The Lean algorithm \
    counts multiplicities and selects rank one for every decidable total preorder and n ≥ 2. \
    The comparison cap holds for every oracle."

register_result "second-smallest-exact-comparison-bound" where
  title := "The optimal worst-case second-smallest comparison count is n + ⌈log₂ n⌉ − 2"
  topic := "comparison algorithms"
  sources := [
    { paper := Kislitsyn1964, theorem := "Corollary (unnumbered)",
      locator := "End of §2, p. 562. The comparison model and order reversal are in §1, p. 557." }
  ]
  theorems := [IsSecondMinAlg.exists_le_countQueries, exists_countQueries_findSecondMin_eq]
  scope := "For every fixed list of n ≥ 2 distinct keys and every correct deterministic comparison \
    program, some linear order on the alphabet forces the lower bound. The bound is attained by \
    the knockout tournament. Programs may ask self-comparisons and query keys outside their input."
