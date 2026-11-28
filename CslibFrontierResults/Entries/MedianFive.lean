/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Algorithms.Lean.Query.Select.MedianFive

/-!
# Median selection in six comparisons
-/

register_result "median-of-five-six-comparisons" where
  title := "Six comparisons suffice to select the median of five"
  topic := "comparison selection"
  sources := [
    { paper := RuzickaWiedermann1979, theorem := "Fig. 3",
      locator := "§2, p. 322, case 2b on p. 323 and Figure 3 on p. 324." }
  ]
  theorems := [Cslib.Query.eval_medianFive, Cslib.Query.medianFive_countQueries]
  scope := "The source selects the third largest of five distinct inputs. Lean's decision tree \
    returns the third occurrence in stable sorted order under any total preorder, breaking ties by \
    input position. Every Boolean comparison oracle induces exactly six queries. The result gives \
    the constructive upper bound. Worst-case optimality and average-case comparisons are separate."
