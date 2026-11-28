/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Complexity.Problems.Permanent.XorGadget

/-! # The weighted XOR gadget for the permanent -/

register_result "permanent-xor-gadget" where
  title := "Valiant's XOR gadget for weighted cycle covers"
  topic := "counting complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 9, Exercise 3",
      locator := "Web draft 2007-01-08, printed p. 185 (PDF p. 201), Figure 9.3 on p. 177" }
  ]
  theorems := [
    Cslib.Complexity.XorGadget.sum_lift,
    Cslib.Complexity.XorGadget.disjoint_lift,
    Cslib.Complexity.XorGadget.sum_filter_notMem_lift,
    Cslib.Complexity.XorGadget.permanent_replace
  ]
  scope := "For two distinct directed edges of a finite weighted graph over a commutative ring, \
    the lifted covers of each cycle cover that uses exactly one edge have four times its total \
    weight. Different covers have disjoint lifts, and all remaining covers have total weight \
    zero. The incoming gadget edges carry the replaced weights, recovering Figure 9.3 when \
    both are one."
