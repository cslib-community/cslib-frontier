/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.SaksZhou.DecisionSpace

/-! # The logarithmic-space instance of Saks and Zhou's deterministic simulation -/

register_result "saks-zhou-halting-bpl-dspace" where
  title := "Halting BPL is contained in deterministic space O(log n · √log n)"
  topic := "space complexity"
  sources := [
    { paper := SaksZhou1999, theorem := "Theorem 1.1, specialized to logarithmic space",
      locator := "Section 1, pp. 377–378, JCSS 58 (1999)" }
  ]
  theorems := [Cslib.Complexity.BPL_subset_DSPACE_log2_mul_sqrt]
  scope := "A fair-coin multitape machine with a read-only input, bounded two-sided error \
    and halting on every branch is simulated deterministically on the same encoded language. \
    The workspace bound is the product of the binary logarithm and its integer square root, \
    up to multiplicative and additive constants."
