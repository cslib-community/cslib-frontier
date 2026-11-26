/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Probability.HashFamily.PolynomialBirthday

/-!
# Collected results: polynomial hashing
-/

register_result "polynomial-hash-birthday-lower-bound" where
  title := "Two-block polynomial hashing has constant collision probability at the birthday scale"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 7.26(a)",
      locator := "v0.6, printed p. 284; equation (7.3), printed p. 255; \
        Remark 7.2, printed p. 263" }
  ]
  theorems := [Cslib.Probability.one_eighth_le_polyHash_twoBlock_collision]
  scope := "For any fixed key, floor(sqrt(card F)) independent uniform two-block messages \
    contain two distinct messages with equal digests with probability at least 1/8 once \
    card F ≥ 16. Following Remark 7.2, messages range over F × F and are passed as two-block \
    lists to the variable-length hash of equation (7.3). The result covers finite semirings, \
    including the prime field of the exercise."
