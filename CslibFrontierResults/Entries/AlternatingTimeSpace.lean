/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Complexity.Classes.Alternation.DeterministicSpace

/-!
# Collected results: alternating time within deterministic space
-/

register_result "alternation-atime-dspace" where
  title := "Chandra-Kozen-Stockmeyer: alternating time t is within deterministic space n + t \
    (and space t for t(n) >= n)"
  topic := "space complexity"
  sources := [
    { paper := ChandraKozenStockmeyer1981,
      theorem := "Theorem 3.2",
      locator := "Section 3, printed pp. 122-123 (PDF pp. 9-10)" },
    { paper := Sipser2013,
      theorem := unverified,
      locator := "Section 10.3" }
  ]
  theorems := [
    Cslib.Complexity.ATIME_subset_DSPACE,
    Cslib.Complexity.ATIME_subset_DSPACE_of_le
  ]
  scope := "One finite-state binary-alphabet alternating multi-tape machine per problem \
    (Turing.MultiTapeATM, two transition choices per live step, no negating states) with \
    least-fixed-point acceptance and every computation path halting within c_1 * t(n) + c_2 \
    steps on encoded instances of length n (MultiTapeATM.DecidesInTime); DSPACE is deterministic \
    halting decision (MultiTapeTM.DecidableInTimeAndSpace) within work-tape space \
    c_1 * (n + t(n)) + c_2 unconditionally (ATIME_subset_DSPACE), or c_1 * t(n) + c_2 when \
    n <= t(n) for all n (ATIME_subset_DSPACE_of_le), for arbitrary injective encodings \
    enc : alpha -> List Bool and with no constructibility hypothesis on t. Chandra, Kozen and \
    Stockmeyer (Definition 2.5, p. 120, and Theorem 3.2, pp. 122-123) define ATIME(T(n)) and \
    DSPACE(T(n)) over arbitrary finite alphabets via recognizers (removing constructibility by \
    iterating T = 1, 2, ...); here every branch of an ATIME decider halts within c_1 * t(n) + c_2 \
    moves, so the depth-first single-bit game evaluator \
    (Turing.MultiTapeATM.computableInSpace_gameValue) halts on all inputs without computing t. \
    The sublinear random-access relaxation t(n) >= log n (pp. 123-124) and the converse inclusion \
    NSPACE(s) <= ATIME(s^2) (Theorem 3.1) are not included."
