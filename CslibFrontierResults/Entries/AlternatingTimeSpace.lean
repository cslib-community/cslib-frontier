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
  title := "Chandra-Kozen-Stockmeyer: alternating time t is within deterministic space t for \
    t(n) >= n (from the library's ATIME(t) <= DSPACE(n + t) bound)"
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
    c_1 * s(n) + c_2, for arbitrary injective encodings enc : alpha -> List Bool and with no \
    constructibility hypothesis on t. ATIME_subset_DSPACE_of_le proves ATIME(t) <= DSPACE(t) \
    under n <= t(n) for all n, mapping to Chandra, Kozen and Stockmeyer Theorem 3.2 (T(n) >= n, \
    printed pp. 122-123) in the library's binary halting-decider model; ATIME_subset_DSPACE \
    proves ATIME(t) <= DSPACE(n + t) as the library's formulation for arbitrary t, where the n \
    term pays for copying the encoded input during sequential coin replay. Chandra, Kozen and \
    Stockmeyer (Definition 2.5, p. 120, and Theorem 3.2, pp. 122-123) define ATIME(T(n)) and \
    DSPACE(T(n)) over arbitrary finite alphabets via least-fixed-point recognizers whose proof \
    removes constructibility by trying depths T = 1, 2, ... (which can keep trying larger depths \
    on rejected inputs); here every branch of an ATIME decider halts within c_1 * t(n) + c_2 \
    moves, so Turing.MultiTapeATM.computableInSpace_gameValue halts on all inputs without \
    computing t. Their remark on printed pp. 123-124 notes that equipping alternating machines \
    with random-access input indexing suffices in their proof to avoid storing the entire input \
    in each reconstructed configuration and relax T(n) >= n to T(n) >= log n (without proving \
    random access is necessary); that random-access variant and Theorem 3.1 \
    (NSPACE(s) <= ATIME(s^2)) are not included. Outside-fleet source check: \
    https://github.com/cslib-community/cslib-frontier/pull/7746#pullrequestreview-6016192018"
