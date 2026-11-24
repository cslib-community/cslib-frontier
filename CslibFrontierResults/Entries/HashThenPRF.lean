/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Crypto.Computational.PseudorandomFunction.HashThenPRF

/-!
# Collected results: hash-then-PRF composition
-/

register_result "hash-then-prf-computational-security" where
  title := "Hash-then-PRF composition from a computational universal hash"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 7.7",
      locator := "v0.6, Section 7.3, printed pp. 262–265; equations (7.18)–(7.22)" }
  ]
  theorems := [
    Cslib.Crypto.PRF.hashThenPRFWord_indistinguishable,
    Cslib.Crypto.PRF.computableInPolyTime_hashThenPRFWord,
    Cslib.Crypto.PRF.advantage_hashThenPRFWord_le_add_multiQuery,
    Cslib.Crypto.PRF.advantage_hashThenPRFWord_le_add_collision
  ]
  scope := "Uniform strict oracle-PPT word adversaries. The hash and PRF keys are sampled \
    independently at fixed widths computable from the unary security parameter. The message \
    domain has a polynomial-time validity test and maps to the fixed-width input of the PRF. \
    The ideal function consistently samples independent replies on valid messages. Repetitions \
    are allowed, and malformed messages receive empty replies in both games. The explicit \
    wrappers have strict PPT certificates and the single-pair bound uses bounded fair-bit \
    rejection sampling."
