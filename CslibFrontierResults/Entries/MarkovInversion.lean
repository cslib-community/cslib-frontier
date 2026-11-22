/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Circuit.Boolean.Inversion.Markov

register_result "markov-inversion-complexity" where
  title := "The minimum number of NOT gates for a Boolean system is ⌈log₂ (d + 1)⌉"
  topic := "circuit complexity"
  sources := [
    { paper := Markov1963,
      theorem := "Theorem 4.1",
      locator := "Doklady Akademii Nauk SSSR 150(3), printed p. 478; decrease defined in §3, \
        pp. 477–478; proof in §5, Lemmas 5.1–5.2, pp. 478–479" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.exists_computes_negationCost_le_iff,
    Cslib.Circuits.Boolean.ecomplexityFrom_negationCost_eq_clog,
    Cslib.Circuits.Boolean.exists_computes_negationCost_eq_clog
  ]
  scope := "For every finite n and m and every target : BitString n → BitString m, the native \
    acyclic AND/OR/NOT/constant circuit model with shared gates has a circuit of NOT cost at \
    most k iff decrease target < 2^k. Its existing ecomplexityFrom with identity sources and \
    negationCost equals Nat.clog 2 (decrease target + 1), and the bound is attained. AND, OR \
    and constants have cost zero. The lower argument counts shared NOT gates once; the upper \
    argument constructs circuits by halving the canonical chain-decrease rank. The source's \
    arbitrary free monotone gates are realized by native monotone formulas. A decrease is a \
    transition at which some output changes true to false, and the maximum is formally \
    attained on a nonempty strictly increasing input chain, matching §3. The formal theorem \
    additionally includes zero inputs and zero outputs. No randomness or extra hypotheses \
    occur. Proposed registration: outside-fleet source review is pending and is a merge gate; \
    no independent approval is claimed by this entry."
