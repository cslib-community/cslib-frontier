/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Complexity.FineGrained.SatisfiabilityHypothesis
import CslibFrontier.Computability.Complexity.FineGrained.SharpSatisfiabilityHypothesis
import CslibFrontier.Computability.Complexity.FineGrained.SharpTwoSATPower

/-!
# Collected results: the Satisfiability Hypothesis
-/

register_result "sh-fixed-width-size" where
  title := "The decision Satisfiability Hypothesis in terms of fixed-width formula size"
  topic := "fine-grained complexity"
  sources := [
    { paper := MITHardnessGroup2026SH,
      theorem := "Lemma 2.1 (decision case)",
      locator := "arXiv:2611.02650v2, §2.1, p. 5" }
  ]
  theorems := [Cslib.Complexity.SH_iff_KSAT]
  scope := "On CNF ℕ with native binary labels (encCNF), unrestricted SAT has exponent measure \
    (occurring variables + clauses + literal occurrences), with polynomial overhead in encoded \
    input length. For each fixed k ≥ 3, SH is equivalent to the lack of a deterministic \
    multitape k-SAT solver with a fixed power saving in the exponent measured in occurring \
    variables plus clauses, with the same kind of polynomial overhead."

register_result "sharp-sh-fixed-width-size" where
  title := "The counting Satisfiability Hypothesis in terms of fixed-width formula size"
  topic := "fine-grained complexity"
  sources := [
    { paper := MITHardnessGroup2026SH,
      theorem := "Lemma 2.1 (counting case)",
      locator := "arXiv:2611.02650v2, §2.1, p. 5" }
  ]
  theorems := [Cslib.Complexity.SharpSH_iff_SharpKSAT]
  scope := "With native binary CNF inputs (encCNF) and binary outputs (encNat), exact counts \
    range over occurring variables. The unrestricted exponent measures occurring variables, \
    clauses, and literal occurrences. For each fixed k ≥ 3, the equivalent fixed-width \
    exponent measures occurring variables plus clauses. The deterministic multitape bounds \
    allow polynomial overhead in encoded input length, and the width-guarded counter returns \
    zero on inputs outside the width bound."

register_result "sharp-sh-iff-weak-sharp-eth" where
  title := "The counting Satisfiability Hypothesis is equivalent to Weak #ETH"
  topic := "fine-grained complexity"
  sources := [
    { paper := MITHardnessGroup2026SH,
      theorem := "Theorem 2.4 (counting case)",
      locator := "arXiv:2611.02650v2, §2.3, p. 7" }
  ]
  theorems := [Cslib.Complexity.SharpSH_iff_WeakSharpETH]
  scope := "With native binary CNF input (encCNF) and binary counts (encNat), #SH measures \
    occurring variables, clauses, and literal occurrences of unrestricted formulas. Weak #ETH \
    measures occurring variables of width-at-most-three formulas. Both rule out fixed power \
    savings for deterministic multitape counters with polynomial overhead in the encoded \
    input length. The width-three counter returns zero on wider formulas."

register_result "sh-implies-sharp-sh" where
  title := "The Satisfiability Hypothesis implies its counting counterpart"
  topic := "fine-grained complexity"
  sources := [
    { paper := MITHardnessGroup2026SH,
      theorem := "Decision-to-counting implication",
      locator := "arXiv:2611.02650v2, §2, p. 5" }
  ]
  theorems := [Cslib.Complexity.SH.sharpSH]
  scope := "For deterministic multitape machines on native binary CNF inputs (encCNF), \
    a positive binary model count (encNat) decides satisfiability. Both hypotheses measure \
    occurring variables plus clauses plus literal occurrences and allow polynomial overhead in \
    the encoded input length. The polynomial bit-length bound for the count lets the positivity \
    test preserve the exponent power."

register_result "sh-exponent-transfer" where
  title := "Exponent transfer under the Satisfiability Hypothesis"
  topic := "fine-grained complexity"
  sources := [
    { paper := MITHardnessGroup2026SH,
      theorem := "Theorem 3.1",
      locator := "arXiv:2611.02650v2, §3, p. 8" }
  ]
  theorems := [Cslib.Complexity.SH.not_decidableInPowerExpTime_of_reduction]
  scope := "Under SH, a deterministic multitape many-one reduction from ThreeSAT, with source \
    size s = occurring variables + clauses, time 2 ^ O((s + 1) ^ q) times a polynomial in the \
    source encoding length, and target parameter N = O((s + 1) ^ (b + η)) for every η > 0, \
    rules out a deterministic target solver in 2 ^ O((N + 1) ^ p) times a polynomial in the \
    target encoding length whenever b > 0, p > 0 and b * p < 1. The hypothesis q < 1 allows \
    q = 0 for polynomial-time reductions. The reduction's time bounds the length it writes."

register_result "sharp-sh-three-occurrence-sharp-two-sat" where
  title := "The counting Satisfiability Hypothesis gives a bounded-degree #2SAT lower bound"
  topic := "fine-grained complexity"
  sources := [
    { paper := MITHardnessGroup2026SH,
      theorem := "Corollary 6.1",
      locator := "arXiv:2611.02650v2, §6, p. 10" }
  ]
  theorems := [Cslib.Complexity.SharpSH.not_computableInPowerExpTime_sharpTwoSAT_threeOccurrence]
  scope := "Under #SH, for every fixed 0 < p < 1 a deterministic multitape machine cannot count \
    satisfying assignments in time 2 ^ O((n + m + 1) ^ p) times a polynomial in the encoded input \
    length, where n counts occurring variables and m counts clauses. The promise requires width \
    at most two and at most three literal occurrences per variable. Only promised inputs require \
    correct binary counts (encNat) within the time bound. The subtype encoding sends only the \
    ordinary binary CNF word (encCNF)."
