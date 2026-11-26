/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Complexity.FineGrained.SatisfiabilityHypothesis
import CslibFrontier.Computability.Complexity.FineGrained.SharpSatisfiabilityHypothesis

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
