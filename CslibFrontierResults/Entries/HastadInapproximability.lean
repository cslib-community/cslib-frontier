/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.PCP.Approximation.Hastad.Hardness

/-!
# Collected results: Håstad's optimal inapproximability for MAX-E3LIN-2 and MAX-E3SAT
-/

register_result "hastad-max-e3lin-2-inapproximability" where
  title := "MAX-E3LIN-2 is NP-hard to approximate beyond the random-assignment threshold 1/2 \
    (factor 2 − ε), and gapLin_{1−δ, 1/2+ε} is NP-hard"
  topic := "hardness of approximation"
  sources := [
    { paper := Hastad2001,
      theorem := "Theorem 5.4",
      locator := "Section 5, author PDF pp. 27–28 / JACM 48(4) pp. 821–822" },
    { paper := Goldreich2007DraftR5,
      theorem := "Theorem 10.9 (corrected separated range)",
      locator := "r5.pdf; PDF page 80 / printed page 462" }
  ]
  theorems := [
    Cslib.Complexity.GapExactThreeLin_npHard,
    Cslib.Complexity.GapLin_npHard_of_lt,
    Cslib.Complexity.P_eq_NP_of_maxExactThreeLin_approx
  ]
  scope := "For every 0 < δ, 0 < ε with 1/2 + ε < 1 − δ, GapExactThreeLin (1 − δ) (1/2 + ε) \
    (systems of parity equations on three distinct variables, e.scope.length = 3 ∧ e.scope.Nodup, \
    encoded by encCSP encBool encNat) and GapLin (1 − δ) (1/2 + ε) (XORSAT.System under \
    XORSAT.encoding) are NP-hard under native multi-tape polynomial-time many-one promise \
    reductions (PromiseProblem.NPHard). For every ρ > 1/2 (factor 2 − ε), any polynomial-time \
    ρ-approximation algorithm for distinct-variable MAX-E3LIN-2 returning the list of true \
    variables implies P enc = NP enc for every instance encoding enc. Proved from small-soundness \
    Label Cover (GapLabelCover_npHard_pow via Raz–Holenstein parallel repetition) and Håstad's \
    folded Long Code 3-bit test (gapLabelCover_dichotomy_lt_one), with unweighted rational noise \
    rate 1/m and degenerate repeated-variable equations dropped and absorbed by choosing the \
    repetition count k large. Goldreich's literal Theorem 10.9 omits an upper bound on ε; the \
    formalized range 1/2 + ε < 1 − δ restricts to separated thresholds. Awaits outside-fleet \
    source check on the PR."

register_result "hastad-max-e3sat-imperfect-completeness-inapproximability" where
  title := "MAX-E3SAT (imperfect completeness) is NP-hard to approximate beyond the \
    random-assignment threshold 7/8 (factor 8/7 − ε)"
  topic := "hardness of approximation"
  sources := [
    { paper := Hastad2001,
      theorem := "Theorem 6.1",
      locator := "Section 6, author PDF p. 38 / JACM 48(4) p. 831" }
  ]
  theorems := [
    Cslib.Complexity.GapMaxExactThreeSAT_npHard,
    Cslib.Complexity.P_eq_NP_of_maxExactThreeSAT_approx
  ]
  scope := "For every 0 < δ, 0 < ε with 7/8 + ε < 1 − δ, GapMaxExactThreeSAT (1 − δ) (7/8 + ε) \
    (CNF ℕ formulas with three distinct variables per clause, CNF.IsExactThreeDistinct, encoded \
    by encCNF) is NP-hard under native multi-tape polynomial-time many-one promise reductions. \
    For every ρ > 7/8 (factor 8/7 − ε), any polynomial-time ρ-approximation algorithm for \
    distinct-variable MAX-E3SAT implies P enc = NP enc for every instance encoding enc, matching \
    Johnson's 7/8-approximation (exists_polyTime_maxExactThreeSAT_approx). Proved by composing \
    GapExactThreeLin_npHard with the four-clause XOR gadget (CSP.toCNFBounded 3 CSP.paritySem). \
    Completeness is imperfect (1 − δ < 1); Håstad's Theorem 6.5 (perfect completeness 1 vs \
    7/8 + ε on satisfiable E3-CNF formulas) requires a different PCP test and is not formalized \
    here. Awaits outside-fleet source check on the PR."
