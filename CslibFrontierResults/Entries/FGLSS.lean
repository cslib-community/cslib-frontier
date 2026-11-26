/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.PCP.Approximation.IndependentSet

/-!
# Collected results: FGLSS constant-factor hardness of approximation
-/

register_result "goldreich-fglss-constant-factor-hardness" where
  title := "Independent Set and Clique are NP-hard to approximate within every constant factor"
  topic := "hardness of approximation"
  sources := [
    { paper := Goldreich2007DraftR5,
      theorem := "Exercise 9.18, constant-factor hardness claim",
      locator := "r5.pdf; PDF pages 67–68 / printed pages 449–450" },
    { paper := FeigeGoldwasserLovaszSafraSzegedy1996,
      theorem := "Section 3 (constant-factor specialization)",
      locator := "Section 3, Definitions 3.3–3.4 and pp. 276–277" }
  ]
  theorems := [
    Cslib.Complexity.GapIndependentSet_npHard,
    Cslib.Complexity.GapClique_npHard
  ]
  scope := "For every fixed real constant 0 < s < 1, GapIndependentSet s and GapClique s are \
    NP-hard under native polynomial-time many-one promise reductions (PromiseProblem.NPHard on \
    encIndependentSetInstance and encCliqueInstance: framed binary vertex/edge lists encGraph \
    paired with binary target encNat). Yes-instances have an independent set (or clique) of at \
    least k declared vertices; no-instances have none of more than s * k declared vertices. \
    Derived from NP = PCP(log n, 1) (NP_eq_PCP_log), k-fold independent verifier repetition \
    (PCPWith_one), the nonadaptive FGLSS edge-list reduction (fglssToIndependentSet), and graph \
    complementation. Adaptive PCP graph bounds for Exercise 9.18 items 1–4 and size-dependent \
    subconstant gaps (FGLSS 1996 N^c, Goldreich Theorem 10.5) are not covered. Outside-fleet \
    source check: \
    https://github.com/cslib-community/cslib-frontier/pull/7528#pullrequestreview-6013618269"
