/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Complexity.Classes.AverageCase.SharpP

/-!
# Collected results: samplable ensembles that are not computable unless `#P` is easy
-/

register_result "samplable-not-computable-unless-sharp-p-easy" where
  title := "Unless #P ⊆ FP, some polynomial-time samplable ensemble is not polynomial-time \
    computable"
  topic := "average-case complexity"
  sources := [
    { paper := Goldreich2007DraftR5, theorem := "Exercise 10.26",
      locator := "r5.pdf; PDF page 120 / printed page 502" },
    { paper := AroraBarak07, theorem := "Chapter 15, Exercise 4",
      locator := "Web draft 2007-01-08, printed p. 279; PDF p. 295" }
  ]
  theorems := [
    Cslib.Complexity.Ensemble.exists_pSamp_not_pComp_of_not_SharpP_subset,
    Cslib.Complexity.Ensemble.exists_pSamp_not_pComp_of_P_ne_PWithSharpPOracle
  ]
  scope := "Ensembles are Bogdanov–Trevisan ensembles: the n-th distribution is on words of \
    length exactly n, cumulative distributions order words of a length by binary value \
    (lexicographically). Polynomial-time computable (Ensemble.PComp): the cumulative \
    distribution is an exact ratio of two polynomial-time natural-valued functions in binary, \
    which contains Goldreich's binary-fraction outputs; samplable (Ensemble.PSamp): an exact \
    strict-PPT sampler given n in unary. Goldreich's hypothesis #P ⊄ FP is stated for \
    SharpP encBits (exact-length certificates of a native polynomial-time verifier on words) \
    and binary output. Arora–Barak's hypothesis P^#P ≠ P is P enc ≠ PWithSharpPOracle enc at \
    any instance encoding; the source states the exercise for single distributions on {0,1}* \
    (Levin's model, Definition 15.12), not for ensembles."
