/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.PredictionMarket.ScoringRules
import CslibFrontier.GameTheory.PredictionMarket.LMSR

/-!
# Collected results: proper scoring rules and Hanson's LMSR
-/

register_result "savage-proper-scoring-rule-characterization" where
  title := "Savage / Gneiting–Raftery characterization of proper and strictly proper scoring rules"
  topic := "game theory"
  sources := [
    { paper := Savage1971, theorem := unverified, locator := unverified },
    { paper := GneitingRaftery2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.PredictionMarket.isProperOn_iff_exists_savage,
    Cslib.GameTheory.PredictionMarket.isStrictlyProperOn_iff_exists_savage,
    Cslib.GameTheory.PredictionMarket.isProperOn_savageScoringRule_of_convexOn,
    Cslib.GameTheory.PredictionMarket.isStrictlyProperOn_savageScoringRule_of_strictConvexOn,
    Cslib.GameTheory.PredictionMarket.savageScoringRule_score_gap_eq_bregmanDivergence
  ]
  scope := "Finite outcome space Ω and real-valued scoring rules on any convex subset P of the \
    probability simplex probSimplex Ω (where real-valued finiteness on P discharges \
    Gneiting–Raftery's regularity condition). Characterization is stated in terms of (strictly) \
    convex potentials G : (Ω → ℝ) → ℝ and (strict) subgradient maps g : (Ω → ℝ) → ℝ, together \
    with differentiable sufficiency via Fréchet derivatives within P and exact Bregman \
    divergence gap."

register_result "nrtv-quadratic-scoring-rule" where
  title := "Strict propriety and sharp range bounds of the quadratic (Brier) scoring rule"
  topic := "game theory"
  sources := [
    { paper := FriedmanResnickSami2007,
      theorem := "Exercise 27.7",
      locator := "Chapter 27, p. 697 (see also §27.4.2, pp. 686–687)" },
    { paper := Brier1950, theorem := unverified, locator := unverified },
    { paper := GneitingRaftery2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.PredictionMarket.isStrictlyProper_quadraticScore,
    Cslib.GameTheory.PredictionMarket.isStrictlyProper_brierScore,
    Cslib.GameTheory.PredictionMarket.quadraticScore_bounds
  ]
  scope := "Any finite outcome type Ω on the full closed simplex probSimplex Ω. Exercise 27.7 \
    states the 2-event affine form a + b * quadraticScore without writing b > 0; here \
    quadraticScore and brierScore are proved strictly proper on arbitrary finite Ω with [-1, 1] \
    range bounds (giving [a - b, a + b] and strict propriety for b > 0 via \
    ScoringRule.IsStrictlyProperOn.affine)."

register_result "nrtv-logarithmic-scoring-rule" where
  title := "Strict propriety of the logarithmic scoring rule"
  topic := "game theory"
  sources := [
    { paper := FriedmanResnickSami2007,
      theorem := "Section 27.4.2 (strict propriety of the logarithmic scoring rule)",
      locator := "Chapter 27, §27.4.2, pp. 686–687" },
    { paper := GneitingRaftery2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.PredictionMarket.logScore_expectedScore_lt,
    Cslib.GameTheory.PredictionMarket.isStrictlyProperOn_logScore
  ]
  scope := "Any finite outcome type Ω. Because Lean's real logarithm maps 0 ↦ 0, the real-valued \
    logarithmic score is proved strictly proper on openProbSimplex Ω (and whenever \
    supp(q) ⊆ supp(p) on probSimplex Ω)."

register_result "gneiting-raftery-spherical-scoring-rule" where
  title := "Strict propriety of the spherical scoring rule"
  topic := "game theory"
  sources := [
    { paper := GneitingRaftery2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.PredictionMarket.isStrictlyProper_sphericalScore
  ]
  scope := "Any finite outcome type Ω on the full closed simplex probSimplex Ω."

register_result "nrtv-hanson-lmsr-market-maker" where
  title := "Hanson's LMSR: softmax gradient, MSR equivalence, and bounded worst-case loss"
  topic := "game theory"
  sources := [
    { paper := PennockSami2007,
      theorem := "Section 26.4.1 (Hanson's LMSR)",
      locator := "Chapter 26, §26.4.1, pp. 663–664" },
    { paper := Hanson2003, theorem := unverified, locator := unverified },
    { paper := Hanson2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.PredictionMarket.hasFDerivAt_lmsrCost,
    Cslib.GameTheory.PredictionMarket.hasDerivAt_lmsrCost_update,
    Cslib.GameTheory.PredictionMarket.lmsrTraderPayoff_eq_msrStepPayoff,
    Cslib.GameTheory.PredictionMarket.sum_lmsrTraderPayoff_eq_msrTotalPayoff,
    Cslib.GameTheory.PredictionMarket.exists_shares_lmsrTraderPayoff_eq_msrStepPayoff,
    Cslib.GameTheory.PredictionMarket.lmsrTraderPayoff_zero_le,
    Cslib.GameTheory.PredictionMarket.lmsrTraderPayoff_zero_seq_le,
    Cslib.GameTheory.PredictionMarket.exists_lmsrTraderPayoff_zero_gt
  ]
  scope := "Any nonempty finite outcome type Ω and liquidity parameter b > 0. Proves exact \
    Fréchet gradient and coordinate partial derivatives of C(q) = b * log (∑ exp (q ω / b)) \
    giving softmax prices, pointwise and sequential equivalence with Hanson's scaled logarithmic \
    market scoring rule (including realizability of any open-simplex report sequence), and the \
    sharp worst-case market-maker loss bound b * log |Ω| starting from zero shares."
