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
    { paper := Savage1971, theorem := "Convex-function characterization of proper scoring rules",
      locator := "JASA 66(336), pp. 783–801" },
    { paper := GneitingRaftery2007, theorem := "Theorem 1",
      locator := "JASA 102(477), §2, pp. 360–361" }
  ]
  theorems := [
    Cslib.GameTheory.PredictionMarket.isProperOn_iff_exists_savage,
    Cslib.GameTheory.PredictionMarket.isStrictlyProperOn_iff_exists_savage,
    Cslib.GameTheory.PredictionMarket.isProperOn_savageScoringRule_of_convexOn,
    Cslib.GameTheory.PredictionMarket.isStrictlyProperOn_savageScoringRule_of_strictConvexOn,
    Cslib.GameTheory.PredictionMarket.savageScoringRule_score_gap_eq_bregmanDivergence
  ]
  scope := "Finite outcome space Ω and real-valued scoring rules on any convex subset P of the \
    probability simplex probSimplex Ω. Characterization is stated in terms of (strictly) convex \
    potentials G : (Ω → ℝ) → ℝ and (strict) subgradient maps g : (Ω → ℝ) → Ω → ℝ, together with \
    differentiable sufficiency via Fréchet derivatives within P and exact Bregman divergence gap."

register_result "nrtv-canonical-strictly-proper-scoring-rules" where
  title := "Strict propriety of quadratic (Brier), logarithmic, and spherical scoring rules"
  topic := "game theory"
  sources := [
    { paper := FriedmanResnickSami2007,
      theorem := "Definition 27.1, §27.4.2, and Exercise 27.7",
      locator := "Chapter 27, §27.4.2 (pp. 685–687) and Exercise 27.7 (p. 697)" },
    { paper := Brier1950, theorem := "Quadratic (Brier) probability score",
      locator := "Monthly Weather Review 78(1), pp. 1–3" },
    { paper := GneitingRaftery2007,
      theorem := "Strict propriety of quadratic, log, and spherical scores",
      locator := "JASA 102(477), §3.1, pp. 362–363" }
  ]
  theorems := [
    Cslib.GameTheory.PredictionMarket.isStrictlyProper_quadraticScore,
    Cslib.GameTheory.PredictionMarket.isStrictlyProper_brierScore,
    Cslib.GameTheory.PredictionMarket.quadraticScore_bounds,
    Cslib.GameTheory.PredictionMarket.logScore_expectedScore_lt,
    Cslib.GameTheory.PredictionMarket.isStrictlyProperOn_logScore,
    Cslib.GameTheory.PredictionMarket.isStrictlyProper_sphericalScore
  ]
  scope := "Any finite outcome type Ω. Quadratic, Brier, and spherical scoring rules are proved \
    strictly proper on the full closed simplex probSimplex Ω, with [-1, 1] range bounds for the \
    quadratic score. The real-valued logarithmic score is proved strictly proper on \
    openProbSimplex Ω (and whenever supp(q) ⊆ supp(p)), avoiding Lean's Real.log 0 = 0 artifact."

register_result "nrtv-hanson-lmsr-market-maker" where
  title := "Hanson's LMSR: convexity, softmax gradient, MSR equivalence, and bounded loss"
  topic := "game theory"
  sources := [
    { paper := PennockSami2007, theorem := "§26.4.1 (Hanson's LMSR) and Exercise 26.3",
      locator := "Chapter 26, §26.4.1 (pp. 662–665) and Exercise 26.3 (p. 675)" },
    { paper := Hanson2003, theorem := "Sequential market scoring rule",
      locator := "Information Systems Frontiers 5(1), pp. 107–119" },
    { paper := Hanson2007, theorem := "Logarithmic market scoring rule",
      locator := "Journal of Prediction Markets 1(1), pp. 3–15" }
  ]
  theorems := [
    Cslib.GameTheory.PredictionMarket.hasFDerivAt_lmsrCost,
    Cslib.GameTheory.PredictionMarket.hasDerivAt_lmsrCost_update,
    Cslib.GameTheory.PredictionMarket.convexOn_lmsrCost,
    Cslib.GameTheory.PredictionMarket.lmsrCost_bregmanDivergence_eq,
    Cslib.GameTheory.PredictionMarket.lmsrTraderPayoff_eq_msrStepPayoff,
    Cslib.GameTheory.PredictionMarket.sum_lmsrTraderPayoff_eq_msrTotalPayoff,
    Cslib.GameTheory.PredictionMarket.exists_shares_lmsrTraderPayoff_eq_msrStepPayoff,
    Cslib.GameTheory.PredictionMarket.lmsrTraderPayoff_zero_le,
    Cslib.GameTheory.PredictionMarket.lmsrTraderPayoff_zero_seq_le,
    Cslib.GameTheory.PredictionMarket.exists_lmsrTraderPayoff_zero_gt
  ]
  scope := "Any nonempty finite outcome type Ω and liquidity parameter b > 0. Proves softmax \
    price simplex membership, exact Fréchet gradient and partial derivatives of C(q), global \
    convexity and KL-divergence Bregman identity, pointwise and sequential equivalence with \
    Hanson's scaled logarithmic market scoring rule (including realizability of any open-simplex \
    report sequence), and the sharp worst-case market-maker loss bound b * log |Ω| from zero \
    shares."
