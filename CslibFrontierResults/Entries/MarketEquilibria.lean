/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Market.Basic
import CslibFrontier.GameTheory.Market.EisenbergGale

/-!
# Collected results: Market equilibria, Walras's law, First Welfare Theorem, and Eisenberg–Gale
-/

register_result "walras-law-and-first-welfare-theorem" where
  title := "Walras's law, the First Welfare Theorem, and Fisher-to-exchange market reduction"
  topic := "algorithmic game theory"
  sources := [
    { paper := CodenottiVaradarajan2007,
      theorem := "Section 6.1.1 and Section 6.2",
      locator := "Section 6.1.1, pp. 135–137, and Section 6.2, p. 141" },
    { paper := ArrowDebreu1954,
      theorem := "Section 1 (competitive equilibrium and optimality)",
      locator := "pp. 265–270" },
    { paper := Vazirani2007,
      theorem := "Section 5.11 and Exercise 5.7",
      locator := "Section 5.11, p. 122, and Section 5.15, p. 132" }
  ]
  theorems := [
    Cslib.GameTheory.Market.ExchangeMarket.walras_law,
    Cslib.GameTheory.Market.ExchangeMarket.IsCompetitiveEquilibrium.isParetoOptimal,
    Cslib.GameTheory.Market.LinearExchangeMarket.isCompetitiveEquilibrium_iff_bangPerBuck,
    Cslib.GameTheory.Market.FisherMarket.IsEquilibrium.isParetoOptimal,
    Cslib.GameTheory.Market.FisherMarket.isEquilibrium_iff_toExchangeMarket,
    Cslib.GameTheory.Market.FisherMarket.isEquilibrium_smul_of_toExchangeMarket
  ]
  scope := "Finite trader/buyer type [Fintype I] and finite divisible-good type [Fintype G] \
    over ℝ, with nonnegative endowments or supplies/budgets and free-disposal market clearing \
    (excessDemand x g ≤ 0 with p g * excessDemand x g = 0). Under local nonsatiation on \
    nonnegative bundles (IsLocallyNonsatiated), every optimal demand profile satisfies Walras's \
    law expenditure p (excessDemand x) = 0, and every competitive equilibrium of an \
    ExchangeMarket or FisherMarket is Pareto optimal (First Welfare Theorem, without convexity \
    or continuity hypotheses). Positive-budget Fisher markets embed into ExchangeMarket by \
    budget-proportional endowment shares (toExchangeMarket), preserving equilibria up to positive \
    price rescaling (Exercise 5.7); machine-level complexity of the reduction is not modeled."

register_result "eisenberg-gale-linear-fisher-equilibria" where
  title := "Eisenberg–Gale convex program, KKT equivalence, and linear Fisher market equilibria"
  topic := "algorithmic game theory"
  sources := [
    { paper := Vazirani2007,
      theorem := "Theorem 5.1, Exercise 5.1, Section 5.2, Section 5.11, and Exercise 5.7",
      locator := "Section 5.2, Program (5.1) and Theorem 5.1, pp. 105–107; Section 5.11, p. 122; \
        and Section 5.15, p. 132" },
    { paper := EisenbergGale1959,
      theorem := "Theorems 1 and 2, and Corollaries 1 and 2",
      locator := "pp. 165–168" }
  ]
  theorems := [
    Cslib.GameTheory.Market.LinearFisherMarket.isEquilibrium_iff_bangPerBuck,
    Cslib.GameTheory.Market.LinearFisherMarket.isEquilibrium_iff_isEisenbergGaleKKT,
    Cslib.GameTheory.Market.LinearFisherMarket.IsEisenbergGaleKKT.eisenbergGaleObjective_le,
    Cslib.GameTheory.Market.LinearFisherMarket.isEquilibrium_iff_isMaxOn_eisenbergGaleObjective,
    Cslib.GameTheory.Market.LinearFisherMarket.IsNonDegenerate.exists_isEquilibrium,
    Cslib.GameTheory.Market.LinearFisherMarket.convex_setOf_exists_isEquilibrium,
    Cslib.GameTheory.Market.LinearFisherMarket.buyerUtility_eq_of_isEquilibrium,
    Cslib.GameTheory.Market.LinearFisherMarket.price_eq_of_isEquilibrium,
    Cslib.GameTheory.Market.LinearFisherMarket.isEquilibrium_iff_toLinearExchangeMarket,
    Cslib.GameTheory.Market.LinearFisherMarket.isEquilibrium_smul_of_toLinearExchangeMarket
  ]
  scope := "Finite buyer type [Fintype I] and finite divisible-good type [Fintype G] over ℝ in \
    LinearFisherMarket (general nonnegative supplies supply : G → ℝ, with unitSupply for \
    supply g = 1). Under IsNonDegenerate (positive budgets and supplies, every buyer desires at \
    least one good, and every good is desired by at least one buyer), proves the three-way \
    equivalence between market equilibria, maximum bang-per-buck / Eisenberg–Gale KKT conditions \
    (IsEisenbergGaleKKT), and maximizers of ∑_i budget_i * log(buyerUtility_i) over \
    IsPositiveUtilityAllocation (with explicit dual prices eisenbergGaleDualPrice), together \
    with Theorem 5.1 parts 1–3: equilibrium existence, convexity of equilibrium allocations, and \
    uniqueness of equilibrium utilities and prices. Polynomial-bit rationality of rational \
    instances (Theorem 5.1 part 4, proved in Vazirani Section 5.9–5.10 via DPSV / Lemma 5.20) \
    remains open under #7789."
