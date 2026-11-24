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
  topic := "game theory"
  sources := [
    { paper := CodenottiVaradarajan2007,
      theorem := "Section 6.1.1, Section 6.1.7, and Section 6.2",
      locator := "Section 6.1.1, pp. 136–137; Section 6.1.7, p. 140; Section 6.2, p. 141" },
    { paper := ArrowDebreu1954,
      theorem := unverified,
      locator := unverified }
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
    law expenditure p (excessDemand x) = 0 (CodenottiVaradarajan2007, §6.1.1, p. 137), and every \
    competitive equilibrium of an ExchangeMarket or FisherMarket is Pareto optimal (First Welfare \
    Theorem, without convexity or continuity hypotheses). Positive-budget Fisher markets embed \
    into ExchangeMarket by budget-proportional endowment shares (toExchangeMarket; \
    CodenottiVaradarajan2007, §6.1.7, p. 140), preserving equilibria up to positive price \
    rescaling; machine-level complexity of the reduction is not modeled."

register_result "eisenberg-gale-linear-fisher-equilibria" where
  title := "Eisenberg–Gale convex program, KKT equivalence, and linear Fisher market equilibria"
  topic := "game theory"
  sources := [
    { paper := Vazirani2007,
      theorem := "Section 5.2, Program (5.1), and Theorem 5.1",
      locator := "Section 5.2, pp. 105–107 \
        (KKT conditions (i)–(iv) on p. 106; Theorem 5.1, p. 107)" },
    { paper := CodenottiVaradarajan2007,
      theorem := "Section 6.1.7 (proportional-endowment Fisher-to-exchange embedding)",
      locator := "Section 6.1.7, p. 140" },
    { paper := EisenbergGale1959,
      theorem := unverified,
      locator := unverified }
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
    (IsEisenbergGaleKKT; Vazirani2007, §5.2, p. 106), and maximizers of \
    ∑_i budget_i * log(buyerUtility_i) over IsPositiveUtilityAllocation (with explicit dual \
    prices eisenbergGaleDualPrice), together with Theorem 5.1 parts 1–3 (p. 107): equilibrium \
    existence, convexity of equilibrium allocations, and uniqueness of equilibrium utilities and \
    prices, plus the proportional-endowment embedding toLinearExchangeMarket \
    (CodenottiVaradarajan2007, §6.1.7, p. 140). Polynomial-bit rationality of rational instances \
    (Theorem 5.1 part 4, proved in Vazirani Section 5.9–5.10 via DPSV / Lemma 5.20) remains open \
    under #7789."
