/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Market.Basic
import CslibFrontier.GameTheory.Market.ConvexExchange
import CslibFrontier.GameTheory.Market.EisenbergGale
import CslibFrontier.GameTheory.Market.HomogeneousFisher
import CslibFrontier.GameTheory.Market.Leontief

/-!
# Collected results: Market equilibria, Walras's law, First Welfare Theorem, and convex programs
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
    (Theorem 5.1 part 4) is formalized in BalancedFlow.lean \
    (entry fisher-rational-equilibria-polynomial-bit), and the full DPSV primal-dual algorithm \
    (Theorem 5.22) is formalized in DPSVAlgorithm.lean (entry fisher-dpsv-main-algorithm)."

open Cslib.GameTheory.Market in
register_result "eisenberg-homogeneous-fisher-program" where
  title := "Eisenberg's convex program for Fisher markets with homogeneous consumers"
  topic := "game theory"
  sources := [
    { paper := CodenottiVaradarajan2007,
      theorem := "Section 6.2 (Equations (6.2)–(6.4) and equilibrium characterization)",
      locator := "Section 6.1.5, p. 139; Section 6.2, pp. 141–142" }
  ]
  theorems := [
    IsHomogeneousDegOne.fderivWithin_self_eq,
    IsHomogeneousDegOne.sum_partial_mul_eq,
    FisherMarket.IsEisenbergKKT.isEquilibrium,
    FisherMarket.IsEisenbergKKT.exists_isEquilibrium_exactClearing,
    FisherMarket.exists_isEisenbergKKT_of_isMaxOn,
    FisherMarket.exists_isEquilibrium_of_isMaxOn_eisenbergObjective,
    FisherMarket.exists_isEquilibrium_exactClearing_of_isMaxOn_eisenbergObjective,
    FisherMarket.IsEquilibrium.isMaxOn_eisenbergObjective,
    FisherMarket.exists_isEquilibrium_iff_isMaxOn_eisenbergObjective,
    cesFisherMarket_exists_isEquilibrium_of_isMaxOn
  ]
  scope := "Finite buyer type [Fintype I] and finite divisible-good type [Fintype G] over ℝ in \
    FisherMarket with positive buyer budgets and concave, positively homogeneous-of-degree-1 \
    utilities on ℝ_+^G. Proves Euler's identity on ℝ_+^G, unconditional existence of nonnegative \
    KKT multipliers satisfying Equations (6.2)–(6.4) (p. 141) from any Eisenberg maximizer where \
    each utility is differentiable within ℝ_+^G (via Farkas' lemma on the polyhedral active cone, \
    without assuming KKT multipliers as a hypothesis), exact budget exhaustion, free-disposal and \
    (under designated-buyer monotonicity) exact-clearing equilibrium characterization, the full \
    converse without concavity/differentiability, and automatic interiority and equilibrium \
    recovery for CES Fisher markets (α > 0, ρ < 1, ρ ≠ 0). Polynomial-time \
    ellipsoid/interior-point computation of an approximate maximizer is not modeled."

open Cslib.GameTheory.Market in
register_result "convex-programs-exchange-markets" where
  title := "Convex programs for linear and CES exchange economies and disconnected CES equilibria"
  topic := "game theory"
  sources := [
    { paper := CodenottiVaradarajan2007,
      theorem := "Section 6.4.1, Section 6.4.2 (Equation (6.7) and Proposition 6.11), \
        and Section 6.5.1",
      locator := "Section 6.4.1, p. 149; Section 6.4.2, pp. 149–150 \
        (Proposition 6.11, Equations (6.7)–(6.9)); Section 6.5.1, p. 151" }
  ]
  theorems := [
    LinearExchangeMarket.isConvexProgramFeasible_iff_isCompetitiveEquilibrium,
    LinearExchangeMarket.convex_setOf_isConvexProgramFeasible,
    demandSet_cesUtility_eq,
    convexOn_cesTransformedDemand,
    CESExchangeMarket.isWalrasianEquilibrium_sq_iff,
    CESExchangeMarket.convex_setOf_transformedEquilibrium,
    gjerstadMarket_isWalrasianEquilibrium_half,
    gjerstadMarket_exists_disconnected_equilibria
  ]
  scope := "Finite trader and divisible-good types over ℝ. (1) Section 6.4.1 (p. 149; \
    Nenakov–Primak 1983, Jain 2004): exact two-way equivalence between feasible points (ψ, x) of \
    the logarithmic-price feasibility program and positive-price competitive equilibria \
    (x, exp ∘ ψ) of a LinearExchangeMarket when every trader desires at least one good, together \
    with convexity of the feasible set. (2) Section 6.4.2 (pp. 149–150): strict uniqueness of \
    closed-form CES demand (6.7) for α > 0, ρ < 1, ρ ≠ 0; Proposition 6.11 convexity of \
    f_{ij}(σ) = σ_j x_{ij}(σ^2) on ℝ_{++}^G for -1 ≤ ρ_i < 0 via Equations (6.8)–(6.9); and \
    convexity of the transformed equilibrium price set. (3) Section 6.5.1 (p. 151; Gjerstad \
    1996): for every ρ < -1 and small a > 0 (a^{-ρ/(1-ρ)} < (-ρ-1)/(1-ρ)), the 2-trader 2-good \
    CES economy admits disconnected normalized equilibria (1/2, 1/2), (p, 1-p), and (1-p, p) \
    with unique p ∈ (0, 1/2). Algorithmic ellipsoid rounding is outside this entry."

open Cslib.GameTheory.Market in
register_result "bimatrix-to-leontief-exchange-correspondence" where
  title := "One-to-one correspondence between bimatrix Nash equilibria and Leontief market prices"
  topic := "game theory"
  sources := [
    { paper := CodenottiVaradarajan2007,
      theorem := "Section 6.5.2 (bimatrix-to-Leontief exchange economy correspondence)",
      locator := "Section 6.1.5, p. 139; Section 6.5.2, p. 152" }
  ]
  theorems := [
    bimatrixLeontiefMarket_isNash_of_equilibriumPrice,
    bimatrixLeontiefMarket_existsUnique_equilibriumPrice_of_isNash
  ]
  scope := "Finite strategy sets [Fintype M] [Fintype N] [Nonempty M] [Nonempty N] over ℝ. For \
    any bimatrix game G = (A, B) with strictly positive payoff matrices A, B > 0, constructs the \
    (M ⊕ N)-trader, (M ⊕ N)-good bipartite Leontief exchange economy bimatrixLeontiefMarket G hA \
    hB (unit self-endowments, proportions B and Aᵀ) and proves the exact bijection \
    (packaged as Equiv in bimatrixLeontiefNashEquivEquilibriumPrice) between mixed Nash \
    equilibria (x, y) of G and normalized nonnegative-price competitive equilibrium prices \
    (∑ π = 1) of the Leontief economy, including boundary equilibria with zero prices. \
    PPAD-completeness reductions are outside this entry."
