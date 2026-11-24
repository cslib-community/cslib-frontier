/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Contract.CombinatorialAgency
import CslibFrontier.GameTheory.P2P.Generosity

/-!
# Collected results: peer-to-peer generosity and combinatorial agency
-/

namespace CslibFrontierResults.Entries.P2PIncentives

register_result "p2p-generosity-equilibria" where
  title := "Equilibria, penalties, and exclusion tradeoffs in peer-to-peer generosity models"
  topic := "game theory"
  sources := [
    { paper := BabaioffChuangFeldman2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.P2P.uniformEquilibrium_iff,
    Cslib.GameTheory.P2P.uniform_at_four_and_collapse,
    Cslib.GameTheory.P2P.uniform_stability,
    Cslib.GameTheory.P2P.unifHighRoot_strictMono,
    Cslib.GameTheory.P2P.unifHighRoot_tendsto_one,
    Cslib.GameTheory.P2P.mixture_upper_bound,
    Cslib.GameTheory.P2P.mixtureEquilibrium_iff,
    Cslib.GameTheory.P2P.fullCooperation_penalty_threshold,
    Cslib.GameTheory.P2P.exclHighRoot_equilibrium,
    Cslib.GameTheory.P2P.excl_rescues_low_generosity,
    Cslib.GameTheory.P2P.excl_can_reduce_welfare
  ]
  scope := "Formalizes the continuous-population peer-to-peer generosity and service \
    differentiation models of Babaioff, Chuang, and Feldman (NRTV Chapter 23, Section 23.3; \
    printed theorem/page locators unverified directly). Establishes the uniform-generosity \
    threshold at theta_m >= 4 with bifurcation from 1/2, local stability of the upper root, \
    strict monotonicity and convergence to 1, the mixture-law threshold 16*phi/(1+phi)^2 and \
    participation cap (1+phi)/2, Claim 23.2 full-cooperation penalty threshold p >= 1/alpha \
    over any nonnegative generosity tail distribution, and Exercise 23.2 uniform exclusion \
    tradeoffs rescuing cooperation below theta_m = 4 while reducing total welfare on \
    supercritical instances."

register_result "combinatorial-agency-pou" where
  title := "Optimal contracts, monotonicity, and Price of Unaccountability for AND/OR agency"
  topic := "game theory"
  sources := [
    { paper := BabaioffChuangFeldman2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.Contract.isPureNash_optContract,
    Cslib.GameTheory.Contract.optContract_le_of_isPureNash,
    Cslib.GameTheory.Contract.optPayment_le_of_limitedLiability,
    Cslib.GameTheory.Contract.isStrongEquilibrium_optContract,
    Cslib.GameTheory.Contract.isStrongNash_optContract,
    Cslib.GameTheory.Contract.monotonicity_firstBest,
    Cslib.GameTheory.Contract.monotonicity_agency,
    Cslib.GameTheory.Contract.andTech_skips_interior,
    Cslib.GameTheory.Contract.andTech_pou_eq,
    Cslib.GameTheory.Contract.andTech_pou_unbounded_in_n,
    Cslib.GameTheory.Contract.andTech_pou_unbounded_in_gamma,
    Cslib.GameTheory.Contract.orTech_transitions,
    Cslib.GameTheory.Contract.orTech_pou_le_two,
    Cslib.GameTheory.Contract.orTech_pou_le
  ]
  scope := "Formalizes finite combinatorial principal-agent contract design with hidden actions \
    and limited liability over arbitrary finite agent sets and Boolean technologies \
    (NRTV Chapter 23, Section 23.5; printed theorem/page locators unverified directly). Proves \
    minimal Nash-inducing contract optimality under two-outcome limited liability, coalition \
    stability in CostGame (distinguishing IsStrongEquilibrium under nonnegative costs from \
    IsStrongNash under strictly positive costs), the Monotonicity Lemma for first-best and \
    hidden-action values, slope criteria for cardinality skipping versus full stepping, the \
    exact Price of Unaccountability (1/gamma - 1)^(n - 1) + (1 - gamma/(1 - gamma)) and \
    unboundedness for noisy AND technologies, and full cardinality stepping plus the uniform \
    constant bound POU <= 2 <= 5/2 for noisy OR technologies. Excludes Read-Once #P-hardness."

end CslibFrontierResults.Entries.P2PIncentives
