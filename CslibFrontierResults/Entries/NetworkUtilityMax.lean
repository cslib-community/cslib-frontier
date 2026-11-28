/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.ResourceAllocation.NetworkUtilityMax

/-!
# Collected results: Network Utility Maximization, Dual Control & Wireless Max-Weight (NRTV §22.1)

Registers the headline theorems of Section 22.1 of Nisan–Roughgarden–Tardos–Vazirani
([OzdaglarSrikant2007], Chapter 22, pp. 572–578) and Kelly ([Kelly1997]) formalized in
`CslibFrontier.GameTheory.ResourceAllocation.NetworkUtilityMax`.
-/

section
open Cslib.GameTheory

register_result "nrtv-num-kkt-shadow-price-decentralization" where
  title := "Multi-link Network Utility Maximization KKT characterization, existence, uniqueness, \
    and shadow-price decentralization"
  topic := "algorithmic game theory"
  sources := [
    { paper := OzdaglarSrikant2007,
      theorem := "Eqs. (22.1)–(22.7) (KKT optimality and shadow-price decentralization)",
      locator := "Chapter 22, §22.1, pp. 572–574" },
    { paper := Kelly1997,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    NetworkUtilityModel.sum_routePrice_mul_eq_sum_price_mul_linkLoad,
    NetworkUtilityModel.isSocialOptimum_of_priceTaking,
    NetworkUtilityModel.IsKKT.priceTaking_optimal,
    NetworkUtilityModel.isSocialOptimum_iff_exists_isKKT,
    NetworkUtilityModel.exists_isKKT,
    NetworkUtilityModel.IsSocialOptimum.eq_of_strictConcaveOn,
    NetworkUtilityModel.IsKKT.price_eq_of_injective_routePrice
  ]
  scope := "Finite multi-link network NetworkUtilityModel R L with route incidence, link \
    capacities, and utilities on [0, ∞). IsKKT states the general nonnegative KKT conditions \
    U'_r(x_r) ≤ q_r with equality at 0 < x_r (matching Eq. (22.2) at interior rates) plus \
    Eqs. (22.3)–(22.5). Necessity (IsSocialOptimum.exists_isKKT) is proved via Farkas' lemma \
    without requiring Slater's condition. Existence (exists_isKKT) assumes nonempty routes, \
    nonnegative capacities, and utilities differentiable on [0, ∞); uniqueness of rates assumes \
    strict concavity on [0, ∞), and uniqueness of link prices assumes 0 < x and full row rank \
    (Function.Injective M.routePrice)."

register_result "nrtv-weighted-proportional-fairness-myopic-alignment" where
  title := "Weighted proportionally fair rate allocation, KKT equivalence, and myopic bid alignment"
  topic := "algorithmic game theory"
  sources := [
    { paper := OzdaglarSrikant2007,
      theorem := "Eqs. (22.8)–(22.12) and (22.15) (weighted proportional fairness and bid \
        alignment)",
      locator := "Chapter 22, §22.1, pp. 574, 576" },
    { paper := Vazirani2007,
      theorem := "Proportional fairness convex program",
      locator := "Chapter 5, §5.13, p. 125" },
    { paper := Kelly1997,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    NetworkUtilityModel.isWeightedPropFair_iff_max_log,
    NetworkUtilityModel.isWeightedPropFair_iff_exists_kkt,
    NetworkUtilityModel.existsUnique_isWeightedPropFair,
    NetworkUtilityModel.IsKKT.isWeightedPropFairKKT_of_myopicBids,
    myopicBid_isMax_iff_derivWithin_eq
  ]
  scope := "Finite multi-link network NetworkUtilityModel R L with positive bids w > 0. Proves \
    equivalence between weighted proportional fairness ∑_r w_r (y_r - x_r) / x_r ≤ 0, \
    maximization of ∑_r w_r log x_r over strictly positive feasible rates (Eq. (22.8)), and the \
    KKT system Eqs. (22.9)–(22.12) (correcting the printed sum index typo in Eq. (22.9) from \
    r : l ∈ r to l : l ∈ r). Existence and uniqueness assume nonempty routes and strictly \
    positive link capacities. Also proves alignment with social optimality under \
    w_r = x̂_r U'_r(x̂_r) and equivalence of myopic bid maximization with U'_r(w_r / q_r) = q_r."

register_result "nrtv-dual-congestion-control-lyapunov-convergence" where
  title := "Lyapunov stability and global asymptotic convergence of dual congestion control"
  topic := "algorithmic game theory"
  sources := [
    { paper := OzdaglarSrikant2007,
      theorem := "Eqs. (22.13)–(22.15) (quadratic Lyapunov stability and convergence)",
      locator := "Chapter 22, §22.1, pp. 575–576" }
  ]
  theorems := [
    NetworkUtilityModel.IsDualPriceTrajectory.hasDerivWithinAt_lyapunov_le,
    NetworkUtilityModel.IsDualPriceTrajectory.antitoneOn_lyapunov_of_fixedBids,
    NetworkUtilityModel.IsDualPriceTrajectory.tendsto_of_fixedBids,
    NetworkUtilityModel.IsDualPriceTrajectory.antitoneOn_lyapunov_of_myopic,
    NetworkUtilityModel.IsDualPriceTrajectory.tendsto_of_myopic
  ]
  scope := "Continuous-time projected dual price trajectories ṗ_l = (y_l - c_l)^+_{p_l} on [0, ∞) \
    (Eq. (22.13)). Proves the exact quadratic Lyapunov drift bound dV/dt ≤ (q - q*)ᵀ (x - x*), \
    Lyapunov monotonicity, and global convergence of route prices q(t) → q*, rates x(t) → x*, \
    and (under full row rank Function.Injective M.routePrice) link prices p(t) → p* both for \
    fixed bids x_r = w_r / q_r (Eq. (22.14), assuming nonempty routes, positive capacities, and \
    positive route prices) and for myopic rate control U'_r(x_r) = q_r (Eq. (22.15), assuming \
    nonempty routes, nonnegative capacities, and strictly concave admissible utilities). \
    Convergence assumes a trajectory satisfying Eq. (22.13) exists on [0, ∞) (ODE well-posedness \
    is not proved here)."

register_result "nrtv-wireless-max-weight-dual-decomposition-lyapunov" where
  title := "Wireless network utility maximization: Max-Weight corner-point identity, KKT \
    characterization, Lyapunov stability, and convergence"
  topic := "algorithmic game theory"
  sources := [
    { paper := OzdaglarSrikant2007,
      theorem := "Eqs. (22.16)–(22.21) (wireless dual decomposition and Max-Weight Lyapunov \
        stability)",
      locator := "Chapter 22, §22.1, pp. 577–578" }
  ]
  theorems := [
    WirelessNetworkModel.sum_price_mul_scheduledCapacity_eq,
    WirelessNetworkModel.sum_price_mul_scheduledCapacity_le_maxWeight,
    WirelessNetworkModel.exists_maxWeight_corner,
    WirelessNetworkModel.IsWirelessKKT.isWirelessOptimum,
    WirelessNetworkModel.IsWirelessOptimum.exists_isWirelessKKT,
    WirelessNetworkModel.exists_isWirelessKKT,
    WirelessNetworkModel.IsWirelessDualTrajectory.hasDerivWithinAt_lyapunov_le,
    WirelessNetworkModel.IsWirelessDualTrajectory.antitoneOn_lyapunov_of_myopic,
    WirelessNetworkModel.IsWirelessDualTrajectory.tendsto_of_myopic
  ]
  scope := "Finite wireless network WirelessNetworkModel R L S extending NetworkUtilityModel with \
    interference-free link schedules schedule : S → Finset L. Proves the exact Max-Weight linear \
    program corner-point identity (Eq. (22.20)), wireless KKT sufficiency and Farkas-based \
    necessity and existence (Eqs. (22.16)–(22.20)), and for any continuous-time wireless dual \
    trajectory ṗ_l = (y_l - ∑_{s : l ∈ M_s} f_s c_l)^+_{p_l} (Eq. (22.21)) using a Max-Weight \
    schedule distribution at every instant, the quadratic Lyapunov drift bound, monotonicity, and \
    global convergence of rates, route prices, and (under full row rank) link prices under \
    myopic rate control (Eq. (22.15)) for strictly concave admissible utilities."

end
