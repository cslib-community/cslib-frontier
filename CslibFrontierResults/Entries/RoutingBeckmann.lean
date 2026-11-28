/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Congestion.BeckmannPotential
import CslibFrontier.GameTheory.Congestion.MarginalCostPricing
import CslibFrontier.GameTheory.Congestion.CapacityAugmentation
import CslibFrontier.GameTheory.Congestion.WardropNoRegret

/-!
# Collected results: nonatomic selfish routing, pricing, capacity augmentation, and no-regret flow
-/

open Cslib.GameTheory

register_result "wardrop-variational-inequality" where
  title := "Variational inequality characterization of Wardrop equilibria"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Proposition 18.20",
      locator := "Section 18.4.1, p. 474" }
  ]
  theorems := [
    NonatomicCongestionGame.isWardrop_iff_variationalInequality
  ]
  scope := "Finite-path, finite-resource multicommodity nonatomic congestion games with real path \
    flows. Proves both directions of the edge-flow variational inequality characterization; takes \
    no separate nonemptiness hypothesis, since feasibility of f already supplies the rerouted \
    flows in the converse implication."

register_result "beckmann-potential-characterization" where
  title := "Beckmann's potential characterizes Wardrop equilibria as global minimizers"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Proposition 18.11",
      locator := "Section 18.3.1, p. 470" }
  ]
  theorems := [
    NonatomicCongestionGame.isWardrop_iff_isMinOn_beckmannPotential
  ]
  scope := "Finite-path, finite-resource multicommodity nonatomic congestion games with continuous \
    nondecreasing latencies on [0, ∞): a feasible flow is a Wardrop equilibrium iff it globally \
    minimizes Beckmann's integral potential ∑_e ∫_0^{f_e} c_e(x) dx over all feasible flows."

register_result "wardrop-existence-uniqueness" where
  title := "Existence and essential uniqueness of Wardrop equilibria"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Theorem 18.8",
      locator := "Section 18.3.1, p. 468 (proof p. 470)" }
  ]
  theorems := [
    NonatomicCongestionGame.exists_isWardrop,
    NonatomicCongestionGame.isWardrop_latency_eq,
    NonatomicCongestionGame.isWardrop_cost_eq
  ]
  scope := "Finite-path, finite-resource multicommodity nonatomic congestion games. Under \
    nonnegative demand rates, at least one path per positive-demand commodity, and continuous \
    latencies on [0, ∞), a Wardrop equilibrium exists; under nondecreasing latencies on [0, ∞), \
    all Wardrop equilibria induce identical edge latencies and identical total social cost."

register_result "pigou-linear-price-of-stability" where
  title := "Pigou's linear network has unique Wardrop equilibrium and price of stability 4/3"
  topic := "game theory"
  sources := [
    { paper := RoughgardenTardos2007,
      theorem := "Example 17.1",
      locator := "Section 17.2.1, pp. 447–448 (CUP 2007; p. 445 in the author chapter PDF)" }
  ]
  theorems := [
    NonatomicCongestionGame.pigouNetwork_id_isWardrop_iff,
    NonatomicCongestionGame.pigouNetwork_id_priceOfStability
  ]
  scope := "Two-link unit-rate Pigou network with latencies x and 1: ![1/2, 1/2] minimizes total \
    cost at 3/4, while every Wardrop equilibrium equals ![1, 0] and costs (4/3) * (3/4) = 1."

register_result "beckmann-potential-poa-bound" where
  title := "Potential-function price-of-anarchy upper bound for nonatomic selfish routing"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Theorem 18.16",
      locator := "Section 18.4.1, p. 472" }
  ]
  theorems := [
    NonatomicCongestionGame.IsWardrop.cost_le_mul_of_le_mul_integral
  ]
  scope := "Finite-path, finite-resource multicommodity nonatomic congestion games with continuous \
    nondecreasing latencies on [0, ∞) satisfying x * c_e(x) ≤ γ * ∫_0^x c_e(y) dy for x ≥ 0 and \
    γ ≥ 0: every Wardrop equilibrium costs at most γ times every feasible flow."

register_result "beckmann-potential-poa-polynomial" where
  title := "Potential-function price-of-anarchy bound d + 1 for degree-d polynomial latencies"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Corollary 18.17",
      locator := "Section 18.4.1, p. 473" }
  ]
  theorems := [
    NonatomicCongestionGame.IsWardrop.cost_le_succ_mul_of_mem_polynomialLatencies
  ]
  scope := "Finite-path, finite-resource multicommodity nonatomic congestion games whose latencies \
    are polynomials of degree at most d with nonnegative coefficients: every Wardrop equilibrium \
    costs at most (d + 1) times every feasible flow."

register_result "marginal-cost-pricing" where
  title := "Socially optimal flows coincide with marginal-cost Wardrop equilibria"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Corollary 18.10",
      locator := "Section 18.3.1, pp. 468–469 (with Proposition 18.9)" }
  ]
  theorems := [
    NonatomicCongestionGame.isOptimal_iff_isWardrop_of_hasDerivWithinAt_mul
  ]
  scope := "Finite-path, finite-resource multicommodity nonatomic congestion games. When each \
    edge cost contribution x ↦ x * c_e(x) is convex on [0, ∞) and has derivative mc e within \
    [0, ∞) (without requiring c_e itself to be differentiable at 0, so latencies such as c_e(x) \
    = √x with unused edges f_e = 0 are admitted), a flow minimizes total latency iff it is a \
    Wardrop equilibrium of G.withLatency mc (and unfolding IsWardrop gives the path-sum \
    characterization of Proposition 18.9). The companion theorem \
    isOptimal_iff_isWardrop_withMarginalCost specializes mc e(x) = c_e(x) + x * c'_e(x) by the \
    product rule when c_e itself has derivative c'_e within [0, ∞)."

register_result "pigouvian-marginal-cost-taxes" where
  title := "Pigouvian marginal-cost taxes induce socially optimal flows as Wardrop equilibria"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Theorem 18.27",
      locator := "Section 18.5.1, p. 478" }
  ]
  theorems := [
    NonatomicCongestionGame.IsOptimal.isWardrop_withTaxes_pigouvianTax,
    NonatomicCongestionGame.IsOptimal.cost_eq_of_isWardrop_withTaxes
  ]
  scope := "Finite-path, finite-resource multicommodity nonatomic congestion games. For any \
    socially optimal flow f* where each c_e has derivative c'_e within [0, ∞) at f*_e (without \
    requiring convexity), constant per-unit Pigouvian edge taxes τ_e = f*_e * c'_e(f*_e) make f* \
    a Wardrop equilibrium of (G, r, c + τ). When each c_e is also nondecreasing on [0, ∞) \
    (without requiring strict monotonicity), every Wardrop equilibrium of the taxed game has the \
    exact same total cost and is socially optimal for G."

register_result "pigou-bound-concave-latencies" where
  title := "The Pigou bound of nonnegative nondecreasing concave latencies is 4/3"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Exercise 18.6",
      locator := "Exercises, p. 485" }
  ]
  theorems := [
    pigouBound_concaveLatencies
  ]
  scope := "Exact Pigou bound pigouBound concaveLatencies = ENNReal.ofReal (4 / 3) for the class \
    of nonnegative, nondecreasing, concave latency functions on [0, ∞)."

register_result "pigou-bound-polynomial-asymptotics" where
  title := "Polynomial Pigou bound grows asymptotically as d / ln d"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Exercise 18.1",
      locator := "Exercises, p. 484" }
  ]
  theorems := [
    tendsto_toReal_pigouBound_polynomialLatencies_mul_log_div
  ]
  scope := "Exact asymptotic limit (pigouBound (polynomialLatencies d)).toReal * (Real.log d / d) \
    → 1 as d → ∞."

register_result "selfish-routing-capacity-augmentation" where
  title := "Selfish routing beats centralized routing at twice the traffic"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Theorem 18.29",
      locator := "Section 18.5.2, p. 479" }
  ]
  theorems := [
    NonatomicCongestionGame.IsWardrop.cost_le_of_scaleRate_two
  ]
  scope := "Finite-path, finite-resource multicommodity nonatomic congestion games with arbitrary \
    nonnegative nondecreasing latencies on [0, ∞): any Wardrop equilibrium at rate r costs at \
    most any feasible flow at rate 2r."

register_result "selfish-routing-link-speedup" where
  title := "Doubling link speed offsets the inefficiency of selfish routing"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Corollary 18.30",
      locator := "Section 18.5.2, p. 480" }
  ]
  theorems := [
    NonatomicCongestionGame.IsWardrop.speedup_two_cost_le
  ]
  scope := "Finite-path, finite-resource multicommodity nonatomic congestion games with arbitrary \
    nonnegative nondecreasing latencies on [0, ∞): any Wardrop equilibrium of G.speedup 2 (with \
    latencies c_e(x / 2) / 2) costs at most any feasible flow of G."

register_result "selfish-routing-capacity-augmentation-refinements" where
  title := "Sharp (1 + δ)r capacity augmentation, atomic counterexample, and affine δ = 1/4"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Exercise 18.8",
      locator := "Exercises, p. 485 (with Example 18.28, p. 479)" }
  ]
  theorems := [
    NonatomicCongestionGame.IsWardrop.cost_le_inv_mul_of_scaleRate,
    NonatomicCongestionGame.exists_pigouNetwork_pow_scaleRate_cost_lt,
    NonatomicCongestionGame.affine_scaleRate_bound_iff,
    CongestionGame.exists_atomic_pureNash_socialCost_gt_doubled
  ]
  scope := "Refinements of Theorem 18.29: (c) general (1 / δ) bound for rate (1 + δ) r with \
    δ > 0; (d) tightness on degree-d Pigou networks as d → ∞; (e) exact threshold δ ≥ 1/4 for \
    nonnegative affine latencies; and (b) explicit 4-player vs. 8-player unweighted k^4 atomic \
    congestion game where a pure Nash equilibrium at rate r has social cost 972 > 128 at rate 2r."

register_result "braess-wheatstone-paradox" where
  title := "Braess's four-node Wheatstone paradox increases equilibrium cost by a factor of 4/3"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Example 18.4",
      locator := "Section 18.2.1, pp. 464–465" }
  ]
  theorems := [
    NonatomicCongestionGame.braessInitial_isWardrop_iff,
    NonatomicCongestionGame.braessAugmented_isWardrop_iff,
    NonatomicCongestionGame.braessAugmented_isOptimal_half,
    NonatomicCongestionGame.braess_paradox
  ]
  scope := "On the four-node Wheatstone network with unit traffic rate, braessInitial has unique \
    Wardrop equilibrium ![1/2, 1/2] of cost 3/2, whereas braessAugmented (adding the zero-cost \
    cross edge) has optimal flow ![1/2, 1/2, 0] of cost 3/2 and unique Wardrop equilibrium \
    ![0, 0, 1] of cost 2 = (4/3) * (3/2)."

register_result "braess-paradox-bound" where
  title := "Adding paths increases Wardrop cost by at most the Pigou bound (4/3 for affine)"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Remark 18.22",
      locator := "Section 18.4.1, p. 475" }
  ]
  theorems := [
    NonatomicCongestionGame.IsWardrop.cost_le_toReal_pigouBound_mul_restrictPaths,
    NonatomicCongestionGame.HasAffineLatencies.cost_le_four_thirds_restrictPaths
  ]
  scope := "Zero-extension Function.extend ι f₁ 0 embeds any path-restricted subnetwork \
    G.restrictPaths ι (ι : P₁ ↪ P₂) into G with identical edge flows and cost, so adding paths \
    or edges increases Wardrop equilibrium cost by at most (pigouBound C).toReal (4/3 for \
    nonnegative affine latencies)."

register_result "wardrop-no-regret-convergence" where
  title := "Time-averaged no-regret routing with affine latencies is an ε-Wardrop equilibrium"
  topic := "game theory"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorem 4.18",
      locator := "Section 4.7, p. 97" }
  ]
  theorems := [
    NonatomicCongestionGame.HasAffineLatencies.isApproxWardrop_timeAverageFlow,
    NonatomicCongestionGame.HasAffineLatencies.isApproxWardrop_timeAverageFlow_unit
  ]
  scope := "Multicommodity and single-commodity unit-rate nonatomic congestion games with \
    nonnegative affine latencies over T > 0 days: whenever daily feasible flows have average \
    external regret at most ε, their time-averaged flow timeAverageFlow f T is feasible and \
    ε-Wardrop with no degradation in ε. Original nonlinear time-average extensions and the \
    quadratic counterexample in WardropNoRegret.lean are intentionally omitted from this entry, \
    and per-day (1 - ε)-fraction convergence from Section 4.7, pp. 97–98 remains open under #7789."
