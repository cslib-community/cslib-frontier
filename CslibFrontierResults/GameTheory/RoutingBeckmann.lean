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

register_result "wardrop-existence-uniqueness" where
  title := "Beckmann's potential characterizes Wardrop equilibria, establishing existence and \
    essential uniqueness"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Theorem 18.8, Proposition 18.11, Theorem 18.16, Corollary 18.17, and \
        Proposition 18.20",
      locator := "Sections 18.3.1 and 18.4.1, pp. 468–470 and 472–474" },
    { paper := RoughgardenTardos2007,
      theorem := "Example 17.1",
      locator := "Section 17.2.1, pp. 447–448" }
  ]
  theorems := [
    NonatomicCongestionGame.isWardrop_iff_variationalInequality,
    NonatomicCongestionGame.isWardrop_iff_isMinOn_beckmannPotential,
    NonatomicCongestionGame.exists_isWardrop,
    NonatomicCongestionGame.isWardrop_latency_eq,
    NonatomicCongestionGame.isWardrop_cost_eq,
    NonatomicCongestionGame.pigouNetwork_id_priceOfStability,
    NonatomicCongestionGame.IsWardrop.cost_le_mul_of_le_mul_integral,
    NonatomicCongestionGame.IsWardrop.cost_le_succ_mul_of_mem_polynomialLatencies
  ]
  scope := "Finite-path, finite-resource multicommodity nonatomic congestion games with real path \
    flows. Proves both directions of the variational inequality characterization (assuming a \
    feasible flow exists for the forward implication only when constructing rerouted flows, which \
    holds whenever f is feasible), equivalence between Wardrop equilibria and global minimizers of \
    Beckmann's integral potential ∑_e ∫_0^{f_e} c_e(x) dx over the compact convex feasible flow \
    polytope under continuous nondecreasing latencies on [0, ∞), existence of Wardrop equilibria \
    whenever the feasible set is nonempty, essential uniqueness of equilibrium edge latencies, \
    used-path latencies, and total social cost (deducing uniqueness and PoS = 4/3 on Pigou's \
    linear network), and Beckmann-potential price-of-anarchy bounds including p + 1 for degree-p \
    polynomials."

register_result "marginal-cost-pricing" where
  title := "Socially optimal flows satisfy the marginal-cost Wardrop condition and are induced \
    by Pigouvian taxes"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Proposition 18.9, Corollary 18.10, and Theorem 18.27",
      locator := "Sections 18.3.1 and 18.5.1, pp. 468–469 and 478" }
  ]
  theorems := [
    NonatomicCongestionGame.isOptimal_iff_marginalCost_le,
    NonatomicCongestionGame.isOptimal_iff_isWardrop_withMarginalCost,
    NonatomicCongestionGame.IsOptimal.isWardrop_withTaxes_pigouvianTax,
    NonatomicCongestionGame.IsOptimal.cost_eq_of_isWardrop_withTaxes
  ]
  scope := "Finite-path, finite-resource multicommodity nonatomic congestion games. When x ↦ \
    x * c_e(x) is convex on [0, ∞) and c_e has derivative c'_e on [0, ∞), a feasible flow \
    minimizes total latency iff it satisfies the Wardrop condition with respect to marginal cost \
    c_e(x) + x * c'_e(x) (and optimality implies the marginal-cost Wardrop condition even without \
    convexity). For any socially optimal flow f*, constant per-unit Pigouvian edge taxes \
    τ_e = f*_e * c'_e(f*_e) (nonnegative when c_e is nondecreasing) make f* a Wardrop equilibrium \
    of (G, r, c + τ), and whenever each c_e is nondecreasing on [0, ∞) and differentiable within \
    [0, ∞) at f*_e (without requiring convexity or strict monotonicity), every Wardrop equilibrium \
    of the taxed game has the exact same total cost and is socially optimal for G."

register_result "selfish-routing-capacity-augmentation" where
  title := "Selfish routing beats centralized routing at half the traffic, with sharp (1 + δ)r \
    and affine (5/4)r bounds"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Example 18.28, Theorem 18.29, Corollary 18.30, and Exercises 18.1, 18.6, 18.8",
      locator := "Section 18.5.2 and Exercises, pp. 479–480 and 484–485" }
  ]
  theorems := [
    pigouBound_concaveLatencies,
    tendsto_polynomialPigouBound_nat_mul_log_div,
    tendsto_toReal_pigouBound_polynomialLatencies_mul_log_div,
    NonatomicCongestionGame.IsWardrop.cost_le_inv_mul_of_scaleRate,
    NonatomicCongestionGame.IsWardrop.cost_le_of_scaleRate_two,
    NonatomicCongestionGame.IsWardrop.speedup_two_cost_le,
    NonatomicCongestionGame.affine_scaleRate_bound_iff,
    CongestionGame.exists_atomic_pureNash_socialCost_gt_doubled
  ]
  scope := "Covers capacity augmentation and complementary Pigou-bound results in Chapter 18: \
    (1) for arbitrary nonnegative nondecreasing latencies on [0, ∞) and δ > 0, a Wardrop flow at \
    rate r costs at most (1 / δ) times any feasible flow at rate (1 + δ) r (giving cost_le at 2r \
    and speedup 2), with matching tightness on degree-d Pigou networks as d → ∞; (2) an explicit \
    4-player vs. 8-player unweighted k^4 atomic congestion game where a pure Nash equilibrium at \
    rate r has social cost 972 > 128 at rate 2r; (3) the exact threshold δ ≥ 1/4 for nonnegative \
    affine latencies; (4) pigouBound = 4/3 for nonnegative nondecreasing concave latencies on \
    [0, ∞); and (5) exact p / log p asymptotics of the degree-p polynomial Pigou bound."

register_result "braess-paradox-bound" where
  title := "Braess's Wheatstone paradox attains the tight 4/3 affine subnetwork bound"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2007Routing,
      theorem := "Example 18.4 and Remark 18.22",
      locator := "Sections 18.2.1 and 18.4.1, pp. 464–465 and 475" }
  ]
  theorems := [
    NonatomicCongestionGame.braessInitial_isWardrop_iff,
    NonatomicCongestionGame.braessAugmented_isWardrop_iff,
    NonatomicCongestionGame.braess_paradox,
    NonatomicCongestionGame.IsWardrop.cost_le_toReal_pigouBound_mul_restrictPaths,
    NonatomicCongestionGame.HasAffineLatencies.cost_le_four_thirds_restrictPaths
  ]
  scope := "On the four-node Wheatstone network with unit traffic rate, the initial two-path \
    network has unique Wardrop equilibrium ![1/2, 1/2] of cost 3/2, whereas adding the zero-cost \
    cross edge produces unique Wardrop equilibrium ![0, 0, 1] of cost 2 = (4/3) * (3/2) while \
    ![1/2, 1/2, 0] remains optimal at cost 3/2. More generally, zero-extension embeds any \
    path-restricted subnetwork G.restrictPaths ι (ι : P₁ ↪ P₂) into G with identical edge flows \
    and cost, so adding paths/edges cannot increase optimal cost and increases Wardrop equilibrium \
    cost by at most pigouBound C (4/3 for nonnegative affine latencies)."

register_result "wardrop-no-regret-convergence" where
  title := "Time-averaged no-regret routing converges to approximate Wardrop equilibrium"
  topic := "game theory"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorem 4.18 and Section 4.7",
      locator := "Section 4.7, pp. 96–98" }
  ]
  theorems := [
    NonatomicCongestionGame.cost_timeAverageFlow_le,
    NonatomicCongestionGame.isApproxWardrop_timeAverageFlow_of_concaveOn,
    NonatomicCongestionGame.HasAffineLatencies.isApproxWardrop_timeAverageFlow,
    NonatomicCongestionGame.HasAffineLatencies.isApproxWardrop_timeAverageFlow_unit,
    NonatomicCongestionGame.exists_not_isApproxWardrop_timeAverageFlow_sq,
    NonatomicCongestionGame.isApproxWardrop_timeAverageFlow_of_lipschitz,
    NonatomicCongestionGame.isApproxWardrop_timeAverageFlow_of_convexOn_of_lipschitz,
    NonatomicCongestionGame.isWardrop_timeAverageFlow_of_hasAvgRegretLe_zero
  ]
  scope := "Multicommodity and single-commodity unit-rate nonatomic congestion games over T > 0 \
    days. When edge latencies are concave on [0, ∞) and x ↦ x * c_e(x) is convex on [0, ∞) — in \
    particular for all nonnegative affine latencies (Theorem 4.18) — average external regret ≤ ε \
    implies that the time-averaged flow is feasible and ε-Wardrop with no loss in ε. A concrete \
    two-day quadratic Pigou counterexample (regret 44/64 vs. Wardrop gap 45/64) shows literal ε \
    fails for superlinear convex latencies without fluctuation slack; for general nondecreasing \
    L-Lipschitz latencies on [0, ∞), Chebyshev covariance and Cauchy–Schwarz establish \
    (ε + 2 * totalFlow * √(|E| * L * ε))-Wardrop convergence (and ε + totalFlow * √(|E| * L * ε) \
    when convex, hence exact Wardrop at ε = 0)."
