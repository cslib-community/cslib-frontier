/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Evolutionary.RoutingDynamics

/-!
# Collected results: evolutionary dynamics applied to selfish routing
-/

open Cslib.GameTheory.NonatomicCongestionGame

register_result "suri-imitative-routing-feasibility" where
  title := "Equivalence of imitative and replicator dynamics and all-time flow feasibility"
  topic := "game theory"
  sources := [
    { paper := Suri2007, theorem := "Equations 29.1–29.2 and Exercise 29.6",
      locator := "Section 29.3.1, pp. 724–725; Section 29.6, p. 736" }
  ]
  theorems := [
    imitativeDrift_eq_replicatorDrift,
    sum_replicatorDrift_eq_zero,
    IsReplicatorTrajectory.isFeasible,
    IsReplicatorTrajectory.isFeasible_relative
  ]
  scope := "Single-commodity unit-rate nonatomic congestion games \
    G : NonatomicCongestionGame Unit P E with G.rate () = 1. Proves that for any flow summing to \
    1 the pairwise imitative drift (Equation 29.1) equals the replicator drift (Equation 29.2) \
    and sums to 0, and that any trajectory of Equation (29.2) starting from a feasible flow \
    remains feasible for all t ≥ 0 (both for continuous rate functions lam ∘ x and for the \
    relative rate λ(x) = (G.cost x)⁻¹ when feasible average latency is bounded below by lStar > 0)."

register_result "suri-imitative-routing-convergence" where
  title := "Fast convergence of imitative dynamics to an ε-approximate equilibrium \
    in selfish routing"
  topic := "game theory"
  sources := [
    { paper := Suri2007, theorem := "Theorem 29.12", locator := "Section 29.3.3, pp. 727–728" }
  ]
  theorems := [
    exists_relativeReplicatorTrajectory_isApproxEquilibrium,
    IsReplicatorTrajectory.exists_mem_Icc_isApproxEquilibrium
  ]
  scope := "Single-commodity unit-rate nonatomic congestion games \
    G : NonatomicCongestionGame Unit P E (G.rate () = 1) with nonnegative, nondecreasing, \
    Lipschitz latency functions on [0, 1], positive minimum feasible average latency lStar > 0, \
    and a feasible initial flow x₀ with G.cost x₀ ≤ lMax. Proves global existence (via \
    Picard–Lindelöf on a clamped extension) and uniqueness of the relative-rate replicator \
    trajectory x on [0, ∞) starting at x₀, all-time feasibility, Lyapunov monotonicity of the \
    shifted Beckmann potential (Equation 29.3), and that for every ε > 0 the trajectory reaches \
    an ε-approximate equilibrium (Definition 29.11) at some time \
    t ∈ [0, (2 / ε ^ 3) * Real.log (2 * lMax / lStar)] (sharpening the constant 4 on p. 728 to 2; \
    as in the source proof, this is a hitting-time bound rather than permanence inside the \
    approximate-equilibrium set)."
