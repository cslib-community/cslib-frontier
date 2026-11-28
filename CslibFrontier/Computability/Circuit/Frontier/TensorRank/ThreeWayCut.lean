/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.BalancedCut

/-!
# `Z₃`-symmetric planar Gaussian `3`-way cuts of subcubic multigraphs

To reduce a fan-in-`2` circuit to a single square matrix multiplication `Tensor.mm D D D`, one needs
a vertex `3`-coloring `V = V₀ ⊔ V₁ ⊔ V₂` of a connected loopless subcubic multigraph `G` that
simultaneously balances a target vertex subset `A ⊆ V` (`|A ∩ V_c| = |A| / 3 ± o(|V|)`) and bounds
all three pairwise edge cuts `E(V₀, V₁)`, `E(V₁, V₂)`, `E(V₂, V₀)`.

1. **Weight-capped compression.** `CappedCompression` with unit vertex weight and cap `M` shrinks
   `G` to a loopless subcubic quotient `Q` with block size `≤ M`, `#(Q₁ ∪ Q₂) = O(|V| / M)`, and
   `#Q₃ ≤ 2 β₁(G) + #Q₁`.
2. **`Z₃`-symmetric `120°` planar Gaussian cut.** Assign each block two independent standard
   Gaussians `(g₁, g₂)` and three independent Gaussian tie-breakers. Each quotient edge `e` gets the
   `2`D vector `z_e = (edgeScore Q q R g₁ e, edgeScore Q q R g₂ e) ∈ ℝ²`, partitioned into three
   `120°` open sectors `S₀, S₁, S₂`. Each block chooses the sector containing the strict majority of
   its incident edge vectors (breaking ties via its independent tie-breakers).
3. **Ray-crossing + spherical-cap triangle bound.** At a degree-`3` block `B`, the number of
   incident edges falling outside `B`'s chosen sector is `0` in `(3, 0, 0)`, `1` in `(2, 1, 0)`, and
   `2` in the rainbow `(1, 1, 1)` case. Counting oriented crossings of the three boundary rays by
   ordered edge pairs (`rayCross`) together with the origin-in-triangle event `(0, 0) ∈ conv(z_i)`
   (`ProbabilityTheory.measureReal_pi_prod_convex_zero_le`) bounds the expected mismatched half-edge
   count at `B` by
   `threeWayCapCoefficient = (3 / 2) p + (1 / 2) (1 - √((1 + 2√2 / 3) / 2)) ≈ 0.217728 ≤ 0.21773`,
   so each pairwise cut has expected size at most `(2 / 3) threeWayCapCoefficient β₁(G) + o(|V|)`.
   Weighted local Chebyshev concentration (`WeightedSecondMoment`) yields a single coloring meeting
   all six balance and cut bounds simultaneously.

## Main definitions

* `Cslib.Circuits.Frontier.TensorRank.threeWayCapCoefficient`: the `3`-way planar Gaussian
  half-edge mismatch coefficient `(3 / 2) p + (1 / 2) (1 - √((1 + 2√2 / 3) / 2))`.

## Main results

* `Cslib.Circuits.Frontier.TensorRank.threeWayCapCoefficient_pos`: `0 < threeWayCapCoefficient`.
* `Cslib.Circuits.Frontier.TensorRank.threeWayCapCoefficient_le_21773`:
  `threeWayCapCoefficient ≤ 21773 / 100000`.
* `Cslib.Circuits.Frontier.TensorRank.circuitThreshold_gt_3041`:
  `3041 / 1000 < 1 + 4 / (9 * threeWayCapCoefficient)`.
* `Cslib.Circuits.Frontier.TensorRank.exists_balanced_threeWayCut`: simultaneous `1 / 3`-balance on
  `A ⊆ V` and `(2 / 3) · threeWayCapCoefficient · β₁(G)` bound on all three pairwise edge cuts.
-/
