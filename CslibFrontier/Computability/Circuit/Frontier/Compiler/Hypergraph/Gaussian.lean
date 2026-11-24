/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Compiler
public import CslibFrontier.Foundations.Probability.Gaussian.Slepian
public import CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Gaussian.DualCert
public import CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Gaussian.Layout

/-!
# Adaptive bipartite Gaussian kernel and dual-certificate layouts for signal hypergraphs

Given a single-output circuit `c : Circuit σ n 1` of fan-in at most `r ≥ 2`, `Hypergraph/Compiler`
constructs its live signal hypergraph on `HyperNode c = LiveGate c ⊕ Unit` (`≤ c.multiarySize + 1`
vertices), where every node belongs to at most `r + 1` hyperedges, every gate signal spans at least
`2` nodes, and the total pin count satisfies `∑ w, |hyperEdge c w| ≤ (r + 1) |LiveGate c| + 1`.

Instead of expanding high-fan-out signals into fixed degree-`3` junction chains prior to choosing a
layout, this module scores `HyperNode c` directly by an **adaptive bipartite walk-maximum Gaussian
kernel** over `HyperNode c` and the pruned hyperedges of cardinality in `[2, K₀]`:

1. **Truncation and bipartite walk-maximum kernel.** Signals of size `k > K₀` are bounded
   deterministically (`1 ≤ a (K₀ + 1) + b ≤ a k + b`), while signals `e` of size `2 ≤ k ≤ K₀` form a
   bipartite incidence graph of maximum degree `D = max (r + 1) K₀` with non-backtracking branching
   `r` at nodes and `k - 1` at hyperedges, and step attenuation `θ / (r (k - 1)) ^ (1/4)`.
   Non-backtracking cancellation bounds the radius-`m` boundary mass by `D θ ^ (2 m)` without any
   girth assumption.
2. **Four straddling-probability regimes (`HyperEdgeBound`).** On any hyperedge `e` of size `k`:
   - **Pairwise two-step Sheppard (`.pairwise`):** distinct `u, v ∈ e` achieve limiting inner
     product `twoStepCorr r k = 2 q₂ / (1 + q₂²)`, `q₂ = 1 / √(r (k - 1))`.
   - **One-step spherical-cap Sheppard (`.cap`):** every `v ∈ e` achieves inner product
     `κ = 2 q₁ / (1 + q₁²)` (`q₁² = q₂`) with the hyperedge center row `e`, giving average pairwise
     correlation `capCorr r k = (k κ² - 1) / (k - 1)` when `κ² > 1 / 2` via
     `InnerProductGeometry.sum_offDiag_angle_le`.
   - **Two-step star-cone Sheppard (`.starCone`):** truncating vertex rows at the hyperedge envelope
     `M(z) = max_{v ∈ e} walkMax (2S - 2) v z` puts every `b_v` in `[q₂ M, M]` with one coordinate
     attaining `M(z)`, yielding the strictly stronger average pairwise correlation
     `coneCorr r k = (2 q₂ + (k - 2) q₂²) / (1 + (k - 1) q₂²)` whenever the cone tangent hypotheses
     hold (`r ∈ {3, 4, 8, 16}`, `k = 3`, etc.).
   - **Equicorrelated Slepian comparison (`.slepian`):** `measureReal_straddlesOn_le_equicorr`
     bounds the straddling probability uniformly over all thresholds `t` by
     `equicorrStraddle k (twoStepCorr r k)`.
3. **Dual LP certificate layout theorem (`HyperDualCert`, `exists_layout_hyperWidth_le`).** Any
   rational certificate `(a, b)` dominating the active hyperedge bounds on `2 ≤ k ≤ K₀` and `1` at
   `K₀ + 1` yields, via second-moment grid concentration on `HyperNode c`, a layout `π` of
   `hyperWidth c π ≤ ((r + 1) a + b) |LiveGate c| + max b (-a) |LiveInput c| + ξ |HyperNode c| + C`.

The bipartite adaptive hypergraph kernel, the star-cone Sheppard correlation identity, and the
dual-LP hypergraph layout reduction are original to this library, building on Gaussian threshold
sweeps [Gaspers2026], Sheppard's median identity [Sheppard1899], and Slepian's inequality
[LedouxTalagrand1991, Corollary 3.12].

## Main definitions

* `Cslib.Circuits.Frontier.Hypergraph.twoStepCorr`, `capSq`, `capCorr`, `coneMeanSq`, `coneCorr`:
  limiting correlations of the bipartite walk-maximum kernel.
* `Cslib.Circuits.Frontier.Hypergraph.HyperEdgeBound`,
  `Cslib.Circuits.Frontier.Hypergraph.HyperDualCert`,
  `Cslib.Circuits.Frontier.Hypergraph.hyperCoeff`: dual certificate specification and resulting
  circuit-size lower-bound constant `(r - 1) (1 - max b (-a)) / ((r + 1) a + b)`.

## Main results

* `Cslib.Circuits.Frontier.Hypergraph.exists_layout_hyperWidth_le`: unconditional layout existence
  for every circuit of fan-in at most `r` from a `HyperDualCert r K₀ a b`.

## References

* [S. Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster
  Exponential Algorithms*][Gaspers2026]
* [W. F. Sheppard, *On the application of the theory of error to cases of normal distribution
  and normal correlation*][Sheppard1899]
* [M. Ledoux, M. Talagrand, *Probability in Banach Spaces*][LedouxTalagrand1991]
-/
