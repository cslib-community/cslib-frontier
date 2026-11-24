/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Gaussian.Slepian
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Arccos

/-!
# Limiting Correlation Functions and Dual-LP Certificate Interface for Hypergraphs

Defines the limiting Gaussian straddling correlations (`twoStepCorr`, `capSq`, `capCorr`,
`coneMeanSq`, `coneCorr`), the four-regime `HyperEdgeBound` predicate, the dual-LP certificate
structure `HyperDualCert`, and the resulting lower-bound constant `hyperCoeff`.

## Main definitions

* `twoStepCorr`, `capSq`, `capCorr`, `coneMeanSq`, `coneCorr`: limiting Gaussian correlation
  functions on size-`k` hyperedges in fan-in at most `r`.
* `HyperEdgeBound`, `HyperDualCert`, `hyperCoeff`: admissible hyperedge straddling bounds and
  rational dual-LP certificates.
-/

public section

namespace Cslib.Circuits.Frontier.Hypergraph

open MeasureTheory ProbabilityTheory Real Set Filter Cslib.Circuits
open scoped RealInnerProductSpace Interval

/-! ### Limiting correlation functions and dual-LP certificate interface -/

/-- Limiting two-step pairwise correlation `2 q₂ / (1 + q₂²)` (`q₂ = 1 / √(r (k - 1))`) between
distinct vertices of a size-`k` hyperedge in fan-in `r`. -/
@[expose] noncomputable def twoStepCorr (r k : ℕ) : ℝ :=
  2 * (1 / √((r : ℝ) * ((k : ℝ) - 1))) / (1 + (1 / √((r : ℝ) * ((k : ℝ) - 1))) ^ 2)

/-- Squared one-step vertex-to-hyperedge correlation `4 √m / (√m + 1)²`, `m = r (k - 1)`. -/
@[expose] noncomputable def capSq (r k : ℕ) : ℝ :=
  4 * √((r : ℝ) * ((k : ℝ) - 1)) / (√((r : ℝ) * ((k : ℝ) - 1)) + 1) ^ 2

/-- Average pairwise correlation `(k κ² - 1) / (k - 1)` in the one-step spherical cap around a
hyperedge center. -/
@[expose] noncomputable def capCorr (r k : ℕ) : ℝ :=
  ((k : ℝ) * capSq r k - 1) / ((k : ℝ) - 1)

/-- Symmetric mean squared norm `(1 + (k - 1) q₂²) / k` (`q₂ = 1 / √(r (k - 1))`) of envelope-
truncated vertex rows in the star-cone bound. -/
@[expose] noncomputable def coneMeanSq (r k : ℕ) : ℝ :=
  (1 + ((k : ℝ) - 1) * (1 / √((r : ℝ) * ((k : ℝ) - 1))) ^ 2) / (k : ℝ)

/-- Limiting average pairwise correlation `(2 q₂ + (k - 2) q₂²) / (1 + (k - 1) q₂²)` from the
two-step star-cone bound on a size-`k` hyperedge. -/
@[expose] noncomputable def coneCorr (r k : ℕ) : ℝ :=
  let q₂ := 1 / √((r : ℝ) * ((k : ℝ) - 1))
  (2 * q₂ + ((k : ℝ) - 2) * q₂ ^ 2) / (1 + ((k : ℝ) - 1) * q₂ ^ 2)

/-- Admissible upper bounds `p` on the limiting Gaussian straddling probability of a hyperedge of
cardinality `k ≥ 2` in fan-in at most `r`. -/
inductive HyperEdgeBound (r k : ℕ) : ℝ → Prop
  | pairwise {p : ℝ} (hp : (k : ℝ) / (2 * π) * arccos (twoStepCorr r k) ≤ p) :
      HyperEdgeBound r k p
  | cap {p : ℝ} (hcap : 1 / 2 < capSq r k)
      (hp : (k : ℝ) / (2 * π) * arccos (capCorr r k) ≤ p) :
      HyperEdgeBound r k p
  | starCone {p : ℝ} (hk : 3 ≤ k)
      (hlo : 1 / √((r : ℝ) * ((k : ℝ) - 1)) < coneMeanSq r k)
      (hhi : coneMeanSq r k - 1 / √((r : ℝ) * ((k : ℝ) - 1)) <
        2 * (1 / √((r : ℝ) * ((k : ℝ) - 1))) * √(coneMeanSq r k))
      (hp : (k : ℝ) / (2 * π) * arccos (coneCorr r k) ≤ p) :
      HyperEdgeBound r k p
  | slepian {p : ℝ} (hp : equicorrStraddle k (twoStepCorr r k) ≤ p) :
      HyperEdgeBound r k p

/-- Dual LP certificate `(a, b)` for bounded-fan-in `r` hypergraph cutwidth with size cutoff `K₀`:
every hyperedge of size `2 ≤ k ≤ K₀` straddles a Gaussian threshold with limiting probability at
most `a * k + b`, and every hyperedge of size `k ≥ K₀ + 1` satisfies `1 ≤ a * k + b`. -/
structure HyperDualCert (r K₀ : ℕ) (a b : ℚ) : Prop where
  /-- Fan-in bound is at least two. -/
  hr : 2 ≤ r
  /-- Hyperedge truncation threshold is at least two. -/
  hK₀ : 2 ≤ K₀
  /-- Positive per-pin weight `a > 0`. -/
  ha : 0 < a
  /-- Nonnegativity at `k = 2`. -/
  h2 : 0 ≤ 2 * a + b
  /-- Large hyperedges (`k ≥ K₀ + 1`) deterministically satisfy `1 ≤ a * k + b`. -/
  htail : 1 ≤ a * (K₀ + 1) + b
  /-- Positive per-gate supply coefficient `(r + 1) a + b > 0`. -/
  hdenom : 0 < (r + 1 : ℚ) * a + b
  /-- Input supply coefficient `max b (-a)` is strictly below `1`. -/
  hnum : max b (-a) < 1
  /-- Pointwise hyperedge straddling bound across `2 ≤ k ≤ K₀`. -/
  hedge : ∀ k ∈ Finset.Icc 2 K₀, HyperEdgeBound r k ((a : ℝ) * k + b)

/-- Resulting circuit-size lower-bound constant `(r - 1) (1 - max b (-a)) / ((r + 1) a + b)` for
`(r - 1) * c.multiarySize`. -/
@[expose] def hyperCoeff (r : ℕ) (a b : ℚ) : ℚ :=
  (r - 1 : ℚ) * (1 - max b (-a)) / ((r + 1 : ℚ) * a + b)


end Cslib.Circuits.Frontier.Hypergraph
