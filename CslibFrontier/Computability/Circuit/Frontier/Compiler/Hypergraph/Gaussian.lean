/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Compiler
public import CslibFrontier.Foundations.Probability.Gaussian.Slepian
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Basic
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Scores
import CslibFrontier.Foundations.Analysis.InnerProductSpace.Basic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Arccos
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Metric
import CslibFrontier.Foundations.Geometry.Euclidean.Angle.Cap
import CslibFrontier.Foundations.Probability.Gaussian.Sheppard
import Mathlib.MeasureTheory.Integral.Bochner.Basic

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

/-! ### Pure Euclidean and combinatorial helpers for Sheppard straddling bounds -/

section Helpers

private theorem norm_inv_smul_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (hx : 1 ≤ ‖x‖) (hy : 1 ≤ ‖y‖) :
    ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ := by
  have hx0 : 0 < ‖x‖ := zero_lt_one.trans_le hx
  have hy0 : 0 < ‖y‖ := zero_lt_one.trans_le hy
  have hdecomp : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y =
      ‖x‖⁻¹ • (x - y) + ((‖y‖ - ‖x‖) / (‖x‖ * ‖y‖)) • y := by
    rw [smul_sub]
    have hscal : (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖) = ‖x‖⁻¹ - ‖y‖⁻¹ := by
      field_simp
    rw [hscal, sub_smul]
    abel
  rw [hdecomp]
  calc ‖‖x‖⁻¹ • (x - y) + ((‖y‖ - ‖x‖) / (‖x‖ * ‖y‖)) • y‖
      ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖((‖y‖ - ‖x‖) / (‖x‖ * ‖y‖)) • y‖ := norm_add_le _ _
    _ = ‖x‖⁻¹ * ‖x - y‖ + |‖y‖ - ‖x‖| / ‖x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hx0), abs_div, abs_of_pos (mul_pos hx0 hy0),
          div_mul_eq_mul_div, mul_div_mul_right _ _ hy0.ne']
    _ ≤ 1 * ‖x - y‖ + ‖x - y‖ / 1 := by
        gcongr
        · exact inv_le_one_of_one_le₀ hx
        · rw [abs_sub_comm]
          exact abs_norm_sub_norm_le x y
    _ = 2 * ‖x - y‖ := by ring

private theorem abs_inner_sub_inner_of_norm_eq_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u₁ u₂ v₁ v₂ : E} (hu₂ : ‖u₂‖ = 1) (hv₁ : ‖v₁‖ = 1) :
    |⟪u₁, v₁⟫ - ⟪u₂, v₂⟫| ≤ ‖u₁ - u₂‖ + ‖v₁ - v₂‖ := by
  have hdecomp : ⟪u₁, v₁⟫ - ⟪u₂, v₂⟫ = ⟪u₁ - u₂, v₁⟫ + ⟪u₂, v₁ - v₂⟫ := by
    rw [inner_sub_left, inner_sub_right]
    ring
  rw [hdecomp]
  calc |⟪u₁ - u₂, v₁⟫ + ⟪u₂, v₁ - v₂⟫|
      ≤ |⟪u₁ - u₂, v₁⟫| + |⟪u₂, v₁ - v₂⟫| := abs_add_le _ _
    _ ≤ ‖u₁ - u₂‖ * ‖v₁‖ + ‖u₂‖ * ‖v₁ - v₂‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ = ‖u₁ - u₂‖ + ‖v₁ - v₂‖ := by rw [hv₁, hu₂, mul_one, one_mul]

/-- Pointwise step-defect inequality shared by the 1-step and 2-step kernel inner-product bounds. -/
private theorem two_mul_div_step_defect_le {q a b a₀ b₀ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : q * b₀ ≤ a) (hba : q * a₀ ≤ b) :
    2 * q / (1 + q ^ 2) * (a ^ 2 + b ^ 2) / 2 - a * b ≤
      (if a₀ < a then a ^ 2 else 0) + (if b₀ < b then b ^ 2 else 0) := by
  have hκ1 : 2 * q / (1 + q ^ 2) ≤ 1 := Gaussian.two_mul_div_one_add_sq_le_one q
  have hκ0 : 0 ≤ 2 * q / (1 + q ^ 2) := by positivity
  have hab0 : 0 ≤ a * b := mul_nonneg ha hb
  by_cases ha_lt : a₀ < a
  · rw [ite_eq_left ha_lt]
    by_cases hb_lt : b₀ < b
    · rw [ite_eq_left hb_lt]
      nlinarith [sq_nonneg a, sq_nonneg b]
    · rw [ite_eq_right hb_lt]
      have hqb : q * b ≤ a := by
        have hble : b ≤ b₀ := not_lt.mp hb_lt
        exact (mul_le_mul_of_nonneg_left hble hq0).trans hab
      by_cases hqa : q * a ≤ b
      · have hprod : 0 ≤ (a - q * b) * (b - q * a) :=
          mul_nonneg (sub_nonneg.mpr hqb) (sub_nonneg.mpr hqa)
        have hden : 0 < 1 + q ^ 2 := by positivity
        nlinarith [div_mul_cancel₀ (2 * q) hden.ne', sq_nonneg a]
      · have hba_le : b ≤ a := by
          have : b < q * a := not_le.mp hqa
          have : q * a ≤ 1 * a := mul_le_mul_of_nonneg_right hq1 ha
          linarith
        have hb_sq : b ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hb hba_le 2
        nlinarith [sq_nonneg a]
  · rw [ite_eq_right ha_lt]
    have hqa : q * a ≤ b :=
      (mul_le_mul_of_nonneg_left (not_lt.mp ha_lt) hq0).trans hba
    by_cases hb_lt : b₀ < b
    · rw [ite_eq_left hb_lt]
      by_cases hqb : q * b ≤ a
      · have hprod : 0 ≤ (a - q * b) * (b - q * a) :=
          mul_nonneg (sub_nonneg.mpr hqb) (sub_nonneg.mpr hqa)
        have hden : 0 < 1 + q ^ 2 := by positivity
        nlinarith [div_mul_cancel₀ (2 * q) hden.ne', sq_nonneg b]
      · have hab_le : a ≤ b := by
          have : a < q * b := not_le.mp hqb
          have : q * b ≤ 1 * b := mul_le_mul_of_nonneg_right hq1 hb
          linarith
        have ha_sq : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab_le 2
        nlinarith [sq_nonneg b]
    · rw [ite_eq_right hb_lt]
      have hqb : q * b ≤ a :=
        (mul_le_mul_of_nonneg_left (not_lt.mp hb_lt) hq0).trans hab
      have hprod : 0 ≤ (a - q * b) * (b - q * a) :=
        mul_nonneg (sub_nonneg.mpr hqb) (sub_nonneg.mpr hqa)
      have hden : 0 < 1 + q ^ 2 := by positivity
      nlinarith [div_mul_cancel₀ (2 * q) hden.ne']

private theorem sum_union_le_of_nonneg {α : Type*} [DecidableEq α] {A B : Finset α} {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ A ∪ B, f x ≤ (∑ x ∈ A, f x) + ∑ x ∈ B, f x := by
  have h1 := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)
  have h2 : 0 ≤ ∑ x ∈ A ∩ B, f x := Finset.sum_nonneg fun x _ => hf x
  linarith

/-- Tangent lower bound for `x + q / x` on `(0, 1]` at `x₀` when `q ≤ x₀²` and
`x₀² - q ≤ 2 q x₀`. -/
private theorem tangent_le_add_div {q x₀ x : ℝ} (_hq : 0 < q) (hx₀ : 0 < x₀) (hx0 : 0 < x)
    (hx1 : x ≤ 1) (hlo : q ≤ x₀ ^ 2) (hhi : x₀ ^ 2 - q ≤ 2 * q * x₀) :
    (x₀ + q / x₀) + (x₀ ^ 2 - q) / (2 * x₀ ^ 3) * (x ^ 2 - x₀ ^ 2) ≤ x + q / x := by
  have hden : 0 < 2 * x * x₀ ^ 3 := by positivity
  suffices h : 0 ≤ ((x + q / x) - ((x₀ + q / x₀) +
      (x₀ ^ 2 - q) / (2 * x₀ ^ 3) * (x ^ 2 - x₀ ^ 2))) * (2 * x * x₀ ^ 3) by
    have h0 := nonneg_of_mul_nonneg_left h hden
    linarith
  have hfac : ((x + q / x) - ((x₀ + q / x₀) +
      (x₀ ^ 2 - q) / (2 * x₀ ^ 3) * (x ^ 2 - x₀ ^ 2))) * (2 * x * x₀ ^ 3) =
      (x - x₀) ^ 2 * (2 * q * x₀ - (x₀ ^ 2 - q) * x) := by
    field_simp
    ring
  rw [hfac]
  refine mul_nonneg (sq_nonneg _) ?_
  have hsub : 0 ≤ x₀ ^ 2 - q := sub_nonneg.mpr hlo
  have hmul : (x₀ ^ 2 - q) * x ≤ (x₀ ^ 2 - q) * 1 := mul_le_mul_of_nonneg_left hx1 hsub
  linarith

/-- Pointwise quadratic cone inequality: `q M ≤ b ≤ M` implies `(1 + q) b M ≥ b² + q M²`. -/
private theorem mul_le_one_add_mul_of_mem_cone {q b M : ℝ} (hlo : q * M ≤ b) (hhi : b ≤ M) :
    b ^ 2 + q * M ^ 2 ≤ (1 + q) * (b * M) := by
  have hprod : 0 ≤ (b - q * M) * (M - b) := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith

/-- **Star-cone sum of inner products.** Given `s : Finset κ` with `k = s.card ≥ 3`, nonnegative
envelope `M : EuclideanSpace ℝ V` (`1 ≤ ‖M‖`), and vectors `b : κ → EuclideanSpace ℝ V`
(`1 ≤ ‖b v‖`) satisfying `q M(z) ≤ b v z ≤ M(z)` at every coordinate `z` with one `v* ∈ s`
attaining `b v* z = M(z)`, the normalized vectors `u v = ‖b v‖⁻¹ • b v` satisfy
`∑ p ∈ s.offDiag, ⟪u p.1, u p.2⟫ ≥ k (k - 1) (2 q + (k - 2) q²) / (1 + (k - 1) q²)` whenever the
cone tangent hypotheses hold. -/
private theorem starCone_sum_offDiag_inner_le {V κ : Type*} [Fintype V]
    {s : Finset κ} (hs : 3 ≤ s.card) {q : ℝ} (hq0 : 0 < q)
    {M : EuclideanSpace ℝ V} (hM1 : 1 ≤ ‖M‖) (hM_nn : ∀ z : V, 0 ≤ M z)
    {b : κ → EuclideanSpace ℝ V} (hb1 : ∀ v ∈ s, 1 ≤ ‖b v‖)
    (hcone_lo : ∀ v ∈ s, ∀ z : V, q * M z ≤ b v z)
    (hcone_hi : ∀ v ∈ s, ∀ z : V, b v z ≤ M z)
    (hattain : ∀ z : V, ∃ v ∈ s, b v z = M z)
    (htan_lo : q ≤ (1 + ((s.card : ℝ) - 1) * q ^ 2) / (s.card : ℝ))
    (htan_hi : (1 + ((s.card : ℝ) - 1) * q ^ 2) / (s.card : ℝ) - q ≤
      2 * q * √((1 + ((s.card : ℝ) - 1) * q ^ 2) / (s.card : ℝ))) :
    (s.card : ℝ) * ((s.card : ℝ) - 1) *
        ((2 * q + ((s.card : ℝ) - 2) * q ^ 2) / (1 + ((s.card : ℝ) - 1) * q ^ 2)) ≤
      ∑ p ∈ s.offDiag, ⟪‖b p.1‖⁻¹ • b p.1, ‖b p.2‖⁻¹ • b p.2⟫ := by
  classical
  set k : ℝ := (s.card : ℝ)
  have hk3 : (3 : ℝ) ≤ k := Nat.ofNat_le_cast.mpr hs
  have hk_pos : 0 < k := by linarith
  have hM_pos : 0 < ‖M‖ := zero_lt_one.trans_le hM1
  have hM_sq_pos : 0 < ‖M‖ ^ 2 := sq_pos_of_pos hM_pos
  set w : EuclideanSpace ℝ V := ‖M‖⁻¹ • M
  have hw_norm : ‖w‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hM_pos.ne']
  let u : κ → EuclideanSpace ℝ V := fun v => ‖b v‖⁻¹ • b v
  have hu_norm (v : κ) (hv : v ∈ s) : ‖u v‖ = 1 := by
    have hbv : 0 < ‖b v‖ := zero_lt_one.trans_le (hb1 v hv)
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hbv.ne']
  set Q₀ : ℝ := (1 + (k - 1) * q ^ 2) / k
  have hQ₀_pos : 0 < Q₀ := lt_of_lt_of_le hq0 htan_lo
  set x₀ : ℝ := √Q₀
  have hx₀_pos : 0 < x₀ := sqrt_pos.mpr hQ₀_pos
  have hx₀_sq : x₀ ^ 2 = Q₀ := sq_sqrt hQ₀_pos.le
  let x : κ → ℝ := fun v => ‖b v‖ / ‖M‖
  have hx_pos (v : κ) (hv : v ∈ s) : 0 < x v :=
    div_pos (zero_lt_one.trans_le (hb1 v hv)) hM_pos
  have hx_le_one (v : κ) (hv : v ∈ s) : x v ≤ 1 := by
    rw [div_le_one hM_pos]
    have hsq : ‖b v‖ ^ 2 ≤ ‖M‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_le_sum fun z _ => ?_
      have hb0 : 0 ≤ b v z := (mul_nonneg hq0.le (hM_nn z)).trans (hcone_lo v hv z)
      exact pow_le_pow_left₀ hb0 (hcone_hi v hv z) 2
    nlinarith [norm_nonneg (b v)]
  have hinner_ge (v : κ) (hv : v ∈ s) : (x v + q / x v) / (1 + q) ≤ ⟪u v, w⟫ := by
    have hbv_pos : 0 < ‖b v‖ := zero_lt_one.trans_le (hb1 v hv)
    have hsum : ‖b v‖ ^ 2 + q * ‖M‖ ^ 2 ≤ (1 + q) * ⟪b v, M⟫ := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply]
      simp only [RCLike.inner_apply, conj_trivial]
      calc (∑ z, b v z ^ 2) + q * ∑ z, M z ^ 2
          = ∑ z, (b v z ^ 2 + q * M z ^ 2) := by rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        _ ≤ ∑ z, (1 + q) * (b v z * M z) :=
            Finset.sum_le_sum fun z _ =>
              mul_le_one_add_mul_of_mem_cone (hcone_lo v hv z) (hcone_hi v hv z)
        _ = (1 + q) * ∑ z, M z * b v z := by
            rw [← Finset.mul_sum]
            exact congrArg ((1 + q) * ·) (Finset.sum_congr rfl fun z _ => mul_comm _ _)
    have hinner_eq : ⟪u v, w⟫ = ‖b v‖⁻¹ * (‖M‖⁻¹ * ⟪b v, M⟫) := by
      rw [real_inner_smul_left, real_inner_smul_right]
    rw [hinner_eq]
    have hxv_pos := hx_pos v hv
    have hcalc : (x v + q / x v) / (1 + q) =
        (‖b v‖ ^ 2 + q * ‖M‖ ^ 2) / ((1 + q) * ‖b v‖ * ‖M‖) := by
      dsimp only [x]
      field_simp
    rw [hcalc, div_le_iff₀ (by positivity)]
    have h1 : ‖b v‖⁻¹ * (‖M‖⁻¹ * ⟪b v, M⟫) * ((1 + q) * ‖b v‖ * ‖M‖) = (1 + q) * ⟪b v, M⟫ := by
      field_simp
    linarith
  have hsum_x_sq : k * x₀ ^ 2 ≤ ∑ v ∈ s, x v ^ 2 := by
    have hcoord (z : V) : (1 + (k - 1) * q ^ 2) * M z ^ 2 ≤ ∑ v ∈ s, b v z ^ 2 := by
      obtain ⟨v₀, hv₀, hbv₀⟩ := hattain z
      rw [← Finset.add_sum_erase _ _ hv₀, hbv₀]
      have hrest : ∑ _v ∈ s.erase v₀, q ^ 2 * M z ^ 2 ≤ ∑ v ∈ s.erase v₀, b v z ^ 2 := by
        refine Finset.sum_le_sum fun v hv => ?_
        have hvs := Finset.mem_of_mem_erase hv
        exact (mul_pow q (M z) 2).symm.trans_le
          (pow_le_pow_left₀ (mul_nonneg hq0.le (hM_nn z)) (hcone_lo v hvs z) 2)
      have herase_card : ((s.erase v₀).card : ℝ) = k - 1 := by
        rw [Finset.card_erase_of_mem hv₀, Nat.cast_sub (by omega), Nat.cast_one]
      have hconst : ∑ _v ∈ s.erase v₀, q ^ 2 * M z ^ 2 = (k - 1) * q ^ 2 * M z ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, herase_card, mul_assoc]
      linarith
    have hsum_b : (1 + (k - 1) * q ^ 2) * ‖M‖ ^ 2 ≤ ∑ v ∈ s, ‖b v‖ ^ 2 := by
      simp_rw [EuclideanSpace.real_norm_sq_eq]
      rw [Finset.mul_sum, Finset.sum_comm]
      exact Finset.sum_le_sum fun z _ => hcoord z
    have hkx₀ : k * x₀ ^ 2 = 1 + (k - 1) * q ^ 2 := by
      rw [hx₀_sq]
      dsimp only [Q₀]
      field_simp
    calc k * x₀ ^ 2
        = ((1 + (k - 1) * q ^ 2) * ‖M‖ ^ 2) / ‖M‖ ^ 2 := by
          rw [hkx₀, mul_div_cancel_right₀ _ hM_sq_pos.ne']
      _ ≤ (∑ v ∈ s, ‖b v‖ ^ 2) / ‖M‖ ^ 2 := div_le_div_of_nonneg_right hsum_b hM_sq_pos.le
      _ = ∑ v ∈ s, x v ^ 2 := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun v _ => (div_pow (‖b v‖) ‖M‖ 2).symm
  have hsum_tang : k * ((x₀ + q / x₀) / (1 + q)) ≤ ∑ v ∈ s, ⟪u v, w⟫ := by
    set slope := (x₀ ^ 2 - q) / (2 * x₀ ^ 3)
    have hslope_nn : 0 ≤ slope := div_nonneg (sub_nonneg.mpr (hx₀_sq ▸ htan_lo)) (by positivity)
    have hpt (v : κ) (hv : v ∈ s) :
        ((x₀ + q / x₀) + slope * (x v ^ 2 - x₀ ^ 2)) / (1 + q) ≤ ⟪u v, w⟫ :=
      (div_le_div_of_nonneg_right (tangent_le_add_div hq0 hx₀_pos (hx_pos v hv) (hx_le_one v hv)
        (hx₀_sq ▸ htan_lo) (by simpa only [hx₀_sq] using htan_hi)) (by positivity)).trans
        (hinner_ge v hv)
    calc k * ((x₀ + q / x₀) / (1 + q))
        ≤ (k * (x₀ + q / x₀) + slope * ((∑ v ∈ s, x v ^ 2) - k * x₀ ^ 2)) / (1 + q) := by
          rw [add_div (k * (x₀ + q / x₀)), mul_div_assoc]
          have hnn : 0 ≤ slope * ((∑ v ∈ s, x v ^ 2) - k * x₀ ^ 2) / (1 + q) :=
            div_nonneg (mul_nonneg hslope_nn (sub_nonneg.mpr hsum_x_sq)) (by positivity)
          linarith [hnn]
      _ = ∑ v ∈ s, ((x₀ + q / x₀) + slope * (x v ^ 2 - x₀ ^ 2)) / (1 + q) := by
          rw [← Finset.sum_div]
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
            Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ s, ⟪u v, w⟫ := Finset.sum_le_sum hpt
  have hsimp_tang : k * ((x₀ + q / x₀) / (1 + q)) = (1 + (k - 1) * q) / x₀ := by
    have hnum_id : k * (x₀ ^ 2 + q) = (1 + q) * (1 + (k - 1) * q) := by
      rw [hx₀_sq]
      dsimp only [Q₀]
      field_simp
      ring
    have h1 : x₀ + q / x₀ = (x₀ ^ 2 + q) / x₀ := by field_simp
    rw [h1]
    field_simp
    linarith
  rw [hsimp_tang] at hsum_tang
  have hnorm_sum : (1 + (k - 1) * q) / x₀ ≤ ‖∑ v ∈ s, u v‖ :=
    hsum_tang.trans ((sum_inner (𝕜 := ℝ) s u w).symm.trans_le
      ((real_inner_le_norm _ w).trans_eq (by rw [hw_norm, mul_one])))
  have h0_lhs : 0 ≤ (1 + (k - 1) * q) / x₀ := by
    have : 0 ≤ k - 1 := by linarith
    positivity
  have hsq_sum := mul_le_mul hnorm_sum hnorm_sum h0_lhs (h0_lhs.trans hnorm_sum)
  have hexp := norm_sum_sq_real s u
  have hdiag : ∑ v ∈ s, ‖u v‖ ^ 2 = k := by
    calc ∑ v ∈ s, ‖u v‖ ^ 2 = ∑ _v ∈ s, (1 : ℝ) :=
          Finset.sum_congr rfl fun v hv => by rw [hu_norm v hv, one_pow]
      _ = k := by rw [Finset.sum_const, nsmul_one]
  have hident : ((1 + (k - 1) * q) / x₀) ^ 2 - k =
      k * (k - 1) * ((2 * q + (k - 2) * q ^ 2) / (1 + (k - 1) * q ^ 2)) := by
    rw [div_pow, hx₀_sq]
    dsimp only [Q₀]
    have hden_pos : 0 < 1 + (k - 1) * q ^ 2 := by
      have : 0 ≤ k - 1 := by linarith
      positivity
    field_simp
    ring
  linarith [sq (‖∑ v ∈ s, u v‖), sq ((1 + (k - 1) * q) / x₀)]

/-- **Combinatorial Sheppard bound for hyperedge straddling.** If `s : Finset V` (`2 ≤ s.card`) has
unit vectors `u : V → EuclideanSpace ℝ V` whose angles over `s.offDiag` sum to at most
`s.card * (s.card - 1) * θ_avg`, then for every threshold `t : ℝ`, `s` straddles `t` under
standard Gaussian projections with probability at most `(s.card / (2 π)) * θ_avg`. -/
private theorem measureReal_straddlesOn_le_of_sum_angle {V : Type*} [Fintype V]
    {s : Finset V} (hs : 2 ≤ s.card) {u : V → EuclideanSpace ℝ V} (hu : ∀ v ∈ s, ‖u v‖ = 1)
    {θ_avg : ℝ}
    (hangle : open Classical in ∑ p ∈ s.offDiag, InnerProductGeometry.angle (u p.1) (u p.2) ≤
      (s.card : ℝ) * ((s.card : ℝ) - 1) * θ_avg)
    (t : ℝ) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real
        {ω | StraddlesOn (fun v => ⟪u v, WithLp.toLp 2 ω⟫) t ↑s} ≤
      (s.card : ℝ) / (2 * π) * θ_avg := by
  classical
  set P := Measure.pi fun _ : V => gaussianReal 0 1
  let score : (V → ℝ) → V → ℝ := fun ω v => ⟪u v, WithLp.toLp 2 ω⟫
  have hmeas_score (v : V) : Measurable fun ω : V → ℝ => score ω v := by
    dsimp only [score]
    fun_prop
  set E : Set (V → ℝ) := {ω | StraddlesOn (score ω) t ↑s}
  have hmeas_E : MeasurableSet E := by
    have heq : E = (⋃ v ∈ s, {ω | score ω v < t}) ∩ (⋃ v ∈ s, {ω | t ≤ score ω v}) := by
      ext ω
      simp [E, StraddlesOn]
    rw [heq]
    exact (s.measurableSet_biUnion fun v _ =>
      measurableSet_lt (hmeas_score v) measurable_const).inter
      (s.measurableSet_biUnion fun v _ => measurableSet_le measurable_const (hmeas_score v))
  let sepSet (p : V × V) : Set (V → ℝ) := {ω | t ∈ Ι (score ω p.1) (score ω p.2)}
  have hmeas_sep (p : V × V) : MeasurableSet (sepSet p) :=
    measurableSet_setOf_mem_uIoc (hmeas_score p.1) (hmeas_score p.2) t
  have hpt (ω : V → ℝ) :
      2 * ((s.card : ℝ) - 1) * E.indicator (fun _ => (1 : ℝ)) ω ≤
        ∑ p ∈ s.offDiag, (sepSet p).indicator (fun _ => (1 : ℝ)) ω := by
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]
      obtain ⟨⟨u₁, hu₁s, hu₁lt⟩, ⟨u₂, hu₂s, hu₂ge⟩⟩ := hω
      let L := s.filter fun v => score ω v < t
      let U := s.filter fun v => t ≤ score ω v
      have hL_pos : 1 ≤ L.card :=
        Finset.card_pos.mpr ⟨u₁, Finset.mem_filter.mpr ⟨hu₁s, hu₁lt⟩⟩
      have hU_pos : 1 ≤ U.card :=
        Finset.card_pos.mpr ⟨u₂, Finset.mem_filter.mpr ⟨hu₂s, hu₂ge⟩⟩
      have hLU_card : L.card + U.card = s.card := by
        have hpart := Finset.card_filter_add_card_filter_not (s := s) (fun v => score ω v < t)
        have hU_eq : (s.filter fun v => ¬score ω v < t) = U := by
          ext v
          simp [U]
        rwa [hU_eq] at hpart
      let active := s.offDiag.filter fun p => t ∈ Ι (score ω p.1) (score ω p.2)
      have hsub1 : L ×ˢ U ⊆ active := by
        rintro ⟨a, b⟩ hab
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
        obtain ⟨has, halt⟩ := Finset.mem_filter.mp ha
        obtain ⟨hbs, hbge⟩ := Finset.mem_filter.mp hb
        have hab_ne : a ≠ b := fun h => by subst h; linarith
        dsimp only [active]
        refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨has, hbs, hab_ne⟩, ?_⟩
        rw [uIoc_of_le (halt.le.trans hbge)]
        exact ⟨halt, hbge⟩
      have hsub2 : U ×ˢ L ⊆ active := by
        rintro ⟨b, a⟩ hba
        obtain ⟨hb, ha⟩ := Finset.mem_product.mp hba
        obtain ⟨hbs, hbge⟩ := Finset.mem_filter.mp hb
        obtain ⟨has, halt⟩ := Finset.mem_filter.mp ha
        have hba_ne : b ≠ a := fun h => by subst h; linarith
        dsimp only [active]
        refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hbs, has, hba_ne⟩, ?_⟩
        rw [uIoc_comm, uIoc_of_le (halt.le.trans hbge)]
        exact ⟨halt, hbge⟩
      have hdisj : Disjoint (L ×ˢ U) (U ×ˢ L) := by
        rw [Finset.disjoint_left]
        rintro ⟨a, b⟩ h1 h2
        have halt := (Finset.mem_filter.mp (Finset.mem_product.mp h1).1).2
        have hage := (Finset.mem_filter.mp (Finset.mem_product.mp h2).1).2
        linarith
      have hcard_act : 2 * (s.card - 1) ≤ active.card := by
        have hs1 : s.card = (s.card - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
        calc 2 * (s.card - 1) ≤ L.card * U.card + U.card * L.card := by nlinarith
          _ = (L ×ˢ U ∪ U ×ˢ L).card := by
              rw [Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product]
          _ ≤ active.card := Finset.card_le_card (Finset.union_subset hsub1 hsub2)
      have hsum_ind : ∑ p ∈ s.offDiag, (sepSet p).indicator (fun _ => (1 : ℝ)) ω = active.card := by
        have hcongr : ∑ p ∈ s.offDiag, (sepSet p).indicator (fun _ => (1 : ℝ)) ω =
            ∑ p ∈ s.offDiag, if t ∈ Ι (score ω p.1) (score ω p.2) then (1 : ℝ) else 0 :=
          Finset.sum_congr rfl fun p _ => by simp [sepSet, indicator]
        rw [hcongr, Finset.sum_boole]
      rw [hsum_ind, mul_one]
      have hcast : (2 : ℝ) * ((s.card : ℝ) - 1) = ((2 * (s.card - 1) : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast]
      exact_mod_cast hcard_act
    · rw [indicator_of_notMem hω, mul_zero]
      exact Finset.sum_nonneg fun p _ => indicator_nonneg (fun _ _ => zero_le_one) ω
  have hint_lhs : Integrable (fun ω => 2 * ((s.card : ℝ) - 1) *
      E.indicator (fun _ => (1 : ℝ)) ω) P :=
    ((integrable_const (1 : ℝ)).indicator hmeas_E).const_mul _
  have hint_rhs : ∀ p ∈ s.offDiag,
      Integrable (fun ω => (sepSet p).indicator (fun _ => (1 : ℝ)) ω) P :=
    fun p _ => (integrable_const (1 : ℝ)).indicator (hmeas_sep p)
  have hint_le := integral_mono hint_lhs (integrable_finsetSum _ hint_rhs) hpt
  rw [integral_const_mul, integral_indicator_const _ hmeas_E, smul_eq_mul, mul_one,
    integral_finsetSum _ hint_rhs] at hint_le
  have hsum_prob : ∑ p ∈ s.offDiag, ∫ ω, (sepSet p).indicator (fun _ => (1 : ℝ)) ω ∂P ≤
      ((s.card : ℝ) * ((s.card : ℝ) - 1) * θ_avg) / π := by
    calc ∑ p ∈ s.offDiag, ∫ ω, (sepSet p).indicator (fun _ => (1 : ℝ)) ω ∂P
        = ∑ p ∈ s.offDiag, P.real (sepSet p) :=
          Finset.sum_congr rfl fun p _ => by
            rw [integral_indicator_const _ (hmeas_sep p), smul_eq_mul, mul_one]
      _ ≤ ∑ p ∈ s.offDiag, InnerProductGeometry.angle (u p.1) (u p.2) / π :=
          Finset.sum_le_sum fun p hp => by
            obtain ⟨h1, h2, -⟩ := Finset.mem_offDiag.mp hp
            exact Gaussian.measureReal_mem_uIoc_le ((hu p.1 h1).trans (hu p.2 h2).symm) t
      _ = (∑ p ∈ s.offDiag, InnerProductGeometry.angle (u p.1) (u p.2)) / π :=
          (Finset.sum_div _ _ _).symm
      _ ≤ ((s.card : ℝ) * ((s.card : ℝ) - 1) * θ_avg) / π :=
          div_le_div_of_nonneg_right hangle pi_pos.le
  have hk1_pos : (0 : ℝ) < (s.card : ℝ) - 1 := by
    have : (2 : ℝ) ≤ s.card := by exact_mod_cast hs
    linarith
  have hcomb := hint_le.trans hsum_prob
  have htarget : P.real E * (2 * π) ≤ s.card * θ_avg := by
    have hmul := mul_le_mul_of_nonneg_right hcomb pi_pos.le
    rw [div_mul_cancel₀ _ pi_pos.ne'] at hmul
    nlinarith
  calc P.real E ≤ (s.card * θ_avg) / (2 * π) :=
        (le_div_iff₀ (by positivity)).mpr htarget
    _ = (s.card : ℝ) / (2 * π) * θ_avg := by ring

end Helpers

/-! ### Pruned bipartite incidence graph and `walkMax` kernel -/

section BipartiteKernel

variable {σ : Signature} {n : ℕ} (c : Circuit σ n 1) (K₀ : ℕ)

/-- Live signals whose hyperedge has cardinality in `[2, K₀]`. -/
private abbrev PrunedEdge : Type :=
  {w : LiveSignal c // 2 ≤ (hyperEdge c w).card ∧ (hyperEdge c w).card ≤ K₀}

/-- Nodes of the pruned bipartite hypergraph: `HyperNode c ⊕ PrunedEdge c K₀`. -/
private abbrev BipNode : Type :=
  HyperNode c ⊕ PrunedEdge c K₀

/-- Incidence adjacency on `BipNode c K₀`. -/
private def bipAdj : BipNode c K₀ → BipNode c K₀ → Prop
  | .inl v, .inr e => v ∈ hyperEdge c e.1
  | .inr e, .inl v => v ∈ hyperEdge c e.1
  | _, _ => False

private theorem bipAdj_symm {x y : BipNode c K₀} (h : bipAdj c K₀ x y) : bipAdj c K₀ y x := by
  cases x <;> cases y <;> exact h

private theorem bipAdj_irrefl (x : BipNode c K₀) : ¬bipAdj c K₀ x x := by
  cases x <;> simp [bipAdj]

/-- Simple graph on `BipNode c K₀` induced by `bipAdj`. -/
private def bipSimpleGraph : SimpleGraph (BipNode c K₀) where
  Adj := bipAdj c K₀
  symm := ⟨fun _ _ h => bipAdj_symm c K₀ h⟩
  loopless := ⟨bipAdj_irrefl c K₀⟩

/-- Non-backtracking branching bound on `BipNode c K₀`: `r` at circuit nodes and `|e| - 1` at
pruned hyperedges. -/
private noncomputable def bipBranch (r : ℕ) : BipNode c K₀ → ℕ
  | .inl _ => r
  | .inr e => (hyperEdge c e.1).card - 1

private theorem one_le_bipBranch {r : ℕ} (hr : 2 ≤ r) (x : BipNode c K₀) :
    1 ≤ bipBranch c K₀ r x := by
  rcases x with v | e
  · exact Nat.one_le_of_lt hr
  · have := e.2.1
    dsimp only [bipBranch]
    omega

/-- Adaptive step attenuation `θ / √(√(br x) * √(br y))` along an incidence step `(x, y)`. -/
private noncomputable def stepWeight (r : ℕ) (θ : ℝ) (x y : BipNode c K₀) : ℝ :=
  θ / √(√(bipBranch c K₀ r x : ℝ) * √(bipBranch c K₀ r y : ℝ))

private theorem stepWeight_nonneg (r : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (x y : BipNode c K₀) :
    0 ≤ stepWeight c K₀ r θ x y :=
  div_nonneg hθ (sqrt_nonneg _)

private theorem stepWeight_le {r : ℕ} (hr : 2 ≤ r) {θ : ℝ} (hθ : 0 ≤ θ) (x y : BipNode c K₀) :
    stepWeight c K₀ r θ x y ≤ θ := by
  have hx1 : (1 : ℝ) ≤ (bipBranch c K₀ r x : ℝ) := by exact_mod_cast one_le_bipBranch c K₀ hr x
  have hy1 : (1 : ℝ) ≤ (bipBranch c K₀ r y : ℝ) := by exact_mod_cast one_le_bipBranch c K₀ hr y
  have hx : (1 : ℝ) ≤ √(bipBranch c K₀ r x : ℝ) :=
    (le_sqrt zero_le_one (Nat.cast_nonneg _)).mpr (by linarith)
  have hy : (1 : ℝ) ≤ √(bipBranch c K₀ r y : ℝ) :=
    (le_sqrt zero_le_one (Nat.cast_nonneg _)).mpr (by linarith)
  have hden : (1 : ℝ) ≤ √(√(bipBranch c K₀ r x : ℝ) * √(bipBranch c K₀ r y : ℝ)) :=
    (le_sqrt zero_le_one (by positivity)).mpr (by nlinarith)
  exact div_le_self hθ hden

private theorem stepWeight_sq (r : ℕ) (θ : ℝ) (x y : BipNode c K₀) :
    stepWeight c K₀ r θ x y ^ 2 =
      θ ^ 2 / (√(bipBranch c K₀ r x : ℝ) * √(bipBranch c K₀ r y : ℝ)) := by
  rw [stepWeight, div_pow, sq_sqrt (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))]

open Classical in
/-- Radius-`m` walk-maximum kernel on `BipNode c K₀ → HyperNode c → ℝ`. -/
private noncomputable def walkMax (r : ℕ) (θ : ℝ) : ℕ → BipNode c K₀ → HyperNode c → ℝ
  | 0, .inl v, z => if v = z then 1 else 0
  | 0, .inr _, _ => 0
  | m + 1, x, z =>
    (insert (walkMax r θ m x z)
      ((Finset.univ.filter (bipAdj c K₀ x)).image fun y =>
        stepWeight c K₀ r θ x y * walkMax r θ m y z)).max' (Finset.insert_nonempty _ _)

private theorem walkMax_mono_step (r : ℕ) (θ : ℝ) (m : ℕ) (x : BipNode c K₀) (z : HyperNode c) :
    walkMax c K₀ r θ m x z ≤ walkMax c K₀ r θ (m + 1) x z := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)

private theorem walkMax_mono (r : ℕ) (θ : ℝ) {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) (x : BipNode c K₀)
    (z : HyperNode c) : walkMax c K₀ r θ m₁ x z ≤ walkMax c K₀ r θ m₂ x z := by
  induction hm with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (walkMax_mono_step c K₀ r θ _ x z)

private theorem walkMax_nonneg (r : ℕ) {θ : ℝ} (_hθ : 0 ≤ θ) (m : ℕ) (x : BipNode c K₀)
    (z : HyperNode c) : 0 ≤ walkMax c K₀ r θ m x z := by
  refine le_trans ?_ (walkMax_mono c K₀ r θ (Nat.zero_le m) x z)
  cases x with
  | inl v => dsimp only [walkMax]; split_ifs <;> norm_num
  | inr _ => exact le_rfl

private theorem step_mul_walkMax_le (r : ℕ) (θ : ℝ) (m : ℕ) {x y : BipNode c K₀}
    (hadj : bipAdj c K₀ x y) (z : HyperNode c) :
    stepWeight c K₀ r θ x y * walkMax c K₀ r θ m y z ≤ walkMax c K₀ r θ (m + 1) x z := by
  classical
  let img : Finset ℝ := (Finset.univ.filter (bipAdj c K₀ x)).image fun y' =>
    stepWeight c K₀ r θ x y' * walkMax c K₀ r θ m y' z
  have hmem : stepWeight c K₀ r θ x y * walkMax c K₀ r θ m y z ∈
      insert (walkMax c K₀ r θ m x z) img :=
    Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hadj⟩, rfl⟩)
  exact Finset.le_max' _ _ hmem

private theorem exists_step_of_walkMax_lt (r : ℕ) (θ : ℝ) (m : ℕ) {x : BipNode c K₀}
    {z : HyperNode c} (hlt : walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z) :
    ∃ y : BipNode c K₀, bipAdj c K₀ x y ∧
      walkMax c K₀ r θ (m + 1) x z = stepWeight c K₀ r θ x y * walkMax c K₀ r θ m y z := by
  classical
  have hmem := Finset.max'_mem (insert (walkMax c K₀ r θ m x z)
    ((Finset.univ.filter (bipAdj c K₀ x)).image fun y =>
      stepWeight c K₀ r θ x y * walkMax c K₀ r θ m y z)) (Finset.insert_nonempty _ _)
  change walkMax c K₀ r θ (m + 1) x z ∈ _ at hmem
  rcases Finset.mem_insert.mp hmem with heq | himg
  · exact absurd heq hlt.ne'
  · obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp himg
    exact ⟨y, (Finset.mem_filter.mp hy).2, heq.symm⟩

private theorem one_le_norm_walkMax (r : ℕ) (θ : ℝ) (m : ℕ) (v : HyperNode c) :
    1 ≤ ‖WithLp.toLp 2 (walkMax c K₀ r θ m (.inl v))‖ := by
  have hv1 : 1 ≤ walkMax c K₀ r θ m (.inl v) v := by
    simpa [walkMax] using walkMax_mono c K₀ r θ (Nat.zero_le m) (.inl v) v
  have hsq : 1 ≤ ‖WithLp.toLp 2 (walkMax c K₀ r θ m (.inl v))‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc (1 : ℝ) ≤ walkMax c K₀ r θ m (.inl v) v ^ 2 := by nlinarith
      _ ≤ ∑ z, walkMax c K₀ r θ m (.inl v) z ^ 2 :=
          Finset.single_le_sum (fun z _ => sq_nonneg _) (Finset.mem_univ v)
  nlinarith [norm_nonneg (WithLp.toLp 2 (walkMax c K₀ r θ m (.inl v)))]

/-! ### Degree, support, and non-backtracking boundary-mass bounds -/

open Classical in
private theorem card_bipAdj_inl_le {r : ℕ} (hfan : c.FanInAtMost r) (v : HyperNode c) :
    (Finset.univ.filter (bipAdj c K₀ (.inl v))).card ≤ r + 1 := by
  let f : {y : BipNode c K₀ // y ∈ Finset.univ.filter (bipAdj c K₀ (.inl v))} →
      {w : LiveSignal c // v ∈ hyperEdge c w} := fun ⟨y, hy⟩ =>
    match y, (Finset.mem_filter.mp hy).2 with | .inr e', hadj => ⟨e'.1, hadj⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨u₁ | e₁, h₁⟩ ⟨u₂ | e₂, h₂⟩ h
    · exact False.elim (Finset.mem_filter.mp h₁).2
    · exact False.elim (Finset.mem_filter.mp h₁).2
    · exact False.elim (Finset.mem_filter.mp h₂).2
    · have he : e₁.1 = e₂.1 := congrArg (Subtype.val : {w // v ∈ hyperEdge c w} → _) h
      exact Subtype.ext (congrArg Sum.inr (Subtype.ext he))
  have hcard := Fintype.card_le_of_injective f hf_inj
  rw [Fintype.card_coe, Fintype.card_subtype] at hcard
  exact hcard.trans (card_signals_at_node_le hfan v)

open Classical in
private theorem card_bipAdj_inr_eq (e : PrunedEdge c K₀) :
    (Finset.univ.filter (bipAdj c K₀ (.inr e))).card = (hyperEdge c e.1).card := by
  refine Finset.card_bij (fun y hy => match y, (Finset.mem_filter.mp hy).2 with
    | .inl v, _ => v) (fun y hy => ?_) (fun y₁ hy₁ y₂ hy₂ h => ?_) (fun v hv => ?_)
  · rcases y with v | e'
    · exact (Finset.mem_filter.mp hy).2
    · exact False.elim (Finset.mem_filter.mp hy).2
  · rcases y₁ with v₁ | e₁ <;> rcases y₂ with v₂ | e₂
    · exact congrArg Sum.inl h
    · exact False.elim (Finset.mem_filter.mp hy₂).2
    · exact False.elim (Finset.mem_filter.mp hy₁).2
    · exact False.elim (Finset.mem_filter.mp hy₁).2
  · exact ⟨.inl v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩

open Classical in
private theorem card_bipAdj_le {r : ℕ} (hfan : c.FanInAtMost r) (x : BipNode c K₀) :
    (Finset.univ.filter (bipAdj c K₀ x)).card ≤ max (r + 1) K₀ := by
  rcases x with v | e
  · exact (card_bipAdj_inl_le c K₀ hfan v).trans (le_max_left _ _)
  · exact ((card_bipAdj_inr_eq c K₀ e).trans_le e.2.2).trans (le_max_right _ _)

open Classical in
private theorem card_bipAdj_ne_le {r : ℕ} (hfan : c.FanInAtMost r) {prev x : BipNode c K₀}
    (hprev : bipAdj c K₀ prev x) :
    (Finset.univ.filter fun y => bipAdj c K₀ x y ∧ y ≠ prev).card ≤ bipBranch c K₀ r x := by
  have hmem : prev ∈ Finset.univ.filter (bipAdj c K₀ x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, bipAdj_symm c K₀ hprev⟩
  have hsub : (Finset.univ.filter fun y => bipAdj c K₀ x y ∧ y ≠ prev) ⊆
      (Finset.univ.filter (bipAdj c K₀ x)).erase prev := by
    intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    exact Finset.mem_erase.mpr ⟨hy'.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'.1⟩⟩
  have hcard_le := (Finset.card_le_card hsub).trans (Finset.card_erase_of_mem hmem).le
  rcases x with v | e
  · have := card_bipAdj_inl_le c K₀ hfan v
    dsimp only [bipBranch]
    omega
  · have := card_bipAdj_inr_eq c K₀ e
    dsimp only [bipBranch]
    omega

private theorem degree_bipSimpleGraph_le {r : ℕ} (hfan : c.FanInAtMost r)
    [DecidableRel (bipSimpleGraph c K₀).Adj] (x : BipNode c K₀) :
    (bipSimpleGraph c K₀).degree x ≤ max (r + 1) K₀ := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have heq : (bipSimpleGraph c K₀).neighborFinset x = Finset.univ.filter (bipAdj c K₀ x) := by
    ext y
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ y, h⟩, fun h => h.2⟩
  rw [heq]
  exact card_bipAdj_le c K₀ hfan x

private theorem edist_le_of_walkMax_ne_zero {r : ℕ} {θ : ℝ} :
    ∀ {m : ℕ} {x : BipNode c K₀} {z : HyperNode c},
      walkMax c K₀ r θ m x z ≠ 0 → (bipSimpleGraph c K₀).edist x (.inl z) ≤ m
  | 0, .inl v, z, hne => by
    dsimp only [walkMax] at hne
    by_cases h : v = z
    · subst h; simp
    · rw [ite_eq_right h] at hne
      exact absurd rfl hne
  | 0, .inr _, _, hne => absurd rfl hne
  | m + 1, x, z, hne => by
    by_cases hprev : walkMax c K₀ r θ m x z = walkMax c K₀ r θ (m + 1) x z
    · exact (edist_le_of_walkMax_ne_zero (hprev.symm ▸ hne)).trans
        (by exact_mod_cast Nat.le_succ m)
    · have hlt := lt_of_le_of_ne (walkMax_mono_step c K₀ r θ m x z) hprev
      obtain ⟨y, hadj, heq⟩ := exists_step_of_walkMax_lt c K₀ r θ m hlt
      have hy_ne : walkMax c K₀ r θ m y z ≠ 0 := by
        intro hy0
        rw [heq, hy0, mul_zero] at hne
        exact hne rfl
      have htri : (bipSimpleGraph c K₀).edist x (.inl z) ≤
          (bipSimpleGraph c K₀).edist y (.inl z) + 1 :=
        SimpleGraph.Adj.edist_le_edist_add_one (G := bipSimpleGraph c K₀) hadj
          (Sum.inl z : BipNode c K₀)
      calc (bipSimpleGraph c K₀).edist x (.inl z)
          ≤ (bipSimpleGraph c K₀).edist y (.inl z) + 1 := htri
        _ ≤ (m : ℕ∞) + 1 := add_le_add_left (edist_le_of_walkMax_ne_zero hy_ne) 1
        _ = ((m + 1 : ℕ) : ℕ∞) := by push_cast; rfl

open Classical in
/-- Non-backtracking edge-step boundary mass: coordinates `z` at which `walkMax (m + 1) prev z`
strictly improves over `walkMax m prev z` via the first step `prev → x`. -/
private noncomputable def edgeBoundaryMass (r : ℕ) (θ : ℝ) (m : ℕ) (prev x : BipNode c K₀) : ℝ :=
  ∑ z ∈ Finset.univ.filter (fun z : HyperNode c =>
      bipAdj c K₀ prev x ∧
      walkMax c K₀ r θ m prev z < walkMax c K₀ r θ (m + 1) prev z ∧
      walkMax c K₀ r θ (m + 1) prev z = stepWeight c K₀ r θ prev x * walkMax c K₀ r θ m x z),
    walkMax c K₀ r θ m x z ^ 2 / √(bipBranch c K₀ r x : ℝ)

private theorem edgeBoundaryMass_le {r : ℕ} (hr : 2 ≤ r) (hfan : c.FanInAtMost r) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∀ (m : ℕ) (prev x : BipNode c K₀), edgeBoundaryMass c K₀ r θ m prev x ≤ θ ^ (2 * m)
  | 0, prev, x => by
    classical
    rw [Nat.mul_zero, pow_zero]
    rcases x with v | e
    · have hsub : (Finset.univ.filter fun z : HyperNode c =>
          bipAdj c K₀ prev (.inl v) ∧
          walkMax c K₀ r θ 0 prev z < walkMax c K₀ r θ 1 prev z ∧
          walkMax c K₀ r θ 1 prev z = stepWeight c K₀ r θ prev (.inl v) *
            walkMax c K₀ r θ 0 (.inl v) z) ⊆ {v} := by
        intro z hz
        have hlt := (Finset.mem_filter.mp hz).2.2.1
        have heq := (Finset.mem_filter.mp hz).2.2.2
        have h0 : 0 ≤ walkMax c K₀ r θ 0 prev z := walkMax_nonneg c K₀ r hθ0.le 0 prev z
        refine Finset.mem_singleton.mpr ?_
        by_contra hzv
        have hzv' : v ≠ z := fun h => hzv h.symm
        have hw0 : walkMax c K₀ r θ 0 (.inl v) z = 0 := by
          dsimp only [walkMax]
          exact ite_eq_right hzv'
        rw [hw0, mul_zero] at heq
        linarith
      calc edgeBoundaryMass c K₀ r θ 0 prev (.inl v)
          ≤ ∑ z ∈ ({v} : Finset (HyperNode c)),
              walkMax c K₀ r θ 0 (.inl v) z ^ 2 / √(bipBranch c K₀ r (.inl v) : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ = 1 / √(r : ℝ) := by simp [walkMax, bipBranch]
        _ ≤ 1 := div_le_one_of_le₀
            ((le_sqrt zero_le_one (Nat.cast_nonneg _)).mpr
              (by norm_num; exact_mod_cast Nat.one_le_of_lt hr))
            (sqrt_nonneg _)
    · have hemp : (Finset.univ.filter fun z : HyperNode c =>
          bipAdj c K₀ prev (.inr e) ∧
          walkMax c K₀ r θ 0 prev z < walkMax c K₀ r θ 1 prev z ∧
          walkMax c K₀ r θ 1 prev z = stepWeight c K₀ r θ prev (.inr e) *
            walkMax c K₀ r θ 0 (.inr e) z) = ∅ := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
          not_and]
        intro _ hlt heq
        have h0 : 0 ≤ walkMax c K₀ r θ 0 prev z := walkMax_nonneg c K₀ r hθ0.le 0 prev z
        have hw0 : walkMax c K₀ r θ 0 (.inr e) z = 0 := rfl
        rw [hw0, mul_zero] at heq
        linarith
      simp [edgeBoundaryMass, hemp]
  | m + 1, prev, x => by
    classical
    by_cases hpx : bipAdj c K₀ prev x
    · let S := Finset.univ.filter fun z : HyperNode c =>
        bipAdj c K₀ prev x ∧
        walkMax c K₀ r θ (m + 1) prev z < walkMax c K₀ r θ (m + 2) prev z ∧
        walkMax c K₀ r θ (m + 2) prev z =
          stepWeight c K₀ r θ prev x * walkMax c K₀ r θ (m + 1) x z
      let N : Finset (BipNode c K₀) := Finset.univ.filter fun y => bipAdj c K₀ x y ∧ y ≠ prev
      let Fy (y : BipNode c K₀) : Finset (HyperNode c) := Finset.univ.filter fun z =>
        bipAdj c K₀ x y ∧
        walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z ∧
        walkMax c K₀ r θ (m + 1) x z = stepWeight c K₀ r θ x y * walkMax c K₀ r θ m y z
      have hsub : S ⊆ N.biUnion Fy := by
        intro z hz
        have hlt2 := (Finset.mem_filter.mp hz).2.2.1
        have heq2 := (Finset.mem_filter.mp hz).2.2.2
        have hlt1 : walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z := by
          by_contra! hle
          have hstep := step_mul_walkMax_le c K₀ r θ m hpx z
          have hmul := mul_le_mul_of_nonneg_left hle (stepWeight_nonneg c K₀ r hθ0.le prev x)
          linarith
        obtain ⟨y, hadj_xy, heq1⟩ := exists_step_of_walkMax_lt c K₀ r θ m hlt1
        have hy_ne : y ≠ prev := by
          rintro rfl
          have hsw1 := stepWeight_le c K₀ hr hθ0.le y x
          have hsw2 := stepWeight_le c K₀ hr hθ0.le x y
          have hw0 := walkMax_nonneg c K₀ r hθ0.le m y z
          have hmono := walkMax_mono_step c K₀ r θ m y z
          have hprod : stepWeight c K₀ r θ y x *
              (stepWeight c K₀ r θ x y * walkMax c K₀ r θ m y z) ≤
              walkMax c K₀ r θ m y z := by
            have h1 : stepWeight c K₀ r θ x y * walkMax c K₀ r θ m y z ≤
                1 * walkMax c K₀ r θ m y z :=
              mul_le_mul_of_nonneg_right (hsw2.trans hθ1) hw0
            have h2 : stepWeight c K₀ r θ y x * walkMax c K₀ r θ m y z ≤
                1 * walkMax c K₀ r θ m y z :=
              mul_le_mul_of_nonneg_right (hsw1.trans hθ1) hw0
            nlinarith [stepWeight_nonneg c K₀ r hθ0.le y x]
          rw [heq1] at heq2
          linarith
        exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hadj_xy, hy_ne⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ z, hadj_xy, hlt1, heq1⟩⟩
      have hbr_pos : (0 : ℝ) < bipBranch c K₀ r x := by
        exact_mod_cast one_le_bipBranch c K₀ hr x
      have hterm (y : BipNode c K₀) :
          ∑ z ∈ Fy y, walkMax c K₀ r θ (m + 1) x z ^ 2 / √(bipBranch c K₀ r x : ℝ) ≤
            (θ ^ 2 / (bipBranch c K₀ r x : ℝ)) * θ ^ (2 * m) := by
        have hrew : ∑ z ∈ Fy y, walkMax c K₀ r θ (m + 1) x z ^ 2 / √(bipBranch c K₀ r x : ℝ) =
            (θ ^ 2 / (bipBranch c K₀ r x : ℝ)) * edgeBoundaryMass c K₀ r θ m x y := by
          rw [edgeBoundaryMass, Finset.mul_sum]
          refine Finset.sum_congr rfl fun z hz => ?_
          have heq1 := (Finset.mem_filter.mp hz).2.2.2
          rw [heq1, mul_pow, stepWeight_sq]
          have hsx_ne : √(bipBranch c K₀ r x : ℝ) ≠ 0 := (sqrt_pos.mpr hbr_pos).ne'
          by_cases hby : (bipBranch c K₀ r y : ℝ) = 0
          · simp [hby]
          · have hsy_ne : √(bipBranch c K₀ r y : ℝ) ≠ 0 :=
              (sqrt_pos.mpr (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hby))).ne'
            field_simp
            rw [sq_sqrt hbr_pos.le]
            ring
        rw [hrew]
        exact mul_le_mul_of_nonneg_left (edgeBoundaryMass_le hr hfan hθ0 hθ1 m x y) (by positivity)
      calc edgeBoundaryMass c K₀ r θ (m + 1) prev x
          ≤ ∑ z ∈ N.biUnion Fy, walkMax c K₀ r θ (m + 1) x z ^ 2 / √(bipBranch c K₀ r x : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ ≤ ∑ y ∈ N, ∑ z ∈ Fy y, walkMax c K₀ r θ (m + 1) x z ^ 2 / √(bipBranch c K₀ r x : ℝ) := by
            clear hsub
            induction N using Finset.induction_on with
            | empty => simp
            | insert a s ha ih =>
              rw [Finset.biUnion_insert, Finset.sum_insert ha]
              exact (sum_union_le_of_nonneg fun _ => by positivity).trans (add_le_add le_rfl ih)
        _ ≤ ∑ _y ∈ N, (θ ^ 2 / (bipBranch c K₀ r x : ℝ)) * θ ^ (2 * m) :=
            Finset.sum_le_sum fun y _ => hterm y
        _ = N.card * ((θ ^ 2 / (bipBranch c K₀ r x : ℝ)) * θ ^ (2 * m)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (bipBranch c K₀ r x : ℝ) * ((θ ^ 2 / (bipBranch c K₀ r x : ℝ)) * θ ^ (2 * m)) := by
            gcongr
            exact_mod_cast card_bipAdj_ne_le c K₀ hfan hpx
        _ = θ ^ (2 * (m + 1)) := by
            have hne := hbr_pos.ne'
            field_simp
            ring
    · have hemp : (Finset.univ.filter fun z : HyperNode c =>
          bipAdj c K₀ prev x ∧
          walkMax c K₀ r θ (m + 1) prev z < walkMax c K₀ r θ (m + 2) prev z ∧
          walkMax c K₀ r θ (m + 2) prev z =
            stepWeight c K₀ r θ prev x * walkMax c K₀ r θ (m + 1) x z) = ∅ := by
        ext z
        simp [hpx]
      rw [edgeBoundaryMass, hemp, Finset.sum_empty]
      positivity

/-- **Non-backtracking boundary-mass bound:** for every `x : BipNode c K₀` and `m : ℕ`, the sum of
`walkMax (m + 1) x z ^ 2` over coordinates where step `m + 1` strictly improves `walkMax m x z` is
at most `max (r + 1) K₀ * θ ^ (2 (m + 1))`. -/
private theorem sum_sq_walkMax_strict_le {r : ℕ} (hr : 2 ≤ r) (hfan : c.FanInAtMost r) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (m : ℕ) (x : BipNode c K₀) :
    open Classical in
    ∑ z ∈ Finset.univ.filter (fun z => walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z),
      walkMax c K₀ r θ (m + 1) x z ^ 2 ≤
      (max (r + 1) K₀ : ℝ) * θ ^ (2 * (m + 1)) := by
  classical
  let N : Finset (BipNode c K₀) := Finset.univ.filter (bipAdj c K₀ x)
  let Fy (y : BipNode c K₀) : Finset (HyperNode c) := Finset.univ.filter fun z =>
    bipAdj c K₀ x y ∧
    walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z ∧
    walkMax c K₀ r θ (m + 1) x z = stepWeight c K₀ r θ x y * walkMax c K₀ r θ m y z
  have hsub : (Finset.univ.filter fun z =>
      walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z) ⊆ N.biUnion Fy := by
    intro z hz
    have hlt := (Finset.mem_filter.mp hz).2
    obtain ⟨y, hadj, heq⟩ := exists_step_of_walkMax_lt c K₀ r θ m hlt
    exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hadj⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ z, hadj, hlt, heq⟩⟩
  have hbr1 : (1 : ℝ) ≤ (bipBranch c K₀ r x : ℝ) := by exact_mod_cast one_le_bipBranch c K₀ hr x
  have h1_br : (1 : ℝ) ≤ √(bipBranch c K₀ r x : ℝ) :=
    (le_sqrt zero_le_one (Nat.cast_nonneg _)).mpr (by linarith)
  have hterm (y : BipNode c K₀) :
      ∑ z ∈ Fy y, walkMax c K₀ r θ (m + 1) x z ^ 2 ≤ θ ^ (2 * (m + 1)) := by
    calc ∑ z ∈ Fy y, walkMax c K₀ r θ (m + 1) x z ^ 2
        ≤ ∑ z ∈ Fy y, θ ^ 2 * (walkMax c K₀ r θ m y z ^ 2 / √(bipBranch c K₀ r y : ℝ)) := by
          refine Finset.sum_le_sum fun z hz => ?_
          have heq := (Finset.mem_filter.mp hz).2.2.2
          rw [heq, mul_pow, stepWeight_sq]
          have hby_pos : (0 : ℝ) < √(bipBranch c K₀ r y : ℝ) :=
            sqrt_pos.mpr (by exact_mod_cast one_le_bipBranch c K₀ hr y)
          calc θ ^ 2 / (√(bipBranch c K₀ r x : ℝ) * √(bipBranch c K₀ r y : ℝ)) *
                walkMax c K₀ r θ m y z ^ 2
              = (θ ^ 2 / √(bipBranch c K₀ r x : ℝ)) *
                (walkMax c K₀ r θ m y z ^ 2 / √(bipBranch c K₀ r y : ℝ)) := by ring
            _ ≤ θ ^ 2 * (walkMax c K₀ r θ m y z ^ 2 / √(bipBranch c K₀ r y : ℝ)) := by
                gcongr
                exact div_le_self (by positivity) h1_br
      _ = θ ^ 2 * edgeBoundaryMass c K₀ r θ m x y := by rw [← Finset.mul_sum, edgeBoundaryMass]
      _ ≤ θ ^ 2 * θ ^ (2 * m) :=
          mul_le_mul_of_nonneg_left (edgeBoundaryMass_le c K₀ hr hfan hθ0 hθ1 m x y) (sq_nonneg θ)
      _ = θ ^ (2 * (m + 1)) := by ring
  calc ∑ z ∈ Finset.univ.filter (fun z => walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z),
        walkMax c K₀ r θ (m + 1) x z ^ 2
      ≤ ∑ z ∈ N.biUnion Fy, walkMax c K₀ r θ (m + 1) x z ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    _ ≤ ∑ y ∈ N, ∑ z ∈ Fy y, walkMax c K₀ r θ (m + 1) x z ^ 2 := by
        clear hsub
        induction N using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          rw [Finset.biUnion_insert, Finset.sum_insert ha]
          exact (sum_union_le_of_nonneg fun _ => sq_nonneg _).trans (add_le_add le_rfl ih)
    _ ≤ ∑ _y ∈ N, θ ^ (2 * (m + 1)) := Finset.sum_le_sum fun y _ => hterm y
    _ = N.card * θ ^ (2 * (m + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (max (r + 1) K₀ : ℝ) * θ ^ (2 * (m + 1)) := by
        gcongr
        exact_mod_cast card_bipAdj_le c K₀ hfan x

/-- Two-step boundary mass bound: coordinates where `walkMax (m + 2) x z > walkMax m x z` have
sum of squares at most `2 * max (r + 1) K₀ * θ ^ (2 * m + 2)`. -/
private theorem sum_sq_walkMax_twoStep_strict_le {r : ℕ} (hr : 2 ≤ r) (hfan : c.FanInAtMost r)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (m : ℕ) (x : BipNode c K₀) :
    open Classical in
    ∑ z ∈ Finset.univ.filter (fun z => walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 2) x z),
      walkMax c K₀ r θ (m + 2) x z ^ 2 ≤
      2 * (max (r + 1) K₀ : ℝ) * θ ^ (2 * m + 2) := by
  classical
  let A1 := Finset.univ.filter fun z =>
    walkMax c K₀ r θ (m + 1) x z < walkMax c K₀ r θ (m + 2) x z
  let A2 := Finset.univ.filter fun z =>
    walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z ∧
    walkMax c K₀ r θ (m + 2) x z = walkMax c K₀ r θ (m + 1) x z
  have hsub : (Finset.univ.filter fun z =>
      walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 2) x z) ⊆ A1 ∪ A2 := by
    intro z hz
    have hlt := (Finset.mem_filter.mp hz).2
    by_cases h1 : walkMax c K₀ r θ (m + 1) x z < walkMax c K₀ r θ (m + 2) x z
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ z, h1⟩)
    · have heq := le_antisymm (walkMax_mono_step c K₀ r θ (m + 1) x z) (not_lt.mp h1)
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ z, heq ▸ hlt, heq.symm⟩)
  have hsum1 := sum_sq_walkMax_strict_le c K₀ hr hfan hθ0 hθ1 (m + 1) x
  have hsum2 : ∑ z ∈ A2, walkMax c K₀ r θ (m + 2) x z ^ 2 ≤
      (max (r + 1) K₀ : ℝ) * θ ^ (2 * (m + 1)) := by
    calc ∑ z ∈ A2, walkMax c K₀ r θ (m + 2) x z ^ 2
        = ∑ z ∈ A2, walkMax c K₀ r θ (m + 1) x z ^ 2 :=
          Finset.sum_congr rfl fun z hz => by rw [(Finset.mem_filter.mp hz).2.2]
      _ ≤ ∑ z ∈ Finset.univ.filter (fun z =>
            walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z),
            walkMax c K₀ r θ (m + 1) x z ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ z, (Finset.mem_filter.mp hz).2.1⟩)
            (fun _ _ _ => sq_nonneg _)
      _ ≤ (max (r + 1) K₀ : ℝ) * θ ^ (2 * (m + 1)) :=
          sum_sq_walkMax_strict_le c K₀ hr hfan hθ0 hθ1 m x
  set D_val : ℝ := (max (r + 1) K₀ : ℝ)
  change ∑ z ∈ A1, walkMax c K₀ r θ (m + 2) x z ^ 2 ≤ D_val * θ ^ (2 * (m + 2)) at hsum1
  change ∑ z ∈ A2, walkMax c K₀ r θ (m + 2) x z ^ 2 ≤ D_val * θ ^ (2 * (m + 1)) at hsum2
  have hD_nn : 0 ≤ D_val := by positivity
  have hpow : θ ^ (2 * (m + 2)) ≤ θ ^ (2 * m + 2) :=
    pow_le_pow_of_le_one hθ0.le hθ1 (by omega)
  have hexp : 2 * (m + 1) = 2 * m + 2 := by ring
  rw [hexp] at hsum2
  calc ∑ z ∈ Finset.univ.filter (fun z => walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 2) x z),
        walkMax c K₀ r θ (m + 2) x z ^ 2
      ≤ ∑ z ∈ A1 ∪ A2, walkMax c K₀ r θ (m + 2) x z ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    _ ≤ (∑ z ∈ A1, walkMax c K₀ r θ (m + 2) x z ^ 2) +
          ∑ z ∈ A2, walkMax c K₀ r θ (m + 2) x z ^ 2 :=
        sum_union_le_of_nonneg fun _ => sq_nonneg _
    _ ≤ D_val * θ ^ (2 * (m + 2)) + D_val * θ ^ (2 * m + 2) := add_le_add hsum1 hsum2
    _ ≤ 2 * D_val * θ ^ (2 * m + 2) := by nlinarith

/-! ### Unit vertex rows and the three correlation lower bounds -/

/-- Unit row of vertex `v : HyperNode c` at radius `2 * S`. -/
private noncomputable def hyperUnitRow (r : ℕ) (θ : ℝ) (S : ℕ) (v : HyperNode c) :
    EuclideanSpace ℝ (HyperNode c) :=
  let a := WithLp.toLp 2 (walkMax c K₀ r θ (2 * S) (.inl v))
  ‖a‖⁻¹ • a

private theorem norm_hyperUnitRow (r : ℕ) (θ : ℝ) (S : ℕ) (v : HyperNode c) :
    ‖hyperUnitRow c K₀ r θ S v‖ = 1 := by
  have h1 := one_le_norm_walkMax c K₀ r θ (2 * S) v
  dsimp only [hyperUnitRow]
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (by linarith)]

private theorem hyperUnitRow_nonneg (r : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (S : ℕ) (v z : HyperNode c) :
    0 ≤ hyperUnitRow c K₀ r θ S v z :=
  mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (walkMax_nonneg c K₀ r hθ (2 * S) (.inl v) z)

private theorem inner_hyperUnitRow_nonneg (r : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (S : ℕ)
    (u v : HyperNode c) : 0 ≤ ⟪hyperUnitRow c K₀ r θ S u, hyperUnitRow c K₀ r θ S v⟫ := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  exact Finset.sum_nonneg fun z _ =>
    mul_nonneg (hyperUnitRow_nonneg c K₀ r hθ S v z) (hyperUnitRow_nonneg c K₀ r hθ S u z)

/-- Step-weight product `v → e → w` equals `θ² / √(r (k - 1))`. -/
private theorem stepWeight_mul_stepWeight {r : ℕ} (hr : 2 ≤ r) (θ : ℝ) (e : PrunedEdge c K₀)
    (u v : HyperNode c) :
    stepWeight c K₀ r θ (.inl u) (.inr e) * stepWeight c K₀ r θ (.inr e) (.inl v) =
      θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1)) := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk2 : 2 ≤ (hyperEdge c e.1).card := e.2.1
  have hk1 : ((hyperEdge c e.1).card - 1 : ℕ) = ((hyperEdge c e.1).card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have _ := hr
  dsimp only [stepWeight, bipBranch]
  rw [hk1, mul_comm (√(((hyperEdge c e.1).card : ℝ) - 1)) (√(r : ℝ)), div_mul_div_comm,
    mul_self_sqrt (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)), ← sqrt_mul hr0, ← pow_two]

/-- **Two-step pairwise correlation lower bound:** for `S ≥ 1` and `u, v ∈ hyperEdge c e.1`,
`⟪hyperUnitRow u, hyperUnitRow v⟫ ≥ 2 q₂' / (1 + q₂'²) - 4 D θ ^ (4S - 2)` where
`q₂' = θ² / √(r (k - 1))`. -/
private theorem twoStep_le_inner_hyperUnitRow {r : ℕ} (hr : 2 ≤ r) (hfan : c.FanInAtMost r)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {S : ℕ} (hS : 1 ≤ S) (e : PrunedEdge c K₀)
    {u v : HyperNode c} (hu : u ∈ hyperEdge c e.1) (hv : v ∈ hyperEdge c e.1) :
    let q₂' := θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1))
    2 * q₂' / (1 + q₂' ^ 2) - 4 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S - 2) ≤
      ⟪hyperUnitRow c K₀ r θ S u, hyperUnitRow c K₀ r θ S v⟫ := by
  classical
  intro q₂'
  have hq₂'_nn : 0 ≤ q₂' := div_nonneg (sq_nonneg θ) (sqrt_nonneg _)
  have hq₂'_le : q₂' ≤ 1 := by
    have hk2 : (2 : ℝ) ≤ (hyperEdge c e.1).card := by exact_mod_cast e.2.1
    have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have h1 : (1 : ℝ) ≤ √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1)) :=
      (le_sqrt zero_le_one (by nlinarith)).mpr (by nlinarith)
    exact (div_le_self (sq_nonneg θ) h1).trans (pow_le_one₀ hθ0.le hθ1)
  set m := 2 * S - 2
  have hm2 : m + 2 = 2 * S := by omega
  let a := WithLp.toLp 2 (walkMax c K₀ r θ (2 * S) (.inl u))
  let b := WithLp.toLp 2 (walkMax c K₀ r θ (2 * S) (.inl v))
  have ha1 : 1 ≤ ‖a‖ := one_le_norm_walkMax c K₀ r θ (2 * S) u
  have hb1 : 1 ≤ ‖b‖ := one_le_norm_walkMax c K₀ r θ (2 * S) v
  have ha_pos : 0 < ‖a‖ := zero_lt_one.trans_le ha1
  have hb_pos : 0 < ‖b‖ := zero_lt_one.trans_le hb1
  have hstep_uv (z : HyperNode c) :
      q₂' * walkMax c K₀ r θ m (.inl v) z ≤ walkMax c K₀ r θ (2 * S) (.inl u) z := by
    rw [← hm2, show q₂' = stepWeight c K₀ r θ (.inl u) (.inr e) *
        stepWeight c K₀ r θ (.inr e) (.inl v) from
      (stepWeight_mul_stepWeight c K₀ hr θ e u v).symm, mul_assoc]
    exact (mul_le_mul_of_nonneg_left
      (step_mul_walkMax_le c K₀ r θ m (x := .inr e) (y := .inl v) hv z)
      (stepWeight_nonneg c K₀ r hθ0.le _ _)).trans
      (step_mul_walkMax_le c K₀ r θ (m + 1) (x := .inl u) (y := .inr e) hu z)
  have hstep_vu (z : HyperNode c) :
      q₂' * walkMax c K₀ r θ m (.inl u) z ≤ walkMax c K₀ r θ (2 * S) (.inl v) z := by
    rw [← hm2, show q₂' = stepWeight c K₀ r θ (.inl v) (.inr e) *
        stepWeight c K₀ r θ (.inr e) (.inl u) from
      (stepWeight_mul_stepWeight c K₀ hr θ e v u).symm, mul_assoc]
    exact (mul_le_mul_of_nonneg_left
      (step_mul_walkMax_le c K₀ r θ m (x := .inr e) (y := .inl u) hu z)
      (stepWeight_nonneg c K₀ r hθ0.le _ _)).trans
      (step_mul_walkMax_le c K₀ r θ (m + 1) (x := .inl v) (y := .inr e) hv z)
  have hsum_def : 2 * q₂' / (1 + q₂' ^ 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 - ⟪a, b⟫ ≤
      4 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S - 2) := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    have hrew : 2 * q₂' / (1 + q₂' ^ 2) * ((∑ z, a z ^ 2) + ∑ z, b z ^ 2) / 2 -
          ∑ z, b z * a z =
        ∑ z, (2 * q₂' / (1 + q₂' ^ 2) * (a z ^ 2 + b z ^ 2) / 2 - a z * b z) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [mul_comm (b _)]
    rw [hrew]
    have hpt (z : HyperNode c) := two_mul_div_step_defect_le hq₂'_nn hq₂'_le
      (walkMax_nonneg c K₀ r hθ0.le (2 * S) (.inl u) z)
      (walkMax_nonneg c K₀ r hθ0.le (2 * S) (.inl v) z) (hstep_uv z) (hstep_vu z)
    have hsum_le := Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) => hpt z
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter] at hsum_le
    have hbu := sum_sq_walkMax_twoStep_strict_le c K₀ hr hfan hθ0 hθ1 m (.inl u)
    have hbv := sum_sq_walkMax_twoStep_strict_le c K₀ hr hfan hθ0 hθ1 m (.inl v)
    have hexp : 2 * m + 2 = 4 * S - 2 := by omega
    rw [hm2, hexp] at hbu hbv
    exact hsum_le.trans (by linarith)
  have hamgm : 2 * ‖a‖ * ‖b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have hprod_ge : 1 ≤ ‖a‖ * ‖b‖ := one_mul (1 : ℝ) ▸ mul_le_mul ha1 hb1 zero_le_one ha_pos.le
  have hinner_ab : (2 * q₂' / (1 + q₂' ^ 2)) * (‖a‖ * ‖b‖) -
      4 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S - 2) ≤ ⟪a, b⟫ := by
    have hκ0 : 0 ≤ 2 * q₂' / (1 + q₂' ^ 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hamgm hκ0]
  have hdiv := div_le_div_of_nonneg_right hinner_ab (mul_pos ha_pos hb_pos).le
  have herr_le : 4 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S - 2) / (‖a‖ * ‖b‖) ≤
      4 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S - 2) :=
    div_le_self (by positivity) hprod_ge
  have h1 : (2 * q₂' / (1 + q₂' ^ 2) * (‖a‖ * ‖b‖) -
      4 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S - 2)) / (‖a‖ * ‖b‖) =
      2 * q₂' / (1 + q₂' ^ 2) - 4 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S - 2) / (‖a‖ * ‖b‖) := by
    rw [sub_div, mul_div_cancel_right₀ _ (mul_pos ha_pos hb_pos).ne']
  have h2 : ⟪a, b⟫ / (‖a‖ * ‖b‖) = ⟪hyperUnitRow c K₀ r θ S u, hyperUnitRow c K₀ r θ S v⟫ := by
    dsimp only [hyperUnitRow]
    rw [real_inner_smul_left, real_inner_smul_right]
    change ⟪a, b⟫ / (‖a‖ * ‖b‖) = ‖a‖⁻¹ * (‖b‖⁻¹ * ⟪a, b⟫)
    field_simp
  linarith

/-- **One-step vertex-to-hyperedge center correlation lower bound:** for `S ≥ 1` and
`v ∈ hyperEdge c e.1`, there exists a unit center vector `w_e` (independent of `v`) with
`⟪hyperUnitRow v, w_e⟫ ≥ 2 q₁' / (1 + q₁'²) - 2 D θ ^ (4S) / q₁'` where
`q₁' = θ / √(√r * √(k - 1))`. -/
private theorem oneStep_le_inner_hyperUnitRow_center {r : ℕ} (hr : 2 ≤ r) (hfan : c.FanInAtMost r)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {S : ℕ} (hS : 1 ≤ S) (e : PrunedEdge c K₀) :
    let q₁' := stepWeight c K₀ r θ (.inr e) (.inl (Classical.choose
      (Finset.card_pos.mp (Nat.zero_lt_of_lt e.2.1))))
    ∃ w_e : EuclideanSpace ℝ (HyperNode c), ‖w_e‖ = 1 ∧
      ∀ v ∈ hyperEdge c e.1,
        2 * q₁' / (1 + q₁' ^ 2) - 2 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S) / q₁' ≤
          ⟪hyperUnitRow c K₀ r θ S v, w_e⟫ := by
  classical
  set v₀ := Classical.choose (Finset.card_pos.mp (Nat.zero_lt_of_lt e.2.1))
  have hv₀ : v₀ ∈ hyperEdge c e.1 :=
    Classical.choose_spec (Finset.card_pos.mp (Nat.zero_lt_of_lt e.2.1))
  intro q₁'
  have hq₁'_eq_all (v : HyperNode c) : stepWeight c K₀ r θ (.inr e) (.inl v) = q₁' ∧
      stepWeight c K₀ r θ (.inl v) (.inr e) = q₁' := by
    dsimp only [q₁', stepWeight, bipBranch]
    exact ⟨rfl, by rw [mul_comm]⟩
  have hq₁'_pos : 0 < q₁' := by
    have hr_pos : (0 : ℝ) < r := by exact_mod_cast Nat.zero_lt_of_lt hr
    have hk_pos : (0 : ℝ) < ((hyperEdge c e.1).card - 1 : ℕ) := by
      exact_mod_cast (show 0 < (hyperEdge c e.1).card - 1 by have := e.2.1; omega)
    dsimp only [q₁', stepWeight, bipBranch]
    exact div_pos hθ0 (sqrt_pos.mpr (mul_pos (sqrt_pos.mpr hk_pos) (sqrt_pos.mpr hr_pos)))
  have hq₁'_le : q₁' ≤ 1 := (stepWeight_le c K₀ hr hθ0.le _ _).trans hθ1
  set m := 2 * S - 1
  have hm1 : m + 1 = 2 * S := by omega
  let b := WithLp.toLp 2 (walkMax c K₀ r θ (2 * S) (.inr e))
  have hb_ge : q₁' ≤ ‖b‖ := by
    have hv₀_val : q₁' ≤ b v₀ := by
      have h1 := step_mul_walkMax_le c K₀ r θ m (x := .inr e) (y := .inl v₀) hv₀ v₀
      have h2 : 1 ≤ walkMax c K₀ r θ m (.inl v₀) v₀ := by
        simpa [walkMax] using walkMax_mono c K₀ r θ (Nat.zero_le m) (.inl v₀) v₀
      rw [hm1, (hq₁'_eq_all v₀).1] at h1
      nlinarith
    have hsq : q₁' ^ 2 ≤ ‖b‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc q₁' ^ 2 ≤ b v₀ ^ 2 := pow_le_pow_left₀ hq₁'_pos.le hv₀_val 2
        _ ≤ ∑ z, b z ^ 2 := Finset.single_le_sum (fun z _ => sq_nonneg _) (Finset.mem_univ v₀)
    nlinarith [norm_nonneg b]
  have hb_pos : 0 < ‖b‖ := hq₁'_pos.trans_le hb_ge
  refine ⟨‖b‖⁻¹ • b, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hb_pos.ne'], ?_⟩
  intro v hv
  let a := WithLp.toLp 2 (walkMax c K₀ r θ (2 * S) (.inl v))
  have ha1 : 1 ≤ ‖a‖ := one_le_norm_walkMax c K₀ r θ (2 * S) v
  have ha_pos : 0 < ‖a‖ := zero_lt_one.trans_le ha1
  have hstep_ve (z : HyperNode c) :
      q₁' * walkMax c K₀ r θ m (.inr e) z ≤ walkMax c K₀ r θ (2 * S) (.inl v) z := by
    rw [← hm1, ← (hq₁'_eq_all v).2]
    exact step_mul_walkMax_le c K₀ r θ m (x := .inl v) (y := .inr e) hv z
  have hstep_ev (z : HyperNode c) :
      q₁' * walkMax c K₀ r θ m (.inl v) z ≤ walkMax c K₀ r θ (2 * S) (.inr e) z := by
    rw [← hm1, ← (hq₁'_eq_all v).1]
    exact step_mul_walkMax_le c K₀ r θ m (x := .inr e) (y := .inl v) hv z
  have hsum_def : 2 * q₁' / (1 + q₁' ^ 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 - ⟪a, b⟫ ≤
      2 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S) := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    have hrew : 2 * q₁' / (1 + q₁' ^ 2) * ((∑ z, a z ^ 2) + ∑ z, b z ^ 2) / 2 -
          ∑ z, b z * a z =
        ∑ z, (2 * q₁' / (1 + q₁' ^ 2) * (a z ^ 2 + b z ^ 2) / 2 - a z * b z) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [mul_comm (b _)]
    rw [hrew]
    have hpt (z : HyperNode c) := two_mul_div_step_defect_le hq₁'_pos.le hq₁'_le
      (walkMax_nonneg c K₀ r hθ0.le (2 * S) (.inl v) z)
      (walkMax_nonneg c K₀ r hθ0.le (2 * S) (.inr e) z) (hstep_ve z) (hstep_ev z)
    have hsum_le := Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) => hpt z
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter] at hsum_le
    have hbv := sum_sq_walkMax_strict_le c K₀ hr hfan hθ0 hθ1 m (.inl v)
    have hbe := sum_sq_walkMax_strict_le c K₀ hr hfan hθ0 hθ1 m (.inr e)
    have hexp : 2 * (m + 1) = 4 * S := by omega
    rw [hexp] at hbv hbe
    rw [hm1] at hbv hbe
    exact hsum_le.trans (by linarith)
  have hamgm : 2 * ‖a‖ * ‖b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have hprod_ge : q₁' ≤ ‖a‖ * ‖b‖ := one_mul q₁' ▸ mul_le_mul ha1 hb_ge hq₁'_pos.le ha_pos.le
  have hinner_ab : (2 * q₁' / (1 + q₁' ^ 2)) * (‖a‖ * ‖b‖) -
      2 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S) ≤ ⟪a, b⟫ := by
    have hκ0 : 0 ≤ 2 * q₁' / (1 + q₁' ^ 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hamgm hκ0]
  have hdiv := div_le_div_of_nonneg_right hinner_ab (mul_pos ha_pos hb_pos).le
  have herr_le : 2 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S) / (‖a‖ * ‖b‖) ≤
      2 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S) / q₁' :=
    div_le_div_of_nonneg_left (by positivity) hq₁'_pos hprod_ge
  have h1 : (2 * q₁' / (1 + q₁' ^ 2) * (‖a‖ * ‖b‖) -
      2 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S)) / (‖a‖ * ‖b‖) =
      2 * q₁' / (1 + q₁' ^ 2) - 2 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S) / (‖a‖ * ‖b‖) := by
    rw [sub_div, mul_div_cancel_right₀ _ (mul_pos ha_pos hb_pos).ne']
  have h2 : ⟪a, b⟫ / (‖a‖ * ‖b‖) = ⟪hyperUnitRow c K₀ r θ S v, ‖b‖⁻¹ • b⟫ := by
    dsimp only [hyperUnitRow]
    rw [real_inner_smul_left, real_inner_smul_right]
    change ⟪a, b⟫ / (‖a‖ * ‖b‖) = ‖a‖⁻¹ * (‖b‖⁻¹ * ⟪a, b⟫)
    field_simp
  linarith

/-- **Two-step star-cone sum of inner products on `hyperUnitRow`:** when `3 ≤ k` and the perturbed
cone tangent hypotheses hold at `q₂' = θ² / √(r (k - 1))`, the off-diagonal inner products of
`hyperUnitRow` on `hyperEdge c e.1` average at least
`(2 q₂' + (k - 2) q₂'²) / (1 + (k - 1) q₂'²) - 8 √D θ ^ (2S - 1)`. -/
private theorem starCone_le_sum_offDiag_inner_hyperUnitRow {r : ℕ} (hr : 2 ≤ r)
    (hfan : c.FanInAtMost r) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {S : ℕ} (hS : 1 ≤ S)
    (e : PrunedEdge c K₀) (hk : 3 ≤ (hyperEdge c e.1).card)
    (htan_lo : θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1)) ≤
      (1 + (((hyperEdge c e.1).card : ℝ) - 1) *
        (θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1))) ^ 2) /
        (hyperEdge c e.1).card)
    (htan_hi : (1 + (((hyperEdge c e.1).card : ℝ) - 1) *
        (θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1))) ^ 2) /
        (hyperEdge c e.1).card -
        θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1)) ≤
      2 * (θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1))) *
        √((1 + (((hyperEdge c e.1).card : ℝ) - 1) *
          (θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1))) ^ 2) /
          (hyperEdge c e.1).card)) :
    let s := hyperEdge c e.1
    let q₂' := θ ^ 2 / √((r : ℝ) * ((s.card : ℝ) - 1))
    (s.card : ℝ) * ((s.card : ℝ) - 1) *
        ((2 * q₂' + ((s.card : ℝ) - 2) * q₂' ^ 2) / (1 + ((s.card : ℝ) - 1) * q₂' ^ 2) -
          8 * √(max (r + 1) K₀ : ℝ) * θ ^ (2 * S - 1)) ≤
      ∑ p ∈ s.offDiag, ⟪hyperUnitRow c K₀ r θ S p.1, hyperUnitRow c K₀ r θ S p.2⟫ := by
  classical
  intro s q₂'
  have hs_ne : s.Nonempty := Finset.card_pos.mp (show 0 < s.card by dsimp only [s]; omega)
  have hq₂'_pos : 0 < q₂' := by
    have hr_pos : (0 : ℝ) < r := by exact_mod_cast Nat.zero_lt_of_lt hr
    have hk_pos : (0 : ℝ) < (s.card : ℝ) - 1 := by
      have : (3 : ℝ) ≤ s.card := by exact_mod_cast hk
      linarith
    exact div_pos (sq_pos_of_pos hθ0) (sqrt_pos.mpr (mul_pos hr_pos hk_pos))
  set m := 2 * S - 2
  have hm2 : m + 2 = 2 * S := by omega
  let a : HyperNode c → EuclideanSpace ℝ (HyperNode c) :=
    fun v => WithLp.toLp 2 (walkMax c K₀ r θ (2 * S) (.inl v))
  let M : EuclideanSpace ℝ (HyperNode c) :=
    WithLp.toLp 2 fun z => (s.image fun v => walkMax c K₀ r θ m (.inl v) z).max' (hs_ne.image _)
  let b : HyperNode c → EuclideanSpace ℝ (HyperNode c) :=
    fun v => WithLp.toLp 2 fun z => min (a v z) (M z)
  have hle_M_of_mem (v : HyperNode c) (hv : v ∈ s) (z : HyperNode c) :
      walkMax c K₀ r θ m (.inl v) z ≤ M z :=
    Finset.le_max' (s.image fun u => walkMax c K₀ r θ m (.inl u) z)
      (walkMax c K₀ r θ m (.inl v) z) (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  have ⟨v₀, hv₀⟩ := hs_ne
  have hM_nn (z : HyperNode c) : 0 ≤ M z :=
    (walkMax_nonneg c K₀ r hθ0.le m (.inl v₀) z).trans (hle_M_of_mem v₀ hv₀ z)
  have hM1 : 1 ≤ ‖M‖ := by
    have hv₀1 : 1 ≤ M v₀ := by
      have h1 : 1 ≤ walkMax c K₀ r θ m (.inl v₀) v₀ := by
        simpa [walkMax] using walkMax_mono c K₀ r θ (Nat.zero_le m) (.inl v₀) v₀
      exact h1.trans (hle_M_of_mem v₀ hv₀ v₀)
    have hsq : 1 ≤ ‖M‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc (1 : ℝ) ≤ M v₀ ^ 2 := by nlinarith
        _ ≤ ∑ z, M z ^ 2 := Finset.single_le_sum (fun z _ => sq_nonneg _) (Finset.mem_univ v₀)
    nlinarith [norm_nonneg M]
  have hb1 (v : HyperNode c) (hv : v ∈ s) : 1 ≤ ‖b v‖ := by
    have h1 : 1 ≤ b v v := by
      have ha_v : 1 ≤ a v v := by
        simpa [a, walkMax] using walkMax_mono c K₀ r θ (Nat.zero_le (2 * S)) (.inl v) v
      have hM_v : 1 ≤ M v := by
        have hm_v : 1 ≤ walkMax c K₀ r θ m (.inl v) v := by
          simpa [walkMax] using walkMax_mono c K₀ r θ (Nat.zero_le m) (.inl v) v
        exact hm_v.trans (hle_M_of_mem v hv v)
      exact le_min ha_v hM_v
    have hsq : 1 ≤ ‖b v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc (1 : ℝ) ≤ b v v ^ 2 := by nlinarith
        _ ≤ ∑ z, b v z ^ 2 := Finset.single_le_sum (fun z _ => sq_nonneg _) (Finset.mem_univ v)
    nlinarith [norm_nonneg (b v)]
  have hattain_M (z : HyperNode c) : ∃ v ∈ s, walkMax c K₀ r θ m (.inl v) z = M z := by
    have hmem := Finset.max'_mem (s.image fun v => walkMax c K₀ r θ m (.inl v) z) (hs_ne.image _)
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hmem
    exact ⟨v, hv, heq⟩
  have hcone_lo (v : HyperNode c) (hv : v ∈ s) (z : HyperNode c) : q₂' * M z ≤ b v z := by
    obtain ⟨v_star, hv_star, hv_star_eq⟩ := hattain_M z
    have hstep : q₂' * walkMax c K₀ r θ m (.inl v_star) z ≤ a v z := by
      dsimp only [a]
      rw [← hm2, show q₂' = stepWeight c K₀ r θ (.inl v) (.inr e) *
          stepWeight c K₀ r θ (.inr e) (.inl v_star) from
        (stepWeight_mul_stepWeight c K₀ hr θ e v v_star).symm, mul_assoc]
      exact (mul_le_mul_of_nonneg_left
        (step_mul_walkMax_le c K₀ r θ m (x := .inr e) (y := .inl v_star) hv_star z)
        (stepWeight_nonneg c K₀ r hθ0.le _ _)).trans
        (step_mul_walkMax_le c K₀ r θ (m + 1) (x := .inl v) (y := .inr e) hv z)
    rw [hv_star_eq] at hstep
    have hq₂'_le : q₂' ≤ 1 := by
      have hk3 : (3 : ℝ) ≤ s.card := by exact_mod_cast hk
      have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
      have h1 : (1 : ℝ) ≤ √((r : ℝ) * ((s.card : ℝ) - 1)) :=
        (le_sqrt zero_le_one (by nlinarith)).mpr (by nlinarith)
      exact (div_le_self (sq_nonneg θ) h1).trans (pow_le_one₀ hθ0.le hθ1)
    exact le_min hstep (mul_le_of_le_one_left (hM_nn z) hq₂'_le)
  have hcone_hi (v : HyperNode c) (_hv : v ∈ s) (z : HyperNode c) : b v z ≤ M z := min_le_right _ _
  have hattain (z : HyperNode c) : ∃ v ∈ s, b v z = M z := by
    obtain ⟨v_star, hv_star, hv_star_eq⟩ := hattain_M z
    refine ⟨v_star, hv_star, min_eq_right ?_⟩
    rw [← hv_star_eq]
    exact walkMax_mono c K₀ r θ (by omega : m ≤ 2 * S) (.inl v_star) z
  have hstar := starCone_sum_offDiag_inner_le hk hq₂'_pos hM1 hM_nn hb1 hcone_lo hcone_hi hattain
    htan_lo htan_hi
  have hdiff_u (v : HyperNode c) (hv : v ∈ s) :
      ‖hyperUnitRow c K₀ r θ S v - ‖b v‖⁻¹ • b v‖ ≤
        4 * √(max (r + 1) K₀ : ℝ) * θ ^ (2 * S - 1) := by
    have ha_ge : 1 ≤ ‖a v‖ := one_le_norm_walkMax c K₀ r θ (2 * S) v
    have h1 := norm_inv_smul_sub_le ha_ge (hb1 v hv)
    have hnorm_ab_sq : ‖a v - b v‖ ^ 2 ≤ 2 * (max (r + 1) K₀ : ℝ) * θ ^ (2 * m + 2) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      let Bv := Finset.univ.filter fun z =>
        walkMax c K₀ r θ m (.inl v) z < walkMax c K₀ r θ (m + 2) (.inl v) z
      calc ∑ z, (a v z - b v z) ^ 2
          ≤ ∑ z, if z ∈ Bv then walkMax c K₀ r θ (m + 2) (.inl v) z ^ 2 else 0 := by
            refine Finset.sum_le_sum fun z _ => ?_
            by_cases hz : z ∈ Bv
            · rw [ite_eq_left hz]
              have hle1 : 0 ≤ a v z - b v z := sub_nonneg.mpr (min_le_left _ _)
              have hle2 : a v z - b v z ≤ a v z := sub_le_self _
                (le_min (walkMax_nonneg c K₀ r hθ0.le (2 * S) (.inl v) z) (hM_nn z))
              have hsq := pow_le_pow_left₀ hle1 hle2 2
              simpa only [a, hm2] using hsq
            · rw [ite_eq_right hz]
              have heq_m := le_antisymm
                (not_lt.mp fun hlt => hz (Finset.mem_filter.mpr ⟨Finset.mem_univ z, hlt⟩))
                (walkMax_mono c K₀ r θ (by omega) (.inl v) z)
              have hle_M : a v z ≤ M z := by
                have hm_le_M : walkMax c K₀ r θ m (.inl v) z ≤ M z := hle_M_of_mem v hv z
                dsimp only [a]
                rw [← hm2, heq_m]
                exact hm_le_M
              have hb_eq : b v z = a v z := min_eq_left hle_M
              simp [hb_eq]
        _ = ∑ z ∈ Bv, walkMax c K₀ r θ (m + 2) (.inl v) z ^ 2 := by
            rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
        _ ≤ 2 * (max (r + 1) K₀ : ℝ) * θ ^ (2 * m + 2) :=
            sum_sq_walkMax_twoStep_strict_le c K₀ hr hfan hθ0 hθ1 m (.inl v)
    have hexp : 2 * m + 2 = 2 * (2 * S - 1) := by omega
    rw [hexp, pow_mul'] at hnorm_ab_sq
    have h4 : 2 * (max (r + 1) K₀ : ℝ) * (θ ^ (2 * S - 1)) ^ 2 ≤
        (2 * √(max (r + 1) K₀ : ℝ) * θ ^ (2 * S - 1)) ^ 2 := by
      rw [mul_pow, mul_pow, sq_sqrt (by positivity)]
      have : 0 ≤ (max (r + 1) K₀ : ℝ) * (θ ^ (2 * S - 1)) ^ 2 := by positivity
      linarith
    have hnorm_ab : ‖a v - b v‖ ≤ 2 * √(max (r + 1) K₀ : ℝ) * θ ^ (2 * S - 1) := by
      have htot := hnorm_ab_sq.trans h4
      have hrhs_nn : 0 ≤ 2 * √(max (r + 1) K₀ : ℝ) * θ ^ (2 * S - 1) := by positivity
      nlinarith [norm_nonneg (a v - b v)]
    dsimp only [hyperUnitRow]
    linarith
  have hp_diff (p : HyperNode c × HyperNode c) (hp : p ∈ s.offDiag) :
      ⟪‖b p.1‖⁻¹ • b p.1, ‖b p.2‖⁻¹ • b p.2⟫ -
          8 * √(max (r + 1) K₀ : ℝ) * θ ^ (2 * S - 1) ≤
        ⟪hyperUnitRow c K₀ r θ S p.1, hyperUnitRow c K₀ r θ S p.2⟫ := by
    obtain ⟨h1, h2, -⟩ := Finset.mem_offDiag.mp hp
    have hb2_norm : ‖‖b p.2‖⁻¹ • b p.2‖ = 1 := by
      have hp2 : 0 < ‖b p.2‖ := zero_lt_one.trans_le (hb1 p.2 h2)
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hp2.ne']
    have habs := abs_inner_sub_inner_of_norm_eq_one (u₁ := hyperUnitRow c K₀ r θ S p.1)
      (u₂ := ‖b p.1‖⁻¹ • b p.1) (v₁ := hyperUnitRow c K₀ r θ S p.2) (v₂ := ‖b p.2‖⁻¹ • b p.2)
      (by
        have hp1 : 0 < ‖b p.1‖ := zero_lt_one.trans_le (hb1 p.1 h1)
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hp1.ne'])
      (norm_hyperUnitRow c K₀ r θ S p.2)
    have hd1 := hdiff_u p.1 h1
    have hd2 := hdiff_u p.2 h2
    linarith [neg_abs_le (⟪hyperUnitRow c K₀ r θ S p.1, hyperUnitRow c K₀ r θ S p.2⟫ -
      ⟪‖b p.1‖⁻¹ • b p.1, ‖b p.2‖⁻¹ • b p.2⟫)]
  have hsum_diff := Finset.sum_le_sum hp_diff
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum_diff
  have hoff_card : (s.offDiag.card : ℝ) = (s.card : ℝ) * ((s.card : ℝ) - 1) := by
    rw [Finset.offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
    ring
  rw [hoff_card] at hsum_diff
  linarith

/-! ### Uniform `(θ, S)` parameter selection for `HyperDualCert` -/

private theorem twoStepCorr_pos {r k : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k) : 0 < twoStepCorr r k := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : 0 < (r : ℝ) * ((k : ℝ) - 1) := by nlinarith
  unfold twoStepCorr
  positivity

private theorem twoStepCorr_lt_one {r k : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k) : twoStepCorr r k < 1 := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : (2 : ℝ) ≤ (r : ℝ) * ((k : ℝ) - 1) := by nlinarith
  set q := 1 / √((r : ℝ) * ((k : ℝ) - 1))
  have hq_lt : q < 1 := by
    dsimp only [q]
    rw [div_lt_one (sqrt_pos.mpr (by linarith))]
    exact (lt_sqrt zero_le_one).mpr (by linarith)
  change 2 * q / (1 + q ^ 2) < 1
  rw [div_lt_one (by positivity)]
  nlinarith [sq_pos_of_pos (sub_pos.mpr hq_lt)]

/-- Gaussian vertex score induced by `hyperUnitRow c K₀ r θ S`. -/
private noncomputable def hyperScore (r : ℕ) (θ : ℝ) (S : ℕ) (ω : HyperNode c → ℝ)
    (v : HyperNode c) : ℝ :=
  ⟪hyperUnitRow c K₀ r θ S v, WithLp.toLp 2 ω⟫

end BipartiteKernel

section ParameterSelection

/-- Shared `(θ, S)` convergence selection for the two-step pairwise inner-product bound: for any
`r ≥ 2`, `k ≥ 2`, and `δ > 0`, choosing `θ` close to `1` and `S` large makes every pair of vertices
in any size-`k` pruned hyperedge have inner product at least `twoStepCorr r k - 3 * δ / 4`. -/
private theorem exists_theta_radius_twoStep_inner_ge {r k K₀ : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ₀ ∈ Ioo (0 : ℝ) 1, ∀ θ ∈ Ioo θ₀ 1, ∃ S₀ : ℕ, 1 ≤ S₀ ∧ ∀ S ≥ S₀,
      ∀ {σ : Signature} {n : ℕ} (c : Circuit σ n 1), c.FanInAtMost r →
        ∀ (e : PrunedEdge c K₀), (hyperEdge c e.1).card = k →
          ∀ {u v : HyperNode c}, u ∈ hyperEdge c e.1 → v ∈ hyperEdge c e.1 →
            twoStepCorr r k - 3 * δ / 4 ≤
              ⟪hyperUnitRow c K₀ r θ S u, hyperUnitRow c K₀ r θ S v⟫ := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hm_pos : 0 < (r : ℝ) * ((k : ℝ) - 1) := by nlinarith
  set q₂ := 1 / √((r : ℝ) * ((k : ℝ) - 1))
  have hq₂_pos : 0 < q₂ := by positivity
  set D : ℝ := max ((r : ℝ) + 1) (K₀ : ℝ)
  have hD_pos : 0 < D := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set ρ₀ := twoStepCorr r k
  let f : ℝ → ℝ := fun θ => 2 * (θ ^ 2 * q₂) / (1 + (θ ^ 2 * q₂) ^ 2)
  have hf_cont : ContinuousAt f 1 := by
    dsimp only [f]
    refine ((continuousAt_const.mul ((continuousAt_id.pow 2).mul continuousAt_const)).div
      (continuousAt_const.add (((continuousAt_id.pow 2).mul continuousAt_const).pow 2)) ?_)
    positivity
  have hf1 : f 1 = ρ₀ := by simp [f, ρ₀, twoStepCorr, q₂]
  obtain ⟨γ, hγ, hcont_f⟩ := Metric.continuousAt_iff.mp hf_cont (δ / 2) (half_pos hδ)
  set θ₀ := 1 - min γ (1 / 2) / 2
  have hθ₀_mem : θ₀ ∈ Ioo (0 : ℝ) 1 := by
    have hmin_pos : 0 < min γ (1 / 2) := lt_min hγ (by norm_num)
    have hmin_le : min γ (1 / 2) ≤ 1 / 2 := min_le_right _ _
    exact ⟨by dsimp only [θ₀]; linarith, by dsimp only [θ₀]; linarith⟩
  refine ⟨θ₀, hθ₀_mem, fun θ hθ => ?_⟩
  have hθ0 : 0 < θ := hθ₀_mem.1.trans hθ.1
  have hθ1 : θ < 1 := hθ.2
  have hdist_θ : dist θ 1 < γ := by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    have : min γ (1 / 2) ≤ γ := min_le_left _ _
    have : θ₀ < θ := hθ.1
    dsimp only [θ₀] at this
    linarith
  have hf_close : ρ₀ - δ / 2 < f θ := by
    have H := hcont_f hdist_θ
    rw [Real.dist_eq, hf1] at H
    linarith [neg_abs_le (f θ - ρ₀)]
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < δ / (16 * D)) hθ1
  refine ⟨max 1 (N + 1), le_max_left _ _, fun S hS σ n c hfan e hk_eq u v hu hv => ?_⟩
  have hS1 : 1 ≤ S := (le_max_left 1 (N + 1)).trans hS
  have hSN : N ≤ 4 * S - 2 := by
    have : N + 1 ≤ S := (le_max_right 1 (N + 1)).trans hS
    omega
  have herr : 4 * D * θ ^ (4 * S - 2) < δ / 4 := by
    have hpow : θ ^ (4 * S - 2) ≤ θ ^ N := pow_le_pow_of_le_one hθ0.le hθ1.le hSN
    have hlt := (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 4 * D)).trans_lt
      (mul_lt_mul_of_pos_left hN (by positivity : 0 < 4 * D))
    have hsimp : 4 * D * (δ / (16 * D)) = δ / 4 := by field_simp; ring
    linarith
  have hcorr := twoStep_le_inner_hyperUnitRow c K₀ hr hfan hθ0 hθ1.le hS1 e hu hv
  have hq_eq : θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1)) = θ ^ 2 * q₂ := by
    rw [hk_eq]
    dsimp only [q₂]
    ring
  dsimp only at hcorr
  rw [hq_eq] at hcorr
  change 2 * (θ ^ 2 * q₂) / (1 + (θ ^ 2 * q₂) ^ 2) - 4 * D * θ ^ (4 * S - 2) ≤ _ at hcorr
  dsimp only [ρ₀, f] at hf_close ⊢
  linarith

/-- Analytic parameter selection for a single hyperedge size `k`: given `HyperEdgeBound r k p` and
`η > 0`, there is a decay threshold `θ₀ ∈ (0, 1)` such that for every `θ ∈ (θ₀, 1)` there is a
radius `S₀` above which every size-`k` pruned hyperedge in any fan-in-`r` circuit straddles any
threshold `t` with probability at most `p + η`. -/
private theorem exists_theta_radius_of_hyperEdgeBound {r k K₀ : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k)
    {p η : ℝ} (hη : 0 < η) (hb : HyperEdgeBound r k p) :
    ∃ θ₀ ∈ Ioo (0 : ℝ) 1, ∀ θ ∈ Ioo θ₀ 1, ∃ S₀ : ℕ, 1 ≤ S₀ ∧ ∀ S ≥ S₀,
      ∀ {σ : Signature} {n : ℕ} (c : Circuit σ n 1), c.FanInAtMost r →
        ∀ (e : PrunedEdge c K₀), (hyperEdge c e.1).card = k → ∀ t : ℝ,
          (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
            {ω | HyperedgeStraddles (hyperEdge c e.1)
              {v | hyperScore c K₀ r θ S ω v < t}} ≤ p + η := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hm_pos : 0 < (r : ℝ) * ((k : ℝ) - 1) := by nlinarith
  set q₂ := 1 / √((r : ℝ) * ((k : ℝ) - 1))
  have hq₂_pos : 0 < q₂ := by positivity
  set D : ℝ := max ((r : ℝ) + 1) (K₀ : ℝ)
  have hD_pos : 0 < D := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  cases hb with
  | pairwise hp =>
    set ρ₀ := twoStepCorr r k
    obtain ⟨δ, hδ, hcont_arc⟩ := Metric.continuousAt_iff.mp
      (continuous_arccos.continuousAt (x := ρ₀)) (2 * π * η / k) (by positivity)
    obtain ⟨θ₀, hθ₀_mem, hθ_sel⟩ := exists_theta_radius_twoStep_inner_ge (K₀ := K₀) hr hk hδ
    set ρ := ρ₀ - 3 * δ / 4
    have hdist_ρ : dist ρ ρ₀ < δ := by
      rw [Real.dist_eq, show ρ - ρ₀ = -(3 * δ / 4) by dsimp only [ρ]; ring, abs_neg,
        abs_of_pos (by positivity)]
      linarith
    have harc_le : (k : ℝ) / (2 * π) * arccos ρ ≤ p + η := by
      have H := (le_abs_self _).trans (hcont_arc hdist_ρ).le
      rw [Real.dist_eq] at *
      have hmul := mul_le_mul_of_nonneg_left (show arccos ρ ≤ arccos ρ₀ + 2 * π * η / k by
        linarith [le_abs_self (arccos ρ - arccos ρ₀), (hcont_arc hdist_ρ).le])
        (by positivity : 0 ≤ (k : ℝ) / (2 * π))
      have hcancel : (k : ℝ) / (2 * π) * (2 * π * η / k) = η := by
        have hk_ne : (k : ℝ) ≠ 0 := by positivity
        field_simp
      linarith
    refine ⟨θ₀, hθ₀_mem, fun θ hθ => ?_⟩
    obtain ⟨S₀, hS₀, hS_sel⟩ := hθ_sel θ hθ
    refine ⟨S₀, hS₀, fun S hS σ n c hfan e hk_eq t => ?_⟩
    have hangle : ∑ pq ∈ (hyperEdge c e.1).offDiag,
        InnerProductGeometry.angle (hyperUnitRow c K₀ r θ S pq.1)
          (hyperUnitRow c K₀ r θ S pq.2) ≤
        ((hyperEdge c e.1).card : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1) * arccos ρ := by
      have hcard : ((hyperEdge c e.1).offDiag.card : ℝ) =
          ((hyperEdge c e.1).card : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1) := by
        rw [Finset.offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
        ring
      rw [← hcard, ← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun pq hpq => ?_
      obtain ⟨h1, h2, -⟩ := Finset.mem_offDiag.mp hpq
      rw [InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one
        (norm_hyperUnitRow c K₀ r θ S pq.1) (norm_hyperUnitRow c K₀ r θ S pq.2)]
      exact arccos_le_arccos (hS_sel S hS c hfan e hk_eq h1 h2)
    have hprob := measureReal_straddlesOn_le_of_sum_angle (hk_eq ▸ hk)
      (fun v _ => norm_hyperUnitRow c K₀ r θ S v) hangle t
    have hev : {ω : HyperNode c → ℝ | HyperedgeStraddles (hyperEdge c e.1)
        {v | hyperScore c K₀ r θ S ω v < t}} =
        {ω | StraddlesOn (fun v => ⟪hyperUnitRow c K₀ r θ S v, WithLp.toLp 2 ω⟫) t
          ↑(hyperEdge c e.1)} := by
      ext ω
      exact hyperedgeStraddles_threshold_iff _ _ _
    rw [hev]
    rw [hk_eq] at hprob
    exact hprob.trans harc_le
  | slepian hp =>
    set ρ₀ := twoStepCorr r k
    have hρ₀_pos := twoStepCorr_pos hr hk
    have hρ₀_lt := twoStepCorr_lt_one hr hk
    obtain ⟨δ₀, hδ₀, hcont_sl⟩ := Metric.continuousAt_iff.mp
      (continuousAt_equicorrStraddle k hρ₀_pos hρ₀_lt) η hη
    set δ := min δ₀ (min ρ₀ (1 - ρ₀))
    have hδ : 0 < δ := lt_min hδ₀ (lt_min hρ₀_pos (sub_pos.mpr hρ₀_lt))
    obtain ⟨θ₀, hθ₀_mem, hθ_sel⟩ := exists_theta_radius_twoStep_inner_ge (K₀ := K₀) hr hk hδ
    set ρ := ρ₀ - 3 * δ / 4
    have hρ0 : 0 ≤ ρ := by
      have : δ ≤ ρ₀ := (min_le_right _ _).trans (min_le_left _ _)
      dsimp only [ρ]
      linarith
    have hρ1 : ρ < 1 := by
      dsimp only [ρ]
      linarith
    have hdist_ρ : dist ρ ρ₀ < δ₀ := by
      rw [Real.dist_eq, show ρ - ρ₀ = -(3 * δ / 4) by dsimp only [ρ]; ring, abs_neg,
        abs_of_pos (by positivity)]
      have : δ ≤ δ₀ := min_le_left _ _
      linarith
    have hsl_le : equicorrStraddle k ρ ≤ p + η := by
      have H := (le_abs_self (equicorrStraddle k ρ - equicorrStraddle k ρ₀)).trans
        (by simpa [Real.dist_eq] using (hcont_sl hdist_ρ).le)
      linarith
    refine ⟨θ₀, hθ₀_mem, fun θ hθ => ?_⟩
    obtain ⟨S₀, hS₀, hS_sel⟩ := hθ_sel θ hθ
    refine ⟨S₀, hS₀, fun S hS σ n c hfan e hk_eq t => ?_⟩
    have hprob := measureReal_straddlesOn_le_equicorr (s := hyperEdge c e.1) (hk_eq ▸ hk)
      (fun v _ => norm_hyperUnitRow c K₀ r θ S v) hρ0 hρ1
      (fun u hu v hv _ => hS_sel S hS c hfan e hk_eq hu hv) t
    have hev : {ω : HyperNode c → ℝ | HyperedgeStraddles (hyperEdge c e.1)
        {v | hyperScore c K₀ r θ S ω v < t}} =
        {ω | (∃ v ∈ hyperEdge c e.1, ⟪hyperUnitRow c K₀ r θ S v, WithLp.toLp 2 ω⟫ < t) ∧
          (∃ v ∈ hyperEdge c e.1, t ≤ ⟪hyperUnitRow c K₀ r θ S v, WithLp.toLp 2 ω⟫)} := by
      ext ω
      rw [mem_ofPred_eq, mem_ofPred_eq, hyperedgeStraddles_threshold_iff]
      simp only [StraddlesOn, Finset.mem_coe, hyperScore]
    rw [hev]
    rw [hk_eq] at hprob
    exact hprob.trans hsl_le
  | cap hcap hp =>
    set q₁ := 1 / √(√((k : ℝ) - 1) * √(r : ℝ))
    have hq₁_pos : 0 < q₁ := by
      have : 0 < √((k : ℝ) - 1) * √(r : ℝ) :=
        mul_pos (sqrt_pos.mpr (by linarith)) (sqrt_pos.mpr (by linarith))
      exact div_pos one_pos (sqrt_pos.mpr this)
    have hq₁_sq : q₁ ^ 2 = 1 / √((r : ℝ) * ((k : ℝ) - 1)) := by
      dsimp only [q₁]
      rw [div_pow, one_pow, sq_sqrt (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)),
        mul_comm (√((k : ℝ) - 1)), ← sqrt_mul (by linarith)]
    set κ₀ := 2 * q₁ / (1 + q₁ ^ 2)
    have hκ₀_sq : κ₀ ^ 2 = capSq r k := by
      dsimp only [κ₀, capSq]
      rw [div_pow, mul_pow, hq₁_sq]
      set s := √((r : ℝ) * ((k : ℝ) - 1))
      have hs : 0 < s := sqrt_pos.mpr hm_pos
      field_simp
      ring
    have hκ₀_gt : √2 / 2 < κ₀ := by
      have hsq : (√2 / 2) ^ 2 < κ₀ ^ 2 := by
        rw [div_pow, sq_sqrt zero_le_two, hκ₀_sq]
        linarith
      have hκ₀_nn : 0 ≤ κ₀ := by positivity
      nlinarith [sqrt_nonneg 2]
    let Hcap : ℝ → ℝ := fun κ => ((k : ℝ) * κ ^ 2 - 1) / ((k : ℝ) - 1)
    have hHcap_eq : Hcap κ₀ = capCorr r k := by
      dsimp only [Hcap, capCorr]
      rw [hκ₀_sq]
    have hcomp_cont : ContinuousAt (fun κ => arccos (Hcap κ)) κ₀ := by
      refine continuous_arccos.continuousAt.comp ?_
      dsimp only [Hcap]
      exact ((continuousAt_const.mul (continuousAt_id.pow 2)).sub continuousAt_const).div_const _
    obtain ⟨δ₀, hδ₀, hcont_cap⟩ := Metric.continuousAt_iff.mp hcomp_cont
      (2 * π * η / k) (by positivity)
    set δ := min δ₀ (κ₀ - √2 / 2)
    have hδ : 0 < δ := lt_min hδ₀ (sub_pos.mpr hκ₀_gt)
    let g : ℝ → ℝ := fun θ => 2 * (θ * q₁) / (1 + (θ * q₁) ^ 2)
    have hg_cont : ContinuousAt g 1 := by
      dsimp only [g]
      refine ((continuousAt_const.mul (continuousAt_id.mul continuousAt_const)).div
        (continuousAt_const.add ((continuousAt_id.mul continuousAt_const).pow 2)) ?_)
      positivity
    have hg1 : g 1 = κ₀ := by simp [g, κ₀]
    obtain ⟨γ, hγ, hcont_g⟩ := Metric.continuousAt_iff.mp hg_cont (δ / 2) (half_pos hδ)
    set θ₀ := 1 - min γ (1 / 2) / 2
    have hθ₀_mem : θ₀ ∈ Ioo (0 : ℝ) 1 := by
      have hmin_pos : 0 < min γ (1 / 2) := lt_min hγ (by norm_num)
      have hmin_le : min γ (1 / 2) ≤ 1 / 2 := min_le_right _ _
      exact ⟨by dsimp only [θ₀]; linarith, by dsimp only [θ₀]; linarith⟩
    refine ⟨θ₀, hθ₀_mem, fun θ hθ => ?_⟩
    have hθ0 : 0 < θ := hθ₀_mem.1.trans hθ.1
    have hθ1 : θ < 1 := hθ.2
    have hdist_θ : dist θ 1 < γ := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      have : min γ (1 / 2) ≤ γ := min_le_left _ _
      have : θ₀ < θ := hθ.1
      dsimp only [θ₀] at this
      linarith
    have hg_close : κ₀ - δ / 2 < g θ := by
      have H := hcont_g hdist_θ
      rw [Real.dist_eq, hg1] at H
      linarith [neg_abs_le (g θ - κ₀)]
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
      (by positivity : 0 < δ * (θ * q₁) / (8 * D)) hθ1
    refine ⟨max 1 N, le_max_left _ _, fun S hS σ n c hfan e hk_eq t => ?_⟩
    have hS1 : 1 ≤ S := (le_max_left 1 N).trans hS
    have hSN : N ≤ 4 * S := by
      have : N ≤ S := (le_max_right 1 N).trans hS
      omega
    have herr : 2 * D * θ ^ (4 * S) / (θ * q₁) < δ / 4 := by
      have hpow : θ ^ (4 * S) ≤ θ ^ N := pow_le_pow_of_le_one hθ0.le hθ1.le hSN
      have hq1_pos : 0 < θ * q₁ := mul_pos hθ0 hq₁_pos
      rw [div_lt_iff₀ hq1_pos]
      have hlt := (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 2 * D)).trans_lt
        (mul_lt_mul_of_pos_left hN (by positivity : 0 < 2 * D))
      have hsimp : 2 * D * (δ * (θ * q₁) / (8 * D)) = δ / 4 * (θ * q₁) := by field_simp; ring
      linarith
    set κ := κ₀ - 3 * δ / 4
    have hκ_ge : √2 / 2 ≤ κ := by
      have : δ ≤ κ₀ - √2 / 2 := min_le_right _ _
      dsimp only [κ]
      linarith
    have hdist_κ : dist κ κ₀ < δ₀ := by
      rw [Real.dist_eq, show κ - κ₀ = -(3 * δ / 4) by dsimp only [κ]; ring, abs_neg,
        abs_of_pos (by positivity)]
      have : δ ≤ δ₀ := min_le_left _ _
      linarith
    have harc_le : (k : ℝ) / (2 * π) * arccos (Hcap κ) ≤ p + η := by
      have H := (le_abs_self (arccos (Hcap κ) - arccos (Hcap κ₀))).trans
        (by simpa [Real.dist_eq] using (hcont_cap hdist_κ).le)
      rw [hHcap_eq] at H
      have hmul := mul_le_mul_of_nonneg_left H (by positivity : 0 ≤ (k : ℝ) / (2 * π))
      have hcancel : (k : ℝ) / (2 * π) * (2 * π * η / k) = η := by
        have hk_ne : (k : ℝ) ≠ 0 := by positivity
        field_simp
      linarith
    obtain ⟨w_e, hw_e_norm, hw_e_inner⟩ :=
      oneStep_le_inner_hyperUnitRow_center c K₀ hr hfan hθ0 hθ1.le hS1 e
    have hsw_eq : stepWeight c K₀ r θ (.inr e)
        (.inl (Classical.choose (Finset.card_pos.mp (Nat.zero_lt_of_lt e.2.1)))) = θ * q₁ := by
      dsimp only [stepWeight, bipBranch, q₁]
      have hk1 : ((hyperEdge c e.1).card - 1 : ℕ) = (k : ℝ) - 1 := by
        rw [hk_eq, Nat.cast_sub (by omega), Nat.cast_one]
      rw [hk1]
      ring
    have hκ_inner (v : HyperNode c) (hv : v ∈ hyperEdge c e.1) :
        κ ≤ ⟪hyperUnitRow c K₀ r θ S v, w_e⟫ := by
      have hcorr := hw_e_inner v hv
      rw [hsw_eq] at hcorr
      dsimp only [κ, g] at hg_close ⊢
      linarith
    have hsum_ang := InnerProductGeometry.sum_offDiag_angle_le hw_e_norm
      (fun v _ => norm_hyperUnitRow c K₀ r θ S v) hκ_ge hκ_inner
    have hH_eq : (((hyperEdge c e.1).card : ℝ) * κ ^ 2 - 1) /
        (((hyperEdge c e.1).card : ℝ) - 1) = Hcap κ := by
      rw [hk_eq]
    rw [hH_eq] at hsum_ang
    have hprob := measureReal_straddlesOn_le_of_sum_angle (hk_eq ▸ hk)
      (fun v _ => norm_hyperUnitRow c K₀ r θ S v) hsum_ang t
    have hev : {ω : HyperNode c → ℝ | HyperedgeStraddles (hyperEdge c e.1)
        {v | hyperScore c K₀ r θ S ω v < t}} =
        {ω | StraddlesOn (fun v => ⟪hyperUnitRow c K₀ r θ S v, WithLp.toLp 2 ω⟫) t
          ↑(hyperEdge c e.1)} := by
      ext ω
      exact hyperedgeStraddles_threshold_iff _ _ _
    rw [hev]
    rw [hk_eq] at hprob
    exact hprob.trans harc_le
  | starCone hk3 hlo hhi hp =>
    set ρ₀ := coneCorr r k
    have hρ₀_pos : 0 < ρ₀ := by
      dsimp only [ρ₀, coneCorr]
      have hk2_nn : 0 ≤ (k : ℝ) - 2 := by
        have : (3 : ℝ) ≤ k := by exact_mod_cast hk3
        linarith
      have hk1_nn : 0 ≤ (k : ℝ) - 1 := by linarith
      positivity
    obtain ⟨δ₀, hδ₀, hcont_arc⟩ := Metric.continuousAt_iff.mp
      (continuous_arccos.continuousAt (x := ρ₀)) (2 * π * η / k) (by positivity)
    set δ := min δ₀ ρ₀
    have hδ : 0 < δ := lt_min hδ₀ hρ₀_pos
    let qf : ℝ → ℝ := fun θ => θ ^ 2 * q₂
    let Qf : ℝ → ℝ := fun θ => (1 + ((k : ℝ) - 1) * qf θ ^ 2) / k
    let cf : ℝ → ℝ := fun θ =>
      (2 * qf θ + ((k : ℝ) - 2) * qf θ ^ 2) / (1 + ((k : ℝ) - 1) * qf θ ^ 2)
    have hqf_cont : Continuous qf := (continuous_pow 2).mul continuous_const
    have hQf_cont : Continuous Qf :=
      (continuous_const.add (continuous_const.mul (hqf_cont.pow 2))).div_const _
    have hcf_cont : ContinuousAt cf 1 := by
      dsimp only [cf]
      refine ((continuous_const.mul hqf_cont |>.add
        (continuous_const.mul (hqf_cont.pow 2))).continuousAt).div
        (continuous_const.add (continuous_const.mul (hqf_cont.pow 2))).continuousAt ?_
      have : 0 ≤ (k : ℝ) - 1 := by linarith
      have : 0 ≤ qf 1 ^ 2 := sq_nonneg _
      positivity
    have hgap1_cont : ContinuousAt (fun θ => Qf θ - qf θ) 1 :=
      (hQf_cont.sub hqf_cont).continuousAt
    have hgap2_cont : ContinuousAt (fun θ => 2 * qf θ * √(Qf θ) - (Qf θ - qf θ)) 1 :=
      (((continuous_const.mul hqf_cont).mul
        (continuous_sqrt.comp hQf_cont)).sub (hQf_cont.sub hqf_cont)).continuousAt
    have hgap1_pos : 0 < Qf 1 - qf 1 := by
      simpa [Qf, qf, coneMeanSq, q₂] using sub_pos.mpr hlo
    have hgap2_pos : 0 < 2 * qf 1 * √(Qf 1) - (Qf 1 - qf 1) := by
      simpa [Qf, qf, coneMeanSq, q₂] using sub_pos.mpr hhi
    have hcf1 : cf 1 = ρ₀ := by simp [cf, qf, ρ₀, coneCorr, q₂]
    obtain ⟨γ₁, hγ₁, hc1⟩ := Metric.continuousAt_iff.mp hcf_cont (δ / 2) (half_pos hδ)
    obtain ⟨γ₂, hγ₂, hc2⟩ := Metric.continuousAt_iff.mp hgap1_cont ((Qf 1 - qf 1) / 2)
      (half_pos hgap1_pos)
    obtain ⟨γ₃, hγ₃, hc3⟩ := Metric.continuousAt_iff.mp hgap2_cont
      ((2 * qf 1 * √(Qf 1) - (Qf 1 - qf 1)) / 2) (half_pos hgap2_pos)
    set γ := min γ₁ (min γ₂ γ₃)
    have hγ : 0 < γ := lt_min hγ₁ (lt_min hγ₂ hγ₃)
    set θ₀ := 1 - min γ (1 / 2) / 2
    have hθ₀_mem : θ₀ ∈ Ioo (0 : ℝ) 1 := by
      have hmin_pos : 0 < min γ (1 / 2) := lt_min hγ (by norm_num)
      have hmin_le : min γ (1 / 2) ≤ 1 / 2 := min_le_right _ _
      exact ⟨by dsimp only [θ₀]; linarith, by dsimp only [θ₀]; linarith⟩
    refine ⟨θ₀, hθ₀_mem, fun θ hθ => ?_⟩
    have hθ0 : 0 < θ := hθ₀_mem.1.trans hθ.1
    have hθ1 : θ < 1 := hθ.2
    have hdist_θ : dist θ 1 < γ := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      have : min γ (1 / 2) ≤ γ := min_le_left _ _
      have : θ₀ < θ := hθ.1
      dsimp only [θ₀] at this
      linarith
    have hcf_close : ρ₀ - δ / 2 < cf θ := by
      have H := hc1 (hdist_θ.trans_le (min_le_left _ _))
      rw [Real.dist_eq, hcf1] at H
      linarith [neg_abs_le (cf θ - ρ₀)]
    have htan_lo_θ : qf θ ≤ Qf θ := by
      have H := hc2 (hdist_θ.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
      rw [Real.dist_eq] at H
      linarith [neg_abs_le ((Qf θ - qf θ) - (Qf 1 - qf 1))]
    have htan_hi_θ : Qf θ - qf θ ≤ 2 * qf θ * √(Qf θ) := by
      have H := hc3 (hdist_θ.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
      rw [Real.dist_eq] at H
      linarith [neg_abs_le ((2 * qf θ * √(Qf θ) - (Qf θ - qf θ)) -
        (2 * qf 1 * √(Qf 1) - (Qf 1 - qf 1)))]
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < δ / (32 * √D)) hθ1
    refine ⟨max 1 (N + 1), le_max_left _ _, fun S hS σ n c hfan e hk_eq t => ?_⟩
    have hS1 : 1 ≤ S := (le_max_left 1 (N + 1)).trans hS
    have hSN : N ≤ 2 * S - 1 := by
      have : N + 1 ≤ S := (le_max_right 1 (N + 1)).trans hS
      omega
    have herr : 8 * √D * θ ^ (2 * S - 1) < δ / 4 := by
      have hpow : θ ^ (2 * S - 1) ≤ θ ^ N := pow_le_pow_of_le_one hθ0.le hθ1.le hSN
      have hlt := (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 8 * √D)).trans_lt
        (mul_lt_mul_of_pos_left hN (by positivity : 0 < 8 * √D))
      have hsimp : 8 * √D * (δ / (32 * √D)) = δ / 4 := by
        have hsqD : √D ≠ 0 := (sqrt_pos.mpr hD_pos).ne'
        field_simp
        ring
      linarith
    set ρ := ρ₀ - 3 * δ / 4
    have hρ0 : 0 ≤ ρ := by
      have : δ ≤ ρ₀ := min_le_right _ _
      dsimp only [ρ]
      linarith
    have hdist_ρ : dist ρ ρ₀ < δ₀ := by
      rw [Real.dist_eq, show ρ - ρ₀ = -(3 * δ / 4) by dsimp only [ρ]; ring, abs_neg,
        abs_of_pos (by positivity)]
      have : δ ≤ δ₀ := min_le_left _ _
      linarith
    have harc_le : (k : ℝ) / (2 * π) * arccos ρ ≤ p + η := by
      have H := (le_abs_self (arccos ρ - arccos ρ₀)).trans
        (by simpa [Real.dist_eq] using (hcont_arc hdist_ρ).le)
      have hmul := mul_le_mul_of_nonneg_left H (by positivity : 0 ≤ (k : ℝ) / (2 * π))
      have hcancel : (k : ℝ) / (2 * π) * (2 * π * η / k) = η := by
        have hk_ne : (k : ℝ) ≠ 0 := by positivity
        field_simp
      linarith
    have hq_eq : θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1)) = qf θ := by
      rw [hk_eq]
      dsimp only [qf, q₂]
      ring
    have hlo_e : θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1)) ≤
        (1 + (((hyperEdge c e.1).card : ℝ) - 1) *
          (θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1))) ^ 2) /
          (hyperEdge c e.1).card := by
      rw [hq_eq, hk_eq]
      exact htan_lo_θ
    have hhi_e : (1 + (((hyperEdge c e.1).card : ℝ) - 1) *
        (θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1))) ^ 2) /
        (hyperEdge c e.1).card -
        θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1)) ≤
      2 * (θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1))) *
        √((1 + (((hyperEdge c e.1).card : ℝ) - 1) *
          (θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1))) ^ 2) /
          (hyperEdge c e.1).card) := by
      rw [hq_eq, hk_eq]
      exact htan_hi_θ
    have hcone_sum := starCone_le_sum_offDiag_inner_hyperUnitRow c K₀ hr hfan hθ0 hθ1.le hS1 e
      (hk_eq ▸ hk3) hlo_e hhi_e
    dsimp only at hcone_sum
    rw [hq_eq, hk_eq] at hcone_sum
    have hsum_ang : ∑ pq ∈ (hyperEdge c e.1).offDiag,
        InnerProductGeometry.angle (hyperUnitRow c K₀ r θ S pq.1)
          (hyperUnitRow c K₀ r θ S pq.2) ≤
        ((hyperEdge c e.1).card : ℝ) * (((hyperEdge c e.1).card : ℝ) - 1) * arccos ρ := by
      have hcard : ((hyperEdge c e.1).offDiag.card : ℝ) =
          (k : ℝ) * ((k : ℝ) - 1) := by
        rw [Finset.offDiag_card, hk_eq, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
        ring
      have hrew : ∑ pq ∈ (hyperEdge c e.1).offDiag,
          InnerProductGeometry.angle (hyperUnitRow c K₀ r θ S pq.1)
            (hyperUnitRow c K₀ r θ S pq.2) =
          ∑ pq ∈ (hyperEdge c e.1).offDiag,
            arccos ⟪hyperUnitRow c K₀ r θ S pq.1, hyperUnitRow c K₀ r θ S pq.2⟫ :=
        Finset.sum_congr rfl fun pq _ =>
          InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one
            (norm_hyperUnitRow c K₀ r θ S pq.1) (norm_hyperUnitRow c K₀ r θ S pq.2)
      rw [hrew, hk_eq, ← hcard]
      refine Real.sum_arccos_le_card_mul_arccos _ (fun pq _ => ⟨?_, ?_⟩) ?_
      · exact inner_hyperUnitRow_nonneg c K₀ r hθ0.le S pq.1 pq.2
      · exact (real_inner_le_norm _ _).trans_eq
          (by rw [norm_hyperUnitRow, norm_hyperUnitRow, one_mul])
      · rw [hcard]
        have hk3R : (3 : ℝ) ≤ k := by exact_mod_cast hk3
        have hk_prod_nn : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
        have hρ_le : ρ ≤ cf θ - 8 * √D * θ ^ (2 * S - 1) := by
          dsimp only [ρ]
          linarith
        exact (mul_le_mul_of_nonneg_left hρ_le hk_prod_nn).trans hcone_sum
    have hprob := measureReal_straddlesOn_le_of_sum_angle (hk_eq ▸ hk)
      (fun v _ => norm_hyperUnitRow c K₀ r θ S v) hsum_ang t
    have hev : {ω : HyperNode c → ℝ | HyperedgeStraddles (hyperEdge c e.1)
        {v | hyperScore c K₀ r θ S ω v < t}} =
        {ω | StraddlesOn (fun v => ⟪hyperUnitRow c K₀ r θ S v, WithLp.toLp 2 ω⟫) t
          ↑(hyperEdge c e.1)} := by
      ext ω
      exact hyperedgeStraddles_threshold_iff _ _ _
    rw [hev]
    rw [hk_eq] at hprob
    exact hprob.trans harc_le

/-- Uniform `(θ, S)` across all `k ∈ [2, K₀]` for a `HyperDualCert r K₀ a b`. -/
private theorem exists_uniform_theta_radius {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) {η : ℝ} (hη : 0 < η) :
    ∃ θ ∈ Ioo (0 : ℝ) 1, ∃ S : ℕ, 1 ≤ S ∧
      ∀ {σ : Signature} {n : ℕ} (c : Circuit σ n 1), c.FanInAtMost r →
        ∀ (e : PrunedEdge c K₀) (t : ℝ),
          (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
            {ω | HyperedgeStraddles (hyperEdge c e.1)
              {v | hyperScore c K₀ r θ S ω v < t}} ≤
            (a : ℝ) * (hyperEdge c e.1).card + b + η := by
  classical
  let I := Finset.Icc 2 K₀
  have hI_ne : I.Nonempty := Finset.nonempty_Icc.mpr hcert.hK₀
  have hex (k : I) := exists_theta_radius_of_hyperEdgeBound (K₀ := K₀) hcert.hr
    (Finset.mem_Icc.mp k.2).1 hη (hcert.hedge k.1 k.2)
  let θ_of (k : I) : ℝ := Classical.choose (hex k)
  have hθ_spec (k : I) := Classical.choose_spec (hex k)
  let θ_img : Finset ℝ := (Finset.univ : Finset I).image θ_of
  have hθ_img_ne : θ_img.Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨2, Finset.mem_Icc.mpr ⟨le_rfl, hcert.hK₀⟩⟩⟩ |>.image θ_of
  let θ_max : ℝ := θ_img.max' hθ_img_ne
  have hθ_max_lt : θ_max < 1 := by
    obtain ⟨k_star, _, hk_star_eq⟩ := Finset.mem_image.mp (Finset.max'_mem θ_img hθ_img_ne)
    dsimp only [θ_max]
    rw [← hk_star_eq]
    exact (hθ_spec k_star).1.2
  have hθ_max_pos : 0 < θ_max := by
    let k₂ : I := ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, hcert.hK₀⟩⟩
    exact (hθ_spec k₂).1.1.trans_le
      (Finset.le_max' θ_img (θ_of k₂) (Finset.mem_image.mpr ⟨k₂, Finset.mem_univ k₂, rfl⟩))
  set θ := (θ_max + 1) / 2
  have hθ_mem : θ ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp only [θ]; linarith, by dsimp only [θ]; linarith⟩
  have hθ_k (k : I) : θ ∈ Ioo (θ_of k) 1 := by
    have hle : θ_of k ≤ θ_max :=
      Finset.le_max' θ_img (θ_of k) (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
    exact ⟨by dsimp only [θ]; linarith, hθ_mem.2⟩
  let S_of (k : I) : ℕ := Classical.choose ((hθ_spec k).2 θ (hθ_k k))
  have hS_spec (k : I) := Classical.choose_spec ((hθ_spec k).2 θ (hθ_k k))
  set S : ℕ := max 1 ((Finset.univ : Finset I).sup S_of)
  refine ⟨θ, hθ_mem, S, le_max_left _ _, fun c hfan e t => ?_⟩
  let k_e : I := ⟨(hyperEdge c e.1).card, Finset.mem_Icc.mpr ⟨e.2.1, e.2.2⟩⟩
  have hS_ge : S_of k_e ≤ S :=
    (Finset.le_sup (f := S_of) (Finset.mem_univ k_e)).trans (le_max_right _ _)
  exact (hS_spec k_e).2 S hS_ge c hfan e rfl t

end ParameterSelection

/-! ### Grid control, local concentration, and unconditional layout existence -/

section GridAndLayout

variable {σ : Signature} {n : ℕ}

/-- Every circuit of fan-in at most `r` has at most `(r + 1) |HyperNode c|` live signals. -/
private theorem card_liveSignal_le {c : Circuit σ n 1} {r : ℕ} (hfan : c.FanInAtMost r) :
    Fintype.card (LiveSignal c) ≤ (r + 1) * Nat.card (HyperNode c) := by
  have h1 : Fintype.card (LiveSignal c) ≤ ∑ w : LiveSignal c, (hyperEdge c w).card := by
    calc Fintype.card (LiveSignal c) = ∑ _w : LiveSignal c, 1 := by simp
      _ ≤ ∑ w : LiveSignal c, (hyperEdge c w).card :=
          Finset.sum_le_sum fun w _ => card_hyperEdge_pos c w
  have h2 := sum_card_hyperEdge_le hfan
  have hnode : Nat.card (HyperNode c) = Fintype.card (LiveGate c) + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_unique (α := Unit)]
  rw [hnode]
  calc Fintype.card (LiveSignal c) ≤ (r + 1) * Fintype.card (LiveGate c) + 1 := h1.trans h2
    _ ≤ (r + 1) * Fintype.card (LiveGate c) + (r + 1) := Nat.add_le_add_left (Nat.le_add_left 1 r) _
    _ = (r + 1) * (Fintype.card (LiveGate c) + 1) := by ring

/-- Any finset `F` of live signals each meeting `S : Set (HyperNode c)` has cardinality at most
`(r + 1) |S|`. -/
private theorem card_touching_signals_le_of_subset {c : Circuit σ n 1} {r : ℕ}
    (hfan : c.FanInAtMost r) (S : Set (HyperNode c)) (F : Finset (LiveSignal c))
    (hF : ∀ w ∈ F, ∃ u ∈ hyperEdge c w, u ∈ S) :
    F.card ≤ (r + 1) * S.ncard := by
  have : DecidablePred (· ∈ S) := Classical.decPred _
  have hsub : F ⊆ S.toFinset.biUnion fun u => Finset.univ.filter fun w => u ∈ hyperEdge c w := by
    intro w hw
    obtain ⟨u, huw, huS⟩ := hF w hw
    exact Finset.mem_biUnion.mpr
      ⟨u, mem_toFinset.mpr huS, Finset.mem_filter.mpr ⟨Finset.mem_univ w, huw⟩⟩
  calc F.card
      ≤ (S.toFinset.biUnion fun u => Finset.univ.filter fun w => u ∈ hyperEdge c w).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ u ∈ S.toFinset, (Finset.univ.filter fun w => u ∈ hyperEdge c w).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ S.toFinset, (r + 1) := Finset.sum_le_sum fun u _ => card_signals_at_node_le hfan u
    _ = (r + 1) * S.ncard := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm, ncard_eq_toFinset_card' S]

/-- **Grid control for hypergraphs.** Sorting `HyperNode c` by `score` yields a layout of
`hyperWidth c lay ≤ B` whenever the lower tail, upper tail, and each grid threshold plus window
count are bounded by `B`. -/
private theorem exists_hyperWidth_le_of_vertexScore {c : Circuit σ n 1} {r : ℕ}
    (hfan : c.FanInAtMost r) (score : HyperNode c → ℝ) {a₀ δ : ℝ} (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : ((r + 1 : ℕ) : ℝ) * ({v | score v < a₀}.ncard : ℝ) ≤ B)
    (high : ((r + 1 : ℕ) : ℝ) * ({v | a₀ + M * δ ≤ score v}.ncard : ℝ) ≤ B)
    (mid : ∀ i < M, ((hyperCut c {v | score v < a₀ + i * δ}).card : ℝ) +
      ((r + 1 : ℕ) : ℝ) * ({v | a₀ + i * δ ≤ score v ∧ score v < a₀ + (i + 1) * δ}.ncard : ℝ) ≤ B) :
    ∃ lay : Layout (HyperNode c), (hyperWidth c lay : ℝ) ≤ B := by
  obtain ⟨lay, hlay⟩ := Layout.exists_threshold score
  have hB0 : 0 ≤ B := le_trans (by positivity) low
  refine ⟨lay, ?_⟩
  have hsup : hyperWidth c lay ≤ ⌊B⌋₊ := by
    unfold hyperWidth
    refine Finset.sup_le fun t ht => Nat.le_floor ?_
    have ht_lt : t < Nat.card (HyperNode c) := Finset.mem_range.mp ht
    obtain ⟨m, hP, hPc⟩ := hlay t ht_lt
    set P := lay.initial t
    have count_touch (S : Set (HyperNode c))
        (hsub : ∀ w ∈ hyperCut c P, ∃ u ∈ hyperEdge c w, u ∈ S) :
        ((hyperCut c P).card : ℝ) ≤ ((r + 1 : ℕ) : ℝ) * S.ncard := by
      exact_mod_cast card_touching_signals_le_of_subset hfan S (hyperCut c P) hsub
    by_cases hlo : m < a₀
    · refine (count_touch {v | score v < a₀} fun w hw => ?_).trans low
      obtain ⟨⟨u, huw, huP⟩, -⟩ := mem_hyperCut_iff.mp hw
      exact ⟨u, huw, (hP u huP).trans_lt hlo⟩
    by_cases hhi : a₀ + M * δ ≤ m
    · refine (count_touch {v | a₀ + M * δ ≤ score v} fun w hw => ?_).trans high
      obtain ⟨-, ⟨v, hvw, hvP⟩⟩ := mem_hyperCut_iff.mp hw
      exact ⟨v, hvw, hhi.trans (hPc v hvP)⟩
    obtain ⟨i, hi, ht_lo, ht_hi⟩ := exists_grid_index hδ (M := M) (not_lt.mp hlo) (not_le.mp hhi)
    let W := {v : HyperNode c | a₀ + i * δ ≤ score v ∧ score v < a₀ + (i + 1) * δ}
    have : DecidablePred (fun w : LiveSignal c => ∃ u ∈ hyperEdge c w, u ∈ W) :=
      Classical.decPred _
    let FW := (Finset.univ : Finset (LiveSignal c)).filter fun w => ∃ u ∈ hyperEdge c w, u ∈ W
    have hsplit : hyperCut c P ⊆ hyperCut c {v | score v < a₀ + i * δ} ∪ FW := by
      intro w hw
      obtain ⟨⟨u, huw, huP⟩, ⟨v, hvw, hvP⟩⟩ := mem_hyperCut_iff.mp hw
      by_cases hut : score u < a₀ + i * δ
      · exact Finset.mem_union_left _ (mem_hyperCut_iff.mpr
          ⟨⟨u, huw, hut⟩, ⟨v, hvw, not_lt.mpr (ht_lo.trans (hPc v hvP))⟩⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ w,
          u, huw, not_lt.mp hut, (hP u huP).trans_lt ht_hi⟩)
    have hFW : FW.card ≤ (r + 1) * W.ncard :=
      card_touching_signals_le_of_subset hfan W FW fun w hw => (Finset.mem_filter.mp hw).2
    have hnat : (hyperCut c P).card ≤
        (hyperCut c {v | score v < a₀ + i * δ}).card + (r + 1) * W.ncard :=
      (Finset.card_le_card hsplit).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left hFW _))
    have hreal : ((hyperCut c P).card : ℝ) ≤
        (hyperCut c {v | score v < a₀ + i * δ}).card + ((r + 1 : ℕ) : ℝ) * W.ncard := by
      exact_mod_cast hnat
    exact hreal.trans (mid i hi)
  exact (Nat.cast_le.mpr hsup).trans (Nat.floor_le hB0)

/-- Support ball of `x : BipNode c K₀` on `HyperNode c` at bipartite distance `L`. -/
private def bipSupportBall (c : Circuit σ n 1) (K₀ : ℕ) (x : BipNode c K₀) (L : ℕ) :
    Set (HyperNode c) :=
  {z | (bipSimpleGraph c K₀).edist x (.inl z) ≤ L}

private theorem hyperScore_congr {c : Circuit σ n 1} {K₀ r : ℕ} {θ : ℝ} {S : ℕ} {v : HyperNode c}
    {ω ω' : HyperNode c → ℝ} (h : ∀ z ∈ bipSupportBall c K₀ (.inl v) (2 * S), ω z = ω' z) :
    hyperScore c K₀ r θ S ω v = hyperScore c K₀ r θ S ω' v := by
  refine Gaussian.inner_toLp_congr (fun z hz => ?_) h
  have hw0 : walkMax c K₀ r θ (2 * S) (.inl v) z = 0 := by
    by_contra hne
    exact hz (edist_le_of_walkMax_ne_zero c K₀ hne)
  simp [hyperUnitRow, hw0]

private theorem card_overlap_bipSupportBall_le {c : Circuit σ n 1} {K₀ r : ℕ}
    (hfan : c.FanInAtMost r) {κ : Type*} {emb : κ → BipNode c K₀} (hemb : Function.Injective emb)
    (L : ℕ) (i : κ) [Fintype κ] :
    open Classical in
    (Finset.univ.filter fun j : κ =>
      ¬Disjoint (bipSupportBall c K₀ (emb i) L) (bipSupportBall c K₀ (emb j) L)).card ≤
      (max (r + 1) K₀ + 1) ^ (2 * L) := by
  classical
  let ball := Finset.univ.filter fun y : BipNode c K₀ =>
    (bipSimpleGraph c K₀).edist (emb i) y ≤ ((2 * L : ℕ) : ℕ∞)
  have hmaps : ∀ j ∈ Finset.univ.filter (fun j : κ =>
      ¬Disjoint (bipSupportBall c K₀ (emb i) L) (bipSupportBall c K₀ (emb j) L)),
      emb j ∈ ball := by
    intro j hj
    obtain ⟨z, hzi, hzj⟩ := Set.not_disjoint_iff.mp (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    calc (bipSimpleGraph c K₀).edist (emb i) (emb j)
        ≤ (bipSimpleGraph c K₀).edist (emb i) (.inl z) +
          (bipSimpleGraph c K₀).edist (.inl z) (emb j) := SimpleGraph.edist_triangle
      _ = (bipSimpleGraph c K₀).edist (emb i) (.inl z) +
          (bipSimpleGraph c K₀).edist (emb j) (.inl z) := by
            rw [SimpleGraph.edist_comm (G := bipSimpleGraph c K₀)
              (u := (Sum.inl z : BipNode c K₀))]
      _ ≤ (L : ℕ∞) + L := add_le_add hzi hzj
      _ = ((2 * L : ℕ) : ℕ∞) := by push_cast; ring
  have hinj_card : (Finset.univ.filter fun j : κ =>
      ¬Disjoint (bipSupportBall c K₀ (emb i) L) (bipSupportBall c K₀ (emb j) L)).card ≤
      ball.card :=
    Finset.card_le_card_of_injOn emb hmaps fun _ _ _ _ h => hemb h
  exact hinj_card.trans
    (SimpleGraph.card_edist_le_le (degree_bipSimpleGraph_le c K₀ hfan) (emb i) (2 * L))

/-- Dual-LP pin-counting bound on `LiveSignal c`: the deterministic supply
`((r + 1) a + b) |LiveGate c| + max b (-a) |LiveInput c| + a` is nonnegative and dominates the sum
of pruned expected straddling probabilities plus the cardinality of large signals (`|e| > K₀`). -/
private theorem dualSupply_nonneg_and_sum_le {c : Circuit σ n 1} {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) (hfan : c.FanInAtMost r) {η₀ : ℝ} (hη₀ : 0 ≤ η₀)
    (P_cross : PrunedEdge c K₀ → ℝ)
    (hP : ∀ e : PrunedEdge c K₀, P_cross e ≤ (a : ℝ) * (hyperEdge c e.1).card + b + η₀) :
    let B_main := (((r + 1 : ℕ) : ℝ) * a + b) * Fintype.card (LiveGate c) +
      max (b : ℝ) (-a) * Fintype.card (LiveInput c) + a
    0 ≤ B_main ∧
      (∑ e : PrunedEdge c K₀, P_cross e) +
        (((Finset.univ : Finset (LiveSignal c)).filter
          fun w => K₀ < (hyperEdge c w).card).card : ℝ) ≤
        B_main + (Nat.card (HyperNode c) : ℝ) * (η₀ * ((r + 1 : ℕ) : ℝ)) := by
  intro B_main
  have ha_pos : (0 : ℝ) < a := Rat.cast_pos.mpr hcert.ha
  have h2_nn : (0 : ℝ) ≤ 2 * a + b := by exact_mod_cast hcert.h2
  have hpin : (∑ x : LiveInput c, ((hyperEdge c (.inl x)).card : ℝ)) +
      (∑ x : LiveGate c, ((hyperEdge c (.inr x)).card : ℝ)) ≤
      ((r + 1 : ℕ) : ℝ) * Fintype.card (LiveGate c) + 1 := by
    have h := sum_card_hyperEdge_le hfan
    rw [Fintype.sum_sum_type] at h
    exact_mod_cast h
  have hB_nn : 0 ≤ B_main := by
    have hgate_nn (g : LiveGate c) : (0 : ℝ) ≤ (a : ℝ) * (hyperEdge c (.inr g)).card + b := by
      have hk2 : (2 : ℝ) ≤ (hyperEdge c (.inr g)).card :=
        Nat.ofNat_le_cast.mpr (two_le_card_hyperEdge_gate c g)
      nlinarith
    have hinp_nn (i : LiveInput c) :
        (0 : ℝ) ≤ (a : ℝ) * (hyperEdge c (.inl i)).card + max (b : ℝ) (-a) := by
      have hk1 : (1 : ℝ) ≤ (hyperEdge c (.inl i)).card :=
        Nat.one_le_cast.mpr (card_hyperEdge_pos c (.inl i))
      nlinarith [le_max_right (b : ℝ) (-a)]
    have hsum_nn : 0 ≤ (∑ g : LiveGate c, ((a : ℝ) * (hyperEdge c (.inr g)).card + b)) +
        ∑ i : LiveInput c, ((a : ℝ) * (hyperEdge c (.inl i)).card + max (b : ℝ) (-a)) :=
      add_nonneg (Finset.sum_nonneg fun g _ => hgate_nn g)
        (Finset.sum_nonneg fun i _ => hinp_nn i)
    have hsum_le : (∑ g : LiveGate c, ((a : ℝ) * (hyperEdge c (.inr g)).card + b)) +
        (∑ i : LiveInput c, ((a : ℝ) * (hyperEdge c (.inl i)).card + max (b : ℝ) (-a))) ≤
        B_main := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
        Finset.card_univ, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, ← Finset.mul_sum,
        ← Finset.mul_sum]
      dsimp only [B_main]
      nlinarith [hpin]
    exact hsum_nn.trans hsum_le
  refine ⟨hB_nn, ?_⟩
  let wt : LiveSignal c → ℝ := fun w => match w with
    | .inr g => (a : ℝ) * (hyperEdge c (.inr g)).card + b + η₀
    | .inl i => (a : ℝ) * (hyperEdge c (.inl i)).card + max (b : ℝ) (-a) + η₀
  have hwt_nn (w : LiveSignal c) : 0 ≤ wt w := by
    rcases w with i | g
    · have hk1 : (1 : ℝ) ≤ (hyperEdge c (.inl i)).card :=
        Nat.one_le_cast.mpr (card_hyperEdge_pos c (.inl i))
      dsimp only [wt]
      nlinarith [le_max_right (b : ℝ) (-a)]
    · have hk2 : (2 : ℝ) ≤ (hyperEdge c (.inr g)).card :=
        Nat.ofNat_le_cast.mpr (two_le_card_hyperEdge_gate c g)
      dsimp only [wt]
      nlinarith
  have hwt_ge (w : LiveSignal c) : (a : ℝ) * (hyperEdge c w).card + b + η₀ ≤ wt w := by
    rcases w with i | g
    · dsimp only [wt]; linarith [le_max_left (b : ℝ) (-a)]
    · exact le_rfl
  let F_mid := (Finset.univ : Finset (LiveSignal c)).filter fun w =>
    2 ≤ (hyperEdge c w).card ∧ (hyperEdge c w).card ≤ K₀
  let S_big := (Finset.univ : Finset (LiveSignal c)).filter fun w => K₀ < (hyperEdge c w).card
  have hdisj : Disjoint F_mid S_big := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    have := (Finset.mem_filter.mp h1).2.2
    have := (Finset.mem_filter.mp h2).2
    omega
  have hsum_pruned : ∑ e : PrunedEdge c K₀, P_cross e ≤ ∑ w ∈ F_mid, wt w := by
    calc ∑ e : PrunedEdge c K₀, P_cross e
        ≤ ∑ e : PrunedEdge c K₀, wt e.1 := Finset.sum_le_sum fun e _ => (hP e).trans (hwt_ge e.1)
      _ = ∑ w ∈ F_mid, wt w :=
          Finset.sum_bij (fun e _ => e.1)
            (fun e _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩)
            (fun _ _ _ _ h => Subtype.ext h)
            (fun w hw => ⟨⟨w, (Finset.mem_filter.mp hw).2⟩, Finset.mem_univ _, rfl⟩)
            (fun _ _ => rfl)
  have hsum_big : (S_big.card : ℝ) ≤ ∑ w ∈ S_big, wt w := by
    calc (S_big.card : ℝ) = ∑ _w ∈ S_big, (1 : ℝ) := by simp
      _ ≤ ∑ w ∈ S_big, wt w := Finset.sum_le_sum fun w hw => by
          have hk_gt : (K₀ + 1 : ℝ) ≤ (hyperEdge c w).card := by
            have : K₀ + 1 ≤ (hyperEdge c w).card := (Finset.mem_filter.mp hw).2
            exact_mod_cast this
          have htailR : (1 : ℝ) ≤ (a : ℝ) * (K₀ + 1) + b := by exact_mod_cast hcert.htail
          have h1 : (1 : ℝ) ≤ (a : ℝ) * (hyperEdge c w).card + b + η₀ := by nlinarith
          exact h1.trans (hwt_ge w)
  have hsig : (Fintype.card (LiveInput c) : ℝ) + Fintype.card (LiveGate c) ≤
      ((r + 1 : ℕ) : ℝ) * Nat.card (HyperNode c) := by
    have hs := card_liveSignal_le hfan
    rw [Fintype.card_sum] at hs
    exact_mod_cast hs
  have htot_wt : ∑ w : LiveSignal c, wt w ≤
      B_main + (Nat.card (HyperNode c) : ℝ) * (η₀ * ((r + 1 : ℕ) : ℝ)) := by
    rw [Fintype.sum_sum_type]
    dsimp only [wt, B_main]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum]
    nlinarith [hpin, hsig]
  calc (∑ e : PrunedEdge c K₀, P_cross e) + (S_big.card : ℝ)
      ≤ (∑ w ∈ F_mid, wt w) + ∑ w ∈ S_big, wt w := add_le_add hsum_pruned hsum_big
    _ = ∑ w ∈ F_mid ∪ S_big, wt w := (Finset.sum_union hdisj).symm
    _ ≤ ∑ w : LiveSignal c, wt w :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun w _ _ => hwt_nn w
    _ ≤ B_main + (Nat.card (HyperNode c) : ℝ) * (η₀ * ((r + 1 : ℕ) : ℝ)) := htot_wt

private def hyperCrossEvent (c : Circuit σ n 1) (K₀ r : ℕ) (θ : ℝ) (S : ℕ) (t : ℝ)
    (e : PrunedEdge c K₀) : Set (HyperNode c → ℝ) :=
  {ω | HyperedgeStraddles (hyperEdge c e.1) {v | hyperScore c K₀ r θ S ω v < t}}

private def hyperVertEvent (c : Circuit σ n 1) (K₀ r : ℕ) (θ : ℝ) (S : ℕ) (f : ℝ → Prop)
    (v : HyperNode c) : Set (HyperNode c → ℝ) :=
  {ω | f (hyperScore c K₀ r θ S ω v)}

/-- Grid-threshold bound on `(hyperCut c {v | hyperScore ... < t}).card` from concentration of
pruned hyperedges. -/
private theorem card_hyperCut_threshold_le {c : Circuit σ n 1} {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) (hfan : c.FanInAtMost r) {η₀ c_dev : ℝ} (hη₀ : 0 ≤ η₀)
    (θ : ℝ) (S : ℕ) (ω : HyperNode c → ℝ) (t : ℝ)
    (hprob : ∀ e : PrunedEdge c K₀,
      (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real (hyperCrossEvent c K₀ r θ S t e) ≤
        (a : ℝ) * (hyperEdge c e.1).card + b + η₀)
    (hdev : ω ∉ Gaussian.deviation (hyperCrossEvent c K₀ r θ S t) c_dev) :
    ((hyperCut c {v | hyperScore c K₀ r θ S ω v < t}).card : ℝ) ≤
      ((((r + 1 : ℕ) : ℝ) * a + b) * Fintype.card (LiveGate c) +
        max (b : ℝ) (-a) * Fintype.card (LiveInput c) + a) +
        (Nat.card (HyperNode c) : ℝ) * (η₀ * ((r + 1 : ℕ) : ℝ)) + c_dev := by
  let S_cut := hyperCut c {v | hyperScore c K₀ r θ S ω v < t}
  let S_mid := S_cut.filter fun w => 2 ≤ (hyperEdge c w).card ∧ (hyperEdge c w).card ≤ K₀
  let S_big := (Finset.univ : Finset (LiveSignal c)).filter fun w => K₀ < (hyperEdge c w).card
  have hcut_sub : S_cut ⊆ S_mid ∪ S_big := by
    intro w hw
    by_cases hle : (hyperEdge c w).card ≤ K₀
    · have hk2 : 2 ≤ (hyperEdge c w).card := by
        obtain ⟨⟨u, hu, h1⟩, ⟨v, hv, h2⟩⟩ := mem_hyperCut_iff.mp hw
        have huv : u ≠ v := fun h => by subst h; exact h2 h1
        exact Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv⟩
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, hk2, hle⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ w, not_le.mp hle⟩)
  have hmid_card : S_mid.card =
      {e : PrunedEdge c K₀ | ω ∈ hyperCrossEvent c K₀ r θ S t e}.ncard := by
    have : DecidablePred (fun e : PrunedEdge c K₀ => ω ∈ hyperCrossEvent c K₀ r θ S t e) :=
      Classical.decPred _
    rw [ncard_eq_toFinset_card']
    refine Finset.card_bij (fun w hw => ⟨w, (Finset.mem_filter.mp hw).2⟩)
      (fun w hw => mem_toFinset.mpr (mem_hyperCut_iff.mp (Finset.mem_filter.mp hw).1))
      (fun _ _ _ _ h => congrArg Subtype.val h)
      (fun e he => ⟨e.1, Finset.mem_filter.mpr ⟨mem_hyperCut_iff.mpr (mem_toFinset.mp he), e.2⟩,
        Subtype.ext rfl⟩)
  have hcard_cut : (S_cut.card : ℝ) ≤ (S_mid.card : ℝ) + (S_big.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hcut_sub).trans (Finset.card_union_le _ _)
  have hmid_lt : (S_mid.card : ℝ) <
      (∑ e : PrunedEdge c K₀,
        (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
          (hyperCrossEvent c K₀ r θ S t e)) + c_dev := by
    rw [hmid_card]
    exact Gaussian.ncard_lt_of_notMem_deviation hdev
  have hsum := (dualSupply_nonneg_and_sum_le hcert hfan hη₀
    (fun e => (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
      (hyperCrossEvent c K₀ r θ S t e)) hprob).2
  linarith [hcard_cut, hmid_lt, hsum]

private theorem ncard_hyperWindow_le {c : Circuit σ n 1} {K₀ r : ℕ} {θ : ℝ} {S : ℕ}
    {ω : HyperNode c → ℝ} {a₀ δ c_dev : ℝ} (hδ : 0 ≤ δ)
    (hdev : ω ∉ Gaussian.deviation
      (hyperVertEvent c K₀ r θ S fun x => a₀ ≤ x ∧ x < a₀ + δ) c_dev) :
    ({v : HyperNode c |
      a₀ ≤ hyperScore c K₀ r θ S ω v ∧ hyperScore c K₀ r θ S ω v < a₀ + δ}.ncard : ℝ) ≤
      (Nat.card (HyperNode c) : ℝ) * (δ / √(2 * π)) + c_dev := by
  have hW := Gaussian.ncard_lt_of_notMem_deviation hdev
  have hWm : ∑ v : HyperNode c,
      (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
        (hyperVertEvent c K₀ r θ S (fun x => a₀ ≤ x ∧ x < a₀ + δ) v) ≤
      (Nat.card (HyperNode c) : ℝ) * (δ / √(2 * π)) := by
    refine (Finset.sum_le_sum fun v _ =>
      Gaussian.measureReal_window_le (norm_hyperUnitRow c K₀ r θ S v) a₀ hδ).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hset : {v : HyperNode c |
      a₀ ≤ hyperScore c K₀ r θ S ω v ∧ hyperScore c K₀ r θ S ω v < a₀ + δ} =
      {v : HyperNode c | ω ∈ hyperVertEvent c K₀ r θ S (fun x => a₀ ≤ x ∧ x < a₀ + δ) v} := rfl
  rw [hset]
  linarith [hW, hWm]

private theorem measurable_hyperScore (c : Circuit σ n 1) (K₀ r : ℕ) (θ : ℝ) (S : ℕ)
    (v : HyperNode c) : Measurable fun ω : HyperNode c → ℝ => hyperScore c K₀ r θ S ω v := by
  unfold hyperScore
  fun_prop

private theorem measurableSet_hyperCrossEvent (c : Circuit σ n 1) (K₀ r : ℕ) (θ : ℝ) (S : ℕ)
    (t : ℝ) (e : PrunedEdge c K₀) : MeasurableSet (hyperCrossEvent c K₀ r θ S t e) := by
  have heq : hyperCrossEvent c K₀ r θ S t e =
      (⋃ v ∈ hyperEdge c e.1, {ω | hyperScore c K₀ r θ S ω v < t}) ∩
      (⋃ v ∈ hyperEdge c e.1, {ω | ¬ hyperScore c K₀ r θ S ω v < t}) := by
    ext ω
    simp only [hyperCrossEvent, HyperedgeStraddles, mem_ofPred_eq, mem_inter_iff, mem_iUnion,
      exists_prop]
  rw [heq]
  exact ((hyperEdge c e.1).measurableSet_biUnion fun v _ =>
    measurableSet_lt (measurable_hyperScore c K₀ r θ S v) measurable_const).inter
    ((hyperEdge c e.1).measurableSet_biUnion fun v _ =>
      (measurableSet_lt (measurable_hyperScore c K₀ r θ S v) measurable_const).compl)

private theorem dependsOn_hyperCrossEvent (c : Circuit σ n 1) (K₀ r : ℕ) (θ : ℝ) (S : ℕ) (t : ℝ)
    (e : PrunedEdge c K₀) :
    DependsOn (· ∈ hyperCrossEvent c K₀ r θ S t e)
      (bipSupportBall c K₀ (.inr e) (2 * S + 1)) := by
  intro ω ω' hω
  have hsc (v : HyperNode c) (hv : v ∈ hyperEdge c e.1) :
      hyperScore c K₀ r θ S ω v = hyperScore c K₀ r θ S ω' v := by
    refine hyperScore_congr fun z (hz : (bipSimpleGraph c K₀).edist (.inl v) (.inl z) ≤ 2 * S) =>
      hω z ?_
    have hadj : (bipSimpleGraph c K₀).Adj (.inr e) (.inl v) := hv
    calc (bipSimpleGraph c K₀).edist (.inr e) (.inl z)
        ≤ (bipSimpleGraph c K₀).edist (.inr e) (.inl v) +
          (bipSimpleGraph c K₀).edist (.inl v) (.inl z) := SimpleGraph.edist_triangle
      _ = 1 + (bipSimpleGraph c K₀).edist (.inl v) (.inl z) := by
          rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj]
      _ ≤ 1 + (2 * S : ℕ∞) := add_le_add_right hz 1
      _ = ((2 * S + 1 : ℕ) : ℕ∞) := by push_cast; ring
  simp only [hyperCrossEvent, mem_ofPred_eq, HyperedgeStraddles]
  exact propext ⟨fun ⟨⟨u, hu, h1⟩, ⟨v, hv, h2⟩⟩ =>
    ⟨⟨u, hu, by rwa [← hsc u hu]⟩, ⟨v, hv, by rwa [← hsc v hv]⟩⟩,
    fun ⟨⟨u, hu, h1⟩, ⟨v, hv, h2⟩⟩ =>
    ⟨⟨u, hu, by rwa [hsc u hu]⟩, ⟨v, hv, by rwa [hsc v hv]⟩⟩⟩

private theorem dependsOn_hyperVertEvent (c : Circuit σ n 1) (K₀ r : ℕ) (θ : ℝ) (S : ℕ)
    (f : ℝ → Prop) (v : HyperNode c) :
    DependsOn (· ∈ hyperVertEvent c K₀ r θ S f v)
      (bipSupportBall c K₀ (.inl v) (2 * S + 1)) := by
  intro ω ω' hω
  simp only [hyperVertEvent, mem_ofPred_eq]
  rw [hyperScore_congr fun z (hz : _ ≤ (2 * S : ℕ∞)) =>
    hω z (hz.trans (by exact_mod_cast Nat.le_succ (2 * S)))]

/-- Concentration of pruned hyperedge straddling counts, grid windows, and tails on `HyperNode c`.
-/
private theorem exists_concentrated_hyperSample {c : Circuit σ n 1} {r K₀ D_ov : ℕ}
    (hfan : c.FanInAtMost r) (θ : ℝ) (S : ℕ)
    (hD_ov : (max (r + 1) K₀ + 1) ^ (2 * (2 * S + 1)) ≤ D_ov) (T δ : ℝ) {ε c_dev : ℝ}
    (hε : 0 < ε) (hc_eq : c_dev = ε * Nat.card (HyperNode c)) (M : ℕ)
    (hlarge : ((M : ℝ) * (((r + 1 : ℕ) : ℝ) + 1) + 2) * (D_ov : ℝ) / ε ^ 2 <
      Nat.card (HyperNode c)) :
    ∃ ω : HyperNode c → ℝ,
      (∀ i < M,
        ω ∉ Gaussian.deviation (hyperCrossEvent c K₀ r θ S (-T + i * δ)) c_dev ∧
        ω ∉ Gaussian.deviation
          (hyperVertEvent c K₀ r θ S fun x => -T + i * δ ≤ x ∧ x < -T + i * δ + δ) c_dev) ∧
      ω ∉ Gaussian.deviation (hyperVertEvent c K₀ r θ S (· < -T)) c_dev ∧
      ω ∉ Gaussian.deviation (hyperVertEvent c K₀ r θ S (T ≤ ·)) c_dev := by
  set P := Measure.pi fun _ : HyperNode c => gaussianReal 0 1
  set h : ℝ := (Nat.card (HyperNode c) : ℝ) with hh
  set dr : ℝ := ((r + 1 : ℕ) : ℝ)
  have hh_pos : 0 < h := lt_of_le_of_lt (by positivity) hlarge
  have hc_pos : 0 < c_dev := hc_eq ▸ mul_pos hε hh_pos
  have hcardV : (Fintype.card (HyperNode c) : ℝ) = h := by
    rw [hh, Nat.card_eq_fintype_card]
  have hcard_pruned : (Fintype.card (PrunedEdge c K₀) : ℝ) ≤ dr * h := by
    have hle : Fintype.card (PrunedEdge c K₀) ≤ (r + 1) * Nat.card (HyperNode c) :=
      (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans
        (card_liveSignal_le hfan)
    have hR : (Fintype.card (PrunedEdge c K₀) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) * Nat.card (HyperNode c) :=
      by exact_mod_cast hle
    exact hR
  have crossDev (t : ℝ) : P.real (Gaussian.deviation (hyperCrossEvent c K₀ r θ S t) c_dev) ≤
      (dr * h) * (D_ov : ℝ) / c_dev ^ 2 := by
    have hd := Gaussian.measureReal_deviation_le (measurableSet_hyperCrossEvent c K₀ r θ S t)
      (fun e => bipSupportBall c K₀ (.inr e) (2 * S + 1))
      (dependsOn_hyperCrossEvent c K₀ r θ S t)
      (fun e => (card_overlap_bipSupportBall_le hfan Sum.inr_injective (2 * S + 1) e).trans hD_ov)
      hc_pos
    exact hd.trans (by gcongr)
  have vertDev {f : ℝ → Prop} (hf : MeasurableSet {x | f x}) :
      P.real (Gaussian.deviation (hyperVertEvent c K₀ r θ S f) c_dev) ≤
        h * (D_ov : ℝ) / c_dev ^ 2 := by
    have hd := Gaussian.measureReal_deviation_le
      (fun v => measurable_hyperScore c K₀ r θ S v hf)
      (fun v => bipSupportBall c K₀ (.inl v) (2 * S + 1))
      (dependsOn_hyperVertEvent c K₀ r θ S f)
      (fun v => (card_overlap_bipSupportBall_le hfan Sum.inl_injective (2 * S + 1) v).trans hD_ov)
      hc_pos
    rwa [hcardV] at hd
  have hsmall : M * ((dr * h) * (D_ov : ℝ) / c_dev ^ 2 + h * (D_ov : ℝ) / c_dev ^ 2) +
      h * (D_ov : ℝ) / c_dev ^ 2 + h * (D_ov : ℝ) / c_dev ^ 2 < 1 := by
    have hcalc : M * ((dr * h) * (D_ov : ℝ) / c_dev ^ 2 + h * (D_ov : ℝ) / c_dev ^ 2) +
        h * (D_ov : ℝ) / c_dev ^ 2 + h * (D_ov : ℝ) / c_dev ^ 2 =
        ((M : ℝ) * (dr + 1) + 2) * (D_ov : ℝ) / ε ^ 2 / h := by
      rw [hc_eq]
      field_simp
      ring
    rw [hcalc, div_lt_one hh_pos]
    exact hlarge
  exact Gaussian.exists_sample_of_grid_bounds
    (fun i _ => crossDev (-T + i * δ))
    (fun i _ => vertDev ((measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)))
    (vertDev (measurableSet_lt measurable_id measurable_const))
    (vertDev (measurableSet_le measurable_const measurable_id)) hsmall

private theorem exists_hyperGrid_parameters (r : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    let dr : ℝ := ((r + 1 : ℕ) : ℝ)
    ∃ (η₀ T ε : ℝ) (M : ℕ), 0 < η₀ ∧ 0 < T ∧ 0 < ε ∧ 0 < M ∧
      η₀ * dr + dr / T ^ 2 + dr * (2 * T / M) / √(2 * π) + (dr + 1) * ε ≤ ξ := by
  intro dr
  have hdr_pos : 0 < dr := by positivity
  set η₀ := ξ / (4 * dr) with hη₀_def
  set T := 1 + 4 * dr / ξ with hT_def
  set ε := ξ / (4 * (dr + 1)) with hε_def
  set M : ℕ := ⌈8 * dr * T / ξ⌉₊ + 1 with hM_def
  have hT : 0 < T := by positivity
  have hM : 0 < M := Nat.succ_pos _
  have hMR : 8 * dr * T / ξ ≤ (M : ℝ) := by
    rw [hM_def]
    push_cast
    linarith [Nat.le_ceil (8 * dr * T / ξ)]
  have htail_err : dr / T ^ 2 ≤ ξ / 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos hT)]
    have hsq : 4 * dr / ξ ≤ T ^ 2 := by
      rw [hT_def]
      nlinarith [sq_nonneg (4 * dr / ξ)]
    have H := mul_le_mul_of_nonneg_left hsq hξ.le
    rw [mul_div_cancel₀ _ hξ.ne'] at H
    linarith [H]
  have hgrid_err : dr * (2 * T / M) / √(2 * π) ≤ ξ / 4 := by
    have hsqrt : 1 ≤ √(2 * π) :=
      (le_sqrt zero_le_one (by positivity)).mpr (by linarith [two_le_pi])
    have hfrac : dr * (2 * T / M) ≤ ξ / 4 := by
      rw [← mul_div_assoc, div_le_iff₀ (Nat.cast_pos.mpr hM)]
      have H := (div_le_iff₀ hξ).mp hMR
      linarith [H]
    exact (div_le_self (by positivity) hsqrt).trans hfrac
  refine ⟨η₀, T, ε, M, by positivity, hT, by positivity, hM, ?_⟩
  have h1 : η₀ * dr = ξ / 4 := by rw [hη₀_def]; field_simp
  have h2 : (dr + 1) * ε = ξ / 4 := by rw [hε_def]; field_simp
  linarith [h1, h2, htail_err, hgrid_err]

/-- **Unconditional dual-certificate hypergraph layout theorem.** Given a `HyperDualCert r K₀ a b`
and any slack `ξ > 0`, there is a constant `C : ℝ` (depending only on `r, K₀, a, b, ξ`) such that
every single-output circuit `c : Circuit σ n 1` of fan-in at most `r` admits a vertex layout
`lay : Layout (HyperNode c)` with
`hyperWidth c lay ≤ ((r + 1) a + b) |LiveGate c| + max b (-a) |LiveInput c| + ξ |HyperNode c| + C`.
-/
theorem exists_layout_hyperWidth_le {r K₀ : ℕ} {a b : ℚ} (hcert : HyperDualCert r K₀ a b)
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ C : ℝ, ∀ {σ : Signature} {n : ℕ} (c : Circuit σ n 1), c.FanInAtMost r →
      ∃ lay : Layout (HyperNode c), (hyperWidth c lay : ℝ) ≤
        (((r + 1 : ℕ) : ℝ) * a + b) * Fintype.card (LiveGate c) +
          max (b : ℝ) (-a) * Fintype.card (LiveInput c) +
          ξ * Nat.card (HyperNode c) + C := by
  let dr : ℝ := ((r + 1 : ℕ) : ℝ)
  have hdr_pos : 0 < dr := by positivity
  obtain ⟨η₀, T, ε, M, hη₀, hT, hε, hM, herr_sum⟩ := exists_hyperGrid_parameters r hξ
  obtain ⟨θ, hθ_mem, S, hS1, hprob_unif⟩ := exists_uniform_theta_radius hcert hη₀
  obtain ⟨D_ov, hD_ov⟩ : ∃ D_ov : ℕ, (max (r + 1) K₀ + 1) ^ (2 * (2 * S + 1)) ≤ D_ov :=
    ⟨_, le_rfl⟩
  obtain ⟨N₀, hN₀_ge⟩ : ∃ N₀ : ℕ, ((M : ℝ) * (dr + 1) + 2) * (D_ov : ℝ) / ε ^ 2 ≤ N₀ :=
    ⟨⌈((M : ℝ) * (dr + 1) + 2) * (D_ov : ℝ) / ε ^ 2⌉₊, Nat.le_ceil _⟩
  obtain ⟨C, ha_le_C, hC_small⟩ :
      ∃ C : ℝ, (a : ℝ) ≤ C ∧ dr * (N₀ : ℝ) ≤ C - |max (b : ℝ) (-a)| * (dr * (N₀ : ℝ)) := by
    refine ⟨|(a : ℝ)| + (dr + |max (b : ℝ) (-a)| * dr) * (N₀ : ℝ) + 1, ?_, ?_⟩
    · have hnn : 0 ≤ (dr + |max (b : ℝ) (-a)| * dr) * (N₀ : ℝ) := by positivity
      linarith [le_abs_self (a : ℝ), hnn]
    · have h0 : 0 ≤ |(a : ℝ)| := abs_nonneg _
      linarith [h0]
  refine ⟨C, fun {σ n} c hfan => ?_⟩
  by_cases hbig : N₀ < Nat.card (HyperNode c)
  · have hN₀_lt : (N₀ : ℝ) < Nat.card (HyperNode c) := Nat.cast_lt.mpr hbig
    have hlarge : ((M : ℝ) * (dr + 1) + 2) * (D_ov : ℝ) / ε ^ 2 < Nat.card (HyperNode c) :=
      hN₀_ge.trans_lt hN₀_lt
    set P := Measure.pi fun _ : HyperNode c => gaussianReal 0 1
    set h : ℝ := (Nat.card (HyperNode c) : ℝ) with hh
    set δ : ℝ := 2 * T / M
    set c_dev : ℝ := ε * h with hc_dev
    obtain ⟨ω, hmid, hlow, hhigh⟩ :=
      exists_concentrated_hyperSample hfan θ S hD_ov T δ hε hc_dev M hlarge
    have hh_pos : 0 < h := lt_of_le_of_lt (by positivity) hlarge
    have hδ_pos : 0 < δ := by positivity
    have hcardV_eq : (Fintype.card (HyperNode c) : ℝ) = h := by
      rw [hh, Nat.card_eq_fintype_card]
    set B_main := (dr * a + b) * Fintype.card (LiveGate c) +
      max (b : ℝ) (-a) * Fintype.card (LiveInput c) + a
    have hB_main_nn : 0 ≤ B_main :=
      (dualSupply_nonneg_and_sum_le hcert hfan hη₀.le
        (fun e => P.real (hyperCrossEvent c K₀ r θ S 0 e))
        (fun e => hprob_unif c hfan e 0)).1
    set B := B_main + h * (η₀ * dr + dr / T ^ 2 + dr * δ / √(2 * π) + (dr + 1) * ε) with hB_def
    have hunit (v : HyperNode c) : ‖hyperUnitRow c K₀ r θ S v‖ = 1 :=
      norm_hyperUnitRow c K₀ r θ S v
    have tail (f : ℝ → Prop) (hf : ∀ x, f x → T ≤ |x|)
        (hdev : ω ∉ Gaussian.deviation (hyperVertEvent c K₀ r θ S f) c_dev) :
        dr * ({v | f (hyperScore c K₀ r θ S ω v)}.ncard : ℝ) ≤ B := by
      have hcount := Gaussian.ncard_lt_of_notMem_deviation hdev
      have hmean : ∑ v, P.real (hyperVertEvent c K₀ r θ S f v) ≤ h * (1 / T ^ 2) := by
        refine (Finset.sum_le_sum fun v _ =>
          (measureReal_mono (μ := P) fun ω' hω' => hf _ hω').trans
            (Gaussian.measureReal_le_abs_le (hunit v) hT)).trans_eq ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardV_eq]
      have hset : {v | f (hyperScore c K₀ r θ S ω v)} =
          {v | ω ∈ hyperVertEvent c K₀ r θ S f v} := rfl
      have hbound : ({v | f (hyperScore c K₀ r θ S ω v)}.ncard : ℝ) ≤ h * (1 / T ^ 2) + c_dev := by
        rw [hset]
        linarith [hcount, hmean]
      have hmult := mul_le_mul_of_nonneg_left hbound hdr_pos.le
      have hextra : 0 ≤ B_main + h * (η₀ * dr + dr * δ / √(2 * π) + ε) := by positivity
      have hid : B = dr * (h * (1 / T ^ 2) + c_dev) +
          (B_main + h * (η₀ * dr + dr * δ / √(2 * π) + ε)) := by
        rw [hB_def, hc_dev]
        ring
      rw [hid]
      linarith [hmult, hextra]
    have htop : -T + M * δ = T := by
      have hM_ne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
      dsimp only [δ]
      field_simp [hM_ne]
      ring
    obtain ⟨lay, hlay⟩ := exists_hyperWidth_le_of_vertexScore hfan (hyperScore c K₀ r θ S ω)
      hδ_pos M (a₀ := -T) (B := B)
      (tail (· < -T) (fun x hx => by rw [abs_of_neg (by linarith)]; linarith) hlow)
      (by
        rw [htop]
        exact tail (T ≤ ·) (fun x hx => hx.trans (le_abs_self x)) hhigh)
      (fun i hi => by
        have hthr : -T + ((i : ℝ) + 1) * δ = -T + i * δ + δ := by ring
        rw [hthr]
        have hC_le : ((hyperCut c {v | hyperScore c K₀ r θ S ω v < -T + i * δ}).card : ℝ) ≤
            B_main + h * (η₀ * dr) + c_dev :=
          card_hyperCut_threshold_le hcert hfan hη₀.le θ S ω (-T + i * δ)
            (fun e => hprob_unif c hfan e (-T + i * δ)) (hmid i hi).1
        have hW_le := ncard_hyperWindow_le hδ_pos.le (hmid i hi).2
        have hmult := mul_le_mul_of_nonneg_left hW_le hdr_pos.le
        have htail_nn : 0 ≤ h * (dr / T ^ 2) := by positivity
        have hid : B = (B_main + h * (η₀ * dr) + c_dev) + dr * (h * (δ / √(2 * π)) + c_dev) +
            h * (dr / T ^ 2) := by
          rw [hB_def, hc_dev]
          ring
        rw [hid]
        linarith [hC_le, hmult, htail_nn])
    refine ⟨lay, hlay.trans ?_⟩
    have hh_err := mul_le_mul_of_nonneg_left herr_sum hh_pos.le
    rw [hB_def]
    dsimp only [B_main, δ] at hh_err ⊢
    linarith [hh_err, ha_le_C]
  · -- Small circuit (`Nat.card (HyperNode c) ≤ N₀`): any layout works deterministically.
    have hle_N₀ : (Nat.card (HyperNode c) : ℝ) ≤ (N₀ : ℝ) := Nat.cast_le.mpr (not_lt.mp hbig)
    let lay : Layout (HyperNode c) := Finite.equivFin (HyperNode c)
    have hw_le : (hyperWidth c lay : ℝ) ≤ dr * (N₀ : ℝ) := by
      have hsup : hyperWidth c lay ≤ (r + 1) * Nat.card (HyperNode c) := by
        unfold hyperWidth
        refine Finset.sup_le fun t _ => ?_
        exact (Finset.card_le_univ _).trans (card_liveSignal_le hfan)
      have hsupR : (hyperWidth c lay : ℝ) ≤ ((r + 1 : ℕ) : ℝ) * Nat.card (HyperNode c) := by
        exact_mod_cast hsup
      exact hsupR.trans (mul_le_mul_of_nonneg_left hle_N₀ hdr_pos.le)
    have hinp_le : (Fintype.card (LiveInput c) : ℝ) ≤ dr * (N₀ : ℝ) := by
      have hinp_nat : Fintype.card (LiveInput c) ≤ (r + 1) * Nat.card (HyperNode c) := by
        have hs := card_liveSignal_le hfan
        rw [Fintype.card_sum] at hs
        omega
      have hinpR : (Fintype.card (LiveInput c) : ℝ) ≤
          ((r + 1 : ℕ) : ℝ) * Nat.card (HyperNode c) := by
        exact_mod_cast hinp_nat
      exact hinpR.trans (mul_le_mul_of_nonneg_left hle_N₀ hdr_pos.le)
    have hgate_nn : 0 ≤ (dr * a + b) * Fintype.card (LiveGate c) := by
      have hd_pos : (0 : ℝ) < dr * a + b := by
        have hq := Rat.cast_pos (K := ℝ).mpr hcert.hdenom
        push_cast at hq
        dsimp only [dr]
        push_cast
        linarith [hq]
      positivity
    have hinp_abs : -(|max (b : ℝ) (-a)| * (dr * (N₀ : ℝ))) ≤
        max (b : ℝ) (-a) * Fintype.card (LiveInput c) := by
      have h1 := neg_abs_le (max (b : ℝ) (-a))
      have h2 := mul_le_mul_of_nonneg_right h1
        (Nat.cast_nonneg (α := ℝ) (Fintype.card (LiveInput c)))
      have h3 := mul_le_mul_of_nonneg_left hinp_le (abs_nonneg (max (b : ℝ) (-a)))
      linarith [h2, h3]
    have hξh_nn : 0 ≤ ξ * Nat.card (HyperNode c) := mul_nonneg hξ.le (Nat.cast_nonneg _)
    exact ⟨lay, by linarith [hw_le, hgate_nn, hinp_abs, hξh_nn, hC_small]⟩

end GridAndLayout

end Cslib.Circuits.Frontier.Hypergraph
