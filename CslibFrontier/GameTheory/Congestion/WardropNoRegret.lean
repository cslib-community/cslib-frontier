/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Congestion.BeckmannPotential
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Convergence of regret-minimizing flows to approximate Wardrop equilibria

In online routing ([BlumMansour2007AGT], Section 4.7, following Blum, Even-Dar and Ligett, 2006),
a population of nonatomic users routes traffic over `T` days, producing feasible daily flows
`f 0, …, f (T - 1)`. Following [BlumMansour2007AGT], Section 4.7, p. 97:

* A feasible flow `f` is **`ε`-Wardrop** (`IsApproxWardrop`, "`ε`-Nash" in [BlumMansour2007AGT],
  p. 97) if the excess total travel cost of `f` over rerouting along any feasible flow `g` (at the
  latencies induced by `f`) is at most `ε`:
  `G.cost f ≤ ∑ p, g p * G.pathLatency f p + ε`.
  At `ε = 0` this coincides with `G.IsWardrop f` (`isApproxWardrop_zero_iff`), and in the
  single-commodity unit-rate model (`K = Unit`, `rate () = 1`) it is equivalent to
  `∀ p, G.cost f ≤ G.pathLatency f p + ε`, i.e., `C(f) ≤ ε + min_p pathLatency f p` verbatim
  (`isApproxWardrop_unit_iff`).
* A sequence of daily flows `f 0, …, f (T - 1)` has **average external regret at most `ε`**
  (`HasAvgRegretLe`) if for every fixed feasible flow `g`,
  `(∑ t < T, G.cost (f t)) / T ≤ (∑ t < T, ∑ p, g p * G.pathLatency (f t) p) / T + ε`,
  which in the single-commodity unit-rate model equals the source's `R(T) ≤ ε * T` against every
  fixed path (`hasAvgRegretLe_unit_iff`).

This module formalizes [BlumMansour2007AGT], Theorem 4.18 (p. 97), together with original
nonlinear time-average extensions inspired by the bounded-slope discussion in
[BlumMansour2007AGT], Section 4.7, pp. 97–98 (where the source's informal per-day
`(1 - ε)`-fraction convergence claim from Blum, Even-Dar and Ligett, 2006 remains open under
#7789):

* **Theorem 4.18 for affine latencies**
  (`HasAffineLatencies.isApproxWardrop_timeAverageFlow`,
  `HasAffineLatencies.isApproxWardrop_timeAverageFlow_unit`, [BlumMansour2007AGT], Theorem 4.18,
  p. 97): when every edge latency is nonnegative affine, average external regret `≤ ε` implies
  that `timeAverageFlow f T` is feasible and `ε`-Wardrop with *no* degradation in `ε`.
* **Cost Jensen bound** (`cost_timeAverageFlow_le`): whenever `x ↦ x * latency e x` is convex on
  `[0, ∞)`, `G.cost (timeAverageFlow f T) ≤ (∑ t < T, G.cost (f t)) / T`.
* **Original concave-latency generalization** (`isApproxWardrop_timeAverageFlow_of_concaveOn`,
  original): extends Theorem 4.18's Jensen proof to any concave latencies on `[0, ∞)` with convex
  edge cost `x ↦ x * latency e x`.
* **Original quadratic counterexample to literal `ε`-preservation**
  (`exists_not_isApproxWardrop_timeAverageFlow_sq`, original):
  for the convex quadratic latency `x ^ 2` on `pigouNetwork (· ^ 2) 1`, two daily flows have
  average regret `44 / 64` while their time average has Wardrop gap `45 / 64 > 44 / 64`, showing
  that literal `ε`-preservation requires concavity/linearity of `latency e` on the benchmark side.
* **Original bounded-slope time-average convergence**
  (`isApproxWardrop_timeAverageFlow_of_lipschitz`,
  `isApproxWardrop_timeAverageFlow_of_convexOn_of_lipschitz`,
  `isWardrop_timeAverageFlow_of_hasAvgRegretLe_zero`, original formulations inspired by
  [BlumMansour2007AGT], Section 4.7, pp. 97–98): for *any* nondecreasing `L`-Lipschitz latencies
  on `[0, ∞)`, bounding edge-latency fluctuations via the Chebyshev covariance identity
  `(c_e(x_t) - c_e(x̂))^2 ≤ L * (x_t - x̂) * (c_e(x_t) - c_e(x̂))` proves that
  `timeAverageFlow f T` is `(ε + 2 * totalFlow * √(|E| * L * ε))`-Wardrop (improving to
  `ε + totalFlow * √(|E| * L * ε)` when `latency e` is also convex on `[0, ∞)`, and giving an
  exact Wardrop equilibrium when `ε = 0`).

## Main definitions

* `Cslib.GameTheory.NonatomicCongestionGame.IsApproxWardrop`: `ε`-approximate Wardrop equilibrium.
* `Cslib.GameTheory.NonatomicCongestionGame.HasAvgRegretLe`: time-averaged external path regret at
  most `ε` over `T` steps.
* `Cslib.GameTheory.timeAverageFlow`: the time-averaged path flow `(∑ t < T, f t p) / T`.

## Main results

* `Cslib.GameTheory.NonatomicCongestionGame.isApproxWardrop_unit_iff` and
  `Cslib.GameTheory.NonatomicCongestionGame.hasAvgRegretLe_unit_iff`: single-commodity unit-rate
  equivalences matching `C(f) ≤ ε + min_p pathLatency f p` and `R(T) ≤ ε * T`.
* `Cslib.GameTheory.NonatomicCongestionGame.cost_timeAverageFlow_le`: Jensen bound on
  `cost (timeAverageFlow f T)`.
* `Cslib.GameTheory.NonatomicCongestionGame.HasAffineLatencies.isApproxWardrop_timeAverageFlow` and
  `Cslib.GameTheory.NonatomicCongestionGame.HasAffineLatencies.isApproxWardrop_timeAverageFlow_unit`
  ([BlumMansour2007AGT], Theorem 4.18, p. 97): exact `ε`-Wardrop convergence for nonnegative
  affine latencies.
* `Cslib.GameTheory.NonatomicCongestionGame.isApproxWardrop_timeAverageFlow_of_concaveOn`
  (original): exact `ε`-Wardrop convergence for concave latencies with convex edge cost.
* `Cslib.GameTheory.NonatomicCongestionGame.exists_not_isApproxWardrop_timeAverageFlow_sq`
  (original): quadratic counterexample showing literal `ε` fails without concavity/linearity of
  `latency e`.
* `Cslib.GameTheory.NonatomicCongestionGame.isApproxWardrop_timeAverageFlow_of_lipschitz` and
  `Cslib.GameTheory.NonatomicCongestionGame.isWardrop_timeAverageFlow_of_hasAvgRegretLe_zero`
  (plus `isApproxWardrop_timeAverageFlow_of_convexOn_of_lipschitz`; original, inspired by
  [BlumMansour2007AGT], Section 4.7, pp. 97–98): `O(ε + √ε)` time-average convergence for general
  nonlinear nondecreasing bounded-slope latencies.

## References

* [BlumMansour2007AGT]
* [Roughgarden2007Routing]
-/

public section

namespace Cslib.GameTheory

open Finset

/-- The **time-averaged path flow** `(1 / T) ∑ t < T, f t` over `T` steps
([BlumMansour2007AGT], Section 4.7, Theorem 4.18). -/
@[expose] noncomputable def timeAverageFlow {P : Type*} (f : ℕ → P → ℝ) (T : ℕ) (p : P) : ℝ :=
  (∑ t ∈ range T, f t p) / T

/-- If `c : ℝ → ℝ` is nondecreasing and convex on `[0, ∞)`, then `x ↦ x * c x` is convex on
`[0, ∞)`. -/
private theorem convexOn_mul_of_monotoneOn_convexOn {c : ℝ → ℝ} (hm : MonotoneOn c (Set.Ici 0))
    (hc : ConvexOn ℝ (Set.Ici 0) c) : ConvexOn ℝ (Set.Ici 0) (fun x => x * c x) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hcomb0 : 0 ≤ a * x + b * y := add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hstep1 : (a * x + b * y) * c (a * x + b * y) ≤
      (a * x + b * y) * (a * c x + b * c y) :=
    mul_le_mul_of_nonneg_left (hc.2 hx hy ha hb hab) hcomb0
  have hcheb : 0 ≤ (x - y) * (c x - c y) := by
    rcases le_total y x with hyx | hxy
    · exact mul_nonneg (sub_nonneg.2 hyx) (sub_nonneg.2 (hm hy hx hyx))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hxy) (sub_nonpos.2 (hm hx hy hxy))
  have hident : a * (x * c x) + b * (y * c y) - (a * x + b * y) * (a * c x + b * c y) =
      a * b * ((x - y) * (c x - c y)) := by
    calc a * (x * c x) + b * (y * c y) - (a * x + b * y) * (a * c x + b * c y)
        = (a + b) * (a * (x * c x) + b * (y * c y)) - (a * x + b * y) * (a * c x + b * c y) := by
            rw [hab, one_mul]
      _ = a * b * ((x - y) * (c x - c y)) := by ring
  nlinarith [mul_nonneg ha hb]

namespace NonatomicCongestionGame

section Definitions

variable {K P E : Type*} [Fintype P] [DecidableEq E] (G : NonatomicCongestionGame K P E)

/-- An **`ε`-approximate Wardrop equilibrium** ("`ε`-Nash flow" in [BlumMansour2007AGT],
Section 4.7, p. 97): a feasible flow `f` whose cost exceeds the latency under `f` of any feasible
rerouting `g` by at most `ε`. -/
@[expose] def IsApproxWardrop [DecidableEq K] (ε : ℝ) (f : P → ℝ) : Prop :=
  G.IsFeasible f ∧ ∀ g, G.IsFeasible g → G.cost f ≤ ∑ p, g p * G.pathLatency f p + ε

/-- A sequence of flows `f 0, …, f (T - 1)` has **average external regret at most `ε`**
([BlumMansour2007AGT], Section 4.7, p. 97) if each `f t` (`t < T`) is feasible and the average
flow cost exceeds that of any fixed feasible benchmark flow `g` by at most `ε`. -/
@[expose] def HasAvgRegretLe [DecidableEq K] (f : ℕ → P → ℝ) (T : ℕ) (ε : ℝ) : Prop :=
  (∀ t < T, G.IsFeasible (f t)) ∧ ∀ g, G.IsFeasible g →
    (∑ t ∈ range T, G.cost (f t)) / T ≤
      (∑ t ∈ range T, ∑ p, g p * G.pathLatency (f t) p) / T + ε

/-- At `ε = 0`, `IsApproxWardrop 0 f` is equivalent to `IsWardrop f`. -/
theorem isApproxWardrop_zero_iff [DecidableEq K] {f : P → ℝ} :
    G.IsApproxWardrop 0 f ↔ G.IsWardrop f := by
  simp only [IsApproxWardrop, add_zero, isWardrop_iff_forall_cost_le_sum_mul_pathLatency]

/-- Monotonicity of `IsApproxWardrop` in the slack `ε`. -/
theorem IsApproxWardrop.mono [DecidableEq K] {G : NonatomicCongestionGame K P E}
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) {f : P → ℝ} (hf : G.IsApproxWardrop ε₁ f) :
    G.IsApproxWardrop ε₂ f :=
  ⟨hf.1, fun g hg => (hf.2 g hg).trans (by linarith)⟩

omit [DecidableEq E] in
/-- For a single-commodity unit-rate network (`rate () = 1`), placing all unit flow on path `p` is
feasible, and any feasible flow yields a nonempty path set. -/
private theorem isFeasible_unitSinglePath {G : NonatomicCongestionGame Unit P E}
    (hr : G.rate () = 1) [DecidableEq P] (p : P) :
    G.IsFeasible (fun q => if q = p then 1 else 0) := by
  refine ⟨fun q => by dsimp only; split_ifs <;> norm_num, fun x => ?_⟩
  simp only [filter_true, sum_ite_eq', mem_univ, ↓reduceIte, Subsingleton.elim x (), hr]

omit [DecidableEq E] in
private theorem min_le_sum_mul_of_unitFeasible {G : NonatomicCongestionGame Unit P E}
    (hr : G.rate () = 1) {g : P → ℝ} (hg : G.IsFeasible g) (w : P → ℝ) :
    ∃ p₀ : P, w p₀ ≤ ∑ p, g p * w p := by
  have hne : (univ : Finset P).Nonempty := by
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    have hsum := hg.2 ()
    rw [hempty, filter_empty, sum_empty, hr] at hsum
    norm_num at hsum
  obtain ⟨p₀, _, hp₀⟩ := exists_min_image univ w hne
  have hsum_g : ∑ p, g p = 1 := by
    simpa only [eq_iff_true_of_subsingleton, filter_true, hr] using hg.2 ()
  refine ⟨p₀, ?_⟩
  calc w p₀ = (∑ p, g p) * w p₀ := by rw [hsum_g, one_mul]
    _ = ∑ p, g p * w p₀ := sum_mul _ _ _
    _ ≤ ∑ p, g p * w p := sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hp₀ p hp) (hg.1 p)

/-- In a single-commodity unit-rate network (`K = Unit`, `G.rate () = 1`), `G.IsApproxWardrop ε f`
is equivalent to `G.IsFeasible f ∧ ∀ p, G.cost f ≤ G.pathLatency f p + ε`, matching
`C(f) ≤ ε + min_p pathLatency f p` in [BlumMansour2007AGT], Section 4.7, p. 97. -/
theorem isApproxWardrop_unit_iff {G : NonatomicCongestionGame Unit P E}
    (hr : G.rate () = 1) {ε : ℝ} {f : P → ℝ} :
    G.IsApproxWardrop ε f ↔ G.IsFeasible f ∧ ∀ p, G.cost f ≤ G.pathLatency f p + ε := by
  refine ⟨fun ⟨hf, hvi⟩ => ⟨hf, fun p => ?_⟩, fun ⟨hf, hmin⟩ => ⟨hf, fun g hg => ?_⟩⟩
  · classical
    have h := hvi (fun q => if q = p then 1 else 0) (isFeasible_unitSinglePath hr p)
    simpa only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte] using h
  · obtain ⟨p₀, hge⟩ := min_le_sum_mul_of_unitFeasible hr hg (G.pathLatency f)
    linarith [hmin p₀]

/-- In a single-commodity unit-rate network (`K = Unit`, `G.rate () = 1`), `G.HasAvgRegretLe f T ε`
is equivalent to feasibility of each `f t` together with
`∀ p, (∑ t < T, G.cost (f t)) / T ≤ (∑ t < T, G.pathLatency (f t) p) / T + ε`, i.e.,
`R(T) ≤ ε * T` in [BlumMansour2007AGT], Section 4.7, p. 97. -/
theorem hasAvgRegretLe_unit_iff {G : NonatomicCongestionGame Unit P E}
    (hr : G.rate () = 1) {f : ℕ → P → ℝ} {T : ℕ} {ε : ℝ} :
    G.HasAvgRegretLe f T ε ↔
      (∀ t < T, G.IsFeasible (f t)) ∧
        ∀ p, (∑ t ∈ range T, G.cost (f t)) / T ≤
          (∑ t ∈ range T, G.pathLatency (f t) p) / T + ε := by
  refine ⟨fun ⟨hf, hreg⟩ => ⟨hf, fun p => ?_⟩, fun ⟨hf, hmin⟩ => ⟨hf, fun g hg => ?_⟩⟩
  · classical
    have h := hreg (fun q => if q = p then 1 else 0) (isFeasible_unitSinglePath hr p)
    simpa only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte] using h
  · have hswap : (∑ t ∈ range T, ∑ p, g p * G.pathLatency (f t) p) / T =
        ∑ p, g p * ((∑ t ∈ range T, G.pathLatency (f t) p) / T) := by
      rw [sum_comm, sum_div]
      refine sum_congr rfl fun p _ => by rw [← mul_sum, mul_div_assoc]
    rw [hswap]
    obtain ⟨p₀, hge⟩ := min_le_sum_mul_of_unitFeasible hr hg
      (fun p => (∑ t ∈ range T, G.pathLatency (f t) p) / T)
    linarith [hmin p₀]

omit [DecidableEq E] in
/-- The time average of feasible daily flows over `T > 0` days is feasible. -/
theorem isFeasible_timeAverageFlow [DecidableEq K] {f : ℕ → P → ℝ} {T : ℕ} (hT : 0 < T)
    (hf : ∀ t < T, G.IsFeasible (f t)) :
    G.IsFeasible (timeAverageFlow f T) := by
  have hT_pos : (0 : ℝ) < T := by exact_mod_cast hT
  refine ⟨fun p => div_nonneg (sum_nonneg fun t ht => (hf t (mem_range.1 ht)).1 p) hT_pos.le,
    fun k => ?_⟩
  simp only [timeAverageFlow, ← sum_div]
  rw [sum_comm]
  have hsum : ∑ t ∈ range T, ∑ p with G.commodity p = k, f t p = T * G.rate k := by
    have hcongr : ∀ t ∈ range T, ∑ p with G.commodity p = k, f t p = G.rate k :=
      fun t ht => (hf t (mem_range.1 ht)).2 k
    rw [sum_congr rfl hcongr, sum_const, card_range, nsmul_eq_mul]
  rw [hsum, mul_div_cancel_left₀ _ hT_pos.ne']

/-- `edgeFlow` commutes with `timeAverageFlow`. -/
theorem edgeFlow_timeAverageFlow (f : ℕ → P → ℝ) (T : ℕ) (e : E) :
    G.edgeFlow (timeAverageFlow f T) e = (∑ t ∈ range T, G.edgeFlow (f t) e) / T := by
  simp only [edgeFlow, timeAverageFlow, ← sum_div]
  rw [sum_comm]

end Definitions

/-! ### Cost Jensen bound and Theorem 4.18 -/

section JensenAndAffine

variable {K P E : Type*} [Fintype P] [DecidableEq E] {G : NonatomicCongestionGame K P E}

/-- Time-averaged total cost written edge by edge. -/
private theorem avgCost_eq_sum_edgeFlow [Fintype E] {G : NonatomicCongestionGame K P E}
    (f : ℕ → P → ℝ) (T : ℕ) :
    (∑ t ∈ range T, G.cost (f t)) / T =
      ∑ e, (∑ t ∈ range T, G.edgeFlow (f t) e * G.latency e (G.edgeFlow (f t) e)) / T := by
  have hc : ∀ t ∈ range T, G.cost (f t) =
      ∑ e, G.edgeFlow (f t) e * G.latency e (G.edgeFlow (f t) e) :=
    fun t _ => G.cost_eq_sum_edgeFlow (f t)
  rw [sum_congr rfl hc, sum_comm, sum_div]

/-- Time-averaged benchmark cost against `g` written edge by edge. -/
private theorem avgPathLatency_eq_sum_edgeFlow [Fintype E] {G : NonatomicCongestionGame K P E}
    (f : ℕ → P → ℝ) (g : P → ℝ) (T : ℕ) :
    (∑ t ∈ range T, ∑ p, g p * G.pathLatency (f t) p) / T =
      ∑ e, G.edgeFlow g e * ((∑ t ∈ range T, G.latency e (G.edgeFlow (f t) e)) / T) := by
  have hex : ∀ t ∈ range T, ∑ p, g p * G.pathLatency (f t) p =
      ∑ e, G.edgeFlow g e * G.latency e (G.edgeFlow (f t) e) :=
    fun t _ => G.sum_mul_sum_resources g _
  rw [sum_congr rfl hex, sum_comm, sum_div]
  exact sum_congr rfl fun e _ => by rw [← mul_sum, mul_div_assoc]

/-- Sum of uniform weights `(T : ℝ)⁻¹` over `range T` equals `1` when `0 < T`. -/
private theorem sum_range_inv_eq_one {T : ℕ} (hT : 0 < T) :
    ∑ _t ∈ range T, (T : ℝ)⁻¹ = 1 := by
  have hT_pos : (0 : ℝ) < T := by exact_mod_cast hT
  rw [sum_const, card_range, nsmul_eq_mul, mul_inv_cancel₀ hT_pos.ne']

/-- When `x ↦ x * latency e x` is convex on `[0, ∞)` for every resource `e` (in particular for
every nondecreasing convex latency), the cost of the time-averaged flow is at most the time average
of the daily flow costs. -/
theorem cost_timeAverageFlow_le [Finite E]
    (hconv : ∀ e, ConvexOn ℝ (Set.Ici 0) (fun x => x * G.latency e x))
    {f : ℕ → P → ℝ} {T : ℕ} (hT : 0 < T) (hf : ∀ t < T, ∀ p, 0 ≤ f t p) :
    G.cost (timeAverageFlow f T) ≤ (∑ t ∈ range T, G.cost (f t)) / T := by
  have := Fintype.ofFinite E
  have hT_nonneg : (0 : ℝ) ≤ (T : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg T)
  rw [G.cost_eq_sum_edgeFlow, avgCost_eq_sum_edgeFlow]
  refine sum_le_sum fun e _ => ?_
  have hj := (hconv e).map_sum_le (fun _ _ => hT_nonneg) (sum_range_inv_eq_one hT)
    (fun t ht => G.edgeFlow_nonneg (hf t (mem_range.1 ht)) e)
  simp only [smul_eq_mul, ← div_eq_inv_mul, ← sum_div] at hj
  rwa [G.edgeFlow_timeAverageFlow]

/-- **Original concave-latency generalization of [BlumMansour2007AGT], Theorem 4.18**: if
`latency e` is concave on `[0, ∞)` and `x ↦ x * latency e x` is convex on `[0, ∞)` (for instance,
`c(x) = a x + b` or `c(x) = x ^ α` with `0 ≤ α ≤ 1`), then any flow sequence with average external
regret at most `ε` over `T > 0` steps has time-average flow that is feasible and `ε`-Wardrop. -/
theorem isApproxWardrop_timeAverageFlow_of_concaveOn [DecidableEq K] [Finite E]
    (hconc : ∀ e, ConcaveOn ℝ (Set.Ici 0) (G.latency e))
    (hconv : ∀ e, ConvexOn ℝ (Set.Ici 0) (fun x => x * G.latency e x))
    {f : ℕ → P → ℝ} {T : ℕ} (hT : 0 < T) {ε : ℝ}
    (hreg : G.HasAvgRegretLe f T ε) :
    G.IsApproxWardrop ε (timeAverageFlow f T) := by
  have := Fintype.ofFinite E
  have hT_nonneg : (0 : ℝ) ≤ (T : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg T)
  refine ⟨G.isFeasible_timeAverageFlow hT hreg.1, fun g hg => ?_⟩
  have hcost_le := cost_timeAverageFlow_le hconv hT fun t ht => (hreg.1 t ht).1
  have hreg_g := hreg.2 g hg
  have hlat_le : (∑ t ∈ range T, ∑ p, g p * G.pathLatency (f t) p) / T ≤
      ∑ p, g p * G.pathLatency (timeAverageFlow f T) p := by
    have h2 : ∑ p, g p * G.pathLatency (timeAverageFlow f T) p =
        ∑ e, G.edgeFlow g e * G.latency e (G.edgeFlow (timeAverageFlow f T) e) :=
      G.sum_mul_sum_resources g _
    rw [avgPathLatency_eq_sum_edgeFlow, h2]
    refine sum_le_sum fun e _ => mul_le_mul_of_nonneg_left ?_ (G.edgeFlow_nonneg hg.1 e)
    have hj := (hconc e).le_map_sum (fun _ _ => hT_nonneg) (sum_range_inv_eq_one hT)
      (fun t ht => G.edgeFlow_nonneg (hreg.1 t (mem_range.1 ht)).1 e)
    simp only [smul_eq_mul, ← div_eq_inv_mul, ← sum_div] at hj
    rwa [G.edgeFlow_timeAverageFlow]
  linarith

/-- **Time-averaged no-regret routing with affine latencies is `ε`-Wardrop**
([BlumMansour2007AGT], Theorem 4.18, p. 97): if `G` has nonnegative affine latencies and
`f 0, …, f (T - 1)` has average external regret at most `ε`, then `timeAverageFlow f T` is feasible
and `ε`-Wardrop. -/
theorem HasAffineLatencies.isApproxWardrop_timeAverageFlow [DecidableEq K] [Finite E]
    (hG : G.HasAffineLatencies) {f : ℕ → P → ℝ} {T : ℕ} (hT : 0 < T) {ε : ℝ}
    (hreg : G.HasAvgRegretLe f T ε) :
    G.IsApproxWardrop ε (timeAverageFlow f T) := by
  obtain ⟨a, b, ha, -, hl⟩ := hG
  refine isApproxWardrop_timeAverageFlow_of_concaveOn
    (fun e => ⟨convex_Ici 0, fun x _ y _ u v _ _ huv => ?_⟩)
    (fun e => convexOn_mul_of_monotoneOn_convexOn
      (fun x _ y _ hxy => by rw [hl, hl]; nlinarith [ha e])
      ⟨convex_Ici 0, fun x _ y _ u v _ _ huv => ?_⟩)
    hT hreg
  · simp only [smul_eq_mul, hl]
    have hb : (u + v) * b e = b e := by rw [huv, one_mul]
    linarith
  · simp only [smul_eq_mul, hl]
    have hb : (u + v) * b e = b e := by rw [huv, one_mul]
    linarith

/-- Single-commodity unit-rate form of Theorem 4.18 ([BlumMansour2007AGT], Section 4.7, p. 97,
verbatim): if `G` has nonnegative affine latencies, `G.rate () = 1`, each `f t` (`t < T`) is
feasible, and `R(T) ≤ ε * T` against every path `p`, then `timeAverageFlow f T` satisfies
`G.cost (timeAverageFlow f T) ≤ G.pathLatency (timeAverageFlow f T) p + ε` for every path `p`. -/
theorem HasAffineLatencies.isApproxWardrop_timeAverageFlow_unit [Finite E]
    {G : NonatomicCongestionGame Unit P E} (hG : G.HasAffineLatencies) (hr : G.rate () = 1)
    {f : ℕ → P → ℝ} {T : ℕ} (hT : 0 < T) {ε : ℝ}
    (hf : ∀ t < T, G.IsFeasible (f t))
    (hR : ∀ p, ∑ t ∈ range T, G.cost (f t) - ∑ t ∈ range T, G.pathLatency (f t) p ≤ ε * T) :
    G.IsApproxWardrop ε (timeAverageFlow f T) := by
  have hT_pos : (0 : ℝ) < T := by exact_mod_cast hT
  refine hG.isApproxWardrop_timeAverageFlow hT ((hasAvgRegretLe_unit_iff hr).2 ⟨hf, fun p => ?_⟩)
  rw [div_le_iff₀ hT_pos, add_mul, div_mul_cancel₀ _ hT_pos.ne']
  linarith [hR p]

/-- **Original quadratic counterexample to literal `ε`-preservation without concavity/linearity**
(inspired by [BlumMansour2007AGT], Section 4.7, pp. 97–98): on `pigouNetwork (· ^ 2) 1`, the
two-day sequence `f 0 = ![0, 1]`, `f 1 = ![1 / 2, 1 / 2]` has average external regret `44 / 64`,
whereas `timeAverageFlow f 2 = ![1 / 4, 3 / 4]` has Wardrop gap `45 / 64 > 44 / 64` and is
therefore *not* `(44 / 64)`-Wardrop. -/
theorem exists_not_isApproxWardrop_timeAverageFlow_sq :
    ∃ (f : ℕ → Fin 2 → ℝ),
      (pigouNetwork (fun x : ℝ => x ^ 2) 1).HasAvgRegretLe f 2 (44 / 64) ∧
        ¬ (pigouNetwork (fun x : ℝ => x ^ 2) 1).IsApproxWardrop (44 / 64)
          (timeAverageFlow f 2) := by
  let G := pigouNetwork (fun x : ℝ => x ^ 2) 1
  let f : ℕ → Fin 2 → ℝ := fun t => if t = 0 then ![0, 1] else ![1 / 2, 1 / 2]
  refine ⟨f, ?_, ?_⟩
  · rw [hasAvgRegretLe_unit_iff rfl]
    refine ⟨fun t ht => ?_, fun p => ?_⟩
    · have ht2 : t = 0 ∨ t = 1 := by omega
      rcases ht2 with rfl | rfl
      · change G.IsFeasible ![0, 1]
        have h01 : (![0, (1 : ℝ) - 0] : Fin 2 → ℝ) = ![0, 1] := by
          ext i; fin_cases i <;> norm_num
        rw [← h01]
        exact pigouNetwork_isFeasible (fun x : ℝ => x ^ 2) le_rfl zero_le_one
      · change G.IsFeasible ![1 / 2, 1 / 2]
        have h12 : (![1 / 2, (1 : ℝ) - 1 / 2] : Fin 2 → ℝ) = ![1 / 2, 1 / 2] := by
          ext i; fin_cases i <;> norm_num
        rw [← h12]
        exact pigouNetwork_isFeasible (fun x : ℝ => x ^ 2) (by norm_num) (by norm_num)
    · simp only [sum_range_succ, sum_range_zero, zero_add, pigouNetwork_cost, pathLatency,
        pigouNetwork_edgeFlow, f, ↓reduceIte]
      fin_cases p <;> norm_num [pigouNetwork]
  · rw [isApproxWardrop_unit_iff rfl]
    rintro ⟨_, hmin⟩
    have h0 := hmin 0
    have havg : timeAverageFlow f 2 = ![1 / 4, 3 / 4] := by
      ext i
      simp only [timeAverageFlow, sum_range_succ, sum_range_zero, zero_add, f, ↓reduceIte]
      fin_cases i <;> norm_num
    have hp0 : G.pathLatency ![1 / 4, 3 / 4] 0 = (1 / 4 : ℝ) ^ 2 := by
      simp only [pathLatency, G, pigouNetwork_edgeFlow]
      simp [pigouNetwork]
    rw [havg, pigouNetwork_cost, hp0] at h0
    norm_num at h0

end JensenAndAffine

/-! ### Original bounded-slope time-average convergence (inspired by Section 4.7, pp. 97–98) -/

section BoundedSlopeNonlinear

variable {K P E : Type*} [Fintype P] [DecidableEq E] {G : NonatomicCongestionGame K P E}

/-- Key edge-fluctuation bound via Chebyshev covariance and Cauchy–Schwarz: if every resource
latency is nondecreasing and `L`-Lipschitz on `[0, ∞)` (`L ≥ 0`) and `f` has average regret at most
`ε` over `T > 0` steps, then
`∑ e, |(∑ t < T, latency e (edgeFlow (f t) e)) / T - latency e (edgeFlow (timeAverageFlow f T) e)|
  ≤ √(|E| * L * ε)`. -/
private theorem sum_abs_avgLatency_sub_le [DecidableEq K] [Fintype E] {L : ℝ} (hL : 0 ≤ L)
    (hm : ∀ e, MonotoneOn (G.latency e) (Set.Ici 0))
    (hlip : ∀ e x y, 0 ≤ x → x ≤ y → G.latency e y - G.latency e x ≤ L * (y - x))
    {f : ℕ → P → ℝ} {T : ℕ} (hT : 0 < T) {ε : ℝ}
    (hreg : G.HasAvgRegretLe f T ε) :
    ∑ e, |(∑ t ∈ range T, G.latency e (G.edgeFlow (f t) e)) / T -
        G.latency e (G.edgeFlow (timeAverageFlow f T) e)| ≤
      √((Fintype.card E : ℝ) * L * ε) := by
  have hT_pos : (0 : ℝ) < T := by exact_mod_cast hT
  set fbar := timeAverageFlow f T
  set cbar : E → ℝ := fun e => (∑ t ∈ range T, G.latency e (G.edgeFlow (f t) e)) / T
  have hfbar : G.IsFeasible fbar := G.isFeasible_timeAverageFlow hT hreg.1
  have hedge_sq : ∀ e, (cbar e - G.latency e (G.edgeFlow fbar e)) ^ 2 ≤
      L * ((∑ t ∈ range T, G.edgeFlow (f t) e * G.latency e (G.edgeFlow (f t) e)) / T -
        G.edgeFlow fbar e * cbar e) := by
    intro e
    set xhat := G.edgeFlow fbar e
    have hxhat0 : 0 ≤ xhat := G.edgeFlow_nonneg hfbar.1 e
    have hpt : ∀ t ∈ range T, (G.latency e (G.edgeFlow (f t) e) - G.latency e xhat) ^ 2 ≤
        L * ((G.edgeFlow (f t) e - xhat) *
          (G.latency e (G.edgeFlow (f t) e) - G.latency e xhat)) := by
      intro t ht
      set xt := G.edgeFlow (f t) e
      have hxt0 : 0 ≤ xt := G.edgeFlow_nonneg (hreg.1 t (mem_range.1 ht)).1 e
      rcases le_total xhat xt with hle | hle
      · have h1 : 0 ≤ G.latency e xt - G.latency e xhat := sub_nonneg.2 (hm e hxhat0 hxt0 hle)
        have h2 : G.latency e xt - G.latency e xhat ≤ L * (xt - xhat) := hlip e xhat xt hxhat0 hle
        nlinarith [mul_le_mul_of_nonneg_right h2 h1]
      · have h1 : 0 ≤ G.latency e xhat - G.latency e xt := sub_nonneg.2 (hm e hxt0 hxhat0 hle)
        have h2 : G.latency e xhat - G.latency e xt ≤ L * (xhat - xt) := hlip e xt xhat hxt0 hle
        nlinarith [mul_le_mul_of_nonneg_right h2 h1]
    have hcs := _root_.sq_sum_le_card_mul_sum_sq (s := range T)
      (f := fun t => G.latency e (G.edgeFlow (f t) e) - G.latency e xhat)
    rw [card_range] at hcs
    have hsum_diff : (∑ t ∈ range T, (G.latency e (G.edgeFlow (f t) e) - G.latency e xhat)) / T =
        cbar e - G.latency e xhat := by
      rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, sub_div,
        mul_div_cancel_left₀ _ hT_pos.ne']
    have hdiv_sq : (cbar e - G.latency e xhat) ^ 2 ≤
        (∑ t ∈ range T, (G.latency e (G.edgeFlow (f t) e) - G.latency e xhat) ^ 2) / T := by
      rw [← hsum_diff, div_pow, div_le_iff₀ (pow_pos hT_pos 2)]
      calc (∑ t ∈ range T, (G.latency e (G.edgeFlow (f t) e) - G.latency e xhat)) ^ 2
          ≤ (T : ℝ) * ∑ t ∈ range T,
              (G.latency e (G.edgeFlow (f t) e) - G.latency e xhat) ^ 2 := hcs
        _ = ((∑ t ∈ range T, (G.latency e (G.edgeFlow (f t) e) - G.latency e xhat) ^ 2) / T) *
              (T : ℝ) ^ 2 := by field_simp [hT_pos.ne']
    have hcov : (∑ t ∈ range T, (G.edgeFlow (f t) e - xhat) *
        (G.latency e (G.edgeFlow (f t) e) - G.latency e xhat)) / T =
        (∑ t ∈ range T, G.edgeFlow (f t) e * G.latency e (G.edgeFlow (f t) e)) / T -
          xhat * cbar e := by
      have hexp : ∀ t ∈ range T, (G.edgeFlow (f t) e - xhat) *
          (G.latency e (G.edgeFlow (f t) e) - G.latency e xhat) =
          G.edgeFlow (f t) e * G.latency e (G.edgeFlow (f t) e) -
            xhat * G.latency e (G.edgeFlow (f t) e) -
            G.edgeFlow (f t) e * G.latency e xhat + xhat * G.latency e xhat :=
        fun _ _ => by ring
      rw [sum_congr rfl hexp, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
        ← mul_sum, ← sum_mul, sum_const, card_range, nsmul_eq_mul]
      have hxhat_sum : ∑ t ∈ range T, G.edgeFlow (f t) e = (T : ℝ) * xhat := by
        have h := G.edgeFlow_timeAverageFlow f T e
        change xhat = (∑ t ∈ range T, G.edgeFlow (f t) e) / T at h
        rw [h, mul_div_cancel₀ _ hT_pos.ne']
      rw [hxhat_sum]
      dsimp only [cbar]
      field_simp [hT_pos.ne']
      ring
    calc (cbar e - G.latency e xhat) ^ 2
        ≤ (∑ t ∈ range T, (G.latency e (G.edgeFlow (f t) e) - G.latency e xhat) ^ 2) / T := hdiv_sq
      _ ≤ (∑ t ∈ range T, L * ((G.edgeFlow (f t) e - xhat) *
            (G.latency e (G.edgeFlow (f t) e) - G.latency e xhat))) / T :=
          div_le_div_of_nonneg_right (sum_le_sum hpt) hT_pos.le
      _ = L * ((∑ t ∈ range T, G.edgeFlow (f t) e * G.latency e (G.edgeFlow (f t) e)) / T -
            xhat * cbar e) := by rw [← mul_sum, mul_div_assoc, hcov]
  have hsum_cov_le : ∑ e, ((∑ t ∈ range T,
      G.edgeFlow (f t) e * G.latency e (G.edgeFlow (f t) e)) / T -
        G.edgeFlow fbar e * cbar e) ≤ ε := by
    rw [sum_sub_distrib, ← avgCost_eq_sum_edgeFlow, ← avgPathLatency_eq_sum_edgeFlow]
    linarith [hreg.2 fbar hfbar]
  have hsum_sq_le : ∑ e, (cbar e - G.latency e (G.edgeFlow fbar e)) ^ 2 ≤ L * ε := by
    calc ∑ e, (cbar e - G.latency e (G.edgeFlow fbar e)) ^ 2
        ≤ ∑ e, L * ((∑ t ∈ range T, G.edgeFlow (f t) e * G.latency e (G.edgeFlow (f t) e)) / T -
            G.edgeFlow fbar e * cbar e) := sum_le_sum fun e _ => hedge_sq e
      _ = L * ∑ e, ((∑ t ∈ range T, G.edgeFlow (f t) e * G.latency e (G.edgeFlow (f t) e)) / T -
            G.edgeFlow fbar e * cbar e) := by rw [← mul_sum]
      _ ≤ L * ε := mul_le_mul_of_nonneg_left hsum_cov_le hL
  have hcs_E := _root_.sq_sum_le_card_mul_sum_sq (s := (univ : Finset E))
    (f := fun e => |cbar e - G.latency e (G.edgeFlow fbar e)|)
  simp only [card_univ, sq_abs] at hcs_E
  have hprod_le : (∑ e, |cbar e - G.latency e (G.edgeFlow fbar e)|) ^ 2 ≤
      (Fintype.card E : ℝ) * L * ε := by
    calc (∑ e, |cbar e - G.latency e (G.edgeFlow fbar e)|) ^ 2
        ≤ (Fintype.card E : ℝ) * ∑ e, (cbar e - G.latency e (G.edgeFlow fbar e)) ^ 2 := hcs_E
      _ ≤ (Fintype.card E : ℝ) * (L * ε) :=
          mul_le_mul_of_nonneg_left hsum_sq_le (Nat.cast_nonneg _)
      _ = (Fintype.card E : ℝ) * L * ε := by ring
  rw [← Real.sqrt_sq (sum_nonneg fun _ _ => abs_nonneg _)]
  exact Real.sqrt_le_sqrt hprod_le

omit [DecidableEq E] in
/-- All feasible flows of `G` have the same total path flow `∑ p, g p`. -/
private theorem sum_eq_of_isFeasible [DecidableEq K] {f g : P → ℝ}
    (hf : G.IsFeasible f) (hg : G.IsFeasible g) : ∑ p, g p = ∑ p, f p := by
  have hmaps : ∀ p ∈ (univ : Finset P), G.commodity p ∈ (univ : Finset P).image G.commodity :=
    fun p _ => mem_image_of_mem _ (mem_univ p)
  rw [← sum_fiberwise_of_maps_to hmaps, ← sum_fiberwise_of_maps_to hmaps]
  exact sum_congr rfl fun k _ => (hg.2 k).trans (hf.2 k).symm

/-- Weighted difference between the time-averaged path latencies and those at the time-average
flow, bounded in absolute value by `totalFlow * ∑_e |cbar e - latency e (edgeFlow fbar e)|`. -/
private theorem abs_avgPathLatency_sub_pathLatency_le [DecidableEq K] [Fintype E]
    {L : ℝ} (hL : 0 ≤ L) (hm : ∀ e, MonotoneOn (G.latency e) (Set.Ici 0))
    (hlip : ∀ e x y, 0 ≤ x → x ≤ y → G.latency e y - G.latency e x ≤ L * (y - x))
    {f : ℕ → P → ℝ} {T : ℕ} (hT : 0 < T) {ε : ℝ} (hreg : G.HasAvgRegretLe f T ε)
    {g : P → ℝ} (hg : G.IsFeasible g) :
    |(∑ t ∈ range T, ∑ p, g p * G.pathLatency (f t) p) / T -
        ∑ p, g p * G.pathLatency (timeAverageFlow f T) p| ≤
      (∑ p, f 0 p) * √((Fintype.card E : ℝ) * L * ε) := by
  have hf0 : G.IsFeasible (f 0) := hreg.1 0 hT
  have habs := sum_abs_avgLatency_sub_le hL hm hlip hT hreg
  have hedge_le : ∀ e, G.edgeFlow g e ≤ ∑ p, f 0 p := fun e => by
    rw [← sum_eq_of_isFeasible hf0 hg]
    exact sum_le_univ_sum_of_nonneg hg.1
  have h2 : ∑ p, g p * G.pathLatency (timeAverageFlow f T) p =
      ∑ e, G.edgeFlow g e * G.latency e (G.edgeFlow (timeAverageFlow f T) e) :=
    G.sum_mul_sum_resources g _
  rw [avgPathLatency_eq_sum_edgeFlow, h2, ← sum_sub_distrib]
  calc |∑ e, (G.edgeFlow g e * ((∑ t ∈ range T, G.latency e (G.edgeFlow (f t) e)) / T) -
          G.edgeFlow g e * G.latency e (G.edgeFlow (timeAverageFlow f T) e))|
      ≤ ∑ e, |G.edgeFlow g e * ((∑ t ∈ range T, G.latency e (G.edgeFlow (f t) e)) / T -
          G.latency e (G.edgeFlow (timeAverageFlow f T) e))| := by
        simpa only [mul_sub] using abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, (∑ p, f 0 p) * |(∑ t ∈ range T, G.latency e (G.edgeFlow (f t) e)) / T -
          G.latency e (G.edgeFlow (timeAverageFlow f T) e)| := by
        refine sum_le_sum fun e _ => ?_
        rw [abs_mul, abs_of_nonneg (G.edgeFlow_nonneg hg.1 e)]
        exact mul_le_mul_of_nonneg_right (hedge_le e) (abs_nonneg _)
    _ = (∑ p, f 0 p) * ∑ e, |(∑ t ∈ range T, G.latency e (G.edgeFlow (f t) e)) / T -
          G.latency e (G.edgeFlow (timeAverageFlow f T) e)| := by rw [← mul_sum]
    _ ≤ (∑ p, f 0 p) * √((Fintype.card E : ℝ) * L * ε) :=
        mul_le_mul_of_nonneg_left habs (sum_nonneg fun p _ => hf0.1 p)

/-- **Original bounded-slope time-average convergence to approximate Wardrop equilibrium**
(inspired by the bounded-slope discussion in [BlumMansour2007AGT], Section 4.7, pp. 97–98; the
source's per-day `(1 - ε)`-fraction convergence claim remains open under #7789): if every resource
latency is nondecreasing and `L`-Lipschitz on `[0, ∞)` (`L ≥ 0`), then any flow sequence `f` with
average external regret at most `ε` over `T > 0` steps has time-average flow `timeAverageFlow f T`
that is `(ε + 2 * (∑ p, f 0 p) * √(|E| * L * ε))`-Wardrop. -/
theorem isApproxWardrop_timeAverageFlow_of_lipschitz [DecidableEq K] [Fintype E]
    {L : ℝ} (hL : 0 ≤ L)
    (hm : ∀ e, MonotoneOn (G.latency e) (Set.Ici 0))
    (hlip : ∀ e x y, 0 ≤ x → x ≤ y → G.latency e y - G.latency e x ≤ L * (y - x))
    {f : ℕ → P → ℝ} {T : ℕ} (hT : 0 < T) {ε : ℝ}
    (hreg : G.HasAvgRegretLe f T ε) :
    G.IsApproxWardrop (ε + 2 * (∑ p, f 0 p) * √((Fintype.card E : ℝ) * L * ε))
      (timeAverageFlow f T) := by
  set fbar := timeAverageFlow f T
  have hfbar : G.IsFeasible fbar := G.isFeasible_timeAverageFlow hT hreg.1
  have hT_pos : (0 : ℝ) < T := by exact_mod_cast hT
  have hcov_nonneg : (∑ t ∈ range T, ∑ p, fbar p * G.pathLatency (f t) p) / T ≤
      (∑ t ∈ range T, G.cost (f t)) / T := by
    rw [avgPathLatency_eq_sum_edgeFlow, avgCost_eq_sum_edgeFlow]
    refine sum_le_sum fun e _ => ?_
    have hmv : MonovaryOn (fun t => G.edgeFlow (f t) e)
        (fun t => G.latency e (G.edgeFlow (f t) e)) (range T) := fun t ht s hs hlt => by
      exact le_of_not_gt fun hgt =>
        hlt.not_ge (hm e (G.edgeFlow_nonneg (hreg.1 s (mem_range.1 hs)).1 e)
          (G.edgeFlow_nonneg (hreg.1 t (mem_range.1 ht)).1 e) hgt.le)
    have hcheb := hmv.sum_mul_sum_le_card_mul_sum
    rw [card_range] at hcheb
    rw [G.edgeFlow_timeAverageFlow, div_mul_div_comm,
      div_le_div_iff₀ (mul_pos hT_pos hT_pos) hT_pos]
    nlinarith
  have hfbar_diff := (abs_le.1 (abs_avgPathLatency_sub_pathLatency_le hL hm hlip hT hreg hfbar)).1
  refine ⟨hfbar, fun g hg => ?_⟩
  have hg_diff := (abs_le.1 (abs_avgPathLatency_sub_pathLatency_le hL hm hlip hT hreg hg)).2
  have hcost_fbar : ∑ p, fbar p * G.pathLatency fbar p = G.cost fbar := rfl
  linarith [hreg.2 g hg]

/-- **Original sharpened bounded-slope time-average bound for convex latencies** (inspired by
[BlumMansour2007AGT], Section 4.7, pp. 97–98): when resource latencies are convex, nondecreasing
and `L`-Lipschitz on `[0, ∞)`, convexity gives
`G.cost (timeAverageFlow f T) ≤ (∑ t < T, G.cost (f t)) / T` directly, eliminating one of the two
fluctuation error terms. -/
theorem isApproxWardrop_timeAverageFlow_of_convexOn_of_lipschitz [DecidableEq K] [Fintype E]
    {L : ℝ} (hL : 0 ≤ L)
    (hm : ∀ e, MonotoneOn (G.latency e) (Set.Ici 0))
    (hconv : ∀ e, ConvexOn ℝ (Set.Ici 0) (G.latency e))
    (hlip : ∀ e x y, 0 ≤ x → x ≤ y → G.latency e y - G.latency e x ≤ L * (y - x))
    {f : ℕ → P → ℝ} {T : ℕ} (hT : 0 < T) {ε : ℝ}
    (hreg : G.HasAvgRegretLe f T ε) :
    G.IsApproxWardrop (ε + (∑ p, f 0 p) * √((Fintype.card E : ℝ) * L * ε))
      (timeAverageFlow f T) := by
  have hcost_le := cost_timeAverageFlow_le
    (fun e => convexOn_mul_of_monotoneOn_convexOn (hm e) (hconv e)) hT
    fun t ht => (hreg.1 t ht).1
  refine ⟨G.isFeasible_timeAverageFlow hT hreg.1, fun g hg => ?_⟩
  have hg_diff := (abs_le.1 (abs_avgPathLatency_sub_pathLatency_le hL hm hlip hT hreg hg)).2
  linarith [hreg.2 g hg]

/-- **Original zero-regret time-average convergence for bounded-slope latencies** (corollary of
`isApproxWardrop_timeAverageFlow_of_lipschitz`): at zero external regret (`ε = 0`), for any
nondecreasing `L`-Lipschitz latencies on `[0, ∞)`, the time-averaged flow is an exact Wardrop
equilibrium. -/
theorem isWardrop_timeAverageFlow_of_hasAvgRegretLe_zero [DecidableEq K] [Finite E]
    {L : ℝ} (hL : 0 ≤ L)
    (hm : ∀ e, MonotoneOn (G.latency e) (Set.Ici 0))
    (hlip : ∀ e x y, 0 ≤ x → x ≤ y → G.latency e y - G.latency e x ≤ L * (y - x))
    {f : ℕ → P → ℝ} {T : ℕ} (hT : 0 < T)
    (hreg : G.HasAvgRegretLe f T 0) :
    G.IsWardrop (timeAverageFlow f T) := by
  have := Fintype.ofFinite E
  have h := isApproxWardrop_timeAverageFlow_of_lipschitz hL hm hlip hT hreg
  simp only [mul_zero, Real.sqrt_zero, add_zero] at h
  exact G.isApproxWardrop_zero_iff.1 h

end BoundedSlopeNonlinear

end NonatomicCongestionGame

end Cslib.GameTheory
