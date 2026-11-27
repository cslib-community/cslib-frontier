/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Congestion.Pricing.PricedWardrop
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# Oligopoly pricing and tight efficiency bounds in parallel networks

When competing profit-maximizing service providers `s : Provider` own disjoint portfolios of
parallel links (`owner : Link → Provider`), each provider sets per-unit bandwidth prices on its
links anticipating end-user Wardrop routing ([Ozdaglar and Srikant, Section 22.2.4, Eq. (22.26),
p. 583][OzdaglarSrikant2007]; [Acemoglu and Ozdaglar, Definition 4.1,
p. 8][AcemogluOzdaglar2007MOR]).

Unlike a monopolist—who internalizes congestion across the entire network and extracts `100%` of
the optimal social surplus—oligopolistic providers add a strategic congestion markup on top of their
Pigovian marginal-congestion cost (`price_eq_min_markup`, `price_eq_two_link_markup`,
[OzdaglarSrikant2007], Eq. (22.27), p. 583). Nevertheless, the worst-case efficiency loss is
strictly bounded independent of the number of links and portfolio structure:

1. **Inelastic reservation-utility parallel networks** ([Ozdaglar and Srikant, Theorem 22.3,
   p. 584][OzdaglarSrikant2007]; [Acemoglu and Ozdaglar, Theorem 5.2,
   p. 20][AcemogluOzdaglar2007MOR]): every pure-strategy Oligopoly Equilibrium achieves at least
   `5 / 6` of the optimal social surplus (`oligopoly_surplus_five_sixths`), and **Example 22.2**
   achieves `5 / 6` exactly for every `I = n + 2 ≥ 2` (`oligopolyTightness_surplus_eq_five_sixths`).
2. **Elastic traffic with concave marginal utility** ([Ozdaglar and Srikant, Theorem 22.4,
   p. 585][OzdaglarSrikant2007]; [Ozdaglar2008]): when aggregate user utility `u` is smooth and
   concave with concave marginal utility `u'`, every pure-strategy Oligopoly Equilibrium on parallel
   links achieves at least `2 / 3` of the optimal elastic social surplus
   (`elastic_oligopoly_surplus_two_thirds`), and this `2 / 3` bound is asymptotically tight even on
   a single link (`elasticTightness_surplus_lt_two_thirds_add`).

## Main definitions

* `Cslib.GameTheory.providerProfit`, `IsOligopolyEquilibrium`, `ZeroLatencySingleton`:
  multi-provider portfolio profit, pure-strategy Oligopoly Equilibrium ([OzdaglarSrikant2007],
  Eq. (22.26), p. 583), and [AcemogluOzdaglar2007MOR] Assumption 4.1 (automatic under injective
  ownership or positive latencies on `(0, ∞)`).
* `Cslib.GameTheory.oligopolyTightnessLatency`, `oligopolyTightnessPrice`, `oligopolyTightnessFlow`:
  `I`-link exact `5 / 6` tightness witness ([OzdaglarSrikant2007], Example 22.2, p. 584).
* `Cslib.GameTheory.SmoothConcaveMarginalUtility`, `IsElasticPricedWardrop`, `elasticSocialSurplus`,
  `IsElasticSocialOptimum`, `IsElasticOligopolyEquilibrium`: elastic-traffic pricing model with
  concave marginal utility ([OzdaglarSrikant2007], Section 22.2.6, pp. 584–585).

## Main results

* `Cslib.GameTheory.IsOligopolyEquilibrium.price_pos_and_flow_pos`,
  `Cslib.GameTheory.IsOligopolyEquilibrium.price_eq_min_markup`: interior positivity and explicit OE
  price formula ([AcemogluOzdaglar2007MOR], Lemma 4.2 and Corollary 4.1, pp. 10–12;
  [OzdaglarSrikant2007], p. 583).
* `Cslib.GameTheory.oligopoly_surplus_five_sixths`,
  `Cslib.GameTheory.oligopoly_surplus_five_sixths_of_injective`,
  `Cslib.GameTheory.oligopoly_efficiency_ge_five_sixths`: tight `5 / 6` social-surplus bound
  ([OzdaglarSrikant2007], Theorem 22.3, p. 584; [AcemogluOzdaglar2007MOR], Theorem 5.2, p. 20).
* `Cslib.GameTheory.oligopolyTightness_isOligopolyEquilibrium`,
  `Cslib.GameTheory.oligopolyTightness_surplus_eq_five_sixths`: checked `I`-link `5 / 6` witness
  ([OzdaglarSrikant2007], Example 22.2, p. 584).
* `Cslib.GameTheory.elastic_oligopoly_surplus_two_thirds`,
  `Cslib.GameTheory.elastic_oligopoly_efficiency_ge_two_thirds`,
  `Cslib.GameTheory.elasticTightness_surplus_lt_two_thirds_add`: tight `2 / 3` elastic-traffic
  bound ([OzdaglarSrikant2007], Theorem 22.4, p. 585; [Ozdaglar2008]).

## References

* [AcemogluOzdaglar2007MOR]
* [Ozdaglar2008]
* [OzdaglarSrikant2007]
-/

public section

namespace Cslib.GameTheory

section Definitions

variable {Link Provider : Type*}

/-- Portfolio profit `∑ i with owner i = s, p i * x i` of service provider `s` ([Ozdaglar and
Srikant, Section 22.2.4, p. 582][OzdaglarSrikant2007]). -/
@[expose] def providerProfit [Fintype Link] [DecidableEq Provider] (owner : Link → Provider)
    (s : Provider) (p x : Link → ℝ) : ℝ :=
  ∑ i with owner i = s, p i * x i

/-- A pure-strategy **Oligopoly Equilibrium** `(p, x)` on parallel links partitioned among
service providers via `owner : Link → Provider` ([Ozdaglar and Srikant, Section 22.2.4, Eq. (22.26),
p. 583][OzdaglarSrikant2007]; [Acemoglu and Ozdaglar, Definition 4.1,
p. 8][AcemogluOzdaglar2007MOR]): prices are nonnegative, `x` is a priced Wardrop equilibrium at
`p`, and no provider `s` can increase its portfolio profit by changing prices on its own links. -/
@[expose] def IsOligopolyEquilibrium [Fintype Link] [DecidableEq Provider] (d R : ℝ)
    (latency : Link → ℝ → ℝ) (owner : Link → Provider) (p x : Link → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧
    IsPricedWardrop d R latency p x ∧
    ∀ s p' x', (∀ i, 0 ≤ p' i) → (∀ j, owner j ≠ s → p' j = p j) →
      IsPricedWardrop d R latency p' x' →
      providerProfit owner s p' x' ≤ providerProfit owner s p x

/-- Multi-link zero-latency portfolio condition ([Acemoglu and Ozdaglar, Assumption 4.1, p. 10, and
Section 5.1, Footnote 11, p. 13][AcemogluOzdaglar2007MOR]): any link carrying positive flow with
zero latency is the unique link owned by its provider. Automatically satisfied when each provider
owns a single link (`zeroLatencySingleton_of_injective`) or when latencies are positive at positive
flow (`zeroLatencySingleton_of_latency_pos`). -/
@[expose] def ZeroLatencySingleton (latency : Link → ℝ → ℝ) (owner : Link → Provider)
    (x : Link → ℝ) : Prop :=
  ∀ i, 0 < x i → latency i (x i) = 0 → ∀ j, owner j = owner i → j = i

theorem zeroLatencySingleton_of_injective {latency : Link → ℝ → ℝ} {owner : Link → Provider}
    (hinj : Function.Injective owner) (x : Link → ℝ) :
    ZeroLatencySingleton latency owner x :=
  fun _ _ _ _ hj => hinj hj

theorem zeroLatencySingleton_of_latency_pos {latency : Link → ℝ → ℝ}
    (hpos : ∀ i u, 0 < u → 0 < latency i u) (owner : Link → Provider) (x : Link → ℝ) :
    ZeroLatencySingleton latency owner x :=
  fun i hxi hz => False.elim ((hpos i (x i) hxi).ne' hz)

end Definitions

section Helpers

private theorem SmoothConvexLatencies.latency_le {Link : Type*}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    (i : Link) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : latency i a ≤ latency i b :=
  h.monotoneOn i ha (ha.trans hab) hab

private theorem SmoothConvexLatencies.exists_step_lt {Link : Type*}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    (i : Link) {xi c K η : ℝ} (hxi : 0 ≤ xi) (hc : 0 < c) (hlt_K : latency i xi < K)
    (hη : 0 < η) :
    ∃ δ, 0 < δ ∧ δ < η ∧ δ < c ∧ latency i (xi + δ) < K := by
  obtain ⟨η₁, hη₁, hball⟩ := Metric.eventually_nhds_iff.mp
    ((h.hasDerivAt i xi hxi).continuousAt.eventually (eventually_lt_nhds hlt_K))
  let δ : ℝ := min (min (η / 2) (η₁ / 2)) (c / 2)
  have hδ0 : 0 < δ := lt_min (lt_min (half_pos hη) (half_pos hη₁)) (half_pos hc)
  refine ⟨δ, hδ0, ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hη),
    (min_le_right _ _).trans_lt (half_lt_self hc), hball ?_⟩
  rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hδ0]
  exact ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hη₁)

private theorem SmoothConvexLatencies.exists_zero_swap_step {Link : Type*}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    (i : Link) {q : Link} {xi xq K η : ℝ} (hxi : 0 ≤ xi) (hxq : 0 < xq)
    (hlat_q0 : latency q xq = 0) (hlt_K : latency i xi < K) (hη : 0 < η) :
    ∃ δ, 0 < δ ∧ δ < η ∧ δ < xq ∧ latency i (xi + δ) < K ∧ latency q (xq - δ) = 0 := by
  obtain ⟨δ, hδ0, hδη, hδxq, hlat_i_lt⟩ := h.exists_step_lt i hxi hxq hlt_K hη
  exact ⟨δ, hδ0, hδη, hδxq, hlat_i_lt, le_antisymm ((h.monotoneOn q (Set.mem_Ici.mpr (by linarith))
    (Set.mem_Ici.mpr hxq.le) (by linarith)).trans hlat_q0.le) (h.latency_nonneg q (by linarith))⟩

private theorem le_div_mul_add_of_mul_le {a b c δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (h : a * δ ≤ b * c) : a ≤ b / δ * c + (0 + ε) := by
  rw [div_mul_eq_mul_div, zero_add]
  linarith [(le_div_iff₀ hδ).mpr h]

private theorem mul_div_two_mul {n c : ℝ} (hn : n ≠ 0) : n * (c / (2 * n)) = c / 2 := by
  field_simp

private theorem div_mul_le_of_mul_le {a b c δ : ℝ} (hδ : 0 < δ) (h : b * c ≤ a * δ) :
    b / δ * c ≤ a := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hδ]
  exact h

private theorem convex_comb_scale_zero {t K : ℝ} (ht : 0 < t) (hK : 1 < K) :
    0 < K * t ∧ 0 ≤ 1 / K ∧ 0 ≤ 1 - 1 / K ∧ 1 / K + (1 - 1 / K) = 1 ∧
      (1 / K) • (K * t) + (1 - 1 / K) • (0 : ℝ) = t := by
  have hK_pos : 0 < K := zero_lt_one.trans hK
  refine ⟨mul_pos hK_pos ht, div_nonneg zero_le_one hK_pos.le,
    sub_nonneg.mpr ((div_le_one hK_pos).mpr hK.le), by ring, ?_⟩
  simp only [smul_eq_mul, mul_zero, add_zero]
  field_simp

private theorem exists_pos_le_of_continuousOn_Icc {g : ℝ → ℝ} {r μ : ℝ}
    (hr : 0 < r) (hμ : 0 < μ) (hcont : ContinuousOn g (Set.Icc 0 r))
    (hg0 : g 0 = 0) (hgr : μ ≤ g r) :
    ∃ s, 0 < s ∧ s ≤ r ∧ g s = μ := by
  obtain ⟨s, hs_Icc, hs_eq⟩ := isPreconnected_Icc.intermediate_value₂ (g := fun _ => μ)
    ⟨le_rfl, hr.le⟩ ⟨hr.le, le_rfl⟩ hcont continuousOn_const (by linarith) hgr
  refine ⟨s, lt_of_le_of_ne hs_Icc.1 fun hz => ?_, hs_Icc.2, hs_eq⟩
  subst hz
  linarith

/-- For a smooth convex latency with `latency i 0 = 0` and `0 < x`, `latency i x = 0` if and only
if `latencyDeriv i x = 0`. -/
theorem SmoothConvexLatencies.latency_eq_zero_iff_deriv_eq_zero {Link : Type*}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    (i : Link) {x : ℝ} (hx : 0 < x) :
    latency i x = 0 ↔ latencyDeriv i x = 0 := by
  constructor
  · intro hz
    have hge : 0 ≤ latencyDeriv i x := h.latencyDeriv_nonneg i hx.le
    have hmul : x * latencyDeriv i x ≤ 0 := by
      refine mul_deriv_le_of_forall_pos_sub hx (h.hasDerivAt i x hx.le) fun η hη => ?_
      let δ : ℝ := min (η / 2) (x / 2)
      have hδ0 : 0 < δ := lt_min (half_pos hη) (half_pos hx)
      have hδη : δ < η := (min_le_left _ _).trans_lt (half_lt_self hη)
      have hδx : δ < x := (min_le_right _ _).trans_lt (half_lt_self hx)
      have h0 : latency i (x - δ) = 0 :=
        le_antisymm
          ((h.latency_le i (by linarith) (by linarith)).trans hz.le)
          (h.latency_nonneg i (by linarith))
      exact ⟨δ, hδ0, hδη, hδx, by simp [hz, h0]⟩
    exact le_antisymm (nonpos_of_mul_nonpos_right hmul hx) hge
  · intro hd0
    have hle := h.latency_le_mul_deriv i hx.le
    rw [hd0, mul_zero] at hle
    exact le_antisymm hle (h.latency_nonneg i hx.le)

/-- Strict decrease on `(0, x)` when `latency i x > 0`: by convexity and `latency i 0 = 0`,
`latency i (x - r) < latency i x` for every `0 < r < x`. -/
theorem SmoothConvexLatencies.latency_sub_lt_of_pos {Link : Type*}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    (i : Link) {x r : ℝ} (hr0 : 0 < r) (hrx : r < x) (hpos : 0 < latency i x) :
    latency i (x - r) < latency i x := by
  have hx : 0 < x := hr0.trans hrx
  have hw1 : 0 ≤ r / x := div_nonneg hr0.le hx.le
  have hw2 : 0 ≤ (x - r) / x := div_nonneg (by linarith) hx.le
  have hw_sum : r / x + (x - r) / x = 1 := by field_simp; ring
  have hcomb : (r / x) • (0 : ℝ) + ((x - r) / x) • x = x - r := by
    simp only [smul_eq_mul, mul_zero, zero_add]
    field_simp
  have hconv := (h.convexOn i).2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx.le) hw1 hw2 hw_sum
  rw [hcomb, h.zero_at_zero i, smul_eq_mul, mul_zero, zero_add, smul_eq_mul] at hconv
  have hlt : (x - r) / x * latency i x < 1 * latency i x :=
    mul_lt_mul_of_pos_right ((div_lt_one hx).mpr (by linarith)) hpos
  linarith

end Helpers

section PriceCharacterization

variable {Link Provider : Type*} [Fintype Link] [DecidableEq Provider]

/-- A feasible flow with uniform effective cost `K ≤ R` is a priced Wardrop flow, provided it
routes full demand whenever `K < R`. -/
private theorem isPricedWardrop_of_effectiveCost_eq {d R K : ℝ} {latency : Link → ℝ → ℝ}
    {p x : Link → ℝ} (hx : IsFeasiblePricedFlow d x)
    (hcost : ∀ k, latency k (x k) + p k = K) (hKR : K ≤ R) (hd : K < R → ∑ k, x k = d) :
    IsPricedWardrop d R latency p x :=
  ⟨hx, fun a b _ => ((hcost a).trans (hcost b).symm).le, fun a _ => (hcost a).trans_le hKR,
    fun ⟨a, ha⟩ => hd ((hcost a).symm.trans_lt ha)⟩

/-- At any pure-strategy Oligopoly Equilibrium, every link's price is at least its Pigovian
marginal-congestion cost `x i * latencyDeriv i (x i)`. -/
theorem IsOligopolyEquilibrium.mul_latencyDeriv_le_price {d R : ℝ}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    {owner : Link → Provider} {p x : Link → ℝ}
    (hoe : IsOligopolyEquilibrium d R latency owner p x) (i : Link) :
    x i * latencyDeriv i (x i) ≤ p i :=
  markup_ge_mul_deriv_of_wardrop_bestResponse (fun k => owner k = owner i) rfl hoe.1 hoe.2.1
    (h.monotoneOn i) (h.hasDerivAt i (x i) (hoe.2.1.1.1 i))
    (fun q _ => h.monotoneOn q) (fun q _ => h.continuousOn q)
    (fun m _ => (h.zero_at_zero m).ge)
    (fun p' x' hp'0 hp'comp _ hw' => hoe.2.2 (owner i) p' x' hp'0 hp'comp hw')

private theorem IsOligopolyEquilibrium.providerProfit_pos_of_bound {d R : ℝ}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    {owner : Link → Provider} {p x : Link → ℝ}
    (hoe : IsOligopolyEquilibrium d R latency owner p x)
    (hd_pos : 0 < d) {K : ℝ} (hK_pos : 0 < K) (hK_le_R : K ≤ R) {s : Provider}
    (hge_K : ∀ q, owner q ≠ s → K ≤ latency q (x q) + p q) (hs : ∃ k, owner k = s) :
    0 < providerProfit owner s p x := by
  obtain ⟨k₀, hk₀⟩ := hs
  have hnonneg : 0 ≤ providerProfit owner s p x :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hoe.1 k) (hoe.2.1.1.1 k)
  refine lt_of_le_of_ne hnonneg fun hzero => ?_
  let p' : Link → ℝ := fun k => if owner k = s then K / 2 else p k
  have hp'0 : ∀ k, 0 ≤ p' k := fun k => by
    simp only [p']; split_ifs <;> [linarith; exact hoe.1 k]
  obtain ⟨x', hw'⟩ :=
    exists_isPricedWardrop (R := R) (fun k => h.continuousOn k) hd_pos.le p'
  have hex_s : ∃ m, owner m = s ∧ 0 < x' m := by
    by_contra hnone
    push Not at hnone
    have hm0 : ∀ m, owner m = s → x' m = 0 := fun m hm =>
      le_antisymm (hnone m hm) (hw'.1.1 m)
    have hcost_k₀ : latency k₀ (x' k₀) + p' k₀ = K / 2 := by
      simp [hm0 k₀ hk₀, h.zero_at_zero k₀, p', hk₀]
    have hsum_d : ∑ k, x' k = d := hw'.2.2.2 ⟨k₀, by linarith⟩
    have hex_q : ∃ q, 0 < x' q := by
      by_contra hall
      push Not at hall
      have h0 : ∀ q, x' q = 0 := fun q => le_antisymm (hall q) (hw'.1.1 q)
      simp only [h0, Finset.sum_const_zero] at hsum_d
      linarith
    obtain ⟨q₁, hxq₁⟩ := hex_q
    have hlt_x : ∀ q, 0 < x' q → x' q < x q := fun q hxq => by
      have hqs : owner q ≠ s := fun hqs => by linarith [hm0 q hqs]
      have hward := hw'.2.1 q k₀ hxq
      rw [hcost_k₀] at hward
      simp only [p', hqs, ↓reduceIte] at hward
      have hlat_lt : latency q (x' q) < latency q (x q) := by linarith [hge_K q hqs]
      by_contra hge_x
      push Not at hge_x
      linarith [h.latency_le q (hoe.2.1.1.1 q) hge_x]
    have hsum_lt : ∑ k, x' k < ∑ k, x k := by
      refine Finset.sum_lt_sum (fun k _ => ?_) ⟨q₁, Finset.mem_univ q₁, hlt_x q₁ hxq₁⟩
      rcases (hw'.1.1 k).eq_or_lt with h0 | hpos_k
      · rw [← h0]; exact hoe.2.1.1.1 k
      · exact (hlt_x k hpos_k).le
    linarith [hoe.2.1.1.2]
  obtain ⟨m, hms, hxm⟩ := hex_s
  have hprof_new : 0 < providerProfit owner s p' x' := by
    have hm_mem : m ∈ Finset.univ.filter (fun k => owner k = s) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ m, hms⟩
    have hterm : 0 < p' m * x' m := by
      simp only [p', hms, ↓reduceIte]
      exact mul_pos (half_pos hK_pos) hxm
    exact hterm.trans_le
      (Finset.single_le_sum (fun k _ => mul_nonneg (hp'0 k) (hw'.1.1 k)) hm_mem)
  have hbest := hoe.2.2 s p' x' hp'0 (fun q hq => by simp [p', hq]) hw'
  linarith

/-- **Zero-revenue OE optimality** ([Acemoglu and Ozdaglar, Lemma 5.1,
p. 13][AcemogluOzdaglar2007MOR]): if `p i * x i = 0` on every link at an Oligopoly Equilibrium, then
`x` is a social optimum. -/
theorem IsOligopolyEquilibrium.isSocialOptimum_of_forall_mul_eq_zero {d R : ℝ}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    {owner : Link → Provider} {p x : Link → ℝ}
    (hoe : IsOligopolyEquilibrium d R latency owner p x) (hzero : ∀ i, p i * x i = 0) :
    IsSocialOptimum d R latency x := by
  refine ⟨hoe.2.1.1, fun y hy => ?_⟩
  by_cases hne : Nonempty Link
  · rcases le_or_gt d 0 with hd0 | hd_pos
    · have hy0 : ∀ i, y i = 0 := fun i =>
        le_antisymm ((Finset.single_le_sum (fun k _ => hy.1 k) (Finset.mem_univ i)).trans
          (hy.2.trans hd0)) (hy.1 i)
      have hx0 : ∀ i, x i = 0 := fun i =>
        le_antisymm ((Finset.single_le_sum (fun k _ => hoe.2.1.1.1 k) (Finset.mem_univ i)).trans
          (hoe.2.1.1.2.trans hd0)) (hoe.2.1.1.1 i)
      simp [socialSurplus, hy0, hx0]
    rcases le_or_gt R 0 with hR0 | hR_pos
    · have hy_nonpos : socialSurplus R latency y ≤ 0 := by
        refine Finset.sum_nonpos fun i _ => ?_
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith [h.latency_nonneg i (hy.1 i)]) (hy.1 i)
      exact hy_nonpos.trans (hoe.2.1.socialSurplus_nonneg hoe.1)
    -- Now Nonempty Link, 0 < d, 0 < R. First show latency j (x j) = 0 for all j:
    have hlat_zero : ∀ j, latency j (x j) = 0 := fun j => by
      rcases (h.latency_nonneg j (hoe.2.1.1.1 j)).eq_or_lt with hz | hpos
      · exact hz.symm
      · obtain ⟨hxj, hdj⟩ := h.deriv_pos_of_latency_pos j (hoe.2.1.1.1 j) hpos
        have hpi : 0 < p j := (mul_pos hxj hdj).trans_le (hoe.mul_latencyDeriv_le_price h j)
        linarith [mul_pos hpi hxj, hzero j]
    -- Show ∃ j₀, 0 < x j₀:
    have hex_pos : ∃ j₀, 0 < x j₀ := by
      by_contra! hall
      have hx_all0 : ∀ k, x k = 0 := fun k => le_antisymm (hall k) (hoe.2.1.1.1 k)
      have hsum0 : ∑ k, x k < d := by simp [hx_all0, hd_pos]
      obtain ⟨i₀⟩ := hne
      have hpos_prof := hoe.providerProfit_pos_of_bound h hd_pos hR_pos le_rfl
        (fun q _ => hoe.2.1.le_effectiveCost_of_sum_lt hsum0 q) ⟨i₀, rfl⟩
      have hprof_old : providerProfit owner (owner i₀) p x = 0 :=
        Finset.sum_eq_zero fun k _ => hzero k
      linarith
    obtain ⟨j₀, hxj₀⟩ := hex_pos
    have hpj₀ : p j₀ = 0 := (mul_eq_zero.mp (hzero j₀)).resolve_right hxj₀.ne'
    have hsum_d : ∑ k, x k = d :=
      hoe.2.1.2.2.2 ⟨j₀, by rw [hlat_zero j₀, hpj₀, add_zero]; exact hR_pos⟩
    have hx_surp : socialSurplus R latency x = R * d := by
      simp only [socialSurplus, hlat_zero, sub_zero, ← Finset.mul_sum, hsum_d]
    rw [hx_surp]
    have hle1 : socialSurplus R latency y ≤ ∑ i, R * y i := by
      refine Finset.sum_le_sum fun i _ => ?_
      nlinarith [h.latency_nonneg i (hy.1 i), hy.1 i]
    rw [← Finset.mul_sum] at hle1
    exact hle1.trans (mul_le_mul_of_nonneg_left hy.2 hR_pos.le)
  · rw [not_nonempty_iff] at hne
    simp [socialSurplus]

/-- **Positive provider profits** ([Acemoglu and Ozdaglar, Lemma 4.2(a),
p. 10][AcemogluOzdaglar2007MOR]): if some link has `0 < p i₀ * x i₀` at an Oligopoly Equilibrium,
every provider owning at least one link earns strictly positive profit. -/
theorem IsOligopolyEquilibrium.providerProfit_pos {d R : ℝ}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    {owner : Link → Provider} {p x : Link → ℝ}
    (hoe : IsOligopolyEquilibrium d R latency owner p x)
    (hpos : ∃ i₀, 0 < p i₀ * x i₀) {s : Provider} (hs : ∃ k, owner k = s) :
    0 < providerProfit owner s p x := by
  obtain ⟨i₀, hi₀⟩ := hpos
  have hpi₀ : 0 < p i₀ := pos_of_mul_pos_left hi₀ (hoe.2.1.1.1 i₀)
  have hxi₀ : 0 < x i₀ := pos_of_mul_pos_right hi₀ (hoe.1 i₀)
  have hd_pos : 0 < d :=
    (hxi₀.trans_le (Finset.single_le_sum (fun k _ => hoe.2.1.1.1 k) (Finset.mem_univ i₀))).trans_le
      hoe.2.1.1.2
  exact hoe.providerProfit_pos_of_bound h hd_pos
    (by linarith [h.latency_nonneg i₀ hxi₀.le]) (hoe.2.1.2.2.1 i₀ hxi₀)
    (fun q _ => hoe.2.1.2.1 i₀ q hxi₀) hs

/-- **Interior positivity on every link** ([Acemoglu and Ozdaglar, Lemma 4.2(b),
p. 10][AcemogluOzdaglar2007MOR]): under `ZeroLatencySingleton`, if some link has `0 < p i₀ * x i₀`
at an Oligopoly Equilibrium, then `0 < p j` and `0 < x j` on **every** link `j`. -/
theorem IsOligopolyEquilibrium.price_pos_and_flow_pos {d R : ℝ}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    {owner : Link → Provider} {p x : Link → ℝ}
    (hoe : IsOligopolyEquilibrium d R latency owner p x)
    (hzs : ZeroLatencySingleton latency owner x)
    (hpos : ∃ i₀, 0 < p i₀ * x i₀) (j : Link) :
    0 < p j ∧ 0 < x j := by
  classical
  let s := owner j
  have hs_pos : 0 < providerProfit owner s p x := hoe.providerProfit_pos h hpos ⟨j, rfl⟩
  have hex_m : ∃ m, owner m = s ∧ 0 < p m * x m := by
    by_contra hnone
    push Not at hnone
    have hz : providerProfit owner s p x = 0 :=
      Finset.sum_eq_zero fun m hm =>
        le_antisymm (hnone m (Finset.mem_filter.mp hm).2) (mul_nonneg (hoe.1 m) (hoe.2.1.1.1 m))
    linarith
  obtain ⟨m, hms, hm_pos⟩ := hex_m
  have hm_mem : m ∈ Finset.univ.filter (fun k => owner k = s) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ m, hms⟩
  have hpm : 0 < p m := pos_of_mul_pos_left hm_pos (hoe.2.1.1.1 m)
  have hxm : 0 < x m := pos_of_mul_pos_right hm_pos (hoe.1 m)
  by_cases hjm : j = m
  · subst hjm; exact ⟨hpm, hxm⟩
  have hprod_pos : 0 < p j * x j := by
    refine lt_of_le_of_ne (mul_nonneg (hoe.1 j) (hoe.2.1.1.1 j)) fun hzero_j => ?_
    have hlat_m_pos : 0 < latency m (x m) :=
      (h.latency_nonneg m hxm.le).lt_of_ne fun hz => hjm (hzs m hxm hz.symm j hms.symm)
    obtain ⟨K, hK⟩ : ∃ K, K = latency m (x m) + p m := ⟨_, rfl⟩
    have hK_le_R : K ≤ R := hK ▸ hoe.2.1.2.2.1 m hxm
    -- Show x j = 0 (if x j > 0, then p j = 0, so latency j (x j) = K > 0, forcing p j > 0):
    have hxj0 : x j = 0 := by
      refine ((hoe.2.1.1.1 j).eq_or_lt.resolve_right fun hxj_pos => ?_).symm
      have hpj0 : p j = 0 := (mul_eq_zero.mp hzero_j.symm).resolve_right hxj_pos.ne'
      have heff := hoe.2.1.effectiveCost_eq_of_pos hxj_pos hxm
      obtain ⟨_, hdj_pos⟩ := h.deriv_pos_of_latency_pos j hxj_pos.le (by linarith)
      linarith [(mul_pos hxj_pos hdj_pos).trans_le (hoe.mul_latencyDeriv_le_price h j)]
    -- Use continuity of latency j at 0 to choose 0 < ε < x m with latency j ε < latency m (x m):
    have hcont_j : ContinuousWithinAt (latency j) (Set.Ici 0) 0 := h.continuousOn j 0 le_rfl
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ)), latency j t < latency m (x m) :=
      hcont_j.eventually (eventually_lt_nhds ((h.zero_at_zero j).trans_lt hlat_m_pos))
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨η, hη, hball⟩ := hev
    let ε : ℝ := min (η / 2) (x m / 2)
    have hε0 : 0 < ε := lt_min (half_pos hη) (half_pos hxm)
    have hε_xm : ε < x m := (min_le_right _ _).trans_lt (half_lt_self hxm)
    have hdist : dist ε 0 < η := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hε0]
      exact (min_le_left _ _).trans_lt (half_lt_self hη)
    have hlat_j_lt : latency j ε < latency m (x m) := hball hdist (Set.mem_Ici.mpr hε0.le)
    have hlat_m_le : latency m (x m - ε) ≤ latency m (x m) :=
      h.latency_le m (by linarith) (by linarith)
    let x' : Link → ℝ := Function.update (Function.update x m (x m - ε)) j (x j + ε)
    let p' : Link → ℝ :=
      Function.update (Function.update p m (K - latency m (x m - ε))) j (K - latency j ε)
    have hp'0 : ∀ k, 0 ≤ p' k := fun k => by
      simp only [p', Function.update_apply]
      split_ifs <;> linarith [hoe.1 k]
    have hp'comp : ∀ q, owner q ≠ s → p' q = p q := fun q hq => by
      have hqj : q ≠ j := fun h => hq (h ▸ rfl)
      have hqm : q ≠ m := fun h => hq (h ▸ hms)
      simp [p', hqj, hqm]
    have hx'sum : ∑ k, x' k = ∑ k, x k := sum_update_sub_add_eq x (Ne.symm hjm) ε
    have hcost : ∀ k, K ≤ latency k (x' k) + p' k ∧
        (0 < x' k → latency k (x' k) + p' k = K) := fun k => by
      rcases eq_or_ne k j with rfl | hkj
      · simp [x', p', hxj0]
      rcases eq_or_ne k m with rfl | hkm
      · simp [x', p', hkj]
      simp only [x', p', Function.update_of_ne hkj, Function.update_of_ne hkm]
      exact ⟨hK ▸ hoe.2.1.2.1 m k hxm, fun hxk => hK ▸ hoe.2.1.effectiveCost_eq_of_pos hxk hxm⟩
    have hw' : IsPricedWardrop d R latency p' x' :=
      ⟨⟨nonneg_update_sub_add hoe.2.1.1.1 hε0.le hε_xm.le, hx'sum.trans_le hoe.2.1.1.2⟩,
        fun a b ha => ((hcost a).2 ha).trans_le (hcost b).1,
        fun a ha => ((hcost a).2 ha).trans_le hK_le_R,
        fun ⟨a, ha⟩ => hx'sum.trans (hoe.2.1.2.2.2 ⟨m, by linarith [(hcost a).1]⟩)⟩
    have hbest := hoe.2.2 s p' x' hp'0 hp'comp hw'
    have hdiff : providerProfit owner s p' x' - providerProfit owner s p x =
        (K - latency j ε) * ε + ((K - latency m (x m - ε)) * (x m - ε) - p m * x m) := by
      have hj_mem : j ∈ Finset.univ.filter (fun k => owner k = s) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      rw [providerProfit, providerProfit, ← Finset.sum_sub_distrib, Finset.sum_eq_add_of_mem j m
        hj_mem hm_mem hjm fun k _ hk => by simp [x', p', hk.1, hk.2]]
      simp [x', p', Ne.symm hjm, hxj0]
    subst hK
    nlinarith [mul_nonneg (sub_nonneg.2 hlat_m_le) (sub_nonneg.2 hε_xm.le),
      mul_pos hε0 (sub_pos.2 hlat_j_lt)]
  exact ⟨pos_of_mul_pos_left hprod_pos (hoe.2.1.1.1 j),
    pos_of_mul_pos_right hprod_pos (hoe.1 j)⟩

/-- **Partial-demand OE optimality** ([Acemoglu and Ozdaglar, Lemma 5.2(ii),
p. 14][AcemogluOzdaglar2007MOR]): under `ZeroLatencySingleton`, if an Oligopoly Equilibrium routes
strictly less than `d` units of traffic (`∑ i, x i < d`), then `x` is a social optimum. -/
theorem IsOligopolyEquilibrium.isSocialOptimum_of_sum_lt {d R : ℝ}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    {owner : Link → Provider} {p x : Link → ℝ}
    (hoe : IsOligopolyEquilibrium d R latency owner p x)
    (hzs : ZeroLatencySingleton latency owner x) (hlt : ∑ i, x i < d) :
    IsSocialOptimum d R latency x := by
  classical
  by_cases hpos : ∃ i₀, 0 < p i₀ * x i₀
  · have hmarg_zero : ∀ i, R - latency i (x i) - x i * latencyDeriv i (x i) = 0 := fun i => by
      obtain ⟨hpi, hxi⟩ := hoe.price_pos_and_flow_pos h hzs hpos i
      have heff_R : latency i (x i) + p i = R := hoe.2.1.effectiveCost_eq_R_of_sum_lt hlt hxi
      have hp_ge : x i * latencyDeriv i (x i) ≤ p i := hoe.mul_latencyDeriv_le_price h i
      have hp_le : p i ≤ x i * latencyDeriv i (x i) + 0 := by
        refine le_mul_deriv_add_of_forall_pos_add (h.hasDerivAt i (x i) hxi.le)
          fun ε η hε hη => ?_
        obtain ⟨δ, hδ0, hδη, hδ_sum, hlat_lt_R⟩ :=
          h.exists_step_lt i hxi.le (sub_pos.mpr hlt) (by linarith : latency i (x i) < R) hη
        let x' : Link → ℝ := Function.update x i (x i + δ)
        let p' : Link → ℝ := Function.update p i (R - latency i (x i + δ))
        have hp'0 : ∀ k, 0 ≤ p' k := fun k => by
          simp only [p', Function.update_apply]; split_ifs <;> linarith [hoe.1 k]
        have hp'comp : ∀ q, owner q ≠ owner i → p' q = p q := fun q hq =>
          Function.update_of_ne (by rintro rfl; exact hq rfl) _ _
        have hcost_R : ∀ k, latency k (x' k) + p' k = R := fun k => by
          rcases eq_or_ne k i with rfl | hki
          · simp [x', p']
          simp only [x', p', Function.update_of_ne hki]
          exact hoe.2.1.effectiveCost_eq_R_of_sum_lt hlt (hoe.price_pos_and_flow_pos h hzs hpos k).2
        have hbest := hoe.2.2 (owner i) p' x' hp'0 hp'comp
          (isPricedWardrop_of_effectiveCost_eq
            (isFeasiblePricedFlow_update_add hoe.2.1.1 hδ0.le (by linarith)) hcost_R le_rfl
            fun h => (lt_irrefl _ h).elim)
        simp only [providerProfit] at hbest
        rw [sum_filter_eq_add_erase (fun k => owner k = owner i) rfl
            (fun m => p' m * x' m) (fun m => p m * x m) (fun m _ hmi => by simp [p', x', hmi]),
          sum_filter_eq_add_erase (fun k => owner k = owner i) rfl
            (fun m => p m * x m) (fun m => p m * x m) (fun _ _ _ => rfl)] at hbest
        simp only [p', x', Function.update_self] at hbest
        exact ⟨δ, hδ0, hδη, le_div_mul_add_of_mul_le hδ0 hε.le (by nlinarith)⟩
      linarith
    rw [h.isSocialOptimum_iff_kkt]
    exact ⟨hoe.2.1.1, 0, le_rfl, zero_mul _, fun i => (hmarg_zero i).le, fun i _ => hmarg_zero i⟩
  · push Not at hpos
    exact hoe.isSocialOptimum_of_forall_mul_eq_zero h fun i =>
      le_antisymm (hpos i) (mul_nonneg (hoe.1 i) (hoe.2.1.1.1 i))

/-- **Intra-portfolio marginal-cost equalization**: at any positive-revenue Oligopoly Equilibrium
satisfying `ZeroLatencySingleton`, any two links `i` and `j` owned by the same provider equalize
marginal social cost `latency i (x i) + x i * latencyDeriv i (x i)`. -/
theorem IsOligopolyEquilibrium.marginalCost_eq_of_owner_eq {d R : ℝ}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    {owner : Link → Provider} {p x : Link → ℝ}
    (hoe : IsOligopolyEquilibrium d R latency owner p x)
    (hzs : ZeroLatencySingleton latency owner x)
    (hpos : ∃ i₀, 0 < p i₀ * x i₀) {i j : Link} (hij_own : owner i = owner j) :
    latency i (x i) + x i * latencyDeriv i (x i) =
      latency j (x j) + x j * latencyDeriv j (x j) := by
  classical
  have hle : ∀ a b : Link, owner a = owner b →
      latency b (x b) + x b * latencyDeriv b (x b) ≤
        latency a (x a) + x a * latencyDeriv a (x a) := by
    intro a b hab
    by_cases heq : a = b
    · subst heq; exact le_rfl
    obtain ⟨hpa, hxa⟩ := hoe.price_pos_and_flow_pos h hzs hpos a
    obtain ⟨hpb, hxb⟩ := hoe.price_pos_and_flow_pos h hzs hpos b
    let K : ℝ := latency a (x a) + p a
    have hKb : latency b (x b) + p b = K := hoe.2.1.effectiveCost_eq_of_pos hxb hxa
    have hKR : K ≤ R := hoe.2.1.2.2.1 a hxa
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp
      ((h.hasDerivAt a (x a) hxa.le).continuousAt.eventually (eventually_lt_nhds
        (by linarith : latency a (x a) < K)))
    let g : ℝ → ℝ := fun t =>
      -((K - latency a (x a + t)) * (x a + t) + (K - latency b (x b - t)) * (x b - t))
    have hg_deriv : HasDerivAt g
        ((latency a (x a) + x a * latencyDeriv a (x a)) -
          (latency b (x b) + x b * latencyDeriv b (x b))) 0 := by
      have hrev : ∀ k : Link, HasDerivAt (fun u => (K - latency k u) * u)
          (K - latency k (x k) - x k * latencyDeriv k (x k)) (x k) := fun k => by
        have hsub : HasDerivAt (fun u => K - latency k u) (0 - latencyDeriv k (x k)) (x k) :=
          (hasDerivAt_const (x k) K).sub (h.hasDerivAt k (x k) (hoe.2.1.1.1 k))
        convert hsub.mul (hasDerivAt_id' (x k)) using 1
        ring
      convert ((HasDerivAt.comp_const_add (x a) 0 (by simpa using hrev a)).add
        (HasDerivAt.comp_const_sub (x b) 0 (by simpa using hrev b))).neg using 1
      ring
    have h0 : 0 ≤ (latency a (x a) + x a * latencyDeriv a (x a)) -
        (latency b (x b) + x b * latencyDeriv b (x b)) := by
      refine nonneg_of_hasDerivAt_of_forall_pos (lt_min hη hxb) hg_deriv fun t ht0 htm => ?_
      have htxb : t < x b := htm.trans_le (min_le_right _ _)
      have hlat_a_lt : latency a (x a + t) < K := by
        refine hball ?_
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos ht0]
        exact htm.trans_le (min_le_left _ _)
      have hlat_b_le : latency b (x b - t) ≤ latency b (x b) :=
        h.latency_le b (by linarith) (by linarith)
      let x' : Link → ℝ := Function.update (Function.update x b (x b - t)) a (x a + t)
      let p' : Link → ℝ :=
        Function.update (Function.update p b (K - latency b (x b - t))) a (K - latency a (x a + t))
      have hp'0 : ∀ k, 0 ≤ p' k := fun k => by
        simp only [p', Function.update_apply]; split_ifs <;> linarith [hoe.1 k]
      have hp'comp : ∀ q, owner q ≠ owner a → p' q = p q := fun q hq => by
        have hqa : q ≠ a := fun h => hq (h ▸ rfl)
        have hqb : q ≠ b := fun h => hq (h ▸ hab.symm)
        simp [p', hqa, hqb]
      have hx'sum : ∑ k, x' k = ∑ k, x k := sum_update_sub_add_eq x (Ne.symm heq) t
      have hcost_K : ∀ k, latency k (x' k) + p' k = K := fun k => by
        rcases eq_or_ne k a with rfl | hka
        · simp [x', p']
        rcases eq_or_ne k b with rfl | hkb
        · simp [x', p', hka]
        simp only [x', p', Function.update_of_ne hka, Function.update_of_ne hkb]
        exact hoe.2.1.effectiveCost_eq_of_pos (hoe.price_pos_and_flow_pos h hzs hpos k).2 hxa
      have hbest := hoe.2.2 (owner a) p' x' hp'0 hp'comp
        (isPricedWardrop_of_effectiveCost_eq
          ⟨nonneg_update_sub_add hoe.2.1.1.1 ht0.le htxb.le, hx'sum.trans_le hoe.2.1.1.2⟩
          hcost_K hKR fun hK => hx'sum.trans (hoe.2.1.2.2.2 ⟨a, hK⟩))
      have hdiff : providerProfit owner (owner a) p' x' - providerProfit owner (owner a) p x =
          (K - latency a (x a + t)) * (x a + t) - p a * x a +
            ((K - latency b (x b - t)) * (x b - t) - p b * x b) := by
        have ha_mem : a ∈ Finset.univ.filter (fun k => owner k = owner a) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
        have hb_mem : b ∈ Finset.univ.filter (fun k => owner k = owner a) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.symm⟩
        rw [providerProfit, providerProfit, ← Finset.sum_sub_distrib, Finset.sum_eq_add_of_mem a b
          ha_mem hb_mem heq fun k _ hk => by simp [x', p', hk.1, hk.2]]
        simp [x', p', Ne.symm heq]
      simp only [g, add_zero, sub_zero, neg_le_neg_iff]
      rw [show K - latency a (x a) = p a by simp [K], show K - latency b (x b) = p b by linarith]
      linarith
    linarith
  exact le_antisymm (hle j i hij_own.symm) (hle i j hij_own)

/-- **Zero-derivative competitor markup bound**: if full demand `d` is routed and some competitor
link `q` (`owner q ≠ owner i`) has `latencyDeriv q (x q) = 0`, then `p i = x i * latencyDeriv i
(x i)`. -/
theorem IsOligopolyEquilibrium.price_eq_mul_deriv_of_comp_deriv_zero {d R : ℝ}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    {owner : Link → Provider} {p x : Link → ℝ}
    (hoe : IsOligopolyEquilibrium d R latency owner p x)
    (hzs : ZeroLatencySingleton latency owner x)
    (hpos : ∃ i₀, 0 < p i₀ * x i₀) {i q : Link}
    (hq_comp : owner q ≠ owner i) (hq_deriv : latencyDeriv q (x q) = 0) :
    p i = x i * latencyDeriv i (x i) := by
  classical
  refine le_antisymm ?_ (hoe.mul_latencyDeriv_le_price h i)
  obtain ⟨hpi, hxi⟩ := hoe.price_pos_and_flow_pos h hzs hpos i
  obtain ⟨hpq, hxq⟩ := hoe.price_pos_and_flow_pos h hzs hpos q
  have hqi : q ≠ i := fun heq => hq_comp (heq ▸ rfl)
  have hlat_q0 : latency q (x q) = 0 :=
    (h.latency_eq_zero_iff_deriv_eq_zero q hxq).mpr hq_deriv
  let K : ℝ := latency i (x i) + p i
  have hKq : latency q (x q) + p q = K := hoe.2.1.effectiveCost_eq_of_pos hxq hxi
  have hKR : K ≤ R := hoe.2.1.2.2.1 i hxi
  have hp_le : p i ≤ x i * latencyDeriv i (x i) + 0 := by
    refine le_mul_deriv_add_of_forall_pos_add (h.hasDerivAt i (x i) hxi.le)
      fun ε η hε hη => ?_
    obtain ⟨δ, hδ0, hδη, hδxq, hlat_i_lt, hlat_q_sub⟩ :=
      h.exists_zero_swap_step (K := K) i hxi.le hxq hlat_q0 (by simp only [K]; linarith) hη
    let x' : Link → ℝ := Function.update (Function.update x q (x q - δ)) i (x i + δ)
    let p' : Link → ℝ := Function.update p i (K - latency i (x i + δ))
    have hp'0 : ∀ k, 0 ≤ p' k := fun k => by
      simp only [p', Function.update_apply]; split_ifs <;> linarith [hoe.1 k]
    have hp'comp : ∀ r, owner r ≠ owner i → p' r = p r := fun r hr =>
      Function.update_of_ne (by rintro rfl; exact hr rfl) _ _
    have hx'sum : ∑ k, x' k = ∑ k, x k := sum_update_sub_add_eq x hqi δ
    have hcost_K : ∀ k, latency k (x' k) + p' k = K := fun k => by
      rcases eq_or_ne k i with rfl | hki
      · simp [x', p']
      rcases eq_or_ne k q with rfl | hkq
      · simp only [x', p', Function.update_of_ne hqi, Function.update_self, hlat_q_sub]
        linarith
      simp only [x', p', Function.update_of_ne hki, Function.update_of_ne hkq]
      exact hoe.2.1.effectiveCost_eq_of_pos (hoe.price_pos_and_flow_pos h hzs hpos k).2 hxi
    have hbest := hoe.2.2 (owner i) p' x' hp'0 hp'comp
      (isPricedWardrop_of_effectiveCost_eq
        ⟨nonneg_update_sub_add hoe.2.1.1.1 hδ0.le hδxq.le, hx'sum.trans_le hoe.2.1.1.2⟩
        hcost_K hKR fun hK => hx'sum.trans (hoe.2.1.2.2.2 ⟨i, hK⟩))
    simp only [providerProfit] at hbest
    rw [sum_filter_eq_add_erase (fun k => owner k = owner i) rfl
        (fun m => p' m * x' m) (fun m => p m * x m)
        (fun m hm_own hmi => by
          have hmq : m ≠ q := fun heq => hq_comp (heq ▸ hm_own)
          simp [p', x', hmi, hmq]),
      sum_filter_eq_add_erase (fun k => owner k = owner i) rfl
        (fun m => p m * x m) (fun m => p m * x m) (fun _ _ _ => rfl)] at hbest
    simp only [p', x', Function.update_self, K] at hbest
    exact ⟨δ, hδ0, hδη, le_div_mul_add_of_mul_le hδ0 hε.le (by nlinarith)⟩
  linarith

/-- Shared portfolio-profit inequality under a signed flow redistribution `sStep` across
competitor links `owner q ≠ owner i` that shifts the uniform effective cost `cStar` by `δc`. -/
private theorem IsOligopolyEquilibrium.profit_flowShift_bound {d R : ℝ}
    {latency : Link → ℝ → ℝ} {owner : Link → Provider} {p x : Link → ℝ}
    (hoe : IsOligopolyEquilibrium d R latency owner p x)
    (hsum_d : ∑ k, x k = d) {i : Link}
    (heff : ∀ k, latency k (x k) + p k = latency i (x i) + p i)
    (δc : ℝ) (sStep : Link → ℝ)
    (hi_le : ∑ q with owner q ≠ owner i, sStep q ≤ x i)
    (hcomp_nn : ∀ q, owner q ≠ owner i → 0 ≤ x q + sStep q)
    (hcomp_lat : ∀ q, owner q ≠ owner i → latency q (x q + sStep q) - latency q (x q) = δc)
    (hcR : latency i (x i) + p i + δc ≤ R)
    (hpi' : 0 ≤ latency i (x i) + p i + δc -
      latency i (x i - ∑ q with owner q ≠ owner i, sStep q))
    (hp_own : ∀ m, owner m = owner i → m ≠ i → 0 ≤ p m + δc) :
    δc * (∑ m with owner m = owner i, x m) +
      (latency i (x i) - latency i (x i - ∑ q with owner q ≠ owner i, sStep q)) *
        (x i - ∑ q with owner q ≠ owner i, sStep q) ≤
      (p i + δc) * ∑ q with owner q ≠ owner i, sStep q := by
  classical
  let ownSet : Finset Link := Finset.univ.filter fun m => owner m = owner i
  let compSet : Finset Link := Finset.univ.filter fun q => owner q ≠ owner i
  let Δs : ℝ := ∑ q ∈ compSet, sStep q
  let cStar : ℝ := latency i (x i) + p i
  let x' : Link → ℝ := flowShift i compSet sStep x
  let p' : Link → ℝ := fun k =>
    if k = i then cStar + δc - latency i (x i - Δs)
    else if owner k = owner i then p k + δc
    else p k
  have hi_not_comp : i ∉ compSet := fun hc => (Finset.mem_filter.mp hc).2 rfl
  have hp'0 : ∀ k, 0 ≤ p' k := fun k => by
    by_cases hki : k = i
    · subst hki; simpa [p', cStar, Δs, compSet] using hpi'
    · by_cases hko : owner k = owner i
      · simp only [p', hki, hko, ↓reduceIte]; exact hp_own k hko hki
      · simp only [p', hki, hko, ↓reduceIte]; exact hoe.1 k
  have hp'comp : ∀ q, owner q ≠ owner i → p' q = p q := fun q hq => by
    have hqi : q ≠ i := fun heq => hq (heq ▸ rfl)
    simp [p', hqi, hq]
  have hx'sum : ∑ k, x' k = d := (sum_flowShift_eq hi_not_comp sStep x).trans hsum_d
  have hcost_eq : ∀ k, latency k (x' k) + p' k = cStar + δc := fun k => by
    by_cases hki : k = i
    · subst hki; simp [x', flowShift, Δs, p']
    · by_cases hko : owner k = owner i
      · have hkc : k ∉ compSet := fun hc => (Finset.mem_filter.mp hc).2 hko
        simp only [x', flowShift, p', hki, hkc, hko, ↓reduceIte]
        linarith [heff k]
      · have hkc : k ∈ compSet := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hko⟩
        simp only [x', flowShift, p', hki, hkc, hko, ↓reduceIte]
        linarith [heff k, hcomp_lat k hko]
  have hbest := hoe.2.2 (owner i) p' x' hp'0 hp'comp
    (isPricedWardrop_of_effectiveCost_eq ⟨nonneg_flowShift hoe.2.1.1.1 hi_le
      (fun q hq => hcomp_nn q (Finset.mem_filter.mp hq).2), hx'sum.le⟩ hcost_eq hcR
      fun _ => hx'sum)
  simp only [providerProfit] at hbest
  have hi_mem : i ∈ ownSet := Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩
  change ∑ m ∈ ownSet, p' m * x' m ≤ ∑ m ∈ ownSet, p m * x m at hbest
  rw [← Finset.add_sum_erase _ _ hi_mem] at hbest
  conv_rhs at hbest => rw [← Finset.add_sum_erase _ _ hi_mem]
  have hrest : ∑ m ∈ ownSet.erase i, p' m * x' m =
      (∑ m ∈ ownSet.erase i, p m * x m) + δc * ∑ m ∈ ownSet.erase i, x m := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmi : m ≠ i := (Finset.mem_erase.mp hm).1
    have hmo : owner m = owner i := (Finset.mem_filter.mp (Finset.mem_erase.mp hm).2).2
    have hmc : m ∉ compSet := fun hc => (Finset.mem_filter.mp hc).2 hmo
    simp only [p', x', flowShift, hmi, hmo, hmc, ↓reduceIte]
    ring
  have hi_prod : p' i * x' i =
      p i * x i + δc * x i - (p i + δc) * Δs +
        (latency i (x i) - latency i (x i - Δs)) * (x i - Δs) := by
    simp only [p', x', flowShift, Δs, ↓reduceIte, cStar]
    ring
  have hXs_split : δc * ∑ m ∈ ownSet, x m =
      δc * x i + δc * ∑ m ∈ ownSet.erase i, x m := by
    rw [← Finset.add_sum_erase _ _ hi_mem, mul_add]
  rw [hrest, hi_prod] at hbest
  change δc * ∑ m ∈ ownSet, x m +
      (latency i (x i) - latency i (x i - Δs)) * (x i - Δs) ≤ (p i + δc) * Δs
  linarith

/-- **Positive-derivative competitor markup upper bound**: when every competitor link `q`
(`owner q ≠ owner i`) has `0 < latencyDeriv q (x q)` and at least one competitor link exists,
`p i ≤ x i * latencyDeriv i (x i) + (∑ m with owner m = owner i, x m) /
(∑ q with owner q ≠ owner i, (latencyDeriv q (x q))⁻¹)`. -/
theorem IsOligopolyEquilibrium.price_le_mul_deriv_add_markup {d R : ℝ}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    {owner : Link → Provider} {p x : Link → ℝ}
    (hoe : IsOligopolyEquilibrium d R latency owner p x)
    (hzs : ZeroLatencySingleton latency owner x)
    (hpos : ∃ i₀, 0 < p i₀ * x i₀) (hsum : ∑ k, x k = d) {i : Link}
    (hcomp_ne : ∃ q, owner q ≠ owner i)
    (hcomp_pos : ∀ q, owner q ≠ owner i → 0 < latencyDeriv q (x q)) :
    p i ≤ x i * latencyDeriv i (x i) +
      (∑ m with owner m = owner i, x m) /
        (∑ q with owner q ≠ owner i, (latencyDeriv q (x q))⁻¹) := by
  classical
  let s := owner i
  let ownSet : Finset Link := Finset.univ.filter fun m => owner m = s
  let compSet : Finset Link := Finset.univ.filter fun q => owner q ≠ s
  obtain ⟨q₀, hq₀_comp⟩ := hcomp_ne
  have hcomp_nonempty : compSet.Nonempty :=
    ⟨q₀, Finset.mem_filter.mpr ⟨Finset.mem_univ q₀, hq₀_comp⟩⟩
  have hown_nonempty : ownSet.Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩
  obtain ⟨hpi, hxi⟩ := hoe.price_pos_and_flow_pos h hzs hpos i
  let cStar : ℝ := latency i (x i) + p i
  have hcR : cStar ≤ R := hoe.2.1.2.2.1 i hxi
  let Xs : ℝ := ∑ m ∈ ownSet, x m
  let Sinv : ℝ := ∑ q ∈ compSet, (latencyDeriv q (x q))⁻¹
  have hXs_pos : 0 < Xs :=
    hxi.trans_le (Finset.single_le_sum (fun m _ => hoe.2.1.1.1 m)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩))
  have hSinv_pos : 0 < Sinv :=
    (inv_pos.mpr (hcomp_pos q₀ hq₀_comp)).trans_le
      (Finset.single_le_sum (fun q hq => inv_nonneg.mpr
        (hcomp_pos q (Finset.mem_filter.mp hq).2).le)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ q₀, hq₀_comp⟩))
  refine le_mul_deriv_add_of_forall_pos_add (h.hasDerivAt i (x i) hxi.le)
    fun ε η hε hη => ?_
  -- Continuity of latency i at x i ensures latency i (x i + u) - latency i (x i) < p i / 2
  have hcont_i : ContinuousAt (latency i) (x i) := (h.hasDerivAt i (x i) hxi.le).continuousAt
  have hev_i : ∀ᶠ u in nhds (x i), latency i u - latency i (x i) < p i / 2 :=
    (hcont_i.sub continuousAt_const).eventually
      (eventually_lt_nhds (show latency i (x i) - latency i (x i) < p i / 2 by
        linarith [half_pos hpi]))
  rw [Metric.eventually_nhds_iff] at hev_i
  obtain ⟨η₁, hη₁, hball_i⟩ := hev_i
  have hcard_pos : 0 < (compSet.card : ℝ) := Nat.cast_pos.mpr hcomp_nonempty.card_pos
  let rStep : Link → ℝ := fun q => min (x q / 2) (min η η₁ / (2 * compSet.card))
  have hrStep_pos : ∀ q ∈ compSet, 0 < rStep q := fun q _ =>
    lt_min (half_pos (hoe.price_pos_and_flow_pos h hzs hpos q).2)
      (div_pos (lt_min hη hη₁) (by positivity))
  have hrStep_lt_x : ∀ q ∈ compSet, rStep q < x q := fun q _ =>
    (min_le_left _ _).trans_lt (half_lt_self (hoe.price_pos_and_flow_pos h hzs hpos q).2)
  have hlat_q_pos : ∀ q ∈ compSet, 0 < latency q (x q) := fun q hq => by
    have hxq := (hoe.price_pos_and_flow_pos h hzs hpos q).2
    have hdq := hcomp_pos q (Finset.mem_filter.mp hq).2
    rcases (h.latency_nonneg q hxq.le).eq_or_lt with hz | hp
    · exact False.elim (hdq.ne' ((h.latency_eq_zero_iff_deriv_eq_zero q hxq).mp hz.symm))
    · exact hp
  let dropMin : ℝ :=
    compSet.inf' hcomp_nonempty fun q => latency q (x q) - latency q (x q - rStep q)
  have hdrop_pos : 0 < dropMin := by
    rw [Finset.lt_inf'_iff]
    intro q hq
    have hlt := h.latency_sub_lt_of_pos q (hrStep_pos q hq) (hrStep_lt_x q hq) (hlat_q_pos q hq)
    linarith
  let pOwnMin : ℝ := ownSet.inf' hown_nonempty p
  have hpOwn_pos : 0 < pOwnMin := by
    rw [Finset.lt_inf'_iff]
    intro m _
    exact (hoe.price_pos_and_flow_pos h hzs hpos m).1
  let μ : ℝ := min (min (dropMin / 2) (pOwnMin / 2)) (min (p i / 4) (ε / 2))
  have hμ0 : 0 < μ :=
    lt_min (lt_min (half_pos hdrop_pos) (half_pos hpOwn_pos))
      (lt_min (by positivity) (half_pos hε))
  have hμ_lt_drop : μ < dropMin :=
    ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hdrop_pos)
  have hμ_lt_pOwn : ∀ m ∈ ownSet, μ < p m := fun m hm =>
    (((min_le_left _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hpOwn_pos)).trans_le
      (Finset.inf'_le p hm)
  have hμ_le_pi4 : μ ≤ p i / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hμ_lt_ε : μ < ε :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hε)
  have hex_dq : ∀ q ∈ compSet, ∃ t, 0 < t ∧ t < rStep q ∧
      latency q (x q) - latency q (x q - t) = μ := by
    intro q hq
    have hxq := (hoe.price_pos_and_flow_pos h hzs hpos q).2
    have hμ_lt_r : μ < latency q (x q) - latency q (x q - rStep q) :=
      hμ_lt_drop.trans_le (Finset.inf'_le _ hq)
    have hμ_lt_lq : μ < latency q (x q) := by
      linarith [h.latency_nonneg q (show 0 ≤ x q - rStep q by linarith [hrStep_lt_x q hq])]
    obtain ⟨t, ht0, _, hteq, htsmall⟩ := exists_pos_step_sub_eq
      (h.zero_at_zero q) (h.monotoneOn q) (h.continuousOn q) hxq hμ0 hμ_lt_lq
    exact ⟨t, ht0, htsmall (rStep q) (hrStep_pos q hq) (hrStep_lt_x q hq).le hμ_lt_r, hteq⟩
  choose! step hstep_pos hstep_lt hstep_eq using hex_dq
  let Δ : ℝ := ∑ q ∈ compSet, step q
  have hΔ0 : 0 < Δ := Finset.sum_pos hstep_pos hcomp_nonempty
  have hΔ_lt_min : Δ < min η η₁ := by
    have hsum_lt : Δ < ∑ _q ∈ compSet, (min η η₁ / (2 * compSet.card)) :=
      Finset.sum_lt_sum_of_nonempty hcomp_nonempty fun q hq =>
        (hstep_lt q hq).trans_le (min_le_right _ _)
    rw [Finset.sum_const, nsmul_eq_mul, mul_div_two_mul hcard_pos.ne'] at hsum_lt
    exact hsum_lt.trans (half_lt_self (lt_min hη hη₁))
  have hΔη : Δ < η := hΔ_lt_min.trans_le (min_le_left _ _)
  have hΔη₁ : Δ < η₁ := hΔ_lt_min.trans_le (min_le_right _ _)
  -- Convexity on each q ∈ compSet gives μ * (latencyDeriv q (x q))⁻¹ ≤ step q:
  have hΔ_ge : μ * Sinv ≤ Δ := by
    simp only [Sinv, Δ, Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    have hdq_pos : 0 < latencyDeriv q (x q) := hcomp_pos q (Finset.mem_filter.mp hq).2
    have hxq_pos : 0 < x q := (hoe.price_pos_and_flow_pos h hzs hpos q).2
    have hst_lt_x : step q < x q := (hstep_lt q hq).trans (hrStep_lt_x q hq)
    have hconv := h.add_deriv_mul_le q hxq_pos.le (show 0 ≤ x q - step q by linarith)
    have hdq_eq := hstep_eq q hq
    have hmul_le : μ ≤ latencyDeriv q (x q) * step q := by linarith
    rw [← div_eq_mul_inv, div_le_iff₀ hdq_pos]
    linarith
  have hlat_i_inc : latency i (x i + Δ) - latency i (x i) < p i / 2 := by
    refine hball_i ?_
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hΔ0]
    exact hΔη₁
  have hneg_sum : ∑ q ∈ compSet, (-step q) = -Δ := by simp [Δ, Finset.sum_neg_distrib]
  have hsub_neg : x i - -Δ = x i + Δ := sub_neg_eq_add (x i) Δ
  have hpΔ_raw := hoe.profit_flowShift_bound hsum
    (fun k => hoe.2.1.effectiveCost_eq_of_pos (hoe.price_pos_and_flow_pos h hzs hpos k).2 hxi)
    (-μ) (fun q => -step q)
    (by simp only [compSet] at hneg_sum; rw [hneg_sum]; linarith)
    (fun q hq => by
      have hqc : q ∈ compSet := Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩
      have hst := (hstep_lt q hqc).trans (hrStep_lt_x q hqc)
      linarith)
    (fun q hq => by
      have hqc : q ∈ compSet := Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩
      have hdq_eq := hstep_eq q hqc
      rw [← sub_eq_add_neg]
      linarith)
    (by linarith)
    (by
      simp only [compSet] at hneg_sum
      rw [hneg_sum, hsub_neg]
      linarith)
    (fun m hm _ => by
      have hmo : m ∈ ownSet := Finset.mem_filter.mpr ⟨Finset.mem_univ m, hm⟩
      linarith [hμ_lt_pOwn m hmo])
  simp only [compSet] at hneg_sum
  rw [hneg_sum, hsub_neg] at hpΔ_raw
  have hpΔ_le : p i * Δ ≤
      (latency i (x i + Δ) - latency i (x i)) * (x i + Δ) + μ * Xs + μ * Δ := by
    simp only [Xs, ownSet, s]
    linarith
  have hdiv_μ : (μ / Δ) * Xs ≤ Xs / Sinv := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hΔ0 hSinv_pos]
    calc μ * Xs * Sinv = (μ * Sinv) * Xs := by ring
      _ ≤ Δ * Xs := mul_le_mul_of_nonneg_right hΔ_ge hXs_pos.le
      _ = Xs * Δ := by ring
  refine ⟨Δ, hΔ0, hΔη, ?_⟩
  have hdiv_p : p i ≤ ((latency i (x i + Δ) - latency i (x i)) / Δ) * (x i + Δ) +
      (μ / Δ) * Xs + μ := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_add' _ _ _ hΔ0.ne',
      le_div_iff₀ hΔ0]
    linarith
  linarith

/-- **Explicit OE price formula** ([Acemoglu and Ozdaglar, Corollary 4.1,
p. 12][AcemogluOzdaglar2007MOR]; [Ozdaglar and Srikant, Section 22.2.4,
p. 583][OzdaglarSrikant2007]): at any positive-revenue Oligopoly Equilibrium satisfying
`ZeroLatencySingleton` with at least two active providers (`∃ q, owner q ≠ owner i`),
* if `latencyDeriv q (x q) = 0` for some `q` with `owner q ≠ owner i`, then
  `p i = x i * latencyDeriv i (x i)`;
* otherwise,
  `p i = min (R - latency i (x i)) (x i * latencyDeriv i (x i) +
    (∑ m with owner m = owner i, x m) / (∑ q with owner q ≠ owner i, (latencyDeriv q (x q))⁻¹))`. -/
theorem IsOligopolyEquilibrium.price_eq_min_markup {d R : ℝ}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    {owner : Link → Provider} {p x : Link → ℝ}
    (hoe : IsOligopolyEquilibrium d R latency owner p x)
    (hzs : ZeroLatencySingleton latency owner x)
    (hpos : ∃ i₀, 0 < p i₀ * x i₀) {i : Link}
    (hcomp_ne : ∃ q, owner q ≠ owner i)
    (hcomp_pos : ∀ q, owner q ≠ owner i → 0 < latencyDeriv q (x q)) :
    p i = min (R - latency i (x i))
      (x i * latencyDeriv i (x i) +
        (∑ m with owner m = owner i, x m) /
          (∑ q with owner q ≠ owner i, (latencyDeriv q (x q))⁻¹)) := by
  classical
  obtain ⟨hpi, hxi⟩ := hoe.price_pos_and_flow_pos h hzs hpos i
  let cStar : ℝ := latency i (x i) + p i
  have hcR : cStar ≤ R := hoe.2.1.2.2.1 i hxi
  rcases hcR.eq_or_lt with hc_eq_R | hc_lt_R
  · -- When cStar = R, p i = R - latency i (x i). Either ∑ x < d (so p i = x i * l'_i ≤ ...) or
    -- ∑ x = d (so price_le_mul_deriv_add_markup applies):
    have hpR : p i = R - latency i (x i) := by simp only [cStar] at hc_eq_R; linarith
    rcases hoe.2.1.1.2.lt_or_eq with hlt_d | hsum_d
    · obtain ⟨_, μ, hμ0, hcomp_μ, hle_μ, heq_μ⟩ :=
        h.isSocialOptimum_iff_kkt.mp (hoe.isSocialOptimum_of_sum_lt h hzs hlt_d)
      have hμ_zero : μ = 0 := (mul_eq_zero.mp hcomp_μ).resolve_right (by intro h0; linarith)
      have heq_i := heq_μ i hxi
      rw [hμ_zero] at heq_i
      have hdiv_nonneg : 0 ≤ (∑ m with owner m = owner i, x m) /
          (∑ q with owner q ≠ owner i, (latencyDeriv q (x q))⁻¹) :=
        div_nonneg (Finset.sum_nonneg fun m _ => hoe.2.1.1.1 m) (Finset.sum_nonneg fun q hq =>
          inv_nonneg.mpr (hcomp_pos q (Finset.mem_filter.mp hq).2).le)
      rw [hpR, min_eq_left (by linarith)]
    · have hub := hoe.price_le_mul_deriv_add_markup h hzs hpos hsum_d hcomp_ne hcomp_pos
      rw [hpR, min_eq_left (by linarith)]
  · -- When cStar < R, ∑ x = d; prove both ≤ and ≥ to get p i = x i * l'_i + Xs / Sinv:
    have hsum_d : ∑ k, x k = d := hoe.2.1.2.2.2 ⟨i, hc_lt_R⟩
    have hub := hoe.price_le_mul_deriv_add_markup h hzs hpos hsum_d hcomp_ne hcomp_pos
    have hp_lt_R : p i < R - latency i (x i) := by simp only [cStar] at hc_lt_R; linarith
    -- Prove reverse inequality x i * l'_i + Xs / Sinv ≤ p i by upward price perturbation cStar + μ:
    let s := owner i
    let ownSet : Finset Link := Finset.univ.filter fun m => owner m = s
    let compSet : Finset Link := Finset.univ.filter fun q => owner q ≠ s
    obtain ⟨q₀, hq₀_comp⟩ := hcomp_ne
    have hcomp_nonempty : compSet.Nonempty :=
      ⟨q₀, Finset.mem_filter.mpr ⟨Finset.mem_univ q₀, hq₀_comp⟩⟩
    let Xs : ℝ := ∑ m ∈ ownSet, x m
    let Sinv : ℝ := ∑ q ∈ compSet, (latencyDeriv q (x q))⁻¹
    have hXs_pos : 0 < Xs :=
      hxi.trans_le (Finset.single_le_sum (fun m _ => hoe.2.1.1.1 m)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩))
    have hSinv_pos : 0 < Sinv :=
      (inv_pos.mpr (hcomp_pos q₀ hq₀_comp)).trans_le
        (Finset.single_le_sum (fun q hq => inv_nonneg.mpr
          (hcomp_pos q (Finset.mem_filter.mp hq).2).le)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ q₀, hq₀_comp⟩))
    have hlb : x i * latencyDeriv i (x i) + Xs / Sinv ≤ p i := by
      -- Suffices: ∀ ε > 0, x i * l'_i ≤ p i - Xs / Sinv + ε, via mul_deriv_le_of_forall_pos_sub:
      by_contra hlt_lb
      push Not at hlt_lb
      let ε : ℝ := (x i * latencyDeriv i (x i) + Xs / Sinv - p i) / 2
      have hε : 0 < ε := by simp only [ε]; linarith
      have hm_le : x i * latencyDeriv i (x i) ≤ p i - Xs / Sinv + ε := by
        refine mul_deriv_le_of_forall_pos_sub hxi (h.hasDerivAt i (x i) hxi.le) fun η hη => ?_
        have hcard_pos : 0 < (compSet.card : ℝ) := Nat.cast_pos.mpr hcomp_nonempty.card_pos
        let rStep : ℝ := min 1 (min η (x i) / (2 * compSet.card))
        have hrStep_pos : 0 < rStep :=
          lt_min zero_lt_one (div_pos (lt_min hη hxi) (by positivity))
        let incMin : ℝ :=
          compSet.inf' hcomp_nonempty fun q => latency q (x q + rStep) - latency q (x q)
        have hinc_pos : 0 < incMin := by
          rw [Finset.lt_inf'_iff]
          intro q hq
          have hdq := hcomp_pos q (Finset.mem_filter.mp hq).2
          have hconv := h.add_deriv_mul_le q (hoe.2.1.1.1 q)
            (show 0 ≤ x q + rStep by linarith [hoe.2.1.1.1 q])
          have hpos_m : 0 < latencyDeriv q (x q) * rStep := mul_pos hdq hrStep_pos
          linarith
        let μ : ℝ := min (min ((R - cStar) / 2) (incMin / 2)) (ε / 2)
        have hμ0 : 0 < μ :=
          lt_min (lt_min (by linarith) (half_pos hinc_pos)) (half_pos hε)
        have hcμR : cStar + μ < R := by
          have h1 : μ ≤ (R - cStar) / 2 := (min_le_left _ _).trans (min_le_left _ _)
          linarith
        have hμ_lt_inc : μ < incMin :=
          ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hinc_pos)
        have hμ_lt_ε : μ < ε := (min_le_right _ _).trans_lt (half_lt_self hε)
        have hex_dq : ∀ q ∈ compSet, ∃ t, 0 < t ∧ t < rStep ∧
            latency q (x q + t) - latency q (x q) = μ := by
          intro q hq
          have hμ_lt_q : μ < latency q (x q + rStep) - latency q (x q) :=
            hμ_lt_inc.trans_le (Finset.inf'_le _ hq)
          have hr1 : rStep ≤ 1 := min_le_left _ _
          have hle1 : latency q (x q + rStep) ≤ latency q (x q + 1) :=
            h.latency_le q (by linarith [hoe.2.1.1.1 q]) (by linarith)
          obtain ⟨t, ht0, _, hteq, htsmall⟩ := exists_pos_step_add_eq
            (h.monotoneOn q) (h.continuousOn q) (hoe.2.1.1.1 q) hμ0 (by linarith)
          exact ⟨t, ht0, htsmall rStep hrStep_pos hμ_lt_q, hteq⟩
        choose! step hstep_pos hstep_lt hstep_eq using hex_dq
        let Δ : ℝ := ∑ q ∈ compSet, step q
        have hΔ0 : 0 < Δ := Finset.sum_pos hstep_pos hcomp_nonempty
        have hΔ_lt_min : Δ < min η (x i) := by
          have hsum_lt : Δ < ∑ _q ∈ compSet, rStep :=
            Finset.sum_lt_sum_of_nonempty hcomp_nonempty hstep_lt
          rw [Finset.sum_const, nsmul_eq_mul] at hsum_lt
          have hmul_r := mul_le_mul_of_nonneg_left
            (min_le_right _ _ : rStep ≤ min η (x i) / (2 * compSet.card)) hcard_pos.le
          rw [mul_div_two_mul hcard_pos.ne'] at hmul_r
          exact (hsum_lt.trans_le hmul_r).trans (half_lt_self (lt_min hη hxi))
        have hΔη : Δ < η := hΔ_lt_min.trans_le (min_le_left _ _)
        have hΔx : Δ < x i := hΔ_lt_min.trans_le (min_le_right _ _)
        -- Convexity at x q gives step q ≤ μ * (latencyDeriv q (x q))⁻¹, so Δ ≤ μ * Sinv:
        have hΔ_le : Δ ≤ μ * Sinv := by
          simp only [Δ, Sinv, Finset.mul_sum]
          refine Finset.sum_le_sum fun q hq => ?_
          have hdq_pos : 0 < latencyDeriv q (x q) := hcomp_pos q (Finset.mem_filter.mp hq).2
          have hconv := h.add_deriv_mul_le q (hoe.2.1.1.1 q)
            (show 0 ≤ x q + step q by linarith [hoe.2.1.1.1 q, hstep_pos q hq])
          have hdq_eq := hstep_eq q hq
          have hmul_ge : latencyDeriv q (x q) * step q ≤ μ := by linarith
          rw [← div_eq_mul_inv, le_div_iff₀ hdq_pos]
          linarith
        have hlat_i_le : latency i (x i - Δ) ≤ latency i (x i) :=
          h.latency_le i (by linarith) (by linarith)
        have hpΔ_raw := hoe.profit_flowShift_bound hsum_d
          (fun k => hoe.2.1.effectiveCost_eq_of_pos (hoe.price_pos_and_flow_pos h hzs hpos k).2 hxi)
          μ step hΔx.le
          (fun q hq => by
            have hqc : q ∈ compSet := Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩
            linarith [hoe.2.1.1.1 q, hstep_pos q hqc])
          (fun q hq => hstep_eq q (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩))
          hcμR.le
          (by change 0 ≤ latency i (x i) + p i + μ - latency i (x i - Δ); linarith)
          (fun m _ _ => by linarith [hoe.1 m])
        have hmul_le : (latency i (x i) - latency i (x i - Δ)) * (x i - Δ) ≤
            p i * Δ - μ * Xs + μ * Δ := by
          change μ * Xs + (latency i (x i) - latency i (x i - Δ)) * (x i - Δ) ≤
            (p i + μ) * Δ at hpΔ_raw
          linarith
        have hdiv_ge : Xs / Sinv ≤ (μ / Δ) * Xs := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hSinv_pos hΔ0]
          calc Xs * Δ ≤ Xs * (μ * Sinv) := mul_le_mul_of_nonneg_left hΔ_le hXs_pos.le
            _ = μ * Xs * Sinv := by ring
        refine ⟨Δ, hΔ0, hΔη, hΔx, ?_⟩
        have hdiv1 : ((latency i (x i) - latency i (x i - Δ)) / Δ) * (x i - Δ) ≤
            p i - (μ / Δ) * Xs + μ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hΔ0,
            show (p i - (μ / Δ) * Xs + μ) * Δ = p i * Δ - μ * Xs + μ * Δ by field_simp]
          exact hmul_le
        linarith
      simp only [ε] at hm_le
      linarith
    have heq_p : p i = x i * latencyDeriv i (x i) + Xs / Sinv := le_antisymm hub hlb
    rw [heq_p, min_eq_right (by linarith)]

end PriceCharacterization

section FiveSixthsBound

/-!
### Shared weak-duality quadratic envelope and proof of Theorem 22.3 (`5 / 6`)
-/

/-- Per-link weak-duality quadratic upper bound on `m * y - y * latency i y` at reference point
`x ≥ 0` with `l := latency i x`, `d_i := latencyDeriv i x`:
* `0` when `d_i = 0` (which requires `m = 0` when `m ≤ l + x * d_i`), and
* `m * ((x * d_i - l) / d_i) + max 0 (m - (x * d_i - l)) ^ 2 / (4 * d_i)` when `0 < d_i`. -/
private noncomputable def linkSurplusEnvelope (m l t di : ℝ) : ℝ :=
  if di = 0 then 0 else m * ((t - l) / di) + max 0 (m - (t - l)) ^ 2 / (4 * di)

private theorem linkSurplusEnvelope_ge {Link : Type*} {latency latencyDeriv : Link → ℝ → ℝ}
    (h : SmoothConvexLatencies latency latencyDeriv) (i : Link) {x y m : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hm0 : 0 ≤ m)
    (hm_le : m ≤ latency i x + x * latencyDeriv i x) :
    m * y - y * latency i y ≤
      linkSurplusEnvelope m (latency i x) (x * latencyDeriv i x) (latencyDeriv i x) := by
  rcases (h.latencyDeriv_nonneg i hx).eq_or_lt with hdi0 | hdi_pos
  · -- When latencyDeriv i x = 0, latency i x = 0 and m = 0:
    have hdi_z : latencyDeriv i x = 0 := hdi0.symm
    have hl0 : latency i x = 0 := le_antisymm
      ((h.latency_le_mul_deriv i hx).trans (by rw [hdi_z, mul_zero])) (h.latency_nonneg i hx)
    have hm_zero : m = 0 :=
      le_antisymm (by rw [hl0, hdi_z, mul_zero, add_zero] at hm_le; exact hm_le) hm0
    simp only [linkSurplusEnvelope, hdi_z, ↓reduceIte, hm_zero, zero_mul, zero_sub]
    linarith [mul_nonneg hy (h.latency_nonneg i hy)]
  · simp only [linkSurplusEnvelope, hdi_pos.ne', ↓reduceIte]
    let l := latency i x
    let di := latencyDeriv i x
    let t := x * di
    change m * y - y * latency i y ≤ m * ((t - l) / di) + max 0 (m - (t - l)) ^ 2 / (4 * di)
    have hl_nonneg : 0 ≤ l := h.latency_nonneg i hx
    have hl_le_t : l ≤ t := h.latency_le_mul_deriv i hx
    let a : ℝ := (t - l) / di
    have ha_nonneg : 0 ≤ a := div_nonneg (by linarith) hdi_pos.le
    have hda : di * a = t - l := mul_div_cancel₀ (t - l) hdi_pos.ne'
    rcases le_or_gt y a with hya | hay
    · have h1 : m * y - y * latency i y ≤ m * a := by
        have hyl : 0 ≤ y * latency i y := mul_nonneg hy (h.latency_nonneg i hy)
        have hmy : m * y ≤ m * a := mul_le_mul_of_nonneg_left hya hm0
        linarith
      have h2 : 0 ≤ max 0 (m - (t - l)) ^ 2 / (4 * di) := by positivity
      change m * y - y * latency i y ≤ m * a + max 0 (m - (t - l)) ^ 2 / (4 * di)
      linarith
    · let z : ℝ := y - a
      have hz_pos : 0 < z := sub_pos.mpr hay
      have htan := h.add_deriv_mul_le i hx hy
      have hlat_ge : di * z ≤ latency i y := by
        have hcalc : l + di * (y - x) = di * z := by
          simp only [z, t] at hda ⊢
          nlinarith
        linarith
      have hy_lat : y * (di * z) ≤ y * latency i y := mul_le_mul_of_nonneg_left hlat_ge hy
      have hy_eq : y = a + z := by simp [z]
      have hquad : m * y - y * (di * z) = m * a + ((m - (t - l)) * z - di * z ^ 2) := by
        rw [hy_eq]
        nlinarith [hda]
      have hmax_ge : m - (t - l) ≤ max 0 (m - (t - l)) := le_max_right _ _
      have hsq : (m - (t - l)) * z - di * z ^ 2 ≤ max 0 (m - (t - l)) ^ 2 / (4 * di) := by
        have hstep1 : (m - (t - l)) * z ≤ max 0 (m - (t - l)) * z :=
          mul_le_mul_of_nonneg_right hmax_ge hz_pos.le
        rw [le_div_iff₀ (by positivity : 0 < 4 * di)]
        have hcomp : max 0 (m - (t - l)) ^ 2 -
            ((max 0 (m - (t - l)) * z - di * z ^ 2) * (4 * di)) =
            (2 * di * z - max 0 (m - (t - l))) ^ 2 := by ring
        nlinarith [sq_nonneg (2 * di * z - max 0 (m - (t - l)))]
      change m * y - y * latency i y ≤ m * a + max 0 (m - (t - l)) ^ 2 / (4 * di)
      linarith

/-- At `m = l + x * di` (`0 ≤ l`), `linkSurplusEnvelope` evaluates identically to `x ^ 2 * di`. -/
private theorem linkSurplusEnvelope_at_min {x l di : ℝ} (hl0 : 0 ≤ l) :
    linkSurplusEnvelope (l + x * di) l (x * di) di = x ^ 2 * di := by
  by_cases hdi : di = 0
  · simp [linkSurplusEnvelope, hdi]
  · simp only [linkSurplusEnvelope, hdi, ↓reduceIte]
    have hmax : max 0 (l + x * di - (x * di - l)) = 2 * l := by
      rw [show l + x * di - (x * di - l) = 2 * l by ring, max_eq_right (by linarith)]
    rw [hmax]
    field_simp
    ring

/-- The quadratic envelope dominates the reference-point value `m * x - x * l` for `0 ≤ l` and
`0 < di`. -/
private theorem self_le_linkSurplusEnvelope {x l di m : ℝ} (hl0 : 0 ≤ l) (hdi : 0 < di) :
    m * x - x * l ≤ linkSurplusEnvelope m l (x * di) di := by
  simp only [linkSurplusEnvelope, hdi.ne', ↓reduceIte]
  rcases le_or_gt m (x * di - l) with hm_le | hm_gt
  · rw [max_eq_left (by linarith)]
    have hdiff : m * ((x * di - l) / di) + 0 ^ 2 / (4 * di) - (m * x - x * l) =
        l * (x * di - m) / di := by field_simp; ring
    have hnn : 0 ≤ l * (x * di - m) / di :=
      div_nonneg (mul_nonneg hl0 (by linarith)) hdi.le
    linarith
  · rw [max_eq_right (by linarith)]
    have hdiff : m * ((x * di - l) / di) + (m - (x * di - l)) ^ 2 / (4 * di) - (m * x - x * l) =
        (m - x * di - l) ^ 2 / (4 * di) := by field_simp; ring
    have hnn : 0 ≤ (m - x * di - l) ^ 2 / (4 * di) := div_nonneg (sq_nonneg _) (by positivity)
    linarith

private theorem linkSurplusEnvelope_at_min_five_sixths {x l di : ℝ} (_hx : 0 ≤ x) (hl0 : 0 ≤ l)
    (hdi : 0 ≤ di) :
    5 * linkSurplusEnvelope (l + x * di) l (x * di) di ≤
      6 * ((l + x * di) * x - x * l) := by
  rw [linkSurplusEnvelope_at_min hl0]
  nlinarith [mul_nonneg (sq_nonneg x) hdi]

/-- Key per-competitor polynomial inequality for **Theorem 22.3 (`5 / 6`)**: for every link with
`0 ≤ l ≤ t = x * d_q`, `0 < d_q`, `0 ≤ m ≤ l + t ≤ m + dU`, we have
`5 * linkSurplusEnvelope m l t d_q ≤ 6 * (m * x - x * l) + dU ^ 2 / d_q + dU * x`. -/
private theorem linkSurplusEnvelope_competitor_five_sixths {x l di m dU : ℝ}
    (hx : 0 ≤ x) (hl0 : 0 ≤ l) (hdi_pos : 0 < di) (hlt : l ≤ x * di)
    (hm0 : 0 ≤ m) (hmlt : m ≤ l + x * di) (hdU_ge : l + x * di - m ≤ dU) :
    5 * linkSurplusEnvelope m l (x * di) di ≤
      6 * (m * x - x * l) + dU ^ 2 / di + dU * x := by
  let t : ℝ := x * di
  have ht0 : 0 ≤ t := hl0.trans hlt
  have hdU0 : 0 ≤ dU := by linarith
  let dU₀ : ℝ := l + t - m
  have hdU₀_nonneg : 0 ≤ dU₀ := by simp only [dU₀]; linarith
  have hdU_sq : dU₀ ^ 2 / di ≤ dU ^ 2 / di :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hdU₀_nonneg hdU_ge 2) hdi_pos.le
  have hdU_x : dU₀ * x ≤ dU * x := mul_le_mul_of_nonneg_right hdU_ge hx
  suffices h0 : 5 * linkSurplusEnvelope m l t di ≤
      6 * (m * x - x * l) + dU₀ ^ 2 / di + dU₀ * x by
    linarith
  simp only [linkSurplusEnvelope, hdi_pos.ne', ↓reduceIte]
  rcases le_or_gt m (t - l) with hm_le_tl | hm_gt_tl
  · -- Branch 1: m ≤ t - l, so max 0 (m - (t - l)) = 0:
    have hmax0 : max 0 (m - (t - l)) = 0 := max_eq_left (by linarith)
    rw [hmax0]
    have hx_eq : x = t / di := by simp only [t]; field_simp
    rw [hx_eq]
    have hnum_pos : 0 ≤ 6 * (m * (t / di) - t / di * l) + dU₀ ^ 2 / di + dU₀ * (t / di) -
        5 * (m * ((t - l) / di) + 0 ^ 2 / (4 * di)) := by
      have hrewrite : 6 * (m * (t / di) - t / di * l) + dU₀ ^ 2 / di + dU₀ * (t / di) -
          5 * (m * ((t - l) / di) + 0 ^ 2 / (4 * di)) =
          ((t - l - m) ^ 2 + (t - l) ^ 2 + l * (t - l + m)) / di := by
        simp only [dU₀]
        field_simp
        ring
      rw [hrewrite]
      refine div_nonneg ?_ hdi_pos.le
      have h1 : 0 ≤ (t - l - m) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ (t - l) ^ 2 := sq_nonneg _
      have h3 : 0 ≤ l * (t - l + m) := mul_nonneg hl0 (by linarith)
      linarith
    linarith
  · -- Branch 2: m > t - l, so max 0 (m - (t - l)) = m - (t - l):
    have hmax_pos : max 0 (m - (t - l)) = m - (t - l) := max_eq_right (by linarith)
    rw [hmax_pos]
    have hx_eq : x = t / di := by simp only [t]; field_simp
    rw [hx_eq]
    have hrewrite : 6 * (m * (t / di) - t / di * l) + dU₀ ^ 2 / di + dU₀ * (t / di) -
        5 * (m * ((t - l) / di) + (m - (t - l)) ^ 2 / (4 * di)) =
        ((m + t - l) * (3 * t + l - m)) / (4 * di) := by
      simp only [dU₀]
      field_simp
      ring
    have hpos_rhs : 0 ≤ ((m + t - l) * (3 * t + l - m)) / (4 * di) :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
    linarith

/-- **Acemoglu–Ozdaglar `5 / 6` Oligopoly Efficiency Bound** ([Ozdaglar and Srikant, Theorem 22.3,
p. 584][OzdaglarSrikant2007]; [Acemoglu and Ozdaglar, Theorem 5.2,
p. 20][AcemogluOzdaglar2007MOR]): for any multi-provider parallel-link network with smooth convex
latencies (`latency i 0 = 0`) and any pure-strategy Oligopoly Equilibrium `(p, x)` satisfying
`ZeroLatencySingleton`, `5 * socialSurplus R latency y ≤ 6 * socialSurplus R latency x` for every
feasible flow `y`. -/
theorem oligopoly_surplus_five_sixths {Link Provider : Type*} [Fintype Link] [DecidableEq Provider]
    {d R : ℝ} {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    {owner : Link → Provider} {p x y : Link → ℝ}
    (hoe : IsOligopolyEquilibrium d R latency owner p x)
    (hzs : ZeroLatencySingleton latency owner x)
    (hy : IsFeasiblePricedFlow d y) :
    5 * socialSurplus R latency y ≤ 6 * socialSurplus R latency x := by
  classical
  -- Edge case 1: empty Link
  by_cases hne : Nonempty Link
  · have of_opt (hopt : IsSocialOptimum d R latency x) :
        5 * socialSurplus R latency y ≤ 6 * socialSurplus R latency x := by
      linarith [hopt.2 y hy, hoe.2.1.socialSurplus_nonneg hoe.1]
    -- Edge case 2: ∀ i, p i * x i = 0 (Lemma 5.1)
    by_cases hpos : ∃ i₀, 0 < p i₀ * x i₀
    · -- Edge case 3: ∑ x < d (Lemma 5.2(ii))
      rcases hoe.2.1.1.2.lt_or_eq with hlt_d | hsum_d
      · exact of_opt (hoe.isSocialOptimum_of_sum_lt h hzs hlt_d)
      · -- Full demand ∑ k, x k = d with interior positivity on every link:
        have hall_pos := hoe.price_pos_and_flow_pos h hzs hpos
        -- Choose i₀ minimizing mc k := latency k (x k) + x k * latencyDeriv k (x k):
        let mc : Link → ℝ := fun k => latency k (x k) + x k * latencyDeriv k (x k)
        obtain ⟨i₀, _, hi₀_min⟩ := Finset.exists_min_image Finset.univ mc Finset.univ_nonempty
        let m : ℝ := mc i₀
        let s₀ : Provider := owner i₀
        let cStar : ℝ := latency i₀ (x i₀) + p i₀
        have hcR : cStar ≤ R := hoe.2.1.2.2.1 i₀ (hall_pos i₀).2
        have hm0 : 0 ≤ m := add_nonneg (h.latency_nonneg i₀ (hoe.2.1.1.1 i₀))
          (mul_nonneg (hoe.2.1.1.1 i₀) (h.latencyDeriv_nonneg i₀ (hoe.2.1.1.1 i₀)))
        have heff_all : ∀ k, latency k (x k) + p k = cStar := fun k =>
          hoe.2.1.effectiveCost_eq_of_pos (hall_pos k).2 (hall_pos i₀).2
        have hmc_le_c : ∀ k, mc k ≤ cStar := fun k => by
          rw [← heff_all k]
          linarith [hoe.mul_latencyDeriv_le_price h k]
        let dU : ℝ := cStar - m
        have hdU0 : 0 ≤ dU := sub_nonneg.mpr (hmc_le_c i₀)
        -- Reduce from R to cStar: (R - cStar) * ∑ y ≤ (R - cStar) * d = (R - cStar) * ∑ x:
        have hd_pos : 0 < d := by
          rw [← hsum_d]
          exact (hall_pos i₀).2.trans_le
            (Finset.single_le_sum (fun k _ => hoe.2.1.1.1 k) (Finset.mem_univ i₀))
        have hy_shift : socialSurplus R latency y ≤
            socialSurplus cStar latency y + (R - cStar) * d := by
          have hid : socialSurplus R latency y =
              socialSurplus cStar latency y + (R - cStar) * ∑ k, y k := by
            simp only [socialSurplus, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
          rw [hid]
          linarith [mul_le_mul_of_nonneg_left hy.2 (sub_nonneg.mpr hcR)]
        have hx_shift : socialSurplus R latency x =
            socialSurplus cStar latency x + (R - cStar) * d := by
          simp only [socialSurplus, ← hsum_d, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
        have hshift_nonneg : 0 ≤ (R - cStar) * d := mul_nonneg (sub_nonneg.mpr hcR) hd_pos.le
        suffices hc_bound : 5 * socialSurplus cStar latency y ≤
            6 * socialSurplus cStar latency x by
          linarith
        have hbound_of_opt (hopt_c : IsSocialOptimum d cStar latency x) :
            5 * socialSurplus cStar latency y ≤ 6 * socialSurplus cStar latency x := by
          have h0_feas : IsFeasiblePricedFlow d (0 : Link → ℝ) :=
            ⟨fun _ => le_rfl, by simp [hd_pos.le]⟩
          have h0_val : socialSurplus cStar latency (0 : Link → ℝ) = 0 := by simp [socialSurplus]
          linarith [hopt_c.2 y hy, hopt_c.2 0 h0_feas]
        -- Subcase A: no competitor outside s₀ (monopoly!):
        by_cases hcomp_ne : ∃ q, owner q ≠ s₀
        · -- Subcase B: some competitor q outside s₀ has latencyDeriv q (x q) = 0:
          by_cases hcomp_z : ∃ q, owner q ≠ s₀ ∧ latencyDeriv q (x q) = 0
          · obtain ⟨q, hq_comp, hq_z⟩ := hcomp_z
            have hp_eq := hoe.price_eq_mul_deriv_of_comp_deriv_zero h hzs hpos hq_comp hq_z
            have hdU_zero : cStar = m := by simp only [cStar, m, mc, hp_eq]
            -- Then mc k = cStar for all k, so x maximizes socialSurplus cStar latency!
            have hmc_eq : ∀ k, mc k = cStar := fun k =>
              le_antisymm (hmc_le_c k) (hdU_zero ▸ hi₀_min k (Finset.mem_univ k))
            exact hbound_of_opt (h.isSocialOptimum_iff_kkt.mpr
              ⟨hoe.2.1.1, 0, le_rfl, zero_mul _, fun k => by linarith [hmc_eq k],
                fun k _ => by linarith [hmc_eq k]⟩)
          · -- Main Subcase C: every competitor q outside s₀ has 0 < latencyDeriv q (x q)!
            push Not at hcomp_z
            have hcomp_pos : ∀ q, owner q ≠ s₀ → 0 < latencyDeriv q (x q) := fun q hq =>
              lt_of_le_of_ne (h.latencyDeriv_nonneg q (hoe.2.1.1.1 q)) (Ne.symm (hcomp_z q hq))
            -- Upper bound socialSurplus cStar latency y using linkSurplusEnvelope at m:
            have hy_env : socialSurplus cStar latency y ≤
                dU * d + ∑ k, linkSurplusEnvelope m (latency k (x k))
                  (x k * latencyDeriv k (x k)) (latencyDeriv k (x k)) := by
              have hsplit : socialSurplus cStar latency y =
                  dU * (∑ k, y k) + ∑ k, (m * y k - y k * latency k (y k)) := by
                simp only [socialSurplus, dU, Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun k _ => ?_
                ring
              rw [hsplit]
              have h1 : dU * (∑ k, y k) ≤ dU * d := mul_le_mul_of_nonneg_left hy.2 hdU0
              have h2 : ∑ k, (m * y k - y k * latency k (y k)) ≤
                  ∑ k, linkSurplusEnvelope m (latency k (x k))
                    (x k * latencyDeriv k (x k)) (latencyDeriv k (x k)) :=
                Finset.sum_le_sum fun k _ =>
                  linkSurplusEnvelope_ge h k (hoe.2.1.1.1 k) (hy.1 k) hm0
                    (hi₀_min k (Finset.mem_univ k))
              linarith
            -- Decompose socialSurplus cStar latency x via cStar = m + dU:
            have hx_decomp : socialSurplus cStar latency x =
                dU * d + ∑ k, (m * x k - x k * latency k (x k)) := by
              simp only [socialSurplus, dU, ← hsum_d, Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun k _ => ?_
              ring
            -- Apply OE price upper bound at i₀ to lower-bound dU * Xs₀:
            let ownSet : Finset Link := Finset.univ.filter fun k => owner k = s₀
            let compSet : Finset Link := Finset.univ.filter fun q => owner q ≠ s₀
            have hub_i₀ :=
              hoe.price_le_mul_deriv_add_markup h hzs hpos hsum_d hcomp_ne hcomp_pos
            have hdU_eq_diff : dU = p i₀ - x i₀ * latencyDeriv i₀ (x i₀) := by
              simp only [dU, cStar, m, mc]
              ring
            have hSinv_pos : 0 < ∑ q ∈ compSet, (latencyDeriv q (x q))⁻¹ := by
              obtain ⟨q₀, hq₀⟩ := hcomp_ne
              exact (inv_pos.mpr (hcomp_pos q₀ hq₀)).trans_le
                (Finset.single_le_sum (fun q hq => inv_nonneg.mpr
                  (hcomp_pos q (Finset.mem_filter.mp hq).2).le)
                  (Finset.mem_filter.mpr ⟨Finset.mem_univ q₀, hq₀⟩))
            have hdU_Xs : dU * ∑ q ∈ compSet, (latencyDeriv q (x q))⁻¹ ≤
                ∑ r ∈ ownSet, x r := by
              have hle_div : dU ≤ (∑ r ∈ ownSet, x r) /
                  (∑ q ∈ compSet, (latencyDeriv q (x q))⁻¹) := by
                simp only [ownSet, compSet, s₀]
                linarith [hub_i₀, hdU_eq_diff]
              exact (le_div_iff₀ hSinv_pos).mp hle_div
            have hd_split : d = (∑ r ∈ ownSet, x r) + ∑ q ∈ compSet, x q := by
              rw [← hsum_d]
              exact (Finset.sum_filter_add_sum_filter_not Finset.univ
                (fun k => owner k = s₀) x).symm
            have hdU_d_ge : ∑ q ∈ compSet, (dU ^ 2 / latencyDeriv q (x q) + dU * x q) ≤
                dU * d := by
              have hsum1 : dU * (dU * ∑ q ∈ compSet, (latencyDeriv q (x q))⁻¹) =
                  ∑ q ∈ compSet, dU ^ 2 / latencyDeriv q (x q) := by
                rw [← mul_assoc, Finset.mul_sum]
                exact Finset.sum_congr rfl fun q _ => by ring
              rw [hd_split, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
              linarith [mul_le_mul_of_nonneg_left hdU_Xs hdU0]
            -- Partition ∑ k over ownSet and compSet and apply the two per-link lemmas!
            have hpart_env : ∑ k, linkSurplusEnvelope m (latency k (x k))
                  (x k * latencyDeriv k (x k)) (latencyDeriv k (x k)) =
                (∑ r ∈ ownSet, linkSurplusEnvelope m (latency r (x r))
                  (x r * latencyDeriv r (x r)) (latencyDeriv r (x r))) +
                (∑ q ∈ compSet, linkSurplusEnvelope m (latency q (x q))
                  (x q * latencyDeriv q (x q)) (latencyDeriv q (x q))) :=
              (Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => owner k = s₀) _).symm
            have hpart_x : ∑ k, (m * x k - x k * latency k (x k)) =
                (∑ r ∈ ownSet, (m * x r - x r * latency r (x r))) +
                (∑ q ∈ compSet, (m * x q - x q * latency q (x q))) :=
              (Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => owner k = s₀) _).symm
            have hown_bound : 5 * ∑ r ∈ ownSet, linkSurplusEnvelope m (latency r (x r))
                  (x r * latencyDeriv r (x r)) (latencyDeriv r (x r)) ≤
                6 * ∑ r ∈ ownSet, (m * x r - x r * latency r (x r)) := by
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_le_sum fun r hr => ?_
              have hr_own : owner r = s₀ := (Finset.mem_filter.mp hr).2
              have hm_eq_r : m = latency r (x r) + x r * latencyDeriv r (x r) :=
                (hoe.marginalCost_eq_of_owner_eq h hzs hpos hr_own).symm
              rw [hm_eq_r]
              exact linkSurplusEnvelope_at_min_five_sixths (hoe.2.1.1.1 r)
                (h.latency_nonneg r (hoe.2.1.1.1 r))
                (h.latencyDeriv_nonneg r (hoe.2.1.1.1 r))
            have hcomp_bound : 5 * ∑ q ∈ compSet, linkSurplusEnvelope m (latency q (x q))
                  (x q * latencyDeriv q (x q)) (latencyDeriv q (x q)) ≤
                6 * (∑ q ∈ compSet, (m * x q - x q * latency q (x q))) +
                  ∑ q ∈ compSet, (dU ^ 2 / latencyDeriv q (x q) + dU * x q) := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_le_sum fun q hq => ?_
              have hq_comp : owner q ≠ s₀ := (Finset.mem_filter.mp hq).2
              have h1 := linkSurplusEnvelope_competitor_five_sixths (dU := dU)
                (hoe.2.1.1.1 q) (h.latency_nonneg q (hoe.2.1.1.1 q))
                (hcomp_pos q hq_comp) (h.latency_le_mul_deriv q (hoe.2.1.1.1 q))
                hm0 (hi₀_min q (Finset.mem_univ q)) (by linarith [hmc_le_c q])
              linarith
            rw [hpart_env] at hy_env
            rw [hpart_x] at hx_decomp
            linarith
        · -- Monopoly subcase: ∀ q, owner q = s₀, so mc k = m for all k!
          push Not at hcomp_ne
          have hmc_eq : ∀ k, mc k = m := fun k =>
            hoe.marginalCost_eq_of_owner_eq h hzs hpos (hcomp_ne k)
          exact hbound_of_opt (h.isSocialOptimum_iff_kkt.mpr
            ⟨hoe.2.1.1, dU, hdU0, by rw [hsum_d, sub_self, mul_zero],
              fun k => by linarith [hmc_eq k], fun k _ => by linarith [hmc_eq k]⟩)
    · push Not at hpos
      exact of_opt (hoe.isSocialOptimum_of_forall_mul_eq_zero h fun i =>
        le_antisymm (hpos i) (mul_nonneg (hoe.1 i) (hoe.2.1.1.1 i)))
  · rw [not_nonempty_iff] at hne
    simp [socialSurplus]

/-- Single-link-per-provider corollary of **Theorem 22.3** (requiring no `ZeroLatencySingleton`
hypothesis when `Function.Injective owner`). -/
theorem oligopoly_surplus_five_sixths_of_injective {Link Provider : Type*} [Fintype Link]
    [DecidableEq Provider] {d R : ℝ} {latency latencyDeriv : Link → ℝ → ℝ}
    (h : SmoothConvexLatencies latency latencyDeriv) {owner : Link → Provider}
    (hinj : Function.Injective owner) {p x y : Link → ℝ}
    (hoe : IsOligopolyEquilibrium d R latency owner p x) (hy : IsFeasiblePricedFlow d y) :
    5 * socialSurplus R latency y ≤ 6 * socialSurplus R latency x :=
  oligopoly_surplus_five_sixths h hoe (zeroLatencySingleton_of_injective hinj x) hy

/-- Ratio form of **Theorem 22.3** ([Ozdaglar and Srikant, Eq. (22.28) and Theorem 22.3,
pp. 583–584][OzdaglarSrikant2007]): `5 / 6 ≤ S(x) / S(xS)` whenever `0 < S(xS)`. -/
theorem oligopoly_efficiency_ge_five_sixths {Link Provider : Type*} [Fintype Link]
    [DecidableEq Provider] {d R : ℝ} {latency latencyDeriv : Link → ℝ → ℝ}
    (h : SmoothConvexLatencies latency latencyDeriv) {owner : Link → Provider} {p x xS : Link → ℝ}
    (hoe : IsOligopolyEquilibrium d R latency owner p x)
    (hzs : ZeroLatencySingleton latency owner x)
    (hopt : IsSocialOptimum d R latency xS) (hpos : 0 < socialSurplus R latency xS) :
    (5 : ℝ) / 6 ≤ socialSurplus R latency x / socialSurplus R latency xS := by
  rw [div_le_div_iff₀ (by positivity) hpos]
  linarith [oligopoly_surplus_five_sixths h hoe hzs hopt.1]

end FiveSixthsBound

section OligopolyTightnessFamily

/-!
### Exact `5 / 6` witness on `I = n + 2` links ([OzdaglarSrikant2007], Example 22.2, p. 584)
-/

/-- Latency functions of **Example 22.2** on `Fin (n + 2)` links: `0` on link `0` and
`(3 / 2) * (n + 1) * u` on links `i ≠ 0` ([Ozdaglar and Srikant, Example 22.2,
p. 584][OzdaglarSrikant2007]; [Acemoglu and Ozdaglar, Example 5.2,
p. 18][AcemogluOzdaglar2007MOR]). -/
@[expose] noncomputable def oligopolyTightnessLatency (n : ℕ) (i : Fin (n + 2)) (u : ℝ) : ℝ :=
  if i = 0 then 0 else (3 / 2) * ((n : ℝ) + 1) * u

/-- Latency derivatives of `oligopolyTightnessLatency`. -/
@[expose] noncomputable def oligopolyTightnessLatencyDeriv (n : ℕ) (i : Fin (n + 2))
    (_ : ℝ) : ℝ :=
  if i = 0 then 0 else (3 / 2) * ((n : ℝ) + 1)

/-- Equilibrium prices `(1, 1 / 2, ..., 1 / 2)` of **Example 22.2**. -/
@[expose] noncomputable def oligopolyTightnessPrice (n : ℕ) (i : Fin (n + 2)) : ℝ :=
  if i = 0 then 1 else 1 / 2

/-- Equilibrium flows `(2 / 3, 1 / (3 * (n + 1)), ..., 1 / (3 * (n + 1)))` of **Example 22.2**. -/
@[expose] noncomputable def oligopolyTightnessFlow (n : ℕ) (i : Fin (n + 2)) : ℝ :=
  if i = 0 then 2 / 3 else 1 / (3 * ((n : ℝ) + 1))

/-- Socially optimal flow `(1, 0, ..., 0)` of **Example 22.2**. -/
@[expose] def oligopolyTightnessOptFlow (n : ℕ) (i : Fin (n + 2)) : ℝ :=
  if i = 0 then 1 else 0

theorem oligopolyTightness_smoothConvex (n : ℕ) :
    SmoothConvexLatencies (oligopolyTightnessLatency n) (oligopolyTightnessLatencyDeriv n) where
  zero_at_zero i := by simp [oligopolyTightnessLatency]
  monotoneOn i a _ b _ hab := by
    by_cases hi : i = 0
    · simp [oligopolyTightnessLatency, hi]
    · simp only [oligopolyTightnessLatency, hi, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left hab (by positivity)
  convexOn i := by
    refine ⟨convex_Ici 0, fun a _ b _ w₁ w₂ _ _ _ => ?_⟩
    by_cases hi : i = 0
    · simp [oligopolyTightnessLatency, hi]
    · simp only [oligopolyTightnessLatency, hi, ↓reduceIte, smul_eq_mul]
      linarith
  hasDerivAt i x _ := by
    by_cases hi : i = 0
    · subst hi
      simp only [oligopolyTightnessLatencyDeriv, ↓reduceIte]
      have hfun : oligopolyTightnessLatency n 0 = fun _ => 0 := by
        ext u; simp [oligopolyTightnessLatency]
      rw [hfun]
      exact hasDerivAt_const x 0
    · simp only [oligopolyTightnessLatencyDeriv, hi, ↓reduceIte]
      have hfun : oligopolyTightnessLatency n i = fun u => (3 / 2) * ((n : ℝ) + 1) * u := by
        ext u; simp [oligopolyTightnessLatency, hi]
      rw [hfun]
      convert (hasDerivAt_id' x).const_mul ((3 / 2) * ((n : ℝ) + 1)) using 1
      ring

/-- `(oligopolyTightnessPrice n, oligopolyTightnessFlow n)` is a pure-strategy Oligopoly Equilibrium
on `Fin (n + 2)` under single-link ownership `id` ([Ozdaglar and Srikant, Example 22.2,
p. 584][OzdaglarSrikant2007]). -/
theorem oligopolyTightness_isOligopolyEquilibrium (n : ℕ) :
    IsOligopolyEquilibrium 1 1 (oligopolyTightnessLatency n) id
      (oligopolyTightnessPrice n) (oligopolyTightnessFlow n) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcard_er : ((Finset.univ : Finset (Fin (n + 2))).erase 0).card = n + 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0)]; simp
  have hsum : ∑ i : Fin (n + 2), oligopolyTightnessFlow n i = 1 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 2)))]
    have hconst : ∀ i ∈ (Finset.univ : Finset (Fin (n + 2))).erase 0,
        oligopolyTightnessFlow n i = 1 / (3 * ((n : ℝ) + 1)) := fun i hi => by
      simp [oligopolyTightnessFlow, (Finset.mem_erase.mp hi).1]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard_er, nsmul_eq_mul]
    simp only [oligopolyTightnessFlow, ↓reduceIte]
    push_cast
    field_simp
    ring
  have heff_one : ∀ i : Fin (n + 2),
      oligopolyTightnessLatency n i (oligopolyTightnessFlow n i) +
        oligopolyTightnessPrice n i = 1 := fun i => by
    by_cases hi : i = 0
    · simp [oligopolyTightnessLatency, oligopolyTightnessPrice, hi]
    · simp only [oligopolyTightnessLatency, oligopolyTightnessFlow, oligopolyTightnessPrice, hi,
        ↓reduceIte]
      field_simp
      ring
  have hw : IsPricedWardrop 1 1 (oligopolyTightnessLatency n)
      (oligopolyTightnessPrice n) (oligopolyTightnessFlow n) := by
    refine ⟨⟨fun i => ?_, hsum.le⟩, fun a b _ => ?_, fun a _ => ?_, fun _ => hsum⟩
    · by_cases hi : i = 0 <;> simp only [oligopolyTightnessFlow, hi, ↓reduceIte] <;> positivity
    · rw [heff_one a, heff_one b]
    · rw [heff_one a]
  refine ⟨fun i => ?_, hw, fun s p' x' hp'0 hp'comp hw' => ?_⟩
  · by_cases hi : i = 0 <;> simp only [oligopolyTightnessPrice, hi, ↓reduceIte] <;> positivity
  · have hprof_eq : ∀ q xq : Fin (n + 2) → ℝ, providerProfit id s q xq = q s * xq s := by
      intro q xq
      simp only [providerProfit, id_eq]
      have hflt : (Finset.univ.filter fun i : Fin (n + 2) => i = s) = {s} := by
        ext i; simp
      rw [hflt, Finset.sum_singleton]
    rw [hprof_eq, hprof_eq]
    by_cases hs : s = 0
    · -- Provider 0 best response: original profit is 2 / 3.
      subst hs
      simp only [oligopolyTightnessPrice, oligopolyTightnessFlow, ↓reduceIte, one_mul]
      rcases (hw'.1.1 0).eq_or_lt with hx0_z | hx0_pos
      · rw [← hx0_z, mul_zero]; positivity
      have hp'0_le_one : p' 0 ≤ 1 := by
        simpa only [oligopolyTightnessLatency, ↓reduceIte, zero_add] using hw'.2.2.1 0 hx0_pos
      rcases le_or_gt (p' 0) (1 / 2) with hp_le_half | hp_gt_half
      · have hx0_le_one : x' 0 ≤ 1 :=
          (Finset.single_le_sum (fun k _ => hw'.1.1 k) (Finset.mem_univ 0)).trans hw'.1.2
        nlinarith [hp'0 0, hw'.1.1 0]
      · -- When 1 / 2 < p' 0 ≤ 1, each j ≠ 0 satisfies (3/2)*(n+1)*x' j + 1/2 ≥ p' 0:
        have hj_lb : ∀ j ∈ (Finset.univ : Finset (Fin (n + 2))).erase 0,
            (2 / (3 * ((n : ℝ) + 1))) * (p' 0 - 1 / 2) ≤ x' j := fun j hj => by
          have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
          have hward := hw'.2.1 0 j hx0_pos
          have hpj : p' j = 1 / 2 := by rw [hp'comp j hj0]; simp [oligopolyTightnessPrice, hj0]
          simp only [oligopolyTightnessLatency, ↓reduceIte, hj0, hpj, zero_add] at hward
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          linarith
        have hsum_er : (2 / 3) * (p' 0 - 1 / 2) ≤
            ∑ j ∈ (Finset.univ : Finset (Fin (n + 2))).erase 0, x' j := by
          have h1 := Finset.sum_le_sum hj_lb
          rw [Finset.sum_const, hcard_er, nsmul_eq_mul] at h1
          have hl : ((n + 1 : ℕ) : ℝ) * ((2 / (3 * ((n : ℝ) + 1))) * (p' 0 - 1 / 2)) =
              (2 / 3) * (p' 0 - 1 / 2) := by
            push_cast
            field_simp
          linarith
        have htot_le : x' 0 + ∑ j ∈ (Finset.univ : Finset (Fin (n + 2))).erase 0, x' j ≤ 1 :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).trans_le hw'.1.2
        linarith [mul_le_mul_of_nonneg_left (by linarith : x' 0 ≤ 4 / 3 - 2 / 3 * p' 0) (hp'0 0),
          sq_nonneg (p' 0 - 1)]
    · -- Provider s ≠ 0 best response: original profit is 1 / (6 * (n + 1)).
      have hprof_s : oligopolyTightnessPrice n s * oligopolyTightnessFlow n s =
          1 / (6 * ((n : ℝ) + 1)) := by
        simp only [oligopolyTightnessPrice, oligopolyTightnessFlow, hs, ↓reduceIte]
        field_simp
        ring
      rw [hprof_s]
      rcases (hw'.1.1 s).eq_or_lt with hxs_z | hxs_pos
      · rw [← hxs_z, mul_zero]; positivity
      have hward_s0 := hw'.2.1 s 0 hxs_pos
      have hp'0_eq : p' 0 = 1 := by rw [hp'comp 0 (Ne.symm hs)]; simp [oligopolyTightnessPrice]
      simp only [oligopolyTightnessLatency, hs, ↓reduceIte, hp'0_eq, zero_add] at hward_s0
      have hxs_ub : x' s ≤ (1 - p' s) * (2 / (3 * ((n : ℝ) + 1))) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        linarith
      have hquad : p' s * ((1 - p' s) * (2 / (3 * ((n : ℝ) + 1)))) =
          1 / (6 * ((n : ℝ) + 1)) - (p' s - 1 / 2) ^ 2 * (2 / (3 * ((n : ℝ) + 1))) := by
        field_simp
        ring
      linarith [mul_le_mul_of_nonneg_left hxs_ub (hp'0 s),
        mul_nonneg (sq_nonneg (p' s - 1 / 2)) (by positivity : (0 : ℝ) ≤ 2 / (3 * ((n : ℝ) + 1)))]

/-- `oligopolyTightnessOptFlow n` (`(1, 0, ..., 0)`) is a social optimum with social surplus `1`. -/
theorem oligopolyTightness_isSocialOptimum (n : ℕ) :
    IsSocialOptimum 1 1 (oligopolyTightnessLatency n) (oligopolyTightnessOptFlow n) ∧
      socialSurplus 1 (oligopolyTightnessLatency n) (oligopolyTightnessOptFlow n) = 1 := by
  have hval : socialSurplus 1 (oligopolyTightnessLatency n) (oligopolyTightnessOptFlow n) = 1 := by
    simp only [socialSurplus]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 2)))]
    have hrest : ∑ i ∈ (Finset.univ : Finset (Fin (n + 2))).erase 0,
        (1 - oligopolyTightnessLatency n i (oligopolyTightnessOptFlow n i)) *
          oligopolyTightnessOptFlow n i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        simp [oligopolyTightnessOptFlow, (Finset.mem_erase.mp hi).1]
    rw [hrest]
    simp [oligopolyTightnessOptFlow, oligopolyTightnessLatency]
  refine ⟨⟨⟨fun i => ?_, ?_⟩, fun y hy => ?_⟩, hval⟩
  · by_cases hi : i = 0 <;> simp [oligopolyTightnessOptFlow, hi]
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 2)))]
    have hrest : ∑ i ∈ (Finset.univ : Finset (Fin (n + 2))).erase 0,
        oligopolyTightnessOptFlow n i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        simp [oligopolyTightnessOptFlow, (Finset.mem_erase.mp hi).1]
    rw [hrest]
    simp [oligopolyTightnessOptFlow]
  · rw [hval]
    have hle1 : socialSurplus 1 (oligopolyTightnessLatency n) y ≤ ∑ i, y i := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hl0 := (oligopolyTightness_smoothConvex n).latency_nonneg i (hy.1 i)
      nlinarith [hy.1 i]
    exact hle1.trans hy.2

/-- Exact social surplus `5 / 6` at the Oligopoly Equilibrium of **Example 22.2** for every `n : ℕ`
([Ozdaglar and Srikant, Example 22.2, p. 584][OzdaglarSrikant2007]). -/
theorem oligopolyTightness_surplus_eq_five_sixths (n : ℕ) :
    socialSurplus 1 (oligopolyTightnessLatency n) (oligopolyTightnessFlow n) =
      (5 / 6) * socialSurplus 1 (oligopolyTightnessLatency n) (oligopolyTightnessOptFlow n) := by
  rw [(oligopolyTightness_isSocialOptimum n).2, mul_one]
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hcard_er : ((Finset.univ : Finset (Fin (n + 2))).erase 0).card = n + 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0)]; simp
  simp only [socialSurplus]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 2)))]
  have hconst : ∀ i ∈ (Finset.univ : Finset (Fin (n + 2))).erase 0,
      (1 - oligopolyTightnessLatency n i (oligopolyTightnessFlow n i)) *
        oligopolyTightnessFlow n i = 1 / (6 * ((n : ℝ) + 1)) := fun i hi => by
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    simp only [oligopolyTightnessLatency, oligopolyTightnessFlow, hi0, ↓reduceIte]
    field_simp
    ring
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard_er, nsmul_eq_mul]
  simp only [oligopolyTightnessLatency, oligopolyTightnessFlow, ↓reduceIte]
  push_cast
  field_simp
  ring

end OligopolyTightnessFamily

section ElasticTraffic

/-!
### Elastic traffic with concave marginal utility ([OzdaglarSrikant2007], Section 22.2.6, p. 585)
-/

/-- Regularity bundle for elastic aggregate user utility `u` with concave marginal utility `uDeriv`
and second derivative `uSecondDeriv` on `[0, ∞)` ([Ozdaglar and Srikant, Section 22.2.6,
pp. 584–585][OzdaglarSrikant2007]). Note that global monotonicity `uDeriv ≥ 0` on all of `[0, ∞)` is
intentionally not required, because a nonconstant concave nonincreasing function on `[0, ∞)`
(such as linear inverse demand `u'(X) = 1 - X`) eventually becomes negative for large `X`; at any
active Wardrop flow, `uDeriv (∑ i, x i) ≥ 0` holds automatically from nonnegative latencies and
prices. -/
structure SmoothConcaveMarginalUtility (u uDeriv uSecondDeriv : ℝ → ℝ) : Prop where
  zero_at_zero : u 0 = 0
  concaveOn : ConcaveOn ℝ (Set.Ici 0) u
  concaveOn_deriv : ConcaveOn ℝ (Set.Ici 0) uDeriv
  hasDerivAt : ∀ x, 0 ≤ x → HasDerivAt u (uDeriv x) x
  hasSecondDerivAt : ∀ x, 0 ≤ x → HasDerivAt uDeriv (uSecondDeriv x) x

/-- Priced **Wardrop equilibrium with elastic traffic** ([Ozdaglar and Srikant, Section 22.2.6,
p. 585][OzdaglarSrikant2007]): link flows are nonnegative, active links satisfy
`latency i (x i) + p i = uDeriv (∑ j, x j)`, and all links satisfy
`uDeriv (∑ j, x j) ≤ latency i (x i) + p i`. -/
@[expose] def IsElasticPricedWardrop {Link : Type*} [Fintype Link] (uDeriv : ℝ → ℝ)
    (latency : Link → ℝ → ℝ) (p x : Link → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧
    (∀ i, 0 < x i → latency i (x i) + p i = uDeriv (∑ j, x j)) ∧
    (∀ i, uDeriv (∑ j, x j) ≤ latency i (x i) + p i)

/-- **Elastic social surplus** `u (∑ i, x i) - ∑ i, latency i (x i) * x i` ([Ozdaglar and Srikant,
Section 22.2.6, p. 585][OzdaglarSrikant2007]). -/
@[expose] def elasticSocialSurplus {Link : Type*} [Fintype Link] (u : ℝ → ℝ)
    (latency : Link → ℝ → ℝ) (x : Link → ℝ) : ℝ :=
  u (∑ i, x i) - ∑ i, latency i (x i) * x i

/-- A nonnegative link flow `xS` is an **elastic social optimum** if it maximizes
`elasticSocialSurplus u latency` over all nonnegative flows `y ≥ 0`. -/
@[expose] def IsElasticSocialOptimum {Link : Type*} [Fintype Link] (u : ℝ → ℝ)
    (latency : Link → ℝ → ℝ) (xS : Link → ℝ) : Prop :=
  (∀ i, 0 ≤ xS i) ∧
    ∀ y : Link → ℝ, (∀ i, 0 ≤ y i) →
      elasticSocialSurplus u latency y ≤ elasticSocialSurplus u latency xS

/-- Pure-strategy **Oligopoly Equilibrium with elastic traffic** on parallel links where each link
is owned by an independent profit-maximizing provider ([Ozdaglar and Srikant, Section 22.2.6,
Theorem 22.4, p. 585][OzdaglarSrikant2007]; [Ozdaglar2008]). -/
@[expose] def IsElasticOligopolyEquilibrium {Link : Type*} [Fintype Link] [DecidableEq Link]
    (uDeriv : ℝ → ℝ) (latency : Link → ℝ → ℝ) (p x : Link → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧
    IsElasticPricedWardrop uDeriv latency p x ∧
    ∀ i p' x', 0 ≤ p' →
      IsElasticPricedWardrop uDeriv latency (Function.update p i p') x' →
      p' * x' i ≤ p i * x i

namespace SmoothConcaveMarginalUtility

variable {u uDeriv uSecondDeriv : ℝ → ℝ}

theorem continuousOn (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv) :
    ContinuousOn u (Set.Ici 0) :=
  fun x hx => (hu.hasDerivAt x hx).continuousAt.continuousWithinAt

theorem continuousOn_deriv (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv) :
    ContinuousOn uDeriv (Set.Ici 0) :=
  fun x hx => (hu.hasSecondDerivAt x hx).continuousAt.continuousWithinAt

private theorem concaveOn_le_add_deriv_mul {f f' : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ici 0) f)
    (hd : ∀ x, 0 ≤ x → HasDerivAt f (f' x) x) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f y ≤ f x + f' x * (y - x) := by
  let negF : ℝ → ℝ := fun t => (-1 : ℝ) * f t
  have hconv : ConvexOn ℝ (Set.Ici 0) negF := by
    refine ⟨convex_Ici 0, fun a ha b hb w₁ w₂ hw₁ hw₂ hw => ?_⟩
    have h0 := hc.2 ha hb hw₁ hw₂ hw
    simp only [negF, smul_eq_mul] at h0 ⊢
    linarith
  have hderiv : HasDerivAt negF ((-1 : ℝ) * f' x) x := (hd x hx).const_mul (-1)
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hslope := hconv.le_slope_of_hasDerivAt hx hy hxy hderiv
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at hslope
    simp only [negF] at hslope
    linarith
  · simp
  · have hslope := hconv.slope_le_of_hasDerivAt hy hx hyx hderiv
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hyx)] at hslope
    simp only [negF] at hslope
    linarith

/-- First-order concavity upper bound `u y ≤ u x + uDeriv x * (y - x)` on `[0, ∞)`. -/
theorem le_add_deriv_mul (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    u y ≤ u x + uDeriv x * (y - x) :=
  concaveOn_le_add_deriv_mul hu.concaveOn hu.hasDerivAt hx hy

/-- First-order concavity upper bound `uDeriv y ≤ uDeriv x + uSecondDeriv x * (y - x)` on
`[0, ∞)`. -/
theorem deriv_le_add_secondDeriv_mul (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    uDeriv y ≤ uDeriv x + uSecondDeriv x * (y - x) :=
  concaveOn_le_add_deriv_mul hu.concaveOn_deriv hu.hasSecondDerivAt hx hy

theorem antitoneOn_deriv (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv) :
    AntitoneOn uDeriv (Set.Ici 0) := by
  intro a ha b hb hab
  rcases hab.eq_or_lt with rfl | hlt
  · exact le_rfl
  · have h1 := hu.le_add_deriv_mul ha hb
    have h2 := hu.le_add_deriv_mul hb ha
    have hmul : (uDeriv b - uDeriv a) * (b - a) ≤ 0 := by linarith
    have hle : uDeriv b - uDeriv a ≤ 0 := nonpos_of_mul_nonpos_left hmul (sub_pos.mpr hlt)
    linarith

private theorem deriv_le (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) : uDeriv b ≤ uDeriv a :=
  hu.antitoneOn_deriv ha (ha.trans hab) hab

theorem secondDeriv_nonpos (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv) {x : ℝ}
    (hx : 0 ≤ x) : uSecondDeriv x ≤ 0 := by
  let g : ℝ → ℝ := fun t => (-1 : ℝ) * uDeriv (x + t)
  have hd0 : HasDerivAt (fun s => (-1 : ℝ) * uDeriv s) ((-1 : ℝ) * uSecondDeriv x) (x + 0) := by
    simpa only [add_zero] using (hu.hasSecondDerivAt x hx).const_mul (-1)
  have hg_comp : HasDerivAt ((fun s => (-1 : ℝ) * uDeriv s) ∘ fun t => x + t)
      (((-1 : ℝ) * uSecondDeriv x) * 1) 0 :=
    HasDerivAt.comp (0 : ℝ) hd0 ((hasDerivAt_id' (0 : ℝ)).const_add x)
  have hg_deriv : HasDerivAt g ((-1 : ℝ) * uSecondDeriv x) 0 := by
    simpa only [Function.comp_def, mul_one] using hg_comp
  have h0 : 0 ≤ (-1 : ℝ) * uSecondDeriv x := by
    refine nonneg_of_hasDerivAt_of_forall_pos zero_lt_one hg_deriv fun t ht0 _ => ?_
    simp only [g, add_zero]
    have hant := hu.deriv_le hx (show x ≤ x + t by linarith)
    linarith
  linarith

theorem sub_mul_deriv_nonneg (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv) {x : ℝ}
    (hx : 0 ≤ x) : 0 ≤ u x - uDeriv x * x := by
  have h0 := hu.le_add_deriv_mul hx le_rfl
  rw [hu.zero_at_zero] at h0
  linarith

/-- Second-order concavity upper bound on `u y` via `ConcaveOn` of `u` and `uDeriv`: for `0 ≤ x`
and `0 ≤ y`,
`u y ≤ (u x - uDeriv x * x) + uDeriv x * y + (uSecondDeriv x / 2) * max 0 (y - x) ^ 2`. -/
theorem le_quadratic_upper (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    u y ≤ (u x - uDeriv x * x) + uDeriv x * y + (uSecondDeriv x / 2) * max 0 (y - x) ^ 2 := by
  rcases le_or_gt y x with hyx | hxy
  · rw [max_eq_left (by linarith)]
    have h1 := hu.le_add_deriv_mul hx hy
    linarith
  · rw [max_eq_right (by linarith)]
    have hint_u : IntervalIntegrable uDeriv MeasureTheory.volume x y := by
      refine (hu.continuousOn_deriv.mono ?_).intervalIntegrable
      rw [Set.uIcc_of_le hxy.le]
      exact fun t ht => hx.trans ht.1
    have hftc_u : ∫ t in x..y, uDeriv t = u y - u x := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) hint_u
      rw [Set.uIcc_of_le hxy.le] at ht
      exact hu.hasDerivAt t (hx.trans ht.1)
    let q : ℝ → ℝ := fun t =>
      (uDeriv x - uSecondDeriv x * x) * t + (uSecondDeriv x / 2) * (t * t)
    let q' : ℝ → ℝ := fun t => uDeriv x + uSecondDeriv x * (t - x)
    have hq_deriv : ∀ t, HasDerivAt q (q' t) t := fun t => by
      have hd1 : HasDerivAt (fun s => (uDeriv x - uSecondDeriv x * x) * s)
          ((uDeriv x - uSecondDeriv x * x) * 1) t :=
        (hasDerivAt_id' t).const_mul (uDeriv x - uSecondDeriv x * x)
      have hsq : HasDerivAt (fun s => s * s) (1 * t + t * 1) t :=
        (hasDerivAt_id' t).mul (hasDerivAt_id' t)
      have hd2 : HasDerivAt (fun s => (uSecondDeriv x / 2) * (s * s))
          ((uSecondDeriv x / 2) * (1 * t + t * 1)) t :=
        hsq.const_mul (uSecondDeriv x / 2)
      convert hd1.add hd2 using 1
      simp only [q']
      ring
    have hint_q : IntervalIntegrable q' MeasureTheory.volume x y := by
      have hcont_q' : Continuous q' :=
        continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))
      exact hcont_q'.intervalIntegrable x y
    have hftc_q : ∫ t in x..y, q' t = q y - q x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hq_deriv t) hint_q
    have hmono : ∫ t in x..y, uDeriv t ≤ ∫ t in x..y, q' t :=
      intervalIntegral.integral_mono_on hxy.le hint_u hint_q fun t ht =>
        hu.deriv_le_add_secondDeriv_mul hx (hx.trans ht.1)
    rw [hftc_u, hftc_q] at hmono
    have hq_diff : q y - q x =
        uDeriv x * (y - x) + (uSecondDeriv x / 2) * (y - x) ^ 2 := by
      simp only [q]
      ring
    linarith

/-- Envelope upper bound on `u y - m * y` when `m ≤ uDeriv x` and `U₂ = -uSecondDeriv x > 0`. -/
theorem le_envelope_upper (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv) {x y m : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hm_le : m ≤ uDeriv x) (hU2_pos : 0 < -uSecondDeriv x) :
    u y - m * y ≤ (u x - uDeriv x * x) + (uDeriv x - m) * x +
      (uDeriv x - m) ^ 2 / (2 * (-uSecondDeriv x)) := by
  let U₁ := uDeriv x
  let U₂ := -uSecondDeriv x
  have hquad := hu.le_quadratic_upper hx hy
  have hU2_eq : uSecondDeriv x = -U₂ := by simp [U₂]
  rw [hU2_eq] at hquad
  rcases le_or_gt y x with hyx | hxy
  · rw [max_eq_left (by linarith)] at hquad
    have h1 : (U₁ - m) * (y - x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by simp only [U₁]; linarith) (by linarith)
    have h2 : 0 ≤ (U₁ - m) ^ 2 / (2 * U₂) := by positivity
    simp only [U₁, U₂] at h1 h2 hquad ⊢
    linarith
  · rw [max_eq_right (by linarith)] at hquad
    let z : ℝ := y - x
    have hsq : (U₁ - m) * z - (U₂ / 2) * z ^ 2 ≤ (U₁ - m) ^ 2 / (2 * U₂) := by
      rw [le_div_iff₀ (by positivity : 0 < 2 * U₂)]
      have hid : (U₁ - m) ^ 2 - ((U₁ - m) * z - (U₂ / 2) * z ^ 2) * (2 * U₂) =
          (U₂ * z - (U₁ - m)) ^ 2 := by ring
      nlinarith [sq_nonneg (U₂ * z - (U₁ - m))]
    simp only [U₁, U₂, z] at hsq hquad ⊢
    linarith

end SmoothConcaveMarginalUtility

/-- Elastic social surplus is nonnegative at any elastic priced Wardrop equilibrium with
nonnegative prices. -/
theorem IsElasticPricedWardrop.socialSurplus_nonneg {Link : Type*} [Fintype Link]
    {u uDeriv uSecondDeriv : ℝ → ℝ} (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv)
    {latency : Link → ℝ → ℝ} {p x : Link → ℝ}
    (hw : IsElasticPricedWardrop uDeriv latency p x) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ elasticSocialSurplus u latency x := by
  let X : ℝ := ∑ i, x i
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ => hw.1 i
  have hdu : 0 ≤ u X - uDeriv X * X := hu.sub_mul_deriv_nonneg hX0
  have hrev : 0 ≤ uDeriv X * X - ∑ i, latency i (x i) * x i := by
    have hid : uDeriv X * X - ∑ i, latency i (x i) * x i = ∑ i, p i * x i := by
      simp only [X, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases (hw.1 i).eq_or_lt with hxi0 | hxi_pos
      · simp [← hxi0]
      · have heff := hw.2.1 i hxi_pos
        change uDeriv X * x i - latency i (x i) * x i = p i * x i
        nlinarith
    rw [hid]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hw.1 i)
  simp only [elasticSocialSurplus]
  change 0 ≤ u X - ∑ i, latency i (x i) * x i
  linarith

/-- First-order KKT sufficiency for an elastic social optimum: if `x ≥ 0` satisfies
`uDeriv (∑ j, x j) ≤ latency i (x i) + x i * latencyDeriv i (x i)` on all links with equality on
active links (`0 < x i`), then `x` maximizes `elasticSocialSurplus u latency`. -/
theorem isElasticSocialOptimum_of_kkt {Link : Type*} [Fintype Link]
    {u uDeriv uSecondDeriv : ℝ → ℝ} (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv)
    {latency latencyDeriv : Link → ℝ → ℝ} (hl : SmoothConvexLatencies latency latencyDeriv)
    {x : Link → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hle : ∀ i, uDeriv (∑ j, x j) ≤ latency i (x i) + x i * latencyDeriv i (x i))
    (heq : ∀ i, 0 < x i → latency i (x i) + x i * latencyDeriv i (x i) = uDeriv (∑ j, x j)) :
    IsElasticSocialOptimum u latency x := by
  refine ⟨hx0, fun y hy0 => ?_⟩
  let X : ℝ := ∑ i, x i
  let Y : ℝ := ∑ i, y i
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ => hx0 i
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun i _ => hy0 i
  have hu_ub : u Y ≤ u X + ∑ i, uDeriv X * (y i - x i) := by
    have h1 := hu.le_add_deriv_mul hX0 hY0
    have hdiff : Y - X = ∑ i, (y i - x i) := by simp [Y, X, Finset.sum_sub_distrib]
    rw [hdiff, Finset.mul_sum] at h1
    exact h1
  have hl_lb : ∑ i, (latency i (x i) * x i +
        (latency i (x i) + x i * latencyDeriv i (x i)) * (y i - x i)) ≤
      ∑ i, latency i (y i) * y i := by
    refine Finset.sum_le_sum fun i _ => ?_
    have htan := hl.add_deriv_mul_le i (hx0 i) (hy0 i)
    have hmul := mul_le_mul_of_nonneg_right htan (hy0 i)
    have hd_nn := hl.latencyDeriv_nonneg i (hx0 i)
    nlinarith [sq_nonneg (y i - x i)]
  have hsum_nonpos : ∑ i, (uDeriv X - latency i (x i) - x i * latencyDeriv i (x i)) *
      (y i - x i) ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => ?_
    rcases (hx0 i).eq_or_lt with hxi0 | hxi_pos
    · have hi_le := hle i
      simp only [X, ← hxi0, sub_zero] at hi_le ⊢
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hy0 i)
    · have hi_eq := heq i hxi_pos
      have hz : uDeriv X - latency i (x i) - x i * latencyDeriv i (x i) = 0 := by
        simp only [X]; linarith
      rw [hz, zero_mul]
  have hsplit : ∑ i, (uDeriv X - latency i (x i) - x i * latencyDeriv i (x i)) * (y i - x i) =
      (∑ i, uDeriv X * (y i - x i)) -
        ∑ i, (latency i (x i) + x i * latencyDeriv i (x i)) * (y i - x i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [Finset.sum_add_distrib] at hl_lb
  simp only [elasticSocialSurplus]
  change u Y - ∑ i, latency i (y i) * y i ≤ u X - ∑ i, latency i (x i) * x i
  linarith

/-- **Existence of an elastic priced Wardrop equilibrium** at any nonnegative price vector `p'`
whenever an elastic social optimum exists. -/
theorem exists_isElasticPricedWardrop_of_socialOptimum {Link : Type*} [Fintype Link]
    {u uDeriv uSecondDeriv : ℝ → ℝ} (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv)
    {latency latencyDeriv : Link → ℝ → ℝ} (hl : SmoothConvexLatencies latency latencyDeriv)
    {xS : Link → ℝ} (hopt : IsElasticSocialOptimum u latency xS)
    (p' : Link → ℝ) (hp'0 : ∀ i, 0 ≤ p' i) :
    ∃ x', IsElasticPricedWardrop uDeriv latency p' x' := by
  classical
  by_cases hne : Nonempty Link
  · rcases le_or_gt (uDeriv 0) 0 with hu0_le | hu0_pos
    · refine ⟨0, fun _ => le_rfl, fun _ h => False.elim (lt_irrefl 0 h), fun i => ?_⟩
      simp only [Pi.zero_apply, Finset.sum_const_zero, hl.zero_at_zero i, zero_add]
      exact hu0_le.trans (hp'0 i)
    -- Coercivity from hopt: for every link i, ∃ b > 0 with uDeriv b ≤ latency i b!
    have hex_b : ∀ i : Link, ∃ b : ℝ, 0 < b ∧ uDeriv b ≤ latency i b := fun i => by
      by_cases hlat_pos : ∃ t₁ : ℝ, 0 < t₁ ∧ 0 < latency i t₁
      · obtain ⟨t₁, ht₁, hlt₁⟩ := hlat_pos
        let K : ℝ := max 2 (uDeriv 0 / latency i t₁ + 1)
        have hK_gt1 : 1 < K := lt_of_lt_of_le one_lt_two (le_max_left _ _)
        have hK_pos : 0 < K := zero_lt_one.trans hK_gt1
        let b : ℝ := K * t₁
        obtain ⟨hb_pos, hw1, hw2, hw_sum, hcomb⟩ := convex_comb_scale_zero ht₁ hK_gt1
        have hconv :=
          (hl.convexOn i).2 (Set.mem_Ici.mpr hb_pos.le) (Set.mem_Ici.mpr le_rfl) hw1 hw2 hw_sum
        rw [hcomb] at hconv
        simp only [hl.zero_at_zero i, smul_eq_mul, mul_zero, add_zero] at hconv
        have hlat_b : K * latency i t₁ ≤ latency i b := by
          have hm := mul_le_mul_of_nonneg_left hconv hK_pos.le
          have hc : K * (1 / K * latency i b) = latency i b := by field_simp
          linarith
        have hK_ge : uDeriv 0 / latency i t₁ + 1 ≤ K := le_max_right _ _
        have hu0_lt : uDeriv 0 < K * latency i t₁ := by
          have hm := mul_le_mul_of_nonneg_right hK_ge hlt₁.le
          have hc : (uDeriv 0 / latency i t₁ + 1) * latency i t₁ = uDeriv 0 + latency i t₁ := by
            field_simp
          linarith
        have hud_le : uDeriv b ≤ uDeriv 0 :=
          hu.deriv_le le_rfl hb_pos.le
        exact ⟨b, hb_pos, by linarith⟩
      · -- latency i t = 0 for all t ≥ 0:
        push Not at hlat_pos
        have hlat_z : ∀ t, 0 ≤ t → latency i t = 0 := fun t ht => by
          rcases ht.eq_or_lt with rfl | ht_pos
          · exact hl.zero_at_zero i
          · exact le_antisymm (hlat_pos t ht_pos) (hl.latency_nonneg i ht)
        -- u t ≤ M := elasticSocialSurplus u latency xS for all t ≥ 0:
        let M : ℝ := elasticSocialSurplus u latency xS
        have hu_le_M : ∀ t, 0 ≤ t → u t ≤ M := fun t ht => by
          let y : Link → ℝ := Function.update 0 i t
          have hy0 : ∀ k, 0 ≤ y k := fun k => by
            by_cases hki : k = i <;> simp [y, hki, ht]
          have hsum_y : ∑ k, y k = t := by simp [y, Finset.sum_update_of_mem]
          have hlat_y : ∑ k, latency k (y k) * y k = 0 := Finset.sum_eq_zero fun k _ => by
            by_cases hki : k = i <;> simp [y, hki, hlat_z t ht]
          have hle := hopt.2 y hy0
          simp only [elasticSocialSurplus, hsum_y, hlat_y, sub_zero] at hle
          exact hle
        -- Either ∃ c > 0 with uDeriv c < uDeriv 0, or uDeriv ≡ uDeriv 0 (contradicting u ≤ M):
        by_cases hdec : ∃ c : ℝ, 0 < c ∧ uDeriv c < uDeriv 0
        · obtain ⟨c, hc_pos, huc_lt⟩ := hdec
          let δ : ℝ := uDeriv 0 - uDeriv c
          have hδ_pos : 0 < δ := sub_pos.mpr huc_lt
          let K : ℝ := max 2 (uDeriv 0 / δ + 1)
          have hK_gt1 : 1 < K := lt_of_lt_of_le one_lt_two (le_max_left _ _)
          have hK_pos : 0 < K := zero_lt_one.trans hK_gt1
          let b : ℝ := K * c
          obtain ⟨hb_pos, hw1, hw2, hw_sum, hcomb⟩ := convex_comb_scale_zero hc_pos hK_gt1
          have hconc := hu.concaveOn_deriv.2 (Set.mem_Ici.mpr hb_pos.le)
            (Set.mem_Ici.mpr le_rfl) hw1 hw2 hw_sum
          rw [hcomb] at hconc
          simp only [smul_eq_mul] at hconc
          have hmul := mul_le_mul_of_nonneg_left hconc hK_pos.le
          have hlhs : K * (1 / K * uDeriv b + (1 - 1 / K) * uDeriv 0) =
              uDeriv b + (K - 1) * uDeriv 0 := by field_simp
          rw [hlhs] at hmul
          have hub_b : uDeriv b ≤ uDeriv 0 - K * δ := by simp only [δ]; linarith
          have hK_ge : uDeriv 0 / δ + 1 ≤ K := le_max_right _ _
          have hKδ : uDeriv 0 + δ ≤ K * δ := by
            have hm := mul_le_mul_of_nonneg_right hK_ge hδ_pos.le
            have hc2 : (uDeriv 0 / δ + 1) * δ = uDeriv 0 + δ := by field_simp
            linarith
          exact ⟨b, hb_pos, by rw [hlat_z b hb_pos.le]; linarith⟩
        · exfalso
          push Not at hdec
          let b : ℝ := (max 0 M + 1) / uDeriv 0
          have hb_pos : 0 < b := div_pos (by positivity) hu0_pos
          have hud_eq : uDeriv b = uDeriv 0 :=
            le_antisymm (hu.deriv_le le_rfl hb_pos.le) (hdec b hb_pos)
          have hsub := hu.sub_mul_deriv_nonneg hb_pos.le
          rw [hud_eq] at hsub
          have hprod : uDeriv 0 * b = max 0 M + 1 := mul_div_cancel₀ _ hu0_pos.ne'
          have hub_M := hu_le_M b hb_pos.le
          linarith [le_max_right 0 M]
    choose b hb using hex_b
    let B : ℝ := (∑ k, b k) + 1
    have hB_pos : 0 < B := by
      have hsum_nn : 0 ≤ ∑ k, b k := Finset.sum_nonneg fun k _ => (hb k).1.le
      linarith
    -- Minimize Beckmann's elastic potential Φ(y) := (∑ k, ∫_0^{y k} effExt k) - ∫_0^{∑ y} uDerivExt
    let effExt : Link → ℝ → ℝ := fun k t => latency k (max 0 t) + p' k
    have heff_cont : ∀ k, Continuous (effExt k) := fun k =>
      ((hl.continuousOn k).comp_continuous (continuous_const.max continuous_id)
        fun s => le_max_left 0 s).add continuous_const
    let termPot : Link → ℝ → ℝ := fun k w => ∫ t in (0 : ℝ)..w, effExt k t
    have hterm_deriv : ∀ k w, HasDerivAt (termPot k) (effExt k w) w := fun k w =>
      intervalIntegral.integral_hasDerivAt_right ((heff_cont k).intervalIntegrable 0 w)
        ((heff_cont k).stronglyMeasurableAtFilter MeasureTheory.volume (nhds w))
        (heff_cont k).continuousAt
    let uDerivExt : ℝ → ℝ := fun s => uDeriv (max 0 s)
    have hud_cont : Continuous uDerivExt :=
      hu.continuousOn_deriv.comp_continuous (continuous_const.max continuous_id)
        fun s => le_max_left 0 s
    let uPot : ℝ → ℝ := fun w => ∫ t in (0 : ℝ)..w, uDerivExt t
    have huPot_deriv : ∀ w, HasDerivAt uPot (uDerivExt w) w := fun w =>
      intervalIntegral.integral_hasDerivAt_right (hud_cont.intervalIntegrable 0 w)
        (hud_cont.stronglyMeasurableAtFilter MeasureTheory.volume (nhds w))
        hud_cont.continuousAt
    let pot : (Link → ℝ) → ℝ := fun y => (∑ k, termPot k (y k)) - uPot (∑ k, y k)
    have hpot_cont : ContinuousOn pot {y : Link → ℝ | IsFeasiblePricedFlow B y} := by
      have h1 : ContinuousOn (fun y : Link → ℝ => ∑ k, termPot k (y k))
          {y : Link → ℝ | IsFeasiblePricedFlow B y} :=
        continuousOn_finsetSum Finset.univ fun k _ =>
          ((continuous_iff_continuousAt.mpr fun w => (hterm_deriv k w).continuousAt).comp
            (continuous_apply k)).continuousOn
      have h2 : Continuous (fun y : Link → ℝ => uPot (∑ k, y k)) :=
        (continuous_iff_continuousAt.mpr fun w => (huPot_deriv w).continuousAt).comp
          (continuous_finsetSum Finset.univ fun k _ => continuous_apply k)
      exact h1.sub h2.continuousOn
    have hfeas_ne : ({y : Link → ℝ | IsFeasiblePricedFlow B y}).Nonempty :=
      ⟨0, fun _ => le_rfl, by simp [hB_pos.le]⟩
    obtain ⟨x', hx'Feas, hmin⟩ := isCompact_feasiblePricedFlows.exists_isMinOn hfeas_ne hpot_cont
    have hx'min : ∀ y, IsFeasiblePricedFlow B y → pot x' ≤ pot y := fun y hy => hmin hy
    have hterm_upd : ∀ i v, ∑ k, termPot k (Function.update x' i v k) =
        termPot i v + ∑ k ∈ Finset.univ.erase i, termPot k (x' k) := fun i v => by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
      exact congrArg _ (Finset.sum_congr rfl fun k hk => by
        rw [Function.update_of_ne (Finset.mem_erase.mp hk).1])
    have hterm_sub : ∀ k a, HasDerivAt (fun t => termPot k (a - t)) (-effExt k a) 0 :=
      fun k a => by simpa only [sub_zero] using (hterm_deriv k (a - 0)).comp_const_sub a 0
    have hterm_add : ∀ k a, HasDerivAt (fun t => termPot k (a + t)) (effExt k a) 0 :=
      fun k a => by simpa only [add_zero] using (hterm_deriv k (a + 0)).comp_const_add a 0
    let X : ℝ := ∑ k, x' k
    have hX0 : 0 ≤ X := Finset.sum_nonneg fun k _ => hx'Feas.1 k
    -- (1) Decreasing x' i (for 0 < x' i) gives latency i (x' i) + p' i ≤ uDeriv X:
    have hact_le : ∀ i, 0 < x' i → latency i (x' i) + p' i ≤ uDeriv X := by
      intro i hi
      let g : ℝ → ℝ := fun t => pot (Function.update x' i (x' i - t))
      have hg_eq : ∀ t, g t = termPot i (x' i - t) +
          (∑ k ∈ Finset.univ.erase i, termPot k (x' k)) - uPot (X - t) := by
        intro t
        have h2 : ∑ k, Function.update x' i (x' i - t) k = X - t := by
          simpa only [X, sub_eq_add_neg] using sum_update_add_eq x' i (-t)
        simp only [g, pot, hterm_upd, h2]
      have hg_deriv : HasDerivAt g (uDeriv X - (latency i (x' i) + p' i)) 0 := by
        simp only [funext hg_eq]
        have hd2 : HasDerivAt (fun t => uPot (X - t)) (-uDerivExt X) 0 := by
          simpa only [sub_zero] using (huPot_deriv (X - 0)).comp_const_sub X 0
        have htot :=
          ((hterm_sub i (x' i)).add_const (∑ k ∈ Finset.univ.erase i, termPot k (x' k))).sub hd2
        have heff_i : effExt i (x' i) = latency i (x' i) + p' i := by
          simp [effExt, max_eq_right hi.le]
        have hud_X : uDerivExt X = uDeriv X := by simp [uDerivExt, max_eq_right hX0]
        rw [heff_i, hud_X] at htot
        convert htot using 1
        ring
      have h0 : 0 ≤ uDeriv X - (latency i (x' i) + p' i) := by
        refine nonneg_of_hasDerivAt_of_forall_pos hi hg_deriv fun t ht0 hti => ?_
        simp only [g, sub_zero, Function.update_eq_self]
        refine hx'min _ ⟨fun k => ?_, ?_⟩
        · simp only [Function.update_apply]; split_ifs <;> linarith [hx'Feas.1 k]
        · refine (Finset.sum_le_sum fun k _ => ?_).trans hx'Feas.2
          by_cases hki : k = i
          · subst hki; simp only [Function.update_self]; linarith
          · simp only [Function.update_of_ne hki]; exact le_rfl
      linarith
    -- (2) Swapping flow from i (0 < x' i) to j bounds effective cost on i by j:
    have hswap : ∀ i j, 0 < x' i → latency i (x' i) + p' i ≤ latency j (x' j) + p' j := by
      intro i j hi
      by_cases hij : i = j
      · subst hij; exact le_rfl
      let g : ℝ → ℝ := fun t =>
        pot (Function.update (Function.update x' i (x' i - t)) j (x' j + t))
      have hsum_inv : ∀ t,
          ∑ k, Function.update (Function.update x' i (x' i - t)) j (x' j + t) k = X :=
        fun t => sum_update_sub_add_eq x' hij t
      have hg_eq : ∀ t, g t = (termPot i (x' i - t) + termPot j (x' j + t)) +
          ((∑ k ∈ (Finset.univ.erase j).erase i, termPot k (x' k)) - uPot X) := by
        intro t
        simp only [g, pot, hsum_inv t]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        have hi_er : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
        rw [← Finset.add_sum_erase _ _ hi_er]
        have hr : ∑ k ∈ (Finset.univ.erase j).erase i,
            termPot k (Function.update (Function.update x' i (x' i - t)) j (x' j + t) k) =
            ∑ k ∈ (Finset.univ.erase j).erase i, termPot k (x' k) :=
          Finset.sum_congr rfl fun k hk => by
            rw [Function.update_of_ne (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1,
              Function.update_of_ne (Finset.mem_erase.mp hk).1]
        simp only [Function.update_self, Function.update_of_ne hij, hr]
        ring
      have hg_deriv : HasDerivAt g
          ((latency j (x' j) + p' j) - (latency i (x' i) + p' i)) 0 := by
        simp only [funext hg_eq]
        have htot := ((hterm_sub i (x' i)).add (hterm_add j (x' j))).add_const
          ((∑ k ∈ (Finset.univ.erase j).erase i, termPot k (x' k)) - uPot X)
        have heff_i : effExt i (x' i) = latency i (x' i) + p' i := by
          simp [effExt, max_eq_right hi.le]
        have heff_j : effExt j (x' j) = latency j (x' j) + p' j := by
          simp [effExt, max_eq_right (hx'Feas.1 j)]
        rw [heff_i, heff_j] at htot
        convert htot using 1
        ring
      have h0 : 0 ≤ (latency j (x' j) + p' j) - (latency i (x' i) + p' i) := by
        refine nonneg_of_hasDerivAt_of_forall_pos hi hg_deriv fun t ht0 hti => ?_
        have hg0 : g 0 = pot x' := by simp only [g, sub_zero, add_zero, Function.update_eq_self]
        rw [hg0]
        exact hx'min _ ⟨fun k => nonneg_update_sub_add hx'Feas.1 ht0.le hti.le k,
          (hsum_inv t).trans_le hx'Feas.2⟩
      linarith
    -- (3) Show uDeriv X ≤ latency j (x' j) + p' j for all j (both X < B and X = B):
    have hall_ge : ∀ j, uDeriv X ≤ latency j (x' j) + p' j := by
      rcases hx'Feas.2.lt_or_eq with hlt_B | heq_B
      · intro j
        let g : ℝ → ℝ := fun t => pot (Function.update x' j (x' j + t))
        have hg_eq : ∀ t, g t = termPot j (x' j + t) +
            (∑ k ∈ Finset.univ.erase j, termPot k (x' k)) - uPot (X + t) := by
          intro t
          simp only [g, pot, X, hterm_upd, sum_update_add_eq x' j t]
        have hg_deriv : HasDerivAt g ((latency j (x' j) + p' j) - uDeriv X) 0 := by
          simp only [funext hg_eq]
          have hd2 : HasDerivAt (fun t => uPot (X + t)) (uDerivExt X) 0 := by
            simpa only [add_zero] using (huPot_deriv (X + 0)).comp_const_add X 0
          have htot :=
            ((hterm_add j (x' j)).add_const (∑ k ∈ Finset.univ.erase j, termPot k (x' k))).sub hd2
          have heff_j : effExt j (x' j) = latency j (x' j) + p' j := by
            simp [effExt, max_eq_right (hx'Feas.1 j)]
          have hud_X : uDerivExt X = uDeriv X := by simp [uDerivExt, max_eq_right hX0]
          rw [heff_j, hud_X] at htot
          convert htot using 1
        have h0 : 0 ≤ (latency j (x' j) + p' j) - uDeriv X := by
          refine nonneg_of_hasDerivAt_of_forall_pos (sub_pos.mpr hlt_B) hg_deriv
            fun t ht0 htB => ?_
          simp only [g, add_zero, Function.update_eq_self]
          exact hx'min _ (isFeasiblePricedFlow_update_add hx'Feas ht0.le (by linarith))
        linarith
      · -- Boundary case X = B = (∑ k, b k) + 1: some link i₀ satisfies b i₀ < x' i₀!
        have hex_i₀ : ∃ i₀, b i₀ < x' i₀ := by
          by_contra hle_all
          push Not at hle_all
          have hsum_le : ∑ k, x' k ≤ ∑ k, b k := Finset.sum_le_sum fun k _ => hle_all k
          simp only [B] at heq_B
          linarith
        obtain ⟨i₀, hi₀_gt⟩ := hex_i₀
        have hbi₀_pos : 0 < b i₀ := (hb i₀).1
        have hxi₀_pos : 0 < x' i₀ := hbi₀_pos.trans hi₀_gt
        have hbi₀_le_X : b i₀ ≤ X := by
          have h1 : b i₀ ≤ ∑ k, b k :=
            Finset.single_le_sum (fun k _ => (hb k).1.le) (Finset.mem_univ i₀)
          change ∑ k, x' k = B at heq_B
          simp only [B, X] at heq_B ⊢
          linarith
        have hi₀_ge : uDeriv X ≤ latency i₀ (x' i₀) + p' i₀ := by
          linarith [(hb i₀).2, hp'0 i₀, hu.deriv_le hbi₀_pos.le hbi₀_le_X,
            hl.latency_le i₀ hbi₀_pos.le hi₀_gt.le]
        exact fun j => hi₀_ge.trans (hswap i₀ j hxi₀_pos)
    refine ⟨x', hx'Feas.1, fun i hi => le_antisymm (hact_le i hi) (hall_ge i), hall_ge⟩
  · rw [not_nonempty_iff] at hne
    exact ⟨0, fun i => hne.elim i, fun i => hne.elim i, fun i => hne.elim i⟩

/-- **Elastic downward-flow markup bound**: `x i * latencyDeriv i (x i) ≤ p i` at any elastic
Oligopoly Equilibrium. -/
theorem IsElasticOligopolyEquilibrium.mul_latencyDeriv_le_price {Link : Type*} [Fintype Link]
    [DecidableEq Link] {u uDeriv uSecondDeriv : ℝ → ℝ}
    (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv)
    {latency latencyDeriv : Link → ℝ → ℝ} (hl : SmoothConvexLatencies latency latencyDeriv)
    {p x : Link → ℝ} (hoe : IsElasticOligopolyEquilibrium uDeriv latency p x) (i : Link) :
    x i * latencyDeriv i (x i) ≤ p i := by
  rcases (hoe.2.1.1 i).eq_or_lt with hxi0 | hxi
  · rw [← hxi0, zero_mul]; exact hoe.1 i
  let X : ℝ := ∑ k, x k
  have hX_ge_xi : x i ≤ X :=
    Finset.single_le_sum (fun k _ => hoe.2.1.1 k) (Finset.mem_univ i)
  have hX_pos : 0 < X := hxi.trans_le hX_ge_xi
  let cStar : ℝ := uDeriv X
  have hi_eff : latency i (x i) + p i = cStar := hoe.2.1.2.1 i hxi
  -- Subcase 1: uDeriv is flat immediately below X (∃ δ₀ ∈ (0, x i), uDeriv (X - δ₀) = cStar):
  by_cases hflat_u : ∃ δ₀, 0 < δ₀ ∧ δ₀ < x i ∧ uDeriv (X - δ₀) = cStar
  · obtain ⟨δ₀, hδ₀, hδ₀x, hud_flat⟩ := hflat_u
    refine mul_deriv_le_of_forall_pos_sub hxi (hl.hasDerivAt i (x i) hxi.le) fun η hη => ?_
    let δ : ℝ := min (η / 2) (δ₀ / 2)
    have hδ0 : 0 < δ := lt_min (half_pos hη) (half_pos hδ₀)
    have hδη : δ < η := (min_le_left _ _).trans_lt (half_lt_self hη)
    have hδ_le_δ₀ : δ ≤ δ₀ := (min_le_right _ _).trans (half_le_self hδ₀.le)
    have hδx : δ < x i := hδ_le_δ₀.trans_lt hδ₀x
    have hud_eq : uDeriv (X - δ) = cStar := by
      refine le_antisymm ?_ (hu.deriv_le (by linarith) (by linarith))
      rw [← hud_flat]
      exact hu.deriv_le (by linarith) (by linarith)
    let x' : Link → ℝ := Function.update x i (x i - δ)
    let p' : ℝ := cStar - latency i (x i - δ)
    have hlat_le : latency i (x i - δ) ≤ latency i (x i) :=
      hl.latency_le i (by linarith) (by linarith)
    have hp'0 : 0 ≤ p' := by simp only [p']; linarith [hoe.1 i]
    have hx'sum : ∑ k, x' k = X - δ := by
      simpa only [x', X, sub_eq_add_neg] using sum_update_add_eq x i (-δ)
    have hw' : IsElasticPricedWardrop uDeriv latency (Function.update p i p') x' := by
      refine ⟨fun k => ?_, fun k hxk => ?_, fun k => ?_⟩
      · simp only [x', Function.update_apply]; split_ifs <;> linarith [hoe.2.1.1 k]
      · rw [hx'sum, hud_eq]
        by_cases hki : k = i
        · subst hki; simp [x', p']
        · simp only [x', Function.update_of_ne hki] at hxk ⊢
          exact hoe.2.1.2.1 k hxk
      · rw [hx'sum, hud_eq]
        by_cases hki : k = i
        · subst hki; simp [x', p']
        · simp only [x', Function.update_of_ne hki]
          exact hoe.2.1.2.2 k
    have hbest := hoe.2.2 i p' x' hp'0 hw'
    simp only [x', p', Function.update_self, ← hi_eff] at hbest
    exact ⟨δ, hδ0, hδη, hδx, div_mul_le_of_mul_le hδ0 (by nlinarith)⟩
  -- Subcase 2: some competitor q ≠ i with effective cost cStar is flat above x q:
  let Q0 : Finset Link := Finset.univ.filter fun q => q ≠ i ∧ latency q (x q) + p q = cStar
  by_cases hflat_q : ∃ q ∈ Q0, ∃ δ₀ > 0, latency q (x q + δ₀) = latency q (x q)
  · obtain ⟨q, hqQ0, δ₀, hδ₀, hlat_flat⟩ := hflat_q
    have hqi : q ≠ i := (Finset.mem_filter.mp hqQ0).2.1
    have hq_cost : latency q (x q) + p q = cStar := (Finset.mem_filter.mp hqQ0).2.2
    refine mul_deriv_le_of_forall_pos_sub hxi (hl.hasDerivAt i (x i) hxi.le) fun η hη => ?_
    let δ : ℝ := min (min (η / 2) (x i / 2)) (δ₀ / 2)
    have hδ0 : 0 < δ := lt_min (lt_min (half_pos hη) (half_pos hxi)) (half_pos hδ₀)
    have hδη : δ < η := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hη)
    have hδx : δ < x i := ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hxi)
    have hδ_le_δ₀ : δ ≤ δ₀ := (min_le_right _ _).trans (half_le_self hδ₀.le)
    have hlat_q_eq : latency q (x q + δ) = latency q (x q) := by
      refine le_antisymm ?_ (hl.latency_le q (hoe.2.1.1 q) (by linarith))
      rw [← hlat_flat]
      exact hl.latency_le q (by linarith [hoe.2.1.1 q]) (by linarith)
    let x' : Link → ℝ := Function.update (Function.update x i (x i - δ)) q (x q + δ)
    let p' : ℝ := cStar - latency i (x i - δ)
    have hlat_i_le : latency i (x i - δ) ≤ latency i (x i) :=
      hl.latency_le i (by linarith) (by linarith)
    have hp'0 : 0 ≤ p' := by simp only [p']; linarith [hoe.1 i]
    have hx'sum : ∑ k, x' k = X := sum_update_sub_add_eq x hqi.symm δ
    have hcost_eq : ∀ k, k = q ∨ k = i →
        latency k (x' k) + Function.update p i p' k = cStar := by
      rintro k (rfl | rfl)
      · simp only [x', Function.update_self, Function.update_of_ne hqi, hlat_q_eq]
        exact hq_cost
      · simp only [x', p', Function.update_of_ne hqi.symm, Function.update_self, add_sub_cancel]
    have hw' : IsElasticPricedWardrop uDeriv latency (Function.update p i p') x' := by
      refine ⟨fun k => nonneg_update_sub_add hoe.2.1.1 hδ0.le hδx.le k,
        fun k hxk => ?_, fun k => ?_⟩ <;> rw [hx'sum] <;> by_cases hk : k = q ∨ k = i
      · exact hcost_eq k hk
      · push Not at hk
        simp only [x', Function.update_of_ne hk.1, Function.update_of_ne hk.2] at hxk ⊢
        exact hoe.2.1.2.1 k hxk
      · exact (hcost_eq k hk).ge
      · push Not at hk
        simp only [x', Function.update_of_ne hk.1, Function.update_of_ne hk.2]
        exact hoe.2.1.2.2 k
    have hbest := hoe.2.2 i p' x' hp'0 hw'
    simp only [x', p', Function.update_of_ne hqi.symm, Function.update_self, ← hi_eff] at hbest
    exact ⟨δ, hδ0, hδη, hδx, div_mul_le_of_mul_le hδ0 (by nlinarith)⟩
  -- Subcase 3: uDeriv strictly increases below X and every q ∈ Q0 strictly increases above x q:
  push Not at hflat_u hflat_q
  refine mul_deriv_le_of_forall_pos_sub hxi (hl.hasDerivAt i (x i) hxi.le) fun η hη => ?_
  let rStep : ℝ := min 1 (min η (x i) / (2 * ((Q0.card : ℝ) + 1)))
  have hrStep_pos : 0 < rStep :=
    lt_min zero_lt_one (div_pos (lt_min hη hxi) (by positivity))
  have hrStep_lt_xi : rStep < x i := by
    have h1 : rStep ≤ min η (x i) / (2 * ((Q0.card : ℝ) + 1)) := min_le_right _ _
    have h2 : min η (x i) / (2 * ((Q0.card : ℝ) + 1)) ≤ min η (x i) / 2 :=
      div_le_div_of_nonneg_left (lt_min hη hxi).le two_pos
        (by linarith [Nat.cast_nonneg (α := ℝ) Q0.card])
    exact (h1.trans h2).trans_lt ((half_lt_self (lt_min hη hxi)).trans_le (min_le_right _ _))
  have hu_inc_pos : 0 < uDeriv (X - rStep) - cStar := by
    have hge : cStar ≤ uDeriv (X - rStep) := hu.deriv_le (by linarith) (by linarith)
    exact sub_pos.mpr (hge.lt_of_ne (hflat_u rStep hrStep_pos hrStep_lt_xi).symm)
  let remSet : Finset Link := Finset.univ.filter fun r => r ≠ i ∧ r ∉ Q0
  have hrem_gt : ∀ r ∈ remSet, cStar < latency r (x r) + p r := fun r hr =>
    (hoe.2.1.2.2 r).lt_of_ne fun heq => (Finset.mem_filter.mp hr).2.2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ r, (Finset.mem_filter.mp hr).2.1, heq.symm⟩)
  have hex_mu : ∃ μ > 0, μ < uDeriv (X - rStep) - cStar ∧
      (∀ q ∈ Q0, μ < latency q (x q + rStep) - latency q (x q)) ∧
      (∀ r ∈ remSet, cStar + μ ≤ latency r (x r) + p r) := by
    let bU : ℝ := (uDeriv (X - rStep) - cStar) / 2
    have hbU_pos : 0 < bU := half_pos hu_inc_pos
    have hex_bQ : ∃ bQ > 0, ∀ q ∈ Q0, bQ < latency q (x q + rStep) - latency q (x q) := by
      by_cases hQ_ne : Q0.Nonempty
      · let mQ : ℝ := Q0.inf' hQ_ne fun q => latency q (x q + rStep) - latency q (x q)
        have hmQ_pos : 0 < mQ := by
          rw [Finset.lt_inf'_iff]
          intro q hq
          have hge := hl.latency_le q (hoe.2.1.1 q) (show x q ≤ x q + rStep by linarith)
          exact sub_pos.mpr (lt_of_le_of_ne hge (Ne.symm (hflat_q q hq rStep hrStep_pos)))
        refine ⟨mQ / 2, half_pos hmQ_pos, fun q hq => ?_⟩
        exact (half_lt_self hmQ_pos).trans_le (Finset.inf'_le _ hq)
      · exact ⟨1, zero_lt_one, fun q hq => False.elim (hQ_ne ⟨q, hq⟩)⟩
    obtain ⟨bQ, hbQ_pos, hbQ_lt⟩ := hex_bQ
    by_cases hrem_ne : remSet.Nonempty
    · let mR : ℝ := remSet.inf' hrem_ne fun r => latency r (x r) + p r - cStar
      have hmR_pos : 0 < mR := by
        rw [Finset.lt_inf'_iff]; intro r hr; linarith [hrem_gt r hr]
      let μ₀ : ℝ := min (min bU bQ) mR
      refine ⟨μ₀, lt_min (lt_min hbU_pos hbQ_pos) hmR_pos, ?_, fun q hq => ?_, fun r hr => ?_⟩
      · exact ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hu_inc_pos)
      · exact ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (hbQ_lt q hq)
      · have h1 : μ₀ ≤ mR := min_le_right _ _
        have h2 : mR ≤ latency r (x r) + p r - cStar :=
          Finset.inf'_le (fun s => latency s (x s) + p s - cStar) hr
        linarith
    · let μ₀ : ℝ := min bU bQ
      refine ⟨μ₀, lt_min hbU_pos hbQ_pos, (min_le_left _ _).trans_lt (half_lt_self hu_inc_pos),
        fun q hq => (min_le_right _ _).trans_lt (hbQ_lt q hq),
        fun r hr => False.elim (hrem_ne ⟨r, hr⟩)⟩
  obtain ⟨μ, hμ0, hμ_u, hμ_Q, hμ_rem⟩ := hex_mu
  -- Choose step₀ ∈ (0, rStep] with uDeriv (X - step₀) - cStar = μ by IVT:
  have hex_s0 : ∃ s0, 0 < s0 ∧ s0 ≤ rStep ∧ uDeriv (X - s0) = cStar + μ := by
    have hsub_cont : Continuous (fun t : ℝ => X - t) :=
      continuous_sub.comp (continuous_const.prodMk continuous_id)
    have hg_cont : ContinuousOn (fun t => uDeriv (X - t) - cStar) (Set.Icc 0 rStep) := by
      refine (hu.continuousOn_deriv.comp hsub_cont.continuousOn fun t ht => ?_).sub
        continuousOn_const
      rw [Set.mem_Icc] at ht
      exact Set.mem_Ici.mpr (by linarith [ht.2, hrStep_lt_xi, hX_ge_xi])
    obtain ⟨s0, hs0_pos, hs0_le, hs0_eq⟩ := exists_pos_le_of_continuousOn_Icc hrStep_pos hμ0
      hg_cont (by simp [cStar]) hμ_u.le
    exact ⟨s0, hs0_pos, hs0_le, by linarith⟩
  obtain ⟨step0, hstep0_pos, hstep0_le, hud_s0⟩ := hex_s0
  -- Choose step q ∈ (0, rStep) for each q ∈ Q0 via exists_pos_step_add_eq:
  have hex_dq : ∀ q ∈ Q0, ∃ t, 0 < t ∧ t < rStep ∧
      latency q (x q + t) - latency q (x q) = μ := by
    intro q hq
    have hr1 : rStep ≤ 1 := min_le_left _ _
    have hle1 : latency q (x q + rStep) ≤ latency q (x q + 1) :=
      hl.latency_le q (by linarith [hoe.2.1.1 q]) (by linarith)
    obtain ⟨t, ht0, _, hteq, htsmall⟩ := exists_pos_step_add_eq
      (hl.monotoneOn q) (hl.continuousOn q) (hoe.2.1.1 q) hμ0 (by linarith [hμ_Q q hq])
    exact ⟨t, ht0, htsmall rStep hrStep_pos (hμ_Q q hq), hteq⟩
  choose! step hstep_pos hstep_lt hstep_eq using hex_dq
  let Δ : ℝ := step0 + ∑ q ∈ Q0, step q
  have hΔ0 : 0 < Δ :=
    add_pos_of_pos_of_nonneg hstep0_pos (Finset.sum_nonneg fun q hq => (hstep_pos q hq).le)
  have hΔ_lt_min : Δ < min η (x i) := by
    have hsum_le : ∑ q ∈ Q0, step q ≤ Q0.card * rStep :=
      (Finset.sum_le_card_nsmul Q0 step rStep fun q hq => (hstep_lt q hq).le).trans_eq
        (nsmul_eq_mul _ _)
    have hΔ_le : Δ ≤ ((Q0.card : ℝ) + 1) * rStep := by simp only [Δ]; linarith
    have hr_le : rStep ≤ min η (x i) / (2 * ((Q0.card : ℝ) + 1)) := min_le_right _ _
    have hpos_c : 0 < (Q0.card : ℝ) + 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hr_le hpos_c.le
    rw [mul_div_two_mul hpos_c.ne'] at hmul
    exact (hΔ_le.trans hmul).trans_lt (half_lt_self (lt_min hη hxi))
  have hΔη : Δ < η := hΔ_lt_min.trans_le (min_le_left _ _)
  have hΔx : Δ < x i := hΔ_lt_min.trans_le (min_le_right _ _)
  let x' : Link → ℝ := fun k =>
    if k = i then x i - Δ else if k ∈ Q0 then x k + step k else x k
  let p' : ℝ := cStar + μ - latency i (x i - Δ)
  have hi_not_Q0 : i ∉ Q0 := fun hiQ => (Finset.mem_filter.mp hiQ).2.1 rfl
  have hlat_i_le : latency i (x i - Δ) ≤ latency i (x i) :=
    hl.latency_le i (by linarith) (by linarith)
  have hp'0 : 0 ≤ p' := by simp only [p', ← hi_eff]; linarith [hoe.1 i]
  have hx'sum : ∑ k, x' k = X - step0 := by
    have h1 : ∀ k, x' k = x k + ((if k = i then -Δ else 0) + if k ∈ Q0 then step k else 0) :=
      fun k => by
        by_cases hki : k = i
        · subst hki; simp [x', hi_not_Q0, sub_eq_add_neg]
        · by_cases hkQ : k ∈ Q0 <;> simp [x', hki, hkQ]
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Finset.sum_ite_mem, Finset.univ_inter, Δ, X]
    ring
  have hQ_cost : ∀ k ∈ Q0, latency k (x' k) + Function.update p i p' k = cStar + μ :=
    fun k hkQ => by
      have hki : k ≠ i := (Finset.mem_filter.mp hkQ).2.1
      have hkq_cost : latency k (x k) + p k = cStar := (Finset.mem_filter.mp hkQ).2.2
      simp only [x', hki, hkQ, ↓reduceIte, Function.update_of_ne hki]
      linarith [hstep_eq k hkQ]
  have hw' : IsElasticPricedWardrop uDeriv latency (Function.update p i p') x' := by
    refine ⟨fun k => ?_, fun k hxk => ?_, fun k => ?_⟩
    · simp only [x']
      split_ifs with hk1 hk2
      · linarith
      · linarith [hoe.2.1.1 k, hstep_pos k hk2]
      · exact hoe.2.1.1 k
    all_goals
      rw [hx'sum, hud_s0]
      by_cases hki : k = i
      · subst hki; simp [x', p']
      by_cases hkQ : k ∈ Q0
    · exact hQ_cost k hkQ
    · simp only [x', hki, hkQ, ↓reduceIte] at hxk
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hki, hoe.2.1.2.1 k hxk⟩) hkQ
    · exact (hQ_cost k hkQ).ge
    · simp only [x', hki, hkQ, ↓reduceIte, Function.update_of_ne hki]
      exact hμ_rem k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hki, hkQ⟩)
  have hbest := hoe.2.2 i p' x' hp'0 hw'
  have hi_prod : p' * x' i =
      (p i + μ + (latency i (x i) - latency i (x i - Δ))) * (x i - Δ) := by
    simp only [p', x', ↓reduceIte, ← hi_eff]
    ring
  rw [hi_prod] at hbest
  have hpos_mu : 0 ≤ μ * (x i - Δ) := mul_nonneg hμ0.le (by linarith)
  exact ⟨Δ, hΔ0, hΔη, hΔx, div_mul_le_of_mul_le hΔ0 (by nlinarith)⟩

/-- **Elastic zero-revenue OE optimality**: if `p i * x i = 0` on every link at an elastic Oligopoly
Equilibrium and an elastic social optimum exists, then `x` is an elastic social optimum. -/
theorem IsElasticOligopolyEquilibrium.isElasticSocialOptimum_of_forall_mul_eq_zero
    {Link : Type*} [Fintype Link] [DecidableEq Link] {u uDeriv uSecondDeriv : ℝ → ℝ}
    (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv)
    {latency latencyDeriv : Link → ℝ → ℝ} (hl : SmoothConvexLatencies latency latencyDeriv)
    {p x xS : Link → ℝ} (hoe : IsElasticOligopolyEquilibrium uDeriv latency p x)
    (hopt : IsElasticSocialOptimum u latency xS) (hzero : ∀ i, p i * x i = 0) :
    IsElasticSocialOptimum u latency x := by
  by_cases hne : Nonempty Link
  · rcases le_or_gt (uDeriv 0) 0 with hu0_le | hu0_pos
    · -- All flows y ≥ 0 have u (∑ y) ≤ 0, while 0 ≤ elasticSocialSurplus u latency x:
      refine ⟨hoe.2.1.1, fun y hy0 => ?_⟩
      have hY0 : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ => hy0 i
      have huY : u (∑ i, y i) ≤ 0 := by
        have h1 := hu.le_add_deriv_mul le_rfl hY0
        rw [hu.zero_at_zero, sub_zero, zero_add] at h1
        exact h1.trans (mul_nonpos_of_nonpos_of_nonneg hu0_le hY0)
      have hlatY : 0 ≤ ∑ i, latency i (y i) * y i :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hl.latency_nonneg i (hy0 i)) (hy0 i)
      have hy_np : elasticSocialSurplus u latency y ≤ 0 := by
        simp only [elasticSocialSurplus]; linarith
      exact hy_np.trans (hoe.2.1.socialSurplus_nonneg hu hoe.1)
    -- Show latency j (x j) = 0 and x j * latencyDeriv j (x j) = 0 for all j:
    have hlat_z : ∀ j, latency j (x j) = 0 := fun j => by
      rcases (hl.latency_nonneg j (hoe.2.1.1 j)).eq_or_lt with hz | hpos
      · exact hz.symm
      · obtain ⟨hxj, hdj⟩ := hl.deriv_pos_of_latency_pos j (hoe.2.1.1 j) hpos
        have hpj : 0 < p j := (mul_pos hxj hdj).trans_le (hoe.mul_latencyDeriv_le_price hu hl j)
        linarith [mul_pos hpj hxj, hzero j]
    have hmul_z : ∀ j, x j * latencyDeriv j (x j) = 0 := fun j => by
      rcases (hoe.2.1.1 j).eq_or_lt with hxj0 | hxj_pos
      · simp [← hxj0]
      · rw [(hl.latency_eq_zero_iff_deriv_eq_zero j hxj_pos).mp (hlat_z j), mul_zero]
    -- Show ∃ j₀, 0 < x j₀ (else x = 0, p ≥ uDeriv 0 > 0, and undercutting to uDeriv 0 / 2 profits):
    have hex_pos : ∃ j₀, 0 < x j₀ := by
      by_contra! hall
      have hx0 : ∀ k, x k = 0 := fun k => le_antisymm (hall k) (hoe.2.1.1 k)
      have hp_ge : ∀ k, uDeriv 0 ≤ p k := fun k => by
        simpa only [hx0, Finset.sum_const_zero, hl.zero_at_zero k, zero_add] using hoe.2.1.2.2 k
      obtain ⟨i₀⟩ := hne
      let p' : ℝ := uDeriv 0 / 2
      have hp'0 : ∀ k, 0 ≤ Function.update p i₀ p' k := fun k => by
        by_cases hki : k = i₀
        · subst hki; simp only [Function.update_self, p']; linarith
        · simp only [Function.update_of_ne hki]; exact hoe.1 k
      obtain ⟨x', hw'⟩ := exists_isElasticPricedWardrop_of_socialOptimum hu hl hopt _ hp'0
      have hxi₀_pos : 0 < x' i₀ := by
        by_contra! hle0
        have hxi₀0 : x' i₀ = 0 := le_antisymm hle0 (hw'.1 i₀)
        have hud_le : uDeriv (∑ k, x' k) ≤ uDeriv 0 / 2 := by
          simpa only [hxi₀0, hl.zero_at_zero i₀, Function.update_self, p', zero_add] using
            hw'.2.2 i₀
        obtain ⟨q, hxq⟩ : ∃ q, 0 < x' q := by
          by_contra! hall'
          rw [Finset.sum_eq_zero fun q _ => le_antisymm (hall' q) (hw'.1 q)] at hud_le
          linarith
        have hqi₀ : q ≠ i₀ := fun heq => by subst heq; linarith
        have hq_eff := hw'.2.1 q hxq
        simp only [Function.update_of_ne hqi₀] at hq_eff
        linarith [hp_ge q, hl.latency_nonneg q (hw'.1 q)]
      have hp'_pos : 0 < p' := half_pos hu0_pos
      have hbest := hoe.2.2 i₀ p' x' hp'_pos.le hw'
      rw [hzero i₀] at hbest
      linarith [mul_pos hp'_pos hxi₀_pos]
    obtain ⟨j₀, hxj₀⟩ := hex_pos
    have hpj₀ : p j₀ = 0 := (mul_eq_zero.mp (hzero j₀)).resolve_right hxj₀.ne'
    have hud_zero : uDeriv (∑ k, x k) = 0 := by linarith [hoe.2.1.2.1 j₀ hxj₀, hlat_z j₀]
    exact isElasticSocialOptimum_of_kkt hu hl hoe.2.1.1
      (fun i => by rw [hud_zero, hlat_z i, hmul_z i, add_zero])
      (fun i _ => by rw [hud_zero, hlat_z i, hmul_z i, add_zero])
  · rw [not_nonempty_iff] at hne
    exact ⟨hoe.2.1.1, fun y _ => by simp [elasticSocialSurplus]⟩

/-- **Interior positivity for elastic Oligopoly Equilibria**: if some link has `0 < p i₀ * x i₀` and
an elastic social optimum exists, then `0 < p j` and `0 < x j` on **every** link `j`. -/
theorem IsElasticOligopolyEquilibrium.price_pos_and_flow_pos {Link : Type*} [Fintype Link]
    [DecidableEq Link] {u uDeriv uSecondDeriv : ℝ → ℝ}
    (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv)
    {latency latencyDeriv : Link → ℝ → ℝ} (hl : SmoothConvexLatencies latency latencyDeriv)
    {p x xS : Link → ℝ} (hoe : IsElasticOligopolyEquilibrium uDeriv latency p x)
    (hopt : IsElasticSocialOptimum u latency xS)
    (hpos : ∃ i₀, 0 < p i₀ * x i₀) (j : Link) :
    0 < p j ∧ 0 < x j := by
  obtain ⟨i₀, hi₀⟩ := hpos
  have hpi₀ : 0 < p i₀ := pos_of_mul_pos_left hi₀ (hoe.2.1.1 i₀)
  have hxi₀ : 0 < x i₀ := pos_of_mul_pos_right hi₀ (hoe.1 i₀)
  let X : ℝ := ∑ k, x k
  let K : ℝ := uDeriv X
  have hi₀_eff : latency i₀ (x i₀) + p i₀ = K := hoe.2.1.2.1 i₀ hxi₀
  have hK_pos : 0 < K := by linarith [hl.latency_nonneg i₀ hxi₀.le]
  have hprod_pos : 0 < p j * x j := by
    refine lt_of_le_of_ne (mul_nonneg (hoe.1 j) (hoe.2.1.1 j)) fun hzero_j => ?_
    let p' : ℝ := K / 2
    have hp'0 : ∀ k, 0 ≤ Function.update p j p' k := fun k => by
      by_cases hkj : k = j
      · subst hkj; simp only [Function.update_self, p']; linarith
      · simp only [Function.update_of_ne hkj]; exact hoe.1 k
    obtain ⟨x', hw'⟩ := exists_isElasticPricedWardrop_of_socialOptimum hu hl hopt _ hp'0
    have hxj'_pos : 0 < x' j := by
      by_contra hle0
      have hxj'0 : x' j = 0 := le_antisymm (not_lt.mp hle0) (hw'.1 j)
      have hud_le : uDeriv (∑ k, x' k) ≤ K / 2 := by
        have h1 := hw'.2.2 j
        simp only [hxj'0, hl.zero_at_zero j, Function.update_self, p', zero_add] at h1
        exact h1
      -- Hence uDeriv (∑ x') < K = uDeriv X, so X < ∑ x' by AntitoneOn!
      have hX_lt_X' : X < ∑ k, x' k := by
        by_contra hge
        push Not at hge
        have hant := hu.deriv_le (Finset.sum_nonneg fun k _ => hw'.1 k) hge
        change K ≤ uDeriv (∑ k, x' k) at hant
        linarith
      -- Yet every active link q ≠ j has effective cost ≤ K / 2 < K, forcing x' q ≤ x q:
      have hle_each : ∀ q, x' q ≤ x q := fun q => by
        rcases (hw'.1 q).eq_or_lt with h0 | hxq_pos
        · rw [← h0]; exact hoe.2.1.1 q
        · have hqj : q ≠ j := fun heq => by subst heq; linarith
          have hq_eff := hw'.2.1 q hxq_pos
          simp only [Function.update_of_ne hqj] at hq_eff
          have hq_old : K ≤ latency q (x q) + p q := hoe.2.1.2.2 q
          have hlat_lt : latency q (x' q) < latency q (x q) := by linarith
          by_contra hgt_q
          push Not at hgt_q
          have hmono := hl.latency_le q (hoe.2.1.1 q) hgt_q.le
          linarith
      have hsum_le : ∑ k, x' k ≤ X := Finset.sum_le_sum fun k _ => hle_each k
      linarith
    have hp'_pos : 0 < p' := half_pos hK_pos
    have hbest := hoe.2.2 j p' x' hp'_pos.le hw'
    rw [← hzero_j] at hbest
    linarith [mul_pos hp'_pos hxj'_pos]
  exact ⟨pos_of_mul_pos_left hprod_pos (hoe.2.1.1 j),
    pos_of_mul_pos_right hprod_pos (hoe.1 j)⟩

/-- **Elastic zero-derivative competitor markup bound**: if `0 < p k * x k` on some link and some
competitor `q ≠ i` has `latencyDeriv q (x q) = 0`, then `p i = x i * latencyDeriv i (x i)`. -/
theorem IsElasticOligopolyEquilibrium.price_eq_mul_deriv_of_comp_deriv_zero {Link : Type*}
    [Fintype Link] [DecidableEq Link] {u uDeriv uSecondDeriv : ℝ → ℝ}
    (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv)
    {latency latencyDeriv : Link → ℝ → ℝ} (hl : SmoothConvexLatencies latency latencyDeriv)
    {p x xS : Link → ℝ} (hoe : IsElasticOligopolyEquilibrium uDeriv latency p x)
    (hopt : IsElasticSocialOptimum u latency xS)
    (hpos : ∃ i₀, 0 < p i₀ * x i₀) {i q : Link}
    (hqi : q ≠ i) (hq_deriv : latencyDeriv q (x q) = 0) :
    p i = x i * latencyDeriv i (x i) := by
  refine le_antisymm ?_ (hoe.mul_latencyDeriv_le_price hu hl i)
  obtain ⟨hpi, hxi⟩ := hoe.price_pos_and_flow_pos hu hl hopt hpos i
  obtain ⟨hpq, hxq⟩ := hoe.price_pos_and_flow_pos hu hl hopt hpos q
  have hlat_q0 : latency q (x q) = 0 :=
    (hl.latency_eq_zero_iff_deriv_eq_zero q hxq).mpr hq_deriv
  let X : ℝ := ∑ k, x k
  let K : ℝ := uDeriv X
  have hi_eff : latency i (x i) + p i = K := hoe.2.1.2.1 i hxi
  have hq_eff : latency q (x q) + p q = K := hoe.2.1.2.1 q hxq
  have hp_le : p i ≤ x i * latencyDeriv i (x i) + 0 := by
    refine le_mul_deriv_add_of_forall_pos_add (hl.hasDerivAt i (x i) hxi.le)
      fun ε η _ hη => ?_
    obtain ⟨δ, hδ0, hδη, hδxq, hlat_i_lt, hlat_q_sub⟩ :=
      hl.exists_zero_swap_step (K := K) i hxi.le hxq hlat_q0 (by linarith) hη
    let x' : Link → ℝ := Function.update (Function.update x q (x q - δ)) i (x i + δ)
    let p' : ℝ := K - latency i (x i + δ)
    have hp'0 : 0 ≤ p' := by simp only [p']; linarith
    have hx'sum : ∑ k, x' k = X := sum_update_sub_add_eq x hqi δ
    have hcost_K : ∀ k, latency k (x' k) + Function.update p i p' k = K := fun k => by
      by_cases hki : k = i
      · subst hki; simp [x', p']
      · by_cases hkq : k = q
        · subst hkq
          simp only [x', Function.update_of_ne hqi, Function.update_self, hlat_q_sub]
          linarith
        · simp only [x', Function.update_of_ne hki, Function.update_of_ne hkq]
          exact hoe.2.1.2.1 k (hoe.price_pos_and_flow_pos hu hl hopt hpos k).2
    have hw' : IsElasticPricedWardrop uDeriv latency (Function.update p i p') x' :=
      ⟨fun k => nonneg_update_sub_add hoe.2.1.1 hδ0.le hδxq.le k,
        fun k _ => by rw [hx'sum, hcost_K k], fun k => by rw [hx'sum, hcost_K k]⟩
    have hbest := hoe.2.2 i p' x' hp'0 hw'
    simp only [x', p', Function.update_self, ← hi_eff] at hbest
    have hmul_le : p i * δ ≤ (latency i (x i + δ) - latency i (x i)) * (x i + δ) := by nlinarith
    refine ⟨δ, hδ0, hδη, ?_⟩
    have hdiv : p i ≤ ((latency i (x i + δ) - latency i (x i)) / δ) * (x i + δ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ0]
      linarith
    linarith
  linarith

/-- **Elastic positive-derivative competitor markup bound**: when every competitor `q ≠ i` has
`0 < latencyDeriv q (x q)`,
`(p i - x i * latencyDeriv i (x i)) * (1 + (-uSecondDeriv X) * ∑ q ∈ univ.erase i,
(latencyDeriv q (x q))⁻¹) ≤ (-uSecondDeriv X) * x i` (where `X = ∑ k, x k`). -/
theorem IsElasticOligopolyEquilibrium.price_sub_mul_deriv_le_elastic {Link : Type*} [Fintype Link]
    [DecidableEq Link] {u uDeriv uSecondDeriv : ℝ → ℝ}
    (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv)
    {latency latencyDeriv : Link → ℝ → ℝ} (hl : SmoothConvexLatencies latency latencyDeriv)
    {p x xS : Link → ℝ} (hoe : IsElasticOligopolyEquilibrium uDeriv latency p x)
    (hopt : IsElasticSocialOptimum u latency xS)
    (hpos : ∃ i₀, 0 < p i₀ * x i₀) (i : Link)
    (hcomp_pos : ∀ q, q ≠ i → 0 < latencyDeriv q (x q)) :
    (p i - x i * latencyDeriv i (x i)) *
      (1 + (-uSecondDeriv (∑ k, x k)) *
        ∑ q ∈ Finset.univ.erase i, (latencyDeriv q (x q))⁻¹) ≤
      (-uSecondDeriv (∑ k, x k)) * x i := by
  obtain ⟨hpi, hxi⟩ := hoe.price_pos_and_flow_pos hu hl hopt hpos i
  have hxpos : ∀ q, 0 < x q := fun q => (hoe.price_pos_and_flow_pos hu hl hopt hpos q).2
  let X : ℝ := ∑ k, x k
  have hX_pos : 0 < X :=
    hxi.trans_le (Finset.single_le_sum (fun k _ => hoe.2.1.1 k) (Finset.mem_univ i))
  let cStar : ℝ := uDeriv X
  have hi_eff : latency i (x i) + p i = cStar := hoe.2.1.2.1 i hxi
  let U2 : ℝ := -uSecondDeriv X
  have hU2_nn : 0 ≤ U2 := by simp only [U2]; linarith [hu.secondDeriv_nonpos hX_pos.le]
  let compSet : Finset Link := Finset.univ.erase i
  let Sinv : ℝ := ∑ q ∈ compSet, (latencyDeriv q (x q))⁻¹
  have hSinv_nn : 0 ≤ Sinv := Finset.sum_nonneg fun q hq =>
    inv_nonneg.mpr (hcomp_pos q (Finset.mem_erase.mp hq).1).le
  have hdenom_pos : 0 < 1 + U2 * Sinv := by positivity
  -- Suffices to show p i ≤ x i * latencyDeriv i (x i) + (U2 * x i) / (1 + U2 * Sinv):
  suffices hub : p i ≤ x i * latencyDeriv i (x i) + (U2 * x i) / (1 + U2 * Sinv) by
    exact (le_div_iff₀ hdenom_pos).mp (by linarith)
  -- Subcase 1: uDeriv is flat immediately above X (∃ δ₀ > 0, uDeriv (X + δ₀) = cStar):
  by_cases hflat_u : ∃ δ₀ > 0, uDeriv (X + δ₀) = cStar
  · obtain ⟨δ₀, hδ₀, hud_flat⟩ := hflat_u
    have hp_le0 : p i ≤ x i * latencyDeriv i (x i) + 0 := by
      refine le_mul_deriv_add_of_forall_pos_add (hl.hasDerivAt i (x i) hxi.le)
        fun ε η hε hη => ?_
      obtain ⟨δ, hδ0, hδη, hδδ₀, hlat_lt⟩ :=
        hl.exists_step_lt i hxi.le hδ₀ (show latency i (x i) < cStar by linarith) hη
      have hud_eq : uDeriv (X + δ) = cStar := by
        refine le_antisymm (hu.deriv_le hX_pos.le (by linarith)) ?_
        rw [← hud_flat]
        exact hu.deriv_le (by linarith) (by linarith)
      let x' : Link → ℝ := Function.update x i (x i + δ)
      let p' : ℝ := cStar - latency i (x i + δ)
      have hp'0 : 0 ≤ p' := by simp only [p']; linarith
      have hx'sum : ∑ k, x' k = X + δ := sum_update_add_eq x i δ
      have hw' : IsElasticPricedWardrop uDeriv latency (Function.update p i p') x' := by
        refine ⟨fun k => ?_, fun k _ => ?_, fun k => ?_⟩
        · simp only [x', Function.update_apply]; split_ifs <;> linarith [hoe.2.1.1 k]
        all_goals
          rw [hx'sum, hud_eq]
          by_cases hki : k = i
          · subst hki; simp [x', p']
          simp only [x', Function.update_of_ne hki]
        · exact hoe.2.1.2.1 k (hxpos k)
        · exact hoe.2.1.2.2 k
      have hbest := hoe.2.2 i p' x' hp'0 hw'
      simp only [x', p', Function.update_self, ← hi_eff] at hbest
      exact ⟨δ, hδ0, hδη, le_div_mul_add_of_mul_le hδ0 hε.le (by nlinarith)⟩
    linarith [div_nonneg (mul_nonneg hU2_nn hxi.le) hdenom_pos.le]
  -- Subcase 2: uDeriv strictly decreases above X!
  push Not at hflat_u
  refine le_mul_deriv_add_of_forall_pos_add (hl.hasDerivAt i (x i) hxi.le)
    fun ε η hε hη => ?_
  -- Choose δ' > 0 so the perturbed ratio is within ε / 2 of (U2 * x i) / (1 + U2 * Sinv):
  let δ' : ℝ := ε / (2 * x i + 1)
  have hδ'_pos : 0 < δ' := div_pos hε (by positivity)
  have hU2d_pos : 0 < U2 + δ' := by linarith
  have hfrac_close : ((U2 + δ') * x i) / (1 + (U2 + δ') * Sinv) ≤
      (U2 * x i) / (1 + U2 * Sinv) + ε / 2 := by
    have hd1 : 0 < 1 + (U2 + δ') * Sinv := by positivity
    have hdiff : ((U2 + δ') * x i) / (1 + (U2 + δ') * Sinv) -
        (U2 * x i) / (1 + U2 * Sinv) =
        (δ' * x i) / ((1 + (U2 + δ') * Sinv) * (1 + U2 * Sinv)) := by
      field_simp
      ring
    have hden_ge1 : 1 ≤ (1 + (U2 + δ') * Sinv) * (1 + U2 * Sinv) :=
      one_le_mul_of_one_le_of_one_le
        (le_add_of_nonneg_right (mul_nonneg hU2d_pos.le hSinv_nn))
        (le_add_of_nonneg_right (mul_nonneg hU2_nn hSinv_nn))
    have hle1 : (δ' * x i) / ((1 + (U2 + δ') * Sinv) * (1 + U2 * Sinv)) ≤ δ' * x i :=
      div_le_self (mul_nonneg hδ'_pos.le hxi.le) hden_ge1
    have hle2 : δ' * x i ≤ ε / 2 := by
      simp only [δ']
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      linarith
    linarith
  -- From HasDerivAt uDeriv (-U2) X, for small s0 > 0, (cStar - uDeriv (X + s0)) / s0 < U2 + δ':
  have hev_u : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      t⁻¹ • (-uDeriv (X + t) - -uDeriv X) < U2 + δ' :=
    (hu.hasSecondDerivAt X hX_pos.le).neg.tendsto_slope_zero_right.eventually
      (eventually_lt_nhds (show U2 < U2 + δ' by linarith))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev_u
  obtain ⟨η_u, hη_u, hball_u⟩ := hev_u
  -- Continuity of latency i at x i so latency i (x i + Δ) - latency i (x i) < p i / 2:
  have hcont_i : ContinuousAt (latency i) (x i) := (hl.hasDerivAt i (x i) hxi.le).continuousAt
  have hev_i : ∀ᶠ w in nhds (x i), latency i w - latency i (x i) < p i / 2 :=
    (hcont_i.sub continuousAt_const).eventually
      (eventually_lt_nhds (show latency i (x i) - latency i (x i) < p i / 2 by
        linarith [half_pos hpi]))
  rw [Metric.eventually_nhds_iff] at hev_i
  obtain ⟨η₁, hη₁, hball_i⟩ := hev_i
  let r0 : ℝ := min (η_u / 2) (min η η₁ / (2 * ((compSet.card : ℝ) + 1)))
  have hr0_pos : 0 < r0 :=
    lt_min (half_pos hη_u) (div_pos (lt_min hη hη₁) (by positivity))
  let rStep : Link → ℝ := fun q =>
    min (x q / 2) (min η η₁ / (2 * ((compSet.card : ℝ) + 1)))
  have hrStep_pos : ∀ q ∈ compSet, 0 < rStep q := fun q _ =>
    lt_min (half_pos (hxpos q)) (div_pos (lt_min hη hη₁) (by positivity))
  have hrStep_lt_x : ∀ q ∈ compSet, rStep q < x q := fun q _ =>
    (min_le_left _ _).trans_lt (half_lt_self (hxpos q))
  have hu_drop_pos : 0 < cStar - uDeriv (X + r0) := by
    have hle := hu.deriv_le hX_pos.le (show X ≤ X + r0 by linarith)
    exact sub_pos.mpr (lt_of_le_of_ne hle (hflat_u r0 hr0_pos))
  -- Choose μ > 0 smaller than cStar - uDeriv (X + r0), latency drops on compSet, p i / 4, ε / 2:
  have hex_bQ : ∃ bQ > 0, ∀ q ∈ compSet, bQ < latency q (x q) - latency q (x q - rStep q) := by
    by_cases hne_c : compSet.Nonempty
    · let mQ : ℝ := compSet.inf' hne_c fun q => latency q (x q) - latency q (x q - rStep q)
      have hmQ_pos : 0 < mQ := by
        rw [Finset.lt_inf'_iff]
        intro q hq
        have hdq := hcomp_pos q (Finset.mem_erase.mp hq).1
        have hlat_pos : 0 < latency q (x q) :=
          (hl.latency_nonneg q (hxpos q).le).lt_of_ne fun hz =>
            hdq.ne' ((hl.latency_eq_zero_iff_deriv_eq_zero q (hxpos q)).mp hz.symm)
        have hlt := hl.latency_sub_lt_of_pos q (hrStep_pos q hq) (hrStep_lt_x q hq) hlat_pos
        linarith
      exact ⟨mQ / 2, half_pos hmQ_pos, fun q hq =>
        (half_lt_self hmQ_pos).trans_le (Finset.inf'_le _ hq)⟩
    · exact ⟨1, zero_lt_one, fun q hq => False.elim (hne_c ⟨q, hq⟩)⟩
  obtain ⟨bQ, hbQ_pos, hbQ_lt⟩ := hex_bQ
  let μ : ℝ := min (min ((cStar - uDeriv (X + r0)) / 2) bQ) (min (p i / 4) (ε / 4))
  have hμ0 : 0 < μ :=
    lt_min (lt_min (half_pos hu_drop_pos) hbQ_pos) (lt_min (by positivity) (by positivity))
  have hμ_u : μ < cStar - uDeriv (X + r0) :=
    ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hu_drop_pos)
  have hμ_Q : ∀ q ∈ compSet, μ < latency q (x q) - latency q (x q - rStep q) := fun q hq =>
    ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (hbQ_lt q hq)
  have hμ_pi4 : μ ≤ p i / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hμ_ε2 : μ < ε / 2 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  -- Choose step0 ∈ (0, r0] with cStar - uDeriv (X + step0) = μ by IVT:
  have hex_s0 : ∃ s0, 0 < s0 ∧ s0 ≤ r0 ∧ uDeriv (X + s0) = cStar - μ := by
    have hg_cont : ContinuousOn (fun t => cStar - uDeriv (X + t)) (Set.Icc 0 r0) := by
      refine continuousOn_const.sub (hu.continuousOn_deriv.comp
        (continuous_const.add continuous_id).continuousOn fun t ht => ?_)
      rw [Set.mem_Icc] at ht
      exact Set.mem_Ici.mpr (by linarith [ht.1])
    obtain ⟨s0, hs0_pos, hs0_le, hs0_eq⟩ := exists_pos_le_of_continuousOn_Icc hr0_pos hμ0
      hg_cont (by simp [cStar]) hμ_u.le
    exact ⟨s0, hs0_pos, hs0_le, by linarith⟩
  obtain ⟨step0, hstep0_pos, hstep0_le, hud_s0⟩ := hex_s0
  -- Lower bound step0: μ / (U2 + δ') ≤ step0 from hball_u!
  have hstep0_ge : μ * (U2 + δ')⁻¹ ≤ step0 := by
    have hdist : dist step0 0 < η_u := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hstep0_pos]
      exact (hstep0_le.trans (min_le_left _ _)).trans_lt (half_lt_self hη_u)
    have hsl := hball_u hdist hstep0_pos
    rw [smul_eq_mul, hud_s0, show -(cStar - μ) - -uDeriv X = μ by simp only [cStar]; ring,
      inv_mul_lt_iff₀ hstep0_pos] at hsl
    rw [← div_eq_mul_inv, div_le_iff₀ hU2d_pos]
    linarith
  -- Choose step q ∈ (0, rStep q) for each q ∈ compSet via exists_pos_step_sub_eq:
  have hex_dq : ∀ q ∈ compSet, ∃ t, 0 < t ∧ t < rStep q ∧
      latency q (x q) - latency q (x q - t) = μ := by
    intro q hq
    have hμ_lt_lq : μ < latency q (x q) := by
      linarith [hμ_Q q hq,
        hl.latency_nonneg q (show 0 ≤ x q - rStep q by linarith [hrStep_lt_x q hq])]
    obtain ⟨t, ht0, _, hteq, htsmall⟩ := exists_pos_step_sub_eq
      (hl.zero_at_zero q) (hl.monotoneOn q) (hl.continuousOn q) (hxpos q) hμ0 hμ_lt_lq
    exact ⟨t, ht0, htsmall (rStep q) (hrStep_pos q hq) (hrStep_lt_x q hq).le (hμ_Q q hq), hteq⟩
  choose! step hstep_pos hstep_lt hstep_eq using hex_dq
  let Δ : ℝ := step0 + ∑ q ∈ compSet, step q
  have hΔ0 : 0 < Δ :=
    add_pos_of_pos_of_nonneg hstep0_pos (Finset.sum_nonneg fun q hq => (hstep_pos q hq).le)
  have hΔ_lt_min : Δ < min η η₁ := by
    have hq_le : ∑ q ∈ compSet, step q ≤
        compSet.card * (min η η₁ / (2 * ((compSet.card : ℝ) + 1))) :=
      (Finset.sum_le_card_nsmul _ _ _ fun q hq =>
        (hstep_lt q hq).le.trans (min_le_right _ _)).trans_eq (nsmul_eq_mul _ _)
    have hΔ_le : Δ ≤ ((compSet.card : ℝ) + 1) *
        (min η η₁ / (2 * ((compSet.card : ℝ) + 1))) := by
      simp only [Δ]; linarith [hstep0_le.trans (min_le_right _ _)]
    have hpos_c : 0 < (compSet.card : ℝ) + 1 := by positivity
    rw [mul_div_two_mul hpos_c.ne'] at hΔ_le
    exact hΔ_le.trans_lt (half_lt_self (lt_min hη hη₁))
  have hΔη : Δ < η := hΔ_lt_min.trans_le (min_le_left _ _)
  have hΔη₁ : Δ < η₁ := hΔ_lt_min.trans_le (min_le_right _ _)
  -- Convexity on compSet + hstep0_ge gives μ * ((U2 + δ')⁻¹ + Sinv) ≤ Δ:
  have hΔ_ge : μ * ((U2 + δ')⁻¹ + Sinv) ≤ Δ := by
    have hsum_ge : μ * Sinv ≤ ∑ q ∈ compSet, step q := by
      simp only [Sinv, Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq => ?_
      have hdq_pos : 0 < latencyDeriv q (x q) := hcomp_pos q (Finset.mem_erase.mp hq).1
      have hst_lt_x : step q < x q := (hstep_lt q hq).trans (hrStep_lt_x q hq)
      have hconv := hl.add_deriv_mul_le q (hxpos q).le (show 0 ≤ x q - step q by linarith)
      rw [← div_eq_mul_inv, div_le_iff₀ hdq_pos]
      linarith [hstep_eq q hq]
    simp only [Δ]
    linarith
  have hlat_i_inc : latency i (x i + Δ) - latency i (x i) < p i / 2 := by
    refine hball_i ?_
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hΔ0]
    exact hΔη₁
  let x' : Link → ℝ := Function.update (fun k => x k - step k) i (x i + Δ)
  let p' : ℝ := cStar - μ - latency i (x i + Δ)
  have hp'0 : 0 ≤ p' := by simp only [p', ← hi_eff]; linarith
  have hx'sum : ∑ k, x' k = X + step0 := by
    simp only [x', X, Δ, compSet, Finset.sum_update_of_mem (Finset.mem_univ i),
      Finset.sdiff_singleton_eq_erase, Finset.sum_sub_distrib]
    rw [← Finset.add_sum_erase _ x (Finset.mem_univ i)]
    ring
  have hcomp_cost : ∀ k, k ≠ i → latency k (x' k) + Function.update p i p' k = cStar - μ :=
    fun k hki => by
      have hk_cost : latency k (x k) + p k = cStar := hoe.2.1.2.1 k (hxpos k)
      simp only [x', Function.update_of_ne hki]
      linarith [hstep_eq k (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩)]
  have hw' : IsElasticPricedWardrop uDeriv latency (Function.update p i p') x' := by
    refine ⟨fun k => ?_, fun k _ => ?_, fun k => ?_⟩
    · by_cases hki : k = i
      · subst hki; simp only [x', Function.update_self]; linarith
      · have hkc : k ∈ compSet := Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩
        simp only [x', Function.update_of_ne hki]
        linarith [(hstep_lt k hkc).trans (hrStep_lt_x k hkc)]
    all_goals
      rw [hx'sum, hud_s0]
      by_cases hki : k = i
      · subst hki; simp [x', p']
    · exact hcomp_cost k hki
    · exact (hcomp_cost k hki).ge
  have hbest := hoe.2.2 i p' x' hp'0 hw'
  have hi_prod : p' * x' i =
      p i * x i - μ * x i + p i * Δ -
        (latency i (x i + Δ) - latency i (x i)) * (x i + Δ) - μ * Δ := by
    simp only [p', x', Function.update_self, ← hi_eff]
    ring
  rw [hi_prod] at hbest
  have hdiv_μ : (μ / Δ) * x i ≤ ((U2 + δ') * x i) / (1 + (U2 + δ') * Sinv) := by
    have hid_inv : ((U2 + δ')⁻¹ + Sinv) * (U2 + δ') = 1 + (U2 + δ') * Sinv := by
      have hne_u : U2 + δ' ≠ 0 := hU2d_pos.ne'
      field_simp
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hΔ0 (by positivity), ← hid_inv]
    linarith [mul_le_mul_of_nonneg_right hΔ_ge (by positivity : (0 : ℝ) ≤ (U2 + δ') * x i)]
  refine ⟨Δ, hΔ0, hΔη, ?_⟩
  have hdiv_p : p i ≤ ((latency i (x i + Δ) - latency i (x i)) / Δ) * (x i + Δ) +
      (μ / Δ) * x i + μ := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_add' _ _ _ hΔ0.ne',
      le_div_iff₀ hΔ0]
    linarith
  linarith

private theorem linkSurplusEnvelope_at_min_two_thirds {x l di : ℝ} (_hx : 0 ≤ x) (hl0 : 0 ≤ l)
    (hdi : 0 ≤ di) :
    2 * linkSurplusEnvelope (l + x * di) l (x * di) di ≤
      3 * ((l + x * di) * x - x * l) := by
  rw [linkSurplusEnvelope_at_min hl0]
  nlinarith [mul_nonneg (sq_nonneg x) hdi]

private theorem linkSurplusEnvelope_competitor_two_thirds {x l di m dU : ℝ}
    (hx : 0 ≤ x) (hl0 : 0 ≤ l) (hdi_pos : 0 < di) (hlt : l ≤ x * di)
    (hm0 : 0 ≤ m) (hmlt : m ≤ l + x * di) (hdU_ge : l + x * di - m ≤ dU) :
    2 * linkSurplusEnvelope m l (x * di) di ≤
      3 * (m * x - x * l) + dU ^ 2 / di + dU * x := by
  linarith [linkSurplusEnvelope_competitor_five_sixths hx hl0 hdi_pos hlt hm0 hmlt hdU_ge,
    self_le_linkSurplusEnvelope (x := x) (m := m) hl0 hdi_pos]

/-- **Ozdaglar `2 / 3` Elastic-Traffic Oligopoly Efficiency Bound** ([Ozdaglar and Srikant,
Theorem 22.4, p. 585][OzdaglarSrikant2007]; [Ozdaglar2008]): on any parallel-link network where each
link is owned by an independent provider, if latencies satisfy `SmoothConvexLatencies` and aggregate
user utility `u` satisfies `SmoothConcaveMarginalUtility`, then for every pure-strategy elastic
Oligopoly Equilibrium `(p, x)` and every elastic social optimum `xS`,
`2 * elasticSocialSurplus u latency xS ≤ 3 * elasticSocialSurplus u latency x`. -/
theorem elastic_oligopoly_surplus_two_thirds {Link : Type*} [Fintype Link] [DecidableEq Link]
    {u uDeriv uSecondDeriv : ℝ → ℝ} (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv)
    {latency latencyDeriv : Link → ℝ → ℝ} (hl : SmoothConvexLatencies latency latencyDeriv)
    {p x xS : Link → ℝ} (hoe : IsElasticOligopolyEquilibrium uDeriv latency p x)
    (hopt : IsElasticSocialOptimum u latency xS) :
    2 * elasticSocialSurplus u latency xS ≤ 3 * elasticSocialSurplus u latency x := by
  by_cases hne : Nonempty Link
  · have of_opt (hx_opt : IsElasticSocialOptimum u latency x) :
        2 * elasticSocialSurplus u latency xS ≤ 3 * elasticSocialSurplus u latency x := by
      linarith [hx_opt.2 xS hopt.1, hoe.2.1.socialSurplus_nonneg hu hoe.1]
    by_cases hpos : ∃ i₀, 0 < p i₀ * x i₀
    · have hall_pos := hoe.price_pos_and_flow_pos hu hl hopt hpos
      let X : ℝ := ∑ k, x k
      let U1 : ℝ := uDeriv X
      let U2 : ℝ := -uSecondDeriv X
      have hX0 : 0 ≤ X := Finset.sum_nonneg fun k _ => hoe.2.1.1 k
      have hU2_nn : 0 ≤ U2 := by simp only [U2]; linarith [hu.secondDeriv_nonpos hX0]
      let mc : Link → ℝ := fun k => latency k (x k) + x k * latencyDeriv k (x k)
      obtain ⟨i₀, _, hi₀_min⟩ := Finset.exists_min_image Finset.univ mc Finset.univ_nonempty
      let m : ℝ := mc i₀
      have hm0 : 0 ≤ m := add_nonneg (hl.latency_nonneg i₀ (hoe.2.1.1 i₀))
        (mul_nonneg (hoe.2.1.1 i₀) (hl.latencyDeriv_nonneg i₀ (hoe.2.1.1 i₀)))
      have heff_all : ∀ k, latency k (x k) + p k = U1 := fun k =>
        hoe.2.1.2.1 k (hall_pos k).2
      have hmc_le : ∀ k, mc k ≤ U1 := fun k => by
        rw [← heff_all k]
        linarith [hoe.mul_latencyDeriv_le_price hu hl k]
      let dU : ℝ := U1 - m
      have hdU0 : 0 ≤ dU := sub_nonneg.mpr (hmc_le i₀)
      have of_eq (hdU_z : U1 = m) :
          2 * elasticSocialSurplus u latency xS ≤ 3 * elasticSocialSurplus u latency x := by
        have hmc_eq : ∀ k, mc k = U1 := fun k =>
          le_antisymm (hmc_le k) (hdU_z ▸ hi₀_min k (Finset.mem_univ k))
        exact of_opt (isElasticSocialOptimum_of_kkt hu hl hoe.2.1.1
          (fun k => (hmc_eq k).ge) (fun k _ => hmc_eq k))
      -- Subcase A: some competitor q ≠ i₀ has latencyDeriv q (x q) = 0 -> dU = 0 -> x is optimal!
      by_cases hcomp_z : ∃ q, q ≠ i₀ ∧ latencyDeriv q (x q) = 0
      · obtain ⟨q, hqi₀, hq_z⟩ := hcomp_z
        have hp_eq := hoe.price_eq_mul_deriv_of_comp_deriv_zero hu hl hopt hpos hqi₀ hq_z
        exact of_eq (by simp only [U1, ← heff_all i₀, m, mc, hp_eq])
      push Not at hcomp_z
      have hcomp_pos : ∀ q, q ≠ i₀ → 0 < latencyDeriv q (x q) := fun q hq =>
        lt_of_le_of_ne (hl.latencyDeriv_nonneg q (hoe.2.1.1 q)) (Ne.symm (hcomp_z q hq))
      have hmarkup := hoe.price_sub_mul_deriv_le_elastic hu hl hopt hpos i₀ hcomp_pos
      have hdU_eq_diff : dU = p i₀ - x i₀ * latencyDeriv i₀ (x i₀) := by
        simp only [dU, ← heff_all i₀, m, mc]
        ring
      -- Subcase B: U2 = 0 -> hmarkup gives dU * 1 ≤ 0 -> dU = 0 -> x is optimal!
      rcases hU2_nn.eq_or_lt with hU2_z | hU2_pos
      · change (p i₀ - x i₀ * latencyDeriv i₀ (x i₀)) *
          (1 + U2 * ∑ q ∈ Finset.univ.erase i₀, (latencyDeriv q (x q))⁻¹) ≤
          U2 * x i₀ at hmarkup
        rw [← hU2_z, zero_mul, add_zero, zero_mul, ← hdU_eq_diff, mul_one] at hmarkup
        exact of_eq (le_antisymm (sub_nonpos.mp hmarkup) (hmc_le i₀))
      · -- Main Subcase C: U2 > 0 and ∀ q ≠ i₀, 0 < latencyDeriv q (x q)!
        let Δu : ℝ := u X - U1 * X
        have hΔu_nn : 0 ≤ Δu := hu.sub_mul_deriv_nonneg hX0
        let YS : ℝ := ∑ k, xS k
        have hYS0 : 0 ≤ YS := Finset.sum_nonneg fun k _ => hopt.1 k
        -- Upper bound elasticSocialSurplus u latency xS:
        have hxS_env : elasticSocialSurplus u latency xS ≤
            Δu + dU * X + dU ^ 2 / (2 * U2) +
              ∑ k, linkSurplusEnvelope m (latency k (x k))
                (x k * latencyDeriv k (x k)) (latencyDeriv k (x k)) := by
          have hsplit : elasticSocialSurplus u latency xS =
              (u YS - m * YS) + ∑ k, (m * xS k - xS k * latency k (xS k)) := by
            simp only [elasticSocialSurplus, YS, Finset.mul_sum]
            have h2 : ∑ k, (m * xS k - xS k * latency k (xS k)) =
                (∑ k, m * xS k) - ∑ k, latency k (xS k) * xS k := by
              rw [← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun k _ => by ring
            linarith
          rw [hsplit]
          have hu_env : u YS - m * YS ≤ Δu + dU * X + dU ^ 2 / (2 * U2) :=
            hu.le_envelope_upper hX0 hYS0 (hmc_le i₀) hU2_pos
          have hl_env : ∑ k, (m * xS k - xS k * latency k (xS k)) ≤
              ∑ k, linkSurplusEnvelope m (latency k (x k))
                (x k * latencyDeriv k (x k)) (latencyDeriv k (x k)) :=
            Finset.sum_le_sum fun k _ =>
              linkSurplusEnvelope_ge hl k (hoe.2.1.1 k) (hopt.1 k) hm0
                (hi₀_min k (Finset.mem_univ k))
          linarith
        -- Decompose elasticSocialSurplus u latency x:
        have hx_decomp : elasticSocialSurplus u latency x =
            Δu + dU * X + ∑ k, (m * x k - x k * latency k (x k)) := by
          simp only [elasticSocialSurplus, Δu, dU, U1, X]
          have h1 : (∑ k, x k) * m - ∑ k, latency k (x k) * x k =
              ∑ k, (m * x k - x k * latency k (x k)) := by
            rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun k _ => by ring
          linarith
        -- Lower bound dU * X - dU ^ 2 / U2 using hmarkup:
        let compSet : Finset Link := Finset.univ.erase i₀
        have hxi₀_lb : dU / U2 + dU * ∑ q ∈ compSet, (latencyDeriv q (x q))⁻¹ ≤ x i₀ := by
          change (p i₀ - x i₀ * latencyDeriv i₀ (x i₀)) *
            (1 + U2 * ∑ q ∈ compSet, (latencyDeriv q (x q))⁻¹) ≤ U2 * x i₀ at hmarkup
          rw [← hdU_eq_diff] at hmarkup
          rw [div_add' _ _ _ hU2_pos.ne', div_le_iff₀ hU2_pos]
          linarith
        have hX_split : X = x i₀ + ∑ q ∈ compSet, x q :=
          (Finset.add_sum_erase Finset.univ x (Finset.mem_univ i₀)).symm
        have hdU_budget : ∑ q ∈ compSet, (dU ^ 2 / latencyDeriv q (x q) + dU * x q) ≤
            dU * X - dU ^ 2 / U2 := by
          have hmul := mul_le_mul_of_nonneg_left hxi₀_lb hdU0
          have hlhs : dU * (dU / U2 + dU * ∑ q ∈ compSet, (latencyDeriv q (x q))⁻¹) =
              dU ^ 2 / U2 + ∑ q ∈ compSet, dU ^ 2 / latencyDeriv q (x q) := by
            rw [mul_add, ← mul_assoc, Finset.mul_sum]
            congr 1
            · ring
            · exact Finset.sum_congr rfl fun q _ => by ring
          rw [hlhs] at hmul
          rw [hX_split, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
          linarith
        -- Split sums into i₀ and compSet = univ.erase i₀:
        have hpart_env : ∑ k, linkSurplusEnvelope m (latency k (x k))
              (x k * latencyDeriv k (x k)) (latencyDeriv k (x k)) =
            linkSurplusEnvelope m (latency i₀ (x i₀))
              (x i₀ * latencyDeriv i₀ (x i₀)) (latencyDeriv i₀ (x i₀)) +
            ∑ q ∈ compSet, linkSurplusEnvelope m (latency q (x q))
              (x q * latencyDeriv q (x q)) (latencyDeriv q (x q)) :=
          (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀)).symm
        have hpart_x : ∑ k, (m * x k - x k * latency k (x k)) =
            (m * x i₀ - x i₀ * latency i₀ (x i₀)) +
            ∑ q ∈ compSet, (m * x q - x q * latency q (x q)) :=
          (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀)).symm
        have hi₀_bound : 2 * linkSurplusEnvelope m (latency i₀ (x i₀))
              (x i₀ * latencyDeriv i₀ (x i₀)) (latencyDeriv i₀ (x i₀)) ≤
            3 * (m * x i₀ - x i₀ * latency i₀ (x i₀)) :=
          linkSurplusEnvelope_at_min_two_thirds (hoe.2.1.1 i₀)
            (hl.latency_nonneg i₀ (hoe.2.1.1 i₀))
            (hl.latencyDeriv_nonneg i₀ (hoe.2.1.1 i₀))
        have hcomp_bound : 2 * ∑ q ∈ compSet, linkSurplusEnvelope m (latency q (x q))
              (x q * latencyDeriv q (x q)) (latencyDeriv q (x q)) ≤
            3 * (∑ q ∈ compSet, (m * x q - x q * latency q (x q))) +
              ∑ q ∈ compSet, (dU ^ 2 / latencyDeriv q (x q) + dU * x q) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun q hq => ?_
          have hqi₀ : q ≠ i₀ := (Finset.mem_erase.mp hq).1
          have h1 := linkSurplusEnvelope_competitor_two_thirds (dU := dU)
            (hoe.2.1.1 q) (hl.latency_nonneg q (hoe.2.1.1 q))
            (hcomp_pos q hqi₀) (hl.latency_le_mul_deriv q (hoe.2.1.1 q))
            hm0 (hi₀_min q (Finset.mem_univ q)) (by linarith [hmc_le q])
          linarith
        have h2U2 : 2 * (dU ^ 2 / (2 * U2)) = dU ^ 2 / U2 := by
          rw [mul_div_assoc', mul_div_mul_left _ _ two_ne_zero]
        rw [hpart_env] at hxS_env
        rw [hpart_x] at hx_decomp
        linarith
    · push Not at hpos
      exact of_opt (hoe.isElasticSocialOptimum_of_forall_mul_eq_zero hu hl hopt fun i =>
        le_antisymm (hpos i) (mul_nonneg (hoe.1 i) (hoe.2.1.1 i)))
  · rw [not_nonempty_iff] at hne
    simp [elasticSocialSurplus, hu.zero_at_zero]

/-- Ratio form of **Theorem 22.4** ([Ozdaglar and Srikant, Theorem 22.4,
p. 585][OzdaglarSrikant2007]): `2 / 3 ≤ S_u(x) / S_u(xS)` when `0 < S_u(xS)`. -/
theorem elastic_oligopoly_efficiency_ge_two_thirds {Link : Type*} [Fintype Link] [DecidableEq Link]
    {u uDeriv uSecondDeriv : ℝ → ℝ} (hu : SmoothConcaveMarginalUtility u uDeriv uSecondDeriv)
    {latency latencyDeriv : Link → ℝ → ℝ} (hl : SmoothConvexLatencies latency latencyDeriv)
    {p x xS : Link → ℝ} (hoe : IsElasticOligopolyEquilibrium uDeriv latency p x)
    (hopt : IsElasticSocialOptimum u latency xS)
    (hpos : 0 < elasticSocialSurplus u latency xS) :
    (2 : ℝ) / 3 ≤ elasticSocialSurplus u latency x / elasticSocialSurplus u latency xS := by
  rw [div_le_div_iff₀ (by positivity) hpos]
  linarith [elastic_oligopoly_surplus_two_thirds hu hl hoe hopt]

end ElasticTraffic

section ElasticTightnessFamily

/-!
### Asymptotic tightness of `2 / 3` for elastic traffic ([OzdaglarSrikant2007], Theorem 22.4)

On a single zero-latency link (`Fin 1`, `latency _ _ = 0`), smoothing `u'(X) = min(1, 2 - X)` over
`[1 - ε, 1]` (`ε = 1 / (n + 2)`) yields a `C^2` utility `elasticTightnessUtility n` satisfying
`SmoothConcaveMarginalUtility` whose unique elastic Oligopoly Equilibrium `(p = 1, x = 1)` achieves
surplus `1 + ε / 2 - ε^2 / 6` while the social optimum `xS = 2` achieves `3 / 2 + ε / 2 - ε^2 / 6`,
approaching `2 / 3` from above as `n → ∞`.
-/

/-- Second derivative `w_n(t)` of `elasticTightnessUtility n`: `0` on `(-∞, 1 - ε]`, linear ramp
`-(t - (1 - ε)) / ε` on `[1 - ε, 1]`, and `-1` on `[1, ∞)` where `ε = 1 / (n + 2)`. -/
@[expose] noncomputable def elasticTightnessUtilitySecondDeriv (n : ℕ) (t : ℝ) : ℝ :=
  max (-1) (min 0 (-(t - (1 - 1 / ((n : ℝ) + 2))) / (1 / ((n : ℝ) + 2))))

/-- First derivative `u'_n(x) = (1 + ε / 2) + ∫ t in 0..x, w_n(t)` of
`elasticTightnessUtility n`. -/
noncomputable def elasticTightnessUtilityDeriv (n : ℕ) (x : ℝ) : ℝ :=
  (1 + 1 / (2 * ((n : ℝ) + 2))) +
    ∫ t in (0 : ℝ)..x, elasticTightnessUtilitySecondDeriv n t

/-- Aggregate utility `u_n(x) = ∫ t in 0..x, u'_n(t)` for the `2 / 3` tightness family. -/
noncomputable def elasticTightnessUtility (n : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, elasticTightnessUtilityDeriv n t

private theorem continuous_elasticTightnessSecondDeriv (n : ℕ) :
    Continuous (elasticTightnessUtilitySecondDeriv n) := by
  unfold elasticTightnessUtilitySecondDeriv
  exact continuous_const.max
    (continuous_const.min (((continuous_id.sub continuous_const).neg).div_const _))

private theorem antitone_elasticTightnessSecondDeriv (n : ℕ) :
    Antitone (elasticTightnessUtilitySecondDeriv n) := by
  intro a b hab
  simp only [elasticTightnessUtilitySecondDeriv]
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  have hdiv : -(b - (1 - 1 / ((n : ℝ) + 2))) / (1 / ((n : ℝ) + 2)) ≤
      -(a - (1 - 1 / ((n : ℝ) + 2))) / (1 / ((n : ℝ) + 2)) :=
    div_le_div_of_nonneg_right (by linarith) hε.le
  exact max_le_max le_rfl (min_le_min le_rfl hdiv)

private theorem hasDerivAt_elasticTightnessDeriv (n : ℕ) (x : ℝ) :
    HasDerivAt (elasticTightnessUtilityDeriv n) (elasticTightnessUtilitySecondDeriv n x) x := by
  have hc := continuous_elasticTightnessSecondDeriv n
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter MeasureTheory.volume (nhds x)) hc.continuousAt
  unfold elasticTightnessUtilityDeriv
  exact hd.const_add (1 + 1 / (2 * ((n : ℝ) + 2)))

private theorem continuous_elasticTightnessDeriv (n : ℕ) :
    Continuous (elasticTightnessUtilityDeriv n) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_elasticTightnessDeriv n x).continuousAt

private theorem hasDerivAt_elasticTightnessUtility (n : ℕ) (x : ℝ) :
    HasDerivAt (elasticTightnessUtility n) (elasticTightnessUtilityDeriv n x) x := by
  have hc := continuous_elasticTightnessDeriv n
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter MeasureTheory.volume (nhds x)) hc.continuousAt

private theorem concaveOn_of_hasDerivAt_antitone {f f' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hcont : Continuous f') (hant : Antitone f') :
    ConcaveOn ℝ (Set.Ici 0) f := by
  refine ⟨convex_Ici 0, ?_⟩
  have hpair : ∀ a b : ℝ, a ≤ b → ∀ w₁ w₂ : ℝ, 0 ≤ w₁ → 0 ≤ w₂ → w₁ + w₂ = 1 →
      w₁ * f a + w₂ * f b ≤ f (w₁ * a + w₂ * b) := by
    intro a b hab w₁ w₂ hw₁ hw₂ hw
    let c : ℝ := w₁ * a + w₂ * b
    have hac : a ≤ c := by
      have hid1 : c - a = w₂ * (b - a) := by
        simp only [c]
        rw [show w₁ = 1 - w₂ by linarith]
        ring
      linarith [mul_nonneg hw₂ (sub_nonneg.mpr hab)]
    have hcb : c ≤ b := by
      have hid2 : b - c = w₁ * (b - a) := by
        simp only [c]
        rw [show w₂ = 1 - w₁ by linarith]
        ring
      linarith [mul_nonneg hw₁ (sub_nonneg.mpr hab)]
    have hftc1 : ∫ t in a..c, f' t = f c - f a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
        (hcont.intervalIntegrable a c)
    have hftc2 : ∫ t in c..b, f' t = f b - f c :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
        (hcont.intervalIntegrable c b)
    have hge1 : (c - a) * f' c ≤ f c - f a := by
      have hm : ∫ _t in a..c, f' c ≤ ∫ t in a..c, f' t :=
        intervalIntegral.integral_mono_on hac (continuous_const.intervalIntegrable a c)
          (hcont.intervalIntegrable a c) fun t ht => hant ht.2
      rw [intervalIntegral.integral_const, smul_eq_mul, hftc1] at hm
      exact hm
    have hle2 : f b - f c ≤ (b - c) * f' c := by
      have hm : ∫ t in c..b, f' t ≤ ∫ _t in c..b, f' c :=
        intervalIntegral.integral_mono_on hcb (hcont.intervalIntegrable c b)
          (continuous_const.intervalIntegrable c b) fun t ht => hant ht.1
      rw [intervalIntegral.integral_const, smul_eq_mul, hftc2] at hm
      exact hm
    have hm1 := mul_le_mul_of_nonneg_left hge1 hw₁
    have hm2 := mul_le_mul_of_nonneg_left hle2 hw₂
    have hid : w₁ * ((c - a) * f' c) - w₂ * ((b - c) * f' c) = 0 := by
      simp only [c]
      rw [show w₁ = 1 - w₂ by linarith]
      ring
    have hgoal : 0 ≤ w₁ * (f c - f a) - w₂ * (f b - f c) := by linarith
    have hsum_c : w₁ * (f c - f a) - w₂ * (f b - f c) =
        (w₁ + w₂) * f c - (w₁ * f a + w₂ * f b) := by ring
    rw [hsum_c, hw, one_mul] at hgoal
    linarith
  intro a _ b _ w₁ w₂ hw₁ hw₂ hw
  simp only [smul_eq_mul]
  rcases le_total a b with hab | hba
  · exact hpair a b hab w₁ w₂ hw₁ hw₂ hw
  · have h := hpair b a hba w₂ w₁ hw₂ hw₁ (by linarith)
    rw [show w₂ * b + w₁ * a = w₁ * a + w₂ * b by ring] at h
    linarith

private theorem antitone_elasticTightnessDeriv (n : ℕ) :
    Antitone (elasticTightnessUtilityDeriv n) := by
  intro a b hab
  have hc := continuous_elasticTightnessSecondDeriv n
  have hftc : ∫ t in a..b, elasticTightnessUtilitySecondDeriv n t =
      elasticTightnessUtilityDeriv n b - elasticTightnessUtilityDeriv n a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_elasticTightnessDeriv n t) (hc.intervalIntegrable a b)
  have hnp : ∀ t, elasticTightnessUtilitySecondDeriv n t ≤ 0 := fun t => by
    simp only [elasticTightnessUtilitySecondDeriv]
    exact max_le (by norm_num) (min_le_left _ _)
  have hm : ∫ t in a..b, elasticTightnessUtilitySecondDeriv n t ≤ ∫ _t in a..b, (0 : ℝ) :=
    intervalIntegral.integral_mono_on hab (hc.intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b) fun t _ => hnp t
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_zero, hftc] at hm
  linarith

theorem elasticTightness_smoothConcave (n : ℕ) :
    SmoothConcaveMarginalUtility (elasticTightnessUtility n)
      (elasticTightnessUtilityDeriv n) (elasticTightnessUtilitySecondDeriv n) where
  zero_at_zero := by simp [elasticTightnessUtility]
  concaveOn := concaveOn_of_hasDerivAt_antitone (hasDerivAt_elasticTightnessUtility n)
    (continuous_elasticTightnessDeriv n) (antitone_elasticTightnessDeriv n)
  concaveOn_deriv := concaveOn_of_hasDerivAt_antitone (hasDerivAt_elasticTightnessDeriv n)
    (continuous_elasticTightnessSecondDeriv n) (antitone_elasticTightnessSecondDeriv n)
  hasDerivAt x _ := hasDerivAt_elasticTightnessUtility n x
  hasSecondDerivAt x _ := hasDerivAt_elasticTightnessDeriv n x

/-- Closed-form value of `elasticTightnessUtilityDeriv n x` on `[0, 1 - 1 / (n + 2)]`. -/
theorem elasticTightnessDeriv_eq_of_le (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 1 - 1 / ((n : ℝ) + 2)) :
    elasticTightnessUtilityDeriv n x = 1 + 1 / (2 * ((n : ℝ) + 2)) := by
  simp only [elasticTightnessUtilityDeriv]
  have hint0 : ∫ t in (0 : ℝ)..x, elasticTightnessUtilitySecondDeriv n t = 0 := by
    have hcongr : ∫ t in (0 : ℝ)..x, elasticTightnessUtilitySecondDeriv n t =
        ∫ _t in (0 : ℝ)..x, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hx0] at ht
      simp only [elasticTightnessUtilitySecondDeriv]
      have hε : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      have hnn : 0 ≤ -(t - (1 - 1 / ((n : ℝ) + 2))) / (1 / ((n : ℝ) + 2)) :=
        div_nonneg (by linarith [ht.2]) hε.le
      rw [min_eq_left hnn, max_eq_right (by norm_num)]
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, mul_zero]
  linarith

/-- Closed-form value of `elasticTightnessUtilityDeriv n x` on `[1 - 1 / (n + 2), 1]`. -/
theorem elasticTightnessDeriv_eq_mid (n : ℕ) {x : ℝ}
    (hx1 : 1 - 1 / ((n : ℝ) + 2) ≤ x) (hx2 : x ≤ 1) :
    elasticTightnessUtilityDeriv n x =
      1 + 1 / (2 * ((n : ℝ) + 2)) -
        (x - (1 - 1 / ((n : ℝ) + 2))) ^ 2 / (2 * (1 / ((n : ℝ) + 2))) := by
  let ε : ℝ := 1 / ((n : ℝ) + 2)
  have hε : 0 < ε := by positivity
  have h1mε : 0 ≤ 1 - ε := by
    have hn2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hle : ε ≤ 1 / 2 := div_le_div_of_nonneg_left zero_le_one two_pos hn2
    linarith
  have hc := continuous_elasticTightnessSecondDeriv n
  have hadj := (intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 (1 - ε))
    (hc.intervalIntegrable (μ := MeasureTheory.volume) (1 - ε) x)).symm
  have hint1 : ∫ t in (0 : ℝ)..(1 - ε), elasticTightnessUtilitySecondDeriv n t = 0 := by
    have h0 := elasticTightnessDeriv_eq_of_le n h1mε le_rfl
    simp only [elasticTightnessUtilityDeriv] at h0
    change (1 + 1 / (2 * ((n : ℝ) + 2))) +
      ∫ t in (0 : ℝ)..(1 - ε), elasticTightnessUtilitySecondDeriv n t =
      1 + 1 / (2 * ((n : ℝ) + 2)) at h0
    linarith
  have hint2 : ∫ t in (1 - ε)..x, elasticTightnessUtilitySecondDeriv n t =
      -(x - (1 - ε)) ^ 2 / (2 * ε) := by
    have hcongr : ∫ t in (1 - ε)..x, elasticTightnessUtilitySecondDeriv n t =
        ∫ t in (1 - ε)..x, (-(t - (1 - ε)) / ε) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hx1] at ht
      simp only [elasticTightnessUtilitySecondDeriv]
      change max (-1) (min 0 (-(t - (1 - ε)) / ε)) = -(t - (1 - ε)) / ε
      have hnp : -(t - (1 - ε)) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [ht.1]) hε.le
      have hge1 : -1 ≤ -(t - (1 - ε)) / ε := by
        rw [le_div_iff₀ hε]; linarith [ht.2]
      rw [min_eq_right hnp, max_eq_right hge1]
    rw [hcongr]
    let P : ℝ → ℝ := fun t => -((t - (1 - ε)) * (t - (1 - ε))) / (2 * ε)
    have hP_deriv : ∀ t, HasDerivAt P (-(t - (1 - ε)) / ε) t := fun t => by
      have hd_sub : HasDerivAt (fun s => s - (1 - ε)) 1 t :=
        (hasDerivAt_id' t).sub_const (1 - ε)
      have hd_sq : HasDerivAt (fun s => (s - (1 - ε)) * (s - (1 - ε)))
          (1 * (t - (1 - ε)) + (t - (1 - ε)) * 1) t := hd_sub.mul hd_sub
      convert (hd_sq.neg).div_const (2 * ε) using 1
      field_simp
      ring
    have hcont_lin : Continuous (fun t : ℝ => -(t - (1 - ε)) / ε) :=
      ((continuous_id.sub continuous_const).neg).div_const ε
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hP_deriv t)
      (hcont_lin.intervalIntegrable (1 - ε) x)
    rw [hftc]
    simp only [P]
    ring
  simp only [elasticTightnessUtilityDeriv]
  change (1 + 1 / (2 * ((n : ℝ) + 2))) +
    ∫ t in (0 : ℝ)..x, elasticTightnessUtilitySecondDeriv n t =
    1 + 1 / (2 * ((n : ℝ) + 2)) - (x - (1 - ε)) ^ 2 / (2 * ε)
  rw [hadj, hint1, hint2]
  ring

/-- Closed-form value `2 - x` of `elasticTightnessUtilityDeriv n x` on `[1, ∞)`. -/
theorem elasticTightnessDeriv_eq_of_ge_one (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    elasticTightnessUtilityDeriv n x = 2 - x := by
  let ε : ℝ := 1 / ((n : ℝ) + 2)
  have hε : 0 < ε := by positivity
  have h1mε : 1 - ε ≤ 1 := by linarith
  have h_at1 : elasticTightnessUtilityDeriv n 1 = 1 := by
    have hm := elasticTightnessDeriv_eq_mid n h1mε le_rfl
    have heq : 1 + 1 / (2 * ((n : ℝ) + 2)) -
        (1 - (1 - 1 / ((n : ℝ) + 2))) ^ 2 / (2 * (1 / ((n : ℝ) + 2))) = 1 := by
      have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
      field_simp
      ring
    linarith
  have hc := continuous_elasticTightnessSecondDeriv n
  have hadj := (intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 1 x)).symm
  have hint2 : ∫ t in (1 : ℝ)..x, elasticTightnessUtilitySecondDeriv n t = -(x - 1) := by
    have hcongr : ∫ t in (1 : ℝ)..x, elasticTightnessUtilitySecondDeriv n t =
        ∫ _t in (1 : ℝ)..x, (-1 : ℝ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hx] at ht
      simp only [elasticTightnessUtilitySecondDeriv]
      change max (-1) (min 0 (-(t - (1 - ε)) / ε)) = -1
      have hle1 : -(t - (1 - ε)) / ε ≤ -1 := by rw [div_le_iff₀ hε]; linarith [ht.1]
      rw [min_eq_right (hle1.trans (by norm_num)), max_eq_left hle1]
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
    ring
  simp only [elasticTightnessUtilityDeriv] at h_at1 ⊢
  linarith

private theorem elasticTightnessUtility_one_ge_one (n : ℕ) :
    1 ≤ elasticTightnessUtility n 1 := by
  have hc := continuous_elasticTightnessDeriv n
  have hm : ∫ _t in (0 : ℝ)..1, (1 : ℝ) ≤ ∫ t in (0 : ℝ)..1, elasticTightnessUtilityDeriv n t := by
    refine intervalIntegral.integral_mono_on zero_le_one
      (continuous_const.intervalIntegrable 0 1) (hc.intervalIntegrable 0 1) fun t ht => ?_
    have hant := antitone_elasticTightnessDeriv n ht.2
    have h1 := elasticTightnessDeriv_eq_of_ge_one n le_rfl
    linarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at hm
  simp only [elasticTightnessUtility]
  linarith

private theorem elasticTightnessUtility_one_le (n : ℕ) :
    elasticTightnessUtility n 1 ≤ 1 + 1 / (2 * ((n : ℝ) + 2)) := by
  have hc := continuous_elasticTightnessDeriv n
  have hm : ∫ t in (0 : ℝ)..1, elasticTightnessUtilityDeriv n t ≤
      ∫ _t in (0 : ℝ)..1, (1 + 1 / (2 * ((n : ℝ) + 2))) := by
    refine intervalIntegral.integral_mono_on zero_le_one
      (hc.intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1) fun t ht => ?_
    have hant := antitone_elasticTightnessDeriv n ht.1
    have h1mε : (0 : ℝ) ≤ 1 - 1 / ((n : ℝ) + 2) := by
      have hn2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hle : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := div_le_div_of_nonneg_left zero_le_one two_pos hn2
      linarith
    have h0 := elasticTightnessDeriv_eq_of_le n le_rfl h1mε
    linarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at hm
  simp only [elasticTightnessUtility]
  linarith

/-- Closed-form step `elasticTightnessUtility n 2 = elasticTightnessUtility n 1 + 1 / 2`. -/
theorem elasticTightnessUtility_two_eq (n : ℕ) :
    elasticTightnessUtility n 2 = elasticTightnessUtility n 1 + 1 / 2 := by
  have hc := continuous_elasticTightnessDeriv n
  have hadj := (intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 1 2)).symm
  have hint12 : ∫ t in (1 : ℝ)..2, elasticTightnessUtilityDeriv n t = 1 / 2 := by
    have hcongr : ∫ t in (1 : ℝ)..2, elasticTightnessUtilityDeriv n t =
        ∫ t in (1 : ℝ)..2, (2 - t) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
      exact elasticTightnessDeriv_eq_of_ge_one n ht.1
    rw [hcongr]
    let P : ℝ → ℝ := fun t => 2 * t - (t * t) / 2
    have hP_deriv : ∀ t, HasDerivAt P (2 - t) t := fun t => by
      have hd1 : HasDerivAt (fun s => 2 * s) (2 * 1) t := (hasDerivAt_id' t).const_mul 2
      have hd2 : HasDerivAt (fun s => (s * s) / 2) ((1 * t + t * 1) / 2) t :=
        ((hasDerivAt_id' t).mul (hasDerivAt_id' t)).div_const 2
      convert hd1.sub hd2 using 1
      ring
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hP_deriv t)
      ((continuous_const.sub continuous_id).intervalIntegrable 1 2)
    rw [hftc]
    simp only [P]
    norm_num
  simp only [elasticTightnessUtility] at hadj ⊢
  linarith

/-- Zero latency on `Fin 1` for the elastic tightness family. -/
@[expose] def elasticZeroLatency (_ : Fin 1) (_ : ℝ) : ℝ := 0

theorem elasticZeroLatency_smoothConvex :
    SmoothConvexLatencies elasticZeroLatency elasticZeroLatency where
  zero_at_zero _ := rfl
  monotoneOn _ _ _ _ _ _ := le_rfl
  convexOn _ := ⟨convex_Ici 0, fun _ _ _ _ _ _ _ _ _ => by simp [elasticZeroLatency]⟩
  hasDerivAt _ x _ := hasDerivAt_const x 0

/-- `(p = 1, x = 1)` is a pure-strategy elastic Oligopoly Equilibrium for every `n : ℕ`. -/
theorem elasticTightness_isElasticOligopolyEquilibrium (n : ℕ) :
    IsElasticOligopolyEquilibrium (elasticTightnessUtilityDeriv n) elasticZeroLatency
      (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1) := by
  have hu1 : elasticTightnessUtilityDeriv n 1 = 1 := by
    rw [elasticTightnessDeriv_eq_of_ge_one n le_rfl]; norm_num
  refine ⟨fun _ => zero_le_one,
    ⟨fun _ => zero_le_one, fun _ _ => by simp [elasticZeroLatency, hu1],
      fun _ => by simp [elasticZeroLatency, hu1]⟩,
    fun i p' x' hp'0 hw' => ?_⟩
  have hi0 : i = 0 := Subsingleton.elim i 0
  subst hi0
  simp only [one_mul]
  rcases (hw'.1 0).eq_or_lt with hx0_z | hx0_pos
  · rw [← hx0_z, mul_zero]; exact zero_le_one
  have hsum_x' : ∑ k : Fin 1, x' k = x' 0 := by simp
  have heff := hw'.2.1 0 hx0_pos
  simp only [elasticZeroLatency, zero_add, Function.update_self, hsum_x'] at heff
  -- So p' = elasticTightnessUtilityDeriv n (x' 0); show x' 0 * u'_n(x' 0) ≤ 1 on all 3 regions!
  rw [heff]
  let ε : ℝ := 1 / ((n : ℝ) + 2)
  have hε : 0 < ε := by positivity
  have hε_le : ε ≤ 1 / 2 :=
    div_le_div_of_nonneg_left zero_le_one two_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
  rcases le_or_gt (x' 0) (1 - ε) with hle_left | hgt_left
  · have hval := elasticTightnessDeriv_eq_of_le n hx0_pos.le hle_left
    rw [hval]
    have h1 : (1 + 1 / (2 * ((n : ℝ) + 2))) = 1 + ε / 2 := by simp only [ε]; field_simp
    rw [h1]
    have hmul : (1 + ε / 2) * x' 0 ≤ (1 + ε / 2) * (1 - ε) :=
      mul_le_mul_of_nonneg_left hle_left (by positivity)
    have hexp : (1 + ε / 2) * (1 - ε) = 1 - ε / 2 - ε ^ 2 / 2 := by ring
    nlinarith [sq_nonneg ε]
  · rcases le_or_gt (x' 0) 1 with hle_one | hgt_one
    · have hval := elasticTightnessDeriv_eq_mid n hgt_left.le hle_one
      rw [hval]
      have h1 : 1 + 1 / (2 * ((n : ℝ) + 2)) -
          (x' 0 - (1 - 1 / ((n : ℝ) + 2))) ^ 2 / (2 * (1 / ((n : ℝ) + 2))) =
          1 + ε / 2 - (x' 0 - (1 - ε)) ^ 2 / (2 * ε) := by
        simp only [ε]
        congr 2
        field_simp
      rw [h1]
      let s : ℝ := 1 - x' 0
      have hs0 : 0 ≤ s := by simp only [s]; linarith
      have hsε : s < ε := by simp only [s]; linarith
      have hx_s : x' 0 = 1 - s := by simp [s]
      rw [hx_s]
      have hid : 2 * ε * (1 - (1 + ε / 2 - (1 - s - (1 - ε)) ^ 2 / (2 * ε)) * (1 - s)) =
          s ^ 2 * (1 + 2 * ε - s) := by
        field_simp
        ring
      have hrhs_nn : 0 ≤ s ^ 2 * (1 + 2 * ε - s) := mul_nonneg (sq_nonneg s) (by linarith)
      nlinarith
    · have hval := elasticTightnessDeriv_eq_of_ge_one n hgt_one.le
      rw [hval]
      have hid : 1 - (2 - x' 0) * x' 0 = (x' 0 - 1) ^ 2 := by ring
      nlinarith [sq_nonneg (x' 0 - 1)]

/-- `xS = 2` is an elastic social optimum for `elasticTightnessUtility n`. -/
theorem elasticTightness_isElasticSocialOptimum (n : ℕ) :
    IsElasticSocialOptimum (elasticTightnessUtility n) elasticZeroLatency
      (fun _ : Fin 1 => 2) := by
  have hu2 : elasticTightnessUtilityDeriv n 2 = 0 := by
    rw [elasticTightnessDeriv_eq_of_ge_one n (by norm_num)]; ring
  exact isElasticSocialOptimum_of_kkt (elasticTightness_smoothConcave n)
    elasticZeroLatency_smoothConvex (fun _ => by norm_num)
    (fun _ => by simp [elasticZeroLatency, hu2])
    (fun _ _ => by simp [elasticZeroLatency, hu2])

/-- **Asymptotic tightness of the `2 / 3` elastic-traffic bound** ([Ozdaglar and Srikant,
Theorem 22.4, p. 585][OzdaglarSrikant2007]): for every `δ > 0`, there exists `n : ℕ` whose checked
elastic Oligopoly Equilibrium `(p = 1, x = 1)` has elastic social surplus strictly below
`(2 / 3 + δ)` times the optimal elastic social surplus. -/
theorem elasticTightness_surplus_lt_two_thirds_add {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ,
      elasticSocialSurplus (elasticTightnessUtility n) elasticZeroLatency (fun _ : Fin 1 => 1) <
        (2 / 3 + δ) *
          elasticSocialSurplus (elasticTightnessUtility n) elasticZeroLatency
            (fun _ : Fin 1 => 2) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  refine ⟨n, ?_⟩
  have hgt : 1 < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
  have hsurp1 : elasticSocialSurplus (elasticTightnessUtility n) elasticZeroLatency
      (fun _ : Fin 1 => 1) = elasticTightnessUtility n 1 := by
    simp [elasticSocialSurplus, elasticZeroLatency]
  have hsurp2 : elasticSocialSurplus (elasticTightnessUtility n) elasticZeroLatency
      (fun _ : Fin 1 => 2) = elasticTightnessUtility n 1 + 1 / 2 := by
    simp [elasticSocialSurplus, elasticZeroLatency, elasticTightnessUtility_two_eq]
  rw [hsurp1, hsurp2]
  have hu1_ge : 1 ≤ elasticTightnessUtility n 1 := elasticTightnessUtility_one_ge_one n
  have hu1_le : elasticTightnessUtility n 1 ≤ 1 + 1 / (2 * ((n : ℝ) + 2)) :=
    elasticTightnessUtility_one_le n
  have hn2_pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h1_sub : elasticTightnessUtility n 1 - 1 ≤ 1 / (2 * ((n : ℝ) + 2)) := by linarith
  have h1_mul := mul_le_mul_of_nonneg_left h1_sub (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have h1 : (1 / 3) * (elasticTightnessUtility n 1 - 1) ≤ 1 / (6 * ((n : ℝ) + 2)) := by
    calc (1 / 3) * (elasticTightnessUtility n 1 - 1)
        ≤ (1 / 3) * (1 / (2 * ((n : ℝ) + 2))) := h1_mul
      _ = 1 / (6 * ((n : ℝ) + 2)) := by
        have hne : ((n : ℝ) + 2) ≠ 0 := hn2_pos.ne'
        field_simp
        ring
  have h2 : 1 / (6 * ((n : ℝ) + 2)) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have h3 : δ ≤ δ * (elasticTightnessUtility n 1 + 1 / 2) := by nlinarith
  linarith

end ElasticTightnessFamily

end Cslib.GameTheory
