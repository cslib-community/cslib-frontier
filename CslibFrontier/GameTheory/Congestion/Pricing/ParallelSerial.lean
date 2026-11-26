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

/-!
# Price competition in parallel-serial networks

In a **parallel-serial network** ([Ozdaglar and Srikant, Section 22.2.6, Figure 22.2,
pp. 585–586][OzdaglarSrikant2007]; [Acemoglu and Ozdaglar, Section II,
pp. 1181–1182][AcemogluOzdaglar2007JSAC]), traffic routes across parallel paths `i : Path`, each
composed of a nonempty finite series `SerialLink i` of links owned by distinct profit-maximizing
service providers. Path `i`'s latency is `serialPathLatency latency i u = ∑ j, latency i j u` and
its total price is `serialPathPrice p i = ∑ j, p i j`, so end-user Wardrop routing is
`IsPricedWardrop d R (serialPathLatency latency) (serialPathPrice p) x`.

Serial complementarity introduces double marginalization:

* Weak pure-strategy oligopoly equilibria (`IsSerialOligopolyEquilibrium`) can suffer complete
  coordination failure and arbitrarily small efficiency ([Acemoglu and Ozdaglar, Example 2,
  p. 1184][AcemogluOzdaglar2007JSAC], checked in `CslibFrontierTests/GameTheory/NetworkPricing`).
* Even Harsanyi **strict** oligopoly equilibria (`IsStrictSerialOligopolyEquilibrium`) can restrict
  admitted flow below `d` and approach zero efficiency ([Acemoglu and Ozdaglar, Example 3,
  p. 1185][AcemogluOzdaglar2007JSAC]).
* When all `d` units of traffic are transmitted (`∑ i, x i = d`, called a **strong** oligopoly
  equilibrium in [AcemogluOzdaglar2007JSAC], Definition 6, p. 1185, and stated explicitly before
  [Ozdaglar and Srikant, Theorem 22.5, p. 586][OzdaglarSrikant2007]), social surplus is at least
  `1 / 2` of the social optimum (`serial_strict_oligopoly_surplus_half`), and this `1 / 2` bound is
  asymptotically tight as the serial chain length grows (`serialTightness_surplus_lt_half_add`).

## Main definitions

* `Cslib.GameTheory.serialPathLatency`, `serialPathLatencyDeriv`, `serialPathPrice`: aggregate path
  latency, path latency derivative, and path price across serial links.
* `Cslib.GameTheory.SmoothConvexSerialLatencies`: componentwise `SmoothConvexLatencies` on each
  path's serial links.
* `Cslib.GameTheory.IsSerialOligopolyEquilibrium`, `IsStrictSerialOligopolyEquilibrium`,
  `IsStrongSerialOligopolyEquilibrium`: weak, strict, and full-demand strict oligopoly equilibria
  ([AcemogluOzdaglar2007JSAC], Definitions 3, 5, 6, pp. 1183–1185).
* `Cslib.GameTheory.SerialTightnessLink`, `serialTightnessLatency`, `serialTightnessPrice`,
  `serialTightnessFlow`: two-path `(n + 2)`-serial-link tightness family
  ([AcemogluOzdaglar2007JSAC], Example 4, p. 1185).

## Main results

* `Cslib.GameTheory.IsStrictSerialOligopolyEquilibrium.price_pos_and_flow_pos`: every link price and
  path flow is strictly positive at a strict oligopoly equilibrium ([AcemogluOzdaglar2007JSAC],
  Lemma 1, p. 1184).
* `Cslib.GameTheory.IsSerialOligopolyEquilibrium.mul_pathLatencyDeriv_le_price`,
  `Cslib.GameTheory.IsStrictSerialOligopolyEquilibrium.mul_pathLatencyDeriv_le_price`: each serial
  provider charges at least the full path's marginal congestion cost `x i * L_i'(x i)`
  ([AcemogluOzdaglar2007JSAC], Proposition 6(a), p. 1185).
* `Cslib.GameTheory.serial_oligopoly_surplus_half_of_sum_eq`,
  `Cslib.GameTheory.serial_strict_oligopoly_surplus_half`: tight `1 / 2` social-surplus guarantee
  ([Ozdaglar and Srikant, Theorem 22.5, p. 586][OzdaglarSrikant2007];
  [Acemoglu and Ozdaglar, Theorem 2, p. 1189][AcemogluOzdaglar2007JSAC]).
* `Cslib.GameTheory.serialTightness_isStrongSerialOligopolyEquilibrium`,
  `Cslib.GameTheory.serialTightness_surplus_lt_half_add`: checked strict full-demand equilibrium
  family approaching `1 / 2` ([AcemogluOzdaglar2007JSAC], Example 4, p. 1185).

## References

* [AcemogluOzdaglar2007JSAC]
* [OzdaglarSrikant2007]
-/

public section

namespace Cslib.GameTheory

section Definitions

variable {Path : Type*} {SerialLink : Path → Type*} [∀ i, Fintype (SerialLink i)]

/-- Total latency `∑ j, latency i j u` along serial links of path `i`. -/
@[expose] def serialPathLatency (latency : (i : Path) → SerialLink i → ℝ → ℝ)
    (i : Path) (u : ℝ) : ℝ :=
  ∑ j : SerialLink i, latency i j u

/-- Total latency derivative `∑ j, latencyDeriv i j u` along serial links of path `i`. -/
@[expose] def serialPathLatencyDeriv (latencyDeriv : (i : Path) → SerialLink i → ℝ → ℝ)
    (i : Path) (u : ℝ) : ℝ :=
  ∑ j : SerialLink i, latencyDeriv i j u

/-- Total price `∑ j, p i j` charged along serial links of path `i`. -/
@[expose] def serialPathPrice (p : (i : Path) → SerialLink i → ℝ) (i : Path) : ℝ :=
  ∑ j : SerialLink i, p i j

/-- Smoothness, monotonicity, convexity, and zero-base-delay assumptions on every serial link of a
parallel-serial network. -/
@[expose] def SmoothConvexSerialLatencies
    (latency latencyDeriv : (i : Path) → SerialLink i → ℝ → ℝ) : Prop :=
  ∀ i, SmoothConvexLatencies (latency i) (latencyDeriv i)

/-- Update the price of serial link `(i₀, j₀)` to `q`, keeping all other link prices unchanged. -/
@[expose] def updateSerialPrice [DecidableEq Path] [∀ i, DecidableEq (SerialLink i)]
    (p : (i : Path) → SerialLink i → ℝ) (i₀ : Path) (j₀ : SerialLink i₀) (q : ℝ) :
    (i : Path) → SerialLink i → ℝ :=
  Function.update p i₀ (Function.update (p i₀) j₀ q)

variable [Fintype Path]

/-- Pure-strategy **Oligopoly Equilibrium** on a parallel-serial network, where each serial link
`(i, j)` is owned by an independent profit-maximizing provider ([Acemoglu and Ozdaglar,
Definition 3, p. 1183][AcemogluOzdaglar2007JSAC]). -/
@[expose] def IsSerialOligopolyEquilibrium [DecidableEq Path] [∀ i, DecidableEq (SerialLink i)]
    (d R : ℝ) (latency : (i : Path) → SerialLink i → ℝ → ℝ)
    (p : (i : Path) → SerialLink i → ℝ) (x : Path → ℝ) : Prop :=
  (∀ i j, 0 ≤ p i j) ∧
    IsPricedWardrop d R (serialPathLatency latency) (serialPathPrice p) x ∧
    ∀ i j p' x', 0 ≤ p' →
      IsPricedWardrop d R (serialPathLatency latency)
        (serialPathPrice (updateSerialPrice p i j p')) x' →
      p' * x' i ≤ p i j * x i

/-- Harsanyi **strict Oligopoly Equilibrium** on a parallel-serial network: every serial provider
plays a strict best response ([Ozdaglar and Srikant, Section 22.2.6, p. 586][OzdaglarSrikant2007];
[Acemoglu and Ozdaglar, Definition 5, p. 1184][AcemogluOzdaglar2007JSAC]). -/
@[expose] def IsStrictSerialOligopolyEquilibrium [DecidableEq Path]
    [∀ i, DecidableEq (SerialLink i)] (d R : ℝ)
    (latency : (i : Path) → SerialLink i → ℝ → ℝ)
    (p : (i : Path) → SerialLink i → ℝ) (x : Path → ℝ) : Prop :=
  (∀ i j, 0 ≤ p i j) ∧
    IsPricedWardrop d R (serialPathLatency latency) (serialPathPrice p) x ∧
    ∀ i j p' x', 0 ≤ p' → p' ≠ p i j →
      IsPricedWardrop d R (serialPathLatency latency)
        (serialPathPrice (updateSerialPrice p i j p')) x' →
      p' * x' i < p i j * x i

/-- **Strong Oligopoly Equilibrium** (a strict oligopoly equilibrium in which all `d` units of
traffic are transmitted, `∑ i, x i = d`; [Acemoglu and Ozdaglar, Definition 6,
p. 1185][AcemogluOzdaglar2007JSAC]; [Ozdaglar and Srikant, p. 586][OzdaglarSrikant2007]). -/
@[expose] def IsStrongSerialOligopolyEquilibrium [DecidableEq Path]
    [∀ i, DecidableEq (SerialLink i)] (d R : ℝ)
    (latency : (i : Path) → SerialLink i → ℝ → ℝ)
    (p : (i : Path) → SerialLink i → ℝ) (x : Path → ℝ) : Prop :=
  IsStrictSerialOligopolyEquilibrium d R latency p x ∧ ∑ i, x i = d

end Definitions

section HalfBound

variable {Path : Type*} {SerialLink : Path → Type*} [∀ i, Fintype (SerialLink i)]

/-- Summing smooth convex serial-link latencies along each path yields `SmoothConvexLatencies` at
the path level. -/
theorem SmoothConvexSerialLatencies.toPath
    {latency latencyDeriv : (i : Path) → SerialLink i → ℝ → ℝ}
    (h : SmoothConvexSerialLatencies latency latencyDeriv) :
    SmoothConvexLatencies (serialPathLatency latency) (serialPathLatencyDeriv latencyDeriv) where
  zero_at_zero i := Finset.sum_eq_zero fun j _ => (h i).zero_at_zero j
  monotoneOn i a ha b hb hab := Finset.sum_le_sum fun j _ => (h i).monotoneOn j ha hb hab
  convexOn i := by
    refine ⟨convex_Ici 0, fun a ha b hb w₁ w₂ hw₁ hw₂ hw => ?_⟩
    simp only [serialPathLatency, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => ((h i).convexOn j).2 ha hb hw₁ hw₂ hw
  hasDerivAt i u hu :=
    HasDerivAt.fun_sum fun j _ => (h i).hasDerivAt j u hu

@[simp]
theorem serialPathPrice_updateSerialPrice_self [DecidableEq Path]
    [∀ i, DecidableEq (SerialLink i)] (p : (i : Path) → SerialLink i → ℝ)
    (i : Path) (j : SerialLink i) (q : ℝ) :
    serialPathPrice (updateSerialPrice p i j q) i =
      q + ∑ k ∈ Finset.univ.erase j, p i k := by
  simp only [serialPathPrice, updateSerialPrice, Function.update_self]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  exact Finset.sum_congr rfl fun k hk => Function.update_of_ne (Finset.mem_erase.mp hk).1 _ _

@[simp]
theorem serialPathPrice_updateSerialPrice_of_ne [DecidableEq Path]
    [∀ i, DecidableEq (SerialLink i)] (p : (i : Path) → SerialLink i → ℝ)
    {i m : Path} (hmi : m ≠ i) (j : SerialLink i) (q : ℝ) :
    serialPathPrice (updateSerialPrice p i j q) m = serialPathPrice p m := by
  simp [serialPathPrice, updateSerialPrice, hmi]

variable [Fintype Path]

/-- **Strict OE Positivity** ([Acemoglu and Ozdaglar, Lemma 1, p. 1184][AcemogluOzdaglar2007JSAC]):
at any strict oligopoly equilibrium with `0 ≤ d` and `0 ≤ R`, every link price `p i j` and every
path flow `x i` is strictly positive. -/
theorem IsStrictSerialOligopolyEquilibrium.price_pos_and_flow_pos [DecidableEq Path]
    [∀ i, DecidableEq (SerialLink i)] {d R : ℝ}
    {latency latencyDeriv : (i : Path) → SerialLink i → ℝ → ℝ}
    (h : SmoothConvexSerialLatencies latency latencyDeriv) (hd : 0 ≤ d) (hR : 0 ≤ R)
    {p : (i : Path) → SerialLink i → ℝ} {x : Path → ℝ}
    (hstrict : IsStrictSerialOligopolyEquilibrium d R latency p x) (i : Path) (j : SerialLink i) :
    0 < p i j ∧ 0 < x i := by
  have hpath := h.toPath
  have hprod_pos : 0 < p i j * x i := by
    refine lt_of_le_of_ne (mul_nonneg (hstrict.1 i j) (hstrict.2.1.1.1 i)) fun hzero => ?_
    let pHigh : ℝ := max (p i j + 1) (R + 1)
    have hpHigh_nonneg : 0 ≤ pHigh := by linarith [(le_max_right _ _ : R + 1 ≤ pHigh)]
    have hpHigh_ne : pHigh ≠ p i j := by linarith [(le_max_left _ _ : p i j + 1 ≤ pHigh)]
    obtain ⟨x', hx'⟩ := exists_isPricedWardrop (R := R)
      (fun m => hpath.continuousOn m) hd (serialPathPrice (updateSerialPrice p i j pHigh))
    have hx'i0 : x' i = 0 := by
      refine le_antisymm ?_ (hx'.1.1 i)
      by_contra! hpos
      have hcost_le := hx'.2.2.1 i hpos
      rw [serialPathPrice_updateSerialPrice_self] at hcost_le
      linarith [hpath.latency_nonneg i (hx'.1.1 i),
        Finset.sum_nonneg fun k (_ : k ∈ Finset.univ.erase j) => hstrict.1 i k,
        (le_max_right (p i j + 1) (R + 1) : R + 1 ≤ pHigh)]
    exact lt_irrefl (0 : ℝ) (by
      simpa [hx'i0, ← hzero] using hstrict.2.2 i j pHigh x' hpHigh_nonneg hpHigh_ne hx')
  exact ⟨pos_of_mul_pos_left hprod_pos (hstrict.2.1.1.1 i),
    pos_of_mul_pos_right hprod_pos (hstrict.1 i j)⟩

/-- Shared reduction of single-serial-link downward perturbations to
`markup_ge_mul_deriv_of_wardrop_bestResponse`. -/
private theorem serial_link_markup_ge_of_bestResponse [DecidableEq Path]
    [∀ i, DecidableEq (SerialLink i)] {d R : ℝ}
    {latency latencyDeriv : (i : Path) → SerialLink i → ℝ → ℝ}
    (h : SmoothConvexSerialLatencies latency latencyDeriv)
    {p : (i : Path) → SerialLink i → ℝ} {x : Path → ℝ}
    (hp : ∀ m k, 0 ≤ p m k)
    (hw : IsPricedWardrop d R (serialPathLatency latency) (serialPathPrice p) x)
    (i : Path) (j : SerialLink i)
    (hbr : ∀ p' x', 0 ≤ p' → (p' ≠ p i j ∨ x' i ≤ x i) →
      IsPricedWardrop d R (serialPathLatency latency)
        (serialPathPrice (updateSerialPrice p i j p')) x' →
      p' * x' i ≤ p i j * x i) :
    x i * serialPathLatencyDeriv latencyDeriv i (x i) ≤ p i j := by
  have hpath := h.toPath
  let restP : ℝ := ∑ k ∈ Finset.univ.erase j, p i k
  let effLat : Path → ℝ → ℝ := fun m u =>
    serialPathLatency latency m u + if m = i then restP else 0
  let effPrice : Path → ℝ := fun m => if m = i then p i j else serialPathPrice p m
  have heff_sum (m : Path) (u : ℝ) : effLat m u + effPrice m =
      serialPathLatency latency m u + serialPathPrice p m := by
    rcases eq_or_ne m i with rfl | hmi
    · simp only [effLat, effPrice, ↓reduceIte, restP, serialPathPrice,
        ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      ring
    · simp [effLat, effPrice, hmi]
  have hw_eff : IsPricedWardrop d R effLat effPrice x := by
    simpa only [IsPricedWardrop, heff_sum] using hw
  have hp_eff : ∀ m, 0 ≤ effPrice m := fun m => by
    by_cases hmi : m = i
    · simp [effPrice, hmi, hp i j]
    · simpa [effPrice, hmi, serialPathPrice] using Finset.sum_nonneg fun k _ => hp m k
  have hmono_i : MonotoneOn (effLat i) (Set.Ici 0) := fun a ha b hb hab => by
    simpa only [effLat, ↓reduceIte] using add_le_add (hpath.monotoneOn i ha hb hab) (le_refl restP)
  have hderiv_i : HasDerivAt (effLat i) (serialPathLatencyDeriv latencyDeriv i (x i)) (x i) := by
    simpa only [effLat, ↓reduceIte] using (hpath.hasDerivAt i (x i) (hw.1.1 i)).add_const restP
  have hcomp_mono : ∀ q, q ≠ i → MonotoneOn (effLat q) (Set.Ici 0) := fun q hqi => by
    simpa [effLat, hqi] using hpath.monotoneOn q
  have hcomp_cont : ∀ q, q ≠ i → ContinuousOn (effLat q) (Set.Ici 0) := fun q hqi => by
    simpa [effLat, hqi] using hpath.continuousOn q
  have hlat0 : ∀ m, m = i → 0 ≤ effLat m 0 := fun m hmi => hmi ▸ by
    simpa only [effLat, ↓reduceIte, hpath.zero_at_zero i, zero_add, restP] using
      Finset.sum_nonneg fun k _ => hp i k
  simpa [effPrice] using markup_ge_mul_deriv_of_wardrop_bestResponse (own := fun m => m = i) rfl
    hp_eff hw_eff hmono_i hderiv_i hcomp_mono hcomp_cont hlat0
    fun p' x' hp'0 hp'comp hchange hw' => by
      simp only [Finset.sum_filter, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, effPrice]
      have hw_upd : IsPricedWardrop d R (serialPathLatency latency)
          (serialPathPrice (updateSerialPrice p i j (p' i))) x' := by
        have hcost_upd (m : Path) (u : ℝ) :
            serialPathLatency latency m u + serialPathPrice (updateSerialPrice p i j (p' i)) m =
              effLat m u + p' m := by
          rcases eq_or_ne m i with rfl | hmi
          · simp only [serialPathPrice_updateSerialPrice_self, effLat, ↓reduceIte, restP]
            ring
          · simp [serialPathPrice_updateSerialPrice_of_ne p hmi, hp'comp m hmi, effLat, effPrice,
              hmi]
        simpa only [IsPricedWardrop, hcost_upd] using hw'
      exact hbr (p' i) x' (hp'0 i)
        (hchange.imp (fun ⟨_, hm, hne⟩ => by simpa [effPrice, hm] using hne) id) hw_upd

/-- **Serial Provider Markup Lower Bound** ([Acemoglu and Ozdaglar, Proposition 6(a),
p. 1185][AcemogluOzdaglar2007JSAC]): at any pure-strategy oligopoly equilibrium on a
parallel-serial network, every serial link `(i, j)` charges at least `x i * L_i'(x i)`. -/
theorem IsSerialOligopolyEquilibrium.mul_pathLatencyDeriv_le_price [DecidableEq Path]
    [∀ i, DecidableEq (SerialLink i)] {d R : ℝ}
    {latency latencyDeriv : (i : Path) → SerialLink i → ℝ → ℝ}
    (h : SmoothConvexSerialLatencies latency latencyDeriv)
    {p : (i : Path) → SerialLink i → ℝ} {x : Path → ℝ}
    (hoe : IsSerialOligopolyEquilibrium d R latency p x) (i : Path) (j : SerialLink i) :
    x i * serialPathLatencyDeriv latencyDeriv i (x i) ≤ p i j :=
  serial_link_markup_ge_of_bestResponse h hoe.1 hoe.2.1 i j
    fun p' x' hp' _ hw' => hoe.2.2 i j p' x' hp' hw'

/-- Strict OE specialization of `mul_pathLatencyDeriv_le_price` ([Acemoglu and Ozdaglar,
Proposition 6(a), p. 1185][AcemogluOzdaglar2007JSAC]). -/
theorem IsStrictSerialOligopolyEquilibrium.mul_pathLatencyDeriv_le_price [DecidableEq Path]
    [∀ i, DecidableEq (SerialLink i)] {d R : ℝ}
    {latency latencyDeriv : (i : Path) → SerialLink i → ℝ → ℝ}
    (h : SmoothConvexSerialLatencies latency latencyDeriv)
    {p : (i : Path) → SerialLink i → ℝ} {x : Path → ℝ}
    (hstrict : IsStrictSerialOligopolyEquilibrium d R latency p x)
    (i : Path) (j : SerialLink i) :
    x i * serialPathLatencyDeriv latencyDeriv i (x i) ≤ p i j :=
  serial_link_markup_ge_of_bestResponse h hstrict.1 hstrict.2.1 i j
    fun p' x' hp' hcond hw' => by
      rcases eq_or_ne p' (p i j) with rfl | hne
      · exact mul_le_mul_of_nonneg_left (hcond.resolve_left (not_not.mpr rfl)) (hstrict.1 i j)
      · exact (hstrict.2.2 i j p' x' hp' hne hw').le

private theorem serial_surplus_half_of_markup_and_sum_eq [∀ i, Nonempty (SerialLink i)] {d R : ℝ}
    {latency latencyDeriv : (i : Path) → SerialLink i → ℝ → ℝ}
    (h : SmoothConvexSerialLatencies latency latencyDeriv)
    {p : (i : Path) → SerialLink i → ℝ} {x : Path → ℝ}
    (hp : ∀ i j, 0 ≤ p i j)
    (hw : IsPricedWardrop d R (serialPathLatency latency) (serialPathPrice p) x)
    (hmark : ∀ i j, x i * serialPathLatencyDeriv latencyDeriv i (x i) ≤ p i j)
    (hsum : ∑ i, x i = d) {y : Path → ℝ} (hy : IsFeasiblePricedFlow d y) :
    socialSurplus R (serialPathLatency latency) y ≤
      2 * socialSurplus R (serialPathLatency latency) x := by
  have hpath := h.toPath
  by_cases hy0 : socialSurplus R (serialPathLatency latency) y ≤ 0
  · linarith [hw.socialSurplus_nonneg fun i => Finset.sum_nonneg fun j _ => hp i j]
  push Not at hy0
  have hR_pos : 0 < R := by
    by_contra! hR0
    refine hy0.not_ge (Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg ?_ (hy.1 i))
    linarith [hpath.latency_nonneg i (hy.1 i)]
  have hlat_half : ∀ i, 0 < x i → serialPathLatency latency i (x i) ≤ R / 2 := fun i hxi => by
    obtain ⟨j₀⟩ := (inferInstance : Nonempty (SerialLink i))
    have hp_le : p i j₀ ≤ serialPathPrice p i :=
      Finset.single_le_sum (fun j _ => hp i j) (Finset.mem_univ j₀)
    linarith [hpath.latency_le_mul_deriv i hxi.le, hmark i j₀, hw.2.2.1 i hxi, hp_le]
  have hx_lb : R * d / 2 ≤ socialSurplus R (serialPathLatency latency) x := by
    have hsum_ge : ∑ i, (R / 2) * x i ≤ socialSurplus R (serialPathLatency latency) x :=
      Finset.sum_le_sum fun i _ => (hw.1.1 i).eq_or_lt.elim
        (fun hxi0 => by simp [← hxi0])
        fun hxi => by nlinarith [hlat_half i hxi]
    rw [← Finset.mul_sum, hsum] at hsum_ge
    linarith
  have hy_ub : socialSurplus R (serialPathLatency latency) y ≤ R * d :=
    ((Finset.sum_le_sum fun i _ => by nlinarith [hpath.latency_nonneg i (hy.1 i), hy.1 i]).trans_eq
      (Finset.mul_sum Finset.univ y R).symm).trans (mul_le_mul_of_nonneg_left hy.2 hR_pos.le)
  linarith

/-- **Parallel-Serial Full-Demand Efficiency `1 / 2` Bound**: in any parallel-serial network with at
least one serial link per path and smooth convex latencies (`latency i j 0 = 0`), every
pure-strategy oligopoly equilibrium `(p, x)` transmitting full demand `∑ i, x i = d` achieves at
least `1 / 2` of the social surplus of any feasible flow `y`. -/
theorem serial_oligopoly_surplus_half_of_sum_eq [DecidableEq Path]
    [∀ i, DecidableEq (SerialLink i)] [∀ i, Nonempty (SerialLink i)] {d R : ℝ}
    {latency latencyDeriv : (i : Path) → SerialLink i → ℝ → ℝ}
    (h : SmoothConvexSerialLatencies latency latencyDeriv)
    {p : (i : Path) → SerialLink i → ℝ} {x : Path → ℝ}
    (hoe : IsSerialOligopolyEquilibrium d R latency p x) (hsum : ∑ i, x i = d)
    {y : Path → ℝ} (hy : IsFeasiblePricedFlow d y) :
    socialSurplus R (serialPathLatency latency) y ≤
      2 * socialSurplus R (serialPathLatency latency) x :=
  serial_surplus_half_of_markup_and_sum_eq h hoe.1 hoe.2.1 (hoe.mul_pathLatencyDeriv_le_price h)
    hsum hy

/-- **Parallel-Serial Strict Oligopoly Price of Anarchy (`1 / 2`)** ([Ozdaglar and Srikant,
Theorem 22.5, p. 586][OzdaglarSrikant2007]; [Acemoglu and Ozdaglar, Theorem 2,
p. 1189][AcemogluOzdaglar2007JSAC]): in any parallel-serial network with at least one serial link
per path and smooth convex latencies (`latency i j 0 = 0`), every full-demand strict oligopoly
equilibrium (`IsStrongSerialOligopolyEquilibrium`) achieves at least `1 / 2` of the social surplus
of any feasible flow `y`. -/
theorem serial_strict_oligopoly_surplus_half [DecidableEq Path]
    [∀ i, DecidableEq (SerialLink i)] [∀ i, Nonempty (SerialLink i)] {d R : ℝ}
    {latency latencyDeriv : (i : Path) → SerialLink i → ℝ → ℝ}
    (h : SmoothConvexSerialLatencies latency latencyDeriv)
    {p : (i : Path) → SerialLink i → ℝ} {x : Path → ℝ}
    (hstrong : IsStrongSerialOligopolyEquilibrium d R latency p x)
    {y : Path → ℝ} (hy : IsFeasiblePricedFlow d y) :
    socialSurplus R (serialPathLatency latency) y ≤
      2 * socialSurplus R (serialPathLatency latency) x :=
  serial_surplus_half_of_markup_and_sum_eq h hstrong.1.1 hstrong.1.2.1
    (hstrong.1.mul_pathLatencyDeriv_le_price h) hstrong.2 hy

/-- Ratio form of **Theorem 22.5** ([Ozdaglar and Srikant, Theorem 22.5,
p. 586][OzdaglarSrikant2007]): `1 / 2 ≤ S(x) / S(xS)` when `0 < S(xS)`. -/
theorem serial_strict_oligopoly_efficiency_ge_half [DecidableEq Path]
    [∀ i, DecidableEq (SerialLink i)] [∀ i, Nonempty (SerialLink i)] {d R : ℝ}
    {latency latencyDeriv : (i : Path) → SerialLink i → ℝ → ℝ}
    (h : SmoothConvexSerialLatencies latency latencyDeriv)
    {p : (i : Path) → SerialLink i → ℝ} {x xS : Path → ℝ}
    (hstrong : IsStrongSerialOligopolyEquilibrium d R latency p x)
    (hopt : IsSocialOptimum d R (serialPathLatency latency) xS)
    (hpos : 0 < socialSurplus R (serialPathLatency latency) xS) :
    (1 : ℝ) / 2 ≤
      socialSurplus R (serialPathLatency latency) x /
        socialSurplus R (serialPathLatency latency) xS := by
  rw [div_le_div_iff₀ two_pos hpos]
  linarith [serial_strict_oligopoly_surplus_half h hstrong hopt.1]

end HalfBound

section TightnessFamily

/-!
### Asymptotic tightness of `1 / 2` ([AcemogluOzdaglar2007JSAC], Example 4, p. 1185)

Consider a two-path parallel-serial network (`Fin 2`) with demand `d = 1` and reservation utility
`R = 1`, where path `0` has `n + 2` serial links with identically zero latency and path `1` has a
single link with latency `u / 2`. At the unique full-demand strict oligopoly equilibrium, social
surplus is `1 - ((n + 2) / (n + 4)) ^ 2 / 2 → 1 / 2` while optimal social surplus is `1`.
-/

/-- Serial link index type for the `n`-th tightness instance: `Fin (n + 2)` on path `0` and
`Fin 1` on path `1`. -/
abbrev SerialTightnessLink (n : ℕ) (i : Fin 2) : Type :=
  Fin (if i = 0 then n + 2 else 1)

instance (n : ℕ) (i : Fin 2) : Nonempty (SerialTightnessLink n i) := by
  rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl <;> exact inferInstance

/-- Latency functions of the parallel-serial tightness family: `0` on path `0` and `u / 2` on path
`1` ([Acemoglu and Ozdaglar, Example 4, p. 1185][AcemogluOzdaglar2007JSAC]). -/
@[expose] noncomputable def serialTightnessLatency (n : ℕ) (i : Fin 2)
    (_ : SerialTightnessLink n i) (u : ℝ) : ℝ :=
  if i = 0 then 0 else u / 2

/-- Latency derivatives of `serialTightnessLatency`. -/
@[expose] noncomputable def serialTightnessLatencyDeriv (n : ℕ) (i : Fin 2)
    (_ : SerialTightnessLink n i) (_ : ℝ) : ℝ :=
  if i = 0 then 0 else 1 / 2

/-- Equilibrium prices of the parallel-serial tightness family: `1 / (n + 4)` on each link of path
`0` and `(n + 2) / (2 * (n + 4))` on path `1`. -/
@[expose] noncomputable def serialTightnessPrice (n : ℕ) (i : Fin 2)
    (_ : SerialTightnessLink n i) : ℝ :=
  if i = 0 then 1 / ((n : ℝ) + 4) else ((n : ℝ) + 2) / (2 * ((n : ℝ) + 4))

/-- Equilibrium path flows `(2 / (n + 4), (n + 2) / (n + 4))` of the tightness family. -/
@[expose] noncomputable def serialTightnessFlow (n : ℕ) (i : Fin 2) : ℝ :=
  if i = 0 then 2 / ((n : ℝ) + 4) else ((n : ℝ) + 2) / ((n : ℝ) + 4)

/-- Socially optimal path flows `(1, 0)` of the tightness family. -/
@[expose] def serialTightnessOptFlow (i : Fin 2) : ℝ :=
  if i = 0 then 1 else 0

theorem serialTightness_smoothConvex (n : ℕ) :
    SmoothConvexSerialLatencies (serialTightnessLatency n) (serialTightnessLatencyDeriv n) := by
  intro i
  rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
  · exact ⟨fun _ => rfl, fun _ _ _ _ _ _ => le_rfl,
      fun _ => ⟨convex_Ici 0, fun _ _ _ _ _ _ _ _ _ => by simp [serialTightnessLatency]⟩,
      fun _ x _ => hasDerivAt_const x 0⟩
  · refine ⟨fun _ => by simp [serialTightnessLatency],
      fun _ _ _ _ _ hab => div_le_div_of_nonneg_right hab zero_le_two,
      fun _ => ⟨convex_Ici 0, fun _ _ _ _ _ _ _ _ _ => ?_⟩,
      fun _ x _ => (hasDerivAt_id x).div_const 2⟩
    simp only [serialTightnessLatency, one_ne_zero, ↓reduceIte, smul_eq_mul]
    linarith

private theorem serialTightness_pathLatency_zero (n : ℕ) (u : ℝ) :
    serialPathLatency (serialTightnessLatency n) 0 u = 0 := by
  simp [serialPathLatency, SerialTightnessLink, serialTightnessLatency]

private theorem serialTightness_pathLatency_one (n : ℕ) (u : ℝ) :
    serialPathLatency (serialTightnessLatency n) 1 u = u / 2 := by
  simp [serialPathLatency, SerialTightnessLink, serialTightnessLatency]

private theorem serialTightness_pathPrice_zero (n : ℕ) :
    serialPathPrice (serialTightnessPrice n) 0 = ((n : ℝ) + 2) / ((n : ℝ) + 4) := by
  simp only [serialPathPrice, SerialTightnessLink, ↓reduceIte, serialTightnessPrice,
    Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  push_cast
  ring

private theorem serialTightness_pathPrice_one (n : ℕ) :
    serialPathPrice (serialTightnessPrice n) 1 = ((n : ℝ) + 2) / (2 * ((n : ℝ) + 4)) := by
  simp [serialPathPrice, SerialTightnessLink, serialTightnessPrice]

/-- `(serialTightnessPrice n, serialTightnessFlow n)` is a full-demand strict oligopoly equilibrium
(`IsStrongSerialOligopolyEquilibrium`) for every `n : ℕ` ([Acemoglu and Ozdaglar, Example 4,
p. 1185][AcemogluOzdaglar2007JSAC]). -/
theorem serialTightness_isStrongSerialOligopolyEquilibrium (n : ℕ) :
    IsStrongSerialOligopolyEquilibrium 1 1 (serialTightnessLatency n)
      (serialTightnessPrice n) (serialTightnessFlow n) := by
  have hn4 : (0 : ℝ) < (n : ℝ) + 4 := by positivity
  have hsum : ∑ i : Fin 2, serialTightnessFlow n i = 1 := by
    rw [Fin.sum_univ_two]
    simp only [serialTightnessFlow, ↓reduceIte, one_ne_zero]
    field_simp
    ring
  have heff0 : serialPathLatency (serialTightnessLatency n) 0 (serialTightnessFlow n 0) +
      serialPathPrice (serialTightnessPrice n) 0 = ((n : ℝ) + 2) / ((n : ℝ) + 4) := by
    rw [serialTightness_pathLatency_zero, serialTightness_pathPrice_zero, zero_add]
  have heff1 : serialPathLatency (serialTightnessLatency n) 1 (serialTightnessFlow n 1) +
      serialPathPrice (serialTightnessPrice n) 1 = ((n : ℝ) + 2) / ((n : ℝ) + 4) := by
    rw [serialTightness_pathLatency_one, serialTightness_pathPrice_one]
    simp only [serialTightnessFlow, one_ne_zero, ↓reduceIte]
    field_simp
    ring
  have hc_lt_one : ((n : ℝ) + 2) / ((n : ℝ) + 4) < 1 := (div_lt_one hn4).mpr (by linarith)
  have hw : IsPricedWardrop 1 1 (serialPathLatency (serialTightnessLatency n))
      (serialPathPrice (serialTightnessPrice n)) (serialTightnessFlow n) := by
    refine ⟨⟨fun i => ?_, hsum.le⟩, fun a b _ => ?_, fun a _ => ?_, fun _ => hsum⟩
    · rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl <;>
        simp only [serialTightnessFlow, ↓reduceIte, one_ne_zero] <;> positivity
    · rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl <;>
        rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl <;>
        linarith [heff0, heff1]
    · rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl <;>
        linarith [heff0, heff1, hc_lt_one]
  refine ⟨⟨fun i _ => ?_, hw, fun i j p' x' hp' hne hw' => ?_⟩, hsum⟩
  · rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl <;>
      simp only [serialTightnessPrice, ↓reduceIte, one_ne_zero] <;> positivity
  · have hprofit {p x : ℝ} (hp : 0 < p) (hne : p' ≠ p) (hx : 0 ≤ x)
        (hbound : 0 < x → x ≤ 2 * (2 * p - p')) : p' * x < p * (2 * p) := by
      rcases hx.eq_or_lt with hzero | hpos
      · rw [← hzero, mul_zero]; positivity
      · nlinarith [mul_le_mul_of_nonneg_left (hbound hpos) hp',
          sq_pos_of_ne_zero (sub_ne_zero.mpr hne)]
    have hremaining (a : Fin 2) (k : SerialTightnessLink n a) :
        ∑ l ∈ Finset.univ.erase k, serialTightnessPrice n a l =
          serialPathPrice (serialTightnessPrice n) a - serialTightnessPrice n a k :=
      eq_sub_of_add_eq (Finset.sum_erase_add _ _ (Finset.mem_univ k))
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
    · -- Deviation by a link j on path 0:
      have htwice : 2 * serialTightnessPrice n 0 j = 2 / ((n : ℝ) + 4) := mul_one_div 2 _
      rw [serialTightnessFlow, ite_eq_left rfl, ← htwice]
      refine hprofit (by simp only [serialTightnessPrice, ↓reduceIte]; positivity) hne
        (hw'.1.1 0) fun hx0_pos => ?_
      have hcost0 : serialPathLatency (serialTightnessLatency n) 0 (x' 0) +
          serialPathPrice (updateSerialPrice (serialTightnessPrice n) 0 j p') 0 =
          p' + ((n : ℝ) + 1) / ((n : ℝ) + 4) := by
        rw [serialTightness_pathLatency_zero, serialPathPrice_updateSerialPrice_self,
          hremaining, serialTightness_pathPrice_zero, zero_add]
        simp only [serialTightnessPrice, ↓reduceIte]
        ring
      have hcost1 : serialPathLatency (serialTightnessLatency n) 1 (x' 1) +
          serialPathPrice (updateSerialPrice (serialTightnessPrice n) 0 j p') 1 =
          x' 1 / 2 + ((n : ℝ) + 2) / (2 * ((n : ℝ) + 4)) := by
        rw [serialTightness_pathLatency_one,
          serialPathPrice_updateSerialPrice_of_ne _ (by decide), serialTightness_pathPrice_one]
      have hsum_le : x' 0 + x' 1 ≤ 1 := by simpa only [Fin.sum_univ_two] using hw'.1.2
      have hid : 1 + 2 * (((n : ℝ) + 2) / (2 * ((n : ℝ) + 4))) -
          2 * (((n : ℝ) + 1) / ((n : ℝ) + 4)) = 2 * (2 / ((n : ℝ) + 4)) := by field_simp; ring
      linarith [hcost0 ▸ hcost1 ▸ hw'.2.1 0 1 hx0_pos, hsum_le, hid, htwice]
    · -- Deviation by the unique link j on path 1:
      have htwice : 2 * serialTightnessPrice n 1 j = ((n : ℝ) + 2) / ((n : ℝ) + 4) := by
        simp only [serialTightnessPrice, one_ne_zero, ↓reduceIte]
        field_simp
      rw [serialTightnessFlow, ite_eq_right one_ne_zero, ← htwice]
      refine hprofit (by simp only [serialTightnessPrice, one_ne_zero, ↓reduceIte]; positivity)
        hne (hw'.1.1 1) fun hx1_pos => ?_
      have hcost0 : serialPathLatency (serialTightnessLatency n) 0 (x' 0) +
          serialPathPrice (updateSerialPrice (serialTightnessPrice n) 1 j p') 0 =
          ((n : ℝ) + 2) / ((n : ℝ) + 4) := by
        rw [serialTightness_pathLatency_zero,
          serialPathPrice_updateSerialPrice_of_ne _ (by decide), serialTightness_pathPrice_zero,
          zero_add]
      have hcost1 : serialPathLatency (serialTightnessLatency n) 1 (x' 1) +
          serialPathPrice (updateSerialPrice (serialTightnessPrice n) 1 j p') 1 =
          x' 1 / 2 + p' := by
        rw [serialTightness_pathLatency_one, serialPathPrice_updateSerialPrice_self,
          hremaining, serialTightness_pathPrice_one]
        simp only [serialTightnessPrice, one_ne_zero, ↓reduceIte, sub_self, add_zero]
      linarith [hcost0 ▸ hcost1 ▸ hw'.2.1 1 0 hx1_pos, htwice]

/-- `serialTightnessOptFlow` (`(1, 0)`) is a social optimum with social surplus `1`. -/
theorem serialTightness_isSocialOptimum (n : ℕ) :
    IsSocialOptimum 1 1 (serialPathLatency (serialTightnessLatency n)) serialTightnessOptFlow ∧
      socialSurplus 1 (serialPathLatency (serialTightnessLatency n))
        serialTightnessOptFlow = 1 := by
  have hval : socialSurplus 1 (serialPathLatency (serialTightnessLatency n))
      serialTightnessOptFlow = 1 := by
    simp only [socialSurplus, Fin.sum_univ_two, serialTightnessOptFlow, ↓reduceIte, one_ne_zero,
      serialTightness_pathLatency_zero, serialTightness_pathLatency_one]
    ring
  refine ⟨⟨⟨fun i => ?_, ?_⟩, fun y hy => ?_⟩, hval⟩
  · rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl <;> simp [serialTightnessOptFlow]
  · simp [serialTightnessOptFlow]
  rw [hval]
  simp only [socialSurplus, Fin.sum_univ_two, serialTightness_pathLatency_zero,
    serialTightness_pathLatency_one]
  have hysum : y 0 + y 1 ≤ 1 := by simpa only [Fin.sum_univ_two] using hy.2
  nlinarith [hy.1 0, hy.1 1, sq_nonneg (y 1)]

/-- Exact equilibrium social surplus `1 - ((n + 2) / (n + 4)) ^ 2 / 2` of the tightness family. -/
theorem serialTightness_socialSurplus (n : ℕ) :
    socialSurplus 1 (serialPathLatency (serialTightnessLatency n)) (serialTightnessFlow n) =
      1 - (((n : ℝ) + 2) / ((n : ℝ) + 4)) ^ 2 / 2 := by
  have hn4 : ((n : ℝ) + 4) ≠ 0 := by positivity
  simp only [socialSurplus, Fin.sum_univ_two, serialTightnessFlow, ↓reduceIte, one_ne_zero,
    serialTightness_pathLatency_zero, serialTightness_pathLatency_one]
  field_simp
  ring

/-- **Asymptotic tightness of the `1 / 2` parallel-serial bound** ([Ozdaglar and Srikant,
Theorem 22.5, p. 586][OzdaglarSrikant2007]; [Acemoglu and Ozdaglar, Example 4,
p. 1185][AcemogluOzdaglar2007JSAC]): for every `ε > 0`, there exists `n : ℕ` whose checked
full-demand strict oligopoly equilibrium has efficiency strictly below `1 / 2 + ε`. -/
theorem serialTightness_surplus_lt_half_add {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ,
      socialSurplus 1 (serialPathLatency (serialTightnessLatency n)) (serialTightnessFlow n) <
        (1 / 2 + ε) * socialSurplus 1 (serialPathLatency (serialTightnessLatency n))
          serialTightnessOptFlow := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ε)
  refine ⟨n, ?_⟩
  rw [serialTightness_socialSurplus, (serialTightness_isSocialOptimum n).2, mul_one]
  have hn4 : (0 : ℝ) < (n : ℝ) + 4 := by positivity
  -- Show 1 - ((n+2)/(n+4))^2 / 2 = 1/2 + 2*(n+3)/(n+4)^2 < 1/2 + 2/(n+4) < 1/2 + ε:
  have hid : 1 - (((n : ℝ) + 2) / ((n : ℝ) + 4)) ^ 2 / 2 =
      1 / 2 + 2 * ((n : ℝ) + 3) / ((n : ℝ) + 4) ^ 2 := by
    field_simp
    ring
  rw [hid, add_lt_add_iff_left, div_lt_iff₀ (sq_pos_of_pos hn4)]
  nlinarith [(div_lt_iff₀ hε).mp hn, Nat.cast_nonneg (α := ℝ) n]

end TightnessFamily

end Cslib.GameTheory
