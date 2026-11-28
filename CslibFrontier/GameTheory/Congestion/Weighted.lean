/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Congestion.Basic
public import CslibFrontier.GameTheory.Strategic.Stability
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Finite.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weighted atomic congestion games

In a **weighted atomic congestion game**, finitely many players `i : ι` route unsplittable demands
`weight i : ℝ` across finite sets of resources `resources i a : Finset E`. Given a strategy profile
`s`, the **load** `load s e` on resource `e` is the total weight of the players whose chosen
resource set contains `e`. Each unit of traffic on `e` incurs `latency e (load s e)`, so player
`i` incurs per-unit latency `unitCost i s = ∑ e ∈ resources i (s i), latency e (load s e)` and
demand-weighted cost `weight i * unitCost i s`, making the social cost equal to
`∑ e, load s e * latency e (load s e)` (Nisan–Roughgarden–Tardos–Vazirani, Chapter 18,
Definition 18.5; locator not re-verified against primary PDF).

Unlike unweighted congestion games (`Cslib.GameTheory.CongestionGame`), weighted atomic congestion
games with nonlinear nondecreasing latencies need not admit pure Nash equilibria: Goemans, Mirrokni,
and Vetta (FOCS 2005; NRTV Chapter 18, Example 18.7; locator not re-verified against primary PDF)
exhibited a two-player (`weight = fun i => if i = 0 then 1 else 2`), four-path, six-edge network
`gmvGame` with degree-`2` polynomial latencies that has no pure Nash equilibrium and therefore no
generalized ordinal potential.

By contrast, Fotakis, Kontogiannis, and Spirakis (Theoretical Computer Science 2005; NRTV
Chapter 18, Theorem 18.15 and Exercise 18.4; locators not re-verified against primary PDF) showed
that every weighted atomic congestion game with **affine** latencies `latency e x = a e * x + b e`
is a potential game: half of
`affinePotential s = ∑ e, (load s e * latency e (load s e) + ∑_{i : e ∈ s_i} w_i * latency e w_i)`
is an **exact potential** of `toCostGame`. Consequently, every finite weighted affine congestion
game has the finite improvement property, admits a pure Nash equilibrium, and (for nonnegative
weights and affine coefficients) has **price of stability at most `2`**.

## Main definitions

* `Cslib.GameTheory.WeightedCongestionGame`: an atomic congestion game with player demand weights
  `weight : ι → ℝ` and load-dependent resource latencies `latency : E → ℝ → ℝ`.
* `Cslib.GameTheory.WeightedCongestionGame.load`: total player weight on a resource.
* `Cslib.GameTheory.WeightedCongestionGame.unitCost`: per-unit resource latency experienced by a
  player.
* `Cslib.GameTheory.WeightedCongestionGame.toCostGame`: demand-weighted strategic game
  `cost i s = weight i * unitCost i s`.
* `Cslib.GameTheory.WeightedCongestionGame.toUniformCongestionGame`: reduction of an equal-weight
  game (`∀ i, weight i = w`) to `Cslib.GameTheory.CongestionGame`.
* `Cslib.GameTheory.WeightedCongestionGame.HasAffineLatencies`: nonnegative affine latencies
  `latency e x = a e * x + b e` (`a e, b e ≥ 0`).
* `Cslib.GameTheory.WeightedCongestionGame.affinePotential`: the Fotakis–Kontogiannis–Spirakis
  weighted affine potential.
* `Cslib.GameTheory.WeightedCongestionGame.gmvGame`: the two-player quadratic Goemans–Mirrokni–Vetta
  routing game without pure Nash equilibria.

## Main results

* `Cslib.GameTheory.WeightedCongestionGame.isPureNash_toCostGame_iff`: for positive weights, pure
  Nash equilibria of `toCostGame` are profiles where no player can strictly lower `unitCost`.
* `Cslib.GameTheory.WeightedCongestionGame.socialCost_toCostGame`: the social cost equals
  `∑ e, load s e * latency e (load s e)`.
* `Cslib.GameTheory.WeightedCongestionGame.exists_isPureNash_of_uniform_weight`: equal-weight
  atomic congestion games with arbitrary latencies have pure Nash equilibria and the FIP.
* `Cslib.GameTheory.WeightedCongestionGame.affinePotential_update_sub`: exact `2 * weight i`
  unilateral-deviation identity for `affinePotential` under affine latencies.
* `WeightedCongestionGame.HasAffineLatencies.isExactPotential_half_affinePotential`: `1 / 2` of
  `affinePotential` is an exact potential of `toCostGame` under affine latencies.
* `WeightedCongestionGame.HasAffineLatencies.hasFIP`,
  `WeightedCongestionGame.HasAffineLatencies.exists_isPureNash`: finite weighted affine congestion
  games have the FIP and pure Nash equilibria.
* `WeightedCongestionGame.HasAffineLatencies.exists_isPureNash_socialCost_le_two_mul`: the price of
  stability of weighted affine congestion games is at most `2`.
* `Cslib.GameTheory.WeightedCongestionGame.not_exists_isPureNash_gmvGame`,
  `Cslib.GameTheory.WeightedCongestionGame.not_hasFIP_gmvGame`,
  `Cslib.GameTheory.WeightedCongestionGame.not_exists_isGeneralizedOrdinalPotential_gmvGame`:
  `gmvGame` has no pure Nash equilibrium, lacks the FIP, and admits no generalized ordinal
  potential.

## References

* [AwerbuchAzarEpstein2005]
* [MondererShapley1996]
* [NisanRoughgardenTardosVazirani2007]
* [Rosenthal1973]
-/

public section

namespace Cslib.GameTheory

/-- A **weighted atomic congestion game** on resources `E`: player `i` routes unsplittable demand
`weight i` across the finite resource set `resources i a` when playing `a : S i`, and each unit of
demand on resource `e` pays `latency e x` when the total weight on `e` is `x`
([NisanRoughgardenTardosVazirani2007], Chapter 18, Definition 18.5; locator not re-verified against
primary PDF). -/
structure WeightedCongestionGame (ι : Type*) (S : ι → Type*) (E : Type*) where
  /-- The resources used by player `i` when it plays the strategy `a`. -/
  resources : ∀ i, S i → Finset E
  /-- The demand weight routed by player `i`. -/
  weight : ι → ℝ
  /-- The per-unit latency of resource `e` when its total load is `x`. -/
  latency : E → ℝ → ℝ

namespace WeightedCongestionGame

section Basic

variable {ι : Type*} {S : ι → Type*} {E : Type*} [Fintype ι] [DecidableEq E]
  (W : WeightedCongestionGame ι S E)

/-- The **load** on resource `e` at profile `s`: the total weight of players whose chosen resource
set contains `e`. -/
@[expose] def load (s : ∀ i, S i) (e : E) : ℝ :=
  ∑ i with e ∈ W.resources i (s i), W.weight i

/-- The **per-unit latency** experienced by player `i` at profile `s`: the sum of the latencies of
its chosen resources at their current loads. -/
@[expose] def unitCost (i : ι) (s : ∀ i, S i) : ℝ :=
  ∑ e ∈ W.resources i (s i), W.latency e (W.load s e)

/-- The strategic game defined by a weighted congestion game: player `i` pays its demand `weight i`
times its per-unit resource latency `unitCost i s`, so `socialCost` equals total system latency
`∑ e, load s e * latency e (load s e)`. -/
@[expose] def toCostGame : CostGame ι S where
  cost i s := W.weight i * W.unitCost i s

@[simp]
theorem toCostGame_cost (i : ι) (s : ∀ i, S i) :
    W.toCostGame.cost i s = W.weight i * W.unitCost i s := rfl

/-- When all player weights are strictly positive, a profile is a pure Nash equilibrium of
`toCostGame` iff no player can strictly reduce its per-unit path latency `unitCost`
([NisanRoughgardenTardosVazirani2007], Chapter 18, Definition 18.5; locator not re-verified against
primary PDF). -/
theorem isPureNash_toCostGame_iff [DecidableEq ι] (hw : ∀ i, 0 < W.weight i) {s : ∀ i, S i} :
    W.toCostGame.IsPureNash s ↔
      ∀ i (a : S i), W.unitCost i s ≤ W.unitCost i (Function.update s i a) :=
  forall₂_congr fun i _ => mul_le_mul_iff_right₀ (hw i)

/-- Exchanging sums over players and resources: summing `weight i * f e` over every player's chosen
resources weights each resource `e` by `load s e`. -/
theorem sum_weight_mul_sum_resources [Fintype E] (s : ∀ i, S i) (f : E → ℝ) :
    ∑ i, W.weight i * ∑ e ∈ W.resources i (s i), f e = ∑ e, W.load s e * f e := by
  have hlhs (i : ι) : W.weight i * ∑ e ∈ W.resources i (s i), f e =
      ∑ e : E, if e ∈ W.resources i (s i) then W.weight i * f e else 0 := by
    rw [Finset.mul_sum, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  simp only [hlhs]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => by rw [← Finset.sum_filter, load, Finset.sum_mul]

/-- The social cost of a weighted congestion game is `∑ e, load s e * latency e (load s e)`. -/
theorem socialCost_toCostGame [Fintype E] (s : ∀ i, S i) :
    W.toCostGame.socialCost s = ∑ e, W.load s e * W.latency e (W.load s e) :=
  W.sum_weight_mul_sum_resources s fun e => W.latency e (W.load s e)

/-- Nonnegative weights produce nonnegative resource loads. -/
theorem load_nonneg (hw : ∀ i, 0 ≤ W.weight i) (s : ∀ i, S i) (e : E) : 0 ≤ W.load s e :=
  Finset.sum_nonneg fun i _ => hw i

/-- Decomposition of `load t e` into player `i`'s contribution and the remaining players' load. -/
theorem load_eq_ite_add_erase [DecidableEq ι] (t : ∀ j, S j) (i : ι) (e : E) :
    W.load t e = (if e ∈ W.resources i (t i) then W.weight i else 0) +
      ∑ j ∈ Finset.univ.erase i, if e ∈ W.resources j (t j) then W.weight j else 0 := by
  rw [load, Finset.sum_filter, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]

section Deviation

variable [DecidableEq ι]

/-- Unilateral deviation formula for resource load: updating player `i` to `a` replaces player `i`'s
demand indicator while leaving all other players' contributions unchanged. -/
theorem load_update (s : ∀ j, S j) (i : ι) (a : S i) (e : E) :
    W.load (Function.update s i a) e =
      W.load s e + (if e ∈ W.resources i a then W.weight i else 0) -
        (if e ∈ W.resources i (s i) then W.weight i else 0) := by
  have hrest : (∑ j ∈ Finset.univ.erase i,
      if e ∈ W.resources j (Function.update s i a j) then W.weight j else 0) =
      ∑ j ∈ Finset.univ.erase i, if e ∈ W.resources j (s j) then W.weight j else 0 :=
    Finset.sum_congr rfl fun j hj => by
      simp only [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [W.load_eq_ite_add_erase (Function.update s i a) i e, W.load_eq_ite_add_erase s i e,
    Function.update_self, hrest]
  ring

/-- For nonnegative player weight `weight i`, a unilateral deviation of player `i` increases the
load on any resource by at most `weight i`. -/
theorem load_update_le {s : ∀ j, S j} {i : ι} (hi : 0 ≤ W.weight i) (a : S i) (e : E) :
    W.load (Function.update s i a) e ≤ W.load s e + W.weight i := by
  rw [W.load_update s i a e]
  split_ifs <;> linarith

end Deviation

/-! ### Reduction of uniform-weight games to `CongestionGame` -/

/-- When all players share a common demand weight `w`, `W` induces an unweighted
`CongestionGame` with scaled count latencies `w * W.latency e (k * w)`. -/
@[expose] def toUniformCongestionGame (w : ℝ) : CongestionGame ι S E where
  resources := W.resources
  latency e k := w * W.latency e ((k : ℝ) * w)

theorem load_eq_uniform (w : ℝ) (hw : ∀ i, W.weight i = w) (s : ∀ i, S i) (e : E) :
    W.load s e = ((W.toUniformCongestionGame w).load s e : ℝ) * w := by
  simp only [load, CongestionGame.load, hw, Finset.sum_const, nsmul_eq_mul]
  congr 2

/-- If every player has weight `w`, `toUniformCongestionGame w` induces the exact same `CostGame`
as `W`. -/
theorem toCostGame_toUniformCongestionGame (w : ℝ) (hw : ∀ i, W.weight i = w) :
    (W.toUniformCongestionGame w).toCostGame = W.toCostGame := by
  unfold CongestionGame.toCostGame toCostGame
  congr with i s
  simp [toUniformCongestionGame, unitCost, hw i, Finset.mul_sum, W.load_eq_uniform w hw s]

/-- **Equilibrium existence for equal-weight atomic congestion games**
([NisanRoughgardenTardosVazirani2007], Chapter 18, Theorem 18.12; locator not re-verified against
primary PDF): if all players route a common demand `w`, `W` has the finite improvement property
and admits a pure Nash equilibrium for arbitrary latency functions. -/
theorem hasFIP_of_uniform_weight [DecidableEq ι] [Finite E] [∀ i, Finite (S i)]
    (w : ℝ) (hw : ∀ i, W.weight i = w) : W.toCostGame.HasFIP := by
  rw [← W.toCostGame_toUniformCongestionGame w hw]
  exact (W.toUniformCongestionGame w).hasFIP

theorem exists_isPureNash_of_uniform_weight [DecidableEq ι] [Finite E] [∀ i, Finite (S i)]
    [∀ i, Nonempty (S i)] (w : ℝ) (hw : ∀ i, W.weight i = w) :
    ∃ s, W.toCostGame.IsPureNash s := by
  rw [← W.toCostGame_toUniformCongestionGame w hw]
  exact (W.toUniformCongestionGame w).exists_isPureNash

/-! ### Fotakis–Kontogiannis–Spirakis affine weighted potential -/

/-- `W` has **affine latencies** if there are nonnegative `a e, b e ≥ 0` with
`latency e x = a e * x + b e` for every resource `e` and load `x`. -/
@[expose] def HasAffineLatencies : Prop :=
  ∃ a b : E → ℝ, (∀ e, 0 ≤ a e) ∧ (∀ e, 0 ≤ b e) ∧ ∀ e x, W.latency e x = a e * x + b e

/-- The **Fotakis–Kontogiannis–Spirakis affine potential**
([NisanRoughgardenTardosVazirani2007], Chapter 18, Exercise 18.4; locator not re-verified against
primary PDF):
`Φ(s) = ∑ e, (load s e * latency e (load s e) + ∑_{i : e ∈ s_i} weight i * latency e (weight i))`.
-/
def affinePotential [Fintype E] (s : ∀ i, S i) : ℝ :=
  ∑ e, (W.load s e * W.latency e (W.load s e) +
    ∑ i with e ∈ W.resources i (s i), W.weight i * W.latency e (W.weight i))

theorem affinePotential_def [Fintype E] (s : ∀ i, S i) :
    W.affinePotential s = ∑ e, (W.load s e * W.latency e (W.load s e) +
      ∑ i with e ∈ W.resources i (s i), W.weight i * W.latency e (W.weight i)) := by
  rw [affinePotential]

/-- **Exact `2 * weight i` deviation identity for `affinePotential`**
([NisanRoughgardenTardosVazirani2007], Chapter 18, Exercise 18.4; locator not re-verified against
primary PDF): for any affine latencies `latency e x = a e * x + b e` (without sign hypotheses on
`a`, `b`, or `weight`), a unilateral deviation changes `affinePotential` by `2 * weight i` times
the change in player `i`'s per-unit cost `unitCost`. -/
theorem affinePotential_update_sub [DecidableEq ι] [Fintype E] {a b : E → ℝ}
    (hl : ∀ e x, W.latency e x = a e * x + b e) (s : ∀ j, S j) (i : ι) (a' : S i) :
    W.affinePotential (Function.update s i a') - W.affinePotential s =
      2 * W.weight i * (W.unitCost i (Function.update s i a') - W.unitCost i s) := by
  set s' := Function.update s i a' with hs'_def
  have hs'i : s' i = a' := Function.update_self i a' s
  have hself (t : ∀ j, S j) (e : E) :
      (∑ j with e ∈ W.resources j (t j), W.weight j * W.latency e (W.weight j)) =
        (if e ∈ W.resources i (t i) then W.weight i * W.latency e (W.weight i) else 0) +
          ∑ j ∈ Finset.univ.erase i,
            if e ∈ W.resources j (t j) then W.weight j * W.latency e (W.weight j) else 0 := by
    rw [Finset.sum_filter, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hpt (e : E) :
      (W.load s' e * W.latency e (W.load s' e) +
          ∑ j with e ∈ W.resources j (s' j), W.weight j * W.latency e (W.weight j)) -
        (W.load s e * W.latency e (W.load s e) +
          ∑ j with e ∈ W.resources j (s j), W.weight j * W.latency e (W.weight j)) =
      2 * W.weight i *
        ((if e ∈ W.resources i a' then W.latency e (W.load s' e) else 0) -
          (if e ∈ W.resources i (s i) then W.latency e (W.load s e) else 0)) := by
    have hrest : (∑ j ∈ Finset.univ.erase i,
        if e ∈ W.resources j (s' j) then W.weight j * W.latency e (W.weight j) else 0) =
        ∑ j ∈ Finset.univ.erase i,
          if e ∈ W.resources j (s j) then W.weight j * W.latency e (W.weight j) else 0 :=
      Finset.sum_congr rfl fun j hj => by
        simp only [hs'_def, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hself s' e, hself s e, hrest, hs'i, hs'_def, W.load_update s i a' e]
    simp only [hl]
    by_cases h1 : e ∈ W.resources i (s i) <;> by_cases h2 : e ∈ W.resources i a' <;>
      simp only [h1, h2, ↓reduceIte] <;> ring
  rw [affinePotential_def, affinePotential_def, ← Finset.sum_sub_distrib]
  simp only [hpt, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter]
  rw [unitCost, unitCost, hs'i]

/-- Half of `affinePotential` is an **exact potential** of `toCostGame` whenever latencies are
affine ([NisanRoughgardenTardosVazirani2007], Chapter 18, Exercise 18.4 and Chapter 19,
Exercise 19.11(b); locators not re-verified against primary PDF). -/
theorem isExactPotential_half_affinePotential_of_forall [DecidableEq ι] [Fintype E] {a b : E → ℝ}
    (hl : ∀ e x, W.latency e x = a e * x + b e) :
    W.toCostGame.IsExactPotential (fun s => 1 / 2 * W.affinePotential s) := by
  intro s i a'
  dsimp only [toCostGame]
  linarith [W.affinePotential_update_sub hl s i a']

variable {W}

omit [Fintype ι] [DecidableEq E] in
/-- Nonnegative affine latencies are nondecreasing. -/
theorem HasAffineLatencies.monotone_latency (h : W.HasAffineLatencies) (e : E) :
    Monotone (W.latency e) := by
  obtain ⟨a, b, ha, -, hl⟩ := h
  intro x y hxy
  rw [hl, hl]
  nlinarith [ha e]

theorem HasAffineLatencies.isExactPotential_half_affinePotential [DecidableEq ι] [Fintype E]
    (h : W.HasAffineLatencies) :
    W.toCostGame.IsExactPotential (fun s => 1 / 2 * W.affinePotential s) := by
  obtain ⟨a, b, -, -, hl⟩ := h
  exact W.isExactPotential_half_affinePotential_of_forall hl

theorem HasAffineLatencies.isOrdinalPotential_affinePotential [DecidableEq ι] [Fintype E]
    (h : W.HasAffineLatencies) : W.toCostGame.IsOrdinalPotential W.affinePotential := by
  intro s i a'
  have hex := h.isExactPotential_half_affinePotential s i a'
  constructor <;> intro hlt <;> linarith

/-- **Finite improvement property for weighted affine congestion games** (Fotakis, Kontogiannis,
and Spirakis 2005; [NisanRoughgardenTardosVazirani2007], Chapter 18, Theorem 18.15; locator not
re-verified against primary PDF). -/
theorem HasAffineLatencies.hasFIP [DecidableEq ι] [Finite E] [∀ i, Finite (S i)]
    (h : W.HasAffineLatencies) : W.toCostGame.HasFIP := by
  have := Fintype.ofFinite E
  exact h.isExactPotential_half_affinePotential.isGeneralizedOrdinalPotential.hasFIP

/-- **Pure Nash equilibrium existence for weighted affine congestion games** (Fotakis,
Kontogiannis, and Spirakis 2005; [NisanRoughgardenTardosVazirani2007], Chapter 18, Theorem 18.15;
locator not re-verified against primary PDF). -/
theorem HasAffineLatencies.exists_isPureNash [DecidableEq ι] [Finite E] [∀ i, Finite (S i)]
    [∀ i, Nonempty (S i)] (h : W.HasAffineLatencies) : ∃ s, W.toCostGame.IsPureNash s :=
  h.hasFIP.exists_isPureNash

/-- Under nonnegative player weights and nonnegative affine latencies,
`socialCost s ≤ affinePotential s ≤ 2 * socialCost s`. -/
theorem HasAffineLatencies.socialCost_le_affinePotential [Fintype E]
    (h : W.HasAffineLatencies) (hw : ∀ i, 0 ≤ W.weight i) (s : ∀ i, S i) :
    W.toCostGame.socialCost s ≤ W.affinePotential s := by
  obtain ⟨a, b, ha, hb, hl⟩ := h
  rw [W.socialCost_toCostGame, affinePotential_def]
  refine Finset.sum_le_sum fun e _ => le_add_of_nonneg_right <| Finset.sum_nonneg fun i _ => ?_
  rw [hl]
  exact mul_nonneg (hw i) (add_nonneg (mul_nonneg (ha e) (hw i)) (hb e))

theorem HasAffineLatencies.affinePotential_le_two_mul_socialCost [Fintype E]
    (h : W.HasAffineLatencies) (hw : ∀ i, 0 ≤ W.weight i) (s : ∀ i, S i) :
    W.affinePotential s ≤ 2 * W.toCostGame.socialCost s := by
  rw [W.socialCost_toCostGame, affinePotential_def, Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  have hle : ∑ i with e ∈ W.resources i (s i), W.weight i * W.latency e (W.weight i) ≤
      W.load s e * W.latency e (W.load s e) := by
    rw [load, Finset.sum_mul]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
      (h.monotone_latency e (Finset.single_le_sum (fun j _ => hw j) hi)) (hw i)
  linarith

/-- **Price of stability at most `2` for weighted affine congestion games**: every finite nonempty
weighted affine congestion game with nonnegative weights has a pure Nash equilibrium of social cost
at most `2 * socialCost s'` for every profile `s'`, reachable from `s'` by better-response steps.
-/
theorem HasAffineLatencies.exists_isPureNash_socialCost_le_two_mul [DecidableEq ι] [Finite E]
    [∀ i, Finite (S i)] (h : W.HasAffineLatencies) (hw : ∀ i, 0 ≤ W.weight i) (s' : ∀ i, S i) :
    ∃ s, Relation.ReflTransGen (flip W.toCostGame.Improves) s' s ∧
      W.toCostGame.IsPureNash s ∧ W.toCostGame.socialCost s ≤ 2 * W.toCostGame.socialCost s' := by
  have := Fintype.ofFinite E
  obtain ⟨s, hpath, hs, hbound⟩ :=
    h.isOrdinalPotential_affinePotential.isGeneralizedOrdinalPotential
      |>.exists_reflTransGen_isPureNash_socialCost_le (A := 1) (B := 2) zero_le_one
      (fun t => by simpa only [one_mul] using h.socialCost_le_affinePotential hw t)
      (fun t => h.affinePotential_le_two_mul_socialCost hw t) s'
  exact ⟨s, hpath, hs, by simpa only [one_mul] using hbound⟩

end Basic

/-! ### Goemans–Mirrokni–Vetta pure-equilibrium nonexistence witness -/

section GMVCounterexample

/-- Resources of the four `s`–`t` paths in Goemans, Mirrokni, and Vetta's six-edge Wheatstone-plus-
direct network ([NisanRoughgardenTardosVazirani2007], Chapter 18, Example 18.7; locator not
re-verified against primary PDF):
`0` is `s → u → t`, `1` is `s → v → t`, `2` is `s → u → v → t`, and `3` is the direct edge
`s → t`. -/
@[expose] def gmvPaths : Fin 4 → Finset (Fin 6)
  | 0 => {0, 2}
  | 1 => {1, 3}
  | 2 => {0, 4, 3}
  | 3 => {5}

/-- Resource latencies of the Goemans–Mirrokni–Vetta network:
`13 x`, `x^2 + 44`, `x + 33`, `3 x^2`, `6 x^2`, and `47 x`. -/
@[expose] def gmvLatency : Fin 6 → ℝ → ℝ
  | 0, x => 13 * x
  | 1, x => x ^ 2 + 44
  | 2, x => x + 33
  | 3, x => 3 * x ^ 2
  | 4, x => 6 * x ^ 2
  | 5, x => 47 * x

/-- The **Goemans–Mirrokni–Vetta weighted congestion game** (FOCS 2005;
[NisanRoughgardenTardosVazirani2007], Chapter 18, Example 18.7; locator not re-verified against
primary PDF): two players of weights `1` and `2` routing across `gmvPaths` under nonnegative,
nondecreasing polynomial latencies of degree at most `2`. -/
@[expose] def gmvGame : WeightedCongestionGame (Fin 2) (fun _ => Fin 4) (Fin 6) where
  resources _ := gmvPaths
  weight i := if i = 0 then 1 else 2
  latency := gmvLatency

theorem gmvGame_weight_pos (i : Fin 2) : 0 < gmvGame.weight i := by
  fin_cases i <;> norm_num [gmvGame]

theorem gmvGame_monotoneOn_latency (e : Fin 6) : MonotoneOn (gmvGame.latency e) (Set.Ici 0) := by
  intro x hx y hy hxy
  fin_cases e <;> simp only [gmvGame, gmvLatency] at * <;>
    nlinarith [Set.mem_Ici.mp hx, Set.mem_Ici.mp hy]

/-- Explicit unilateral improvement witness from every one of the `16` profiles of `gmvGame`. -/
private def gmvImprover (s : Fin 2 → Fin 4) : Fin 2 × Fin 4 :=
  if s 1 = 0 ∨ s 1 = 2 then
    if s 0 = 3 then (1, 1) else (0, 3)
  else
    if s 0 = 2 then (1, 0) else (0, 2)

private lemma gmvLoad_eq (s : Fin 2 → Fin 4) (e : Fin 6) :
    gmvGame.load s e =
      (if e ∈ gmvPaths (s 0) then 1 else 0) + (if e ∈ gmvPaths (s 1) then 2 else 0) := by
  have h1 : (Finset.univ.erase (0 : Fin 2)) = {1} := rfl
  rw [gmvGame.load_eq_ite_add_erase s 0 e, h1]
  simp [gmvGame]

/-- **Weighted congestion games with quadratic latencies need not have pure Nash equilibria**
(Goemans, Mirrokni, and Vetta 2005; [NisanRoughgardenTardosVazirani2007], Chapter 18,
Example 18.7; locator not re-verified against primary PDF). -/
theorem not_exists_isPureNash_gmvGame : ¬ ∃ s, gmvGame.toCostGame.IsPureNash s := by
  rintro ⟨s, hs⟩
  obtain ⟨a, ha⟩ : ∃ a, s 0 = a := ⟨s 0, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, s 1 = b := ⟨s 1, rfl⟩
  have hs_eq : s = fun i : Fin 2 => if i = 0 then a else b := by
    funext i
    fin_cases i <;> simp [ha, hb]
  rw [hs_eq] at hs
  have hle := hs (gmvImprover fun i => if i = 0 then a else b).1
    (gmvImprover fun i => if i = 0 then a else b).2
  fin_cases a <;> fin_cases b <;>
    revert hle <;>
    simp only [gmvImprover, toCostGame_cost, unitCost, gmvLoad_eq] <;>
    norm_num [gmvGame, gmvPaths, gmvLatency, Function.update, Fin.isValue]

/-- `gmvGame` lacks the finite improvement property. -/
theorem not_hasFIP_gmvGame : ¬ gmvGame.toCostGame.HasFIP :=
  fun h => not_exists_isPureNash_gmvGame h.exists_isPureNash

/-- `gmvGame` admits no generalized ordinal potential (and hence no ordinal or exact potential;
[NisanRoughgardenTardosVazirani2007], Chapter 19, Exercise 19.11(c); locator not re-verified
against primary PDF). -/
theorem not_exists_isGeneralizedOrdinalPotential_gmvGame :
    ¬ ∃ Φ, gmvGame.toCostGame.IsGeneralizedOrdinalPotential Φ := by
  rw [← CostGame.hasFIP_iff_exists_isGeneralizedOrdinalPotential]
  exact not_hasFIP_gmvGame

end GMVCounterexample

end WeightedCongestionGame

end Cslib.GameTheory
