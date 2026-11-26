/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Congestion.Affine
public import CslibFrontier.GameTheory.Congestion.Weighted
public import CslibFrontier.GameTheory.Strategic.Nash
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The price of anarchy of weighted affine congestion games

For weighted atomic congestion games (`Cslib.GameTheory.WeightedCongestionGame`) with nonnegative
weights and nonnegative affine latencies `latency e x = a e * x + b e`, Awerbuch, Azar, and
Epstein [AwerbuchAzarEpstein2005] proved that the price of anarchy of pure and mixed Nash
equilibria is `(3 + √5) / 2 = φ² ≈ 2.618`, strictly larger than the unweighted bound `5 / 2` of
`CslibFrontier.GameTheory.Congestion.Affine` (see also Nisan–Roughgarden–Tardos–Vazirani
[NisanRoughgardenTardosVazirani2007], Chapter 18, Theorem 18.23, Lemmas 18.24–18.25, Example 18.6,
and Exercise 18.2; locators not re-verified against primary PDF).

We organize the theory around smoothness (`Cslib.GameTheory.CostGame.IsSmooth`):

1. **Equilibrium condition and inequality (Lemmas 18.24–18.25):**
   `sum_cost_update_le_socialCost_add` proves
   `∑ i, cost i (update s i (s' i)) ≤ socialCost s' + ∑ e, a e * load s e * load s' e`,
   yielding `socialCost_le_add_sum_mul_load_of_isPureNash` at any pure Nash equilibrium `s`.
2. **`((5 + √5) / 4, (√5 - 1) / 4)`-smoothness and `(3 + √5) / 2` Price of Anarchy
   (Theorem 18.23):** combining Lemma 18.25 with `x² + x y ≤ (5 + √5) / 4 * x² + (√5 - 1) / 4 * y²`
   (`sq_add_mul_le_golden_smooth`) establishes `isSmooth_of_hasAffineLatencies`, giving
   `(3 + √5) / 2` upper bounds simultaneously for pure Nash equilibria
   (`socialCost_le_of_isPureNash`), coarse correlated equilibria (`expected_socialCost_le`), and
   mixed Nash equilibria (`expected_socialCost_le_of_isMixedNash`).
3. **Network and player-count tightness witnesses (Example 18.6 & Exercise 18.2(a, b)):**
   - `aaeTriangleGame wHeavy wLight`: four-player routing on a three-vertex bidirected triangle
     with four latency-`x` edges and two latency-`0` edges. At `(1, 1)` it realizes Example 18.6
     (`10 = 5 / 2 * 4`); at `((1 + √5) / 2, 1)` it attains `(3 + √5) / 2` on the same network
     (Exercise 18.2(a)).
   - `exists_three_player_socialCost_eq_golden_mul`: a three-player weighted game with weights
     `(1, φ, φ)` attaining `(3 + √5) / 2` (Exercise 18.2(b)).
4. **Exact two-player affine Price of Anarchy (Exercise 18.2(c)):**
   - Unweighted two-player affine congestion games (`Fintype.card ι ≤ 2`) are `(2, 0)`-smooth
     (`CongestionGame.isSmooth_two_zero_of_card_le_two`), giving `PoA = 2` for pure, mixed, and
     coarse correlated equilibria, attained by
     `CongestionGame.exists_two_player_socialCost_eq_two_mul`.
   - Weighted two-player affine congestion games on `Fin 2` with `0 ≤ w₀ ≤ w₁` (`0 < w₁`) have
     exact pure Nash ratio
     `twoPlayerRatio w₀ w₁ = (w₀ + w₁) (w₀² + w₀ w₁ + w₁²) / (w₀³ + w₀² w₁ + w₁³)`
     (`socialCost_le_twoPlayerRatio_mul_of_isPureNash` and
     `exists_two_player_socialCost_eq_twoPlayerRatio_mul`), strictly exceeding `2` at `(4, 5)`
     while staying bounded by `21 / 10 < 5 / 2` across all weights.

## Main definitions

* `Cslib.GameTheory.WeightedCongestionGame.aaeTriangleGame`: the four-player bidirected-triangle
  network of Awerbuch–Azar–Epstein parameterized by heavy and light demand weights.
* `Cslib.GameTheory.WeightedCongestionGame.twoPlayerRatio`: exact worst-case pure-Nash ratio
  `(w₀ + w₁) (w₀² + w₀ w₁ + w₁²) / (w₀³ + w₀² w₁ + w₁³)` for two weighted players `0 ≤ w₀ ≤ w₁`.
* `Cslib.GameTheory.WeightedCongestionGame.twoPlayerTightGame`: three-resource two-player affine
  congestion game attaining `twoPlayerRatio w₀ w₁`.

## Main results

* `WeightedCongestionGame.sq_add_mul_le_golden_smooth`:
  `x² + x y ≤ (5 + √5) / 4 * x² + (√5 - 1) / 4 * y²` for all `x, y : ℝ`.
* `WeightedCongestionGame.unitCost_le_of_isPureNash`: equilibrium condition (Lemma 18.24).
* `WeightedCongestionGame.socialCost_le_add_sum_mul_load_of_isPureNash`: equilibrium inequality
  `socialCost s ≤ socialCost s' + ∑ e, a e * load s e * load s' e` (Lemma 18.25).
* `WeightedCongestionGame.isSmooth_of_hasAffineLatencies`: weighted affine congestion games with
  nonnegative weights are `((5 + √5) / 4, (√5 - 1) / 4)`-smooth.
* `WeightedCongestionGame.socialCost_le_of_isPureNash`,
  `WeightedCongestionGame.expected_socialCost_le`,
  `WeightedCongestionGame.expected_socialCost_le_of_isMixedNash`: pure, coarse correlated, and
  mixed price of anarchy at most `(3 + √5) / 2` (Theorem 18.23).
* `WeightedCongestionGame.aaeTriangleGame_unweighted_five_halves`: unweighted `10 = 5 / 2 * 4`
  pure Nash equilibria on the bidirected triangle (Example 18.6).
* `WeightedCongestionGame.aaeTriangleGame_weighted_golden`: weighted `(3 + √5) / 2` tightness on
  the bidirected triangle (Exercise 18.2(a)).
* `WeightedCongestionGame.exists_three_player_socialCost_eq_golden_mul`: three-player weighted
  tightness of `(3 + √5) / 2` (Exercise 18.2(b)).
* `CongestionGame.isSmooth_two_zero_of_card_le_two`,
  `CongestionGame.socialCost_le_two_mul_of_card_le_two`,
  `CongestionGame.expected_socialCost_le_two_mul_of_card_le_two`,
  `CongestionGame.exists_two_player_socialCost_eq_two_mul`: exact unweighted two-player `PoA = 2`
  (Exercise 18.2(c)).
* `WeightedCongestionGame.socialCost_le_twoPlayerRatio_mul_of_isPureNash`,
  `WeightedCongestionGame.exists_two_player_socialCost_eq_twoPlayerRatio_mul`,
  `WeightedCongestionGame.twoPlayerRatio_le_twenty_one_tenths`: exact two-player weighted pure
  `PoA` and `< 5 / 2` global bound.

## References

* [AwerbuchAzarEpstein2005]
* [ChristodoulouKoutsoupias2005]
* [NisanRoughgardenTardosVazirani2007]
* [Roughgarden2015]
-/

public section

namespace Cslib.GameTheory

namespace WeightedCongestionGame

/-! ### Golden-ratio smoothness algebra -/

private lemma sqrt_five_bounds : 2 < Real.sqrt 5 ∧ Real.sqrt 5 < 3 := by
  refine ⟨Real.lt_sqrt_of_sq_lt (by norm_num), ?_⟩
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

/-- Real smoothness inequality underlying Awerbuch–Azar–Epstein's `(3 + √5) / 2` bound:
`x² + x y ≤ (5 + √5) / 4 * x² + (√5 - 1) / 4 * y²` for all real numbers `x` and `y`, with equality
when `y = (1 + √5) / 2 * x`. -/
theorem sq_add_mul_le_golden_smooth (x y : ℝ) :
    x ^ 2 + x * y ≤ (5 + Real.sqrt 5) / 4 * x ^ 2 + (Real.sqrt 5 - 1) / 4 * y ^ 2 := by
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hid : (Real.sqrt 5 - 1) / 4 * ((Real.sqrt 5 + 1) / 2 * x - y) ^ 2 =
      (1 + Real.sqrt 5) / 4 * x ^ 2 - x * y + (Real.sqrt 5 - 1) / 4 * y ^ 2 := by
    calc (Real.sqrt 5 - 1) / 4 * ((Real.sqrt 5 + 1) / 2 * x - y) ^ 2
      _ = (Real.sqrt 5 ^ 2 - 1) * (Real.sqrt 5 + 1) / 16 * x ^ 2 -
            (Real.sqrt 5 ^ 2 - 1) / 4 * x * y + (Real.sqrt 5 - 1) / 4 * y ^ 2 := by ring
      _ = (1 + Real.sqrt 5) / 4 * x ^ 2 - x * y + (Real.sqrt 5 - 1) / 4 * y ^ 2 := by
            rw [hs5]; ring
  linarith [mul_nonneg (by linarith [sqrt_five_bounds.1] : 0 ≤ (Real.sqrt 5 - 1) / 4)
    (sq_nonneg ((Real.sqrt 5 + 1) / 2 * x - y))]

private lemma golden_smooth_ratio :
    ((5 + Real.sqrt 5) / 4) / (1 - (Real.sqrt 5 - 1) / 4) = (3 + Real.sqrt 5) / 2 := by
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [div_eq_iff (by linarith [sqrt_five_bounds.2])]
  calc (5 + Real.sqrt 5) / 4
    _ = (15 + 2 * Real.sqrt 5 - Real.sqrt 5 ^ 2) / 8 := by rw [hs5]; ring
    _ = (3 + Real.sqrt 5) / 2 * (1 - (Real.sqrt 5 - 1) / 4) := by ring

private lemma goldenRatio_identities {φ : ℝ} (hφ : φ = (1 + Real.sqrt 5) / 2) :
    0 < φ ∧ φ ^ 2 = φ + 1 ∧ (3 + Real.sqrt 5) / 2 = φ ^ 2 := by
  subst hφ
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hgt2 : 2 < Real.sqrt 5 := sqrt_five_bounds.1
  have hφ_sq : ((1 + Real.sqrt 5) / 2) ^ 2 = (1 + Real.sqrt 5) / 2 + 1 := by
    calc ((1 + Real.sqrt 5) / 2) ^ 2
      _ = (1 + 2 * Real.sqrt 5 + Real.sqrt 5 ^ 2) / 4 := by ring
      _ = (1 + Real.sqrt 5) / 2 + 1 := by rw [hs5]; ring
  exact ⟨by linarith, hφ_sq, by linarith⟩

/-! ### Equilibrium inequalities, smoothness, and `(3 + √5) / 2` Price of Anarchy -/

section SmoothAndPoA

variable {ι : Type*} {S : ι → Type*} {E : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq E]
  (W : WeightedCongestionGame ι S E)

/-- **Deviation bound for weighted affine latencies**: when player `i` with `0 ≤ weight i`
deviates from `s` to `a'`, its per-unit latency on `a'` is at most
`∑ e ∈ resources i a', (a e * (load s e + weight i) + b e)`. -/
theorem unitCost_update_le {a b : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (hl : ∀ e x, W.latency e x = a e * x + b e) {s : ∀ j, S j} {i : ι}
    (hi : 0 ≤ W.weight i) (a' : S i) :
    W.unitCost i (Function.update s i a') ≤
      ∑ e ∈ W.resources i a', (a e * (W.load s e + W.weight i) + b e) := by
  simp only [unitCost, Function.update_self]
  exact Finset.sum_le_sum fun e _ => by rw [hl]; nlinarith [ha e, W.load_update_le (s := s) hi a' e]

/-- **Equilibrium condition for weighted affine congestion games**
([NisanRoughgardenTardosVazirani2007], Chapter 18, Lemma 18.24; locator not re-verified against
primary PDF): at any pure Nash equilibrium `s` with `0 < weight i`,
`∑ e ∈ resources i (s i), (a e * load s e + b e) ≤
  ∑ e ∈ resources i a', (a e * (load s e + weight i) + b e)`. -/
theorem unitCost_le_of_isPureNash {a b : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (hl : ∀ e x, W.latency e x = a e * x + b e) {s : ∀ j, S j}
    (hs : W.toCostGame.IsPureNash s) {i : ι} (hi : 0 < W.weight i) (a' : S i) :
    ∑ e ∈ W.resources i (s i), (a e * W.load s e + b e) ≤
      ∑ e ∈ W.resources i a', (a e * (W.load s e + W.weight i) + b e) := by
  have hcost := (mul_le_mul_iff_right₀ hi).mp (hs i a')
  simpa only [unitCost, hl] using hcost.trans (W.unitCost_update_le ha hl hi.le a')

omit [DecidableEq ι] in
/-- Sum-of-squares domination on a resource: for nonnegative weights,
`∑_{i : e ∈ s'_i} (weight i)² ≤ (load s' e)²`. -/
private lemma sum_sq_weight_le_sq_load (hw : ∀ i, 0 ≤ W.weight i) (s' : ∀ i, S i) (e : E) :
    ∑ i with e ∈ W.resources i (s' i), W.weight i ^ 2 ≤ W.load s' e ^ 2 := by
  calc ∑ i with e ∈ W.resources i (s' i), W.weight i ^ 2
    _ ≤ ∑ i with e ∈ W.resources i (s' i), W.weight i * W.load s' e :=
          Finset.sum_le_sum fun i hi => by
            have hle : W.weight i ≤ W.load s' e := Finset.single_le_sum (fun j _ => hw j) hi
            nlinarith [hw i]
    _ = W.load s' e ^ 2 := by rw [← Finset.sum_mul, ← load, sq]

/-- **Deviation-sum inequality** underlying Lemma 18.25: for arbitrary profiles `s` and `s'`,
`∑ i, cost i (update s i (s' i)) ≤ socialCost s' + ∑ e, a e * load s e * load s' e`. -/
theorem sum_cost_update_le_socialCost_add [Fintype E] {a b : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (hl : ∀ e x, W.latency e x = a e * x + b e) (hw : ∀ i, 0 ≤ W.weight i)
    (s s' : ∀ i, S i) :
    ∑ i, W.toCostGame.cost i (Function.update s i (s' i)) ≤
      W.toCostGame.socialCost s' + ∑ e, a e * W.load s e * W.load s' e := by
  have hdev (i : ι) : W.toCostGame.cost i (Function.update s i (s' i)) ≤
      (W.weight i * ∑ e ∈ W.resources i (s' i), (a e * W.load s e + b e)) +
        ∑ e ∈ W.resources i (s' i), a e * W.weight i ^ 2 := by
    refine (mul_le_mul_of_nonneg_left (W.unitCost_update_le ha hl (hw i) (s' i)) (hw i)).trans_eq ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hexch_sq : (∑ i, ∑ e ∈ W.resources i (s' i), a e * W.weight i ^ 2) =
      ∑ e, a e * ∑ i with e ∈ W.resources i (s' i), W.weight i ^ 2 := by
    simp_rw [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_ite_mem, Finset.univ_inter]
  calc ∑ i, W.toCostGame.cost i (Function.update s i (s' i))
    _ ≤ (∑ i, W.weight i * ∑ e ∈ W.resources i (s' i), (a e * W.load s e + b e)) +
          ∑ i, ∑ e ∈ W.resources i (s' i), a e * W.weight i ^ 2 := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun i _ => hdev i
    _ = (∑ e, W.load s' e * (a e * W.load s e + b e)) +
          ∑ e, a e * ∑ i with e ∈ W.resources i (s' i), W.weight i ^ 2 := by
          rw [W.sum_weight_mul_sum_resources s' (fun e => a e * W.load s e + b e), hexch_sq]
    _ ≤ (∑ e, W.load s' e * (a e * W.load s e + b e)) + ∑ e, a e * W.load s' e ^ 2 :=
          add_le_add_right (Finset.sum_le_sum fun e _ =>
            mul_le_mul_of_nonneg_left (W.sum_sq_weight_le_sq_load hw s' e) (ha e)) _
    _ = W.toCostGame.socialCost s' + ∑ e, a e * W.load s e * W.load s' e := by
          rw [W.socialCost_toCostGame s', ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun e _ => by rw [hl]; ring

/-- **Equilibrium inequality for weighted affine congestion games**
([NisanRoughgardenTardosVazirani2007], Chapter 18, Lemma 18.25; locator not re-verified against
primary PDF): at any pure Nash equilibrium `s`,
`socialCost s ≤ socialCost s' + ∑ e, a e * load s e * load s' e`. -/
theorem socialCost_le_add_sum_mul_load_of_isPureNash [Fintype E] {a b : E → ℝ}
    (ha : ∀ e, 0 ≤ a e) (hl : ∀ e x, W.latency e x = a e * x + b e) (hw : ∀ i, 0 ≤ W.weight i)
    {s : ∀ i, S i} (hs : W.toCostGame.IsPureNash s) (s' : ∀ i, S i) :
    W.toCostGame.socialCost s ≤
      W.toCostGame.socialCost s' + ∑ e, a e * W.load s e * W.load s' e :=
  (Finset.sum_le_sum fun i _ => hs i (s' i)).trans
    (W.sum_cost_update_le_socialCost_add ha hl hw s s')

variable [Finite E]

/-- Weighted atomic congestion games with nonnegative weights and nonnegative affine latencies are
**`((5 + √5) / 4, (√5 - 1) / 4)`-smooth**. -/
theorem isSmooth_of_hasAffineLatencies (h : W.HasAffineLatencies) (hw : ∀ i, 0 ≤ W.weight i) :
    W.toCostGame.IsSmooth ((5 + Real.sqrt 5) / 4) ((Real.sqrt 5 - 1) / 4) := by
  have := Fintype.ofFinite E
  obtain ⟨a, b, ha, hb, hl⟩ := h
  have hgt2 : 2 < Real.sqrt 5 := sqrt_five_bounds.1
  intro s s'
  calc ∑ i, W.toCostGame.cost i (Function.update s i (s' i))
    _ ≤ W.toCostGame.socialCost s' + ∑ e, a e * W.load s e * W.load s' e :=
          W.sum_cost_update_le_socialCost_add ha hl hw s s'
    _ = ∑ e, (a e * (W.load s' e ^ 2 + W.load s' e * W.load s e) + b e * W.load s' e) := by
          rw [W.socialCost_toCostGame s', ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun e _ => by rw [hl]; ring
    _ ≤ ∑ e, ((5 + Real.sqrt 5) / 4 * (W.load s' e * W.latency e (W.load s' e)) +
            (Real.sqrt 5 - 1) / 4 * (W.load s e * W.latency e (W.load s e))) :=
          Finset.sum_le_sum fun e _ => by
            rw [hl, hl]
            nlinarith [mul_le_mul_of_nonneg_left
              (sq_add_mul_le_golden_smooth (W.load s' e) (W.load s e)) (ha e),
              mul_nonneg (hb e) (W.load_nonneg hw s' e), mul_nonneg (hb e) (W.load_nonneg hw s e)]
    _ = (5 + Real.sqrt 5) / 4 * W.toCostGame.socialCost s' +
          (Real.sqrt 5 - 1) / 4 * W.toCostGame.socialCost s := by
          rw [W.socialCost_toCostGame s', W.socialCost_toCostGame s, Finset.sum_add_distrib,
            Finset.mul_sum, Finset.mul_sum]

/-- **Awerbuch–Azar–Epstein theorem: pure Price of Anarchy at most `(3 + √5) / 2`**
([AwerbuchAzarEpstein2005]; [NisanRoughgardenTardosVazirani2007], Chapter 18, Theorem 18.23;
locator not re-verified against primary PDF). -/
theorem socialCost_le_of_isPureNash (h : W.HasAffineLatencies) (hw : ∀ i, 0 ≤ W.weight i)
    {s : ∀ i, S i} (hs : W.toCostGame.IsPureNash s) (s' : ∀ i, S i) :
    W.toCostGame.socialCost s ≤ (3 + Real.sqrt 5) / 2 * W.toCostGame.socialCost s' := by
  simpa only [golden_smooth_ratio] using
    (W.isSmooth_of_hasAffineLatencies h hw).socialCost_le_of_isPureNash
      (by linarith [sqrt_five_bounds.2]) hs s'

/-- **Robust Price of Anarchy at most `(3 + √5) / 2` for coarse correlated equilibria**
([AwerbuchAzarEpstein2005]; [Roughgarden2015], Theorem 3.2). -/
theorem expected_socialCost_le (h : W.HasAffineLatencies) (hw : ∀ i, 0 ≤ W.weight i)
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} (hσ : W.toCostGame.IsCoarseCorrelatedEquilibrium σ)
    (s' : ∀ i, S i) :
    σ.weights.sum (fun s w => w * W.toCostGame.socialCost s) ≤
      (3 + Real.sqrt 5) / 2 * W.toCostGame.socialCost s' := by
  simpa only [golden_smooth_ratio] using
    (W.isSmooth_of_hasAffineLatencies h hw).expected_socialCost_le
      (by linarith [sqrt_five_bounds.2]) hσ s'

/-- **Mixed Nash Price of Anarchy at most `(3 + √5) / 2`** ([AwerbuchAzarEpstein2005]). -/
theorem expected_socialCost_le_of_isMixedNash [∀ i, Fintype (S i)] (h : W.HasAffineLatencies)
    (hw : ∀ i, 0 ≤ W.weight i) {p : ∀ i, S i → ℝ} (hp : W.toCostGame.IsMixedNash p)
    (s' : ∀ i, S i) :
    ∑ s, productWeight p s * W.toCostGame.socialCost s ≤
      (3 + Real.sqrt 5) / 2 * W.toCostGame.socialCost s' := by
  rw [← productDist_sum (fun i => (hp.1 i).nonneg) (fun i => (hp.1 i).sum_eq_one)]
  exact W.expected_socialCost_le h hw hp.isCoarseCorrelatedEquilibrium s'

end SmoothAndPoA

/-! ### Tightness witnesses: AAE bidirected triangle and 3-player weighted game -/

section TightnessWitnesses

/-- Simple paths of the four players on Awerbuch–Azar–Epstein's three-vertex bidirected triangle
`{u, v, w}` ([NisanRoughgardenTardosVazirani2007], Chapter 18, Example 18.6 and Exercise 18.2(a);
locators not re-verified against primary PDF). The six directed arcs are
`0 : u → w`, `1 : v → w`, `2 : u → v`, `3 : v → u` (each of latency `x`) and
`4 : w → v`, `5 : w → u` (each of latency `0`). Strategy `true` is the direct `1`-hop edge and
strategy `false` is the unique `2`-hop simple path. -/
@[expose] def aaeTrianglePaths : Fin 4 → Bool → Finset (Fin 6)
  | 0, true => {0}
  | 0, false => {2, 1}
  | 1, true => {1}
  | 1, false => {3, 0}
  | 2, true => {2}
  | 2, false => {0, 4}
  | 3, true => {3}
  | 3, false => {1, 5}

/-- The **Awerbuch–Azar–Epstein four-player bidirected-triangle network**, with heavy demand
`wHeavy` for players `0, 1` (`u → w`, `v → w`) and light demand `wLight` for players `2, 3`
(`u → v`, `v → u`). -/
@[expose] def aaeTriangleGame (wHeavy wLight : ℝ) :
    WeightedCongestionGame (Fin 4) (fun _ => Bool) (Fin 6) where
  resources := aaeTrianglePaths
  weight i := if i.val < 2 then wHeavy else wLight
  latency e x := if e.val < 4 then x else 0

theorem hasAffineLatencies_aaeTriangleGame (wHeavy wLight : ℝ) :
    (aaeTriangleGame wHeavy wLight).HasAffineLatencies :=
  ⟨fun e => if e.val < 4 then 1 else 0, fun _ => 0,
    fun e => by by_cases h : e.val < 4 <;> simp [h], fun _ => le_rfl,
    fun e x => by by_cases h : e.val < 4 <;> simp [aaeTriangleGame, h]⟩

private lemma aaeTriangleLoad_eq (wH wL : ℝ) (s : Fin 4 → Bool) (e : Fin 6) :
    (aaeTriangleGame wH wL).load s e =
      (if e ∈ aaeTrianglePaths 0 (s 0) then wH else 0) +
      (if e ∈ aaeTrianglePaths 1 (s 1) then wH else 0) +
      (if e ∈ aaeTrianglePaths 2 (s 2) then wL else 0) +
      (if e ∈ aaeTrianglePaths 3 (s 3) then wL else 0) := by
  rw [load, Finset.sum_filter, show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  norm_num [aaeTriangleGame, Fin.isValue]
  ring

/-- **Unweighted bidirected-triangle `5 / 2` witness** ([NisanRoughgardenTardosVazirani2007],
Chapter 18, Example 18.6; locator not re-verified against primary PDF): at unit weights `(1, 1)`,
both the `1`-hop profile (social cost `4`) and the `2`-hop profile (social cost `10`) are pure Nash
equilibria, achieving `10 = 5 / 2 * 4`. -/
theorem aaeTriangleGame_unweighted_five_halves :
    (aaeTriangleGame 1 1).toCostGame.IsPureNash (fun _ => true) ∧
      (aaeTriangleGame 1 1).toCostGame.IsPureNash (fun _ => false) ∧
      (aaeTriangleGame 1 1).toCostGame.socialCost (fun _ => true) = 4 ∧
      (aaeTriangleGame 1 1).toCostGame.socialCost (fun _ => false) = 10 := by
  have hnash (b : Bool) : (aaeTriangleGame 1 1).toCostGame.IsPureNash (fun _ => b) := fun i a => by
    cases b <;> fin_cases i <;> cases a <;>
      simp only [toCostGame_cost, unitCost, aaeTriangleLoad_eq] <;>
      norm_num [aaeTriangleGame, aaeTrianglePaths, Function.update, Fin.isValue]
  refine ⟨hnash true, hnash false, ?_, ?_⟩ <;>
    simp only [CostGame.socialCost, Fin.sum_univ_four, toCostGame_cost, unitCost,
      aaeTriangleLoad_eq] <;>
    norm_num [aaeTriangleGame, aaeTrianglePaths, Fin.isValue]

/-- **Weighted bidirected-triangle `(3 + √5) / 2` tightness** ([AwerbuchAzarEpstein2005];
[NisanRoughgardenTardosVazirani2007], Chapter 18, Exercise 18.2(a); locator not re-verified against
primary PDF): with heavy weight `φ = (1 + √5) / 2` and light weight `1`, the `2`-hop profile is a
pure Nash equilibrium whose social cost equals `(3 + √5) / 2` times the `1`-hop social cost. -/
theorem aaeTriangleGame_weighted_golden :
    let φ := (1 + Real.sqrt 5) / 2
    (aaeTriangleGame φ 1).toCostGame.IsPureNash (fun _ => false) ∧
      0 < (aaeTriangleGame φ 1).toCostGame.socialCost (fun _ => true) ∧
      (aaeTriangleGame φ 1).toCostGame.socialCost (fun _ => false) =
        (3 + Real.sqrt 5) / 2 * (aaeTriangleGame φ 1).toCostGame.socialCost (fun _ => true) := by
  intro φ
  obtain ⟨hφ_pos, hφ_sq, hgolden⟩ := goldenRatio_identities (φ := φ) rfl
  have htrue : (aaeTriangleGame φ 1).toCostGame.socialCost (fun _ => true) = 2 * φ ^ 2 + 2 := by
    simp only [CostGame.socialCost, Fin.sum_univ_four, toCostGame_cost, unitCost,
      aaeTriangleLoad_eq]
    norm_num [aaeTriangleGame, aaeTrianglePaths, Fin.isValue]
    ring
  refine ⟨fun i a => ?_, htrue ▸ by positivity, ?_⟩
  · fin_cases i <;> cases a <;> simp only [toCostGame_cost, unitCost, aaeTriangleLoad_eq] <;>
      norm_num [aaeTriangleGame, aaeTrianglePaths, Function.update, Fin.isValue] <;>
      nlinarith [hφ_sq, hφ_pos]
  · calc (aaeTriangleGame φ 1).toCostGame.socialCost (fun _ => false)
      _ = 2 * φ * (φ + (φ + 1)) + 2 * (φ + 1) := by
            simp only [CostGame.socialCost, Fin.sum_univ_four, toCostGame_cost, unitCost,
              aaeTriangleLoad_eq]
            norm_num [aaeTriangleGame, aaeTrianglePaths, Fin.isValue]
            ring
      _ = (3 + Real.sqrt 5) / 2 * (aaeTriangleGame φ 1).toCostGame.socialCost (fun _ => true) := by
            rw [htrue, hgolden]
            nlinarith [hφ_sq]

/-- Resource sets of a **three-player** weighted game attaining `(3 + √5) / 2`
([NisanRoughgardenTardosVazirani2007], Chapter 18, Exercise 18.2(b); locator not re-verified
against primary PDF). -/
private def threePlayerGoldenPaths : Fin 3 → Bool → Finset (Fin 4)
  | 0, true => {0, 1}
  | 0, false => {2, 3}
  | 1, true => {2}
  | 1, false => {0, 3}
  | 2, true => {3}
  | 2, false => {1, 2}

/-- **Three-player weighted tightness of `(3 + √5) / 2`**
([NisanRoughgardenTardosVazirani2007], Chapter 18, Exercise 18.2(b); locator not re-verified
against primary PDF): there is a three-player weighted congestion game with strictly positive
weights `(1, φ, φ)` and identity latencies `latency e x = x` admitting a pure Nash equilibrium `s`
and a profile `s'` with `0 < socialCost s'` and
`socialCost s = (3 + √5) / 2 * socialCost s'`. -/
theorem exists_three_player_socialCost_eq_golden_mul :
    ∃ (W : WeightedCongestionGame (Fin 3) (fun _ => Bool) (Fin 4)) (s s' : Fin 3 → Bool),
      W.HasAffineLatencies ∧ (∀ i, 0 < W.weight i) ∧ W.toCostGame.IsPureNash s ∧
        0 < W.toCostGame.socialCost s' ∧
        W.toCostGame.socialCost s = (3 + Real.sqrt 5) / 2 * W.toCostGame.socialCost s' := by
  let φ := (1 + Real.sqrt 5) / 2
  obtain ⟨hφ_pos, hφ_sq, hgolden⟩ := goldenRatio_identities (φ := φ) rfl
  let W : WeightedCongestionGame (Fin 3) (fun _ => Bool) (Fin 4) :=
    { resources := threePlayerGoldenPaths
      weight := fun i => if i = 0 then 1 else φ
      latency := fun _ x => x }
  have hload (t : Fin 3 → Bool) (e : Fin 4) :
      W.load t e = (if e ∈ threePlayerGoldenPaths 0 (t 0) then 1 else 0) +
        (if e ∈ threePlayerGoldenPaths 1 (t 1) then φ else 0) +
        (if e ∈ threePlayerGoldenPaths 2 (t 2) then φ else 0) := by
    rw [load, Finset.sum_filter, Fin.sum_univ_three]
    norm_num [W, Fin.isValue]
  have htrue : W.toCostGame.socialCost (fun _ => true) = 2 + 2 * φ ^ 2 := by
    simp only [CostGame.socialCost, Fin.sum_univ_three, toCostGame_cost, unitCost, hload]
    norm_num [W, threePlayerGoldenPaths, Fin.isValue]
    ring
  refine ⟨W, fun _ => false, fun _ => true,
    ⟨fun _ => 1, fun _ => 0, fun _ => zero_le_one, fun _ => le_rfl, fun _ x => by simp [W]⟩,
    fun i => by fin_cases i <;> simp [W, hφ_pos], fun i a => ?_,
    htrue ▸ by positivity, ?_⟩
  · fin_cases i <;> cases a <;> simp only [toCostGame_cost, unitCost, hload] <;>
      norm_num [W, threePlayerGoldenPaths, Function.update, Fin.isValue] <;>
      nlinarith [hφ_sq, hφ_pos]
  · calc W.toCostGame.socialCost (fun _ => false)
      _ = 2 * (1 + φ) + 2 * φ * (φ + (1 + φ)) := by
            simp only [CostGame.socialCost, Fin.sum_univ_three, toCostGame_cost, unitCost, hload]
            norm_num [W, threePlayerGoldenPaths, Fin.isValue]
            ring
      _ = (3 + Real.sqrt 5) / 2 * W.toCostGame.socialCost (fun _ => true) := by
            rw [htrue, hgolden]
            nlinarith [hφ_sq]

end TightnessWitnesses

/-! ### Exact two-player weighted affine Price of Anarchy -/

section TwoPlayersWeighted

/-- Exact worst-case pure-Nash social-cost ratio for two players with demand weights
`0 ≤ w₀ ≤ w₁` (`0 < w₁`). -/
@[expose] noncomputable def twoPlayerRatio (w₀ w₁ : ℝ) : ℝ :=
  (w₀ + w₁) * (w₀ ^ 2 + w₀ * w₁ + w₁ ^ 2) / (w₀ ^ 3 + w₀ ^ 2 * w₁ + w₁ ^ 3)

@[simp]
theorem twoPlayerRatio_self {w : ℝ} (hw : w ≠ 0) : twoPlayerRatio w w = 2 := by
  unfold twoPlayerRatio
  rw [show w ^ 3 + w ^ 2 * w + w ^ 3 = 3 * w ^ 3 by ring]
  field_simp [pow_ne_zero 3 hw]; ring

/-- Across all nonnegative weight pairs `(w₀, w₁)` with `0 < w₁`, `twoPlayerRatio w₀ w₁` is at most
`21 / 10` (strictly below `5 / 2` and `(3 + √5) / 2`). -/
theorem twoPlayerRatio_le_twenty_one_tenths {w₀ w₁ : ℝ} (hw₀ : 0 ≤ w₀) (hw₁ : 0 < w₁) :
    twoPlayerRatio w₀ w₁ ≤ 21 / 10 := by
  unfold twoPlayerRatio
  rw [div_le_iff₀ (by positivity), ← sub_nonneg]
  have hid : 21 / 10 * (w₀ ^ 3 + w₀ ^ 2 * w₁ + w₁ ^ 3) -
      (w₀ + w₁) * (w₀ ^ 2 + w₀ * w₁ + w₁ ^ 2) =
      11 / 160 * w₁ * (4 * w₁ - 5 * w₀) ^ 2 +
        3 / 4 * w₀ * (w₁ - 259 / 240 * w₀) ^ 2 + 17399 / 76800 * w₀ ^ 3 := by ring
  rw [hid]
  positivity

private lemma twoPlayer_linear_edge_le {w₀ w₁ : ℝ} (hw₀ : 0 ≤ w₀) (hw₀₁ : w₀ ≤ w₁)
    (b'_0 b'_1 b_0 b_1 : Bool) :
    let D := w₀ ^ 3 + w₀ ^ 2 * w₁ + w₁ ^ 3
    let N := (w₀ + w₁) * (w₀ ^ 2 + w₀ * w₁ + w₁ ^ 2)
    let Y₁ := w₁ * (w₀ ^ 2 + w₀ * w₁ + w₁ ^ 2)
    let ld' := (if b'_0 then w₀ else 0) + (if b'_1 then w₁ else 0)
    let ld := (if b_0 then w₀ else 0) + (if b_1 then w₁ else 0)
    let ld0 := (if b'_0 then w₀ else 0) + (if b_1 then w₁ else 0)
    let ld1 := (if b_0 then w₀ else 0) + (if b'_1 then w₁ else 0)
    D * ld ^ 2 + D * (w₀ * ((if b'_0 then ld0 else 0) - (if b_0 then ld else 0))) +
      Y₁ * (w₁ * ((if b'_1 then ld1 else 0) - (if b_1 then ld else 0))) ≤ N * ld' ^ 2 := by
  intro D N Y₁ ld' ld ld0 ld1
  set d := w₁ - w₀
  have hd : 0 ≤ d := sub_nonneg.mpr hw₀₁
  rw [← sub_nonneg]
  dsimp only [D, N, Y₁, ld', ld, ld0, ld1]
  rw [show w₁ = w₀ + d by dsimp [d]; ring]
  cases b'_0 <;> cases b'_1 <;> cases b_0 <;> cases b_1 <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> ring_nf <;> positivity

private lemma twoPlayer_const_edge_le {w₀ w₁ : ℝ} (hw₀ : 0 ≤ w₀) (hw₀₁ : w₀ ≤ w₁)
    (b'_0 b'_1 b_0 b_1 : Bool) :
    let D := w₀ ^ 3 + w₀ ^ 2 * w₁ + w₁ ^ 3
    let N := (w₀ + w₁) * (w₀ ^ 2 + w₀ * w₁ + w₁ ^ 2)
    let Y₁ := w₁ * (w₀ ^ 2 + w₀ * w₁ + w₁ ^ 2)
    let ld' := (if b'_0 then w₀ else 0) + (if b'_1 then w₁ else 0)
    let ld := (if b_0 then w₀ else 0) + (if b_1 then w₁ else 0)
    D * ld + D * (w₀ * ((if b'_0 then 1 else 0) - (if b_0 then 1 else 0))) +
      Y₁ * (w₁ * ((if b'_1 then 1 else 0) - (if b_1 then 1 else 0))) ≤ N * ld' := by
  intro D N Y₁ ld' ld
  set d := w₁ - w₀
  have hd : 0 ≤ d := sub_nonneg.mpr hw₀₁
  rw [← sub_nonneg]
  dsimp only [D, N, Y₁, ld', ld]
  rw [show w₁ = w₀ + d by dsimp [d]; ring]
  cases b'_0 <;> cases b'_1 <;> cases b_0 <;> cases b_1 <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> ring_nf <;> positivity

/-- **Exact two-player weighted affine Price of Anarchy upper bound**: for any two-player weighted
congestion game on `Fin 2` with `0 ≤ weight 0 ≤ weight 1` and `0 < weight 1`, every pure Nash
equilibrium `s` satisfies
`socialCost s ≤ twoPlayerRatio (weight 0) (weight 1) * socialCost s'`. -/
theorem socialCost_le_twoPlayerRatio_mul_of_isPureNash {S : Fin 2 → Type*} {E : Type*}
    [DecidableEq E] [Finite E] (W : WeightedCongestionGame (Fin 2) S E)
    (h : W.HasAffineLatencies) (hw₀ : 0 ≤ W.weight 0) (hw₀₁ : W.weight 0 ≤ W.weight 1)
    (hw₁ : 0 < W.weight 1) {s : ∀ i, S i} (hs : W.toCostGame.IsPureNash s) (s' : ∀ i, S i) :
    W.toCostGame.socialCost s ≤ twoPlayerRatio (W.weight 0) (W.weight 1) *
      W.toCostGame.socialCost s' := by
  have := Fintype.ofFinite E
  obtain ⟨a, b, ha, hb, hl⟩ := h
  let w₀ := W.weight 0
  let w₁ := W.weight 1
  let D := w₀ ^ 3 + w₀ ^ 2 * w₁ + w₁ ^ 3
  let N := (w₀ + w₁) * (w₀ ^ 2 + w₀ * w₁ + w₁ ^ 2)
  let Y₁ := w₁ * (w₀ ^ 2 + w₀ * w₁ + w₁ ^ 2)
  have hD_pos : 0 < D := by dsimp [D, w₀, w₁]; positivity
  have hY₁_nonneg : 0 ≤ Y₁ := by dsimp [Y₁, w₀, w₁]; positivity
  have hload2 (t : ∀ i, S i) (e : E) :
      W.load t e = (if decide (e ∈ W.resources 0 (t 0)) then w₀ else 0) +
        (if decide (e ∈ W.resources 1 (t 1)) then w₁ else 0) := by
    rw [W.load_eq_ite_add_erase t 0 e, show (Finset.univ.erase (0 : Fin 2)) = {1} by decide]
    simp [w₀, w₁]
  have hcost_diff (i : Fin 2) (t' : S i) :
      W.toCostGame.cost i (Function.update s i t') - W.toCostGame.cost i s =
        W.weight i * ∑ e : E,
          ((if decide (e ∈ W.resources i t') then
              W.latency e (W.load (Function.update s i t') e) else 0) -
            (if decide (e ∈ W.resources i (s i)) then W.latency e (W.load s e) else 0)) := by
    simp only [toCostGame_cost, unitCost, Function.update_self, Finset.sum_sub_distrib,
      decide_eq_true_eq, Finset.sum_ite_mem, Finset.univ_inter]
    ring
  have hpt (e : E) :
      D * (W.load s e * W.latency e (W.load s e)) +
          D * (w₀ * ((if decide (e ∈ W.resources 0 (s' 0)) then
              W.latency e (W.load (Function.update s 0 (s' 0)) e) else 0) -
            (if decide (e ∈ W.resources 0 (s 0)) then W.latency e (W.load s e) else 0))) +
          Y₁ * (w₁ * ((if decide (e ∈ W.resources 1 (s' 1)) then
              W.latency e (W.load (Function.update s 1 (s' 1)) e) else 0) -
            (if decide (e ∈ W.resources 1 (s 1)) then W.latency e (W.load s e) else 0))) ≤
        N * (W.load s' e * W.latency e (W.load s' e)) := by
    rw [hl, hl, hl, hl, hload2 (Function.update s 0 (s' 0)) e,
      hload2 (Function.update s 1 (s' 1)) e, hload2 s e, hload2 s' e]
    simp only [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
    generalize decide (e ∈ W.resources 0 (s' 0)) = b'_0,
      decide (e ∈ W.resources 1 (s' 1)) = b'_1,
      decide (e ∈ W.resources 0 (s 0)) = b_0,
      decide (e ∈ W.resources 1 (s 1)) = b_1
    have hlin :=
      mul_le_mul_of_nonneg_left (twoPlayer_linear_edge_le hw₀ hw₀₁ b'_0 b'_1 b_0 b_1) (ha e)
    have hcon :=
      mul_le_mul_of_nonneg_left (twoPlayer_const_edge_le hw₀ hw₀₁ b'_0 b'_1 b_0 b_1) (hb e)
    dsimp only [D, N, Y₁, w₀, w₁] at hlin hcon ⊢
    cases b'_0 <;> cases b'_1 <;> cases b_0 <;> cases b_1 <;>
      simp only [Bool.false_eq_true, ↓reduceIte] at hlin hcon ⊢ <;>
      (ring_nf at hlin hcon ⊢; linarith)
  have hsum := Finset.sum_le_sum fun e (_ : e ∈ Finset.univ) => hpt e
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [← W.socialCost_toCostGame s, ← W.socialCost_toCostGame s',
    ← hcost_diff 0 (s' 0), ← hcost_diff 1 (s' 1)] at hsum
  unfold twoPlayerRatio
  rw [div_mul_eq_mul_div, le_div_iff₀ hD_pos]
  linarith [mul_nonneg hD_pos.le (sub_nonneg.mpr (hs 0 (s' 0))),
    mul_nonneg hY₁_nonneg (sub_nonneg.mpr (hs 1 (s' 1)))]

/-- Resource sets of `twoPlayerTightGame`: player `0` chooses between `{0}` and `{1, 2}`, while
player `1` chooses between `{1}` and `{0}`. -/
private def twoPlayerTightPaths : Fin 2 → Bool → Finset (Fin 3)
  | 0, true => {0}
  | 0, false => {1, 2}
  | 1, true => {1}
  | 1, false => {0}

/-- Three-resource two-player affine congestion game with demand weights `(w₀, w₁)` and latencies
`(w₀ + w₁) x`, `w₁ x`, and `w₀² + w₀ w₁ + w₁²`, attaining `twoPlayerRatio w₀ w₁` for all
`0 < w₀` and `0 < w₁` ([NisanRoughgardenTardosVazirani2007], Chapter 18, Exercise 18.2(c); locator
not re-verified against primary PDF). -/
def twoPlayerTightGame (w₀ w₁ : ℝ) :
    WeightedCongestionGame (Fin 2) (fun _ => Bool) (Fin 3) where
  resources := twoPlayerTightPaths
  weight i := if i = 0 then w₀ else w₁
  latency e x := match e with
    | 0 => (w₀ + w₁) * x
    | 1 => w₁ * x
    | 2 => w₀ ^ 2 + w₀ * w₁ + w₁ ^ 2

theorem hasAffineLatencies_twoPlayerTightGame {w₀ w₁ : ℝ} (hw₀ : 0 ≤ w₀) (hw₁ : 0 ≤ w₁) :
    (twoPlayerTightGame w₀ w₁).HasAffineLatencies :=
  ⟨fun | 0 => w₀ + w₁ | 1 => w₁ | 2 => 0,
   fun | 0 => 0 | 1 => 0 | 2 => w₀ ^ 2 + w₀ * w₁ + w₁ ^ 2,
   fun e => by fin_cases e <;> dsimp <;> positivity,
   fun e => by fin_cases e <;> dsimp <;> positivity,
   fun e _ => by fin_cases e <;> simp [twoPlayerTightGame]⟩

private lemma twoPlayerTightLoad_eq (w₀ w₁ : ℝ) (s : Fin 2 → Bool) (e : Fin 3) :
    (twoPlayerTightGame w₀ w₁).load s e =
      (if e ∈ twoPlayerTightPaths 0 (s 0) then w₀ else 0) +
      (if e ∈ twoPlayerTightPaths 1 (s 1) then w₁ else 0) := by
  rw [(twoPlayerTightGame w₀ w₁).load_eq_ite_add_erase s 0 e,
    show (Finset.univ.erase (0 : Fin 2)) = {1} by decide]
  simp [twoPlayerTightGame]

/-- **Tightness of `twoPlayerRatio w₀ w₁`**: for all `0 < w₀` and `0 < w₁`,
`twoPlayerTightGame w₀ w₁` has a pure Nash equilibrium `(false, false)` whose social cost equals
`twoPlayerRatio w₀ w₁` times the `(true, true)` social cost. -/
theorem exists_two_player_socialCost_eq_twoPlayerRatio_mul {w₀ w₁ : ℝ}
    (hw₀ : 0 < w₀) (hw₁ : 0 < w₁) :
    (twoPlayerTightGame w₀ w₁).toCostGame.IsPureNash (fun _ => false) ∧
      0 < (twoPlayerTightGame w₀ w₁).toCostGame.socialCost (fun _ => true) ∧
      (twoPlayerTightGame w₀ w₁).toCostGame.socialCost (fun _ => false) =
        twoPlayerRatio w₀ w₁ *
          (twoPlayerTightGame w₀ w₁).toCostGame.socialCost (fun _ => true) := by
  have huniv2 : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  have htrue : (twoPlayerTightGame w₀ w₁).toCostGame.socialCost (fun _ => true) =
      w₀ ^ 3 + w₀ ^ 2 * w₁ + w₁ ^ 3 := by
    simp only [CostGame.socialCost, huniv2, toCostGame_cost, unitCost, twoPlayerTightLoad_eq]
    norm_num [twoPlayerTightGame, twoPlayerTightPaths, Fin.isValue]
    ring
  have hden_pos : 0 < w₀ ^ 3 + w₀ ^ 2 * w₁ + w₁ ^ 3 := by positivity
  refine ⟨fun i a => ?_, htrue ▸ hden_pos, ?_⟩
  · fin_cases i <;> cases a <;> simp only [toCostGame_cost, unitCost, twoPlayerTightLoad_eq] <;>
      norm_num [twoPlayerTightGame, twoPlayerTightPaths, Function.update, Fin.isValue] <;> nlinarith
  · rw [htrue, twoPlayerRatio, div_mul_cancel₀ _ hden_pos.ne']
    simp only [CostGame.socialCost, huniv2, toCostGame_cost, unitCost, twoPlayerTightLoad_eq]
    norm_num [twoPlayerTightGame, twoPlayerTightPaths, Fin.isValue]
    ring

end TwoPlayersWeighted

end WeightedCongestionGame

/-! ### Exact unweighted two-player affine Price of Anarchy (`PoA = 2`) -/

namespace CongestionGame

section TwoPlayersUnweighted

variable {ι : Type*} {S : ι → Type*} {E : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq E]
  [Finite E] (C : CongestionGame ι S E)

/-- Every unweighted affine congestion game with at most two players is **`(2, 0)`-smooth**
([NisanRoughgardenTardosVazirani2007], Chapter 18, Exercise 18.2(c); locator not re-verified
against primary PDF). -/
theorem isSmooth_two_zero_of_card_le_two (hcard : Fintype.card ι ≤ 2) (h : C.HasAffineLatencies) :
    C.toCostGame.IsSmooth 2 0 := by
  have := Fintype.ofFinite E
  have hmono := HasAffineLatencies.monotone_latency h
  obtain ⟨a, b, ha, hb, hl⟩ := h
  intro s s'
  calc ∑ i, C.toCostGame.cost i (Function.update s i (s' i))
    _ ≤ ∑ i, ∑ e ∈ C.resources i (s' i), C.latency e 2 :=
          Finset.sum_le_sum fun i _ => by
            rw [toCostGame_cost, Function.update_self]
            exact Finset.sum_le_sum fun e _ => hmono e ((Finset.card_le_univ _).trans hcard)
    _ = ∑ e, (C.load s' e : ℝ) * C.latency e 2 := C.sum_sum_resources_eq_sum_load_mul s' _
    _ ≤ ∑ e, 2 * ((C.load s' e : ℝ) * C.latency e (C.load s' e)) :=
          Finset.sum_le_sum fun e _ => by
            rw [hl, hl]
            have hk_sq : (C.load s' e : ℝ) ≤ (C.load s' e : ℝ) ^ 2 := by
              exact_mod_cast Nat.le_self_pow two_ne_zero (C.load s' e)
            push_cast
            nlinarith [mul_le_mul_of_nonneg_left hk_sq (ha e), hb e,
              (Nat.cast_nonneg (C.load s' e) : (0 : ℝ) ≤ C.load s' e)]
    _ = 2 * C.toCostGame.socialCost s' + 0 * C.toCostGame.socialCost s := by
          rw [C.socialCost_toCostGame s', Finset.mul_sum, zero_mul, add_zero]

/-- **Unweighted two-player affine Price of Anarchy is at most `2`**
([NisanRoughgardenTardosVazirani2007], Chapter 18, Exercise 18.2(c); locator not re-verified
against primary PDF). -/
theorem socialCost_le_two_mul_of_card_le_two (hcard : Fintype.card ι ≤ 2)
    (h : C.HasAffineLatencies) {s : ∀ i, S i} (hs : C.toCostGame.IsPureNash s) (s' : ∀ i, S i) :
    C.toCostGame.socialCost s ≤ 2 * C.toCostGame.socialCost s' := by
  simpa only [sub_zero, div_one] using
    (C.isSmooth_two_zero_of_card_le_two hcard h).socialCost_le_of_isPureNash zero_lt_one hs s'

/-- **Robust unweighted two-player affine Price of Anarchy is at most `2`** for coarse correlated
equilibria. -/
theorem expected_socialCost_le_two_mul_of_card_le_two (hcard : Fintype.card ι ≤ 2)
    (h : C.HasAffineLatencies) {σ : Convexity.StdSimplex ℝ (∀ i, S i)}
    (hσ : C.toCostGame.IsCoarseCorrelatedEquilibrium σ) (s' : ∀ i, S i) :
    σ.weights.sum (fun s w => w * C.toCostGame.socialCost s) ≤
      2 * C.toCostGame.socialCost s' := by
  simpa only [sub_zero, div_one] using
    (C.isSmooth_two_zero_of_card_le_two hcard h).expected_socialCost_le zero_lt_one hσ s'

/-- **Tightness of the unweighted two-player bound `2`**
([NisanRoughgardenTardosVazirani2007], Chapter 18, Exercise 18.2(c); locator not re-verified
against primary PDF): derived directly from `WeightedCongestionGame.twoPlayerTightGame 1 1` via
`toUniformCongestionGame`. -/
theorem exists_two_player_socialCost_eq_two_mul :
    ∃ (C : CongestionGame (Fin 2) (fun _ => Bool) (Fin 3)) (s s' : Fin 2 → Bool),
      C.HasAffineLatencies ∧ C.toCostGame.IsPureNash s ∧ 0 < C.toCostGame.socialCost s' ∧
        C.toCostGame.socialCost s = 2 * C.toCostGame.socialCost s' := by
  let W := WeightedCongestionGame.twoPlayerTightGame 1 1
  let C := W.toUniformCongestionGame 1
  have hto : C.toCostGame = W.toCostGame :=
    W.toCostGame_toUniformCongestionGame 1 fun i => by
      fin_cases i <;> simp [W, WeightedCongestionGame.twoPlayerTightGame]
  obtain ⟨hne, hpos, heq⟩ :=
    WeightedCongestionGame.exists_two_player_socialCost_eq_twoPlayerRatio_mul
      zero_lt_one zero_lt_one
  obtain ⟨a, b, ha, hb, hl⟩ :=
    WeightedCongestionGame.hasAffineLatencies_twoPlayerTightGame zero_le_one zero_le_one
  exact ⟨C, fun _ => false, fun _ => true,
    ⟨a, b, ha, hb, fun e k => by
      simp [C, W, WeightedCongestionGame.toUniformCongestionGame, hl]⟩,
    hto ▸ hne, hto ▸ hpos,
    by rw [hto, heq, WeightedCongestionGame.twoPlayerRatio_self one_ne_zero]⟩

end TwoPlayersUnweighted

end CongestionGame

end Cslib.GameTheory
