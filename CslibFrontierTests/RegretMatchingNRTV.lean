/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Strategic.RegretMatching
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Hart–Mas-Colell regret-matching and NRTV Ch. 4 equilibrium bridges: checked witnesses

Non-vacuous checked witnesses for `CslibFrontier.MachineLearning.OnlineLearning.RegretMatching` and
`CslibFrontier.GameTheory.Strategic.RegretMatching`:

1. **Concrete orthant projection and regret-matching iterate (`Fin 3`)**:
   - Verifies `metricProjection_nonposOrthant` on `![2, -3, 1]` (`= ![0, -3, 0]`, squared residual
     norm `5`) and evaluates round `0` and round `1` of `regretMatchingProb` on `![1, 0, 1]`.
2. **Rock–Paper–Scissors (`rps`)**:
   - Deterministic 6-round non-tie cycle `rpsCycle` whose `empiricalDist` has **zero external
     regret** (`IsCoarseCorrelatedEquilibrium` holds), exact average pairwise internal regret
     `1 / 6`, and exact average swap regret `1 / 2 = 3 * (1 / 6)` (tightness of NRTV Exercise 4.1,
     separating `0`-CCE from `0`-CE).
   - Anytime horizon-free convergence of `rps.extRegretMatchingDist` (`2 * √(3 / T)`-CCE) and
     `rps.intRegretMatchingDist` (`2 * √(2 / T)` pairwise `ε`-CE and `2 * √(6 / T)` swap `ε`-CE)
     for every `T > 0` (including `T = 1`, where `blumMansour_isApproxCorrelatedEquilibrium` does
     not apply because `3 * log 3 > 1`).
3. **Traffic-Light and Chicken (`traffic`, `chicken`, [HartMasColell2000] §2, p. 1129)**:
   - 2-round `trafficCycle` realizes `trafficLight` as `empiricalDist` with zero swap regret.
   - Aumann's `chicken` game (`(6,6)`, `(7,2)`, `(2,7)`, `(0,0)` in negated cost form): the 3-round
     correlated cycle `chickenCycle` (`(C, C)`, `(D, C)`, `(C, D)`) has **zero swap regret**, making
     `empiricalDist chickenCycle 3` an exact correlated equilibrium with social cost `-10`, whereas
     every mixed Nash equilibrium of `chicken` has expected social cost at least `-28 / 3 > -10`
     (witnessing that `empiricalDist chickenCycle 3` lies strictly outside the convex hull of Nash
     equilibrium distributions), plus anytime `intRegretMatchingDynamics` convergence on `chicken`.
4. **Elimination of `ε`-dominated actions (NRTV Theorem 4.13)**:
   - Checks `pd.IsEpsDominated i 1 false` in Prisoner's Dilemma and instantiates
     `average_epsDominated_le_div`.
-/

set_option linter.privateModule false
namespace CslibFrontierTests.RegretMatchingNRTV

open Finset Function Real Cslib
open Cslib.MachineLearning.OnlineLearning.Experts
open Cslib.GameTheory Cslib.GameTheory.CostGame

private def rps : CostGame (Fin 2) (fun _ => Fin 3) where
  cost i s := if s i = s (i + 1) + 1 then -1 else if s (i + 1) = s i + 1 then 1 else 0

private def trafficCost (i : Fin 2) (s : Fin 2 → Bool) : ℝ :=
  match s 0, s 1 with
  | false, false => 0
  | false, true => if i = 0 then 0 else -1
  | true, false => if i = 0 then -1 else 0
  | true, true => 5

private def traffic : CostGame (Fin 2) (fun _ => Bool) := ⟨trafficCost⟩

private def pdCost (i : Fin 2) (s : Fin 2 → Bool) : ℝ :=
  match s i, s (i + 1) with
  | false, false => -3
  | false, true => 0
  | true, false => -5
  | true, true => -1

private def pd : CostGame (Fin 2) (fun _ => Bool) := ⟨pdCost⟩

/-! ### 1. Concrete orthant projection and regret-matching iterate -/

example :
    let y : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![2, -3, 1]
    metricProjection (nonposOrthant (Fin 3)) y = WithLp.toLp 2 ![0, -3, 0] ∧
      ‖y - metricProjection (nonposOrthant (Fin 3)) y‖ ^ 2 = 5 := by
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [metricProjection_nonposOrthant]
    ext i
    fin_cases i <;> norm_num
  · rw [norm_sub_metricProjection_nonposOrthant_sq, Fin.sum_univ_three]
    norm_num

/-- Concrete 2-round trajectory of `regretMatchingProb`: after `ℓ 0 = ![1, 0, 1]`, round `0` plays
uniformly (`1 / 3`), incurs expected loss `2 / 3`, accumulates positive regret `2 / 3` only on
action `1`, and concentrates probability `1` on action `1` in round `1`. -/
example :
    let ℓ : ℕ → Fin 3 → ℝ := fun _ => ![1, 0, 1]
    regretMatchingProb ℓ 0 = ![1 / 3, 1 / 3, 1 / 3] ∧
      regretMatchingProb ℓ 1 = ![0, 1, 0] := by
  intro ℓ
  have h0 : regretMatchingProb ℓ 0 = ![1 / 3, 1 / 3, 1 / 3] := by
    funext i
    rw [regretMatchingProb_zero]
    fin_cases i <;> norm_num
  refine ⟨h0, ?_⟩
  rw [regretMatchingProb_eq]
  have hext : (fun a : Fin 3 => max 0 (externalRegretOf (regretMatchingProb ℓ) ℓ 1 a)) =
      ![0, 2 / 3, 0] := by
    funext a
    rw [externalRegretOf, sum_range_one, h0, Fin.sum_univ_three]
    fin_cases a <;> norm_num [ℓ]
  rw [hext]
  funext a
  unfold regretMatchingStep
  rw [Fin.sum_univ_three]
  fin_cases a <;> norm_num

/-! ### 2. Rock–Paper–Scissors: deterministic empirical cycle and anytime regret-matching -/

/-- Six-round pure-play cycle visiting every non-tie outcome of `rps` once. -/
private def rpsCycle (t : ℕ) : Fin 2 → Fin 3 :=
  match t % 6 with
  | 0 => ![0, 1]
  | 1 => ![1, 2]
  | 2 => ![2, 0]
  | 3 => ![1, 0]
  | 4 => ![2, 1]
  | _ => ![0, 2]

/-- On `rpsCycle`, `empiricalDist` at `T = 6` has zero external regret (an exact coarse correlated
equilibrium), exact pairwise internal-regret slack `1 / 6`, and exact swap-regret slack
`1 / 2 = 3 * (1 / 6)` (matching NRTV Exercise 4.1 with equality and failing `0`-CE). -/
example :
    rps.IsCoarseCorrelatedEquilibrium (empiricalDist rpsCycle 6 (by decide)) ∧
      rps.IsApproxInternalCorrelatedEquilibrium (fun _ => 1 / 6)
        (empiricalDist rpsCycle 6 (by decide)) ∧
      ¬ rps.IsApproxInternalCorrelatedEquilibrium (fun _ => 1 / 12)
        (empiricalDist rpsCycle 6 (by decide)) ∧
      rps.IsApproxCorrelatedEquilibrium (fun _ => 1 / 2)
        (empiricalDist rpsCycle 6 (by decide)) ∧
      ¬ rps.IsApproxCorrelatedEquilibrium (fun _ => 1 / 3)
        (empiricalDist rpsCycle 6 (by decide)) ∧
      ¬ rps.IsCorrelatedEquilibrium (empiricalDist rpsCycle 6 (by decide)) := by
  have hcce : rps.IsCoarseCorrelatedEquilibrium (empiricalDist rpsCycle 6 (by decide)) := by
    rw [empiricalDist_isCoarseCorrelatedEquilibrium_iff]
    intro i a
    fin_cases i <;> fin_cases a <;>
      norm_num [sum_range_succ, rpsCycle, rps, Function.update]
  have hint : rps.IsApproxInternalCorrelatedEquilibrium (fun _ => 1 / 6)
      (empiricalDist rpsCycle 6 (by decide)) := by
    rw [empiricalDist_isApproxInternalCorrelatedEquilibrium_iff]
    intro i a b
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      norm_num [sum_range_succ, rpsCycle, rps, Function.update]
  have hnot_int : ¬ rps.IsApproxInternalCorrelatedEquilibrium (fun _ => 1 / 12)
      (empiricalDist rpsCycle 6 (by decide)) := by
    rw [empiricalDist_isApproxInternalCorrelatedEquilibrium_iff]
    intro h
    have h0 := h 0 0 2
    norm_num [sum_range_succ, rpsCycle, rps, Function.update] at h0
  have hswap : rps.IsApproxCorrelatedEquilibrium (fun _ => 1 / 2)
      (empiricalDist rpsCycle 6 (by decide)) := by
    convert hint.isApproxCorrelatedEquilibrium using 1
    ext
    norm_num
  have hnot_swap : ¬ rps.IsApproxCorrelatedEquilibrium (fun _ => 1 / 3)
      (empiricalDist rpsCycle 6 (by decide)) := by
    rw [empiricalDist_isApproxCorrelatedEquilibrium_iff]
    intro h
    have h0 := h 0 (fun a => a + 2)
    norm_num [sum_range_succ, rpsCycle, rps, Function.update] at h0
  have hnot_ce : ¬ rps.IsCorrelatedEquilibrium (empiricalDist rpsCycle 6 (by decide)) := by
    rw [empiricalDist_isCorrelatedEquilibrium_iff]
    intro h
    have h0 := h 0 (fun a => a + 2)
    norm_num [sum_range_succ, rpsCycle, rps, Function.update] at h0
  exact ⟨hcce, hint, hnot_int, hswap, hnot_swap, hnot_ce⟩

/-- Anytime `O(1 / √T)` convergence of external and stationary internal regret-matching on `rps`
for **every** `T > 0` (including `T = 1`, without any `T ≥ 3 ln 3` precondition). -/
example {T : ℕ} (hT : 0 < T) :
    rps.IsApproxCoarseCorrelatedEquilibrium
      (fun _ => 2 * √(3 / (T : ℝ)))
      (timeAverage rps.extRegretMatchingDist T hT) ∧
    rps.IsApproxInternalCorrelatedEquilibrium
      (fun _ => 2 * √(2 / (T : ℝ)))
      (timeAverage rps.intRegretMatchingDist T hT) ∧
    rps.IsApproxCorrelatedEquilibrium
      (fun _ => 2 * √(6 / (T : ℝ)))
      (timeAverage rps.intRegretMatchingDist T hT) := by
  have hc : ∀ (i : Fin 2) (s : Fin 2 → Fin 3), |rps.cost i s| ≤ 1 := by
    intro i s
    dsimp [rps]
    split_ifs <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · simpa using rps.extRegretMatching_isApproxCoarseCorrelatedEquilibrium zero_le_one hc hT
  · simpa using rps.intRegretMatching_isApproxInternalCorrelatedEquilibrium zero_le_one hc hT
  · convert rps.intRegretMatching_isApproxCorrelatedEquilibrium zero_le_one hc hT using 1
    ext
    norm_num

/-! ### 3. Traffic-Light and Chicken: empirical correlated equilibria outside the Nash hull -/

private def trafficCycle (t : ℕ) : Fin 2 → Bool :=
  if t % 2 = 0 then ![true, false] else ![false, true]

/-- Two-round pure alternation `(go, stop), (stop, go)` induces an exact correlated equilibrium of
`traffic` via zero swap regret. -/
example : traffic.IsCorrelatedEquilibrium (empiricalDist trafficCycle 2 (by decide)) := by
  rw [empiricalDist_isCorrelatedEquilibrium_iff]
  intro i δ
  fin_cases i <;> cases hT : δ true <;> cases hF : δ false <;>
    norm_num [sum_range_succ, trafficCycle, traffic, trafficCost, Function.update, hT, hF]

/-- Aumann's **Chicken** game in cost form (negated payoffs; [HartMasColell2000] §2, p. 1129):
`false` is Cautious (`6` if both cautious, `2` against Dare) and `true` is Dare (`7` against
Cautious, `0` if both Dare). -/
private def chickenCost (i : Fin 2) (s : Fin 2 → Bool) : ℝ :=
  match s 0, s 1 with
  | false, false => -6
  | true, false => if i = 0 then -7 else -2
  | false, true => if i = 0 then -2 else -7
  | true, true => 0

private def chicken : CostGame (Fin 2) (fun _ => Bool) := ⟨chickenCost⟩

/-- Three-round correlated trajectory visiting `(C, C)`, `(D, C)`, and `(C, D)` equally often and
avoiding the crash `(D, D)`. -/
private def chickenCycle (t : ℕ) : Fin 2 → Bool :=
  match t % 3 with
  | 0 => ![false, false]
  | 1 => ![true, false]
  | _ => ![false, true]

/-- `empiricalDist chickenCycle 3` has zero swap regret (hence is an exact correlated equilibrium)
and achieves expected social cost `-10`. -/
example :
    chicken.IsCorrelatedEquilibrium (empiricalDist chickenCycle 3 (by decide)) ∧
      (empiricalDist chickenCycle 3 (by decide)).weights.sum
        (fun s w => w * chicken.socialCost s) = -10 := by
  refine ⟨?_, ?_⟩
  · rw [empiricalDist_isCorrelatedEquilibrium_iff]
    intro i δ
    fin_cases i <;> cases hT : δ true <;> cases hF : δ false <;>
      norm_num [sum_range_succ, chickenCycle, chicken, chickenCost, Function.update, hT, hF]
  · rw [empiricalDist_sum]
    norm_num [sum_range_succ, chickenCycle, chicken, chickenCost, CostGame.socialCost,
      Fin.sum_univ_two]

/-- Every mixed Nash equilibrium `p` of `chicken` has expected social cost at least `-28 / 3 > -10`,
proving that `empiricalDist chickenCycle 3` cannot lie in the convex hull of Nash equilibrium
outcome distributions ([HartMasColell2000] §2, p. 1129). -/
example {p : Fin 2 → Bool → ℝ} (hp : chicken.IsMixedNash p) :
    (-28 / 3 : ℝ) ≤
      (productDist (fun i => (hp.1 i).nonneg) (fun i => (hp.1 i).sum_eq_one)).weights.sum
        (fun s w => w * chicken.socialCost s) := by
  rw [productDist_sum]
  have hp0_sum : p 0 true + p 0 false = 1 := by simpa using (hp.1 0).sum_eq_one
  have hp1_sum : p 1 true + p 1 false = 1 := by simpa using (hp.1 1).sum_eq_one
  have hp0T_nn : 0 ≤ p 0 true := (hp.1 0).nonneg true
  have hp0F_nn : 0 ≤ p 0 false := (hp.1 0).nonneg false
  have hp1T_nn : 0 ≤ p 1 true := (hp.1 1).nonneg true
  have hp1F_nn : 0 ≤ p 1 false := (hp.1 1).nonneg false
  have hdev0F : chicken.deviationCost p 0 false = -6 * p 1 false - 2 * p 1 true := by
    rw [deviationCost_def, ← (piFinTwoEquiv fun _ => Bool).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, piFinTwoEquiv_symm_apply, productWeight_def, Fin.prod_univ_two]
    norm_num [chicken, chickenCost, Function.update]
    linear_combination (-6 * p 1 false - 2 * p 1 true) * hp0_sum
  have hdev0T : chicken.deviationCost p 0 true = -7 * p 1 false := by
    rw [deviationCost_def, ← (piFinTwoEquiv fun _ => Bool).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, piFinTwoEquiv_symm_apply, productWeight_def, Fin.prod_univ_two]
    norm_num [chicken, chickenCost, Function.update]
    linear_combination (-7 * p 1 false) * hp0_sum
  have hdev1F : chicken.deviationCost p 1 false = -6 * p 0 false - 2 * p 0 true := by
    rw [deviationCost_def, ← (piFinTwoEquiv fun _ => Bool).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, piFinTwoEquiv_symm_apply, productWeight_def, Fin.prod_univ_two]
    norm_num [chicken, chickenCost, Function.update]
    linear_combination (-6 * p 0 false - 2 * p 0 true) * hp1_sum
  have hdev1T : chicken.deviationCost p 1 true = -7 * p 0 false := by
    rw [deviationCost_def, ← (piFinTwoEquiv fun _ => Bool).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, piFinTwoEquiv_symm_apply, productWeight_def, Fin.prod_univ_two]
    norm_num [chicken, chickenCost, Function.update]
    linear_combination (-7 * p 0 false) * hp1_sum
  have hsoc : ∑ s, productWeight p s * chicken.socialCost s =
      chicken.expectedCost p 0 + chicken.expectedCost p 1 := by
    simp only [CostGame.socialCost, Fin.sum_univ_two, mul_add, sum_add_distrib, expectedCost_def]
  have hexp0 : chicken.expectedCost p 0 =
      p 0 true * (-7 * p 1 false) + p 0 false * (-6 * p 1 false - 2 * p 1 true) := by
    rw [← chicken.sum_mul_deviationCost_eq_expectedCost p (hp.1 0).sum_eq_one, Fintype.sum_bool,
      hdev0T, hdev0F]
  have hexp1 : chicken.expectedCost p 1 =
      p 1 true * (-7 * p 0 false) + p 1 false * (-6 * p 0 false - 2 * p 0 true) := by
    rw [← chicken.sum_mul_deviationCost_eq_expectedCost p (hp.1 1).sum_eq_one, Fintype.sum_bool,
      hdev1T, hdev1F]
  rw [hsoc]
  rcases hp0T_nn.eq_or_lt with h0T0 | h0T_pos
  · -- `p 0 true = 0`: player 0 plays `false`, forcing `p 1 true = 1` and social cost `-9`.
    have hp0F1 : p 0 false = 1 := by linarith
    have h1_br := hp.2 1 true
    rw [hexp1, hdev1T, ← h0T0, hp0F1] at h1_br
    have hp1F0 : p 1 false = 0 := by nlinarith
    have hp1T1 : p 1 true = 1 := by linarith
    rw [hexp0, hexp1, ← h0T0, hp0F1, hp1F0, hp1T1]
    norm_num
  · rcases hp0F_nn.eq_or_lt with h0F0 | h0F_pos
    · -- `p 0 false = 0`: player 0 plays `true`, forcing `p 1 false = 1` and social cost `-9`.
      have hp0T1 : p 0 true = 1 := by linarith
      have h1_br := hp.2 1 false
      rw [hexp1, hdev1F, ← h0F0, hp0T1] at h1_br
      have hp1T0 : p 1 true = 0 := by nlinarith
      have hp1F1 : p 1 false = 1 := by linarith
      rw [hexp0, hexp1, ← h0F0, hp0T1, hp1T0, hp1F1]
      norm_num
    · -- `0 < p 0 true` and `0 < p 0 false`: indifference forces `(1/3, 2/3)` for both players.
      have eq0T := hp.deviationCost_eq_of_pos 0 h0T_pos
      have eq0F := hp.deviationCost_eq_of_pos 0 h0F_pos
      have hind0 : chicken.deviationCost p 0 true = chicken.deviationCost p 0 false :=
        eq0T.trans eq0F.symm
      rw [hdev0T, hdev0F] at hind0
      have hp1T : p 1 true = 1 / 3 := by linarith
      have hp1F : p 1 false = 2 / 3 := by linarith
      have h1T_pos : 0 < p 1 true := by linarith
      have h1F_pos : 0 < p 1 false := by linarith
      have hind1 : chicken.deviationCost p 1 true = chicken.deviationCost p 1 false :=
        (hp.deviationCost_eq_of_pos 1 h1T_pos).trans (hp.deviationCost_eq_of_pos 1 h1F_pos).symm
      rw [hdev1T, hdev1F] at hind1
      have hp0T : p 0 true = 1 / 3 := by linarith
      have hp0F : p 0 false = 2 / 3 := by linarith
      rw [hexp0, hexp1, hp0T, hp0F, hp1T, hp1F]
      norm_num

/-- Anytime `O(1 / √T)` convergence of stationary regret-matching on `chicken` for all `T > 0`. -/
example {T : ℕ} (hT : 0 < T) :
    chicken.IsApproxCorrelatedEquilibrium
      (fun _ => 14 * √(2 / (T : ℝ)))
      (timeAverage chicken.intRegretMatchingDist T hT) := by
  have hc : ∀ (i : Fin 2) (s : Fin 2 → Bool), |chicken.cost i s| ≤ 7 := by
    intro i s
    fin_cases i <;> cases h0 : s 0 <;> cases h1 : s 1 <;>
      norm_num [chicken, chickenCost, h0, h1]
  have h := chicken.intRegretMatching_isApproxCorrelatedEquilibrium (M := 7) (by norm_num) hc hT
  convert h using 1
  ext
  simp only [Fintype.card_bool]
  norm_num

/-! ### 4. Elimination of `ε`-dominated strategies (NRTV Theorem 4.13) -/

/-- In Prisoner's Dilemma (`pd`), cooperating (`false`) is `1`-dominated by defecting (`true`), so
any play sequence with swap regret at most `R` places time-averaged weight at most `R / T` on
`false`. -/
example (i : Fin 2) {σ : ℕ → Convexity.StdSimplex ℝ (Fin 2 → Bool)} {T : ℕ} (hT : 0 < T) {R : ℝ}
    (hR : ∀ δ : Bool → Bool,
      ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * pd.cost i s) ≤
        ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * pd.cost i (update s i (δ (s i)))) + R) :
    pd.IsEpsDominated i 1 false ∧
      (∑ t ∈ range T,
          (σ t).weights.sum (fun s w => w * if s i ∈ ({false} : Finset Bool) then 1 else 0)) /
        T ≤ R / T := by
  have hdom : pd.IsEpsDominated i 1 false := by
    refine ⟨true, fun s => ?_⟩
    have hne : i + 1 ≠ i := by fin_cases i <;> decide
    dsimp only [pd, pdCost]
    rw [update_self, update_self, update_of_ne hne, update_of_ne hne]
    cases s (i + 1) <;> norm_num
  refine ⟨hdom, ?_⟩
  have h := pd.average_epsDominated_le_div hT zero_lt_one (D := {false})
    (fun a ha => by rw [mem_singleton.mp ha]; exact hdom) hR
  simpa only [one_mul] using h

end CslibFrontierTests.RegretMatchingNRTV
