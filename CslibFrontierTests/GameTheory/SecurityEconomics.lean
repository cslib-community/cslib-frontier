/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.GameTheory.Security.Interdependent
public import CslibFrontier.GameTheory.Security.SystemReliability
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Checked instances and boundary witnesses for security economics games

Concrete, non-vacuous checks for `CslibFrontier.GameTheory.Security.SystemReliability` and
`CslibFrontier.GameTheory.Security.Interdependent`:

1. **Smooth strictly concave reliability curve `P(z) = 1 - (z + 1)⁻¹`**:
   * Total-effort wrong-agent and strict underprovision witness (`val = ![9, 40]`,
     `unitCost = ![1, 5 / 2]`): unique pure Nash equilibrium `![0, 3]` vs. social optimum `![6, 0]`
     with disjoint contributor supports, plus Varian's Fact 8 liability rule restoring `![6, 0]`.
   * Weakest-link continuum `[0, 1]`, negligence due-care rule (`val = ![4, 32]`,
     `unitCost = ![1, 3]`, `zOpt = 2`), and the **`Fin 1` model-boundary witness** showing `![0]` is
     not a pure Nash equilibrium when `|ι| = 1` (`[Nontrivial ι]` in
     `isPureNash_weakestLinkGame_iff` is essential).
   * Best-shot coexistence of the champion equilibrium `![0, 3]` and Varian's §3.3 **slacker
     equilibrium** `![2, 0]` (`val = ![9, 16]`, `unitCost = ![1, 1]`, where higher-ratio player `1`
     free-rides because `16 / 3 < 7`).
   * Tight `n` Price-of-Anarchy bound and `exists_totalEffortGame_socialCost_gt_mul` check.
2. **Kunreuther–Heal (2003) Table 2 (`p = 1/10, q = 4/5, L = 1000, c = 95`)**:
   * Coexistence of pure Nash equilibria `![true, true]` (cost `95`) and `![false, false]` (cost
     `172`), absence of asymmetric pure Nash equilibria, mixed Nash (`θ = 3 / 8`, cost `145`) vs.
     public-signal correlated equilibrium (cost `1145 / 8`, strict gain `15 / 8`), and Pigouvian tax
     `t = 4` making `![true, true]` the unique coarse correlated equilibrium.
3. **Heal–Kunreuther (2007) §5.2 3-airline 2-round tipping cascade (`c = ![75, 85, 90]`)**:
   * Seed `{2}` is **not** a 1-step critical coalition (`¬ IsCriticalCoalition {2}`), yet tips all
     three airlines in two waves (`TipsAll {2}`) to a self-enforcing pure Nash equilibrium.
4. **Source-defect counterexamples to unaligned-cost Heal–Kunreuther (2007) Theorem 3**:
   * `Fin 3` (`qExt = ![4/10, 3/10, 1/10]`, `c = ![89, 95, 59]`): `{1}` is a 1-step critical
     coalition while top-externality `{0}` is **not**, even though both `all false` and `all true`
     are pure Nash equilibria.
   * `Fin 4` (`qExt = ![4/10, 35/100, 14/100, 14/100]`, `c = ![70, 95, 85, 85]`): `{1}` tips all 4
     agents in 2 rounds (`TipsAll {1}`), whereas top-externality `{0}` stalls immediately
     (`¬ TipsAll {0}`).
   * Positive instantiation of `isCriticalCoalition_of_higher_contagion` under aligned reluctance.
-/

public section

namespace CslibFrontierTests.GameTheory.SecurityEconomics

open Cslib.GameTheory Finset Function
open scoped NNReal

/-! ### 1. Smooth strictly concave reliability curve `P(z) = 1 - (z + 1)⁻¹` -/

/-- Smooth strictly concave reliability curve `P(z) = 1 - (z + 1)⁻¹` on `[0, ∞)`. -/
noncomputable def reliabilityCurve (z : ℝ) : ℝ := 1 - (z + 1)⁻¹

/-- Derivative `P'(z) = ((z + 1)^2)⁻¹` of `reliabilityCurve`. -/
noncomputable def reliabilityDeriv (z : ℝ) : ℝ := ((z + 1) ^ 2)⁻¹

theorem hasDerivAt_reliabilityCurve {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt reliabilityCurve (reliabilityDeriv t) t := by
  have h1 : HasDerivAt (fun z : ℝ => z + 1) 1 t := (hasDerivAt_id t).add_const 1
  have h2 := (hasDerivAt_const t (1 : ℝ)).sub (h1.inv (by linarith))
  exact h2.congr_deriv (by simp only [reliabilityDeriv]; ring)

theorem antitoneOn_reliabilityDeriv : AntitoneOn reliabilityDeriv (Set.Ici 0) := by
  intro x hx y _ hxy
  have hx0 : 0 ≤ x := hx
  have hpow : (x + 1) ^ 2 ≤ (y + 1) ^ 2 := by nlinarith
  exact inv_anti₀ (by positivity) hpow

theorem monotoneOn_reliabilityCurve : MonotoneOn reliabilityCurve (Set.Ici 0) := by
  intro x hx y _ hxy
  have hx0 : 0 ≤ x := hx
  simp only [reliabilityCurve]
  linarith [inv_anti₀ (by linarith : 0 < x + 1) (by linarith : x + 1 ≤ y + 1)]

theorem reliabilityCurve_le_one (z : ℝ≥0) : reliabilityCurve z ≤ 1 := by
  have hz : 0 ≤ (z : ℝ) := z.coe_nonneg
  have hpos : 0 ≤ ((z : ℝ) + 1)⁻¹ := inv_nonneg.mpr (by linarith)
  simp only [reliabilityCurve]
  linarith

theorem strictConcaveOn_reliabilityCurve : StrictConcaveOn ℝ (Set.Ici 0) reliabilityCurve := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hx1 : 0 < x + 1 := by linarith
  have hy1 : 0 < y + 1 := by linarith
  have hcomb1 : 0 < a * x + b * y + 1 := by positivity
  simp only [reliabilityCurve, smul_eq_mul]
  -- Equivalently `(a * x + b * y + 1)⁻¹ < a * (x + 1)⁻¹ + b * (y + 1)⁻¹`.
  have hdiff_ne : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hpos_sq : 0 < a * b * (x - y) ^ 2 := mul_pos (mul_pos ha hb) (sq_pos_of_ne_zero hdiff_ne)
  have hnum : (x + 1) * (y + 1) <
      (a * (y + 1) + b * (x + 1)) * (a * x + b * y + 1) := by
    have hb_eq : b = 1 - a := by linarith
    subst hb_eq
    linarith [show (a * (y + 1) + (1 - a) * (x + 1)) * (a * x + (1 - a) * y + 1) -
      (x + 1) * (y + 1) = a * (1 - a) * (x - y) ^ 2 by ring]
  have hdiv : (a * x + b * y + 1)⁻¹ < a * (x + 1)⁻¹ + b * (y + 1)⁻¹ := by
    have h1 : a * (x + 1)⁻¹ + b * (y + 1)⁻¹ =
        (a * (y + 1) + b * (x + 1)) / ((x + 1) * (y + 1)) := by
      field_simp [hx1.ne', hy1.ne']
    rw [← one_div, h1, div_lt_div_iff₀ hcomb1 (mul_pos hx1 hy1)]
    linarith
  linarith [show a * (1 - (x + 1)⁻¹) + b * (1 - (y + 1)⁻¹) =
    (a + b) - (a * (x + 1)⁻¹ + b * (y + 1)⁻¹) by ring]

/-! ### 2. Varian wrong-agent, strict underprovision, and liability witness -/

/-- Two-agent instance (`val = ![9, 40]`, `unitCost = ![1, 5/2]`) witnessing Varian's wrong-agent
and strict-underprovision phenomena. -/
noncomputable def wrongAgentSpec : SystemReliabilitySpec (Fin 2) where
  val := ![9, 40]
  unitCost := ![1, 5 / 2]
  prob := reliabilityCurve

theorem wrongAgentSpec_opt :
    ∀ i : Fin 2, IsStandaloneOpt wrongAgentSpec.prob (wrongAgentSpec.val i)
      (wrongAgentSpec.unitCost i) (![(2 : ℝ≥0), 3] i) := by
  intro i
  refine isStandaloneOpt_of_hasDerivAt (fun _ ht => hasDerivAt_reliabilityCurve ht)
    antitoneOn_reliabilityDeriv ?_ (Or.inr ?_)
  · fin_cases i <;> norm_num [wrongAgentSpec]
  · fin_cases i <;> norm_num [wrongAgentSpec, reliabilityDeriv]

theorem wrongAgentSpec_socialOpt :
    IsStandaloneOpt wrongAgentSpec.prob (∑ i, wrongAgentSpec.val i)
      (wrongAgentSpec.unitCost 0) 6 := by
  refine isStandaloneOpt_of_hasDerivAt (fun _ ht => hasDerivAt_reliabilityCurve ht)
    antitoneOn_reliabilityDeriv ?_ (Or.inr ?_)
  · norm_num [Fin.sum_univ_two, wrongAgentSpec]
  · norm_num [Fin.sum_univ_two, wrongAgentSpec, reliabilityDeriv]

/-- Unique pure Nash equilibrium `Pi.single 1 3`, social optimum `Pi.single 0 6`, strict
underprovision (`totalEffort < 6`), disjoint contributor supports (`x 0 = 0 ∧ y 1 = 0`), and
Pigouvian failure-fine internalization (`totalEffortLiabilityGame 0`). -/
theorem wrongAgentSpec_checked :
    wrongAgentSpec.totalEffortGame.IsPureNash (Pi.single 1 3) ∧
    (∀ x, wrongAgentSpec.totalEffortGame.IsPureNash x → x = Pi.single 1 3) ∧
    (∀ z, wrongAgentSpec.totalEffortGame.socialCost (Pi.single 0 6) ≤
      wrongAgentSpec.totalEffortGame.socialCost z) ∧
    (∀ x, wrongAgentSpec.totalEffortGame.IsPureNash x → totalEffort x < 6) ∧
    (∀ x y, wrongAgentSpec.totalEffortGame.IsPureNash x →
      (∀ z, wrongAgentSpec.totalEffortGame.socialCost y ≤
        wrongAgentSpec.totalEffortGame.socialCost z) →
      x 0 = 0 ∧ y 1 = 0) ∧
    (wrongAgentSpec.totalEffortLiabilityGame 0).IsPureNash (Pi.single 0 6) := by
  have hVal : ∀ i, 0 < wrongAgentSpec.val i := fun i => by
    fin_cases i <;> norm_num [wrongAgentSpec]
  have hCost : ∀ i, 0 < wrongAgentSpec.unitCost i := fun i => by
    fin_cases i <;> norm_num [wrongAgentSpec]
  have hMin : ∀ j, wrongAgentSpec.unitCost 0 ≤ wrongAgentSpec.unitCost j := fun j => by
    fin_cases j <;> norm_num [wrongAgentSpec]
  have hStrict : ∀ j : Fin 2, j ≠ 1 → (![(2 : ℝ≥0), 3] j) < (![(2 : ℝ≥0), 3] 1) := by
    intro j hj
    fin_cases j
    · norm_num
    · exact False.elim (hj rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using
      wrongAgentSpec.isPureNash_totalEffortGame_single strictConcaveOn_reliabilityCurve hVal
        wrongAgentSpec_opt (iStar := 1) (fun j => by fin_cases j <;> norm_num)
  · intro x hx
    simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using
      wrongAgentSpec.eq_single_of_isPureNash_totalEffortGame strictConcaveOn_reliabilityCurve hVal
        wrongAgentSpec_opt hStrict hx
  · exact wrongAgentSpec.socialCost_totalEffortGame_single_le hMin wrongAgentSpec_socialOpt
  · intro x hx
    exact wrongAgentSpec.totalEffort_lt_socialOpt_of_isPureNash strictConcaveOn_reliabilityCurve
      hVal hCost hMin wrongAgentSpec_opt wrongAgentSpec_socialOpt (by norm_num)
      (hasDerivAt_reliabilityCurve (by norm_num))
      (by norm_num [Fin.sum_univ_two, wrongAgentSpec, reliabilityDeriv]) hx
  · intro x y hx hy
    exact wrongAgentSpec.wrongAgent_support_disjoint strictConcaveOn_reliabilityCurve hVal hMin
      (by norm_num [wrongAgentSpec]) wrongAgentSpec_opt hStrict hx hy
  · exact wrongAgentSpec.isPureNash_totalEffortLiabilityGame_single
      strictConcaveOn_reliabilityCurve hVal hCost hMin wrongAgentSpec_opt wrongAgentSpec_socialOpt

/-! ### 3. Weakest-link continuum, negligence rule, `Fin 1` boundary, and best-shot slacker -/

/-- Two-agent weakest-link instance (`val = ![4, 32]`, `unitCost = ![1, 3]`) witnessing Varian's
Fact 9 negligence rule at due-care standard `zOpt = 2`. -/
noncomputable def negligenceSpec : SystemReliabilitySpec (Fin 2) where
  val := ![4, 32]
  unitCost := ![1, 3]
  prob := reliabilityCurve

theorem negligenceSpec_checked :
    ¬ negligenceSpec.weakestLinkGame.IsPureNash (fun _ => 2) ∧
    (negligenceSpec.weakestLinkNegligenceGame 2).IsPureNash (fun _ => 2) ∧
    ∀ x, negligenceSpec.weakestLinkGame.socialCost (fun _ => 2) ≤
      negligenceSpec.weakestLinkGame.socialCost x := by
  have hSoc : IsStandaloneOpt negligenceSpec.prob (∑ i, negligenceSpec.val i)
      (∑ i, negligenceSpec.unitCost i) 2 := by
    refine isStandaloneOpt_of_hasDerivAt (fun _ ht => hasDerivAt_reliabilityCurve ht)
      antitoneOn_reliabilityDeriv ?_ (Or.inr ?_)
    · norm_num [Fin.sum_univ_two, negligenceSpec]
    · norm_num [Fin.sum_univ_two, negligenceSpec, reliabilityDeriv]
  refine ⟨?_, ?_, ?_⟩
  · intro hN
    have hdev := hN 0 1
    have hw1 : weakestLink (fun _ : Fin 2 => (2 : ℝ≥0)) = 2 := by
      simp only [weakestLink, inf'_const]
    have hw2 : weakestLink (update (fun _ : Fin 2 => (2 : ℝ≥0)) 0 1) = 1 := by
      refine le_antisymm ?_ (le_inf' univ_nonempty _ fun k _ => ?_)
      · simpa only [weakestLink, update_self] using
          inf'_le (update (fun _ : Fin 2 => (2 : ℝ≥0)) 0 1) (mem_univ 0)
      · fin_cases k <;> norm_num [update]
    dsimp only [SystemReliabilitySpec.weakestLinkGame, SystemReliabilitySpec.toCostGame] at hdev
    rw [hw1, hw2, update_self] at hdev
    norm_num [negligenceSpec, reliabilityCurve] at hdev
  · exact negligenceSpec.isPureNash_weakestLinkNegligenceGame_const
      (fun i => by fin_cases i <;> norm_num [negligenceSpec])
      (fun i => by fin_cases i <;> norm_num [negligenceSpec])
      (reliabilityCurve_le_one 2) hSoc
  · exact negligenceSpec.socialCost_weakestLinkGame_const_le
      (fun i => by fin_cases i <;> norm_num [negligenceSpec]) hSoc

/-- **Model-boundary witness (`|ι| = 1`)**: when `ι = Fin 1`, `fun _ => 0` is **not** a pure Nash
equilibrium of `weakestLinkGame`, confirming that `[Nontrivial ι]` in
`isPureNash_weakestLinkGame_iff` cannot be dropped. -/
theorem fin1_weakestLink_zero_not_isPureNash :
    let R1 : SystemReliabilitySpec (Fin 1) :=
      { val := fun _ => 9, unitCost := fun _ => 1, prob := reliabilityCurve }
    ¬ R1.weakestLinkGame.IsPureNash (fun _ => 0) := by
  intro R1 hN
  have hdev := hN 0 2
  have hw0 : weakestLink (fun _ : Fin 1 => (0 : ℝ≥0)) = 0 := by
    simp only [weakestLink, inf'_const]
  have hw2 : weakestLink (update (fun _ : Fin 1 => (0 : ℝ≥0)) 0 2) = 2 := by
    refine le_antisymm ?_ (le_inf' univ_nonempty _ fun k _ => ?_)
    · simpa only [weakestLink, update_self] using
        inf'_le (update (fun _ : Fin 1 => (0 : ℝ≥0)) 0 2) (mem_univ 0)
    · rw [Subsingleton.elim k 0, update_self]
  dsimp only [SystemReliabilitySpec.weakestLinkGame, SystemReliabilitySpec.toCostGame] at hdev
  rw [hw0, hw2, update_self] at hdev
  norm_num [R1, reliabilityCurve] at hdev

/-- **Best-shot champion and slacker equilibria** ([Varian2004], §3.3): with `val = ![9, 16]` and
`unitCost = ![1, 1]` (`xBar = ![2, 3]`), both the champion profile `Pi.single 1 3` and the slacker
profile `Pi.single 0 2` (where higher-valuation player `1` free-rides because `16 / 3 < 7`) are
pure Nash equilibria, and both satisfy the `|ι| = 2` Price-of-Anarchy bound. -/
theorem bestShot_champion_and_slacker_checked :
    let R : SystemReliabilitySpec (Fin 2) :=
      { val := ![9, 16], unitCost := fun _ => 1, prob := reliabilityCurve }
    R.bestShotGame.IsPureNash (Pi.single 1 3) ∧
    R.bestShotGame.IsPureNash (Pi.single 0 2) ∧
    (∀ x', R.bestShotGame.socialCost (Pi.single 0 2) ≤ 2 * R.bestShotGame.socialCost x') := by
  intro R
  have hOpt : ∀ i : Fin 2, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (![(2 : ℝ≥0), 3] i) := by
    intro i
    refine isStandaloneOpt_of_hasDerivAt (fun _ ht => hasDerivAt_reliabilityCurve ht)
      antitoneOn_reliabilityDeriv ?_ (Or.inr ?_)
    · fin_cases i <;> norm_num [R]
    · fin_cases i <;> norm_num [R, reliabilityDeriv]
  have hChamp : R.bestShotGame.IsPureNash (Pi.single 1 3) := by
    simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using
      R.isPureNash_bestShotGame_champion monotoneOn_reliabilityCurve
        (fun i => by fin_cases i <;> norm_num [R]) (fun _ => by norm_num [R]) hOpt
        (iStar := 1) (fun i => by fin_cases i <;> norm_num)
  have hSlack : R.bestShotGame.IsPureNash (Pi.single 0 2) := by
    have hiff := R.isPureNash_bestShotGame_single_iff monotoneOn_reliabilityCurve
      (fun i => by fin_cases i <;> norm_num [R]) (fun _ => by norm_num [R]) hOpt (k := 0)
    simp only [Matrix.cons_val_zero] at hiff
    rw [hiff]
    intro i hi
    fin_cases i
    · exact False.elim (hi rfl)
    · norm_num [R, reliabilityCurve]
  refine ⟨hChamp, hSlack, fun x' => ?_⟩
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    R.socialCost_bestShotGame_le_card_mul (fun i => by fin_cases i <;> norm_num [R])
      monotoneOn_reliabilityCurve reliabilityCurve_le_one zero_lt_one (fun _ => rfl) hSlack x'

/-- Non-vacuous check of `exists_totalEffortGame_socialCost_gt_mul` at `n = 3, β = 5 / 2 < 3`. -/
example : ∃ (R : SystemReliabilitySpec (Fin 3)) (x x' : Fin 3 → ℝ≥0),
    R.totalEffortGame.IsPureNash x ∧
    (5 / 2 : ℝ) * R.totalEffortGame.socialCost x' < R.totalEffortGame.socialCost x := by
  obtain ⟨R, x, x', _, _, _, _, _, _, hN, _, hgt⟩ :=
    exists_totalEffortGame_socialCost_gt_mul (n := 3) (by decide) (β := 5 / 2) (by norm_num)
  exact ⟨R, x, x', hN, hgt⟩

/-- **Payoff-maximization vs. `CostGame`-minimization bridge** (`payoff`, `socialPayoff`,
`isStandaloneOpt_iff_payoff_le`, `socialCost_eq_sum_val_sub_socialPayoff`): on `wrongAgentSpec`,
player standalone maximization of `v_i P(z) - c_i z`, unilateral maximization of `payoff`, and
social maximization of `socialPayoff` coincide with `IsStandaloneOpt`, `IsPureNash`, and
`socialCost` minimization. -/
theorem wrongAgentSpec_payoff_bridge_checked :
    (∀ (i : Fin 2) (z : ℝ≥0),
      wrongAgentSpec.val i * wrongAgentSpec.prob z - wrongAgentSpec.unitCost i * (z : ℝ) ≤
        wrongAgentSpec.val i * wrongAgentSpec.prob (![(2 : ℝ≥0), 3] i) -
          wrongAgentSpec.unitCost i * ((![(2 : ℝ≥0), 3] i : ℝ≥0) : ℝ)) ∧
    (∀ (i : Fin 2) (a : ℝ≥0),
      wrongAgentSpec.payoff totalEffort i (update (Pi.single 1 3) i a) ≤
        wrongAgentSpec.payoff totalEffort i (Pi.single 1 3)) ∧
    (∀ z : Fin 2 → ℝ≥0,
      wrongAgentSpec.socialPayoff totalEffort z ≤
        wrongAgentSpec.socialPayoff totalEffort (Pi.single 0 6)) := by
  obtain ⟨hNash, _, hSoc, _, _, _⟩ := wrongAgentSpec_checked
  refine ⟨fun i z => isStandaloneOpt_iff_payoff_le.mp (wrongAgentSpec_opt i) z,
    fun i a => ?_, fun z => ?_⟩
  · have h := hNash i a
    simp only [SystemReliabilitySpec.totalEffortGame,
      SystemReliabilitySpec.cost_eq_val_sub_payoff] at h
    linarith
  · have h := hSoc z
    simp only [SystemReliabilitySpec.totalEffortGame,
      SystemReliabilitySpec.socialCost_eq_sum_val_sub_socialPayoff] at h
    linarith

/-- **Varian's Fact 5 comparative-statics check** (`prob_totalEffort_le_of_subset_of_isPureNash` and
`prob_weakestLink_le_of_subset_of_isPureNash`) across `{0} ⊆ {0, 1}` on `wrongAgentSpec`: adding
agent `1` (`xBar = ![2, 3]`) raises equilibrium total-effort reliability while keeping weakest-link
focal equilibrium reliability bounded by `{0}`'s focal reliability. -/
theorem wrongAgentSpec_fact5_checked :
    let S : Finset (Fin 2) := {0}
    let T : Finset (Fin 2) := {0, 1}
    letI : Nonempty S := ⟨⟨0, mem_singleton_self 0⟩⟩
    letI : Nonempty T := ⟨⟨0, by decide⟩⟩
    (∀ (xS : S → ℝ≥0) (xT : T → ℝ≥0),
      (wrongAgentSpec.restrict S).totalEffortGame.IsPureNash xS →
      (wrongAgentSpec.restrict T).totalEffortGame.IsPureNash xT →
      wrongAgentSpec.prob (totalEffort xS) ≤ wrongAgentSpec.prob (totalEffort xT)) ∧
    (∀ xT : T → ℝ≥0,
      (wrongAgentSpec.restrict T).weakestLinkGame.IsPureNash xT →
      wrongAgentSpec.prob (weakestLink xT) ≤
        wrongAgentSpec.prob (weakestLink fun _ : S =>
          univ.inf' univ_nonempty (fun i : S => ![(2 : ℝ≥0), 3] i.val))) := by
  intro S T
  have : Nonempty S := ⟨⟨0, mem_singleton_self 0⟩⟩
  have : Nonempty T := ⟨⟨0, by decide⟩⟩
  have hST : S ⊆ T := by decide
  have hVal : ∀ i, 0 < wrongAgentSpec.val i := fun i => by
    fin_cases i <;> norm_num [wrongAgentSpec]
  have hCost : ∀ i, 0 ≤ wrongAgentSpec.unitCost i := fun i => by
    fin_cases i <;> norm_num [wrongAgentSpec]
  refine ⟨fun xS xT hxS hxT =>
    wrongAgentSpec.prob_totalEffort_le_of_subset_of_isPureNash hST strictConcaveOn_reliabilityCurve
      monotoneOn_reliabilityCurve hVal wrongAgentSpec_opt hxS hxT,
    fun xT hxT =>
      (wrongAgentSpec.prob_weakestLink_le_of_subset_of_isPureNash hST
        strictConcaveOn_reliabilityCurve monotoneOn_reliabilityCurve hVal hCost wrongAgentSpec_opt
        hxT).2⟩

/-! ### 4. Kunreuther–Heal (2003) Table 2: pure, mixed, correlated, and taxed equilibria -/

/-- Kunreuther–Heal (2003) Table 2 instance (`p = 1/10, q = 4/5, L = 1000, c = 95`). -/
noncomputable def khTable2 : InterdependentSecuritySpec (Fin 2) :=
  symmetricIDSSpec (Fin 2) (1 / 10) (4 / 5) 1000 95

theorem khTable2_checked :
    khTable2.toCostGame.IsPureNash (fun _ => true) ∧
    khTable2.toCostGame.IsPureNash (fun _ => false) ∧
    khTable2.toCostGame.cost 0 (fun _ => true) = 95 ∧
    khTable2.toCostGame.cost 0 (fun _ => false) = 172 ∧
    ¬ khTable2.toCostGame.IsPureNash ![true, false] ∧
    (∃ (mix : Fin 2 → Bool → ℝ) (σ : Convexity.StdSimplex ℝ (Fin 2 → Bool)),
      khTable2.toCostGame.IsMixedNash mix ∧
      khTable2.toCostGame.IsCorrelatedEquilibrium σ ∧
      ∀ i, khTable2.toCostGame.expectedCost mix i -
        σ.weights.sum (fun s w => w * khTable2.toCostGame.cost i s) = 15 / 8) ∧
    ∀ σ : Convexity.StdSimplex ℝ (Fin 2 → Bool),
      (symmetricIDSSpec (Fin 2) (1 / 10) (4 / 5) 1000 (95 - 4)).toCostGame
        |>.IsCoarseCorrelatedEquilibrium σ →
      σ = Convexity.StdSimplex.single (fun _ => true) := by
  have hTrue : khTable2.toCostGame.IsPureNash (fun _ => true) := by
    rw [khTable2.isPureNash_allTrue_iff]
    intro _; norm_num [khTable2, symmetricIDSSpec]
  have hFalse : khTable2.toCostGame.IsPureNash (fun _ => false) := by
    rw [khTable2.isPureNash_allFalse_iff]
    intro i
    have hcard : ((univ.erase i).filter (fun _ : Fin 2 => !false)).card = 1 := by
      rw [filter_true_of_mem (fun _ _ => by simp), card_erase_of_mem (mem_univ i), card_univ,
        Fintype.card_fin]
    rw [khTable2,
      (symmetricIDSSpec_criticalCost_eq_geom_sum (1 / 10) (4 / 5) 1000 95 i (fun _ => false)).2,
      hcard]
    norm_num [symmetricIDSSpec]
  have hcostT : khTable2.toCostGame.cost 0 (fun _ => true) = 95 := by
    simp only [khTable2, InterdependentSecuritySpec.toCostGame, ↓reduceIte,
      InterdependentSecuritySpec.contagionProb_allTrue, mul_zero, add_zero, symmetricIDSSpec]
  have hcostF : khTable2.toCostGame.cost 0 (fun _ => false) = 172 := by
    have h := (symmetricIDSSpec_cost_allFalse_eq_geom_sum 1 (1 / 10) (4 / 5) 1000 95 0).2
    simpa only [khTable2] using h.trans (by norm_num)
  have hNoAsym : ¬ khTable2.toCostGame.IsPureNash ![true, false] := by
    intro hN
    rcases eq_const_of_isPureNash_symmetricIDSSpec (p := 1 / 10) (q := 4 / 5) (L := 1000) (c := 95)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (s := ![true, false]) hN with hAllT | hAllF
    · have h1 := hAllT 1
      simp at h1
    · have h0 := hAllF 0
      simp at h0
  obtain ⟨_, _, hMix, ⟨σ, hCE, _, hGap⟩, _⟩ :=
    symmetricIDSSpec_isMixedNash_and_correlated_strict_improvement
      (p := 1 / 10) (q := 4 / 5) (L := 1000) (c := 95)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hTrue, hFalse, hcostT, hcostF, hNoAsym, ⟨_, σ, hMix, hCE, fun i => ?_⟩, ?_⟩
  · exact (hGap i).trans (by norm_num)
  · intro τ hτ
    exact isCoarseCorrelatedEquilibrium_symmetricIDSSpec_taxed_unique
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Fintype.card_fin]) hτ

/-! ### 5. Heal–Kunreuther (2007) §5.2 3-airline 2-round domino tipping cascade -/

/-- Three-airline Class 1 IDS instance (`investCost = ![75, 85, 90]`, `contagion = 1/5`) exhibiting
a 2-round domino tipping cascade seeded by `{2}`. -/
noncomputable def threeAirlineCascade : InterdependentSecuritySpec (Fin 3) where
  directProb := fun _ => 1
  loss := fun _ => 100
  investCost := ![75, 85, 90]
  contagion := fun _ _ => 1 / 5

/-- Seed `{2}` does **not** tip airline `1` in one round (`80 < 85`), yet tips airline `0`
(`80 ≥ 75`) in round 1 and then airline `1` (`100 ≥ 85`) in round 2, reaching universal investment
`TipsAll {2}` which persists as a self-enforcing pure Nash equilibrium. -/
theorem threeAirlineCascade_two_round_tipping :
    ¬ threeAirlineCascade.IsCriticalCoalition {2} ∧
    threeAirlineCascade.TipsAll {2} ∧
    threeAirlineCascade.toCostGame.IsPureNash (fun _ => true) ∧
    threeAirlineCascade.toCostGame.IsPureNash (fun _ => false) := by
  -- Helper computing `noContagionProb` from unprotected peer count `(4/5)^k`.
  have hnoCont : ∀ (i : Fin 3) (s : Fin 3 → Bool),
      threeAirlineCascade.noContagionProb i s =
        (4 / 5 : ℝ) ^ ((univ.erase i).filter (fun j => !s j)).card := fun i s => by
    simp only [InterdependentSecuritySpec.noContagionProb, threeAirlineCascade, prod_const]
    norm_num
  have hNot1Step : ¬ threeAirlineCascade.IsCriticalCoalition {2} := by
    intro hCrit
    have h1 := hCrit 1 (by decide)
    have hc1 : ((univ.erase (1 : Fin 3)).filter
        (fun j => !decide (j ∈ ({2} : Finset (Fin 3))))).card = 1 := by decide
    rw [InterdependentSecuritySpec.criticalCost, hnoCont, hc1] at h1
    norm_num [threeAirlineCascade] at h1
  -- Compute round 1 (`![true, false, true]`), round 2 (`all true`), and round 3 (`all true`).
  have hStep1 : threeAirlineCascade.cascadeStep {2} (fun i => decide (i ∈ ({2} : Finset (Fin 3)))) =
      ![true, false, true] := by
    ext i
    simp only [InterdependentSecuritySpec.cascadeStep, InterdependentSecuritySpec.criticalCost,
      hnoCont]
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · have hc : ((univ.erase (0 : Fin 3)).filter
          (fun j => !decide (j ∈ ({2} : Finset (Fin 3))))).card = 1 := by decide
      simp only [hc]
      norm_num [threeAirlineCascade]
    · have hc : ((univ.erase (1 : Fin 3)).filter
          (fun j => !decide (j ∈ ({2} : Finset (Fin 3))))).card = 1 := by decide
      simp only [hc]
      norm_num [threeAirlineCascade]
    · simp
  have hStep2 : threeAirlineCascade.cascadeStep {2} ![true, false, true] = fun _ => true := by
    ext i
    simp only [InterdependentSecuritySpec.cascadeStep, InterdependentSecuritySpec.criticalCost,
      hnoCont]
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · have hc : ((univ.erase (0 : Fin 3)).filter (fun j => !(![true, false, true] j))).card = 1 :=
        by decide
      simp only [hc]
      norm_num [threeAirlineCascade]
    · have hc : ((univ.erase (1 : Fin 3)).filter (fun j => !(![true, false, true] j))).card = 0 :=
        by decide
      simp only [hc]
      norm_num [threeAirlineCascade]
    · simp
  have hStep3 : threeAirlineCascade.cascadeStep {2} (fun _ => true) = fun _ => true := by
    ext i
    simp only [InterdependentSecuritySpec.cascadeStep,
      InterdependentSecuritySpec.criticalCost_allTrue]
    fin_cases i <;> norm_num [threeAirlineCascade]
  have hTips : threeAirlineCascade.TipsAll {2} := by
    simp only [InterdependentSecuritySpec.TipsAll, Fintype.card_fin, Function.iterate_succ_apply',
      Function.iterate_zero_apply, hStep1, hStep2, hStep3]
  have hTrue : threeAirlineCascade.toCostGame.IsPureNash (fun _ => true) :=
    threeAirlineCascade.isPureNash_allTrue_of_tipsAll (fun _ => by norm_num [threeAirlineCascade])
      (fun _ => by norm_num [threeAirlineCascade]) (fun _ _ => by norm_num [threeAirlineCascade])
      (fun _ _ => by norm_num [threeAirlineCascade]) hTips
      (fun m hm => by rw [mem_singleton.mp hm]; norm_num [threeAirlineCascade])
  have hFalse : threeAirlineCascade.toCostGame.IsPureNash (fun _ => false) := by
    rw [threeAirlineCascade.isPureNash_allFalse_iff]
    intro i
    rw [InterdependentSecuritySpec.criticalCost, hnoCont]
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · have hc : ((univ.erase (0 : Fin 3)).filter (fun _ : Fin 3 => !false)).card = 2 := by decide
      rw [hc]; norm_num [threeAirlineCascade]
    · have hc : ((univ.erase (1 : Fin 3)).filter (fun _ : Fin 3 => !false)).card = 2 := by decide
      rw [hc]; norm_num [threeAirlineCascade]
    · have hc : ((univ.erase (2 : Fin 3)).filter (fun _ : Fin 3 => !false)).card = 2 := by decide
      rw [hc]; norm_num [threeAirlineCascade]
  exact ⟨hNot1Step, hTips, hTrue, hFalse⟩

/-! ### 6. Counterexamples to unaligned-cost HK2007 Theorem 3 & aligned positive check -/

/-- **1-step counterexample (`Fin 3`)**: `qExt = ![4/10, 3/10, 1/10]`, `investCost = ![89, 95, 59]`.
Both `all false` and `all true` are pure Nash equilibria and `{1}` (`qExt 1 = 3/10`) is a 1-step
critical coalition, yet top-externality `{0}` (`qExt 0 = 4/10`) is **not** a 1-step critical
coalition because `criticalCost 1 (seed {0}) = 90 < 95 = investCost 1`. -/
noncomputable def hkThm3Counterexample3 : InterdependentSecuritySpec (Fin 3) where
  directProb := fun _ => 1
  loss := fun _ => 100
  investCost := ![89, 95, 59]
  contagion := fun j _ => (![(4 / 10 : ℝ), 3 / 10, 1 / 10] j)

theorem hkThm3Counterexample3_checked :
    hkThm3Counterexample3.toCostGame.IsPureNash (fun _ => true) ∧
    hkThm3Counterexample3.toCostGame.IsPureNash (fun _ => false) ∧
    hkThm3Counterexample3.IsCriticalCoalition {1} ∧
    ¬ hkThm3Counterexample3.IsCriticalCoalition {0} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hkThm3Counterexample3.isPureNash_allTrue_iff]
    intro i; fin_cases i <;> norm_num [hkThm3Counterexample3]
  · rw [hkThm3Counterexample3.isPureNash_allFalse_iff]
    intro i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · have hs : (univ.erase (0 : Fin 3)).filter (fun _ : Fin 3 => !false) = {1, 2} := by decide
      rw [InterdependentSecuritySpec.criticalCost, InterdependentSecuritySpec.noContagionProb, hs,
        prod_pair (by decide)]
      norm_num [hkThm3Counterexample3]
    · have hs : (univ.erase (1 : Fin 3)).filter (fun _ : Fin 3 => !false) = {0, 2} := by decide
      rw [InterdependentSecuritySpec.criticalCost, InterdependentSecuritySpec.noContagionProb, hs,
        prod_pair (by decide)]
      norm_num [hkThm3Counterexample3]
    · have hs : (univ.erase (2 : Fin 3)).filter (fun _ : Fin 3 => !false) = {0, 1} := by decide
      rw [InterdependentSecuritySpec.criticalCost, InterdependentSecuritySpec.noContagionProb, hs,
        prod_pair (by decide)]
      norm_num [hkThm3Counterexample3]
  · intro j hj
    fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hj ⊢
    · have hs : (univ.erase (0 : Fin 3)).filter
          (fun u => !decide (u ∈ ({1} : Finset (Fin 3)))) = {2} := by decide
      rw [InterdependentSecuritySpec.criticalCost, InterdependentSecuritySpec.noContagionProb, hs,
        prod_singleton]
      norm_num [hkThm3Counterexample3]
    · exact False.elim (hj (mem_singleton_self 1))
    · have hs : (univ.erase (2 : Fin 3)).filter
          (fun u => !decide (u ∈ ({1} : Finset (Fin 3)))) = {0} := by decide
      rw [InterdependentSecuritySpec.criticalCost, InterdependentSecuritySpec.noContagionProb, hs,
        prod_singleton]
      norm_num [hkThm3Counterexample3]
  · intro hCrit0
    have h1 := hCrit0 1 (by decide)
    have hs : (univ.erase (1 : Fin 3)).filter
        (fun u => !decide (u ∈ ({0} : Finset (Fin 3)))) = {2} := by decide
    rw [InterdependentSecuritySpec.criticalCost, InterdependentSecuritySpec.noContagionProb, hs,
      prod_singleton] at h1
    norm_num [hkThm3Counterexample3] at h1

/-- **Multi-step `TipsAll` counterexample (`Fin 4`)**: `qExt = ![4/10, 35/100, 14/100, 14/100]`,
`investCost = ![70, 95, 85, 85]`. Seed `{1}` (`qExt 1 = 35/100`) tips all 4 agents in 2 rounds,
whereas top-externality `{0}` (`qExt 0 = 4/10`) stalls at `{0}` (`¬ TipsAll {0}`). -/
noncomputable def hkThm3Counterexample4 : InterdependentSecuritySpec (Fin 4) where
  directProb := fun _ => 1
  loss := fun _ => 100
  investCost := ![70, 95, 85, 85]
  contagion := fun j _ => (![(4 / 10 : ℝ), 35 / 100, 14 / 100, 14 / 100] j)

theorem hkThm3Counterexample4_checked :
    hkThm3Counterexample4.TipsAll {1} ∧ ¬ hkThm3Counterexample4.TipsAll {0} := by
  -- First show `cascadeStep {0}` fixes `seed {0}`, so `{0}` never tips anyone!
  have hStuck0 : hkThm3Counterexample4.cascadeStep {0}
      (fun i => decide (i ∈ ({0} : Finset (Fin 4)))) =
      (fun i => decide (i ∈ ({0} : Finset (Fin 4)))) := by
    ext i
    simp only [InterdependentSecuritySpec.cascadeStep]
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · simp
    · have hs : (univ.erase (1 : Fin 4)).filter
          (fun u => !decide (u ∈ ({0} : Finset (Fin 4)))) = {2, 3} := by decide
      simp only [InterdependentSecuritySpec.criticalCost,
        InterdependentSecuritySpec.noContagionProb, hs, prod_pair (by decide : (2 : Fin 4) ≠ 3)]
      norm_num [hkThm3Counterexample4]
    · have hs : (univ.erase (2 : Fin 4)).filter
          (fun u => !decide (u ∈ ({0} : Finset (Fin 4)))) = {1, 3} := by decide
      simp only [InterdependentSecuritySpec.criticalCost,
        InterdependentSecuritySpec.noContagionProb, hs, prod_pair (by decide : (1 : Fin 4) ≠ 3)]
      norm_num [hkThm3Counterexample4]
    · have hs : (univ.erase (3 : Fin 4)).filter
          (fun u => !decide (u ∈ ({0} : Finset (Fin 4)))) = {1, 2} := by decide
      simp only [InterdependentSecuritySpec.criticalCost,
        InterdependentSecuritySpec.noContagionProb, hs, prod_pair (by decide : (1 : Fin 4) ≠ 2)]
      norm_num [hkThm3Counterexample4]
  have hNotTips0 : ¬ hkThm3Counterexample4.TipsAll {0} := by
    intro hT
    simp only [InterdependentSecuritySpec.TipsAll, Fintype.card_fin, Function.iterate_succ_apply',
      Function.iterate_zero_apply, hStuck0] at hT
    have h1 := congrFun hT 1
    revert h1
    decide
  -- Show `{1}` reaches `{0, 1}` (`![true, true, false, false]`) in wave 1 and `all true` in wave 2.
  have hWave1 : hkThm3Counterexample4.cascadeStep {1}
      (fun i => decide (i ∈ ({1} : Finset (Fin 4)))) = ![true, true, false, false] := by
    ext i
    simp only [InterdependentSecuritySpec.cascadeStep]
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · have hs : (univ.erase (0 : Fin 4)).filter
          (fun u => !decide (u ∈ ({1} : Finset (Fin 4)))) = {2, 3} := by decide
      simp only [InterdependentSecuritySpec.criticalCost,
        InterdependentSecuritySpec.noContagionProb, hs, prod_pair (by decide : (2 : Fin 4) ≠ 3)]
      norm_num [hkThm3Counterexample4]
    · simp
    · have hs : (univ.erase (2 : Fin 4)).filter
          (fun u => !decide (u ∈ ({1} : Finset (Fin 4)))) = {0, 3} := by decide
      simp only [InterdependentSecuritySpec.criticalCost,
        InterdependentSecuritySpec.noContagionProb, hs, prod_pair (by decide : (0 : Fin 4) ≠ 3)]
      norm_num [hkThm3Counterexample4]
    · have hs : (univ.erase (3 : Fin 4)).filter
          (fun u => !decide (u ∈ ({1} : Finset (Fin 4)))) = {0, 2} := by decide
      simp only [InterdependentSecuritySpec.criticalCost,
        InterdependentSecuritySpec.noContagionProb, hs, prod_pair (by decide : (0 : Fin 4) ≠ 2)]
      norm_num [hkThm3Counterexample4]
  have hWave2 : hkThm3Counterexample4.cascadeStep {1} ![true, true, false, false] =
      fun _ => true := by
    ext i
    simp only [InterdependentSecuritySpec.cascadeStep]
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · have hs : (univ.erase (0 : Fin 4)).filter
          (fun u => !(![true, true, false, false] u)) = {2, 3} := by decide
      simp only [InterdependentSecuritySpec.criticalCost,
        InterdependentSecuritySpec.noContagionProb, hs, prod_pair (by decide : (2 : Fin 4) ≠ 3)]
      norm_num [hkThm3Counterexample4]
    · simp
    · have hs : (univ.erase (2 : Fin 4)).filter
          (fun u => !(![true, true, false, false] u)) = {3} := by decide
      simp only [InterdependentSecuritySpec.criticalCost,
        InterdependentSecuritySpec.noContagionProb, hs, prod_singleton]
      norm_num [hkThm3Counterexample4]
    · have hs : (univ.erase (3 : Fin 4)).filter
          (fun u => !(![true, true, false, false] u)) = {2} := by decide
      simp only [InterdependentSecuritySpec.criticalCost,
        InterdependentSecuritySpec.noContagionProb, hs, prod_singleton]
      norm_num [hkThm3Counterexample4]
  have hWave3 : hkThm3Counterexample4.cascadeStep {1} (fun _ => true) = fun _ => true := by
    ext i
    simp only [InterdependentSecuritySpec.cascadeStep,
      InterdependentSecuritySpec.criticalCost_allTrue]
    fin_cases i <;> norm_num [hkThm3Counterexample4]
  have hTips1 : hkThm3Counterexample4.TipsAll {1} := by
    simp only [InterdependentSecuritySpec.TipsAll, Fintype.card_fin, Function.iterate_succ_apply',
      Function.iterate_zero_apply, hWave1, hWave2, hWave3]
  exact ⟨hTips1, hNotTips0⟩

/-- **Positive check of `isCriticalCoalition_of_higher_contagion`**: when normalized reluctance is
aligned (`investCost = ![95, 89, 59]`, `qExt = ![4/10, 3/10, 1/10]`), `IsCriticalCoalition {1}`
transfers to top-externality `{0}`. -/
theorem hkThm3Aligned_positive_checked :
    let G : InterdependentSecuritySpec (Fin 3) := {
      directProb := fun _ => 1
      loss := fun _ => 100
      investCost := ![95, 89, 59]
      contagion := fun j _ => (![(4 / 10 : ℝ), 3 / 10, 1 / 10] j)
    }
    G.IsCriticalCoalition {1} → G.IsCriticalCoalition {0} := by
  intro G hCrit1
  refine G.isCriticalCoalition_of_higher_contagion
    (qExt := ![(4 / 10 : ℝ), 3 / 10, 1 / 10])
    (fun _ => zero_lt_one) (fun _ => by norm_num) (fun _ _ _ => rfl)
    (fun j => by fin_cases j <;> norm_num) (by decide)
    (fun j hj k hk => ?_) (fun j hj k hk => ?_) hCrit1
  · have hj0 : j = 0 := by
      have : j ∈ ({0} : Finset (Fin 3)) := (mem_sdiff.mp hj).1
      exact mem_singleton.mp this
    have hk1 : k = 1 := by
      have : k ∈ ({1} : Finset (Fin 3)) := (mem_sdiff.mp hk).1
      exact mem_singleton.mp this
    subst hj0; subst hk1; norm_num
  · have hj0 : j = 0 := by
      have : j ∈ ({0} : Finset (Fin 3)) := (mem_sdiff.mp hj).1
      exact mem_singleton.mp this
    have hk1 : k = 1 := by
      have : k ∈ ({1} : Finset (Fin 3)) := (mem_sdiff.mp hk).1
      exact mem_singleton.mp this
    subst hj0; subst hk1; norm_num [G]

end CslibFrontierTests.GameTheory.SecurityEconomics
