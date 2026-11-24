/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Mechanism.FacilityLocation.MaxCost
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Maximum-cost facility location and the LRM mechanism: checked clients and boundaries

Non-vacuous checked instances and sharp boundary separations for
`CslibFrontier.GameTheory.Mechanism.FacilityLocation.MaxCost`:

1. **Concrete evaluations on `![0, 1, 10] : Fin 3 → ℝ`**:
   - `leftmost = 0`, `rightmost = 10`, `center = 5`, `optMaxCost = 5`.
   - `medianMechanism` places the facility at `1`, achieving optimal `expectedSocialCost = 10` and
     `expectedMaxCost = 9 ≤ 2 * 5`, while `leftmostMechanism` incurs `expectedMaxCost = 10 = 2 * 5`
     (witnessing tightness of the deterministic `2`-approximation bound).
   - `lrmPMF` assigns probabilities `(1/4, 1/4, 1/2)` to `(0, 10, 5)` and achieves
     `expectedMaxCost = 15 / 2 = (3 / 2) * 5`, strictly below every deterministic strategyproof
     bound, while incurring `expectedSocialCost = 29 / 2 > 10 = optSocialCost` (hence not
     `1`-approximate for social cost).
2. **Tightness and lower-bound separations on `Fin 3`**:
   - Neither `medianMechanism` nor any deterministic strategyproof mechanism achieves
     `HasMaxCostApproxRatio (2 - 1 / 100)`.
   - `lrmMechanism` achieves `HasMaxCostApproxRatio (3 / 2)`, and no randomized strategyproof
     mechanism achieves `HasMaxCostApproxRatio (3 / 2 - 1 / 100)`.
3. **Necessity of `2 ≤ Fintype.card ι` in Theorems 3.2 and 3.4**:
   - On `Fin 1`, `medianMechanism` is deterministic, strongly group strategyproof, and
     `1`-approximate (`1 < 3 / 2 < 2`) for maximum cost because the sole agent pays `0`.
4. **Sharp coalitional threshold `n = 2` vs. `n = 3` for `lrmMechanism`**:
   - For `Fin 3`, `¬ (lrmMechanism (ι := Fin 3)).IsGroupStrategyProof`.
   - For `Fin 2`, `(lrmMechanism (ι := Fin 2)).IsGroupStrategyProof` holds (every nonempty
     coalition is either a singleton—covered by strategyproofness—or the grand coalition `{0, 1}`
     of both boundary agents, whose sum of expected costs is at least `|x 1 - x 0|`, preventing
     strict improvement without hurting the partner).
-/

set_option linter.privateModule false
namespace CslibFrontierTests.GameTheory.FacilityLocationMaxCost

open Cslib.GameTheory.FacilityLocation

private def prof3 : Fin 3 → ℝ := ![0, 1, 10]

private theorem prof3_leftmost_rightmost :
    leftmost prof3 = 0 ∧ rightmost prof3 = 10 :=
  leftmost_rightmost_of_bounds (i₀ := 0) (i₁ := 2) rfl rfl fun j => by
    fin_cases j <;> norm_num [prof3]

private theorem prof3_center : center prof3 = 5 := by
  rw [center, prof3_leftmost_rightmost.1, prof3_leftmost_rightmost.2]
  norm_num

private theorem prof3_optMaxCost : optMaxCost prof3 = 5 := by
  rw [optMaxCost_real_eq, prof3_leftmost_rightmost.1, prof3_leftmost_rightmost.2]
  norm_num

private theorem prof3_lowerMedian : Fintype.lowerMedian prof3 = 1 := by
  rw [Fintype.lowerMedian_def]
  refine Fintype.orderStatistic_eq_of_isOrderStatistic (by decide) ⟨⟨1, rfl⟩, ?_, ?_⟩
  · have heq : (Finset.univ.filter fun j : Fin 3 => prof3 j < 1) = {0} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      fin_cases j <;> norm_num [prof3]
    rw [heq]; decide
  · have heq : (Finset.univ.filter fun j : Fin 3 => prof3 j ≤ 1) = {0, 1} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      fin_cases j <;> norm_num [prof3]
    rw [heq]; decide

/-- Concrete evaluation of `medianMechanism`, `leftmostMechanism`, and `lrmMechanism` on
`prof3 = ![0, 1, 10]`. -/
example :
    optMaxCost prof3 = 5 ∧
      expectedMaxCost (medianMechanism prof3) prof3 = 9 ∧
      expectedMaxCost (leftmostMechanism prof3) prof3 = 10 ∧
      lrmPMF prof3 0 = 1 / 4 ∧
      lrmPMF prof3 10 = 1 / 4 ∧
      lrmPMF prof3 5 = 1 / 2 ∧
      expectedMaxCost (lrmMechanism prof3) prof3 = 15 / 2 ∧
      expectedSocialCost (lrmMechanism prof3) prof3 = 29 / 2 ∧
      ¬ (lrmMechanism (ι := Fin 3)).HasApproxRatio 1 := by
  have hlt : leftmost prof3 < rightmost prof3 := by
    rw [prof3_leftmost_rightmost.1, prof3_leftmost_rightmost.2]; norm_num
  obtain ⟨hp0, hp10, hp5⟩ := lrmPMF_apply_of_lt hlt
  rw [prof3_leftmost_rightmost.1] at hp0
  rw [prof3_leftmost_rightmost.2] at hp10
  rw [prof3_center] at hp5
  have hmed_mc : expectedMaxCost (medianMechanism prof3) prof3 = 9 := by
    rw [medianMechanism, Mechanism.expectedMaxCost_deterministic, prof3_lowerMedian,
      maxCost_real_eq, prof3_center, prof3_leftmost_rightmost.1, prof3_leftmost_rightmost.2]
    norm_num
  have hleft_mc : expectedMaxCost (leftmostMechanism prof3) prof3 = 10 := by
    rw [leftmostMechanism, Mechanism.expectedMaxCost_deterministic, prof3_leftmost_rightmost.1,
      maxCost_real_eq, prof3_center, prof3_leftmost_rightmost.1, prof3_leftmost_rightmost.2]
    norm_num
  have hlrm_mc : expectedMaxCost (lrmMechanism prof3) prof3 = 15 / 2 := by
    rw [expectedMaxCost_lrmMechanism, prof3_optMaxCost]; norm_num
  have hlrm_sc : expectedSocialCost (lrmMechanism prof3) prof3 = 29 / 2 := by
    rw [expectedSocialCost, Fin.sum_univ_three]
    simp only [expectedCost_lrmMechanism, prof3_leftmost_rightmost.1,
      prof3_leftmost_rightmost.2, prof3_center]
    norm_num [prof3]
  have hnot_sc1 : ¬ (lrmMechanism (ι := Fin 3)).HasApproxRatio 1 := by
    intro h1
    have hreal := (Mechanism.hasApproxRatio_iff_expectedSocialCost_le zero_le_one
      lrmMechanism_hasFiniteCost).mp h1 prof3
    have hopt_sc : optSocialCost prof3 = 10 := by
      rw [← (lowerMedian_isOptimal prof3).socialCost_eq_optSocialCost, prof3_lowerMedian,
        socialCost, Fin.sum_univ_three]
      norm_num [prof3, Real.dist_eq]
    rw [hlrm_sc, hopt_sc] at hreal
    linarith
  exact ⟨prof3_optMaxCost, hmed_mc, hleft_mc, hp0, hp10, hp5, hlrm_mc, hlrm_sc, hnot_sc1⟩

/-- Tightness of deterministic `2` and randomized `3 / 2` bounds on `Fin 3`. -/
example :
    (medianMechanism (ι := Fin 3)).HasApproxRatio 1 ∧
      (medianMechanism (ι := Fin 3)).HasMaxCostApproxRatio 2 ∧
      ¬ (medianMechanism (ι := Fin 3)).HasMaxCostApproxRatio (2 - 1 / 100) ∧
      (lrmMechanism (ι := Fin 3)).IsWeakGroupStrategyProof ∧
      (lrmMechanism (ι := Fin 3)).HasMaxCostApproxRatio (3 / 2) ∧
      ¬ (lrmMechanism (ι := Fin 3)).HasMaxCostApproxRatio (3 / 2 - 1 / 100) ∧
      ¬ (centerMechanism (ι := Fin 3)).IsStrategyProof := by
  refine ⟨medianMechanism_hasApproxRatio_one,
    medianMechanism_hasMaxCostApproxRatio_two,
    fun h => ?_,
    lrmMechanism_isWeakGroupStrategyProof,
    lrmMechanism_hasMaxCostApproxRatio,
    fun h => ?_,
    not_isStrategyProof_centerMechanism (by decide)⟩
  · have h2 := two_le_of_deterministic_isStrategyProof (ι := Fin 3) (by decide)
      medianMechanism_isStrategyProof h
    linarith
  · have h32 := three_halves_le_of_isStrategyProof (ι := Fin 3) (by decide)
      lrmMechanism_isStrategyProof h
    linarith

/-- Boundary check (`n = 1`): on `Fin 1`, `medianMechanism` achieves maximum-cost approximation
ratio `1 < 3 / 2 < 2`, confirming that `2 ≤ Fintype.card ι` is necessary in Theorems 3.2 and 3.4. -/
example :
    (medianMechanism (ι := Fin 1)).IsGroupStrategyProof ∧
      (medianMechanism (ι := Fin 1)).HasMaxCostApproxRatio 1 := by
  refine ⟨medianMechanism_isGroupStrategyProof, ?_⟩
  rw [medianMechanism, Mechanism.hasMaxCostApproxRatio_deterministic_iff _ zero_le_one]
  intro x
  have hmed : Fintype.lowerMedian x = x 0 := by
    obtain ⟨i, hi⟩ := (Fintype.orderStatistic_isOrderStatistic x (k := 0) (by decide)).1
    rw [Fintype.lowerMedian_def, show (Fintype.card (Fin 1) - 1) / 2 = 0 by decide, ← hi,
      Subsingleton.elim i 0]
  have hmc0 : maxCost x (Fintype.lowerMedian x) = 0 := by
    refine le_antisymm ?_ (maxCost_nonneg x _)
    rw [maxCost_le_iff, hmed]
    intro i
    rw [Subsingleton.elim i 0, dist_self]
  rw [hmc0, one_mul]
  exact optMaxCost_nonneg x

/-- Sharp coalitional threshold (`n = 2` vs `n = 3`): for two agents, `lrmMechanism` is strongly
group strategyproof, whereas for three agents it is only weakly group strategyproof. -/
example :
    (lrmMechanism (ι := Fin 2)).IsGroupStrategyProof ∧
      ¬ (lrmMechanism (ι := Fin 3)).IsGroupStrategyProof := by
  refine ⟨?_, not_isGroupStrategyProof_lrmMechanism (by decide)⟩
  rintro x z A ⟨hle, j, hjA, hlt⟩
  have hle_r : ∀ i ∈ A,
      expectedCost (lrmMechanism (A.piecewise z x)) (x i) ≤
        expectedCost (lrmMechanism x) (x i) := fun i hi =>
    (expectedECost_le_iff_expectedCost_le
      (lrmMechanism_hasFiniteCost _ _) (lrmMechanism_hasFiniteCost _ _)).mp (hle i hi)
  have hlt_r : expectedCost (lrmMechanism (A.piecewise z x)) (x j) <
      expectedCost (lrmMechanism x) (x j) :=
    (expectedECost_lt_iff_expectedCost_lt
      (lrmMechanism_hasFiniteCost _ _) (lrmMechanism_hasFiniteCost _ _)).mp hlt
  have hcardA : A.card ≤ 2 := by simpa using Finset.card_le_univ A
  by_cases hA1 : A.card = 1
  · obtain ⟨i₀, rfl⟩ := Finset.card_eq_one.mp hA1
    rcases Finset.mem_singleton.mp hjA with rfl
    have hpw : ({j} : Finset (Fin 2)).piecewise z x = Function.update x j (z j) := by
      funext k
      by_cases hk : k = j
      · subst hk; simp [Finset.piecewise]
      · simp [Finset.piecewise, hk]
    have hsp := (Mechanism.isStrategyProof_iff_expectedCost_le
      (M := lrmMechanism (ι := Fin 2)) lrmMechanism_hasFiniteCost).mp
      lrmMechanism_isStrategyProof x j (z j)
    rw [hpw] at hlt_r
    exact hlt_r.not_ge hsp
  · have hA2 : A.card = 2 := by
      have hpos : 0 < A.card := Finset.card_pos.mpr ⟨j, hjA⟩
      omega
    have hAu : A = Finset.univ := Finset.eq_univ_of_card A (by simpa using hA2)
    subst hAu
    rw [Finset.piecewise_univ] at hle_r hlt_r
    have hpair : ∀ {a b : ℝ}, a ≤ b →
        (1 / 4 * |a - a| + 1 / 4 * |a - b| + 1 / 2 * |a - (a + b) / 2|) +
          (1 / 4 * |b - a| + 1 / 4 * |b - b| + 1 / 2 * |b - (a + b) / 2|) = b - a := by
      intro a b hab
      rw [sub_self, sub_self, abs_zero,
        abs_of_nonpos (by linarith : a - b ≤ 0),
        abs_of_nonpos (by linarith : a - (a + b) / 2 ≤ 0),
        abs_of_nonneg (by linarith : 0 ≤ b - a),
        abs_of_nonneg (by linarith : 0 ≤ b - (a + b) / 2)]
      ring
    have hsum_x : expectedCost (lrmMechanism x) (x 0) +
        expectedCost (lrmMechanism x) (x 1) = |x 0 - x 1| := by
      rcases le_total (x 0) (x 1) with h01 | h10
      · have hx : leftmost x = x 0 ∧ rightmost x = x 1 :=
          leftmost_rightmost_of_bounds (i₀ := 0) (i₁ := 1) rfl rfl fun k => by
            fin_cases k <;> simp [h01]
        rw [expectedCost_lrmMechanism, expectedCost_lrmMechanism, center, hx.1, hx.2, hpair h01,
          abs_of_nonpos (by linarith : x 0 - x 1 ≤ 0)]
        ring
      · have hx : leftmost x = x 1 ∧ rightmost x = x 0 :=
          leftmost_rightmost_of_bounds (i₀ := 1) (i₁ := 0) rfl rfl fun k => by
            fin_cases k <;> simp [h10]
        rw [add_comm, expectedCost_lrmMechanism, expectedCost_lrmMechanism, center, hx.1, hx.2,
          hpair h10, abs_of_nonneg (by linarith : 0 ≤ x 0 - x 1)]
    have hsum_z_ge : |x 0 - x 1| ≤ expectedCost (lrmMechanism z) (x 0) +
        expectedCost (lrmMechanism z) (x 1) := by
      have h01_tri : ∀ y : ℝ, |x 0 - x 1| ≤ |x 0 - y| + |x 1 - y| := fun y => by
        simpa only [abs_sub_comm (x 1) y] using abs_sub_le (x 0) y (x 1)
      have hL := h01_tri (leftmost z)
      have hR := h01_tri (rightmost z)
      have hC := h01_tri (center z)
      rw [expectedCost_lrmMechanism, expectedCost_lrmMechanism]
      linarith
    have h0_le := hle_r 0 (Finset.mem_univ 0)
    have h1_le := hle_r 1 (Finset.mem_univ 1)
    by_cases hj0 : j = 0
    · subst hj0; linarith
    · have hj1 : j = 1 := by omega
      subst hj1; linarith

end CslibFrontierTests.GameTheory.FacilityLocationMaxCost
