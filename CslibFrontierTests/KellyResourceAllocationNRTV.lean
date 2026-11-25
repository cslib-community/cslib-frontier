/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.ResourceAllocation.KellyMechanism
import CslibFrontier.GameTheory.ResourceAllocation.SSVCG
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Tests and boundary witnesses for NRTV Chapter 21 resource allocation mechanisms

Exercises Kelly's proportional allocation mechanism (`KellyMechanism.lean`) and Scalar Strategy
VCG (`SSVCG.lean`) on concrete instances and subtle model boundaries:

* Zero bids (`w = 0`): allocation is `0`, price is `0`, and `w = 0` is not a Nash equilibrium for
  strictly increasing utilities.
* Single user (`Fin 1`): no price-anticipating Nash equilibrium exists, while a price-taking
  competitive equilibrium does exist.
* Flat zero utilities (`U_i = 0`): `w = 0` is a Nash equilibrium with zero welfare.
* Non-concave counterexample: with `U_0(x) = 2 x^2` and `U_1(x) = U_2(x) = x`,
  `w = ![0, 1/4, 1/4]` is a Nash equilibrium achieving welfare `1 < 3/2 = (3/4) · 2`, refuting the
  `3/4` bound without concavity.
* Strictly concave symmetric witness (`U_i(x) = log (1 + x)`): explicit unique competitive and
  Nash equilibria, variational inequality, and `3/4` efficiency check.
* Affine utilities with positive zero-intercepts and concrete `KellyGame.kellyTightGame` tightness
  ratios (`n = 2` giving `5/6`, `n = 10` giving `29/38`).
* SSVCG witnesses: logarithmic surrogate family, efficient Nash equilibrium (`PoS = 1`), bluff
  equilibrium (`![3, 1/4]`), and `Real.sqrt` satisfying `HasInfiniteInitialSlope` (`PoA = 1`).
-/

namespace CslibFrontierTests.KellyResourceAllocationNRTV

open Cslib.GameTheory Filter Set
open scoped Topology

/-! ### Boundary case 1: Zero bids -/

section ZeroBids

private def twoUserLinear : KellyGame (Fin 2) where
  capacity := 1
  utility := fun _ x => x

/-- Zero total bid yields zero allocation and zero clearing price, and is not a Nash equilibrium
for strictly increasing utilities. -/
example :
    twoUserLinear.price (0 : Fin 2 → ℝ) = 0 ∧
    (∀ i, twoUserLinear.allocation (0 : Fin 2 → ℝ) i = 0) ∧
    ¬ twoUserLinear.IsNashEquilibrium (0 : Fin 2 → ℝ) := by
  refine ⟨by simp [KellyGame.price, twoUserLinear],
    fun i => by simp [KellyGame.allocation, twoUserLinear], fun hne => ?_⟩
  have hmono : ∀ i : Fin 2, StrictMonoOn (twoUserLinear.utility i) (Ici 0) :=
    fun _ _ _ _ _ hxy => hxy
  have hpos := hne.sum_erase_pos (by norm_num [twoUserLinear]) hmono 0
  simp at hpos

end ZeroBids

/-! ### Boundary case 2: Single user (`Fin 1`) -/

section SingleUser

private def oneUserLinear : KellyGame (Fin 1) where
  capacity := 1
  utility := fun _ x => x

/-- With a single user and strictly increasing utility, no price-anticipating Nash equilibrium
exists (confirming sharpness of `2 ≤ Fintype.card ι` in Theorem 21.2). -/
example (w : Fin 1 → ℝ) : ¬ oneUserLinear.IsNashEquilibrium w := by
  intro hne
  have hmono : ∀ i : Fin 1, StrictMonoOn (oneUserLinear.utility i) (Ici 0) :=
    fun _ _ _ _ _ hxy => hxy
  have hpos := hne.sum_erase_pos (by norm_num [oneUserLinear]) hmono 0
  simp at hpos

/-- By contrast, a single user with linear utility admits a price-taking competitive equilibrium
`(![1], 1)` achieving the social optimum. -/
example :
    oneUserLinear.IsCompetitiveEquilibrium ![1] 1 ∧
    oneUserLinear.IsSocialOptimum (oneUserLinear.allocation ![1]) := by
  have hce : oneUserLinear.IsCompetitiveEquilibrium ![1] 1 := by
    refine ⟨fun i => by fin_cases i; norm_num, zero_lt_one, ?_, fun i t _ => ?_⟩
    · simp [KellyGame.price, oneUserLinear]
    · fin_cases i; simp [oneUserLinear]
  exact ⟨hce, hce.isSocialOptimum (by norm_num [oneUserLinear])⟩

end SingleUser

/-! ### Boundary case 3: Identically zero utilities (`U_i = 0`) -/

section ZeroUtility

private def zeroUtilityGame : KellyGame (Fin 2) where
  capacity := 1
  utility := fun _ _ => 0

/-- When all utilities are identically `0`, the zero bid profile `0` IS a Nash equilibrium with
zero welfare (illustrating why strict monotonicity is needed for positive bids). -/
example :
    zeroUtilityGame.IsNashEquilibrium (0 : Fin 2 → ℝ) ∧
    zeroUtilityGame.welfare (zeroUtilityGame.allocation (0 : Fin 2 → ℝ)) = 0 := by
  refine ⟨⟨fun _ => le_rfl, fun i t ht => ?_⟩, by simp [KellyGame.welfare, zeroUtilityGame]⟩
  simp only [KellyGame.payoff, zeroUtilityGame, Pi.zero_apply, Function.update_self]
  linarith

end ZeroUtility

/-! ### Boundary case 4: Non-concave counterexample violating `3/4` -/

section NonConcaveCounterexample

/-- Three-user game of capacity `1` with convex non-concave `U_0(x) = 2 x^2` and linear
`U_1(x) = U_2(x) = x`. -/
private def nonConcaveGame : KellyGame (Fin 3) where
  capacity := 1
  utility := fun i x => if i = 0 then 2 * x ^ 2 else x

/-- Without concavity, the `3/4` efficiency guarantee fails: `w = ![0, 1/4, 1/4]` is a Nash
equilibrium of `nonConcaveGame` with welfare `1`, while allocating all capacity to user `0` gives
welfare `2` (ratio `1/2 < 3/4`). -/
example :
    nonConcaveGame.IsNashEquilibrium ![0, 1 / 4, 1 / 4] ∧
    nonConcaveGame.IsFeasibleAllocation ![1, 0, 0] ∧
    nonConcaveGame.welfare (nonConcaveGame.allocation ![0, 1 / 4, 1 / 4]) = 1 ∧
    nonConcaveGame.welfare ![1, 0, 0] = 2 ∧
    ¬ (3 / 4 * nonConcaveGame.welfare ![1, 0, 0] ≤
        nonConcaveGame.welfare (nonConcaveGame.allocation ![0, 1 / 4, 1 / 4])) := by
  set w : Fin 3 → ℝ := ![0, 1 / 4, 1 / 4]
  have hsum_w : ∑ j : Fin 3, w j = 1 / 2 := by
    simp [w, Fin.sum_univ_three]
    norm_num
  have hne : nonConcaveGame.IsNashEquilibrium w := by
    refine ⟨fun i => by fin_cases i <;> norm_num [w], fun i t ht => ?_⟩
    fin_cases i
    · change nonConcaveGame.payoff (Function.update w 0 t) 0 ≤ nonConcaveGame.payoff w 0
      have hsum_t : ∑ j : Fin 3, Function.update w 0 t j = t + 1 / 2 := by
        simp only [Fin.sum_univ_three, Function.update_self,
          Function.update_of_ne (show (1 : Fin 3) ≠ 0 by decide),
          Function.update_of_ne (show (2 : Fin 3) ≠ 0 by decide)]
        change t + (1 / 4 : ℝ) + 1 / 4 = t + 1 / 2
        ring
      have hpay0 : nonConcaveGame.payoff w 0 = 0 := by
        simp only [KellyGame.payoff, KellyGame.allocation, nonConcaveGame, ↓reduceIte, hsum_w]
        change 2 * (1 * 0 / (1 / 2 : ℝ)) ^ 2 - 0 = 0
        norm_num
      have hpayt : nonConcaveGame.payoff (Function.update w 0 t) 0 =
          2 * (t / (t + 1 / 2)) ^ 2 - t := by
        simp only [KellyGame.payoff, KellyGame.allocation, nonConcaveGame, ↓reduceIte,
          Function.update_self, hsum_t, one_mul]
      rw [hpay0, hpayt]
      have hden : (0 : ℝ) < (t + 1 / 2) ^ 2 := by positivity
      have hsq : 2 * t ^ 2 ≤ t * (t + 1 / 2) ^ 2 := by
        have : 0 ≤ t * (t - 1 / 2) ^ 2 := mul_nonneg ht (sq_nonneg _)
        nlinarith
      rw [div_pow, sub_nonpos, ← mul_div_assoc, div_le_iff₀ hden]
      exact hsq
    · change nonConcaveGame.payoff (Function.update w 1 t) 1 ≤ nonConcaveGame.payoff w 1
      have hsum_t : ∑ j : Fin 3, Function.update w 1 t j = t + 1 / 4 := by
        simp only [Fin.sum_univ_three, Function.update_self,
          Function.update_of_ne (show (0 : Fin 3) ≠ 1 by decide),
          Function.update_of_ne (show (2 : Fin 3) ≠ 1 by decide)]
        change (0 : ℝ) + t + 1 / 4 = t + 1 / 4
        ring
      have hpay1 : nonConcaveGame.payoff w 1 = 1 / 4 := by
        simp only [KellyGame.payoff, KellyGame.allocation, nonConcaveGame, hsum_w]
        change (1 : ℝ) * (1 / 4) / (1 / 2) - 1 / 4 = 1 / 4
        norm_num
      have hpayt : nonConcaveGame.payoff (Function.update w 1 t) 1 = t / (t + 1 / 4) - t := by
        simp only [KellyGame.payoff, KellyGame.allocation, nonConcaveGame, Function.update_self,
          hsum_t]
        change (1 : ℝ) * t / (t + 1 / 4) - t = t / (t + 1 / 4) - t
        ring
      rw [hpay1, hpayt]
      have hden : (0 : ℝ) < t + 1 / 4 := by linarith
      rw [sub_le_iff_le_add, div_le_iff₀ hden]
      nlinarith [sq_nonneg (t - 1 / 4)]
    · change nonConcaveGame.payoff (Function.update w 2 t) 2 ≤ nonConcaveGame.payoff w 2
      have hsum_t : ∑ j : Fin 3, Function.update w 2 t j = t + 1 / 4 := by
        simp only [Fin.sum_univ_three, Function.update_self,
          Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide),
          Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide)]
        change (0 : ℝ) + 1 / 4 + t = t + 1 / 4
        ring
      have hpay2 : nonConcaveGame.payoff w 2 = 1 / 4 := by
        simp only [KellyGame.payoff, KellyGame.allocation, nonConcaveGame, hsum_w]
        change (1 : ℝ) * (1 / 4) / (1 / 2) - 1 / 4 = 1 / 4
        norm_num
      have hpayt : nonConcaveGame.payoff (Function.update w 2 t) 2 = t / (t + 1 / 4) - t := by
        simp only [KellyGame.payoff, KellyGame.allocation, nonConcaveGame, Function.update_self,
          hsum_t]
        change (1 : ℝ) * t / (t + 1 / 4) - t = t / (t + 1 / 4) - t
        ring
      rw [hpay2, hpayt]
      have hden : (0 : ℝ) < t + 1 / 4 := by linarith
      rw [sub_le_iff_le_add, div_le_iff₀ hden]
      nlinarith [sq_nonneg (t - 1 / 4)]
  have hfeas : nonConcaveGame.IsFeasibleAllocation ![1, 0, 0] :=
    ⟨fun i => by fin_cases i <;> norm_num, by simp [nonConcaveGame, Fin.sum_univ_three]⟩
  have hne_w : nonConcaveGame.welfare (nonConcaveGame.allocation w) = 1 := by
    simp only [KellyGame.welfare, KellyGame.allocation, nonConcaveGame, hsum_w, Fin.sum_univ_three]
    change 2 * ((1 : ℝ) * 0 / (1 / 2)) ^ 2 + (1 : ℝ) * (1 / 4) / (1 / 2) +
      (1 : ℝ) * (1 / 4) / (1 / 2) = 1
    norm_num
  have hopt_w : nonConcaveGame.welfare ![1, 0, 0] = 2 := by
    simp only [KellyGame.welfare, nonConcaveGame, Fin.sum_univ_three]
    change 2 * (1 : ℝ) ^ 2 + 0 + 0 = 2
    norm_num
  refine ⟨hne, hfeas, hne_w, hopt_w, ?_⟩
  rw [hne_w, hopt_w]
  norm_num

end NonConcaveCounterexample

/-! ### Concrete strictly concave, affine, and tightness witnesses -/

section ConcreteWitnesses

/-- Two symmetric users with strictly concave `U(x) = log (1 + x)` on capacity `1`:
unique competitive equilibrium and unique Nash equilibrium `w_NE = ![1/6, 1/6]` (`μ = 1/3`),
achieving the symmetric allocation `![1/2, 1/2]`. -/
example :
    let G : KellyGame (Fin 2) := ⟨1, fun _ x => Real.log (1 + x)⟩
    (∃! p : (Fin 2 → ℝ) × ℝ, G.IsCompetitiveEquilibrium p.1 p.2) ∧
    (∃! w : Fin 2 → ℝ, G.IsNashEquilibrium w) ∧
    G.IsNashEquilibrium ![1 / 6, 1 / 6] ∧
    G.allocation ![1 / 6, 1 / 6] = ![1 / 2, 1 / 2] := by
  intro G
  obtain ⟨hadm, hstrict, hderiv⟩ := isAdmissibleUtility_log_one_add
  have hU : ∀ i : Fin 2, IsAdmissibleUtility (G.utility i) := fun _ => hadm
  have hce_uniq := KellyGame.existsUnique_isCompetitiveEquilibrium_of_strictConcaveOn (G := G)
    (by simp [G]) hU (fun _ => hstrict)
  have hne_uniq :=
    (KellyGame.existsUnique_isNashEquilibrium (G := G) (by decide) (by simp [G]) hU).1
  have hsum : ∑ j : Fin 2, (![1 / 6, 1 / 6] : Fin 2 → ℝ) j = 1 / 3 := by
    simp [Fin.sum_univ_two]; norm_num
  have halloc : G.allocation ![1 / 6, 1 / 6] = ![1 / 2, 1 / 2] := by
    funext i
    fin_cases i
    · simp only [KellyGame.allocation, G, hsum]
      change (1 : ℝ) * (1 / 6) / (1 / 3) = 1 / 2; norm_num
    · simp only [KellyGame.allocation, G, hsum]
      change (1 : ℝ) * (1 / 6) / (1 / 3) = 1 / 2; norm_num
  have hne : G.IsNashEquilibrium ![1 / 6, 1 / 6] := by
    rw [KellyGame.isNashEquilibrium_iff_kkt (by simp [G]) hU]
    have hprice : G.price ![1 / 6, 1 / 6] = 1 / 3 := by
      simp only [KellyGame.price, G, hsum, div_one]
    have hfoc : ∀ i : Fin 2,
        derivWithin (G.utility i) (Ici 0) (G.allocation ![1 / 6, 1 / 6] i) *
          (1 - G.allocation ![1 / 6, 1 / 6] i / G.capacity) = G.price ![1 / 6, 1 / 6] := by
      intro i
      rw [halloc, hprice]
      fin_cases i
      · change derivWithin (fun t => Real.log (1 + t)) (Ici 0) (1 / 2) * (1 - (1 / 2) / 1) = 1 / 3
        rw [hderiv (1 / 2) (by norm_num)]; norm_num
      · change derivWithin (fun t => Real.log (1 + t)) (Ici 0) (1 / 2) * (1 - (1 / 2) / 1) = 1 / 3
        rw [hderiv (1 / 2) (by norm_num)]; norm_num
    refine ⟨fun i => by fin_cases i <;> norm_num, fun i => ?_, fun i => (hfoc i).le,
      fun i _ => hfoc i⟩
    fin_cases i
    · change 0 < ∑ j ∈ Finset.univ.erase (0 : Fin 2), (![1 / 6, 1 / 6] : Fin 2 → ℝ) j
      have h1 : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
      rw [h1, Finset.sum_singleton]; norm_num
    · change 0 < ∑ j ∈ Finset.univ.erase (1 : Fin 2), (![1 / 6, 1 / 6] : Fin 2 → ℝ) j
      have h1 : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
      rw [h1, Finset.sum_singleton]; norm_num
  exact ⟨hce_uniq, hne_uniq, hne, halloc⟩

/-- Concrete tightness instances: `KellyGame.kellyTightGame 2` (3 users) gives exact Nash welfare
`5/6` against optimal `1`, and `KellyGame.kellyTightGame 10` (11 users) gives
`29/38 < 3/4 + 1/50`. -/
example :
    (KellyGame.kellyTightGame 2).IsNashEquilibrium (KellyGame.kellyTightBid 2) ∧
    (KellyGame.kellyTightGame 2).welfare
      ((KellyGame.kellyTightGame 2).allocation (KellyGame.kellyTightBid 2)) = 5 / 6 ∧
    (KellyGame.kellyTightGame 10).welfare
      ((KellyGame.kellyTightGame 10).allocation (KellyGame.kellyTightBid 10)) = 29 / 38 ∧
    (KellyGame.kellyTightGame 10).welfare
      ((KellyGame.kellyTightGame 10).allocation (KellyGame.kellyTightBid 10)) < 3 / 4 + 1 / 50 := by
  obtain ⟨_, _, hne2, _, _, hw2⟩ := KellyGame.kellyTightGame_spec (n := 2) le_rfl
  obtain ⟨_, _, _, _, _, hw10⟩ := KellyGame.kellyTightGame_spec (n := 10) (by decide)
  norm_num at hw2 hw10
  exact ⟨hne2, hw2, hw10, by linarith⟩

/-- Affine utilities with positive zero-intercept (`U_i(x) = b_i + a_i x`, `b_i ≥ 0`, `a_i > 0`):
the `3/4` theorem holds directly with strict margin. -/
example :
    let G : KellyGame (Fin 3) :=
      ⟨1, fun i x => (i.val + 1 : ℝ) + (KellyGame.kellyTightGame 2).utility i x⟩
    G.IsNashEquilibrium (KellyGame.kellyTightBid 2) ∧
    3 / 4 * G.welfare (Pi.single (M := fun _ => ℝ) (0 : Fin 3) 1) ≤
      G.welfare (G.allocation (KellyGame.kellyTightBid 2)) := by
  intro G
  obtain ⟨hU_lin, hU0_lin, hne_lin, hopt_lin, _, _⟩ := KellyGame.kellyTightGame_spec (n := 2) le_rfl
  have hU : ∀ i : Fin 3, IsAdmissibleUtility (G.utility i) := fun i => by
    have hi := hU_lin i
    refine ⟨?_, fun x hx y hy hxy => by dsimp only [G]; linarith [hi.strictMonoOn hx hy hxy],
      (differentiableOn_const _).add hi.differentiableOn⟩
    refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
    have hc := hi.concaveOn.2 hx hy ha hb hab
    simp only [G, smul_eq_mul] at hc ⊢
    nlinarith
  have hne : G.IsNashEquilibrium (KellyGame.kellyTightBid 2) := by
    refine ⟨hne_lin.1, fun i t ht => ?_⟩
    have hbr := hne_lin.2 i t ht
    simp only [KellyGame.payoff, KellyGame.allocation, G, KellyGame.kellyTightGame] at hbr ⊢
    linarith
  have hU0 : ∀ i : Fin 3, 0 ≤ G.utility i 0 := fun i => by
    have h0 := hU0_lin i
    dsimp only [G]
    rw [h0, add_zero]
    positivity
  exact ⟨hne, hne.three_fourths_welfare_le (by simp [G]) hU hU0 hopt_lin.1⟩

end ConcreteWitnesses

/-! ### SSVCG concrete witnesses (Corollary 21.12, Example 21.13, Proposition 21.14) -/

section SSVCGWitnesses

/-- `Real.sqrt` satisfies `HasInfiniteInitialSlope` (`U'(x) = 1 / (2 √x) → +∞` as `x → 0⁺`),
giving a non-vacuous witness to Proposition 21.14 (`PoA = 1` for SSVCG). -/
theorem hasInfiniteInitialSlope_sqrt : HasInfiniteInitialSlope Real.sqrt := by
  have hdiff : DifferentiableOn ℝ Real.sqrt (Ioi 0) :=
    fun x hx => (Real.hasDerivAt_sqrt (ne_of_gt hx)).differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), deriv Real.sqrt x = 1 / (2 * Real.sqrt x) := fun x hx =>
    (Real.hasDerivAt_sqrt (ne_of_gt hx)).deriv
  have hconc : ConcaveOn ℝ (Ici 0) Real.sqrt := by
    have hanti : StrictAntiOn (deriv Real.sqrt) (interior (Ici (0 : ℝ))) := by
      rw [interior_Ici]
      intro x hx y hy hxy
      rw [hderiv x hx, hderiv y hy]
      exact one_div_lt_one_div_of_lt (mul_pos two_pos (Real.sqrt_pos.mpr hx))
        (mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt hx.le hxy) two_pos)
    exact (hanti.strictConcaveOn_of_deriv (convex_Ici 0)
      Real.continuous_sqrt.continuousOn).concaveOn
  have hmono : StrictMonoOn Real.sqrt (Ici 0) :=
    fun _ hx _ _ hxy => Real.sqrt_lt_sqrt hx hxy
  have htend : Tendsto (deriv Real.sqrt) (𝓝[>] 0) atTop := by
    rw [tendsto_atTop]
    intro b
    set M := max b 0 + 1
    have hM : 0 < M := by positivity
    set δ := 1 / (4 * M ^ 2)
    have hδ : 0 < δ := by positivity
    filter_upwards [Ioc_mem_nhdsGT hδ] with x hx
    rw [hderiv x hx.1]
    have hsqrt_lt : Real.sqrt x ≤ 1 / (2 * M) := by
      have hsq : x ≤ (1 / (2 * M)) ^ 2 := by
        have : (1 / (2 * M)) ^ 2 = δ := by simp only [δ]; field_simp; ring
        rw [this]; exact hx.2
      exact (Real.sqrt_le_iff).mpr ⟨by positivity, hsq⟩
    have h2s : 2 * Real.sqrt x ≤ 1 / M := by
      have := mul_le_mul_of_nonneg_left hsqrt_lt (by norm_num : (0 : ℝ) ≤ 2)
      have hsimp : 2 * (1 / (2 * M)) = 1 / M := by field_simp
      linarith
    have h2s_pos : 0 < 2 * Real.sqrt x := mul_pos two_pos (Real.sqrt_pos.mpr hx.1)
    have hinv : M ≤ 1 / (2 * Real.sqrt x) := by
      rw [le_div_iff₀ h2s_pos]
      have := (le_div_iff₀ hM).mp h2s
      linarith
    linarith [le_max_left b 0]
  exact ⟨hconc, Real.continuous_sqrt.continuousOn, hmono, hdiff, htend⟩

/-- Applying Proposition 21.14 to one or two users with `U_i(x) = √x` under the logarithmic SSVCG
mechanism: every Nash equilibrium induces a socially optimal allocation (and nonnegative VCG
payments). -/
example (θ : Fin 2 → ℝ)
    (hne : (⟨1, fun t x => t * Real.log (1 + x)⟩ : SSVCGMechanism (Fin 2)).IsNashEquilibrium
      (fun _ => Real.sqrt) θ) :
    (⟨1, fun _ => Real.sqrt⟩ : KellyGame (Fin 2)).IsSocialOptimum
      ((⟨1, fun t x => t * Real.log (1 + x)⟩ : SSVCGMechanism (Fin 2)).allocation θ) ∧
    ∀ i, 0 ≤ (⟨1, fun t x => t * Real.log (1 + x)⟩ : SSVCGMechanism (Fin 2)).payment θ i := by
  have hfam := isSSVCGSurrogateFamily_mul_log_one_add
  exact ⟨SSVCGMechanism.isSocialOptimum_of_isNashEquilibrium_of_infiniteSlope
      zero_lt_one hfam (fun _ => hasInfiniteInitialSlope_sqrt) hne,
    fun i => SSVCGMechanism.payment_nonneg zero_le_one hfam hne.1 i⟩

example (θ : Fin 1 → ℝ)
    (hne : (⟨1, fun t x => t * Real.log (1 + x)⟩ : SSVCGMechanism (Fin 1)).IsNashEquilibrium
      (fun _ => Real.sqrt) θ) :
    (⟨1, fun _ => Real.sqrt⟩ : KellyGame (Fin 1)).IsSocialOptimum
      ((⟨1, fun t x => t * Real.log (1 + x)⟩ : SSVCGMechanism (Fin 1)).allocation θ) :=
  SSVCGMechanism.isSocialOptimum_of_isNashEquilibrium_of_infiniteSlope
    zero_lt_one isSSVCGSurrogateFamily_mul_log_one_add (fun _ => hasInfiniteInitialSlope_sqrt) hne

/-- Corollary 21.12 and Example 21.13 both hold for the logarithmic SSVCG mechanism on two
identical `log (1 + x)` users: an efficient Nash equilibrium exists, and an inefficient bluff
equilibrium also exists. -/
example :
    let M : SSVCGMechanism (Fin 2) := ⟨1, fun t x => t * Real.log (1 + x)⟩
    let U : Fin 2 → ℝ → ℝ := fun _ x => Real.log (1 + x)
    (∃ θ, M.IsNashEquilibrium U θ ∧ (⟨1, U⟩ : KellyGame (Fin 2)).IsSocialOptimum (M.allocation θ)) ∧
    (∃ θ, M.IsNashEquilibrium U θ ∧
      (⟨1, U⟩ : KellyGame (Fin 2)).welfare (M.allocation θ) <
        (⟨1, U⟩ : KellyGame (Fin 2)).welfare ![1 / 2, 1 / 2]) := by
  intro M U
  obtain ⟨hne_b, _, hlt_b⟩ := exists_bluff_isNashEquilibrium
  exact ⟨SSVCGMechanism.exists_efficient_isNashEquilibrium (M := M) zero_lt_one
      isSSVCGSurrogateFamily_mul_log_one_add (fun _ => isAdmissibleUtility_log_one_add.1),
    ⟨![3, 1 / 4], hne_b, hlt_b⟩⟩

end SSVCGWitnesses

end CslibFrontierTests.KellyResourceAllocationNRTV
