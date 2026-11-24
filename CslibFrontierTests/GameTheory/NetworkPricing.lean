/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Congestion.Pricing.Oligopoly
import CslibFrontier.GameTheory.Congestion.Pricing.ParallelSerial
import CslibFrontier.GameTheory.Congestion.Pricing.PricedWardrop
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/-!
# Network pricing, monopoly efficiency, and oligopoly price-of-anarchy tests

Concrete instances and boundary counterexamples for NRTV Chapter 22 (`§22.2–22.3`,
[OzdaglarSrikant2007]; [AcemogluOzdaglar2007MOR]; [AcemogluOzdaglar2007JSAC]):

1. **NRTV Example 22.1** (`l₀(x) = x² / 3`, `l₁(x) = 2 x / 3`, `d = 1`, `R = 1`):
   social optimum `![2 / 3, 1 / 3]`, Pigovian tolls `![8 / 27, 2 / 9]`, monopoly equilibrium
   `p = ![23 / 27, 7 / 9]` with zero consumer surplus and `100%` efficiency, and non-optimality of
   unpriced Wardrop routing.
2. **Acemoglu–Ozdaglar (2007 MOR) Example 4.2**: 3-link, 2-provider network violating
   `ZeroLatencySingleton` where `![2 / 3, 1 / 3, 0]` is a pure-strategy oligopoly equilibrium with
   `p 2 * x 2 = 0` despite positive provider profit `4 / 9`, while still satisfying the `5 / 6`
   efficiency bound (`8 / 9 ≥ 5 / 6`).
3. **NRTV Example 22.2 (`5 / 6` tightness)**: exact `5 / 6` equilibrium-to-optimum surplus ratio on
   two links (`n = 0`).
4. **Elastic-traffic `2 / 3` bound**: concrete quadratic utility `u(X) = X - X² / 2`
   (`3 / 4 ≥ 2 / 3`) and asymptotic `2 / 3 + 1 / 100` tightness witness.
5. **Parallel-serial `1 / 2` bound & boundary counterexamples**: weak OE coordination failure
   (after `[AcemogluOzdaglar2007JSAC]` Example 2), strict OE partial-demand failure
   (`[AcemogluOzdaglar2007JSAC]` Example 3 with `8` serial links, achieving `32 / 81 < 1 / 2`), and
   `1 / 2 + 1 / 100` tightness witness for full-demand strict OE (`Theorem 22.5`).
-/

-- This regression module intentionally exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.NetworkPricing

open Cslib.GameTheory

/-! ### 1. NRTV Example 22.1: social optimum, Pigovian tolls, and monopoly efficiency -/

/-- Latency functions `x² / 3` and `2 x / 3` of NRTV Example 22.1. -/
noncomputable def twoLinkQuadLatency (i : Fin 2) (x : ℝ) : ℝ :=
  if i = 0 then x ^ 2 / 3 else 2 * x / 3

/-- Latency derivatives `2 x / 3` and `2 / 3` of `twoLinkQuadLatency`. -/
noncomputable def twoLinkQuadLatencyDeriv (i : Fin 2) (x : ℝ) : ℝ :=
  if i = 0 then 2 * x / 3 else 2 / 3

theorem ex22_1_smoothConvex :
    SmoothConvexLatencies twoLinkQuadLatency twoLinkQuadLatencyDeriv where
  zero_at_zero i := by
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl <;> simp [twoLinkQuadLatency]
  monotoneOn i := by
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
    · intro a ha b _ hab
      simp only [twoLinkQuadLatency, ↓reduceIte]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ ha hab 2) (by positivity)
    · intro a _ b _ hab
      simp only [twoLinkQuadLatency, one_ne_zero, ↓reduceIte]
      linarith
  convexOn i := by
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
    · refine ⟨convex_Ici 0, fun a _ b _ w₁ w₂ hw₁ hw₂ hw => ?_⟩
      simp only [twoLinkQuadLatency, ↓reduceIte, smul_eq_mul]
      have hdiff : w₁ * (a ^ 2 / 3) + w₂ * (b ^ 2 / 3) - (w₁ * a + w₂ * b) ^ 2 / 3 =
          w₁ * w₂ * (a - b) ^ 2 / 3 := by
        rw [show w₁ = 1 - w₂ by linarith]
        ring
      have hnn : 0 ≤ w₁ * w₂ * (a - b) ^ 2 / 3 := by positivity
      linarith
    · refine ⟨convex_Ici 0, fun a _ b _ w₁ w₂ _ _ _ => ?_⟩
      simp only [twoLinkQuadLatency, one_ne_zero, ↓reduceIte, smul_eq_mul]
      linarith
  hasDerivAt i x _ := by
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
    · simp only [twoLinkQuadLatencyDeriv, ↓reduceIte]
      have hfun : twoLinkQuadLatency 0 = fun y => (y * y) / 3 := by
        ext y; simp only [twoLinkQuadLatency, ↓reduceIte]; ring
      rw [hfun]
      convert (((hasDerivAt_id' x).mul (hasDerivAt_id' x)).div_const 3) using 1
      ring
    · simp only [twoLinkQuadLatencyDeriv, one_ne_zero, ↓reduceIte]
      have hfun : twoLinkQuadLatency 1 = fun y => (2 * y) / 3 := by
        ext y; simp [twoLinkQuadLatency, one_ne_zero]
      rw [hfun]
      convert (((hasDerivAt_id' x).const_mul 2).div_const 3) using 1
      ring

theorem ex22_1_isSocialOptimum :
    IsSocialOptimum 1 1 twoLinkQuadLatency ![2 / 3, 1 / 3] := by
  rw [ex22_1_smoothConvex.isSocialOptimum_iff_kkt]
  refine ⟨⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]; norm_num⟩,
    5 / 9, by norm_num, by simp [Fin.sum_univ_two]; norm_num,
    fun i => ?_, fun i _ => ?_⟩
  · fin_cases i <;> simp [twoLinkQuadLatency, twoLinkQuadLatencyDeriv] <;> norm_num
  · fin_cases i <;> simp [twoLinkQuadLatency, twoLinkQuadLatencyDeriv] <;> norm_num

theorem ex22_1_pigovian_wardrop :
    IsPricedWardrop 1 1 twoLinkQuadLatency
      (pigovianPrice twoLinkQuadLatencyDeriv ![2 / 3, 1 / 3]) ![2 / 3, 1 / 3] ∧
    (pricedParallelCongestionGame 1 twoLinkQuadLatency
      (pigovianPrice twoLinkQuadLatencyDeriv ![2 / 3, 1 / 3])).IsWardrop ![2 / 3, 1 / 3] := by
  have hsum : ∑ i : Fin 2, (![2 / 3, 1 / 3] : Fin 2 → ℝ) i = 1 := by
    simp [Fin.sum_univ_two]; norm_num
  have hw := ex22_1_smoothConvex.isPricedWardrop_pigovianPrice_of_sum_eq ex22_1_isSocialOptimum hsum
  exact ⟨hw, (isPricedWardrop_iff_isWardrop_of_sum_eq hsum hw.2.2.1).mp hw⟩

theorem ex22_1_monopoly_properties :
    (∃ p : Fin 2 → ℝ, IsMonopolyEquilibrium 1 1 twoLinkQuadLatency p ![2 / 3, 1 / 3]) ∧
    (∀ p : Fin 2 → ℝ, IsMonopolyEquilibrium 1 1 twoLinkQuadLatency p ![2 / 3, 1 / 3] →
      p 0 = 23 / 27 ∧ p 1 = 7 / 9 ∧
      consumerSurplus 1 twoLinkQuadLatency p ![2 / 3, 1 / 3] = 0 ∧
      monopolyProfit p ![2 / 3, 1 / 3] = 67 / 81) := by
  have hex := (exists_isMonopolyEquilibrium_iff_isSocialOptimum (d := 1) (R := 1) zero_le_one
    ex22_1_smoothConvex.zero_at_zero).mpr ex22_1_isSocialOptimum
  have hlat0 : ∀ k, 0 ≤ twoLinkQuadLatency k 0 := fun k => (ex22_1_smoothConvex.zero_at_zero k).ge
  refine ⟨hex, fun p hme => ?_⟩
  have hp0 := hme.price_eq_sub_latency hlat0 (i := 0) (by simp)
  have hp1 := hme.price_eq_sub_latency hlat0 (i := 1) (by simp)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, twoLinkQuadLatency, ↓reduceIte,
    one_ne_zero] at hp0 hp1
  have hcs := hme.consumerSurplus_eq_zero hlat0
  have hprof := hme.monopolyProfit_eq_socialSurplus hlat0
  have hsurp : socialSurplus 1 twoLinkQuadLatency ![2 / 3, 1 / 3] = 67 / 81 := by
    simp [socialSurplus, Fin.sum_univ_two, twoLinkQuadLatency]
    norm_num
  exact ⟨by rw [hp0]; norm_num, by rw [hp1]; norm_num, hcs, hprof.trans hsurp⟩

theorem ex22_1_unpriced_not_optimal :
    ¬ IsPricedWardrop 1 1 twoLinkQuadLatency 0 ![2 / 3, 1 / 3] := by
  intro hw
  have h := hw.2.1 1 0 (by simp)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, add_zero, twoLinkQuadLatency,
    one_ne_zero, ↓reduceIte] at h
  norm_num at h

/-! ### 2. Acemoglu–Ozdaglar (2007 MOR) Example 4.2: `ZeroLatencySingleton` boundary -/

/-- Three-link latencies `(0, x, x)` of [AcemogluOzdaglar2007MOR] Example 4.2. -/
def multiOwnerLatency (i : Fin 3) (x : ℝ) : ℝ :=
  if i = 0 then 0 else x

/-- Latency derivatives `(0, 1, 1)` of `multiOwnerLatency`. -/
def multiOwnerLatencyDeriv (i : Fin 3) (_ : ℝ) : ℝ :=
  if i = 0 then 0 else 1

theorem ex4_2_smoothConvex : SmoothConvexLatencies multiOwnerLatency multiOwnerLatencyDeriv where
  zero_at_zero i := by simp [multiOwnerLatency]
  monotoneOn i := by
    by_cases hi : i = 0
    · subst hi; intro _ _ _ _ _; simp [multiOwnerLatency]
    · intro _ _ _ _ hab; simp [multiOwnerLatency, hi, hab]
  convexOn i := by
    by_cases hi : i = 0
    · subst hi; exact ⟨convex_Ici 0, fun _ _ _ _ _ _ _ _ _ => by simp [multiOwnerLatency]⟩
    · refine ⟨convex_Ici 0, fun a _ b _ w₁ w₂ _ _ _ => ?_⟩
      simp only [multiOwnerLatency, hi, ↓reduceIte, smul_eq_mul]
      exact le_rfl
  hasDerivAt i x _ := by
    by_cases hi : i = 0
    · subst hi
      simp only [multiOwnerLatencyDeriv, ↓reduceIte]
      have hfun : multiOwnerLatency 0 = fun _ => 0 := by ext u; simp [multiOwnerLatency]
      rw [hfun]
      exact hasDerivAt_const x 0
    · simp only [multiOwnerLatencyDeriv, hi, ↓reduceIte]
      have hfun : multiOwnerLatency i = fun u => u := by ext u; simp [multiOwnerLatency, hi]
      rw [hfun]
      exact hasDerivAt_id' x

theorem ex4_2_not_zeroLatencySingleton :
    ¬ ZeroLatencySingleton multiOwnerLatency (![0, 1, 0] : Fin 3 → Fin 2) ![2 / 3, 1 / 3, 0] := by
  intro hz
  have h := hz (i := 0) (j := 2) (by simp) (by simp [multiOwnerLatency]) rfl
  exact absurd h.symm (by decide)

theorem ex4_2_isOligopolyEquilibrium :
    IsOligopolyEquilibrium 1 1 multiOwnerLatency (![0, 1, 0] : Fin 3 → Fin 2)
      ![2 / 3, 1 / 3, 1] ![2 / 3, 1 / 3, 0] := by
  refine ⟨fun i => by fin_cases i <;> norm_num, ?_, fun s p' x' hp'0 hp'other hw' => ?_⟩
  · refine ⟨⟨fun i => by fin_cases i <;> norm_num,
      by simp [Fin.sum_univ_three]; norm_num⟩,
      fun i j hi => ?_, fun i hi => ?_, fun _ => by simp [Fin.sum_univ_three]; norm_num⟩
    · fin_cases i <;> fin_cases j <;> simp [multiOwnerLatency] at hi ⊢ <;> norm_num
    · fin_cases i <;> simp [multiOwnerLatency] at hi ⊢ <;> norm_num
  · rcases Fin.exists_fin_two.mp ⟨s, rfl⟩ with rfl | rfl
    · -- Provider 0 owns links 0 and 2 (equilibrium profit 4 / 9), while p' 1 = 1 / 3:
      have hp'1 : p' 1 = 1 / 3 := hp'other 1 (by decide)
      have hflt0 : (Finset.univ.filter fun i : Fin 3 => (![0, 1, 0] : Fin 3 → Fin 2) i = 0) =
          {0, 2} := by decide
      have hprof_eq : ∀ q xq : Fin 3 → ℝ,
          providerProfit (![0, 1, 0] : Fin 3 → Fin 2) 0 q xq = q 0 * xq 0 + q 2 * xq 2 := by
        intro q xq
        simp only [providerProfit, hflt0]
        rw [Finset.sum_pair (by decide)]
      rw [hprof_eq, hprof_eq]
      have hrhs : (![2 / 3, 1 / 3, 1] : Fin 3 → ℝ) 0 * (![2 / 3, 1 / 3, 0] : Fin 3 → ℝ) 0 +
          (![2 / 3, 1 / 3, 1] : Fin 3 → ℝ) 2 * (![2 / 3, 1 / 3, 0] : Fin 3 → ℝ) 2 = 4 / 9 := by
        simp; norm_num
      rw [hrhs]
      let y : ℝ := x' 0 + x' 2
      have hsum3 : x' 0 + x' 1 + x' 2 ≤ 1 := by
        simpa [Fin.sum_univ_three, add_assoc] using hw'.1.2
      have hx'1_le : x' 1 ≤ 1 - y := by simp only [y]; linarith
      have hb0 : p' 0 * x' 0 ≤ (4 / 3 - y) * x' 0 := by
        rcases (hw'.1.1 0).eq_or_lt with h0 | hpos0
        · rw [← h0, mul_zero, mul_zero]
        · have heff := hw'.2.1 0 1 hpos0
          simp only [multiOwnerLatency, ↓reduceIte, one_ne_zero, zero_add, hp'1] at heff
          exact mul_le_mul_of_nonneg_right (by linarith) hpos0.le
      have hb2 : p' 2 * x' 2 ≤ (4 / 3 - y) * x' 2 := by
        rcases (hw'.1.1 2).eq_or_lt with h2 | hpos2
        · rw [← h2, mul_zero, mul_zero]
        · have heff := hw'.2.1 2 1 hpos2
          have h20 : (2 : Fin 3) ≠ 0 := by decide
          have h10 : (1 : Fin 3) ≠ 0 := by decide
          simp only [multiOwnerLatency, h20, h10, ↓reduceIte, hp'1] at heff
          exact mul_le_mul_of_nonneg_right (by linarith) hpos2.le
      have hquad : (4 / 3 - y) * y ≤ 4 / 9 := by
        have hid : 4 / 9 - (4 / 3 - y) * y = (y - 2 / 3) ^ 2 := by ring
        nlinarith [sq_nonneg (y - 2 / 3)]
      have htot : p' 0 * x' 0 + p' 2 * x' 2 ≤ (4 / 3 - y) * y := by
        simp only [y]; linarith
      linarith
    · -- Provider 1 owns link 1 (equilibrium profit 1 / 9), while p' 0 = 2 / 3:
      have hp'0_eq : p' 0 = 2 / 3 := hp'other 0 (by decide)
      have hflt1 : (Finset.univ.filter fun i : Fin 3 => (![0, 1, 0] : Fin 3 → Fin 2) i = 1) =
          {1} := by decide
      have hprof_eq : ∀ q xq : Fin 3 → ℝ,
          providerProfit (![0, 1, 0] : Fin 3 → Fin 2) 1 q xq = q 1 * xq 1 := by
        intro q xq
        simp only [providerProfit, hflt1, Finset.sum_singleton]
      rw [hprof_eq, hprof_eq]
      have hrhs : (![2 / 3, 1 / 3, 1] : Fin 3 → ℝ) 1 * (![2 / 3, 1 / 3, 0] : Fin 3 → ℝ) 1 =
          1 / 9 := by
        simp; norm_num
      rw [hrhs]
      rcases (hw'.1.1 1).eq_or_lt with h1 | hpos1
      · rw [← h1, mul_zero]; norm_num
      · have heff := hw'.2.1 1 0 hpos1
        have h10 : (1 : Fin 3) ≠ 0 := by decide
        simp only [multiOwnerLatency, h10, ↓reduceIte, hp'0_eq, zero_add] at heff
        have hmul : p' 1 * x' 1 ≤ (2 / 3 - x' 1) * x' 1 :=
          mul_le_mul_of_nonneg_right (by linarith) hpos1.le
        nlinarith [sq_nonneg (x' 1 - 1 / 3)]

/-- Even though `ZeroLatencySingleton` fails on Example 4.2 (and link `2` has zero flow), the
equilibrium surplus `8 / 9` still satisfies `5 / 6 ≤ 8 / 9`. -/
theorem ex4_2_surplus_ratio :
    socialSurplus 1 multiOwnerLatency ![2 / 3, 1 / 3, 0] = 8 / 9 ∧
    (5 : ℝ) / 6 ≤ socialSurplus 1 multiOwnerLatency ![2 / 3, 1 / 3, 0] := by
  simp [socialSurplus, Fin.sum_univ_three, multiOwnerLatency]
  norm_num

/-! ### 3. NRTV Example 22.2: exact `5 / 6` efficiency on two links (`n = 0`) -/

theorem ex22_2_two_links_exact_five_sixths :
    socialSurplus 1 (oligopolyTightnessLatency 0) (oligopolyTightnessFlow 0) /
      socialSurplus 1 (oligopolyTightnessLatency 0) (oligopolyTightnessOptFlow 0) = 5 / 6 ∧
    (5 : ℝ) / 6 ≤
      socialSurplus 1 (oligopolyTightnessLatency 0) (oligopolyTightnessFlow 0) /
        socialSurplus 1 (oligopolyTightnessLatency 0) (oligopolyTightnessOptFlow 0) := by
  have heq := oligopolyTightness_surplus_eq_five_sixths 0
  have hopt_eq : socialSurplus 1 (oligopolyTightnessLatency 0) (oligopolyTightnessOptFlow 0) = 1 :=
    (oligopolyTightness_isSocialOptimum 0).2
  have hge := oligopoly_efficiency_ge_five_sixths (oligopolyTightness_smoothConvex 0)
    (oligopolyTightness_isOligopolyEquilibrium 0)
    (zeroLatencySingleton_of_injective Function.injective_id (oligopolyTightnessFlow 0))
    (oligopolyTightness_isSocialOptimum 0).1 (by rw [hopt_eq]; positivity)
  refine ⟨?_, hge⟩
  rw [hopt_eq, div_one]
  rw [hopt_eq, mul_one] at heq
  exact heq

/-! ### 4. Elastic-traffic `2 / 3` bound & quadratic utility witness -/

/-- Quadratic aggregate utility `x - x² / 2` with linear marginal utility. -/
noncomputable def quadU (x : ℝ) : ℝ := x - x ^ 2 / 2

/-- Marginal utility `1 - x` of `quadU`. -/
def quadUDeriv (x : ℝ) : ℝ := 1 - x

/-- Constant second derivative `-1` of `quadU`. -/
def quadUSecondDeriv (_ : ℝ) : ℝ := -1

theorem quadU_smoothConcave :
    SmoothConcaveMarginalUtility quadU quadUDeriv quadUSecondDeriv where
  zero_at_zero := by simp [quadU]
  concaveOn := by
    refine ⟨convex_Ici 0, fun a _ b _ w₁ w₂ hw₁ hw₂ hw => ?_⟩
    simp only [quadU, smul_eq_mul]
    have hdiff : (w₁ * a + w₂ * b - (w₁ * a + w₂ * b) ^ 2 / 2) -
        (w₁ * (a - a ^ 2 / 2) + w₂ * (b - b ^ 2 / 2)) =
        w₁ * w₂ * (a - b) ^ 2 / 2 := by
      rw [show w₁ = 1 - w₂ by linarith]
      ring
    have hnn : 0 ≤ w₁ * w₂ * (a - b) ^ 2 / 2 := by positivity
    linarith
  concaveOn_deriv := by
    refine ⟨convex_Ici 0, fun a _ b _ w₁ w₂ _ _ hw => ?_⟩
    simp only [quadUDeriv, smul_eq_mul]
    rw [show w₁ = 1 - w₂ by linarith]
    linarith
  hasDerivAt x _ := by
    simp only [quadUDeriv]
    have hfun : quadU = fun y => y - (y * y) / 2 := by ext y; simp only [quadU]; ring
    rw [hfun]
    convert (hasDerivAt_id' x).sub (((hasDerivAt_id' x).mul (hasDerivAt_id' x)).div_const 2)
      using 1
    ring
  hasSecondDerivAt x _ := by
    simp only [quadUSecondDeriv]
    have hfun : quadUDeriv = fun y => 1 - y := rfl
    rw [hfun]
    convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x) using 1
    ring

theorem quadU_singleLink_equilibrium_and_bound :
    IsElasticOligopolyEquilibrium quadUDeriv elasticZeroLatency
      (fun _ : Fin 1 => 1 / 2) (fun _ : Fin 1 => 1 / 2) ∧
    IsElasticSocialOptimum quadU elasticZeroLatency (fun _ : Fin 1 => 1) ∧
    (2 : ℝ) / 3 ≤
      elasticSocialSurplus quadU elasticZeroLatency (fun _ : Fin 1 => 1 / 2) /
        elasticSocialSurplus quadU elasticZeroLatency (fun _ : Fin 1 => 1) := by
  have hoe : IsElasticOligopolyEquilibrium quadUDeriv elasticZeroLatency
      (fun _ : Fin 1 => 1 / 2) (fun _ : Fin 1 => 1 / 2) := by
    refine ⟨fun _ => by norm_num,
      ⟨fun _ => by norm_num,
        fun _ _ => by simp [elasticZeroLatency, quadUDeriv]; norm_num,
        fun _ => by simp [elasticZeroLatency, quadUDeriv]; norm_num⟩,
      fun i p' x' _ hw' => ?_⟩
    have hi0 : i = 0 := Subsingleton.elim i 0
    subst hi0
    rcases (hw'.1 0).eq_or_lt with hz | hpos
    · simp only [← hz, mul_zero]; norm_num
    · have heff := hw'.2.1 0 hpos
      simp only [elasticZeroLatency, zero_add, Function.update_self, Fin.sum_univ_one,
        quadUDeriv] at heff
      rw [heff]
      have hid : (1 / 2 : ℝ) * (1 / 2) - (1 - x' 0) * x' 0 = (x' 0 - 1 / 2) ^ 2 := by ring
      nlinarith [sq_nonneg (x' 0 - 1 / 2)]
  have hopt : IsElasticSocialOptimum quadU elasticZeroLatency (fun _ : Fin 1 => 1) :=
    isElasticSocialOptimum_of_kkt quadU_smoothConcave elasticZeroLatency_smoothConvex
      (fun _ => zero_le_one)
      (fun _ => by simp [elasticZeroLatency, quadUDeriv])
      (fun _ _ => by simp [elasticZeroLatency, quadUDeriv])
  have hopt_pos : 0 < elasticSocialSurplus quadU elasticZeroLatency (fun _ : Fin 1 => 1) := by
    simp [elasticSocialSurplus, elasticZeroLatency, quadU]
    norm_num
  exact ⟨hoe, hopt,
    elastic_oligopoly_efficiency_ge_two_thirds quadU_smoothConcave elasticZeroLatency_smoothConvex
      hoe hopt hopt_pos⟩

theorem elastic_tightness_witness_hundredth :
    ∃ n : ℕ,
      IsElasticOligopolyEquilibrium (elasticTightnessUtilityDeriv n) elasticZeroLatency
        (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1) ∧
      IsElasticSocialOptimum (elasticTightnessUtility n) elasticZeroLatency
        (fun _ : Fin 1 => 2) ∧
      elasticSocialSurplus (elasticTightnessUtility n) elasticZeroLatency (fun _ : Fin 1 => 1) <
        (2 / 3 + 1 / 100) *
          elasticSocialSurplus (elasticTightnessUtility n) elasticZeroLatency
            (fun _ : Fin 1 => 2) := by
  obtain ⟨n, hn⟩ := elasticTightness_surplus_lt_two_thirds_add (δ := 1 / 100) (by norm_num)
  exact ⟨n, elasticTightness_isElasticOligopolyEquilibrium n,
    elasticTightness_isElasticSocialOptimum n, hn⟩

/-! ### 5. Parallel-serial `1 / 2` bound & boundary counterexamples (Examples 2 & 3) -/

/-- Zero serial latency on one path with two serial links. -/
def zeroSerialLatency (_ : Fin 1) (_ : Fin 2) (_ : ℝ) : ℝ := 0

/-- Coordination-failure weak OE (after `[AcemogluOzdaglar2007JSAC]` Example 2, p. 1184): two
serial zero-latency providers on one path charging `![2, 2]` sustain `x = 0` as a weak
`IsSerialOligopolyEquilibrium` with `0` social surplus against optimal surplus `1`, showing
strictness is required in Lemma 1 and Theorem 22.5. -/
theorem serial_weak_coordination_failure :
    IsSerialOligopolyEquilibrium 1 1 zeroSerialLatency (fun _ => ![2, 2]) 0 ∧
    ¬ IsStrictSerialOligopolyEquilibrium 1 1 zeroSerialLatency (fun _ => ![2, 2]) 0 ∧
    socialSurplus 1 (serialPathLatency zeroSerialLatency) 0 = 0 ∧
    socialSurplus 1 (serialPathLatency zeroSerialLatency) (fun _ => 1) = 1 := by
  have hweak : IsSerialOligopolyEquilibrium 1 1 zeroSerialLatency (fun _ => ![2, 2]) 0 := by
    refine ⟨fun _ j => by fin_cases j <;> norm_num,
      ⟨⟨fun _ => le_rfl, by simp⟩,
        fun _ _ h => False.elim (lt_irrefl 0 h),
        fun _ h => False.elim (lt_irrefl 0 h),
        fun ⟨i, hi⟩ => ?_⟩,
      fun i j p' x' hp' hw' => ?_⟩
    · simp only [serialPathLatency, zeroSerialLatency, Finset.sum_const_zero, serialPathPrice,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zero_add] at hi
      linarith
    · have hi0 : i = 0 := Subsingleton.elim i 0
      subst hi0
      have hx'0 : x' 0 = 0 := by
        rcases (hw'.1.1 0).eq_or_lt with hz | hpos
        · exact hz.symm
        · exfalso
          have hle := hw'.2.2.1 0 hpos
          simp only [serialPathLatency, zeroSerialLatency, Finset.sum_const_zero, zero_add,
            serialPathPrice, Fin.sum_univ_two, updateSerialPrice] at hle
          rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with rfl | rfl
          · simp at hle; linarith
          · simp at hle; linarith
      simp [hx'0]
  have hnot_strict :
      ¬ IsStrictSerialOligopolyEquilibrium 1 1 zeroSerialLatency (fun _ => ![2, 2]) 0 := by
    intro hst
    have hw0 : IsPricedWardrop 1 1 (serialPathLatency zeroSerialLatency)
        (serialPathPrice (updateSerialPrice (fun _ : Fin 1 => (![2, 2] : Fin 2 → ℝ)) 0 0 0)) 0 := by
      refine ⟨⟨fun _ => le_rfl, by simp⟩,
        fun _ _ h => False.elim (lt_irrefl 0 h),
        fun _ h => False.elim (lt_irrefl 0 h),
        fun ⟨i, hi⟩ => ?_⟩
      have hi0 : i = 0 := Subsingleton.elim i 0
      subst hi0
      simp [serialPathLatency, zeroSerialLatency, serialPathPrice, Fin.sum_univ_two,
        updateSerialPrice] at hi
    have hlt := hst.2.2 0 0 0 0 le_rfl (by norm_num) hw0
    simp at hlt
  exact ⟨hweak, hnot_strict, by simp [socialSurplus],
    by simp [socialSurplus, serialPathLatency, zeroSerialLatency]⟩

/-- Per-link serial latency `x / 8` across `8` serial links
([AcemogluOzdaglar2007JSAC] Example 3). -/
noncomputable def ex3SerialLatency (_ : Fin 1) (_ : Fin 8) (x : ℝ) : ℝ := x / 8

/-- Derivative `1 / 8` of `ex3SerialLatency`. -/
noncomputable def ex3SerialLatencyDeriv (_ : Fin 1) (_ : Fin 8) (_ : ℝ) : ℝ := 1 / 8

theorem ex3Serial_smoothConvex :
    SmoothConvexSerialLatencies ex3SerialLatency ex3SerialLatencyDeriv := fun i =>
  { zero_at_zero := fun _ => by simp [ex3SerialLatency]
    monotoneOn := fun _ _ _ _ _ hab => div_le_div_of_nonneg_right hab (by positivity)
    convexOn := fun _ => ⟨convex_Ici 0, fun _ _ _ _ _ _ _ _ _ => by
      simp only [ex3SerialLatency, smul_eq_mul]; linarith⟩
    hasDerivAt := fun j x _ => by
      simp only [ex3SerialLatencyDeriv]
      have hfun : ex3SerialLatency i j = fun y => y * (1 / 8) := by
        ext y; simp only [ex3SerialLatency]; ring
      rw [hfun]
      convert (hasDerivAt_id' x).mul_const (1 / 8) using 1
      ring }

/-- `[AcemogluOzdaglar2007JSAC]` Example 3 (`n = 8`, p. 1185): even at a **strict** serial OE
`(p = 1 / 9, x = 1 / 9)`, partial demand (`∑ x = 1 / 9 < 1`) yields surplus `8 / 81` against
optimal surplus `1 / 4` (`32 / 81 < 1 / 2`), proving the full-demand hypothesis `∑ i, x i = d` in
Theorem 22.5 (`IsStrongSerialOligopolyEquilibrium`) is indispensable. -/
theorem ex3Serial_strict_partial_demand_below_half :
    IsStrictSerialOligopolyEquilibrium 1 1 ex3SerialLatency
      (fun _ _ => 1 / 9) (fun _ => 1 / 9) ∧
    IsSocialOptimum 1 1 (serialPathLatency ex3SerialLatency) (fun _ => 1 / 2) ∧
    2 * socialSurplus 1 (serialPathLatency ex3SerialLatency) (fun _ => 1 / 9) <
      socialSurplus 1 (serialPathLatency ex3SerialLatency) (fun _ => 1 / 2) := by
  have hpath_eq : ∀ i x, serialPathLatency ex3SerialLatency i x = x := fun _ x => by
    simp [serialPathLatency, ex3SerialLatency]
    ring
  let p0 : Fin 1 → Fin 8 → ℝ := fun _ _ => 1 / 9
  have hstrict : IsStrictSerialOligopolyEquilibrium 1 1 ex3SerialLatency p0 (fun _ => 1 / 9) := by
    refine ⟨fun _ _ => by norm_num,
      ⟨⟨fun _ => by norm_num, by simp; norm_num⟩,
        fun a b _ => by rw [Subsingleton.elim a b],
        fun _ _ => by simp [hpath_eq, serialPathPrice, p0]; norm_num,
        fun ⟨i, hi⟩ => by simp [hpath_eq, serialPathPrice, p0] at hi; norm_num at hi⟩,
      fun i j p' x' hp' hne hw' => ?_⟩
    have hi0 : i = 0 := Subsingleton.elim i 0
    subst hi0
    have hprice_upd : serialPathPrice (updateSerialPrice p0 0 j p') 0 = 7 / 9 + p' := by
      simp only [serialPathPrice]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      have hrest : ∑ k ∈ Finset.univ.erase j, updateSerialPrice p0 0 j p' 0 k = 7 / 9 := by
        have hcongr : ∑ k ∈ Finset.univ.erase j, updateSerialPrice p0 0 j p' 0 k =
            ∑ _k ∈ Finset.univ.erase j, (1 / 9 : ℝ) :=
          Finset.sum_congr rfl fun k hk => by
            simp [updateSerialPrice, p0, (Finset.mem_erase.mp hk).1]
        rw [hcongr, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin]
        norm_num
      rw [hrest]
      simp [updateSerialPrice]
      ring
    rcases (hw'.1.1 0).eq_or_lt with hz | hpos
    · rw [← hz, mul_zero]; simp only [p0]; norm_num
    · have hle1 := hw'.2.2.1 0 hpos
      rw [hpath_eq, hprice_upd] at hle1
      have hsum_eq : x' 0 + p' = 2 / 9 := by
        refine le_antisymm (by linarith) ?_
        by_contra hlt
        have hlt_R : serialPathLatency ex3SerialLatency 0 (x' 0) +
            serialPathPrice (updateSerialPrice p0 0 j p') 0 < 1 := by
          rw [hpath_eq, hprice_upd]; linarith
        have hfull := hw'.2.2.2 ⟨0, hlt_R⟩
        simp only [Fin.sum_univ_one] at hfull
        linarith
      have hx'_eq : x' 0 = 2 / 9 - p' := by linarith
      rw [hx'_eq]
      simp only [p0] at hne ⊢
      have hpos_sq : 0 < (p' - 1 / 9) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
      nlinarith
  have hopt : IsSocialOptimum 1 1 (serialPathLatency ex3SerialLatency) (fun _ => 1 / 2) := by
    refine ⟨⟨fun _ => by norm_num, by simp; norm_num⟩, fun y hy => ?_⟩
    simp only [socialSurplus, Fin.sum_univ_one, hpath_eq]
    have hid : (1 - (1 / 2 : ℝ)) * (1 / 2) - (1 - y 0) * y 0 = (y 0 - 1 / 2) ^ 2 := by ring
    nlinarith [sq_nonneg (y 0 - 1 / 2)]
  refine ⟨hstrict, hopt, ?_⟩
  simp only [socialSurplus, Fin.sum_univ_one, hpath_eq]
  norm_num

theorem serial_tightness_witness_hundredth :
    ∃ n : ℕ,
      IsStrongSerialOligopolyEquilibrium 1 1 (serialTightnessLatency n)
        (serialTightnessPrice n) (serialTightnessFlow n) ∧
      IsSocialOptimum 1 1 (serialPathLatency (serialTightnessLatency n))
        serialTightnessOptFlow ∧
      (1 : ℝ) / 2 ≤
        socialSurplus 1 (serialPathLatency (serialTightnessLatency n))
          (serialTightnessFlow n) /
        socialSurplus 1 (serialPathLatency (serialTightnessLatency n))
          serialTightnessOptFlow ∧
      socialSurplus 1 (serialPathLatency (serialTightnessLatency n))
        (serialTightnessFlow n) <
        (1 / 2 + 1 / 100) *
          socialSurplus 1 (serialPathLatency (serialTightnessLatency n))
            serialTightnessOptFlow := by
  obtain ⟨n, hn⟩ := serialTightness_surplus_lt_half_add (ε := 1 / 100) (by norm_num)
  have hstrong := serialTightness_isStrongSerialOligopolyEquilibrium n
  have hopt := (serialTightness_isSocialOptimum n).1
  have hopt_pos : 0 < socialSurplus 1 (serialPathLatency (serialTightnessLatency n))
      serialTightnessOptFlow := by
    rw [(serialTightness_isSocialOptimum n).2]
    positivity
  exact ⟨n, hstrong, hopt,
    serial_strict_oligopoly_efficiency_ge_half (serialTightness_smoothConvex n) hstrong hopt
      hopt_pos, hn⟩

end CslibFrontierTests.GameTheory.NetworkPricing
