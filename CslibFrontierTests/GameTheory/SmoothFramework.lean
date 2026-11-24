/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.GameTheory.Congestion.Affine
import CslibFrontier.GameTheory.Congestion.Polynomial
import CslibFrontier.GameTheory.Mechanism.OptimalAuction
import CslibFrontier.GameTheory.Mechanism.SmoothAuction
import CslibFrontier.GameTheory.Strategic.SmoothHierarchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Checked witness tests for smooth games, polynomial congestion, and smooth auctions

Non-vacuous boundary and witness checks exercising:
1. A correlated equilibrium of a 2-player cost game that is **not** a product of mixed strategies,
   checked against `IsSmooth.expected_socialCost_le_of_isCorrelatedEquilibrium` and simultaneous
   composition `CostGame.simultaneous`.
2. An incomplete-information (Bayesian) 2-player atomic congestion game with private feasible
   strategy sets under independent Bernoulli priors, instantiating
   `BayesianCostGame.expected_socialCost_ofCostGame_le_of_isPureBayesNash`.
3. Degree-`d` polynomial atomic congestion smoothness (`d = 3`), exact equality at active quadratic
   pairs `(y, z) = (1, 2)` and `(1, 3)` in `mul_add_one_sq_le_quadraticSmooth`, and the 4-player
   `115 / 12` quadratic tightness witness.
4. Complete-information pure Nash equilibrium of the 2-bidder asymmetric first-price auction and
   continuous `Uniform[0, 1]` Bayes–Nash equilibrium (`FirstPrice.isBayesNash_uniformBid`) checked
   against the `1 - exp (-1)` smooth mechanism welfare bounds.
5. Complete-information 2-bidder second-price no-overbidding `1 / 2` bound contrasted with the
   overbidding `0`-welfare witness `Vickrey.exists_overbidding_isPureNash_welfare_zero`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.SmoothFramework

open Finset Function MeasureTheory Cslib.GameTheory
open scoped NNReal

/-! ### 1. Non-product correlated equilibrium and simultaneous smooth composition -/

/-- A 2-player symmetric lane-splitting cost game on `Bool`: choosing the same lane costs `2` per
player (`socialCost = 4`), whereas splitting across lanes costs `1` per player (`socialCost = 2`).
-/
def splitLaneGame : CostGame (Fin 2) (fun _ => Bool) where
  cost _ s := if s 0 = s 1 then 2 else 1

theorem splitLaneGame_isSmooth : splitLaneGame.IsSmooth (3 / 2) (1 / 2) := by
  intro s s'
  simp only [splitLaneGame, CostGame.socialCost, Fin.sum_univ_two]
  rcases Bool.dichotomy (s 0) with h0 | h0 <;> rcases Bool.dichotomy (s 1) with h1 | h1 <;>
    rcases Bool.dichotomy (s' 0) with h0' | h0' <;> rcases Bool.dichotomy (s' 1) with h1' | h1'
  all_goals
    have upd00 : update s 0 (s' 0) 0 = s' 0 := update_self 0 (s' 0) s
    have upd01 : update s 0 (s' 0) 1 = s 1 := update_of_ne (by decide) (s' 0) s
    have upd10 : update s 1 (s' 1) 0 = s 0 := update_of_ne (by decide) (s' 1) s
    have upd11 : update s 1 (s' 1) 1 = s' 1 := update_self 1 (s' 1) s
    rw [upd00, upd01, upd10, upd11, h0, h1, h0', h1']
    norm_num

/-- Uniform correlation over the two anti-coordinated profiles `(false, true)` and `(true, false)`
— a correlated equilibrium that is not a product of mixed strategies. -/
noncomputable def antiCoordSignal : Convexity.StdSimplex ℝ (Fin 2 → Bool) where
  weights := Finsupp.single (fun i => decide (i = 1)) (1 / 2) +
    Finsupp.single (fun i => decide (i = 0)) (1 / 2)
  nonneg s := by
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> norm_num
  total := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
    norm_num

theorem antiCoordSignal_isCorrelatedEquilibrium :
    splitLaneGame.IsCorrelatedEquilibrium antiCoordSignal := by
  intro i δ
  simp only [antiCoordSignal]
  rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
    Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
    Finsupp.sum_single_index (zero_mul _), Finsupp.sum_single_index (zero_mul _),
    Finsupp.sum_single_index (zero_mul _), Finsupp.sum_single_index (zero_mul _)]
  fin_cases i
  · dsimp only
    change _ ≤ 1 / 2 * splitLaneGame.cost 0 (update (fun i => decide (i = 1)) 0 (δ false)) +
      1 / 2 * splitLaneGame.cost 0 (update (fun i => decide (i = 0)) 0 (δ true))
    rcases Bool.dichotomy (δ false) with hf | hf <;>
      rcases Bool.dichotomy (δ true) with ht | ht
    all_goals
      rw [hf, ht]
      dsimp [splitLaneGame]
      norm_num
  · dsimp only
    change _ ≤ 1 / 2 * splitLaneGame.cost 1 (update (fun i => decide (i = 1)) 1 (δ true)) +
      1 / 2 * splitLaneGame.cost 1 (update (fun i => decide (i = 0)) 1 (δ false))
    rcases Bool.dichotomy (δ true) with ht | ht <;>
      rcases Bool.dichotomy (δ false) with hf | hf
    all_goals
      rw [ht, hf]
      dsimp [splitLaneGame]
      norm_num

/-- Instantiating correlated-equilibrium PoA and simultaneous composition on `splitLaneGame`. -/
theorem splitLaneGame_correlated_and_simultaneous_bound :
    antiCoordSignal.weights.sum (fun s w => w * splitLaneGame.socialCost s) ≤
      (3 / 2) / (1 - 1 / 2) * splitLaneGame.socialCost (fun i => decide (i = 1)) ∧
    (CostGame.simultaneous (fun _ : Fin 3 => splitLaneGame)).IsSmooth (3 / 2) (1 / 2) :=
  ⟨splitLaneGame_isSmooth.expected_socialCost_le_of_isCorrelatedEquilibrium (by norm_num)
      antiCoordSignal_isCorrelatedEquilibrium _,
    CostGame.IsSmooth.simultaneous fun _ => splitLaneGame_isSmooth⟩

/-! ### 2. Bayesian incomplete-information congestion game with private feasible sets -/

/-- Two-link parallel atomic congestion game (`latency 0 k = k`, `latency 1 k = k`). -/
def twoLinkCongestion : CongestionGame (Fin 2) (fun _ => Bool) Bool where
  resources _ b := {b}
  latency _ k := k

theorem twoLinkCongestion_hasAffine : twoLinkCongestion.HasAffineLatencies :=
  ⟨fun _ => 1, fun _ => 0, fun _ => zero_le_one, fun _ => le_rfl, fun _ k => by
    change (k : ℝ) = 1 * k + 0
    ring⟩

/-- Type `false` restricts a player to link `false`; type `true` allows only link `true`. -/
def singletonAllowed : Fin 2 → Bool → Set Bool := fun _ t => {t}

noncomputable def uniformBoolPrior : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2

theorem uniformBoolPrior_isMixedStrategy (i : Fin 2) : IsMixedStrategy (uniformBoolPrior i) := by
  rw [isMixedStrategy_iff]
  refine ⟨fun _ => by norm_num [uniformBoolPrior], ?_⟩
  simp [uniformBoolPrior]

theorem bayesian_twoLink_poa_bound :
    ∑ θ : Fin 2 → Bool, productWeight uniformBoolPrior θ *
        twoLinkCongestion.toCostGame.socialCost (fun j => θ j) ≤
      (5 / 3) / (1 - 1 / 3) *
        ∑ θ' : Fin 2 → Bool, productWeight uniformBoolPrior θ' *
          twoLinkCongestion.toCostGame.socialCost (fun j => θ' j) := by
  have hsm := twoLinkCongestion.isSmooth_of_hasAffineLatencies twoLinkCongestion_hasAffine
  have hbn : (BayesianCostGame.ofCostGame twoLinkCongestion.toCostGame
      singletonAllowed).IsPureBayesNash uniformBoolPrior (fun _ t => t) := by
    refine ⟨fun _ _ => rfl, fun i t a ha => ?_⟩
    rw [Set.mem_singleton_iff.1 ha]
  exact BayesianCostGame.expected_socialCost_ofCostGame_le_of_isPureBayesNash singletonAllowed hsm
    (by norm_num) uniformBoolPrior_isMixedStrategy hbn (fun θ' => θ') (fun _ _ => rfl)

/-! ### 3. Polynomial congestion smoothness: active equalities and cubic instantiation -/

/-- Exact equality at both active integer pairs `(y, z) = (1, 2)` and `(1, 3)` of the Aland et al.
quadratic smoothness inequality `y * (z + 1) ^ 2 ≤ 115 / 19 * y ^ 3 + 7 / 19 * z ^ 3`. -/
theorem quadratic_smooth_active_pairs_tight :
    (1 : ℝ) * ((2 : ℝ) + 1) ^ 2 = 115 / 19 * (1 : ℝ) ^ 3 + 7 / 19 * (2 : ℝ) ^ 3 ∧
      (1 : ℝ) * ((3 : ℝ) + 1) ^ 2 = 115 / 19 * (1 : ℝ) ^ 3 + 7 / 19 * (3 : ℝ) ^ 3 := by
  constructor <;> norm_num

/-- Non-vacuous cubic (`d = 3`) congestion game (`latency e k = k ^ 3 + 2 * k`) instantiating
`expected_socialCost_le_succ_pow_of_hasPolynomialLatencies` (`PoA ≤ 4 ^ 4 = 256`). -/
def cubicTwoLink : CongestionGame (Fin 2) (fun _ => Bool) Bool where
  resources _ b := {b}
  latency _ k := (k : ℝ) ^ 3 + 2 * (k : ℝ)

theorem cubicTwoLink_hasPolynomialLatencies : cubicTwoLink.HasPolynomialLatencies 3 := by
  refine ⟨fun _ j => if j = 3 then 1 else if j = 1 then 2 else 0,
    fun _ j => by dsimp only; split_ifs <;> norm_num, fun _ k => ?_⟩
  simp only [cubicTwoLink, sum_range_succ, sum_range_zero, Nat.reduceEqDiff, ↓reduceIte,
    zero_mul, one_mul, pow_one]
  ring

theorem cubicTwoLink_poa_le_256 {σ : Convexity.StdSimplex ℝ (Fin 2 → Bool)}
    (hσ : cubicTwoLink.toCostGame.IsCoarseCorrelatedEquilibrium σ) (s' : Fin 2 → Bool) :
    σ.weights.sum (fun s w => w * cubicTwoLink.toCostGame.socialCost s) ≤
      256 * cubicTwoLink.toCostGame.socialCost s' := by
  have h := CongestionGame.expected_socialCost_le_succ_pow_of_hasPolynomialLatencies
    (d := 3) (by omega) cubicTwoLink_hasPolynomialLatencies hσ s'
  norm_num at h
  exact h

/-! ### 4. First-price smooth auction: complete-information and Uniform[0, 1] Bayesian witnesses -/

def asymVal : Fin 2 → ℝ := fun i => if i = 0 then 2 else 1
def tieBidOne : Fin 2 → ℝ≥0 := fun _ => 1
def winnerZeroAlloc : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0

/-- Complete-information 2-bidder asymmetric first-price pure Nash equilibrium: with valuations
`asymVal 0 = 2`, `asymVal 1 = 1`, both bidding `1` (`tieBidOne`) is a pure Nash equilibrium of
`FirstPrice.mechanism.toCostGame asymVal`, checked against `1 - exp (-1)`. -/
theorem firstPrice_asymmetric_pureNash_witness :
    (SingleParameter.FirstPrice.mechanism.toCostGame asymVal).IsPureNash tieBidOne ∧
      (1 - Real.exp (-1)) * SingleParameter.socialWelfare asymVal winnerZeroAlloc ≤
        SingleParameter.FirstPrice.mechanism.welfare asymVal (fun j => (tieBidOne j : ℝ)) := by
  have hpn : (SingleParameter.FirstPrice.mechanism.toCostGame asymVal).IsPureNash tieBidOne := by
    have hw0 : SingleParameter.Vickrey.Wins (fun j : Fin 2 => (tieBidOne j : ℝ)) 0 := by
      intro j hj
      fin_cases j
      · exact absurd rfl hj
      · simp [tieBidOne]
    have hl1 : SingleParameter.Vickrey.allocation (fun j : Fin 2 => (tieBidOne j : ℝ)) 1 = 0 := by
      rcases SingleParameter.Vickrey.allocation_binary
          (fun j : Fin 2 => (tieBidOne j : ℝ)) 1 with h0 | h1
      · exact h0
      · exact absurd ((SingleParameter.Vickrey.allocation_eq_one_iff.1 h1).unique hw0) (by decide)
    intro i z
    fin_cases i
    · change (SingleParameter.FirstPrice.mechanism.toCostGame asymVal).cost 0 tieBidOne ≤
        (SingleParameter.FirstPrice.mechanism.toCostGame asymVal).cost 0 (update tieBidOne 0 z)
      dsimp only [SingleParameter.Mechanism.toCostGame, SingleParameter.Mechanism.utility,
        SingleParameter.FirstPrice.mechanism]
      rw [SingleParameter.Mechanism.coe_update_nnreal tieBidOne 0 z,
        SingleParameter.Vickrey.allocation_eq_one_iff.2 hw0, update_self]
      have hv0 : asymVal 0 = 2 := rfl
      have hb0 : (tieBidOne 0 : ℝ) = 1 := rfl
      rw [hv0, hb0]
      by_cases hwin : SingleParameter.Vickrey.Wins
          (update (fun j : Fin 2 => (tieBidOne j : ℝ)) 0 (z : ℝ)) 0
      · rw [SingleParameter.Vickrey.allocation_eq_one_iff.2 hwin]
        have hge1 : (1 : ℝ) ≤ z := by
          have := (hwin 1 (by decide)).1
          simpa [tieBidOne] using this
        linarith
      · rw [SingleParameter.Vickrey.allocation_eq_zero_iff.2 hwin]
        norm_num
    · change (SingleParameter.FirstPrice.mechanism.toCostGame asymVal).cost 1 tieBidOne ≤
        (SingleParameter.FirstPrice.mechanism.toCostGame asymVal).cost 1 (update tieBidOne 1 z)
      dsimp only [SingleParameter.Mechanism.toCostGame, SingleParameter.Mechanism.utility,
        SingleParameter.FirstPrice.mechanism]
      rw [SingleParameter.Mechanism.coe_update_nnreal tieBidOne 1 z, hl1, update_self]
      have hv1 : asymVal 1 = 1 := rfl
      rw [hv1]
      by_cases hwin : SingleParameter.Vickrey.Wins
          (update (fun j : Fin 2 => (tieBidOne j : ℝ)) 1 (z : ℝ)) 1
      · rw [SingleParameter.Vickrey.allocation_eq_one_iff.2 hwin]
        have hgt1 : (1 : ℝ) < z := by
          have := (hwin 0 (by decide)).2 (by decide)
          simpa [tieBidOne] using this
        linarith
      · rw [SingleParameter.Vickrey.allocation_eq_zero_iff.2 hwin]
        norm_num
  have hv_nonneg : 0 ≤ asymVal := fun i => by fin_cases i <;> norm_num [asymVal]
  have hx_mem : winnerZeroAlloc ∈ SingleParameter.Vickrey.singleItemFeasible := by
    refine ⟨fun i => by fin_cases i <;> simp [winnerZeroAlloc], ?_⟩
    simp [winnerZeroAlloc]
  have hbound := SingleParameter.FirstPrice.welfare_ge_one_sub_exp_neg_one hv_nonneg hx_mem
    hpn.isCoarseCorrelatedEquilibrium
  rw [Convexity.StdSimplex.weights_single, Finsupp.sum_single_index (zero_mul _), one_mul] at hbound
  exact ⟨hpn, hbound⟩

/-- Uniform probability measure on `[0, 1]` for the continuous 2-bidder Bayes–Nash test. -/
noncomputable abbrev unif01 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

private instance : IsProbabilityMeasure unif01 :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩

/-- Continuous 2-bidder `Uniform[0, 1]` instantiation of
`FirstPrice.integral_welfare_ge_one_sub_exp_neg_one` on `FirstPrice.isBayesNash_uniformBid` against
the welfare-maximizing allocation rule `Vickrey.allocation`. -/
theorem firstPrice_uniformBid_bayesian_welfare_witness :
    (1 - Real.exp (-1)) *
        (∫ v, SingleParameter.socialWelfare v (SingleParameter.Vickrey.allocation v)
          ∂Measure.pi (fun _ : Fin 2 => unif01)) ≤
      ∫ v, SingleParameter.FirstPrice.mechanism.welfare v
        (fun j => SingleParameter.FirstPrice.uniformBid 2 (v j))
        ∂Measure.pi (fun _ : Fin 2 => unif01) := by
  let ν : Fin 2 → Measure ℝ := fun _ => unif01
  have hsupp : ∀ _ : Fin 2, ∀ᵐ t ∂unif01, t ∈ Set.Icc 0 1 := fun _ =>
    ae_restrict_mem measurableSet_Icc
  have hbox : ∀ᵐ v ∂Measure.pi ν, ∀ i, v i ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Filter.eventually_all]
    intro i
    exact (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hsupp i)
  have hbn : SingleParameter.FirstPrice.mechanism.IsBayesNash ν (fun _ => 1)
      (fun _ => SingleParameter.FirstPrice.uniformBid 2) := by
    simpa only [Fintype.card_fin] using
      (SingleParameter.FirstPrice.isBayesNash_uniformBid (ι := Fin 2))
  have halloc_bdd : ∀ (f : (Fin 2 → ℝ) → Fin 2 → ℝ), Measurable f → ∀ i,
      Integrable (fun w => SingleParameter.Vickrey.allocation (f w) i) (Measure.pi ν) := by
    intro f hf i
    refine Integrable.of_bound
      ((SingleParameter.Vickrey.measurable_allocation i).comp hf).aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun w => ?_)
    rcases SingleParameter.Vickrey.allocation_binary (f w) i with h0 | h1
    · rw [h0]; norm_num
    · rw [h1]; norm_num
  have halloc_dev : ∀ (i : Fin 2) (z : ℝ), 0 ≤ z →
      Integrable (fun w => SingleParameter.FirstPrice.mechanism.allocation
        (update (fun j => SingleParameter.FirstPrice.uniformBid 2 (w j)) i z) i)
        (Measure.pi ν) := by
    intro i z _
    refine halloc_bdd _ (measurable_pi_iff.2 fun j => ?_) i
    rcases eq_or_ne j i with rfl | hj
    · simp only [update_self]
      exact measurable_const
    · simp only [update_of_ne hj]
      exact (SingleParameter.FirstPrice.measurable_uniformBid 2).comp (measurable_pi_apply j)
  have hpay_dev : ∀ (i : Fin 2) (z : ℝ), 0 ≤ z →
      Integrable (fun w => SingleParameter.FirstPrice.mechanism.payment
        (update (fun j => SingleParameter.FirstPrice.uniformBid 2 (w j)) i z) i)
        (Measure.pi ν) := by
    intro i z hz
    have heq : (fun w : Fin 2 → ℝ => SingleParameter.FirstPrice.mechanism.payment
          (update (fun j => SingleParameter.FirstPrice.uniformBid 2 (w j)) i z) i) =
        fun w => z * SingleParameter.FirstPrice.mechanism.allocation
          (update (fun j => SingleParameter.FirstPrice.uniformBid 2 (w j)) i z) i := by
      funext w
      simp only [SingleParameter.FirstPrice.mechanism, update_self]
    rw [heq]
    exact (halloc_dev i z hz).const_mul z
  have hpay_eq : ∀ i : Fin 2,
      Integrable (fun v => SingleParameter.FirstPrice.mechanism.payment
        (fun j => SingleParameter.FirstPrice.uniformBid 2 (v j)) i) (Measure.pi ν) := fun i => by
    simpa only [Fintype.card_fin] using
      (SingleParameter.FirstPrice.integrable_payment_uniformBid (ι := Fin 2) i)
  have hval_mul_int : ∀ (f : (Fin 2 → ℝ) → Fin 2 → ℝ), Measurable f → ∀ i,
      Integrable (fun v => v i * SingleParameter.Vickrey.allocation (f v) i) (Measure.pi ν) := by
    intro f hf i
    refine Integrable.of_bound
      ((measurable_pi_apply i).mul
        ((SingleParameter.Vickrey.measurable_allocation i).comp hf)).aestronglyMeasurable 1 ?_
    filter_upwards [hbox] with v hv
    have hv1 : |v i| ≤ 1 := by
      rw [abs_of_nonneg (hv i).1]
      exact (hv i).2
    have ha1 : |SingleParameter.Vickrey.allocation (f v) i| ≤ 1 := by
      rcases SingleParameter.Vickrey.allocation_binary (f v) i with h0 | h1
      · rw [h0]; norm_num
      · rw [h1]; norm_num
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hv1).trans ha1
  have hutil_eq : ∀ i : Fin 2,
      Integrable (fun v => SingleParameter.FirstPrice.mechanism.utility i (v i)
        (fun j => SingleParameter.FirstPrice.uniformBid 2 (v j))) (Measure.pi ν) := by
    intro i
    have hm : Measurable (fun v : Fin 2 → ℝ =>
        fun j => SingleParameter.FirstPrice.uniformBid 2 (v j)) :=
      measurable_pi_iff.2 fun j =>
        (SingleParameter.FirstPrice.measurable_uniformBid 2).comp (measurable_pi_apply j)
    exact (hval_mul_int _ hm i).sub (hpay_eq i)
  have hx_int : Integrable
      (fun v => SingleParameter.socialWelfare v (SingleParameter.Vickrey.allocation v))
      (Measure.pi ν) :=
    integrable_finsetSum _ fun i _ => hval_mul_int id measurable_id i
  exact SingleParameter.FirstPrice.integral_welfare_ge_one_sub_exp_neg_one hsupp hbn
    halloc_dev hpay_dev hutil_eq hpay_eq
    (fun v _ => SingleParameter.Vickrey.allocation_mem_singleItemFeasible v) hx_int

/-! ### 5. Second-price no-overbidding `1 / 2` witness vs. overbidding `0`-welfare witness -/

def unitVal : Fin 2 → ℝ := fun _ => 1
def asymZeroOneBid : Fin 2 → ℝ≥0 := fun i => if i = 0 then 1 else 0
def winnerOneAlloc : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1

/-- Second-price no-overbidding `1 / 2` witness vs. overbidding `0`-welfare witness. -/
theorem secondPrice_noOverbidding_and_overbidding_witnesses :
    (∃ (v : Fin 2 → ℝ) (b : Fin 2 → ℝ≥0) (x : Fin 2 → ℝ),
      0 ≤ v ∧ x ∈ SingleParameter.Vickrey.singleItemFeasible ∧
        SingleParameter.socialWelfare v x = 1 ∧
        (SingleParameter.Vickrey.mechanism.toCostGame v).IsPureNash b ∧
        SingleParameter.Vickrey.mechanism.welfare v (fun j => (b j : ℝ)) = 0) ∧
    (1 / 2 * SingleParameter.socialWelfare unitVal winnerOneAlloc ≤
      SingleParameter.Vickrey.mechanism.welfare unitVal (fun j => (asymZeroOneBid j : ℝ))) := by
  refine ⟨SingleParameter.Vickrey.exists_overbidding_isPureNash_welfare_zero, ?_⟩
  have hv : 0 ≤ unitVal := fun _ => zero_le_one
  have hx : winnerOneAlloc ∈ SingleParameter.Vickrey.singleItemFeasible := by
    refine ⟨fun i => by fin_cases i <;> simp [winnerOneAlloc], ?_⟩
    simp [winnerOneAlloc]
  have hpn : (SingleParameter.Vickrey.mechanism.toCostGame unitVal).IsPureNash asymZeroOneBid := by
    have hw0 : SingleParameter.Vickrey.Wins (fun j : Fin 2 => (asymZeroOneBid j : ℝ)) 0 := by
      intro j hj
      fin_cases j
      · exact absurd rfl hj
      · simp [asymZeroOneBid]
    have hl1 :
        SingleParameter.Vickrey.allocation (fun j : Fin 2 => (asymZeroOneBid j : ℝ)) 1 = 0 := by
      rcases SingleParameter.Vickrey.allocation_binary
          (fun j : Fin 2 => (asymZeroOneBid j : ℝ)) 1 with h0 | h1
      · exact h0
      · exact absurd ((SingleParameter.Vickrey.allocation_eq_one_iff.1 h1).unique hw0) (by decide)
    intro i z
    fin_cases i
    · have hob0 :
          SingleParameter.Vickrey.highestOtherBid
            (fun j : Fin 2 => (asymZeroOneBid j : ℝ)) 0 = 0 := by
        refine le_antisymm ?_ (SingleParameter.Vickrey.highestOtherBid_nonneg _ _)
        refine SingleParameter.Vickrey.highestOtherBid_le_iff.2 ⟨le_rfl, fun j hj => ?_⟩
        fin_cases j
        · exact absurd rfl hj
        · simp [asymZeroOneBid]
      change (SingleParameter.Vickrey.mechanism.toCostGame unitVal).cost 0 asymZeroOneBid ≤
        (SingleParameter.Vickrey.mechanism.toCostGame unitVal).cost 0 (update asymZeroOneBid 0 z)
      dsimp only [SingleParameter.Mechanism.toCostGame, SingleParameter.Mechanism.utility,
        SingleParameter.Vickrey.mechanism, unitVal]
      rw [SingleParameter.Mechanism.coe_update_nnreal asymZeroOneBid 0 z,
        SingleParameter.Vickrey.allocation_eq_one_iff.2 hw0,
        SingleParameter.Vickrey.highestOtherBid_update, hob0]
      rcases SingleParameter.Vickrey.allocation_binary
          (update (fun j : Fin 2 => (asymZeroOneBid j : ℝ)) 0 (z : ℝ)) 0 with h0 | h1
      · rw [h0]; norm_num
      · rw [h1]
    · have hob1 :
          SingleParameter.Vickrey.highestOtherBid
            (fun j : Fin 2 => (asymZeroOneBid j : ℝ)) 1 = 1 := by
        refine le_antisymm ?_ ?_
        · refine SingleParameter.Vickrey.highestOtherBid_le_iff.2 ⟨zero_le_one, fun j hj => ?_⟩
          fin_cases j
          · simp [asymZeroOneBid]
          · exact absurd rfl hj
        · have hle := SingleParameter.Vickrey.le_highestOtherBid
            (b := fun j : Fin 2 => (asymZeroOneBid j : ℝ)) (i := 1) (j := 0) (by decide)
          simpa [asymZeroOneBid] using hle
      change (SingleParameter.Vickrey.mechanism.toCostGame unitVal).cost 1 asymZeroOneBid ≤
        (SingleParameter.Vickrey.mechanism.toCostGame unitVal).cost 1 (update asymZeroOneBid 1 z)
      dsimp only [SingleParameter.Mechanism.toCostGame, SingleParameter.Mechanism.utility,
        SingleParameter.Vickrey.mechanism, unitVal]
      rw [SingleParameter.Mechanism.coe_update_nnreal asymZeroOneBid 1 z, hl1,
        SingleParameter.Vickrey.highestOtherBid_update, hob1]
      rcases SingleParameter.Vickrey.allocation_binary
          (update (fun j : Fin 2 => (asymZeroOneBid j : ℝ)) 1 (z : ℝ)) 1 with h0 | h1
      · rw [h0]
      · rw [h1]; norm_num
  have hnob : ∀ b' ∈ (Convexity.StdSimplex.single (R := ℝ) asymZeroOneBid).weights.support,
      ∀ j, (b' j : ℝ) ≤ unitVal j := by
    intro b' hb' j
    have hb_eq : b' = asymZeroOneBid := by
      by_contra hne
      rw [Convexity.StdSimplex.weights_single, Finsupp.mem_support_iff,
        Finsupp.single_eq_of_ne hne] at hb'
      exact hb' rfl
    subst hb_eq
    fin_cases j <;> simp [asymZeroOneBid, unitVal]
  have h := SingleParameter.Vickrey.welfare_ge_half_of_noOverbidding hv hx
    hpn.isCoarseCorrelatedEquilibrium hnob
  rw [Convexity.StdSimplex.weights_single, Finsupp.sum_single_index (zero_mul _), one_mul] at h
  exact h

end CslibFrontierTests.GameTheory.SmoothFramework
