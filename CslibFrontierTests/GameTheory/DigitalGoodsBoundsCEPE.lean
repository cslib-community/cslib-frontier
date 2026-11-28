/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.GameTheory.Mechanism.DigitalGoods.ConsensusEstimation
import CslibFrontier.GameTheory.Mechanism.DigitalGoods.LowerBounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Digital goods impossibility, lower bounds, limited-supply reduction, and CEPE tests

Non-vacuous client checks and boundary witnesses for
`CslibFrontier.GameTheory.Mechanism.DigitalGoods.LowerBounds` and
`CslibFrontier.GameTheory.Mechanism.DigitalGoods.ConsensusEstimation`:

* **Symmetric deterministic impossibility (`Theorem 13.24` & `Corollary 13.35`) and tightness:**
  concrete values of `symmetricSecondPrice` on `Fin 2` (`(1, 2)`) and `Fin 3` (`(10, 1, 1)` and the
  tie profile `(1, 1, 1)`), non-symmetry contrast for `Vickrey.mechanism` on `Fin 2`, and
  non-vacuous instantiations of `isLeast_symmetricSecondPrice_competitiveRatio`,
  `not_exists_const_competitive_symmetric`, and `exists_not_approx_symmetric_deterministic`.
* **Randomized competitive lower bounds (`Lemma 13.38`, `13 / 6` for `n = 3`, `Exercise 13.8`):**
  client check constructing the truthful-in-expectation mechanism `expectedRSPE` from `rspe`
  (satisfying `IsDSIC`, `IsIR`, `IsNormalized`, `IsUnitAlloc`, and `4`-competitiveness while
  failing `IsBinary`), applying `two_le_of_isCompetitive_two`,
  `thirteen_div_six_le_of_isCompetitive_three`, and `exists_strictly_higher_profit_two`.
* **Limited-supply reduction (`Exercise 13.9`):** concrete `optimalProfitTwoLimited` values
  showing `ℱ⁽²˒²⁾(2, 2, 2) = 4 < 6 = ℱ⁽²⁾(2, 2, 2)` and the `k = 1` boundary (`ℱ⁽²˒¹⁾ = 0`), plus
  instantiations of `limitedSupplyMechanism 2` on both deterministic `symmetricSecondPrice` and
  randomized `expectedRSPE`.
* **CEPE (`Lemmas 13.47–13.48`, `Theorem 13.49`, `Exercise 13.11`):** concrete evaluations of
  `roundDown 2` (positive, zero, and negative inputs), exact consensus measure `1 / 2` at
  `α = 4, ρ = 2`, exact integral `4 / (2 * Real.log 2)` at `α = 2, V = 4`, concrete instantiation
  of `cepeDigitalGoods 2` on `Fin 3` (`v = (1, 1, 1)`, `m = 3` winners), and boundary witness
  showing `ℱ⁽²⁾` drops from `2` to `0` at `m = 2` (`v = (1, 1)`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.DigitalGoodsBoundsCEPE

open Finset MeasureTheory
open scoped BigOperators
open Cslib.GameTheory.SingleParameter
open Cslib.GameTheory.SingleParameter.DigitalGoods

/-! ### Symmetric deterministic impossibility and `symmetricSecondPrice` tightness -/

/-- On `Fin 2` with `b = (1, 2)`, `symmetricSecondPrice` awards bidder `1` at price `1` (profit
`1`, vs `ℱ⁽²⁾ = 2`). -/
example :
    symmetricSecondPrice.allocation ![(1 : ℝ), 2] 0 = 0 ∧
      symmetricSecondPrice.allocation ![(1 : ℝ), 2] 1 = 1 ∧
      ∑ i : Fin 2, symmetricSecondPrice.payment ![(1 : ℝ), 2] i = 1 := by
  have h0 : ((univ : Finset (Fin 2)).erase 0).fold max (0 : ℝ) ![(1 : ℝ), 2] = 2 := by
    have he : (univ : Finset (Fin 2)).erase 0 = {1} := by decide
    rw [he, fold_singleton]; norm_num
  have h1 : ((univ : Finset (Fin 2)).erase 1).fold max (0 : ℝ) ![(1 : ℝ), 2] = 1 := by
    have he : (univ : Finset (Fin 2)).erase 1 = {0} := by decide
    rw [he, fold_singleton]; norm_num
  simp only [symmetricSecondPrice, Fin.sum_univ_two, h0, h1]
  norm_num

/-- On `Fin 3` with all-tied bids `(1, 1, 1)`, every bidder wins and pays `1` (total profit `3`);
on `(10, 1, 1)`, only bidder `0` wins and pays `1` (total profit `1`, vs `ℱ⁽²⁾ = 3`). -/
example :
    ∑ i : Fin 3, symmetricSecondPrice.payment ![(1 : ℝ), 1, 1] i = 3 ∧
      ∑ i : Fin 3, symmetricSecondPrice.payment ![(10 : ℝ), 1, 1] i = 1 := by
  have h111 : ∀ i : Fin 3,
      ((univ : Finset (Fin 3)).erase i).fold max (0 : ℝ) ![(1 : ℝ), 1, 1] = 1 := by
    intro i
    apply le_antisymm
    · rw [Finset.fold_max_le]
      refine ⟨by norm_num, fun j _ => ?_⟩
      fin_cases j <;> norm_num
    · rw [Finset.le_fold_max]
      right
      fin_cases i
      · exact ⟨1, by decide, by norm_num⟩
      · exact ⟨0, by decide, by norm_num⟩
      · exact ⟨0, by decide, by norm_num⟩
  have h10_0 : ((univ : Finset (Fin 3)).erase 0).fold max (0 : ℝ) ![(10 : ℝ), 1, 1] = 1 := by
    have he : (univ : Finset (Fin 3)).erase 0 = {1, 2} := by decide
    rw [he, fold_insert (by decide), fold_singleton]
    norm_num
  have h10_1 : ((univ : Finset (Fin 3)).erase 1).fold max (0 : ℝ) ![(10 : ℝ), 1, 1] = 10 := by
    have he : (univ : Finset (Fin 3)).erase 1 = {0, 2} := by decide
    rw [he, fold_insert (by decide), fold_singleton]
    norm_num
  have h10_2 : ((univ : Finset (Fin 3)).erase 2).fold max (0 : ℝ) ![(10 : ℝ), 1, 1] = 10 := by
    have he : (univ : Finset (Fin 3)).erase 2 = {0, 1} := by decide
    rw [he, fold_insert (by decide), fold_singleton]
    norm_num
  simp only [symmetricSecondPrice, Fin.sum_univ_three, h111, h10_0, h10_1, h10_2]
  norm_num

/-- Contrast: standard index-tie-broken `Vickrey.mechanism` on `Fin 2` is **not** `IsSymmetric`
(on `(1, 1)`, bidder `0` wins while bidder `1` loses). -/
example : ¬ IsSymmetric (Vickrey.mechanism (ι := Fin 2)) := by
  intro hSym
  let b : Fin 2 → ℝ := ![(1 : ℝ), 1]
  have hb : 0 ≤ b := fun i => by fin_cases i <;> norm_num [b]
  have hcomp : b ∘ Equiv.swap (0 : Fin 2) 1 = b := by
    ext i; fin_cases i <;> rfl
  have h := (hSym (Equiv.swap (0 : Fin 2) 1) b 0 hb).1
  rw [hcomp, Equiv.swap_apply_left] at h
  have hw0 : Vickrey.Wins b 0 := fun j hj => by
    fin_cases j
    · exact absurd rfl hj
    · exact ⟨le_rfl, fun hlt => by omega⟩
  have hnw1 : ¬ Vickrey.Wins b 1 := fun hw1 => by
    have hlt := (hw1 0 (by decide)).2 (by decide)
    norm_num [b] at hlt
  simp only [Vickrey.mechanism, Vickrey.allocation, hw0, hnw1, ↓reduceIte] at h
  norm_num at h

/-- Non-vacuity of `isLeast_symmetricSecondPrice_competitiveRatio`,
`not_exists_const_competitive_symmetric`, and `exists_not_approx_symmetric_deterministic`. -/
example :
    IsLeast {β : ℝ | IsCompetitive (optimalProfitTwo (ι := Fin 2))
        (fun b => ∑ i, symmetricSecondPrice.payment b i) β} 2 ∧
      IsLeast {β : ℝ | IsCompetitive (optimalProfitTwo (ι := Fin 3))
        (fun b => ∑ i, symmetricSecondPrice.payment b i) β} 3 ∧
      (∃ n ≥ 2, ∃ h ≥ (1 : ℝ),
        ∀ M : Mechanism (Fin n), M.IsDSIC → M.IsIR → IsBinary M.allocation → IsSymmetric M →
          ∃ b : Fin n → ℝ, (∀ i, 1 ≤ b i ∧ b i ≤ h) ∧
            ∑ i, M.payment b i < optimalProfit b / 2 - h * 1) := by
  refine ⟨?_, ?_, exists_not_approx_symmetric_deterministic (by norm_num : (0 : ℝ) < 2) 1⟩
  · simpa only [Fintype.card_fin, Nat.cast_ofNat] using
      isLeast_symmetricSecondPrice_competitiveRatio (ι := Fin 2) (by decide)
  · simpa only [Fintype.card_fin, Nat.cast_ofNat] using
      isLeast_symmetricSecondPrice_competitiveRatio (ι := Fin 3) (by decide)

/-! ### Randomized lower bounds (`Lemma 13.38`, `13 / 6`, `Exercise 13.8`) via `RSPE` -/

/-- Truthful-in-expectation `Mechanism` obtained by averaging `rspe s` uniformly over all
bipartitions `s : Finset ι`. -/
private noncomputable def expectedRSPE {ι : Type*} [Fintype ι] [DecidableEq ι] : Mechanism ι where
  allocation b i := 𝔼 s : Finset ι, (rspe s).allocation b i
  payment b i := 𝔼 s : Finset ι, (rspe s).payment b i

private theorem expectedRSPE_isDSIC {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (expectedRSPE (ι := ι)).IsDSIC := by
  intro i b v hb hv
  have hutil : ∀ c : ι → ℝ, expectedRSPE.utility i v c = 𝔼 s : Finset ι, (rspe s).utility i v c :=
    fun c => by
      simp only [Mechanism.utility, expectedRSPE, Finset.expect_sub_distrib, Finset.mul_expect]
  rw [hutil, hutil]
  exact rspe_truthfulInExpectation i b v hb hv

private theorem expectedRSPE_isIR {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (expectedRSPE (ι := ι)).IsIR := by
  intro i b hb
  have hutil : expectedRSPE.utility i (b i) b = 𝔼 s : Finset ι, (rspe s).utility i (b i) b := by
    simp only [Mechanism.utility, expectedRSPE, Finset.expect_sub_distrib, Finset.mul_expect]
  rw [hutil]
  have h0 : (0 : ℝ) = 𝔼 _s : Finset ι, (0 : ℝ) := (Finset.expect_const (univ_nonempty) 0).symm
  rw [h0]
  exact Finset.expect_le_expect fun s _ => rspe_isIR s i b hb

private theorem expectedRSPE_isNormalized {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (expectedRSPE (ι := ι)).IsNormalized := by
  intro i b hb
  dsimp only [expectedRSPE]
  have hcongr : (𝔼 s : Finset ι, (rspe s).payment (Function.update b i 0) i) =
      𝔼 _s : Finset ι, (0 : ℝ) :=
    Finset.expect_congr rfl fun s _ => rspe_isNormalized s i b hb
  rw [hcongr, Finset.expect_const univ_nonempty]

private theorem expectedRSPE_isUnitAlloc {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsUnitAlloc (expectedRSPE (ι := ι)).allocation := by
  intro b hb i
  dsimp only [expectedRSPE]
  constructor
  · rw [← Finset.expect_const (s := (univ : Finset (Finset ι))) univ_nonempty (0 : ℝ)]
    exact Finset.expect_le_expect fun s _ => (IsBinary.isUnitAlloc (rspe_isBinary s) b hb i).1
  · rw [← Finset.expect_const (s := (univ : Finset (Finset ι))) univ_nonempty (1 : ℝ)]
    exact Finset.expect_le_expect fun s _ => (IsBinary.isUnitAlloc (rspe_isBinary s) b hb i).2

private theorem expectedRSPE_isCompetitive {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsCompetitive (optimalProfitTwo (ι := ι))
      (fun b => ∑ i, expectedRSPE.payment b i) 4 := by
  have hsum : (fun b : ι → ℝ => ∑ i, expectedRSPE.payment b i) = rspeExpectedProfit := by
    ext b
    dsimp only [expectedRSPE, rspeExpectedProfit]
    exact (Finset.expect_sum_comm _ _ _).symm
  rw [hsum]
  exact rspe_isCompetitive

/-- Non-vacuous client check of **Lemma 13.38** (`2 ≤ β`), the **`13 / 6` lower bound for `n = 3`**,
and **Exercise 13.8** applied to both `expectedRSPE` and `symmetricSecondPrice`. -/
example :
    (2 : ℝ) ≤ 4 ∧ (13 : ℝ) / 6 ≤ 4 ∧
      (∃ M' : Mechanism (Fin 2), M'.IsDSIC ∧ M'.IsIR ∧ M'.IsNormalized ∧ IsBinary M'.allocation ∧
        ∃ b : Fin 2 → ℝ, 0 ≤ b ∧
          ∑ i, symmetricSecondPrice.payment b i < ∑ i, M'.payment b i) :=
  ⟨two_le_of_isCompetitive_two (ι := Fin 2) (Fintype.card_fin 2) expectedRSPE_isDSIC
      expectedRSPE_isIR expectedRSPE_isUnitAlloc expectedRSPE_isCompetitive,
    thirteen_div_six_le_of_isCompetitive_three (ι := Fin 3) (Fintype.card_fin 3) expectedRSPE_isDSIC
      expectedRSPE_isIR expectedRSPE_isUnitAlloc expectedRSPE_isCompetitive,
    exists_strictly_higher_profit_two (ι := Fin 2) (Fintype.card_fin 2) symmetricSecondPrice_isDSIC
      symmetricSecondPrice_isIR (IsBinary.isUnitAlloc symmetricSecondPrice_isBinary)⟩

/-! ### Limited-supply reduction (`Exercise 13.9`) -/

/-- Boundary check for `optimalProfitTwoLimited`:
* when `k = 1`, `ℱ⁽²˒¹⁾ = 0`;
* on `(2, 2, 2)` with `k = 2`, `ℱ⁽²˒²⁾ = 4 < 6 = ℱ⁽²⁾`. -/
example :
    optimalProfitTwoLimited 1 ![(2 : ℝ), 2, 2] = 0 ∧
      optimalProfitTwoLimited 2 ![(2 : ℝ), 2, 2] = 4 := by
  constructor
  · unfold optimalProfitTwoLimited
    have hnot : ¬ 2 ≤ min 1 (Fintype.card (Fin 3)) := by decide
    exact dite_eq_right hnot
  · unfold optimalProfitTwoLimited
    have hge : 2 ≤ min 2 (Fintype.card (Fin 3)) := by decide
    rw [dite_eq_left hge]
    have hmin : min 2 (Fintype.card (Fin 3)) = 2 := by decide
    have hos : Fintype.orderStatistic ![(2 : ℝ), 2, 2] (Fintype.card (Fin 3) - 2) = 2 := by
      refine Fintype.orderStatistic_eq_of_isOrderStatistic (by decide) ?_
      refine ⟨⟨0, rfl⟩, ?_, ?_⟩
      · have h0 : (univ.filter fun i : Fin 3 => ![(2 : ℝ), 2, 2] i < 2) = ∅ :=
          filter_eq_empty_iff.2 fun i _ => by fin_cases i <;> norm_num
        rw [h0, card_empty]; omega
      · have hall : (univ.filter fun i : Fin 3 => ![(2 : ℝ), 2, 2] i ≤ 2) = univ :=
          filter_true_of_mem fun i _ => by fin_cases i <;> norm_num
        rw [hall, card_univ, Fintype.card_fin]; decide
    simp only [hmin, Icc_self, sup'_singleton]
    rw [hos]
    norm_num

/-- Instantiations of **Exercise 13.9** (`limitedSupplyMechanism 2` on `Fin 3`):
* with deterministic `symmetricSecondPrice` on `Fin 2`, yielding a binary `2`-unit DSIC, IR,
  normalized, `2`-competitive auction against `ℱ⁽²˒²⁾`;
* with randomized `expectedRSPE` on `Fin 2`, yielding a `4`-competitive `2`-unit DSIC, IR,
  normalized auction against `ℱ⁽²˒²⁾`. -/
example :
    let M₁ := limitedSupplyMechanism (ι := Fin 3) 2 symmetricSecondPrice
    let M₂ := limitedSupplyMechanism (ι := Fin 3) 2 expectedRSPE
    M₁.IsDSIC ∧ M₁.IsIR ∧ M₁.IsNormalized ∧
      (∀ b : Fin 3 → ℝ, 0 ≤ b → M₁.allocation b ∈ MultiUnit.multiUnitFeasible 2) ∧
      IsCompetitive (optimalProfitTwoLimited 2) (fun b => ∑ i, M₁.payment b i) 2 ∧
      M₂.IsDSIC ∧ M₂.IsIR ∧ M₂.IsNormalized ∧
      (∀ b : Fin 3 → ℝ, 0 ≤ b → ∑ i, M₂.allocation b i ≤ 2) ∧
      IsCompetitive (optimalProfitTwoLimited 2) (fun b => ∑ i, M₂.payment b i) 4 := by
  refine ⟨limitedSupplyMechanism_isDSIC 2 symmetricSecondPrice_isDSIC
      (IsBinary.isUnitAlloc symmetricSecondPrice_isBinary),
    limitedSupplyMechanism_isIR 2 (IsBinary.isUnitAlloc symmetricSecondPrice_isBinary),
    limitedSupplyMechanism_isNormalized 2 _,
    fun b hb => limitedSupplyAlloc_mem_multiUnitFeasible 2 symmetricSecondPrice_isBinary hb,
    limitedSupplyMechanism_isCompetitive 2 symmetricSecondPrice_isDSIC
      symmetricSecondPrice_isNormalized (IsBinary.isUnitAlloc symmetricSecondPrice_isBinary)
      (by simpa only [Fintype.card_fin, show min 2 3 = 2 by decide, Nat.cast_ofNat] using
        symmetricSecondPrice_isCompetitive (ι := Fin (min 2 (Fintype.card (Fin 3))))),
    limitedSupplyMechanism_isDSIC 2 expectedRSPE_isDSIC expectedRSPE_isUnitAlloc,
    limitedSupplyMechanism_isIR 2 expectedRSPE_isUnitAlloc,
    limitedSupplyMechanism_isNormalized 2 _,
    fun b hb => sum_limitedSupplyAlloc_le 2 expectedRSPE_isUnitAlloc hb,
    limitedSupplyMechanism_isCompetitive 2 expectedRSPE_isDSIC expectedRSPE_isNormalized
      expectedRSPE_isUnitAlloc expectedRSPE_isCompetitive⟩

/-! ### CEPE (`Lemmas 13.47–13.48`, `Theorem 13.49`, digital goods instantiation) -/

/-- Concrete evaluations of `roundDown 2` on positive, zero, and negative inputs. -/
example :
    roundDown 2 0 3 = 2 ∧ roundDown 2 0 0 = 0 ∧ roundDown 2 0 (-1) = 0 := by
  refine ⟨?_, roundDown_of_nonpos 2 0 le_rfl, roundDown_of_nonpos 2 0 (by norm_num)⟩
  have h3 : (0 : ℝ) < 3 := by norm_num
  simp only [roundDown, h3, ↓reduceIte, sub_zero, add_zero]
  have hfl : ⌊Real.logb 2 3⌋ = 1 := by
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩
    · rw [Int.cast_one, Real.le_logb_iff_rpow_le (by norm_num) h3]; norm_num
    · rw [Int.cast_one, Real.logb_lt_iff_lt_rpow (by norm_num) h3]; norm_num
  rw [hfl]
  norm_num

/-- Concrete **Lemma 13.47** (`α = 4`, `ρ = 2`, exact consensus probability `1 / 2`) and
**Lemma 13.48** (`α = 2`, `V = 4`, exact expectation `4 / (2 * Real.log 2)`). -/
example :
    volume.real {u ∈ Set.Icc (0 : ℝ) 1 |
        ∀ V' ∈ Set.Icc ((10 : ℝ) / 2) 10, roundDown 4 u V' = roundDown 4 u 10} = 1 / 2 ∧
      ∫ u in (0 : ℝ)..1, roundDown 2 u 4 = 4 / (2 * Real.log 2) := by
  constructor
  · rw [volume_real_roundDown_consensus (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    have hlog : Real.logb 4 2 = 1 / 2 := by
      have h4 : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
      rw [Real.logb, h4, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
      have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
      field_simp [h2]
    rw [hlog]; norm_num
  · rw [integral_roundDown (by norm_num) (by norm_num)]
    norm_num

/-- Concrete digital goods CEPE instantiation (**Theorem 13.49**, `α = 2`) on `Fin 3` with
`v = (1, 1, 1)` (`m = 3` winners): `2 * Real.log 2`-competitive against `ℱ⁽²⁾` and truthful for
every bidder `i` with probability at least `1 - Real.logb 2 (3 / 2) ≥ 1 - 1 / (2 * Real.log 2)`. -/
example :
    IsCompetitive (optimalProfitTwo (ι := Fin 3))
        (cepeExpectedProfit optimalProfitTwo profitExtract (fun _ => 0) 2) (2 * Real.log 2) ∧
      ∀ i : Fin 3,
        IsTruthfulWithHighProbAt (cepeDigitalGoods 2) ![(1 : ℝ), 1, 1] i (Real.logb 2 (3 / 2)) ∧
          Real.logb 2 (3 / 2) ≤ 1 / (2 * Real.log 2) := by
  constructor
  · simpa only [show ((2 : ℝ) * Real.log 2) / (2 - 1) = 2 * Real.log 2 by norm_num] using
      cepeDigitalGoods_isCompetitive (ι := Fin 3) (by norm_num : (1 : ℝ) < 2)
  · intro i
    let v : Fin 3 → ℝ := ![(1 : ℝ), 1, 1]
    have hv : 0 ≤ v := fun j => by fin_cases j <;> norm_num [v]
    have hF2 : optimalProfitTwo v = 1 * ((univ : Finset (Fin 3)).card : ℝ) := by
      apply le_antisymm
      · refine singlePriceProfitOn_le (by simp) fun j _ _ => ?_
        have hbj : v j = 1 := by fin_cases j <;> rfl
        rw [hbj, one_mul, one_mul]
        exact_mod_cast card_filter_le (univ : Finset (Fin 3)) _
      · exact mul_card_le_singlePriceProfitOn (m := 2) (s := univ) (W := univ) (b := v) (p := 1)
          (fun j _ => hv j) subset_rfl (by decide) fun j _ => by fin_cases j <;> norm_num [v]
    have hres := cepeDigitalGoods_truthful_of_winners (α := 2) (by norm_num) hv (W := univ)
      (p := 1) zero_le_one (by decide) (fun j _ => by fin_cases j <;> norm_num [v]) hF2
      (by simp only [card_univ, Fintype.card_fin]; norm_num) i
    simpa only [card_univ, Fintype.card_fin, Nat.cast_ofNat,
      show (3 : ℝ) / ((3 : ℝ) - 1) = 3 / 2 by norm_num,
      show (3 : ℝ) - 1 = 2 by norm_num] using hres

/-- Boundary witness for the `3 ≤ W.card` hypothesis in `cepeDigitalGoods_truthful_of_winners`:
at `m = 2` winners on `Fin 2` (`v = (1, 1)`), `ℱ⁽²⁾(v) = 2` drops to `ℱ⁽²⁾(update v 0 0) = 0`. -/
example :
    optimalProfitTwo ![(1 : ℝ), 1] = 2 ∧
      optimalProfitTwo (Function.update ![(1 : ℝ), 1] 0 0) = 0 := by
  let v : Fin 2 → ℝ := ![(1 : ℝ), 1]
  have hv : 0 ≤ v := fun j => by fin_cases j <;> norm_num [v]
  change optimalProfitTwo v = 2 ∧ optimalProfitTwo (Function.update v 0 0) = 0
  constructor
  · apply le_antisymm
    · refine singlePriceProfitOn_le (by norm_num) fun j _ _ => ?_
      have hbj : v j = 1 := by fin_cases j <;> rfl
      rw [hbj, one_mul]
      exact_mod_cast (card_filter_le (univ : Finset (Fin 2)) _).trans (by decide)
    · have hle := mul_card_le_singlePriceProfitOn (m := 2) (s := univ) (W := univ) (b := v) (p := 1)
        (fun j _ => hv j) subset_rfl (by decide) fun j _ => by fin_cases j <;> norm_num [v]
      simpa only [card_univ, Fintype.card_fin, Nat.cast_ofNat, one_mul] using hle
  · apply le_antisymm
    · refine singlePriceProfitOn_le le_rfl fun j _ hj => ?_
      fin_cases j
      · dsimp only
        rw [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl, Function.update_self, zero_mul]
      · dsimp only at hj ⊢
        rw [show (⟨1, by decide⟩ : Fin 2) = 1 from rfl] at hj
        have hfilt : (univ.filter fun i : Fin 2 =>
            Function.update v 0 0 1 ≤ Function.update v 0 0 i) = {1} := by
          ext i
          simp only [mem_filter, mem_univ, true_and, mem_singleton]
          fin_cases i <;> simp [v]
        rw [hfilt, card_singleton] at hj
        omega
    · exact singlePriceProfitOn_nonneg fun i _ => update_nonneg hv 0 le_rfl i

end CslibFrontierTests.GameTheory.DigitalGoodsBoundsCEPE
