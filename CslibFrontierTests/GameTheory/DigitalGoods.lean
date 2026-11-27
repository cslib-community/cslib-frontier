/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.GameTheory.Mechanism.DigitalGoods.ProfitExtraction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Prior-free digital goods auctions tests

Non-vacuous client checks and boundary witnesses for
`CslibFrontier.GameTheory.Mechanism.DigitalGoods.ProfitExtraction`:

* single-price profit benchmarks `ℱ` and `ℱ⁽²⁾` on concrete profiles (distinct bids, ties,
  all-zero bids, single bidder, empty bidder set) and agreement with `Fintype.orderStatistic`;
* `ProfitExtract_R`: successful extraction with ties, growth to a larger group size (`k = 3` over
  `k = 2`), failure (`ℱ(b) < R`), and the boundaries `R = 0` (nonempty and empty subset) and
  `R < 0`;
* contrast example: a first-price digital goods auction fails `IsDSIC`, and `IsCompetitive` holds
  for `RSPE` at `β = 4` while failing at `β = 3` (and failing for `β < 0`, and for the zero
  auction);
* `RSPE` on the tight two-bid profile `(1, 2)` across all four partitions (`0, 1, 1, 0`, expected
  profit `1/2`, ratio `4`) and a checked counterexample `b = (1, 1)` refuting the literal equality
  `profit(rspe s) = min(R', R'')` from [HartlineKarlin2007], p. 348 when `R' = R'' > 0`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.DigitalGoods

open Finset
open Cslib.GameTheory.SingleParameter
open Cslib.GameTheory.SingleParameter.DigitalGoods

private lemma card_filter_eq {ι : Type*} {s t : Finset ι} {p : ι → Prop} [DecidablePred p]
    (h : ∀ x, x ∈ s ∧ p x ↔ x ∈ t) : (s.filter p).card = t.card :=
  congrArg Finset.card (by ext x; simpa only [mem_filter] using h x)

/-! ### Benchmarks `ℱ` and `ℱ⁽²⁾` -/

/-- Compute `ℱ` and `ℱ⁽²⁾` on `![(1 : ℝ), 2]`: both equal `2`. -/
private theorem optimalProfit_one_two :
    optimalProfit ![(1 : ℝ), 2] = 2 ∧ optimalProfitTwo ![(1 : ℝ), 2] = 2 := by
  let b : Fin 2 → ℝ := ![(1 : ℝ), 2]
  have hb : ∀ i ∈ (univ : Finset (Fin 2)), 0 ≤ b i := fun i _ => by
    fin_cases i <;> norm_num [b]
  have hlt (j : Fin 2) :
      b j * ((univ.filter fun i : Fin 2 => b j ≤ b i).card : ℝ) ≤ 2 := by
    fin_cases j
    · dsimp only
      have h0 : (univ.filter fun i : Fin 2 => b 0 ≤ b i).card = 2 := by
        rw [card_filter_eq (t := ({0, 1} : Finset (Fin 2))) fun x => by
          fin_cases x <;> norm_num [b]]
        decide
      change b 0 * ((univ.filter fun i : Fin 2 => b 0 ≤ b i).card : ℝ) ≤ 2
      rw [h0]; norm_num [b]
    · dsimp only
      have h1 : (univ.filter fun i : Fin 2 => b 1 ≤ b i).card = 1 := by
        rw [card_filter_eq (t := ({1} : Finset (Fin 2))) fun x => by
          fin_cases x <;> norm_num [b]]
        decide
      change b 1 * ((univ.filter fun i : Fin 2 => b 1 ≤ b i).card : ℝ) ≤ 2
      rw [h1]; norm_num [b]
  constructor
  · apply le_antisymm
    · exact singlePriceProfitOn_le (by norm_num) fun j _ _ => hlt j
    · have hle := mul_card_le_singlePriceProfitOn (m := 1) (s := univ) (W := {1}) (b := b)
        (p := 2) hb (subset_univ _) (by decide) fun i hi => by
          rw [mem_singleton.1 hi]; norm_num [b]
      simpa only [card_singleton, Nat.cast_one, mul_one] using hle
  · apply le_antisymm
    · exact singlePriceProfitOn_le (by norm_num) fun j _ _ => hlt j
    · have hle := mul_card_le_singlePriceProfitOn (m := 2) (s := univ) (W := {0, 1}) (b := b)
        (p := 1) hb (subset_univ _) (by decide) fun i _ => by fin_cases i <;> norm_num [b]
      have hcard : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
      simpa only [hcard, Nat.cast_ofNat, one_mul] using hle

/-- Upper bound helper: on `(1, 2, 2)`, every single-price revenue is at most `4`. -/
private theorem singlePriceProfitOn_one_two_two_le (m : ℕ) :
    singlePriceProfitOn m (univ : Finset (Fin 3)) ![(1 : ℝ), 2, 2] ≤ 4 := by
  let b : Fin 3 → ℝ := ![(1 : ℝ), 2, 2]
  refine singlePriceProfitOn_le (by norm_num) fun j _ _ => ?_
  fin_cases j
  · have hc : (univ.filter fun i : Fin 3 => b 0 ≤ b i).card = 3 := by
      rw [card_filter_eq (t := univ) fun x => by fin_cases x <;> norm_num [b]]
      decide
    change b 0 * ((univ.filter fun i : Fin 3 => b 0 ≤ b i).card : ℝ) ≤ 4
    rw [hc]; norm_num [b]
  · have hc : (univ.filter fun i : Fin 3 => b 1 ≤ b i).card = 2 := by
      rw [card_filter_eq (t := ({1, 2} : Finset (Fin 3))) fun x => by
        fin_cases x <;> simp [b]]
      decide
    change b 1 * ((univ.filter fun i : Fin 3 => b 1 ≤ b i).card : ℝ) ≤ 4
    rw [hc]; norm_num [b]
  · have hc : (univ.filter fun i : Fin 3 => b 2 ≤ b i).card = 2 := by
      rw [card_filter_eq (t := ({1, 2} : Finset (Fin 3))) fun x => by
        fin_cases x <;> simp [b]]
      decide
    change b 2 * ((univ.filter fun i : Fin 3 => b 2 ≤ b i).card : ℝ) ≤ 4
    rw [hc]; norm_num [b]

/-- Concrete benchmark values with ties: on `(1, 2, 2)`, both `ℱ` and `ℱ⁽²⁾` equal `4`
(attained at price `2` with `2` winners, beating price `1` with `3` winners). -/
example :
    optimalProfit ![(1 : ℝ), 2, 2] = 4 ∧ optimalProfitTwo ![(1 : ℝ), 2, 2] = 4 := by
  let b : Fin 3 → ℝ := ![(1 : ℝ), 2, 2]
  have hb : ∀ i ∈ (univ : Finset (Fin 3)), 0 ≤ b i := fun i _ => by
    fin_cases i <;> norm_num [b]
  have hlow (m : ℕ) (hm : m ≤ 2) : (4 : ℝ) ≤ singlePriceProfitOn m univ b := by
    have hcard : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
    have hle := mul_card_le_singlePriceProfitOn (m := m) (s := univ) (W := {1, 2}) (b := b)
      (p := 2) hb (subset_univ _) (by rw [hcard]; exact hm) fun i hi => by
        simp only [mem_insert, mem_singleton] at hi
        rcases hi with rfl | rfl <;> norm_num [b]
    rw [hcard] at hle
    norm_num at hle
    exact hle
  exact ⟨le_antisymm (singlePriceProfitOn_one_two_two_le 1) (hlow 1 (by decide)),
    le_antisymm (singlePriceProfitOn_one_two_two_le 2) (hlow 2 le_rfl)⟩

/-- All-equal ties: on `(1, 1, 1)`, `ℱ = ℱ⁽²⁾ = 3`. -/
example :
    optimalProfit ![(1 : ℝ), 1, 1] = 3 ∧ optimalProfitTwo ![(1 : ℝ), 1, 1] = 3 := by
  let b : Fin 3 → ℝ := ![(1 : ℝ), 1, 1]
  have hb : ∀ i ∈ (univ : Finset (Fin 3)), 0 ≤ b i := fun i _ => by
    fin_cases i <;> norm_num [b]
  have hup (m : ℕ) : singlePriceProfitOn m univ b ≤ 3 :=
    singlePriceProfitOn_le (by norm_num) fun j _ _ => by
      have hc : (univ.filter fun i : Fin 3 => b j ≤ b i).card ≤ 3 :=
        (card_filter_le _ _).trans (by decide)
      have hcR : ((univ.filter fun i : Fin 3 => b j ≤ b i).card : ℝ) ≤ 3 := by exact_mod_cast hc
      have hbj : b j = 1 := by fin_cases j <;> norm_num [b]
      calc b j * ((univ.filter fun i : Fin 3 => b j ≤ b i).card : ℝ)
          = ((univ.filter fun i : Fin 3 => b j ≤ b i).card : ℝ) := by rw [hbj, one_mul]
        _ ≤ 3 := hcR
  have hlow (m : ℕ) (hm : m ≤ 3) : (3 : ℝ) ≤ singlePriceProfitOn m univ b := by
    have hcard : (univ : Finset (Fin 3)).card = 3 := by decide
    have hle := mul_card_le_singlePriceProfitOn (m := m) (s := univ) (W := univ) (b := b)
      (p := 1) hb subset_rfl (by rw [hcard]; exact hm) fun i _ => by fin_cases i <;> norm_num [b]
    rw [hcard] at hle
    norm_num at hle
    exact hle
  exact ⟨le_antisymm (hup 1) (hlow 1 (by decide)), le_antisymm (hup 2) (hlow 2 (by decide))⟩

/-- All-zero tie boundary: `ℱ(0, 0) = 0` and `ℱ⁽²⁾(0, 0) = 0`. -/
example :
    optimalProfit ![(0 : ℝ), 0] = 0 ∧ optimalProfitTwo ![(0 : ℝ), 0] = 0 := by
  have h0 (m : ℕ) : singlePriceProfitOn m (univ : Finset (Fin 2)) ![(0 : ℝ), 0] = 0 :=
    le_antisymm (singlePriceProfitOn_le le_rfl fun j _ _ => by
      have : ![(0 : ℝ), 0] j = 0 := by fin_cases j <;> rfl
      rw [this, zero_mul])
      (singlePriceProfitOn_nonneg fun i _ => by fin_cases i <;> norm_num)
  exact ⟨h0 1, h0 2⟩

/-- Fewer than two bidders: for `Fin 1` with bid `5`, `ℱ = 5` while `ℱ⁽²⁾ = 0`. -/
example : optimalProfit ![(5 : ℝ)] = 5 ∧ optimalProfitTwo ![(5 : ℝ)] = 0 := by
  refine ⟨le_antisymm ?_ ?_, singlePriceProfitOn_eq_zero_of_card_lt _ (by decide)⟩
  · refine singlePriceProfitOn_le (by norm_num) fun j _ _ => ?_
    fin_cases j
    have hc : (univ.filter fun i : Fin 1 => ![(5 : ℝ)] 0 ≤ ![(5 : ℝ)] i).card ≤ 1 :=
      (card_filter_le _ _).trans (by decide)
    have hcR : ((univ.filter fun i : Fin 1 => ![(5 : ℝ)] 0 ≤ ![(5 : ℝ)] i).card : ℝ) ≤ 1 := by
      exact_mod_cast hc
    calc ![(5 : ℝ)] 0 * ((univ.filter fun i : Fin 1 => ![(5 : ℝ)] 0 ≤ ![(5 : ℝ)] i).card : ℝ)
        = 5 * ((univ.filter fun i : Fin 1 => ![(5 : ℝ)] 0 ≤ ![(5 : ℝ)] i).card : ℝ) := by norm_num
      _ ≤ 5 * 1 := by linarith
      _ = 5 := mul_one 5
  · have hle := mul_card_le_singlePriceProfitOn (m := 1) (s := univ) (W := {0}) (b := ![(5 : ℝ)])
      (p := 5) (fun i _ => by fin_cases i; norm_num) (subset_univ _) (by decide)
      fun i _ => by fin_cases i; norm_num
    simpa only [card_singleton, Nat.cast_one, mul_one] using hle

/-- Empty bidder pool (`Fin 0`): both `ℱ` and `ℱ⁽²⁾` equal `0`. -/
example (b : Fin 0 → ℝ) : optimalProfit b = 0 ∧ optimalProfitTwo b = 0 :=
  ⟨singlePriceProfitOn_eq_zero_of_card_lt b (by decide),
    singlePriceProfitOn_eq_zero_of_card_lt b (by decide)⟩

/-- Order-statistic bridge (`singlePriceProfitOn_eq_sup_orderStatistic`) agrees with the
sorting-free formula on `![(1 : ℝ), 2, 2]` with `m = 2`. -/
example :
    optimalProfitTwo ![(1 : ℝ), 2, 2] =
      (Icc 2 3).sup' (nonempty_Icc.2 (by decide)) fun k : ℕ =>
        (k : ℝ) * Fintype.orderStatistic ![(1 : ℝ), 2, 2] (3 - k) :=
  singlePriceProfitOn_eq_sup_orderStatistic (ι := Fin 3) (m := 2) (by decide) (by decide)
    fun i => by fin_cases i <;> norm_num

/-! ### `ProfitExtract_R` on success, failure, and boundaries -/

/-- `ProfitExtract_4` succeeds on `(1, 2, 2)` with `k = 2`: bidders `1, 2` win and pay `2`, bidder
`0` loses and pays `0`, total profit `4`. -/
example :
    profitExtractSize (univ : Finset (Fin 3)) 4 ![(1 : ℝ), 2, 2] = 2 ∧
      (profitExtract 4).allocation ![(1 : ℝ), 2, 2] 0 = 0 ∧
      (profitExtract 4).allocation ![(1 : ℝ), 2, 2] 1 = 1 ∧
      (profitExtract 4).allocation ![(1 : ℝ), 2, 2] 2 = 1 ∧
      (profitExtract 4).payment ![(1 : ℝ), 2, 2] 0 = 0 ∧
      (profitExtract 4).payment ![(1 : ℝ), 2, 2] 1 = 2 ∧
      (profitExtract 4).payment ![(1 : ℝ), 2, 2] 2 = 2 ∧
      ∑ i : Fin 3, (profitExtract 4).payment ![(1 : ℝ), 2, 2] i = 4 := by
  classical
  let b : Fin 3 → ℝ := ![(1 : ℝ), 2, 2]
  have hfs : ((Icc 1 3 : Finset ℕ).filter fun k : ℕ =>
      k ≤ (univ.filter fun i : Fin 3 => (4 : ℝ) / (k : ℝ) ≤ b i).card) = {2} := by
    ext k
    simp only [mem_filter, mem_Icc, mem_singleton]
    constructor
    · rintro ⟨⟨hk1, hk3⟩, hc⟩
      interval_cases k
      · have h0 : (univ.filter fun i : Fin 3 => (4 : ℝ) / ((1 : ℕ) : ℝ) ≤ b i).card = 0 := by
          rw [card_filter_eq (t := (∅ : Finset (Fin 3))) fun x => by
            fin_cases x <;> simp [b] <;> norm_num]
          rfl
        omega
      · rfl
      · have h2 : (univ.filter fun i : Fin 3 => (4 : ℝ) / ((3 : ℕ) : ℝ) ≤ b i).card = 2 := by
          rw [card_filter_eq (t := ({1, 2} : Finset (Fin 3))) fun x => by
            fin_cases x <;> simp [b] <;> norm_num]
          decide
        omega
    · rintro rfl
      refine ⟨⟨by decide, by decide⟩, ?_⟩
      have h2 : (univ.filter fun i : Fin 3 => (4 : ℝ) / ((2 : ℕ) : ℝ) ≤ b i).card = 2 := by
        rw [card_filter_eq (t := ({1, 2} : Finset (Fin 3))) fun x => by
          fin_cases x <;> simp [b] <;> norm_num]
        decide
      omega
  have hK : profitExtractSize (univ : Finset (Fin 3)) 4 b = 2 := by
    unfold profitExtractSize
    have h4 : (0 : ℝ) ≤ 4 := by norm_num
    simp only [h4, card_univ, Fintype.card_fin, ↓reduceIte]
    have hne : ((Icc 1 3).filter fun k : ℕ =>
        k ≤ (univ.filter fun i : Fin 3 => (4 : ℝ) / (k : ℝ) ≤ b i).card).Nonempty := by
      rw [show ((Icc 1 3 : Finset ℕ).filter fun k : ℕ =>
          k ≤ (univ.filter fun i : Fin 3 => (4 : ℝ) / (k : ℝ) ≤ b i).card) = {2} from hfs]
      exact singleton_nonempty 2
    simp only [hne, ↓reduceDIte]
    apply le_antisymm
    · refine max'_le _ hne 2 fun k hk => ?_
      have : k ∈ ({2} : Finset ℕ) := by rw [← hfs]; exact hk
      exact (mem_singleton.1 this).le
    · refine le_max' _ 2 ?_
      have : (2 : ℕ) ∈ ({2} : Finset ℕ) := mem_singleton_self 2
      rwa [← hfs] at this
  refine ⟨hK, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold profitExtract profitExtractOn; dsimp only; rw [hK]; norm_num [b]
  · unfold profitExtract profitExtractOn; dsimp only; rw [hK]; norm_num [b]
  · unfold profitExtract profitExtractOn; dsimp only; rw [hK]; norm_num [b]
  · unfold profitExtract profitExtractOn; dsimp only; rw [hK]; norm_num [b]
  · unfold profitExtract profitExtractOn; dsimp only; rw [hK]; norm_num [b]
  · unfold profitExtract profitExtractOn; dsimp only; rw [hK]; norm_num [b]
  · have hb : 0 ≤ b := fun i => by fin_cases i <;> norm_num [b]
    refine sum_payment_profitExtract_of_le (by norm_num) hb ?_
    have hcard : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
    have hle := mul_card_le_singlePriceProfitOn (m := 1) (s := univ) (W := {1, 2}) (b := b)
      (p := 2) (fun i _ => hb i) (subset_univ _) (by decide) fun i hi => by
        simp only [mem_insert, mem_singleton] at hi
        rcases hi with rfl | rfl <;> norm_num [b]
    rw [hcard] at hle
    norm_num at hle
    exact hle

/-- With ties at `(2, 2, 2)` and `R = 4`, `k = 2` is feasible but `k = 3` is maximal, so all three
bidders win and each pays `4 / 3` (total profit `4`). -/
example :
    profitExtractSize (univ : Finset (Fin 3)) 4 ![(2 : ℝ), 2, 2] = 3 ∧
      (profitExtract 4).payment ![(2 : ℝ), 2, 2] 0 = 4 / 3 ∧
      ∑ i : Fin 3, (profitExtract 4).payment ![(2 : ℝ), 2, 2] i = 4 := by
  classical
  let b : Fin 3 → ℝ := ![(2 : ℝ), 2, 2]
  have hmem3 : 3 ∈ (Icc 1 3 : Finset ℕ).filter fun k : ℕ =>
      k ≤ (univ.filter fun i : Fin 3 => (4 : ℝ) / (k : ℝ) ≤ b i).card := by
    refine mem_filter.2 ⟨by decide, ?_⟩
    have : (univ.filter fun i : Fin 3 => (4 : ℝ) / ((3 : ℕ) : ℝ) ≤ b i) = univ :=
      filter_true_of_mem fun i _ => by fin_cases i <;> norm_num [b]
    rw [this]; decide
  have hK : profitExtractSize (univ : Finset (Fin 3)) 4 b = 3 := by
    unfold profitExtractSize
    have h4 : (0 : ℝ) ≤ 4 := by norm_num
    simp only [h4, card_univ, Fintype.card_fin, ↓reduceIte]
    have hne : ((Icc 1 3).filter fun k : ℕ =>
        k ≤ (univ.filter fun i : Fin 3 => (4 : ℝ) / (k : ℝ) ≤ b i).card).Nonempty := ⟨3, hmem3⟩
    simp only [hne, ↓reduceDIte]
    exact le_antisymm
      (max'_le _ hne 3 fun k hk => (mem_Icc.1 (mem_filter.1 hk).1).2)
      (le_max' _ 3 hmem3)
  refine ⟨hK, ?_, ?_⟩
  · unfold profitExtract profitExtractOn; dsimp only; rw [hK]; norm_num [b]
  · have hb : 0 ≤ b := fun i => by fin_cases i <;> norm_num [b]
    refine sum_payment_profitExtract_of_le (by norm_num) hb ?_
    have hcard : (univ : Finset (Fin 3)).card = 3 := by decide
    have hle := mul_card_le_singlePriceProfitOn (m := 1) (s := univ) (W := univ) (b := b)
      (p := 2) (fun i _ => hb i) subset_rfl (by decide)
      fun i _ => by fin_cases i <;> norm_num [b]
    rw [hcard] at hle
    norm_num at hle
    exact (by norm_num : (4 : ℝ) ≤ 6).trans hle

/-- Failure instance: `R = 5 > ℱ(1, 2, 2) = 4`, so `ProfitExtract_5` collects profit `0`. -/
example :
    ∑ i : Fin 3, (profitExtract 5).payment ![(1 : ℝ), 2, 2] i = 0 := by
  have hgt : ¬ (5 : ℝ) ≤ optimalProfit ![(1 : ℝ), 2, 2] :=
    not_le_of_gt (lt_of_le_of_lt (singlePriceProfitOn_one_two_two_le 1) (by norm_num))
  rw [sum_payment_profitExtractOn univ (by norm_num) fun i _ => by fin_cases i <;> norm_num]
  exact ite_eq_right hgt

/-- Boundary `R = 0`: on nonempty `(0, 3)`, every bidder wins at price `0` and profit is `0`;
on `∅`, profit is `0`. On `R = -1 < 0`, nobody wins and payment is `0`, still DSIC and IR. -/
example :
    (profitExtract 0).allocation ![(0 : ℝ), 3] 0 = 1 ∧
      (profitExtract 0).allocation ![(0 : ℝ), 3] 1 = 1 ∧
      ∑ i : Fin 2, (profitExtract 0).payment ![(0 : ℝ), 3] i = 0 ∧
      ∑ i : Fin 2, (profitExtractOn ∅ 0).payment ![(0 : ℝ), 3] i = 0 ∧
      (profitExtract (-1)).allocation ![(0 : ℝ), 3] 1 = 0 ∧
      (profitExtract (ι := Fin 2) (-1)).IsDSIC ∧
      (profitExtract (ι := Fin 2) (-1)).IsIR := by
  classical
  let b : Fin 2 → ℝ := ![(0 : ℝ), 3]
  have h2 : 2 ∈ (Icc 1 2 : Finset ℕ).filter fun k : ℕ =>
      k ≤ (univ.filter fun i : Fin 2 => (0 : ℝ) / (k : ℝ) ≤ b i).card := by
    refine mem_filter.2 ⟨by decide, ?_⟩
    have : (univ.filter fun i : Fin 2 => (0 : ℝ) / ((2 : ℕ) : ℝ) ≤ b i) = univ :=
      filter_true_of_mem fun i _ => by fin_cases i <;> norm_num [b]
    rw [this]; decide
  have hK0 : profitExtractSize (univ : Finset (Fin 2)) 0 b = 2 := by
    unfold profitExtractSize
    have h0 : (0 : ℝ) ≤ 0 := le_rfl
    simp only [h0, card_univ, Fintype.card_fin, ↓reduceIte]
    have hne : ((Icc 1 2).filter fun k : ℕ =>
        k ≤ (univ.filter fun i : Fin 2 => (0 : ℝ) / (k : ℝ) ≤ b i).card).Nonempty := ⟨2, h2⟩
    simp only [hne, ↓reduceDIte]
    exact le_antisymm (max'_le _ hne 2 fun k hk => (mem_Icc.1 (mem_filter.1 hk).1).2)
      (le_max' _ 2 h2)
  have hKneg : profitExtractSize (univ : Finset (Fin 2)) (-1) b = 0 := by
    unfold profitExtractSize
    have hn : ¬ (0 : ℝ) ≤ -1 := by norm_num
    simp only [hn, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, profitExtractOn_isDSIC _ _, profitExtractOn_isIR _ _⟩
  · unfold profitExtract profitExtractOn; dsimp only; rw [hK0]; norm_num [b]
  · unfold profitExtract profitExtractOn; dsimp only; rw [hK0]; norm_num [b]
  · refine sum_payment_profitExtract_of_le le_rfl (fun i => by fin_cases i <;> norm_num [b]) ?_
    exact singlePriceProfitOn_nonneg fun i _ => by fin_cases i <;> norm_num [b]
  · rw [sum_payment_profitExtractOn ∅ le_rfl fun _ hi => (notMem_empty _ hi).elim]
    simp only [optimalProfitOn, singlePriceProfitOn_empty, le_refl, ↓reduceIte]
  · unfold profitExtract profitExtractOn; dsimp only; rw [hKneg]; norm_num

/-- Non-truthful contrast: a pay-your-bid digital goods auction (every bidder receives the item and
pays its own bid) is **not** DSIC (`Fin 1`). -/
example : ¬ (⟨fun _ _ => (1 : ℝ), fun b i => b i⟩ : Mechanism (Fin 1)).IsDSIC := by
  intro h
  have hdev := h 0 ![(1 : ℝ)] 2 (fun i => by fin_cases i; norm_num) (by norm_num)
  simp only [Mechanism.utility, Function.update_self] at hdev
  norm_num at hdev

/-! ### `IsCompetitive` contrast -/

/-- The `4`-competitiveness holds on `Fin 2`, while `β = 3` fails `IsCompetitive` (and the
always-zero auction is not `β`-competitive for any `β : ℝ`). -/
example :
    IsCompetitive (optimalProfitTwo (ι := Fin 2)) rspeExpectedProfit 4 ∧
      ¬ IsCompetitive (optimalProfitTwo (ι := Fin 2)) rspeExpectedProfit 3 ∧
      (∀ β : ℝ, ¬ IsCompetitive (optimalProfitTwo (ι := Fin 2)) (fun _ => 0) β) ∧
      ¬ IsCompetitive (optimalProfitTwo (ι := Fin 1)) rspeExpectedProfit (-1) := by
  refine ⟨rspe_isCompetitive, ?_, ?_, ?_⟩
  · intro h3
    have h4 : (4 : ℝ) ≤ 3 := (isLeast_rspe_competitiveRatio (ι := Fin 2) le_rfl).2 h3
    norm_num at h4
  · intro β hβ
    have h := hβ.2 ![(1 : ℝ), 2] (fun i => by fin_cases i <;> norm_num)
    rw [optimalProfit_one_two.2, mul_zero] at h
    norm_num at h
  · intro hneg
    have : (0 : ℝ) ≤ -1 := hneg.1
    norm_num at this

/-! ### `RSPE` on concrete partitions and counterexample to `profit = min(R', R'')` -/

/-- Singleton benchmark helper: `optimalProfitOn {a} b = b a` for nonnegative `b a`. -/
private theorem optimalProfitOn_singleton {ι : Type*} (a : ι) {b : ι → ℝ} (ha : 0 ≤ b a) :
    optimalProfitOn {a} b = b a := by
  apply le_antisymm
  · refine singlePriceProfitOn_le ha fun j hj _ => ?_
    rw [mem_singleton.1 hj]
    have hcard : (({a} : Finset ι).filter fun i => b a ≤ b i).card ≤ 1 :=
      (card_filter_le _ _).trans (by rw [card_singleton])
    have hcR : ((({a} : Finset ι).filter fun i => b a ≤ b i).card : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    calc b a * ((({a} : Finset ι).filter fun i => b a ≤ b i).card : ℝ)
        ≤ b a * 1 := mul_le_mul_of_nonneg_left hcR ha
      _ = b a := mul_one _
  · have hle := mul_card_le_singlePriceProfitOn (m := 1) (s := {a}) (W := {a}) (b := b)
      (p := b a) (fun i hi => by rw [mem_singleton.1 hi]; exact ha) subset_rfl
      (by rw [card_singleton]) fun i hi => by rw [mem_singleton.1 hi]
    simpa only [card_singleton, Nat.cast_one, mul_one] using hle

/-- Exact computation of `rspe` on **all four partitions** of the two-bid tight instance `(1, 2)`:
`∅ ↦ 0`, `{0} ↦ 1`, `{1} ↦ 1`, `{0, 1} ↦ 0`, so `𝔼[RSPE(1, 2)] = 1 / 2` and `ℱ⁽²⁾(1, 2) = 2`. -/
example :
    let b : Fin 2 → ℝ := ![(1 : ℝ), 2]
    ∑ i, (rspe (∅ : Finset (Fin 2))).payment b i = 0 ∧
      ∑ i, (rspe ({0} : Finset (Fin 2))).payment b i = 1 ∧
      ∑ i, (rspe ({1} : Finset (Fin 2))).payment b i = 1 ∧
      ∑ i, (rspe (univ : Finset (Fin 2))).payment b i = 0 ∧
      rspeExpectedProfit b = 1 / 2 ∧
      optimalProfitTwo b = 2 := by
  intro b
  have hb : 0 ≤ b := fun i => by fin_cases i <;> norm_num [b]
  have hF0 : optimalProfitOn ({0} : Finset (Fin 2)) b = 1 := by
    rw [optimalProfitOn_singleton 0 (hb 0)]; norm_num [b]
  have hF1 : optimalProfitOn ({1} : Finset (Fin 2)) b = 2 := by
    rw [optimalProfitOn_singleton 1 (hb 1)]; norm_num [b]
  have hF_empty : optimalProfitOn (∅ : Finset (Fin 2)) b = 0 := singlePriceProfitOn_empty 1 b
  have hF_all : optimalProfitOn (univ : Finset (Fin 2)) b = 2 := optimalProfit_one_two.1
  have hc0 : ({0} : Finset (Fin 2))ᶜ = {1} := by decide
  have hc1 : ({1} : Finset (Fin 2))ᶜ = {0} := by decide
  have p_empty : ∑ i, (rspe (∅ : Finset (Fin 2))).payment b i = 0 := by
    rw [sum_payment_rspe_eq ∅ hb, compl_empty, hF_empty, hF_all]; norm_num
  have p_0 : ∑ i, (rspe ({0} : Finset (Fin 2))).payment b i = 1 := by
    rw [sum_payment_rspe_eq {0} hb, hc0, hF0, hF1]; norm_num
  have p_1 : ∑ i, (rspe ({1} : Finset (Fin 2))).payment b i = 1 := by
    rw [sum_payment_rspe_eq {1} hb, hc1, hF0, hF1]; norm_num
  have p_univ : ∑ i, (rspe (univ : Finset (Fin 2))).payment b i = 0 := by
    rw [sum_payment_rspe_eq univ hb, compl_univ, hF_empty, hF_all]; norm_num
  refine ⟨p_empty, p_0, p_1, p_univ, ?_, optimalProfit_one_two.2⟩
  rw [rspeExpectedProfit_eq_div]
  have huniv : (univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, univ} := by decide
  rw [huniv]
  simp only [sum_insert (show (∅ : Finset (Fin 2)) ∉ ({({0}), {1}, univ} : Finset (Finset (Fin 2)))
      by decide),
    sum_insert (show ({0} : Finset (Fin 2)) ∉ ({{1}, univ} : Finset (Finset (Fin 2))) by decide),
    sum_insert (show ({1} : Finset (Fin 2)) ∉ ({univ} : Finset (Finset (Fin 2))) by decide),
    sum_singleton]
  rw [p_empty, p_0, p_1, p_univ]
  norm_num

/-- **Checked counterexample to [HartlineKarlin2007], p. 348's literal claim** that the profit of
`RSPE` equals `min(R', R'')`: on equal bids `(1, 1)` and partition `s = {0}`, `R' = R'' = 1`
so `min(R', R'') = 1`, yet **both** halves extract `1`, giving profit **`2 ≠ 1`**, and expected
profit **`1`** (ratio `2`, not `4`). -/
example :
    let b : Fin 2 → ℝ := ![(1 : ℝ), 1]
    let s : Finset (Fin 2) := {0}
    optimalProfitOn s b = 1 ∧
      optimalProfitOn sᶜ b = 1 ∧
      min (optimalProfitOn s b) (optimalProfitOn sᶜ b) = 1 ∧
      ∑ i, (rspe s).payment b i = 2 ∧
      ∑ i, (rspe s).payment b i ≠ min (optimalProfitOn s b) (optimalProfitOn sᶜ b) ∧
      rspeExpectedProfit b = 1 := by
  intro b s
  have hb : 0 ≤ b := fun i => by fin_cases i <;> norm_num [b]
  have hsingle (a : Fin 2) : optimalProfitOn ({a} : Finset (Fin 2)) b = 1 := by
    rw [optimalProfitOn_singleton a (hb a)]; fin_cases a <;> rfl
  have hF_empty : optimalProfitOn (∅ : Finset (Fin 2)) b = 0 := singlePriceProfitOn_empty 1 b
  have hF_all : optimalProfitOn (univ : Finset (Fin 2)) b = 2 := by
    refine le_antisymm (singlePriceProfitOn_le (by norm_num) fun j _ _ => ?_) ?_
    · have hc : (univ.filter fun i : Fin 2 => b j ≤ b i).card ≤ 2 :=
        (card_filter_le _ _).trans (by decide)
      have hcR : ((univ.filter fun i : Fin 2 => b j ≤ b i).card : ℝ) ≤ 2 := by exact_mod_cast hc
      have hbj : b j = 1 := by fin_cases j <;> rfl
      calc b j * ((univ.filter fun i : Fin 2 => b j ≤ b i).card : ℝ)
          = ((univ.filter fun i : Fin 2 => b j ≤ b i).card : ℝ) := by rw [hbj, one_mul]
        _ ≤ 2 := hcR
    · have hcard : (univ : Finset (Fin 2)).card = 2 := by decide
      have hle := mul_card_le_singlePriceProfitOn (m := 1) (s := univ) (W := univ) (b := b)
        (p := 1) (fun i _ => hb i) subset_rfl (by decide)
        fun i _ => by fin_cases i <;> norm_num [b]
      simpa only [hcard, Nat.cast_ofNat, one_mul] using hle
  have hsc : sᶜ = {1} := by decide
  have h1c : ({1} : Finset (Fin 2))ᶜ = {0} := by decide
  have hR' : optimalProfitOn s b = 1 := hsingle 0
  have hR'' : optimalProfitOn sᶜ b = 1 := hsc ▸ hsingle 1
  have p_0 : ∑ i, (rspe s).payment b i = 2 := by
    rw [sum_payment_rspe_eq s hb, hR', hR'']; norm_num
  have p_1 : ∑ i, (rspe ({1} : Finset (Fin 2))).payment b i = 2 := by
    rw [sum_payment_rspe_eq {1} hb, h1c, hsingle 0, hsingle 1]; norm_num
  have p_empty : ∑ i, (rspe (∅ : Finset (Fin 2))).payment b i = 0 := by
    rw [sum_payment_rspe_eq ∅ hb, compl_empty, hF_empty, hF_all]; norm_num
  have p_univ : ∑ i, (rspe (univ : Finset (Fin 2))).payment b i = 0 := by
    rw [sum_payment_rspe_eq univ hb, compl_univ, hF_empty, hF_all]; norm_num
  refine ⟨hR', hR'', by rw [hR', hR'']; norm_num, p_0, by rw [hR', hR'', p_0]; norm_num, ?_⟩
  rw [rspeExpectedProfit_eq_div]
  have huniv : (univ : Finset (Finset (Fin 2))) = {∅, s, {1}, univ} := by decide
  rw [huniv]
  simp only [sum_insert (show (∅ : Finset (Fin 2)) ∉ ({s, {1}, univ} : Finset (Finset (Fin 2)))
      by decide),
    sum_insert (show s ∉ ({{1}, univ} : Finset (Finset (Fin 2))) by decide),
    sum_insert (show ({1} : Finset (Fin 2)) ∉ ({univ} : Finset (Finset (Fin 2))) by decide),
    sum_singleton]
  rw [p_empty, p_0, p_1, p_univ]
  norm_num

/-- Non-vacuity of the headline `isLeast_rspe_competitiveRatio` on both `Fin 2` and `Fin 3`,
together with universal truthfulness (`rspe_isDSIC`) and individual rationality. -/
example :
    IsLeast {β : ℝ | IsCompetitive (optimalProfitTwo (ι := Fin 2)) rspeExpectedProfit β} 4 ∧
      IsLeast {β : ℝ | IsCompetitive (optimalProfitTwo (ι := Fin 3)) rspeExpectedProfit β} 4 ∧
      (∀ s : Finset (Fin 3), (rspe s).IsDSIC ∧ (rspe s).IsIR ∧ (rspe s).IsNormalized) :=
  ⟨isLeast_rspe_competitiveRatio (by decide),
    isLeast_rspe_competitiveRatio (by decide),
    fun s => ⟨rspe_isDSIC s, rspe_isIR s, rspe_isNormalized s⟩⟩

end CslibFrontierTests.GameTheory.DigitalGoods
