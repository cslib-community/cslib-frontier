/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.BiddingLanguage
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Combinatorial auction bidding languages: checked examples and boundary witnesses

Client test module for
`CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.BiddingLanguage` using only its public
surface (no `import all`), checking every concrete textbook example from [BlumrosenNisan2007],
§11.4 (pp. 279–283) and Exercise 11.5 (p. 299), together with model boundary witnesses:

1. **§11.4.1 `XOR` vs. `OR` examples (p. 280):**
   * `({0, 1}, 3) XOR ({2, 3}, 5)` vs. `({0, 1}, 3) OR ({2, 3}, 5)` on `Fin 4`: both value `{0, 2}`
     at `0` and `{0, 1}` at `3`, while `{0, 1, 2, 3}` is valued at `5` (`XOR`) vs. `8` (`OR`).
   * `({0, 1}, 3) OR ({0, 2}, 5)` on `Fin 3` values `{0, 1, 2}` at `5` (overlapping atoms).
   * Agreement between list evaluators (`xorBidEval`, `orBidEval`) and `BidFormula.ofXorList` /
     `BidFormula.ofOrList`.
2. **Empty-bundle and duplicate-atom boundaries:**
   * A positive empty-bundle atom `[(∅, 1)]` on `Bool` has `orBidEval [(∅, 1)] ∅ = 1` and violates
     `IsSuperadditive` (`1 + 1 > 1` on `{false}`, `{true}`), witnessing sharpness of the
     normalization hypothesis `orBidEval bids ∅ = 0` in `orBidEval_isSuperadditive`.
   * Duplicate identical nonempty bids `[({0}, 2), ({0}, 2)]` still conflict and evaluate to `2` on
     `{0}`, whereas duplicate empty-bundle bids `[(∅, 2), (∅, 2)]` are compatible and evaluate to
     `4` on `∅` (exercising `Fin bids.length` indexing).
3. **Additive and unit-demand separations on `Fin 3` (Definition 11.17, pp. 280–281):**
   * Additive `w = ![1, 2, 3]` has `OR` size `3` and requires `XOR` size `≥ 7 = 2^3 - 1`.
   * Unit-demand `w = ![2, 5, 1]` has `XOR` size `3` and has no `OR` representation.
4. **§11.4.2 formula example and Lemma 11.20 downward-sloping valuations (p. 281):**
   * `(({0, 1}, 3) XOR ({2}, 2)) OR ({3}, 5)` on `Fin 4` values `{0, 1, 2}` at `3` and `{0, 1, 3}`
     at `8`.
   * Downward-sloping symmetric valuation on `Fin 3` with marginals `(5, 3, 1)` requires `XOR` size
     `≥ 7`, admits no `OR` bid, and is represented by an `OR`-of-`XOR`s formula of size `9 = 3^2`;
     the `Empty` (`m = 0`) boundary has size `0 = 0^2`.
5. **§11.4.3 dummy-item example and Theorem 11.21 (pp. 282–283):**
   * `({0, d}, 1) OR ({1, d}, 1) OR ({2}, 1)` (`OR*` on `Fin 3` with `Unit` dummy) agrees with
     `(({0}, 1) XOR ({1}, 1)) OR ({2}, 1)` on every bundle `S : Finset (Fin 3)`.
   * Applying `exists_orStarBid_of_bidFormula` to the size-3 §11.4.2 formula yields an `OR*` bid of
     size `3` with `d ≤ 3.choose 2 = 3 ≤ 9 = 3^2` dummy items.
6. **Exercise 11.5 majority valuation lower bound (p. 299):**
   * Even `m = 4` (`Fin 4`): every `OR*` bid for `majorityValuation (Fin 4)` has size
     `≥ 6 = Nat.choose 4 2`.
   * Odd `m = 3` (`Fin 3`): `majorityValuation (Fin 3)` values `{0}` at `0`, `{0, 1}` at `1`, and
     `∅` at `0`, and every `OR*` bid representing it has size `≥ 3 = Nat.choose 3 1`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.BiddingLanguage

open Finset Cslib.GameTheory.CombinatorialAuction Cslib.GameTheory.CombinatorialAuction.SingleMinded

/-! ### 1. §11.4.1 concrete `XOR` and `OR` examples (p. 280) -/

private abbrev exPairBids : List (SingleMindedBid (Fin 4)) :=
  [⟨{0, 1}, 3⟩, ⟨{2, 3}, 5⟩]

private theorem exPairBids_xor_ac : xorBidEval exPairBids {0, 2} = 0 := by
  have h1 : ¬ ({0, 1} : Finset (Fin 4)) ⊆ {0, 2} := by decide
  have h2 : ¬ ({2, 3} : Finset (Fin 4)) ⊆ {0, 2} := by decide
  simp [exPairBids, xorBidEval, SingleMindedBid.eval, h1, h2]

private theorem exPairBids_xor_ab : xorBidEval exPairBids {0, 1} = 3 := by
  have h1 : ({0, 1} : Finset (Fin 4)) ⊆ {0, 1} := Subset.rfl
  have h2 : ¬ ({2, 3} : Finset (Fin 4)) ⊆ {0, 1} := by decide
  simp only [exPairBids, xorBidEval_cons, xorBidEval_nil, SingleMindedBid.eval, h1, h2, ↓reduceIte]
  norm_num

private theorem exPairBids_xor_all : xorBidEval exPairBids {0, 1, 2, 3} = 5 := by
  have h1 : ({0, 1} : Finset (Fin 4)) ⊆ {0, 1, 2, 3} := by decide
  have h2 : ({2, 3} : Finset (Fin 4)) ⊆ {0, 1, 2, 3} := by decide
  simp only [exPairBids, xorBidEval_cons, xorBidEval_nil, SingleMindedBid.eval, h1, h2, ↓reduceIte]
  norm_num

private theorem exPairBids_or_ac : orBidEval exPairBids {0, 2} = 0 := by
  refine le_antisymm ?_ (orBidEval_nonneg _ _)
  rw [orBidEval_le_iff]
  intro W hW
  have hWe : W = ∅ := eq_empty_of_forall_notMem fun i hi => by
    have hsub := hW.2 i hi
    fin_cases i
    · exact (by decide : ¬ ({0, 1} : Finset (Fin 4)) ⊆ {0, 2}) hsub
    · exact (by decide : ¬ ({2, 3} : Finset (Fin 4)) ⊆ {0, 2}) hsub
  simp [hWe]

private theorem exPairBids_or_ab : orBidEval exPairBids {0, 1} = 3 := by
  refine le_antisymm ?_ ?_
  · rw [orBidEval_le_iff]
    intro W hW
    have h1not : (1 : Fin exPairBids.length) ∉ W := fun h1 =>
      (by decide : ¬ ({2, 3} : Finset (Fin 4)) ⊆ {0, 1}) (hW.2 1 h1)
    have hWsub : W ⊆ {0} := fun i hi => by
      fin_cases i
      · exact mem_singleton_self 0
      · exact (h1not hi).elim
    calc
      ∑ i ∈ W, (exPairBids[i]).value
          ≤ ∑ i ∈ ({0} : Finset (Fin exPairBids.length)), (exPairBids[i]).value :=
            sum_le_sum_of_subset_of_nonneg hWsub fun i _ _ => by fin_cases i <;> norm_num
      _ = 3 := by simp
  · have hvalid : IsValidORCollection exPairBids {0, 1} {0} :=
      ⟨by simp [IsCompatible], fun i hi => by
        rw [mem_singleton.mp hi]
        decide⟩
    simpa using le_orBidEval hvalid

private theorem exPairBids_or_all : orBidEval exPairBids {0, 1, 2, 3} = 8 := by
  refine le_antisymm ?_ ?_
  · rw [orBidEval_le_iff]
    intro W _
    calc
      ∑ i ∈ W, (exPairBids[i]).value
          ≤ ∑ i ∈ (Finset.univ : Finset (Fin exPairBids.length)), (exPairBids[i]).value :=
            sum_le_sum_of_subset_of_nonneg (subset_univ W) fun i _ _ => by
              fin_cases i <;> norm_num
      _ = 8 := by
            change ∑ i : Fin 2, (exPairBids[i]).value = 8
            rw [Fin.sum_univ_two]
            norm_num
  · have hvalid : IsValidORCollection exPairBids {0, 1, 2, 3} Finset.univ := by
      refine ⟨fun i _ j _ hij => ?_, fun i _ => ?_⟩
      · fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
      · fin_cases i <;> decide
    have hle := le_orBidEval hvalid
    change ∑ i : Fin 2, (exPairBids[i]).value ≤ _ at hle
    rw [Fin.sum_univ_two] at hle
    norm_num at hle
    exact hle

private abbrev exOverlapBids : List (SingleMindedBid (Fin 3)) :=
  [⟨{0, 1}, 3⟩, ⟨{0, 2}, 5⟩]

private theorem exOverlapBids_or_all : orBidEval exOverlapBids {0, 1, 2} = 5 := by
  refine le_antisymm ?_ ?_
  · rw [orBidEval_le_iff]
    intro W hW
    have hnotboth :
        ¬ ((0 : Fin exOverlapBids.length) ∈ W ∧ (1 : Fin exOverlapBids.length) ∈ W) := by
      rintro ⟨h0, h1⟩
      have hdj := hW.1 h0 h1 (by decide)
      exact (by decide : ¬ Disjoint ({0, 1} : Finset (Fin 3)) {0, 2}) hdj
    by_cases h0 : (0 : Fin exOverlapBids.length) ∈ W
    · have h1 : (1 : Fin exOverlapBids.length) ∉ W := fun h1 => hnotboth ⟨h0, h1⟩
      have hW_eq : W = {0} := by
        ext i; fin_cases i <;> simp [h0, h1]
      rw [hW_eq]
      norm_num
    · by_cases h1 : (1 : Fin exOverlapBids.length) ∈ W
      · have hW_eq : W = {1} := by
          ext i; fin_cases i <;> simp [h0, h1]
        rw [hW_eq]
        norm_num
      · have hW_eq : W = ∅ := by
          ext i; fin_cases i <;> simp [h0, h1]
        simp [hW_eq]
  · have hvalid : IsValidORCollection exOverlapBids {0, 1, 2} {1} :=
      ⟨by simp [IsCompatible], fun i hi => by
        rw [mem_singleton.mp hi]
        decide⟩
    simpa using le_orBidEval hvalid

private theorem exPairBids_formula_agree :
    (BidFormula.ofXorList exPairBids).eval = xorBidEval exPairBids ∧
    (BidFormula.ofOrList exPairBids).eval = orBidEval exPairBids := by
  have hnn : ∀ b ∈ exPairBids, 0 ≤ b.value := by
    intro b hb
    simp only [exPairBids, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> norm_num
  exact ⟨BidFormula.eval_ofXorList hnn, BidFormula.eval_ofOrList hnn⟩

/-! ### 2. Empty-bundle and duplicate-atom boundary witnesses -/

private abbrev emptyBundleOR : List (SingleMindedBid Bool) := [⟨∅, 1⟩]

private theorem emptyBundleOR_eval (S : Finset Bool) : orBidEval emptyBundleOR S = 1 := by
  refine le_antisymm ?_ ?_
  · rw [orBidEval_le_iff]
    intro W _
    calc
      ∑ i ∈ W, (emptyBundleOR[i]).value
          ≤ ∑ i ∈ (Finset.univ : Finset (Fin emptyBundleOR.length)), (emptyBundleOR[i]).value :=
            sum_le_sum_of_subset_of_nonneg (subset_univ W) fun i _ _ => by
              fin_cases i; norm_num
      _ = 1 := by simp
  · have hvalid : IsValidORCollection emptyBundleOR S {0} :=
      ⟨by simp [IsCompatible], fun i hi => by rw [mem_singleton.mp hi]; simp⟩
    simpa using le_orBidEval hvalid

private theorem emptyBundleOR_not_isSuperadditive :
    ¬ IsSuperadditive (orBidEval emptyBundleOR) := by
  intro hsup
  have h := hsup (S := {false}) (T := {true}) (by decide)
  rw [emptyBundleOR_eval, emptyBundleOR_eval, emptyBundleOR_eval] at h
  linarith

private abbrev dupNonemptyOR : List (SingleMindedBid (Fin 2)) := [⟨{0}, 2⟩, ⟨{0}, 2⟩]

private theorem dupNonemptyOR_eval : orBidEval dupNonemptyOR {0} = 2 := by
  refine le_antisymm ?_ ?_
  · rw [orBidEval_le_iff]
    intro W hW
    have hnotboth :
        ¬ ((0 : Fin dupNonemptyOR.length) ∈ W ∧ (1 : Fin dupNonemptyOR.length) ∈ W) := by
      rintro ⟨h0, h1⟩
      exact (by decide : ¬ Disjoint ({0} : Finset (Fin 2)) {0}) (hW.1 h0 h1 (by decide))
    by_cases h0 : (0 : Fin dupNonemptyOR.length) ∈ W
    · have h1 : (1 : Fin dupNonemptyOR.length) ∉ W := fun h1 => hnotboth ⟨h0, h1⟩
      have hW_eq : W = {0} := by ext i; fin_cases i <;> simp [h0, h1]
      rw [hW_eq]; norm_num
    · by_cases h1 : (1 : Fin dupNonemptyOR.length) ∈ W
      · have hW_eq : W = {1} := by ext i; fin_cases i <;> simp [h0, h1]
        rw [hW_eq]; norm_num
      · have hW_eq : W = ∅ := by ext i; fin_cases i <;> simp [h0, h1]
        simp [hW_eq]
  · have hvalid : IsValidORCollection dupNonemptyOR {0} {0} :=
      ⟨by simp [IsCompatible], fun i hi => by rw [mem_singleton.mp hi]; decide⟩
    simpa using le_orBidEval hvalid

private abbrev dupEmptyOR : List (SingleMindedBid (Fin 2)) := [⟨∅, 2⟩, ⟨∅, 2⟩]

private theorem dupEmptyOR_eval : orBidEval dupEmptyOR ∅ = 4 := by
  refine le_antisymm ?_ ?_
  · rw [orBidEval_le_iff]
    intro W _
    calc
      ∑ i ∈ W, (dupEmptyOR[i]).value
          ≤ ∑ i ∈ (Finset.univ : Finset (Fin dupEmptyOR.length)), (dupEmptyOR[i]).value :=
            sum_le_sum_of_subset_of_nonneg (subset_univ W) fun i _ _ => by
              fin_cases i <;> norm_num
      _ = 4 := by
            change ∑ i : Fin 2, (dupEmptyOR[i]).value = 4
            rw [Fin.sum_univ_two]; norm_num
  · have hvalid : IsValidORCollection dupEmptyOR ∅ Finset.univ :=
      ⟨fun i _ j _ _ => by dsimp only [Function.onFun]; fin_cases i <;> fin_cases j <;> simp,
       fun i _ => by fin_cases i <;> simp⟩
    have hle := le_orBidEval hvalid
    change ∑ i : Fin 2, (dupEmptyOR[i]).value ≤ _ at hle
    rw [Fin.sum_univ_two] at hle
    norm_num at hle
    exact hle

/-! ### 3. Additive and unit-demand separations on `Fin 3` (Definition 11.17, pp. 280–281) -/

private def addWeights : Fin 3 → ℝ := ![1, 2, 3]

private theorem addWeights_pos : ∀ j : Fin 3, 0 < addWeights j := by
  intro j; fin_cases j <;> norm_num [addWeights]

private theorem addWeights_or_size_3 :
    ∃ bids : List (SingleMindedBid (Fin 3)),
      bids.length = 3 ∧ orBidEval bids = additiveValuation addWeights := by
  obtain ⟨bids, hlen, _, heq⟩ :=
    exists_orBid_additiveValuation (fun j => (addWeights_pos j).le)
  exact ⟨bids, by simpa using hlen, heq⟩

private theorem addWeights_xor_ge_7 {bids : List (SingleMindedBid (Fin 3))}
    (heq : xorBidEval bids = additiveValuation addWeights) : 7 ≤ bids.length := by
  simpa using xorBid_length_ge_additiveValuation addWeights_pos heq

private def udWeights : Fin 3 → ℝ := ![2, 5, 1]

private theorem udWeights_xor_size_3 :
    ∃ bids : List (SingleMindedBid (Fin 3)),
      bids.length = 3 ∧ xorBidEval bids = unitDemandValuation udWeights := by
  obtain ⟨bids, hlen, _, heq⟩ := exists_xorBid_unitDemandValuation (w := udWeights)
    (fun j => by fin_cases j <;> norm_num [udWeights])
  exact ⟨bids, by simpa using hlen, heq⟩

private theorem udWeights_not_or :
    ¬ ∃ bids : List (SingleMindedBid (Fin 3)), orBidEval bids = unitDemandValuation udWeights :=
  not_exists_orBid_unitDemandValuation (a := (0 : Fin 3)) (b := (1 : Fin 3)) (by decide)
    (by norm_num [udWeights]) (by norm_num [udWeights])

/-! ### 4. §11.4.2 formula example and Lemma 11.20 downward-sloping valuations (p. 281) -/

private def exFormula : BidFormula (Fin 4) :=
  .or (.xor (.atom ⟨{0, 1}, 3⟩) (.atom ⟨{2}, 2⟩)) (.atom ⟨{3}, 5⟩)

private theorem exFormula_eval_abc : exFormula.eval {0, 1, 2} = 3 := by
  simp only [exFormula, BidFormula.eval]
  refine le_antisymm ?_ ?_
  · rw [orVal_le_iff]
    intro R _ T hT _
    have h3 : (3 : Fin 4) ∉ T := fun h3 =>
      (by decide : (3 : Fin 4) ∉ ({0, 1, 2} : Finset (Fin 4))) (hT h3)
    have hT0 : ¬ ({3} : Finset (Fin 4)) ⊆ T := fun h => h3 (h (mem_singleton_self 3))
    have hTval : (⟨{3}, 5⟩ : SingleMindedBid (Fin 4)).eval T = 0 := by
      simp [SingleMindedBid.eval, hT0]
    rw [hTval, add_zero]
    unfold xorVal SingleMindedBid.eval
    split_ifs <;> norm_num
  · have hle := le_orVal (v := xorVal (⟨{0, 1}, 3⟩ : SingleMindedBid (Fin 4)).eval
        (⟨{2}, 2⟩ : SingleMindedBid (Fin 4)).eval)
      (u := (⟨{3}, 5⟩ : SingleMindedBid (Fin 4)).eval)
      (S := {0, 1, 2}) (R := {0, 1, 2}) (T := ∅)
      Subset.rfl (empty_subset _) (disjoint_empty_right _)
    have h1 : ({0, 1} : Finset (Fin 4)) ⊆ {0, 1, 2} := by decide
    have h2 : ({2} : Finset (Fin 4)) ⊆ {0, 1, 2} := by decide
    have h3 : ¬ ({3} : Finset (Fin 4)) ⊆ ∅ := by decide
    simp only [xorVal, SingleMindedBid.eval, h1, h2, h3, ↓reduceIte, add_zero] at hle
    have : max (3 : ℝ) 2 = 3 := by norm_num
    rwa [this] at hle

private theorem exFormula_eval_abd : exFormula.eval {0, 1, 3} = 8 := by
  simp only [exFormula, BidFormula.eval]
  refine le_antisymm ?_ ?_
  · rw [orVal_le_iff]
    intro R _ T _ _
    unfold xorVal SingleMindedBid.eval
    split_ifs <;> norm_num
  · have hle := le_orVal (v := xorVal (⟨{0, 1}, 3⟩ : SingleMindedBid (Fin 4)).eval
        (⟨{2}, 2⟩ : SingleMindedBid (Fin 4)).eval)
      (u := (⟨{3}, 5⟩ : SingleMindedBid (Fin 4)).eval)
      (S := {0, 1, 3}) (R := {0, 1}) (T := {3})
      (by decide) (by decide) (by decide)
    have h1 : ({0, 1} : Finset (Fin 4)) ⊆ {0, 1} := Subset.rfl
    have h2 : ¬ ({2} : Finset (Fin 4)) ⊆ {0, 1} := by decide
    have h3 : ({3} : Finset (Fin 4)) ⊆ {3} := Subset.rfl
    simp only [xorVal, SingleMindedBid.eval, h1, h2, h3, ↓reduceIte] at hle
    have : max (3 : ℝ) 0 + 5 = 8 := by norm_num
    rwa [this] at hle

private def dsMarginals (k : ℕ) : ℝ :=
  if k = 0 then 5 else if k = 1 then 3 else 1

private theorem dsMarginals_orOfXor_fin3 :
    ∃ f : BidFormula (Fin 3),
      f.IsOrOfXor ∧ f.size = 9 ∧ f.eval = downwardSlopingValuation dsMarginals := by
  have hanti : AntitoneOn dsMarginals (Set.Iio (Fintype.card (Fin 3))) := by
    intro a ha b hb hab
    simp only [Set.mem_Iio, Fintype.card_fin] at ha hb
    unfold dsMarginals
    interval_cases a <;> interval_cases b <;> norm_num at hab ⊢
  have hnn : ∀ k < Fintype.card (Fin 3), 0 ≤ dsMarginals k := by
    intro k hk
    simp only [Fintype.card_fin] at hk
    unfold dsMarginals
    interval_cases k <;> norm_num
  obtain ⟨f, his, hsize, _, heq⟩ :=
    exists_orOfXor_downwardSlopingValuation (M := Fin 3) hanti hnn
  exact ⟨f, his, by simpa using hsize, heq⟩

private theorem dsMarginals_xor_ge_7 {bids : List (SingleMindedBid (Fin 3))}
    (heq : xorBidEval bids = downwardSlopingValuation dsMarginals) : 7 ≤ bids.length := by
  have hpos : ∀ k < Fintype.card (Fin 3), 0 < dsMarginals k := by
    intro k hk
    simp only [Fintype.card_fin] at hk
    unfold dsMarginals
    interval_cases k <;> norm_num
  simpa using xorBid_length_ge_downwardSlopingValuation hpos heq

private theorem dsMarginals_not_or :
    ¬ ∃ bids : List (SingleMindedBid (Fin 3)),
      orBidEval bids = downwardSlopingValuation (M := Fin 3) dsMarginals :=
  not_exists_orBid_downwardSlopingValuation (by simp) (by norm_num [dsMarginals])

private theorem dsMarginals_orOfXor_empty :
    ∃ f : BidFormula Empty,
      f.IsOrOfXor ∧ f.size = 0 ∧ f.eval = downwardSlopingValuation dsMarginals := by
  obtain ⟨f, his, hsize, _, heq⟩ := exists_orOfXor_downwardSlopingValuation (M := Empty)
    (w := dsMarginals) (fun _ ha => (Nat.not_lt_zero _ ha).elim)
    (fun _ hk => (Nat.not_lt_zero _ hk).elim)
  exact ⟨f, his, by simpa using hsize, heq⟩

/-! ### 5. §11.4.3 dummy-item example and Theorem 11.21 (pp. 282–283) -/

private abbrev exDummyORStar : ORStarBid (Fin 3) Unit :=
  ⟨[⟨{.inl 0, .inr ()}, 1⟩, ⟨{.inl 1, .inr ()}, 1⟩, ⟨{.inl 2}, 1⟩]⟩

private def exDummyFormula : BidFormula (Fin 3) :=
  .or (.xor (.atom ⟨{0}, 1⟩) (.atom ⟨{1}, 1⟩)) (.atom ⟨{2}, 1⟩)

private theorem exDummyORStar_eq_formula : exDummyORStar.eval = exDummyFormula.eval := by
  funext S
  have hform : exDummyFormula.eval S =
      (if (0 : Fin 3) ∈ S ∨ (1 : Fin 3) ∈ S then (1 : ℝ) else 0) +
      (if (2 : Fin 3) ∈ S then 1 else 0) := by
    simp only [exDummyFormula, BidFormula.eval]
    refine le_antisymm ?_ ?_
    · rw [orVal_le_iff]
      intro R hR T hT _
      have hleft : xorVal (⟨{0}, 1⟩ : SingleMindedBid (Fin 3)).eval
          (⟨{1}, 1⟩ : SingleMindedBid (Fin 3)).eval R ≤
          if (0 : Fin 3) ∈ S ∨ (1 : Fin 3) ∈ S then 1 else 0 := by
        unfold xorVal SingleMindedBid.eval
        by_cases h0 : ({0} : Finset (Fin 3)) ⊆ R
        · have h0S : (0 : Fin 3) ∈ S := hR (singleton_subset_iff.mp h0)
          simp only [h0, ↓reduceIte, h0S, true_or]
          split_ifs <;> norm_num
        · by_cases h1 : ({1} : Finset (Fin 3)) ⊆ R
          · have h1S : (1 : Fin 3) ∈ S := hR (singleton_subset_iff.mp h1)
            simp only [h0, h1, ↓reduceIte, h1S, or_true]
            norm_num
          · simp only [h0, h1, ↓reduceIte, max_self]
            split_ifs <;> norm_num
      have hright : (⟨{2}, 1⟩ : SingleMindedBid (Fin 3)).eval T ≤
          if (2 : Fin 3) ∈ S then 1 else 0 := by
        unfold SingleMindedBid.eval
        by_cases h2 : ({2} : Finset (Fin 3)) ⊆ T
        · have h2S : (2 : Fin 3) ∈ S := hT (singleton_subset_iff.mp h2)
          simp [h2, h2S]
        · simp only [h2, ↓reduceIte]
          split_ifs <;> norm_num
      exact add_le_add hleft hright
    · have hle := le_orVal (v := xorVal (⟨{0}, 1⟩ : SingleMindedBid (Fin 3)).eval
          (⟨{1}, 1⟩ : SingleMindedBid (Fin 3)).eval)
        (u := (⟨{2}, 1⟩ : SingleMindedBid (Fin 3)).eval)
        (S := S) (R := S.erase 2) (T := if (2 : Fin 3) ∈ S then {2} else ∅)
        (erase_subset 2 S) (by split_ifs with h2 <;> simp [h2])
        (by split_ifs <;> simp [disjoint_singleton_right])
      have hL : xorVal (⟨{0}, 1⟩ : SingleMindedBid (Fin 3)).eval
          (⟨{1}, 1⟩ : SingleMindedBid (Fin 3)).eval (S.erase 2) =
          if (0 : Fin 3) ∈ S ∨ (1 : Fin 3) ∈ S then 1 else 0 := by
        unfold xorVal SingleMindedBid.eval
        have h0 : ({0} : Finset (Fin 3)) ⊆ S.erase 2 ↔ (0 : Fin 3) ∈ S := by
          simp [singleton_subset_iff]
        have h1 : ({1} : Finset (Fin 3)) ⊆ S.erase 2 ↔ (1 : Fin 3) ∈ S := by
          simp [singleton_subset_iff]
        by_cases ha : (0 : Fin 3) ∈ S <;> by_cases hb : (1 : Fin 3) ∈ S <;>
          simp [h0, h1, ha, hb]
      have hR : (⟨{2}, 1⟩ : SingleMindedBid (Fin 3)).eval (if (2 : Fin 3) ∈ S then {2} else ∅) =
          if (2 : Fin 3) ∈ S then 1 else 0 := by
        by_cases h2 : (2 : Fin 3) ∈ S <;> simp [SingleMindedBid.eval, h2]
      rwa [hL, hR] at hle
  rw [hform]
  refine le_antisymm ?_ ?_
  · unfold ORStarBid.eval
    rw [orBidEval_le_iff]
    intro W hW
    have hnot01 : ¬ ((0 : Fin exDummyORStar.bids.length) ∈ W ∧
        (1 : Fin exDummyORStar.bids.length) ∈ W) := by
      rintro ⟨h0, h1⟩
      have hdj := hW.1 h0 h1 (by decide)
      exact (Finset.disjoint_left.mp hdj) (a := .inr ()) (by decide) (by decide)
    have h0sub : (0 : Fin exDummyORStar.bids.length) ∈ W → (0 : Fin 3) ∈ S := fun h0 =>
      (Finset.subset_disjSum.mp (hW.2 0 h0)).1 (by decide)
    have h1sub : (1 : Fin exDummyORStar.bids.length) ∈ W → (1 : Fin 3) ∈ S := fun h1 =>
      (Finset.subset_disjSum.mp (hW.2 1 h1)).1 (by decide)
    have h2sub : (2 : Fin exDummyORStar.bids.length) ∈ W → (2 : Fin 3) ∈ S := fun h2 =>
      (Finset.subset_disjSum.mp (hW.2 2 h2)).1 (by decide)
    have hsum : ∑ i ∈ W, (exDummyORStar.bids[i]).value =
        (if (0 : Fin exDummyORStar.bids.length) ∈ W then (1 : ℝ) else 0) +
        (if (1 : Fin exDummyORStar.bids.length) ∈ W then 1 else 0) +
        (if (2 : Fin exDummyORStar.bids.length) ∈ W then 1 else 0) := by
      have h : ∑ i ∈ W, (exDummyORStar.bids[i]).value =
          ∑ i : Fin 3, if i ∈ W then (exDummyORStar.bids[i]).value else 0 := by
        rw [← sum_filter, filter_mem_eq_inter, univ_inter]
        rfl
      rw [h, Fin.sum_univ_three]
      rfl
    rw [hsum]
    by_cases h0 : (0 : Fin exDummyORStar.bids.length) ∈ W <;>
      by_cases h1 : (1 : Fin exDummyORStar.bids.length) ∈ W <;>
      by_cases h2 : (2 : Fin exDummyORStar.bids.length) ∈ W
    · exact (hnot01 ⟨h0, h1⟩).elim
    · exact (hnot01 ⟨h0, h1⟩).elim
    · simp [h0, h1, h2, h0sub h0, h2sub h2]
    · simp only [h0, h1, h2, h0sub h0, true_or, ↓reduceIte, add_zero]; split_ifs <;> norm_num
    · simp [h0, h1, h2, h1sub h1, h2sub h2]
    · simp only [h0, h1, h2, h1sub h1, or_true, ↓reduceIte, zero_add, add_zero]
      split_ifs <;> norm_num
    · simp only [h0, h1, h2, h2sub h2, ↓reduceIte, zero_add]; split_ifs <;> norm_num
    · simp only [h0, h1, h2, ↓reduceIte, add_zero]; split_ifs <;> norm_num
  · let W : Finset (Fin exDummyORStar.bids.length) :=
      (if (0 : Fin 3) ∈ S then {0} else if (1 : Fin 3) ∈ S then {1} else ∅) ∪
      (if (2 : Fin 3) ∈ S then {2} else ∅)
    have hvalid : IsValidORCollection exDummyORStar.bids (S.disjSum Finset.univ) W := by
      refine ⟨fun i hi j hj hij => ?_, fun i hi => ?_⟩
      · by_cases h0 : (0 : Fin 3) ∈ S <;> by_cases h1 : (1 : Fin 3) ∈ S <;>
          by_cases h2 : (2 : Fin 3) ∈ S <;>
          · simp only [W, h0, h1, h2, ↓reduceIte] at hi hj
            fin_cases i <;> fin_cases j <;>
              first | exact (hij rfl).elim | exact absurd hi (by decide)
                    | exact absurd hj (by decide) | decide
      · by_cases h0 : (0 : Fin 3) ∈ S <;> by_cases h1 : (1 : Fin 3) ∈ S <;>
          by_cases h2 : (2 : Fin 3) ∈ S <;>
          · simp only [W, h0, h1, h2, ↓reduceIte] at hi
            fin_cases i
            · first
              | exact absurd hi (by decide)
              | exact Finset.subset_disjSum.mpr ⟨fun x hx => by
                  fin_cases x
                  · exact h0
                  · exact absurd hx (by decide)
                  · exact absurd hx (by decide), subset_univ _⟩
            · first
              | exact absurd hi (by decide)
              | exact Finset.subset_disjSum.mpr ⟨fun x hx => by
                  fin_cases x
                  · exact absurd hx (by decide)
                  · exact h1
                  · exact absurd hx (by decide), subset_univ _⟩
            · first
              | exact absurd hi (by decide)
              | exact Finset.subset_disjSum.mpr ⟨fun x hx => by
                  fin_cases x
                  · exact absurd hx (by decide)
                  · exact absurd hx (by decide)
                  · exact h2, subset_univ _⟩
    have hWsum : ∑ i ∈ W, (exDummyORStar.bids[i]).value =
        (if (0 : Fin 3) ∈ S ∨ (1 : Fin 3) ∈ S then (1 : ℝ) else 0) +
        (if (2 : Fin 3) ∈ S then 1 else 0) := by
      have h : ∑ i ∈ W, (exDummyORStar.bids[i]).value =
          ∑ i : Fin 3, if i ∈ W then (exDummyORStar.bids[i]).value else 0 := by
        rw [← sum_filter, filter_mem_eq_inter, univ_inter]
        rfl
      rw [h, Fin.sum_univ_three]
      by_cases h0 : (0 : Fin 3) ∈ S <;> by_cases h1 : (1 : Fin 3) ∈ S <;>
        by_cases h2 : (2 : Fin 3) ∈ S <;>
        · simp only [W, h0, h1, h2, ↓reduceIte, or_self, or_true, true_or]
          norm_num [Finset.mem_union, Finset.mem_singleton]
    unfold ORStarBid.eval
    exact hWsum.symm.trans_le (le_orBidEval hvalid)

private theorem exFormula_orStar_simulation :
    ∃ (d : ℕ) (b : ORStarBid (Fin 4) (Fin d)),
      b.size = 3 ∧ d ≤ 3 ∧ d ≤ 3 ^ 2 ∧ b.eval = exFormula.eval := by
  have hnn : ∀ a ∈ exFormula.atoms, 0 ≤ a.value := by
    intro a ha
    simp only [exFormula, BidFormula.atoms, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> norm_num
  obtain ⟨d, b, hsize, hd, _, heq⟩ := exists_orStarBid_of_bidFormula exFormula hnn
  have hsz : exFormula.size = 3 := rfl
  rw [hsz] at hsize hd
  exact ⟨d, b, hsize, by norm_num at hd; omega, by norm_num at hd; omega, heq⟩

/-! ### 6. Exercise 11.5 majority valuation lower bound (p. 299) -/

private theorem majority_fin4_orStar_ge_6 {D : Type*} [Fintype D]
    {b : ORStarBid (Fin 4) D} (heq : b.eval = majorityValuation (Fin 4)) :
    6 ≤ b.size := by
  have h := majorityValuation_orStarBid_size_ge heq
  simp only [Fintype.card_fin] at h
  exact le_trans (by decide) h

private theorem majority_fin3_boundary :
    majorityValuation (Fin 3) ∅ = 0 ∧
    majorityValuation (Fin 3) {0} = 0 ∧
    majorityValuation (Fin 3) {0, 1} = 1 := by
  refine ⟨majorityValuation_empty, ?_, ?_⟩
  · simp [majorityValuation, thresholdValuation]
  · rw [majorityValuation_eq_one_iff]
    norm_num

private theorem majority_fin3_orStar_ge_3 {D : Type*} [Fintype D]
    {b : ORStarBid (Fin 3) D} (heq : b.eval = majorityValuation (Fin 3)) :
    3 ≤ b.size := by
  simpa using majorityValuation_orStarBid_size_ge heq

end CslibFrontierTests.GameTheory.BiddingLanguage
