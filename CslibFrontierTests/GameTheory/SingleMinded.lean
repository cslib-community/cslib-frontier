/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.SingleMinded
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Checked tests for single-minded combinatorial auctions (NRTV Ch. 11 §11.2)

Non-vacuous client examples and boundary counterexamples for
`CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.SingleMinded`:

* `SingleMindedBid.eval` on supersets, strict subsets, and the non-normalized empty-bundle case
  (`S* = ∅`, `v* > 0`);
* `IsCompatible` positive and negative instances;
* a four-bidder LOS greedy auction trace verifying `losWinners`, `losWinnersWithout`,
  `losPayment`, and a counterexample showing that the literal printed text of Figure 11.1 in
  [BlumrosenNisan2007] (p. 274, omitting `k ∈ W`) breaks DSIC;
* non-trivial bundle-size scaling `v_j* / √(|S_j*| / |S_i*|)` and critical-value computation;
* deterministic tie-breaking with identical and distinct bundle sizes;
* exact sharpness of Lemma 11.10 (`4 = √4 · 2`) on `m = 4` items with `4` overlapping `OPT` bids;
* empty-bundle bidder inside `losMechanism` (always wins, pays `0`) and emptiness witness showing
  that `[Nonempty M]` in `losWinners_approx` is tight (`m = 0` gives `1 > √0 · 1`);
* three one-bidder counterexamples showing every side condition of Lemma 11.9 is tight:
  1. `IsDSIC ∧ IsIR ∧ HasNonnegPayment ∧ IsWeakMonotone` yet `¬ IsMonotone` (tie at `v = 1`);
  2. `LosersPayZero ∧ IsDSIC ∧ HasNonnegPayment` yet `¬ HasCriticalPayments` (missing `IsIR`);
  3. `LosersPayZero ∧ IsDSIC ∧ IsIR` yet `¬ HasCriticalPayments` (missing `HasNonnegPayment`);
* a non-monotone rule failing both `IsWeakMonotone` and `IsDSIC`;
* a non-superset deviation witness (`¬ S* ⊆ S'`) under `losMechanism`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.SingleMinded

open Cslib.GameTheory.CombinatorialAuction.SingleMinded

/-! ### Single-minded valuations and compatibility (Def. 11.3 & Def. 11.4) -/

private def sampleBid : SingleMindedBid (Fin 3) := ⟨{0, 1}, 5⟩

example : sampleBid.eval {0, 1} = 5 := by
  simp [sampleBid, SingleMindedBid.eval]

example : sampleBid.eval {0, 1, 2} = 5 := by
  have hsub : ({0, 1} : Finset (Fin 3)) ⊆ {0, 1, 2} := by decide
  simp [sampleBid, SingleMindedBid.eval, hsub]

example : sampleBid.eval {0} = 0 := by
  have hnot : ¬ ({0, 1} : Finset (Fin 3)) ⊆ {0} := by decide
  simp [sampleBid, SingleMindedBid.eval, hnot]

example : sampleBid.eval ∅ = 0 :=
  SingleMindedBid.eval_empty_of_nonempty (by decide : ({0, 1} : Finset (Fin 3)).Nonempty)

/-- A bid with empty desired bundle `S* = ∅` and `v* > 0` fails normalization `v(∅) = 0`
(Definition 11.1, p. 268). -/
example : (SingleMindedBid.mk (∅ : Finset (Fin 2)) 5).eval ∅ = 5 := by
  simp [SingleMindedBid.eval]

private def twoBidProfile : Fin 2 → SingleMindedBid (Fin 3)
  | 0 => ⟨{0, 1}, 4⟩
  | 1 => ⟨{1, 2}, 3⟩

private def disjointProfile : Fin 2 → SingleMindedBid (Fin 3)
  | 0 => ⟨{0}, 4⟩
  | 1 => ⟨{1, 2}, 3⟩

example : IsCompatible disjointProfile {0, 1} := by
  intro i hi j hj hij
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · decide
  · decide
  · exact (hij rfl).elim

example : ¬ IsCompatible twoBidProfile {0, 1} := by
  intro h
  have hd : Disjoint (twoBidProfile 0).bundle (twoBidProfile 1).bundle :=
    h (by simp) (by simp) (by decide)
  exact (by decide : ¬ Disjoint ({0, 1} : Finset (Fin 3)) {1, 2}) hd

/-! ### Four-bidder trace and Figure 11.1 literal-text counterexample -/

/-- Four bids on `Fin 3`:
- `0`: `({0}, 10)`, `score = 10` (wins)
- `1`: `({0, 1}, 9 * √2)`, `score = 9` (blocked by `0` on item `0`)
- `2`: `({2}, 8)`, `score = 8` (wins)
- `3`: `({1, 2}, 7 * √2)`, `score = 7` (blocked by `2` on item `2`, overlaps losing `1` on item `1`)
-/
private noncomputable def traceBids : Fin 4 → SingleMindedBid (Fin 3)
  | 0 => ⟨{0}, 10⟩
  | 1 => ⟨{0, 1}, 9 * Real.sqrt 2⟩
  | 2 => ⟨{2}, 8⟩
  | 3 => ⟨{1, 2}, 7 * Real.sqrt 2⟩

private theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private theorem traceBids_nonneg : ∀ i, 0 ≤ (traceBids i).value := by
  intro i
  fin_cases i
  · norm_num [traceBids]
  · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · norm_num [traceBids]
  · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

private theorem traceBids_scores :
    losScore (traceBids 0) = 10 ∧
    losScore (traceBids 1) = 9 ∧
    losScore (traceBids 2) = 8 ∧
    losScore (traceBids 3) = 7 := by
  have h2ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [traceBids, losScore]
  · have hc : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
    simp only [traceBids, losScore, hc, Nat.cast_ofNat]
    field_simp
  · simp [traceBids, losScore]
  · have hc : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
    simp only [traceBids, losScore, hc, Nat.cast_ofNat]
    field_simp

private theorem traceBids_sorted :
    ([0, 1, 2, 3] : List (Fin 4)).Pairwise (losLt traceBids) := by
  obtain ⟨s0, s1, s2, s3⟩ := traceBids_scores
  have h : ∀ {i j : Fin 4}, losScore (traceBids j) < losScore (traceBids i) →
      losLt traceBids i j := fun hlt => Or.inl hlt
  refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_,
    List.pairwise_cons.2 ⟨?_, List.pairwise_singleton _ _⟩⟩⟩
  · intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> exact h (by linarith)
  · intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> exact h (by linarith)
  · intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy; exact h (by linarith)

private theorem traceBids_winners : losWinners traceBids = {0, 2} := by
  rw [losWinners_eq_greedySelect (l := [0, 1, 2, 3]) (by decide)
    (fun i => by fin_cases i <;> decide) traceBids_sorted]
  unfold greedySelect
  simp only [List.foldl_cons, List.foldl_nil, greedyStep, traceBids]
  decide

private theorem traceBids_winnersWithout_two :
    losWinnersWithout traceBids 2 = {0, 3} := by
  have hsort : ([0, 1, 3] : List (Fin 4)).Pairwise (losLt traceBids) :=
    traceBids_sorted.sublist (by decide)
  rw [losWinnersWithout_eq_greedySelect (l := [0, 1, 3]) (by decide)
    (fun j => by fin_cases j <;> decide) hsort]
  unfold greedySelect
  simp only [List.foldl_cons, List.foldl_nil, greedyStep, traceBids]
  decide

/-- Under `losMechanism`, bidder `2` pays `7` (set by bidder `3`, whose `score` is `7` and which
wins when bidder `2` is removed), even though losing bidder `1` precedes `3` and overlaps `3` on
item `1`. -/
example : losPayment traceBids 2 = 7 := by
  have hw2 : (2 : Fin 4) ∈ losWinners traceBids := by rw [traceBids_winners]; decide
  rcases losPayment_eq_first_blocked traceBids hw2 with
    ⟨j, hji, hnd, hcond, hmin, hij, hpay⟩ | ⟨hnone, _⟩
  · have hj3 : j = 3 := by
      fin_cases j
      · exact absurd (by decide : Disjoint (traceBids 2).bundle (traceBids 0).bundle) hnd
      · exact absurd (by decide : Disjoint (traceBids 2).bundle (traceBids 1).bundle) hnd
      · exact (hji rfl).elim
      · rfl
    subst hj3
    have hc2 : (traceBids 2).bundle.card = 1 := by decide
    have hc3 : (traceBids 3).bundle.card = 2 := by decide
    rw [hpay, hc2, hc3]
    simp only [traceBids, Nat.cast_one, Nat.cast_ofNat, div_one]
    have h2ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    field_simp
  · exfalso
    obtain ⟨k, hkW, hki, hkj, hnd⟩ := hnone 3 (by decide) (by decide)
    rw [traceBids_winners] at hkW
    rcases (by simpa using hkW : k = 0 ∨ k = 2) with rfl | rfl
    · exact hnd (by decide)
    · exact hki rfl

/-- In contrast to the corrected payment `7`, NRTV's literal text in Figure 11.1 (p. 274) omits
the winner restriction `k ∈ W` and asks for `∀ k < j, k ≠ i, S_k* ∩ S_j* = ∅`. For `traceBids`
and winner `i = 2`, bidder `3` fails that literal condition because the **losing** bidder `1`
overlaps `3` on item `1`. A mechanism imposing the literal payment condition assigns `payment = 0`
to `2`, enabling a bidder with true bid `⟨{2}, 6⟩` to strictly profit by overbidding `⟨{2}, 8⟩`. -/
example :
    ∃ (k : Fin 4), k ≠ 2 ∧ losLt traceBids k 3 ∧ k ∉ losWinners traceBids ∧
      ¬ Disjoint (traceBids k).bundle (traceBids 3).bundle := by
  obtain ⟨_, s1, _, s3⟩ := traceBids_scores
  refine ⟨1, by decide, Or.inl (by linarith), ?_, by decide⟩
  rw [traceBids_winners]
  decide

private noncomputable def literalFig11_1 : Mechanism (Fin 4) (Fin 3) where
  winners := losWinners
  payment b i :=
    open scoped Classical in
    if i ∈ losWinners b then
      if ∃ j, j ≠ i ∧ ¬ Disjoint (b i).bundle (b j).bundle ∧
          ∀ k, k ≠ i → losLt b k j → Disjoint (b k).bundle (b j).bundle
      then losPayment b i
      else 0
    else 0

example : ¬ literalFig11_1.IsDSIC := by
  intro hdsic
  set trueBid : SingleMindedBid (Fin 3) := ⟨{2}, 6⟩
  have h := hdsic 2 traceBids trueBid traceBids_nonneg (by norm_num [trueBid])
  have hpay_dev : literalFig11_1.payment traceBids 2 = 0 := by
    have hno : ¬ ∃ j : Fin 4, j ≠ 2 ∧
        ¬ Disjoint (traceBids 2).bundle (traceBids j).bundle ∧
        ∀ k, k ≠ 2 → losLt traceBids k j → Disjoint (traceBids k).bundle (traceBids j).bundle := by
      rintro ⟨j, hji, hnd, hcond⟩
      fin_cases j
      · exact hnd (by decide)
      · exact hnd (by decide)
      · exact hji rfl
      · obtain ⟨_, s1, _, s3⟩ := traceBids_scores
        exact (by decide : ¬ Disjoint (traceBids 1).bundle (traceBids 3).bundle)
          (hcond 1 (by decide) (Or.inl (show losScore (traceBids 3) < losScore (traceBids 1) by
            linarith)))
    simp [literalFig11_1, hno]
  have hw_dev : (2 : Fin 4) ∈ literalFig11_1.winners traceBids := by
    change (2 : Fin 4) ∈ losWinners traceBids
    rw [traceBids_winners]; decide
  have hu_dev : literalFig11_1.utility 2 trueBid traceBids = 6 := by
    simp [Mechanism.utility, hw_dev, hpay_dev, SingleMindedBid.eval, traceBids, trueBid]
  have hlos_true : (2 : Fin 4) ∉ losWinners (Function.update traceBids 2 trueBid) := by
    intro hwin
    have hmem := (mem_losWinners_iff _ 2).1 hwin 3
    rw [losWinnersWithout_update, traceBids_winnersWithout_two] at hmem
    have hlt32 : losLt (Function.update traceBids 2 trueBid) 3 2 := by
      left
      have hsc2 : losScore (Function.update traceBids 2 trueBid 2) = 6 := by
        simp [Function.update_self, trueBid, losScore]
      have hsc3 : losScore (Function.update traceBids 2 trueBid 3) = 7 := by
        rw [Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2)]
        exact traceBids_scores.2.2.2
      linarith
    have hd := hmem (by decide) hlt32
    simp only [Function.update_self, Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2)] at hd
    exact (by decide : ¬ Disjoint trueBid.bundle (traceBids 3).bundle) hd
  have hu_true : literalFig11_1.utility 2 trueBid (Function.update traceBids 2 trueBid) = 0 := by
    simp [Mechanism.utility, literalFig11_1, hlos_true]
  linarith

/-- Bidder `0` pays `9` (set by `1`, whose score is `9`), while losers `1, 3` pay `0`. -/
example : losPayment traceBids 0 = 9 ∧ losPayment traceBids 1 = 0 ∧ losPayment traceBids 3 = 0 := by
  refine ⟨?_, losMechanism_losersPayZero traceBids traceBids_nonneg 1 ?_,
    losMechanism_losersPayZero traceBids traceBids_nonneg 3 ?_⟩
  · have hw0 : (0 : Fin 4) ∈ losWinners traceBids := by rw [traceBids_winners]; decide
    rcases losPayment_eq_first_blocked traceBids hw0 with
      ⟨j, hji, hnd, _, _, _, hpay⟩ | ⟨hnone, _⟩
    · have hj1 : j = 1 := by
        fin_cases j
        · exact (hji rfl).elim
        · rfl
        · exact absurd (by decide : Disjoint (traceBids 0).bundle (traceBids 2).bundle) hnd
        · exact absurd (by decide : Disjoint (traceBids 0).bundle (traceBids 3).bundle) hnd
      subst hj1
      have hc0 : (traceBids 0).bundle.card = 1 := by decide
      have hc1 : (traceBids 1).bundle.card = 2 := by decide
      rw [hpay, hc0, hc1]
      simp only [traceBids, Nat.cast_one, Nat.cast_ofNat, div_one]
      have h2ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
      field_simp
    · exfalso
      obtain ⟨k, hkW, hki, hkj, _⟩ := hnone 1 (by decide) (by decide)
      obtain ⟨s0, s1, s2, _⟩ := traceBids_scores
      rw [traceBids_winners] at hkW
      rcases (by simpa using hkW : k = 0 ∨ k = 2) with rfl | rfl
      · exact hki rfl
      · rcases hkj with hlt | ⟨heq, _⟩ <;> linarith
  · change _ ∉ losWinners traceBids; rw [traceBids_winners]; decide
  · change _ ∉ losWinners traceBids; rw [traceBids_winners]; decide

/-! ### Non-trivial `√(|S_j*| / |S_i*|)` payment scaling -/

private noncomputable def scaledBids : Fin 2 → SingleMindedBid (Fin 4)
  | 0 => ⟨Finset.univ, 6⟩
  | 1 => ⟨{0}, 2⟩

example : losWinners scaledBids = {0} ∧ losPayment scaledBids 0 = 4 ∧
    criticalValue losWinners scaledBids 0 = 4 := by
  have hc0 : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
  have hs0 : losScore (scaledBids 0) = 3 := by
    simp only [scaledBids, losScore, hc0, Nat.cast_ofNat, sqrt_four]; norm_num
  have hs1 : losScore (scaledBids 1) = 2 := by
    simp [scaledBids, losScore]
  have hsort : ([0, 1] : List (Fin 2)).Pairwise (losLt scaledBids) := by
    refine List.pairwise_cons.2 ⟨fun y hy => ?_, List.pairwise_singleton _ _⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy
    exact Or.inl (by linarith)
  have hwin : losWinners scaledBids = {0} := by
    rw [losWinners_eq_greedySelect (l := [0, 1]) (by decide)
      (fun i => by fin_cases i <;> decide) hsort]
    unfold greedySelect
    simp only [List.foldl_cons, List.foldl_nil, greedyStep, scaledBids]
    decide
  have hpay0 : losPayment scaledBids 0 = 4 := by
    have hw0 : (0 : Fin 2) ∈ losWinners scaledBids := by rw [hwin]; decide
    rcases losPayment_eq_first_blocked scaledBids hw0 with
      ⟨j, hji, _, _, _, _, hpay⟩ | ⟨hnone, _⟩
    · have hj1 : j = 1 := by fin_cases j <;> [exact (hji rfl).elim; rfl]
      subst hj1
      rw [hpay]
      simp only [scaledBids, hc0, Finset.card_singleton, Nat.cast_one, Nat.cast_ofNat]
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one, sqrt_four]
      norm_num
    · exfalso
      obtain ⟨k, hkW, hki, _, _⟩ := hnone 1 (by decide) (by decide)
      rw [hwin] at hkW
      exact hki (Finset.mem_singleton.1 hkW)
  have hnn : ∀ i, 0 ≤ (scaledBids i).value := fun i => by fin_cases i <;> norm_num [scaledBids]
  have hcv : criticalValue losWinners scaledBids 0 = 4 := by
    rw [← losPayment_eq_criticalValue scaledBids hnn (by rw [hwin]; decide), hpay0]
  exact ⟨hwin, hpay0, hcv⟩

/-! ### Deterministic tie-breaking across distinct bundle sizes -/

private noncomputable def tieBids : Fin 2 → SingleMindedBid (Fin 4)
  | 0 => ⟨{0}, 1⟩
  | 1 => ⟨Finset.univ, 2⟩

example : losScore (tieBids 0) = losScore (tieBids 1) ∧
    losWinners tieBids = {0} ∧ losPayment tieBids 0 = 1 := by
  have hc1 : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
  have hsq : losScore (tieBids 0) = 1 ∧ losScore (tieBids 1) = 1 := by
    constructor
    · simp [tieBids, losScore]
    · simp only [tieBids, losScore, hc1, Nat.cast_ofNat, sqrt_four]; norm_num
  have hsort : ([0, 1] : List (Fin 2)).Pairwise (losLt tieBids) := by
    refine List.pairwise_cons.2 ⟨fun y hy => ?_, List.pairwise_singleton _ _⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy
    exact Or.inr ⟨by linarith [hsq.1, hsq.2], by decide⟩
  have hwin : losWinners tieBids = {0} := by
    rw [losWinners_eq_greedySelect (l := [0, 1]) (by decide)
      (fun i => by fin_cases i <;> decide) hsort]
    unfold greedySelect
    simp only [List.foldl_cons, List.foldl_nil, greedyStep, tieBids]
    decide
  have hpay : losPayment tieBids 0 = 1 := by
    have hw0 : (0 : Fin 2) ∈ losWinners tieBids := by rw [hwin]; decide
    rcases losPayment_eq_first_blocked tieBids hw0 with
      ⟨j, hji, _, _, _, _, hp⟩ | ⟨hnone, _⟩
    · have hj1 : j = 1 := by fin_cases j <;> [exact (hji rfl).elim; rfl]
      subst hj1
      rw [hp]
      simp only [tieBids, hc1, Finset.card_singleton, Nat.cast_one, Nat.cast_ofNat, div_one,
        sqrt_four]
      norm_num
    · exfalso
      obtain ⟨k, hkW, hki, _, _⟩ := hnone 1 (by decide) (by decide)
      rw [hwin] at hkW
      exact hki (Finset.mem_singleton.1 hkW)
  exact ⟨by linarith [hsq.1, hsq.2], hwin, hpay⟩

/-! ### Exact tightness of Lemma 11.10 (`√4 = 2` on `m = 4` items) -/

/-- Five bidders on `4` items: bidder `0` wants all `4` items for value `2` (`score = 1`);
bidders `1..4` each want a distinct singleton for value `1` (`score = 1`). Breaking ties toward
`0` makes `losWinners = {0}` (welfare `2`), while `OPT = {1, 2, 3, 4}` has welfare `4 = √4 · 2`. -/
private noncomputable def tightBids : Fin 5 → SingleMindedBid (Fin 4)
  | 0 => ⟨Finset.univ, 2⟩
  | 1 => ⟨{0}, 1⟩
  | 2 => ⟨{1}, 1⟩
  | 3 => ⟨{2}, 1⟩
  | 4 => ⟨{3}, 1⟩

example :
    let opt : Finset (Fin 5) := {1, 2, 3, 4}
    IsCompatible tightBids opt ∧
    losWinners tightBids = {0} ∧
    ∑ i ∈ opt, (tightBids i).value =
      Real.sqrt (Fintype.card (Fin 4)) * ∑ i ∈ losWinners tightBids, (tightBids i).value := by
  intro opt
  have hc : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
  have hsc : ∀ i : Fin 5, losScore (tightBids i) = 1 := fun i => by
    fin_cases i
    · simp only [tightBids, losScore, hc, Nat.cast_ofNat, sqrt_four]; norm_num
    all_goals simp [tightBids, losScore]
  have hsort : ([0, 1, 2, 3, 4] : List (Fin 5)).Pairwise (losLt tightBids) := by
    have hlt_pw : ([0, 1, 2, 3, 4] : List (Fin 5)).Pairwise (· < ·) := by decide
    exact hlt_pw.imp fun {a c} hac => Or.inr ⟨by rw [hsc a, hsc c], hac⟩
  have hwin : losWinners tightBids = {0} := by
    rw [losWinners_eq_greedySelect (l := [0, 1, 2, 3, 4]) (by decide)
      (fun i => by fin_cases i <;> decide) hsort]
    unfold greedySelect
    simp only [List.foldl_cons, List.foldl_nil, greedyStep, tightBids]
    decide
  have hopt : IsCompatible tightBids opt := by
    intro i hi j hj hij
    have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
      simpa [opt] using hi
    have hj' : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
      simpa [opt] using hj
    rcases hi' with rfl | rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl | rfl <;>
      first | exact (hij rfl).elim | decide
  refine ⟨hopt, hwin, ?_⟩
  rw [hwin]
  have hcard : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
  have hsum_opt : ∑ i ∈ opt, (tightBids i).value = 4 := by
    simp only [opt]
    norm_num [tightBids]
  have hsum_w : ∑ i ∈ ({0} : Finset (Fin 5)), (tightBids i).value = 2 := by
    norm_num [tightBids]
  rw [hsum_opt, hsum_w, hcard]
  norm_num [sqrt_four]

/-! ### Empty desired bundle edge case & `IsEmpty M` boundary -/

private noncomputable def emptyBundleBids : Fin 3 → SingleMindedBid (Fin 2)
  | 0 => ⟨∅, 5⟩
  | 1 => ⟨{0}, 3⟩
  | 2 => ⟨{0, 1}, 1⟩

example : (0 : Fin 3) ∈ losWinners emptyBundleBids ∧
    losPayment emptyBundleBids 0 = 0 ∧
    criticalValue losWinners emptyBundleBids 0 = 0 := by
  have hw0 : (0 : Fin 3) ∈ losWinners emptyBundleBids :=
    mem_losWinners_of_bundle_empty emptyBundleBids (by rfl)
  have hp0 : losPayment emptyBundleBids 0 = 0 :=
    losPayment_eq_zero_of_bundle_empty emptyBundleBids (by rfl)
  have hnn : ∀ i, 0 ≤ (emptyBundleBids i).value := fun i => by
    fin_cases i <;> norm_num [emptyBundleBids]
  have hcv : criticalValue losWinners emptyBundleBids 0 = 0 := by
    rw [← losPayment_eq_criticalValue emptyBundleBids hnn hw0, hp0]
  exact ⟨hw0, hp0, hcv⟩

/-- Tightness of `[Nonempty M]` in `losWinners_approx` (Lemma 11.10, p. 275): on `Empty` (`m = 0`),
a single positive bid `(∅, 1)` yields `∑ OPT = 1` while `√0 * ∑ W = 0`. -/
example :
    let b : Unit → SingleMindedBid Empty := fun _ => ⟨∅, 1⟩
    IsCompatible b {()} ∧ losWinners b = {()} ∧
    ¬ (∑ i ∈ ({()} : Finset Unit), (b i).value ≤
      Real.sqrt (Fintype.card Empty) * ∑ i ∈ losWinners b, (b i).value) := by
  intro b
  have hwin : losWinners b = {()} := by
    ext x
    cases x
    simpa using mem_losWinners_of_bundle_empty b rfl
  refine ⟨fun i _ j _ h => (h (Subsingleton.elim i j)).elim, hwin, ?_⟩
  rw [hwin]
  simp [b]

/-! ### Lemma 11.9 tightness counterexamples (one bidder each) -/

/-- Counterexample 1: strict-value monotonicity (`IsWeakMonotone`) holds, yet non-strict
monotonicity (`IsMonotone`) FAILS at the tie `v = 1`. The mechanism is DSIC, IR, loses pay `0`,
and has nonnegative payments (`{0, 1}` wins at `v ≥ 1`; strict subsets win only at `v > 1`). -/
private noncomputable def tieBoundaryMech : Mechanism Unit (Fin 2) where
  winners b :=
    open scoped Classical in
    if ((b ()).bundle = Finset.univ ∧ 1 ≤ (b ()).value) ∨
        ((b ()).bundle ≠ Finset.univ ∧ 1 < (b ()).value)
    then {()} else ∅
  payment b _ :=
    open scoped Classical in
    if ((b ()).bundle = Finset.univ ∧ 1 ≤ (b ()).value) ∨
        ((b ()).bundle ≠ Finset.univ ∧ 1 < (b ()).value)
    then 1 else 0

example :
    tieBoundaryMech.LosersPayZero ∧
    tieBoundaryMech.IsDSIC ∧
    tieBoundaryMech.IsIR ∧
    tieBoundaryMech.HasNonnegPayment ∧
    IsWeakMonotone tieBoundaryMech.winners ∧
    ¬ IsMonotone tieBoundaryMech.winners := by
  have h0 : tieBoundaryMech.LosersPayZero := by
    intro b _ i hi
    cases i
    simp only [tieBoundaryMech] at hi ⊢
    by_cases h : ((b ()).bundle = Finset.univ ∧ 1 ≤ (b ()).value) ∨
        ((b ()).bundle ≠ Finset.univ ∧ 1 < (b ()).value)
    · simp only [h, ↓reduceIte] at hi
      exact absurd (Finset.mem_singleton_self ()) hi
    · simp only [h, ↓reduceIte]
  have hwin_iff : ∀ b : Unit → SingleMindedBid (Fin 2),
      () ∈ tieBoundaryMech.winners b ↔
        ((b ()).bundle = Finset.univ ∧ 1 ≤ (b ()).value) ∨
        ((b ()).bundle ≠ Finset.univ ∧ 1 < (b ()).value) := by
    intro b
    simp only [tieBoundaryMech]
    split_ifs with h <;> simp [h]
  have hwm : IsWeakMonotone tieBoundaryMech.winners := by
    intro i b S' v' _ hwin _ hlt
    cases i
    have hv : 1 ≤ (b ()).value := by
      rcases (hwin_iff b).1 hwin with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
    rw [hwin_iff]
    simp only [Function.update_self]
    by_cases hS : S' = Finset.univ
    · exact Or.inl ⟨hS, by linarith⟩
    · exact Or.inr ⟨hS, by linarith⟩
  have hcrit : tieBoundaryMech.HasCriticalPayments := by
    intro b _ i hi
    cases i
    have hcond := (hwin_iff b).1 hi
    have hpay : tieBoundaryMech.payment b () = 1 := by
      simp only [tieBoundaryMech, hcond, ↓reduceIte]
    rw [hpay]
    symm
    apply le_antisymm
    · rw [← csInf_Ioi (a := (1 : ℝ))]
      refine csInf_le_csInf ⟨0, fun _ h => h.1⟩ Set.nonempty_Ioi fun z hz => ?_
      have hz1 : 1 < z := hz
      refine ⟨by linarith, (hwin_iff _).2 ?_⟩
      simp only [Function.update_self]
      by_cases hS : (b ()).bundle = Finset.univ
      · exact Or.inl ⟨hS, hz1.le⟩
      · exact Or.inr ⟨hS, hz1⟩
    · refine le_csInf ⟨2, by norm_num, (hwin_iff _).2 ?_⟩ ?_
      · simp only [Function.update_self]
        by_cases hS : (b ()).bundle = Finset.univ
        · exact Or.inl ⟨hS, by norm_num⟩
        · exact Or.inr ⟨hS, by norm_num⟩
      · rintro z ⟨_, hzwin⟩
        rcases (hwin_iff _).1 hzwin with ⟨_, h⟩ | ⟨_, h⟩ <;>
          simp only [Function.update_self] at h <;> linarith
  have hchar := (Mechanism.isDSIC_and_isIR_and_hasNonnegPayment_iff h0).2 ⟨hwm, hcrit⟩
  refine ⟨h0, hchar.1, hchar.2.1, hchar.2.2, hwm, ?_⟩
  intro hmono
  let b : Unit → SingleMindedBid (Fin 2) := fun _ => ⟨Finset.univ, 1⟩
  have hwin : () ∈ tieBoundaryMech.winners b := (hwin_iff b).2 (Or.inl ⟨rfl, le_rfl⟩)
  have hkeep := hmono () b {0} 1 (fun _ => by norm_num [b]) hwin
    (by decide) (by norm_num [b])
  rcases (hwin_iff _).1 hkeep with ⟨heq, _⟩ | ⟨_, hlt⟩
  · exact absurd heq (by decide)
  · simp [Function.update_self] at hlt

/-- Counterexample 2: constant-win mechanism charging a fixed price `10`. Losers vacuously pay `0`,
the mechanism is DSIC and has nonnegative payments, yet fails `IsIR` and `HasCriticalPayments`
(critical value is `0`, payment is `10`). -/
private def alwaysWinCharge (c : ℝ) : Mechanism Unit Unit where
  winners _ := {()}
  payment _ _ := c

private theorem alwaysWinCharge_losersPayZero (c : ℝ) : (alwaysWinCharge c).LosersPayZero :=
  fun _ _ i hi => by cases i; exact (hi (Finset.mem_singleton_self ())).elim

private theorem alwaysWinCharge_isDSIC (c : ℝ) : (alwaysWinCharge c).IsDSIC := by
  intro i b trueBid _ ht
  cases i
  simp only [Mechanism.utility, alwaysWinCharge, Finset.mem_singleton_self, ↓reduceIte,
    Function.update_self, SingleMindedBid.eval_self]
  by_cases hsub : trueBid.bundle ⊆ (b ()).bundle
  · simp [SingleMindedBid.eval, hsub]
  · simp only [SingleMindedBid.eval, hsub, ↓reduceIte]; linarith

example :
    (alwaysWinCharge 10).LosersPayZero ∧
    (alwaysWinCharge 10).IsDSIC ∧
    (alwaysWinCharge 10).HasNonnegPayment ∧
    ¬ (alwaysWinCharge 10).IsIR ∧
    ¬ (alwaysWinCharge 10).HasCriticalPayments := by
  have hnn : (alwaysWinCharge 10).HasNonnegPayment := fun _ _ _ => by norm_num [alwaysWinCharge]
  have hnotIR : ¬ (alwaysWinCharge 10).IsIR := by
    intro hir
    have h := hir () (fun _ => ⟨∅, 0⟩) (fun _ => le_rfl)
    simp [Mechanism.utility, alwaysWinCharge, SingleMindedBid.eval] at h
    linarith
  have hnotCrit : ¬ (alwaysWinCharge 10).HasCriticalPayments := by
    intro hc
    have h := hc (fun _ => ⟨∅, 0⟩) (fun _ => le_rfl) () (Finset.mem_singleton_self ())
    have hcv : criticalValue (alwaysWinCharge 10).winners (fun _ => ⟨∅, 0⟩) () ≤ 0 :=
      criticalValue_le_of_mem le_rfl (Finset.mem_singleton_self ())
    have hp : (alwaysWinCharge 10).payment (fun _ => ⟨∅, 0⟩) () = 10 := rfl
    linarith
  exact ⟨alwaysWinCharge_losersPayZero 10, alwaysWinCharge_isDSIC 10, hnn, hnotIR, hnotCrit⟩

/-- Counterexample 3: constant-win mechanism with negative payment `-5` (positive transfer).
Losers vacuously pay `0`, the mechanism is DSIC and IR, yet fails `HasNonnegPayment` and
`HasCriticalPayments` (critical value is `0`, payment is `-5`). -/
example :
    (alwaysWinCharge (-5)).LosersPayZero ∧
    (alwaysWinCharge (-5)).IsDSIC ∧
    (alwaysWinCharge (-5)).IsIR ∧
    ¬ (alwaysWinCharge (-5)).HasNonnegPayment ∧
    ¬ (alwaysWinCharge (-5)).HasCriticalPayments := by
  have hir : (alwaysWinCharge (-5)).IsIR := fun i b hb => by
    cases i
    have h := hb ()
    simp only [Mechanism.utility, alwaysWinCharge, Finset.mem_singleton_self, ↓reduceIte,
      SingleMindedBid.eval_self]
    linarith
  have hnotNN : ¬ (alwaysWinCharge (-5)).HasNonnegPayment := by
    intro hnn
    have h := hnn (fun _ => ⟨∅, 0⟩) (fun _ => le_rfl) ()
    simp [alwaysWinCharge] at h
    linarith
  have hnotCrit : ¬ (alwaysWinCharge (-5)).HasCriticalPayments := by
    intro hc
    have h := hc (fun _ => ⟨∅, 0⟩) (fun _ => le_rfl) () (Finset.mem_singleton_self ())
    have hcv : 0 ≤ criticalValue (alwaysWinCharge (-5)).winners (fun _ => ⟨∅, 0⟩) () :=
      criticalValue_nonneg _ _ _
    have hp : (alwaysWinCharge (-5)).payment (fun _ => ⟨∅, 0⟩) () = -5 := rfl
    linarith
  exact ⟨alwaysWinCharge_losersPayZero (-5), alwaysWinCharge_isDSIC (-5), hir, hnotNN, hnotCrit⟩

/-! ### Non-monotone allocation rule failing DSIC -/

private noncomputable def antiMonotoneMech : Mechanism Unit Unit where
  winners b := open scoped Classical in if (b ()).value ≤ 1 then {()} else ∅
  payment _ _ := 0

example : ¬ IsWeakMonotone antiMonotoneMech.winners ∧ ¬ antiMonotoneMech.IsDSIC := by
  have h0 : antiMonotoneMech.LosersPayZero := fun _ _ _ _ => rfl
  have hnm : ¬ IsWeakMonotone antiMonotoneMech.winners := by
    intro hm
    let b : Unit → SingleMindedBid Unit := fun _ => ⟨Finset.univ, 1⟩
    have hwin : () ∈ antiMonotoneMech.winners b := by simp [antiMonotoneMech, b]
    have h2 := hm () b Finset.univ 5 (fun _ => by norm_num [b]) hwin
      (Finset.Subset.rfl) (by norm_num [b])
    simp [antiMonotoneMech] at h2
  exact ⟨hnm, fun hdsic => hnm (Mechanism.isWeakMonotone_of_isDSIC h0 hdsic)⟩

/-! ### Non-superset deviation witness (`¬ S* ⊆ S'`) -/

/-- A bidder whose true bundle is `{0, 1}` receives valuation `0` (not `10`) when misreporting a
strict subset `{0}` and winning it. -/
example :
    let trueBid : SingleMindedBid (Fin 2) := ⟨{0, 1}, 10⟩
    let dev : Unit → SingleMindedBid (Fin 2) := fun _ => ⟨{0}, 10⟩
    losMechanism.utility () trueBid dev = 0 ∧
    losMechanism.utility () trueBid (Function.update dev () trueBid) = 10 := by
  intro trueBid dev
  have hw_dev : () ∈ losWinners dev := by
    rw [losWinners_eq_greedySelect (l := [()]) (by decide) (fun i => by cases i; simp)
      (List.pairwise_singleton _ _)]
    simp [greedySelect, greedyStep]
  have hpay_dev : losPayment dev () = 0 := by
    rcases losPayment_eq_first_blocked dev hw_dev with ⟨j, hji, _⟩ | ⟨_, hp⟩
    · exact absurd (Subsingleton.elim j ()) hji
    · exact hp
  have hw_true : () ∈ losWinners (Function.update dev () trueBid) := by
    rw [losWinners_eq_greedySelect (l := [()]) (by decide) (fun i => by cases i; simp)
      (List.pairwise_singleton _ _)]
    simp [greedySelect, greedyStep]
  have hpay_true : losPayment (Function.update dev () trueBid) () = 0 := by
    rcases losPayment_eq_first_blocked (Function.update dev () trueBid) hw_true with
      ⟨j, hji, _⟩ | ⟨_, hp⟩
    · exact absurd (Subsingleton.elim j ()) hji
    · exact hp
  have hnsub : ¬ trueBid.bundle ⊆ (dev ()).bundle := by decide
  constructor
  · simp [Mechanism.utility, losMechanism, hw_dev, hpay_dev, SingleMindedBid.eval, hnsub]
  · simp [Mechanism.utility, losMechanism, hw_true, hpay_true, Function.update_self,
      SingleMindedBid.eval, trueBid]

end CslibFrontierTests.GameTheory.SingleMinded
