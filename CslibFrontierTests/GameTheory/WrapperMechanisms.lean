/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.GameTheory.Mechanism.Approximation.Wrapper
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Checked tests for wrapper mechanisms and undominated-strategy implementation (NRTV Ch. 12 §12.5)

Non-vacuous client examples and boundary witnesses for
`CslibFrontier.GameTheory.Mechanism.Approximation.Wrapper`:

* `SingleValuePlayer` evaluation, upward closure, normalization, and `IsFeasibleAlloc` positive
  and negative instances;
* a three-bidder overlapping known single-minded (`KSM-PROC`) auction with `v_max = 4` running
  multiple rounds of bid doubling and winner switching, verifying exact execution, Lemma 12.38
  (`termRound = 3 ≤ 5`), Proposition 12.41 (dominant strategy and power-of-two tie behavior), and
  Theorem 12.45 (`ksmProc_isDominantStrategyImpl`);
* a three-bidder, four-item multi-minded single-value (`1-CA-PROC`) auction (`√4 = 2`) exercising
  bundle shrinking, `GREEDY` blocking, first-time shrink disjointness, winner replacement, and
  retirement, verifying exact execution (`termRound = 3 ≤ 5`), an explicit out-of-`D` strategy
  weakly dominated by `dominateOneCaStrategy`, Lemma 12.47, Claim 12.50, and Theorem 12.51
  (`oneCaProc_isUndominatedImpl`);
* a tight `v_max = 1` boundary test (`Nat.log 2 ⌊1⌋₊ = 0`) showing `termRound = 1 = 2 * 0 + 1`
  is sharp and both `KSM-PROC` and `1-CA-PROC` maintain non-vacuous positive approximation ratios
  at `v_max = 1`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.WrapperMechanisms

open Cslib.GameTheory.Mechanism.Wrapper

/-- Helper to evaluate `Finset.sort` on small concrete finite sets. -/
private theorem finset_sort_eq {α : Type*} {s : Finset α} {r : α → α → Prop}
    {dr : DecidableRel r} {ht : IsTrans α r} {ha : Std.Antisymm r} {htot : Std.Total r}
    (l : List α) (hnodup : l.Nodup) (hmem : ∀ x, x ∈ s ↔ x ∈ l) (hpair : l.Pairwise r) :
    @Finset.sort α s r dr ht ha htot = l :=
  ((List.perm_ext_iff_of_nodup (s.sort_nodup r) hnodup).2 fun x => by
    rw [Finset.mem_sort, hmem]).eq_of_pairwise
    (fun _ _ _ _ h1 h2 => ha.antisymm _ _ h1 h2) (s.pairwise_sort r) hpair

/-! ### 1. Basic `SingleValuePlayer` and `IsFeasibleAlloc` witnesses -/

private def multiMindedPlayer : SingleValuePlayer (Fin 4) where
  value := 4
  desired := {s | ({0, 1} : Finset (Fin 4)) ⊆ s ∨ ({2, 3} : Finset (Fin 4)) ⊆ s}
  one_le_value := by norm_num
  empty_not_mem := by
    rintro (h | h)
    · exact absurd (h (by decide : (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)))) (by decide)
    · exact absurd (h (by decide : (2 : Fin 4) ∈ ({2, 3} : Finset (Fin 4)))) (by decide)
  desired_nonempty := ⟨{0, 1}, Or.inl Finset.Subset.rfl⟩
  upward_closed := by
    intro s t hs hst
    rcases hs with h | h
    · exact Or.inl (h.trans hst)
    · exact Or.inr (h.trans hst)

example : multiMindedPlayer.eval {0, 1} = 4 :=
  multiMindedPlayer.eval_of_mem (Or.inl Finset.Subset.rfl)

example : multiMindedPlayer.eval {2, 3} = 4 :=
  multiMindedPlayer.eval_of_mem (Or.inr Finset.Subset.rfl)

example : multiMindedPlayer.eval {0, 2} = 0 := by
  apply multiMindedPlayer.eval_of_not_mem
  rintro (h | h)
  · exact absurd (h (by decide : (1 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)))) (by decide)
  · exact absurd (h (by decide : (3 : Fin 4) ∈ ({2, 3} : Finset (Fin 4)))) (by decide)

example : multiMindedPlayer.eval ∅ = 0 := multiMindedPlayer.eval_empty

private def goodAlloc : Fin 2 → Finset (Fin 4)
  | 0 => {0, 1}
  | 1 => {2, 3}

private def badAlloc : Fin 2 → Finset (Fin 4)
  | 0 => {0, 1}
  | 1 => {1, 2}

example : IsFeasibleAlloc goodAlloc := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · decide
  · decide
  · exact (hij rfl).elim

example : ¬ IsFeasibleAlloc badAlloc := by
  intro h
  have hd : Disjoint (badAlloc 0) (badAlloc 1) := h (by decide)
  exact Finset.disjoint_left.1 hd (by decide : (1 : Fin 4) ∈ badAlloc 0) (by decide)

/-! ### 2. Concrete KSM auction (`Wrapper + KSM-PROC`, Lemma 12.38 & Theorem 12.45) -/

private def ksmBundle : Fin 3 → Finset (Fin 3)
  | 0 => {0, 1}
  | 1 => {1, 2}
  | 2 => {0, 2}

private theorem ksmBundle_nonempty (i : Fin 3) : (ksmBundle i).Nonempty := by
  fin_cases i <;> decide

private noncomputable def ksmVal : Fin 3 → ℝ
  | 0 => 4
  | 1 => 3
  | 2 => 3 / 2

private theorem ksmVal_ge_one (i : Fin 3) : 1 ≤ ksmVal i := by
  fin_cases i <;> norm_num [ksmVal]

private theorem ksmVal_le_four (i : Fin 3) : ksmVal i ≤ 4 := by
  fin_cases i <;> norm_num [ksmVal]

/-- Exact maximum-single-bidder algorithm for pairwise-overlapping bundles (`1`-approximation). -/
private noncomputable def ksmMaxAlg (w : Fin 3 → ℝ) : Finset (Fin 3) := by
  classical
  exact if w 1 ≤ w 0 ∧ w 2 ≤ w 0 then {0} else if w 2 ≤ w 1 then {1} else {2}

private theorem ksmMaxAlg_feas (w : Fin 3 → ℝ) (_ : ∀ i, 0 ≤ w i) :
    (ksmMaxAlg w : Set (Fin 3)).PairwiseDisjoint ksmBundle := by
  classical
  unfold ksmMaxAlg
  split_ifs <;> simp only [Finset.coe_singleton, Set.pairwiseDisjoint_singleton]

private theorem ksmMaxAlg_approx (w : Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i) (W : Finset (Fin 3))
    (hpw : (W : Set (Fin 3)).PairwiseDisjoint ksmBundle) :
    ∑ i ∈ W, w i ≤ 1 * ∑ i ∈ ksmMaxAlg w, w i := by
  classical
  rw [one_mul]
  have hcard : W.card ≤ 1 := by
    by_contra hgt
    obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.1 (Nat.lt_of_not_ge hgt)
    have hd : Disjoint (ksmBundle a) (ksmBundle b) := hpw ha hb hne
    fin_cases a <;> fin_cases b
    · exact hne rfl
    · exact Finset.disjoint_left.1 hd (by decide : (1 : Fin 3) ∈ ksmBundle 0) (by decide)
    · exact Finset.disjoint_left.1 hd (by decide : (0 : Fin 3) ∈ ksmBundle 0) (by decide)
    · exact Finset.disjoint_left.1 hd (by decide : (1 : Fin 3) ∈ ksmBundle 1) (by decide)
    · exact hne rfl
    · exact Finset.disjoint_left.1 hd (by decide : (2 : Fin 3) ∈ ksmBundle 1) (by decide)
    · exact Finset.disjoint_left.1 hd (by decide : (0 : Fin 3) ∈ ksmBundle 2) (by decide)
    · exact Finset.disjoint_left.1 hd (by decide : (2 : Fin 3) ∈ ksmBundle 2) (by decide)
    · exact hne rfl
  have hmax : ∀ i : Fin 3, w i ≤ ∑ k ∈ ksmMaxAlg w, w k := by
    intro i
    unfold ksmMaxAlg
    split_ifs with h1 h2
    · rw [Finset.sum_singleton]
      match i with
      | 0 => exact le_rfl
      | 1 => exact h1.1
      | 2 => exact h1.2
    · rw [Finset.sum_singleton]
      push Not at h1
      match i with
      | 0 =>
        by_cases h01 : w 1 ≤ w 0
        · linarith [h1 h01, h2]
        · linarith
      | 1 => exact le_rfl
      | 2 => exact h2
    · rw [Finset.sum_singleton]
      push Not at h1 h2
      match i with
      | 0 =>
        by_cases h01 : w 1 ≤ w 0
        · linarith [h1 h01]
        · linarith
      | 1 => linarith
      | 2 => exact le_rfl
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hcard with h0 | h1
  · rw [Finset.card_eq_zero.1 h0, Finset.sum_empty]
    exact Finset.sum_nonneg fun i _ => hw i
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 h1
    rw [Finset.sum_singleton]
    exact hmax i

/-- Computable natural-number KSM strategy equivalent to `ksmDominantStrategy` on `ksmVal`. -/
private def ksmCompStrat (i : Fin 3) : KsmStrategy (Fin 3) (Fin 3) :=
  fun _ st _ _ =>
    match i with
    | 0 => decide (2 * st.val 0 < 4)
    | 1 => decide (2 * st.val 1 < 3)
    | 2 => decide (4 * st.val 2 < 3)

private theorem ksmCompStrat_eq_dominant (i : Fin 3) :
    ksmCompStrat i = ksmDominantStrategy i (ksmVal i) := by
  funext past st W' s'
  classical
  match i with
  | ⟨0, _⟩ =>
    change decide (2 * st.val 0 < 4) = decide (2 * (st.val 0 : ℝ) < 4)
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq]
    constructor <;> intro h
    · have : ((2 * st.val 0 : ℕ) : ℝ) < (4 : ℕ) := by exact_mod_cast h
      push_cast at this; linarith
    · have : ((2 * st.val 0 : ℕ) : ℝ) < (4 : ℕ) := by push_cast; linarith
      exact_mod_cast this
  | ⟨1, _⟩ =>
    change decide (2 * st.val 1 < 3) = decide (2 * (st.val 1 : ℝ) < 3)
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq]
    constructor <;> intro h
    · have : ((2 * st.val 1 : ℕ) : ℝ) < (3 : ℕ) := by exact_mod_cast h
      push_cast at this; linarith
    · have : ((2 * st.val 1 : ℕ) : ℝ) < (3 : ℕ) := by push_cast; linarith
      exact_mod_cast this
  | ⟨2, _⟩ =>
    change decide (4 * st.val 2 < 3) = decide (2 * (st.val 2 : ℝ) < 3 / 2)
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq]
    constructor <;> intro h
    · have : ((4 * st.val 2 : ℕ) : ℝ) < (3 : ℕ) := by exact_mod_cast h
      push_cast at this; linarith
    · have : ((4 * st.val 2 : ℕ) : ℝ) < (3 : ℕ) := by push_cast; linarith
      exact_mod_cast this

/-- **Theorem 12.45** instantiated on our 3-bidder KSM auction with `v_max = 4` (`c = 1`, factor
`1 + 2 * (2 * Nat.log 2 4 + 1) * 1 = 11`). -/
example :
    let players := fun i =>
      SingleValuePlayer.singleMinded (ksmBundle i) (ksmBundle_nonempty i) (ksmVal i)
        (ksmVal_ge_one i)
    (ksmProc ksmBundle ksmMaxAlg).IsDominantStrategyImpl players
      (fun i => ksmDominantStrategy i (ksmVal i)) 11 := by
  have h := ksmProc_isDominantStrategyImpl ksmBundle ksmBundle_nonempty ksmVal ksmVal_ge_one
    ksmVal_le_four (c := 1) (by norm_num) ksmMaxAlg_feas ksmMaxAlg_approx
  have hlog : Nat.log 2 ⌊(4 : ℝ)⌋₊ = 2 := by
    have hf : ⌊(4 : ℝ)⌋₊ = 4 := by norm_num
    rw [hf]; decide
  simpa only [hlog, Nat.cast_ofNat, mul_one,
    show (1 : ℝ) + 2 * (2 * 2 + 1) = 11 by norm_num] using h

/-- **Proposition 12.41** power-of-two tie witness: at `v = 4` and `st.val 0 = 2`,
`ksmDominantStrategy` retires (`false`) since `4 / 2 ≤ 2 ≤ 4`. -/
example (past : List (WrapperState (Fin 3) (Fin 3))) (W' : Finset (Fin 3))
    (s' : Fin 3 → Finset (Fin 3)) :
    let st : WrapperState (Fin 3) (Fin 3) := ⟨fun _ => 2, ksmBundle, ∅, ∅⟩
    ksmDominantStrategy (0 : Fin 3) 4 past st W' s' = false := by
  intro st
  rw [ksmDominantStrategy_retire_iff (0 : Fin 3) past st W' s' (by norm_num [st])]
  norm_num [st]

private theorem univ_sort_fin3 :
    (Finset.univ : Finset (Fin 3)).sort (· ≤ ·) = [0, 1, 2] :=
  finset_sort_eq [0, 1, 2] (by decide)
    (fun x => by fin_cases x <;> decide) (by decide)

private theorem ksmExtendPareto_singleton (L : Finset (Fin 3)) (w : Fin 3) :
    ksmExtendPareto ksmBundle L {w} = {w} := by
  have hno : ∀ a : Fin 3,
      ¬ (a ∉ L ∧ a ∉ ({w} : Finset (Fin 3)) ∧
          ∀ k ∈ ({w} : Finset (Fin 3)), Disjoint (ksmBundle a) (ksmBundle k)) := by
    intro a ⟨_, hnw, hd⟩
    have hdw : Disjoint (ksmBundle a) (ksmBundle w) := hd w (Finset.mem_singleton_self w)
    fin_cases a <;> fin_cases w
    · exact hnw (Finset.mem_singleton_self _)
    · exact Finset.disjoint_left.1 hdw (by decide : (1 : Fin 3) ∈ ksmBundle 0) (by decide)
    · exact Finset.disjoint_left.1 hdw (by decide : (0 : Fin 3) ∈ ksmBundle 0) (by decide)
    · exact Finset.disjoint_left.1 hdw (by decide : (1 : Fin 3) ∈ ksmBundle 1) (by decide)
    · exact hnw (Finset.mem_singleton_self _)
    · exact Finset.disjoint_left.1 hdw (by decide : (2 : Fin 3) ∈ ksmBundle 1) (by decide)
    · exact Finset.disjoint_left.1 hdw (by decide : (0 : Fin 3) ∈ ksmBundle 2) (by decide)
    · exact Finset.disjoint_left.1 hdw (by decide : (2 : Fin 3) ∈ ksmBundle 2) (by decide)
    · exact hnw (Finset.mem_singleton_self _)
  rw [ksmExtendPareto, univ_sort_fin3]
  simp only [List.foldl_cons, List.foldl_nil, hno 0, hno 1, hno 2, ↓reduceIte]

/-- Exact multi-round trace of `Wrapper + KSM-PROC` on the 3-bidder overlapping auction:
terminates at `J = 3 ≤ 5 = 2 * Nat.log 2 4 + 1` with winner `{0}` paying `2` and welfare `4`. -/
example :
    let P := ksmProc ksmBundle ksmMaxAlg
    let σ := fun i => ksmDominantStrategy (M := Fin 3) i (ksmVal i)
    ¬ TerminatedAt P σ 0 ∧
    ¬ TerminatedAt P σ 1 ∧
    ¬ TerminatedAt P σ 2 ∧
    TerminatedAt P σ 3 ∧
    termRound P σ = 3 ∧
    (wrapperState P σ 3).winners = {0} ∧
    (wrapperState P σ 3).losers = {1, 2} ∧
    (wrapperState P σ 3).val 0 = 2 := by
  classical
  set P := ksmProc ksmBundle ksmMaxAlg
  have hσ : (fun i => ksmDominantStrategy (M := Fin 3) i (ksmVal i)) = ksmCompStrat :=
    funext fun i => (ksmCompStrat_eq_dominant i).symm
  rw [hσ]
  -- Helper to characterize `ksmProc.proc` on any state with at least one positive bid.
  have hst0 : wrapperState P ksmCompStrat 0 = ⟨fun _ => 1, ksmBundle, ∅, ∅⟩ := rfl
  have h0T : ¬ TerminatedAt P ksmCompStrat 0 := by
    rw [TerminatedAt, hst0]; decide
  have hst1 : wrapperState P ksmCompStrat 1 =
      ⟨![1, 2, 0], ksmBundle, {0}, {2}⟩ := by
    have hstep : wrapperState P ksmCompStrat 1 =
        wrapperNext P ksmCompStrat [] (wrapperState P ksmCompStrat 0) := rfl
    rw [hstep, hst0, wrapperNext]
    have hnt : (∅ : Finset (Fin 3)) ∪ ∅ ≠ Finset.univ := by decide
    simp only [hnt, ↓reduceIte, P, ksmProc, ksmMaxAlg, Nat.cast_one, le_refl, and_self]
    have hf : (({0} : Finset (Fin 3)).filter fun i => 0 < (1 : ℕ)) = {0} := by decide
    simp only [hf, Finset.sum_empty, Finset.sum_singleton, Nat.zero_le, ↓reduceIte,
      ksmExtendPareto_singleton, WrapperState.mk.injEq]
    refine ⟨?_, trivial, trivial, ?_⟩
    · funext i; fin_cases i <;> decide
    · ext i; fin_cases i <;> decide
  have h1T : ¬ TerminatedAt P ksmCompStrat 1 := by
    rw [TerminatedAt, hst1]; decide
  have hst2 : wrapperState P ksmCompStrat 2 =
      ⟨![2, 2, 0], ksmBundle, {1}, {2}⟩ := by
    have hstep : wrapperState P ksmCompStrat 2 =
        wrapperNext P ksmCompStrat (wrapperRunHist P ksmCompStrat 1).2
          (wrapperState P ksmCompStrat 1) := rfl
    rw [hstep, hst1, wrapperNext]
    have hnt : ({0} : Finset (Fin 3)) ∪ {2} ≠ Finset.univ := by decide
    simp only [hnt, ↓reduceIte, P, ksmProc, ksmMaxAlg]
    have hmax1 :
        (if ((![1, 2, 0] : Fin 3 → ℕ) 1 : ℝ) ≤ ((![1, 2, 0] : Fin 3 → ℕ) 0 : ℝ) ∧
            ((![1, 2, 0] : Fin 3 → ℕ) 2 : ℝ) ≤ ((![1, 2, 0] : Fin 3 → ℕ) 0 : ℝ)
         then ({0} : Finset (Fin 3))
         else if ((![1, 2, 0] : Fin 3 → ℕ) 2 : ℝ) ≤ ((![1, 2, 0] : Fin 3 → ℕ) 1 : ℝ)
         then {1} else {2}) = {1} := by norm_num
    simp only [hmax1]
    have hf : (({1} : Finset (Fin 3)).filter fun i => 0 < (![1, 2, 0] : Fin 3 → ℕ) i) = {1} := by
      decide
    simp only [hf, Finset.sum_singleton, Matrix.cons_val_zero, Matrix.cons_val_one,
      show (1 : ℕ) ≤ 2 by decide, ↓reduceIte, ksmExtendPareto_singleton, WrapperState.mk.injEq]
    refine ⟨?_, trivial, trivial, ?_⟩
    · funext i; fin_cases i <;> decide
    · ext i; fin_cases i <;> decide
  have h2T : ¬ TerminatedAt P ksmCompStrat 2 := by
    rw [TerminatedAt, hst2]; decide
  have hst3 : wrapperState P ksmCompStrat 3 =
      ⟨![2, 0, 0], ksmBundle, {0}, {1, 2}⟩ := by
    have hstep : wrapperState P ksmCompStrat 3 =
        wrapperNext P ksmCompStrat (wrapperRunHist P ksmCompStrat 2).2
          (wrapperState P ksmCompStrat 2) := rfl
    rw [hstep, hst2, wrapperNext]
    have hnt : ({1} : Finset (Fin 3)) ∪ {2} ≠ Finset.univ := by decide
    simp only [hnt, ↓reduceIte, P, ksmProc, ksmMaxAlg]
    have hmax0 :
        (if ((![2, 2, 0] : Fin 3 → ℕ) 1 : ℝ) ≤ ((![2, 2, 0] : Fin 3 → ℕ) 0 : ℝ) ∧
            ((![2, 2, 0] : Fin 3 → ℕ) 2 : ℝ) ≤ ((![2, 2, 0] : Fin 3 → ℕ) 0 : ℝ)
         then ({0} : Finset (Fin 3))
         else if ((![2, 2, 0] : Fin 3 → ℕ) 2 : ℝ) ≤ ((![2, 2, 0] : Fin 3 → ℕ) 1 : ℝ)
         then {1} else {2}) = {0} := by norm_num
    simp only [hmax0]
    have hf : (({0} : Finset (Fin 3)).filter fun i => 0 < (![2, 2, 0] : Fin 3 → ℕ) i) = {0} := by
      decide
    simp only [hf, Finset.sum_singleton, Matrix.cons_val_zero, Matrix.cons_val_one,
      le_refl, ↓reduceIte, ksmExtendPareto_singleton, WrapperState.mk.injEq]
    refine ⟨?_, trivial, trivial, ?_⟩
    · funext i; fin_cases i <;> decide
    · ext i; fin_cases i <;> decide
  have h3T : TerminatedAt P ksmCompStrat 3 := by
    rw [TerminatedAt, hst3]; decide
  have hJ : termRound P ksmCompStrat = 3 := by
    have hle : termRound P ksmCompStrat ≤ 3 := termRound_le_of_terminatedAt h3T
    have hsp : TerminatedAt P ksmCompStrat (termRound P ksmCompStrat) := termRound_spec ⟨3, h3T⟩
    interval_cases h : termRound P ksmCompStrat
    · exact absurd (h ▸ hsp) h0T
    · exact absurd (h ▸ hsp) h1T
    · exact absurd (h ▸ hsp) h2T
    · rfl
  exact ⟨h0T, h1T, h2T, h3T, hJ, by rw [hst3], by rw [hst3], by rw [hst3]; rfl⟩

/-! ### 3. Concrete multi-minded `1-CA-PROC` auction (weak dominance & Theorem 12.51) -/

private def oneCaPlayers : Fin 3 → SingleValuePlayer (Fin 4)
  | 0 => multiMindedPlayer
  | 1 => SingleValuePlayer.singleMinded {0, 1} (by decide) 3 (by norm_num)
  | 2 => SingleValuePlayer.singleMinded {2, 3} (by decide) 2 (by norm_num)

private theorem oneCaPlayers_le_four (i : Fin 3) : (oneCaPlayers i).value ≤ 4 := by
  fin_cases i <;> norm_num [oneCaPlayers, multiMindedPlayer, SingleValuePlayer.singleMinded]

/-- Explicit computable strategies in `oneCaStrategyClass` for `oneCaPlayers`. -/
private def oneCaGoodStrat : Fin 3 → OneCaStrategy (Fin 3) (Fin 4)
  | 0 =>
    { shrink := fun view =>
        if IsValidShrink view.currentGreedy view.currentBundles (view.state.bundle 0) {0, 1} then
          some {0, 1}
        else if IsValidShrink view.currentGreedy view.currentBundles (view.state.bundle 0) {2, 3}
          then some {2, 3}
        else none
      double := fun _ st _ _ => decide (2 * st.val 0 < 4) }
  | 1 =>
    { shrink := fun view =>
        if IsValidShrink view.currentGreedy view.currentBundles (view.state.bundle 1) {0, 1} then
          some {0, 1}
        else none
      double := fun _ st _ _ => decide (2 * st.val 1 < 3) }
  | 2 =>
    { shrink := fun view =>
        if IsValidShrink view.currentGreedy view.currentBundles (view.state.bundle 2) {2, 3} then
          some {2, 3}
        else none
      double := fun _ st _ _ => decide (2 * st.val 2 < 2) }

private theorem oneCaGoodStrat_mem (i : Fin 3) :
    oneCaGoodStrat i ∈ oneCaStrategyClass (oneCaPlayers i) i := by
  have hsqrt4 : Nat.sqrt (Fintype.card (Fin 4)) = 2 := by
    rw [Fintype.card_fin]
    exact (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  match i with
  | 0 =>
    refine ⟨?_, ?_, ?_⟩
    · intro view b hsh _
      simp only [oneCaGoodStrat] at hsh
      split_ifs at hsh with h1 h2
      · cases hsh; exact Or.inl Finset.Subset.rfl
      · cases hsh; exact Or.inr Finset.Subset.rfl
    · intro view _ ⟨b, hvb, hdes⟩
      have hsub : ({0, 1} : Finset (Fin 4)) ⊆ b ∨ ({2, 3} : Finset (Fin 4)) ⊆ b := hdes
      rcases hsub with h01 | h23
      · have hv01 : IsValidShrink view.currentGreedy view.currentBundles
            (view.state.bundle 0) {0, 1} :=
          ⟨by decide, h01.trans hvb.2.1, by rw [hsqrt4]; decide⟩
        exact ⟨{0, 1}, by simp only [oneCaGoodStrat, hv01, ↓reduceIte], hv01,
          Or.inl Finset.Subset.rfl⟩
      · have hv23 : IsValidShrink view.currentGreedy view.currentBundles
            (view.state.bundle 0) {2, 3} :=
          ⟨by decide, h23.trans hvb.2.1, by rw [hsqrt4]; decide⟩
        by_cases hv01 : IsValidShrink view.currentGreedy view.currentBundles
            (view.state.bundle 0) {0, 1}
        · exact ⟨{0, 1}, by simp only [oneCaGoodStrat, hv01, ↓reduceIte], hv01,
            Or.inl Finset.Subset.rfl⟩
        · exact ⟨{2, 3}, by simp only [oneCaGoodStrat, hv01, hv23, ↓reduceIte], hv23,
            Or.inr Finset.Subset.rfl⟩
    · intro _ st _ _
      change ((4 : ℝ) < 2 * (st.val 0 : ℝ) → decide (2 * st.val 0 < 4) = false) ∧
        (2 * (st.val 0 : ℝ) < 4 → decide (2 * st.val 0 < 4) = true)
      constructor
      · intro hgt
        rw [decide_eq_false_iff_not]
        intro hlt
        have : ((2 * st.val 0 : ℕ) : ℝ) < (4 : ℕ) := by exact_mod_cast hlt
        push_cast at this; linarith
      · intro hlt
        rw [decide_eq_true_iff]
        have : ((2 * st.val 0 : ℕ) : ℝ) < (4 : ℕ) := by push_cast; linarith
        exact_mod_cast this
  | 1 =>
    refine ⟨?_, ?_, ?_⟩
    · intro view b hsh _
      simp only [oneCaGoodStrat] at hsh
      split_ifs at hsh with h1
      · cases hsh; exact Finset.Subset.rfl
    · intro view _ ⟨b, hvb, hdes⟩
      have hv01 : IsValidShrink view.currentGreedy view.currentBundles
          (view.state.bundle 1) {0, 1} :=
        ⟨by decide, hdes.trans hvb.2.1, by rw [hsqrt4]; decide⟩
      exact ⟨{0, 1}, by simp only [oneCaGoodStrat, hv01, ↓reduceIte], hv01, Finset.Subset.rfl⟩
    · intro _ st _ _
      change ((3 : ℝ) < 2 * (st.val 1 : ℝ) → decide (2 * st.val 1 < 3) = false) ∧
        (2 * (st.val 1 : ℝ) < 3 → decide (2 * st.val 1 < 3) = true)
      constructor
      · intro hgt
        rw [decide_eq_false_iff_not]
        intro hlt
        have : ((2 * st.val 1 : ℕ) : ℝ) < (3 : ℕ) := by exact_mod_cast hlt
        push_cast at this; linarith
      · intro hlt
        rw [decide_eq_true_iff]
        have : ((2 * st.val 1 : ℕ) : ℝ) < (3 : ℕ) := by push_cast; linarith
        exact_mod_cast this
  | 2 =>
    refine ⟨?_, ?_, ?_⟩
    · intro view b hsh _
      simp only [oneCaGoodStrat] at hsh
      split_ifs at hsh with h1
      · cases hsh; exact Finset.Subset.rfl
    · intro view _ ⟨b, hvb, hdes⟩
      have hv23 : IsValidShrink view.currentGreedy view.currentBundles
          (view.state.bundle 2) {2, 3} :=
        ⟨by decide, hdes.trans hvb.2.1, by rw [hsqrt4]; decide⟩
      exact ⟨{2, 3}, by simp only [oneCaGoodStrat, hv23, ↓reduceIte], hv23, Finset.Subset.rfl⟩
    · intro _ st _ _
      change ((2 : ℝ) < 2 * (st.val 2 : ℝ) → decide (2 * st.val 2 < 2) = false) ∧
        (2 * (st.val 2 : ℝ) < 2 → decide (2 * st.val 2 < 2) = true)
      constructor
      · intro hgt
        rw [decide_eq_false_iff_not]
        intro hlt
        have : ((2 * st.val 2 : ℕ) : ℝ) < (2 : ℕ) := by exact_mod_cast hlt
        push_cast at this; linarith
      · intro hlt
        rw [decide_eq_true_iff]
        have : ((2 * st.val 2 : ℕ) : ℝ) < (2 : ℕ) := by push_cast; linarith
        exact_mod_cast this

/-- Single-player step function matching the `foldl` body of `oneCaProc` on `oneCaGoodStrat`,
allowing each step of a concrete trace to be evaluated individually without term blowup. -/
private def oneCaStep3 (past : List (WrapperState (Fin 3) (Fin 4)))
    (st : WrapperState (Fin 3) (Fin 4))
    (acc : Finset (Fin 3) × Finset (Fin 3) × Finset (Fin 3) × (Fin 3 → Finset (Fin 4)))
    (i : Fin 3) :
    Finset (Fin 3) × Finset (Fin 3) × Finset (Fin 3) × (Fin 3 → Finset (Fin 4)) :=
  let (wSet, mSet, gSet, bundles) := acc
  let bNew :=
    if i ∈ st.winners then bundles i
    else
      let view : OneCaShrinkView (Fin 3) (Fin 4) := ⟨past, st, wSet, mSet, gSet, bundles⟩
      match (oneCaGoodStrat i).shrink view with
      | some b => if IsValidShrink gSet bundles (bundles i) b then b else bundles i
      | none => bundles i
  let sNext := Function.update bundles i bNew
  if bNew.card ≤ Nat.sqrt (Fintype.card (Fin 4)) then
    let wNext := if bNew ⊆ freeItems wSet sNext then insert i wSet else wSet
    let mNext := if bNew ⊆ freeItems mSet sNext then insert i mSet else mSet
    let gNext := if bNew ⊆ freeItems gSet sNext then insert i gSet else gSet
    (wNext, mNext, gNext, sNext)
  else
    (wSet, mSet, gSet, sNext)

private theorem sqrt_fin4 : Nat.sqrt (Fintype.card (Fin 4)) = 2 := by
  rw [Fintype.card_fin]
  exact (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm

private theorem oneCaProc_proc_of_fold3 (past : List (WrapperState (Fin 3) (Fin 4)))
    (st : WrapperState (Fin 3) (Fin 4)) (a b c : Fin 3)
    (hnodup : ([a, b, c] : List (Fin 3)).Nodup)
    (hmem : ∀ x : Fin 3,
      x ∈ (Finset.univ.filter fun i => 0 < st.val i) ↔ x ∈ ([a, b, c] : List (Fin 3)))
    (hpair : ([a, b, c] : List (Fin 3)).Pairwise
      fun i k => st.val k < st.val i ∨ (st.val k = st.val i ∧ i ≤ k))
    {res : Finset (Fin 3) × Finset (Fin 3) × Finset (Fin 3) × (Fin 3 → Finset (Fin 4))}
    (hfold : ([a, b, c] : List (Fin 3)).foldl (oneCaStep3 past st)
      (st.winners, {a}, ∅, st.bundle) = res) :
    oneCaProc.proc oneCaGoodStrat past st =
      let sumW := ∑ k ∈ res.1, st.val k
      let sumM := ∑ k ∈ res.2.1, st.val k
      let sumG := ∑ k ∈ res.2.2.1, st.val k
      (if sumM ≤ sumW ∧ sumG ≤ sumW then res.1 else if sumG ≤ sumM then res.2.1 else res.2.2.1,
        res.2.2.2) := by
  dsimp only [oneCaProc]
  rw [finset_sort_eq ([a, b, c] : List (Fin 3)) hnodup hmem hpair]
  suffices h :
      ∀ (f : (Finset (Fin 3) × Finset (Fin 3) × Finset (Fin 3) × (Fin 3 → Finset (Fin 4))) →
        Fin 3 → Finset (Fin 3) × Finset (Fin 3) × Finset (Fin 3) × (Fin 3 → Finset (Fin 4))),
        f = oneCaStep3 past st →
        let t := ([a, b, c] : List (Fin 3)).foldl f (st.winners, {a}, ∅, st.bundle)
        (if ∑ k ∈ t.2.1, st.val k ≤ ∑ k ∈ t.1, st.val k ∧
              ∑ k ∈ t.2.2.1, st.val k ≤ ∑ k ∈ t.1, st.val k then t.1
          else if ∑ k ∈ t.2.2.1, st.val k ≤ ∑ k ∈ t.2.1, st.val k then t.2.1 else t.2.2.1,
          t.2.2.2) =
        (if ∑ k ∈ res.2.1, st.val k ≤ ∑ k ∈ res.1, st.val k ∧
              ∑ k ∈ res.2.2.1, st.val k ≤ ∑ k ∈ res.1, st.val k then res.1
          else if ∑ k ∈ res.2.2.1, st.val k ≤ ∑ k ∈ res.2.1, st.val k then res.2.1 else res.2.2.1,
          res.2.2.2) by
    exact h _ (by
      funext ⟨wSet, mSet, gSet, bundles⟩ i
      dsimp only [oneCaStep3]
      by_cases hi : i ∈ st.winners
      · simp only [hi, ↓reduceIte]
      · simp only [hi, ↓reduceIte]
        cases (oneCaGoodStrat i).shrink ⟨past, st, wSet, mSet, gSet, bundles⟩ with
        | none => split_ifs <;> rfl
        | some b =>
          by_cases hv : IsValidShrink gSet bundles (bundles i) b <;>
            simp only [hv, ↓reduceIte])
  rintro f rfl
  dsimp only
  rw [hfold]

/-- Exact multi-round trace of `Wrapper + 1-CA-PROC` on the 3-bidder, 4-item multi-minded auction:
* Round 0: bidders `0` and `2` first-time-shrink to disjoint bundles `{0, 1}` and `{2, 3}` and win
  `W₁ = {0, 2}`, while bidder `1` is blocked by `GREEDY` and doubles to `val 1 = 2`.
* Round 1: bidder `1` shrinks to `{0, 1}` and replaces bidder `0` (`W₂ = {1, 2}`), while bidder `0`
  doubles to `val 0 = 2`.
* Round 2: bidder `0` ties `W₂ = {1, 2}` and retires (`val 0 = 0`), terminating at `J = 3 ≤ 5`. -/
example :
    (wrapperState oneCaProc oneCaGoodStrat 1).winners = {0, 2} ∧
    (wrapperState oneCaProc oneCaGoodStrat 1).bundle 0 = {0, 1} ∧
    (wrapperState oneCaProc oneCaGoodStrat 1).bundle 2 = {2, 3} ∧
    (wrapperState oneCaProc oneCaGoodStrat 1).val 1 = 2 ∧
    (wrapperState oneCaProc oneCaGoodStrat 2).winners = {1, 2} ∧
    (wrapperState oneCaProc oneCaGoodStrat 2).bundle 1 = {0, 1} ∧
    (wrapperState oneCaProc oneCaGoodStrat 2).val 0 = 2 ∧
    ¬ TerminatedAt oneCaProc oneCaGoodStrat 2 ∧
    TerminatedAt oneCaProc oneCaGoodStrat 3 ∧
    termRound oneCaProc oneCaGoodStrat = 3 ∧
    (wrapperState oneCaProc oneCaGoodStrat 3).winners = {1, 2} ∧
    (wrapperState oneCaProc oneCaGoodStrat 3).losers = {0} := by
  let st0 : WrapperState (Fin 3) (Fin 4) := ⟨fun _ => 1, fun _ => Finset.univ, ∅, ∅⟩
  let b01 : Fin 3 → Finset (Fin 4) := ![{0, 1}, Finset.univ, Finset.univ]
  let b02 : Fin 3 → Finset (Fin 4) := ![{0, 1}, Finset.univ, {2, 3}]
  let b12 : Fin 3 → Finset (Fin 4) := ![{0, 1}, {0, 1}, {2, 3}]
  let st1 : WrapperState (Fin 3) (Fin 4) := ⟨![1, 2, 1], b02, {0, 2}, ∅⟩
  let st2 : WrapperState (Fin 3) (Fin 4) := ⟨![2, 2, 1], b12, {1, 2}, ∅⟩
  have hst0 : wrapperState oneCaProc oneCaGoodStrat 0 = st0 := rfl
  have h0T : ¬ TerminatedAt oneCaProc oneCaGoodStrat 0 := by
    rw [TerminatedAt, hst0]; decide
  -- Round 0 → 1: active order is `[0, 1, 2]`.
  have hst1 : wrapperState oneCaProc oneCaGoodStrat 1 = st1 := by
    have hstep : wrapperState oneCaProc oneCaGoodStrat 1 =
        wrapperNext oneCaProc oneCaGoodStrat [] (wrapperState oneCaProc oneCaGoodStrat 0) := rfl
    rw [hstep, hst0, wrapperNext]
    have hnt : st0.winners ∪ st0.losers ≠ Finset.univ := by decide
    simp only [hnt, ↓reduceIte]
    have hstep0 : oneCaStep3 [] st0 (∅, {0}, ∅, st0.bundle) 0 = ({0}, {0}, {0}, b01) := by
      have hv0 : IsValidShrink (∅ : Finset (Fin 3)) st0.bundle (st0.bundle 0) {0, 1} := by
        simp only [IsValidShrink, freeItems, sqrt_fin4]; decide
      have hu : Function.update st0.bundle 0 {0, 1} = b01 := by funext i; fin_cases i <;> rfl
      have hfw : ({0, 1} : Finset (Fin 4)) ⊆ freeItems (∅ : Finset (Fin 3)) b01 := by
        simp only [freeItems]; decide
      have hfm : ¬ ({0, 1} : Finset (Fin 4)) ⊆ freeItems ({0} : Finset (Fin 3)) b01 := by
        intro h
        have := h (by decide : (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)))
        simp only [freeItems, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_singleton,
          exists_eq_left] at this
        exact this.2 (by decide)
      dsimp only [oneCaStep3, oneCaGoodStrat]
      simp only [show (0 : Fin 3) ∉ st0.winners by decide, hv0, ↓reduceIte, hu, sqrt_fin4,
        show ({0, 1} : Finset (Fin 4)).card ≤ 2 by decide, hfw, hfm]
      rfl
    have hstep1 : oneCaStep3 [] st0 ({0}, {0}, {0}, b01) 1 = ({0}, {0}, {0}, b01) := by
      have hv1 : ¬ IsValidShrink ({0} : Finset (Fin 3)) b01 (st0.bundle 1) {0, 1} := by
        intro ⟨_, hsub, _⟩
        have := hsub (by decide : (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)))
        simp only [freeItems, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_biUnion,
          Finset.mem_singleton, exists_eq_left] at this
        exact this.1.2 (by decide)
      dsimp only [oneCaStep3, oneCaGoodStrat]
      simp only [show (1 : Fin 3) ∉ st0.winners by decide, hv1, ↓reduceIte,
        Function.update_eq_self, sqrt_fin4, show ¬ (b01 1).card ≤ 2 by decide]
    have hstep2 : oneCaStep3 [] st0 ({0}, {0}, {0}, b01) 2 = ({0, 2}, {0, 2}, {0, 2}, b02) := by
      have hv2 : IsValidShrink ({0} : Finset (Fin 3)) b01 (st0.bundle 2) {2, 3} := by
        refine ⟨by decide, fun x hx => ?_, by rw [sqrt_fin4]; decide⟩
        simp only [freeItems, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_biUnion, Finset.mem_singleton, exists_eq_left]
        fin_cases x <;> simp_all [b01, st0]
      have hv2' : IsValidShrink ({0} : Finset (Fin 3)) b01 (b01 2) {2, 3} := hv2
      have hu : Function.update b01 2 {2, 3} = b02 := by funext i; fin_cases i <;> rfl
      have hf2 : ({2, 3} : Finset (Fin 4)) ⊆ freeItems ({0} : Finset (Fin 3)) b02 := by
        intro x hx
        simp only [freeItems, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion,
          Finset.mem_singleton, exists_eq_left]
        fin_cases x <;> simp_all [b02]
      dsimp only [oneCaStep3, oneCaGoodStrat]
      simp only [show (2 : Fin 3) ∉ st0.winners by decide, hv2, hv2', ↓reduceIte, hu, sqrt_fin4,
        show ({2, 3} : Finset (Fin 4)).card ≤ 2 by decide, hf2]
      have hins : insert (2 : Fin 3) ({0} : Finset (Fin 3)) = {0, 2} := by decide
      rw [hins]
    have hfold0 : ([0, 1, 2] : List (Fin 3)).foldl (oneCaStep3 [] st0)
        (st0.winners, {0}, ∅, st0.bundle) = ({0, 2}, {0, 2}, {0, 2}, b02) := by
      rw [List.foldl_cons, hstep0, List.foldl_cons, hstep1, List.foldl_cons, hstep2,
        List.foldl_nil]
    have hproc : oneCaProc.proc oneCaGoodStrat [] st0 = ({0, 2}, b02) := by
      rw [oneCaProc_proc_of_fold3 [] st0 0 1 2 (by decide)
        (fun x => by fin_cases x <;> decide) (by decide) hfold0]
      simp only [le_refl, and_self, ↓reduceIte]
    simp only [hproc, st1, WrapperState.mk.injEq]
    refine ⟨?_, trivial, trivial, ?_⟩
    · funext i; fin_cases i <;> decide
    · ext i; fin_cases i <;> decide
  have h1T : ¬ TerminatedAt oneCaProc oneCaGoodStrat 1 := by
    rw [TerminatedAt, hst1]; decide
  -- Round 1 → 2: active order is `[1, 0, 2]` since `val 1 = 2 > 1`.
  have hst2 : wrapperState oneCaProc oneCaGoodStrat 2 = st2 := by
    have hstep : wrapperState oneCaProc oneCaGoodStrat 2 =
        wrapperNext oneCaProc oneCaGoodStrat (wrapperRunHist oneCaProc oneCaGoodStrat 1).2
          (wrapperState oneCaProc oneCaGoodStrat 1) := rfl
    rw [hstep, hst1, wrapperNext]
    set past1 := (wrapperRunHist oneCaProc oneCaGoodStrat 1).2
    have hnt : st1.winners ∪ st1.losers ≠ Finset.univ := by decide
    simp only [hnt, ↓reduceIte]
    have hnotfW01 : ¬ ({0, 1} : Finset (Fin 4)) ⊆ freeItems ({0, 2} : Finset (Fin 3)) b12 := by
      intro h
      have := h (by decide : (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)))
      simp only [freeItems, Finset.mem_sdiff, Finset.mem_biUnion] at this
      exact this.2 ⟨0, by decide, by decide⟩
    have hnotfM01 : ¬ ({0, 1} : Finset (Fin 4)) ⊆ freeItems ({1} : Finset (Fin 3)) b12 := by
      intro h
      have := h (by decide : (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)))
      simp only [freeItems, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_singleton,
        exists_eq_left] at this
      exact this.2 (by decide)
    have hstep1 : oneCaStep3 past1 st1 ({0, 2}, {1}, ∅, b02) 1 = ({0, 2}, {1}, {1}, b12) := by
      have hv1 : IsValidShrink (∅ : Finset (Fin 3)) b02 (st1.bundle 1) {0, 1} := by
        simp only [IsValidShrink, freeItems, sqrt_fin4, st1, b02]; decide
      have hv1' : IsValidShrink (∅ : Finset (Fin 3)) b02 (b02 1) {0, 1} := hv1
      have hu : Function.update b02 1 {0, 1} = b12 := by funext i; fin_cases i <;> rfl
      have hfg : ({0, 1} : Finset (Fin 4)) ⊆ freeItems (∅ : Finset (Fin 3)) b12 := by
        simp only [freeItems]; decide
      dsimp only [oneCaStep3, oneCaGoodStrat]
      simp only [show (1 : Fin 3) ∉ st1.winners by decide, hv1, hv1', ↓reduceIte, hu, sqrt_fin4,
        show ({0, 1} : Finset (Fin 4)).card ≤ 2 by decide, hnotfW01, hnotfM01, hfg]
      rfl
    have hstep0 : oneCaStep3 past1 st1 ({0, 2}, {1}, {1}, b12) 0 = ({0, 2}, {1}, {1}, b12) := by
      have hu : Function.update b12 0 {0, 1} = b12 := Function.update_eq_self 0 b12
      dsimp only [oneCaStep3]
      simp only [show (0 : Fin 3) ∈ st1.winners by decide, ↓reduceIte, sqrt_fin4,
        show (b12 0 : Finset (Fin 4)) = {0, 1} from rfl, hu,
        show ({0, 1} : Finset (Fin 4)).card ≤ 2 by decide, hnotfW01, hnotfM01]
    have hstep2 : oneCaStep3 past1 st1 ({0, 2}, {1}, {1}, b12) 2 =
        ({0, 2}, {1, 2}, {1, 2}, b12) := by
      have hu : Function.update b12 2 {2, 3} = b12 := Function.update_eq_self 2 b12
      have hnotfW2 : ¬ ({2, 3} : Finset (Fin 4)) ⊆ freeItems ({0, 2} : Finset (Fin 3)) b12 := by
        intro h
        have := h (by decide : (2 : Fin 4) ∈ ({2, 3} : Finset (Fin 4)))
        simp only [freeItems, Finset.mem_sdiff, Finset.mem_biUnion] at this
        exact this.2 ⟨2, by decide, by decide⟩
      have hfMG2 : ({2, 3} : Finset (Fin 4)) ⊆ freeItems ({1} : Finset (Fin 3)) b12 := by
        intro x hx
        simp only [freeItems, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion,
          Finset.mem_singleton, exists_eq_left]
        fin_cases x <;> simp_all [b12]
      dsimp only [oneCaStep3]
      simp only [show (2 : Fin 3) ∈ st1.winners by decide, ↓reduceIte, sqrt_fin4,
        show (b12 2 : Finset (Fin 4)) = {2, 3} from rfl, hu,
        show ({2, 3} : Finset (Fin 4)).card ≤ 2 by decide, hnotfW2, hfMG2]
      have hins : insert (2 : Fin 3) ({1} : Finset (Fin 3)) = {1, 2} := by decide
      rw [hins]
    have hfold1 : ([1, 0, 2] : List (Fin 3)).foldl (oneCaStep3 past1 st1)
        (st1.winners, {1}, ∅, st1.bundle) = ({0, 2}, {1, 2}, {1, 2}, b12) := by
      rw [List.foldl_cons, hstep1, List.foldl_cons, hstep0, List.foldl_cons, hstep2,
        List.foldl_nil]
    have hproc1 : oneCaProc.proc oneCaGoodStrat past1 st1 = ({1, 2}, b12) := by
      rw [oneCaProc_proc_of_fold3 past1 st1 1 0 2 (by decide)
        (fun x => by fin_cases x <;> decide) (by decide) hfold1]
      have hsumW : ∑ k ∈ ({0, 2} : Finset (Fin 3)), st1.val k = 2 := by decide
      have hsumM : ∑ k ∈ ({1, 2} : Finset (Fin 3)), st1.val k = 3 := by decide
      simp only [hsumW, hsumM, show ¬ (3 : ℕ) ≤ 2 by decide, false_and, le_refl, ↓reduceIte]
    simp only [hproc1, st2, WrapperState.mk.injEq]
    refine ⟨?_, trivial, trivial, ?_⟩
    · funext i; fin_cases i <;> decide
    · ext i; fin_cases i <;> decide
  have h2T : ¬ TerminatedAt oneCaProc oneCaGoodStrat 2 := by
    rw [TerminatedAt, hst2]; decide
  -- Round 2 → 3: active order is `[0, 1, 2]`, `sum W = sum M = sum G = 3`, `W = {1, 2}` wins tie,
  -- bidder `0` retires (`2 * 2 = 4 ≥ 4`).
  have hst3 : wrapperState oneCaProc oneCaGoodStrat 3 = ⟨![0, 2, 1], b12, {1, 2}, {0}⟩ := by
    have hstep : wrapperState oneCaProc oneCaGoodStrat 3 =
        wrapperNext oneCaProc oneCaGoodStrat (wrapperRunHist oneCaProc oneCaGoodStrat 2).2
          (wrapperState oneCaProc oneCaGoodStrat 2) := rfl
    rw [hstep, hst2, wrapperNext]
    set past2 := (wrapperRunHist oneCaProc oneCaGoodStrat 2).2
    have hnt : st2.winners ∪ st2.losers ≠ Finset.univ := by decide
    simp only [hnt, ↓reduceIte]
    have hnotfW01 : ¬ ({0, 1} : Finset (Fin 4)) ⊆ freeItems ({1, 2} : Finset (Fin 3)) b12 := by
      intro h
      have := h (by decide : (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)))
      simp only [freeItems, Finset.mem_sdiff, Finset.mem_biUnion] at this
      exact this.2 ⟨1, by decide, by decide⟩
    have hnotfM01 : ¬ ({0, 1} : Finset (Fin 4)) ⊆ freeItems ({0} : Finset (Fin 3)) b12 := by
      intro h
      have := h (by decide : (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)))
      simp only [freeItems, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_singleton,
        exists_eq_left] at this
      exact this.2 (by decide)
    have hstep0 : oneCaStep3 past2 st2 ({1, 2}, {0}, ∅, b12) 0 = ({1, 2}, {0}, {0}, b12) := by
      have hv0 : IsValidShrink (∅ : Finset (Fin 3)) b12 (st2.bundle 0) {0, 1} := by
        simp only [IsValidShrink, freeItems, sqrt_fin4, st2, b12]; decide
      have hv0' : IsValidShrink (∅ : Finset (Fin 3)) b12 (b12 0) {0, 1} := hv0
      have hu : Function.update b12 0 {0, 1} = b12 := Function.update_eq_self 0 b12
      have hfg : ({0, 1} : Finset (Fin 4)) ⊆ freeItems (∅ : Finset (Fin 3)) b12 := by
        simp only [freeItems]; decide
      dsimp only [oneCaStep3, oneCaGoodStrat]
      simp only [show (0 : Fin 3) ∉ st2.winners by decide, hv0, hv0', ↓reduceIte, hu, sqrt_fin4,
        show ({0, 1} : Finset (Fin 4)).card ≤ 2 by decide, hnotfW01, hnotfM01, hfg]
      rfl
    have hstep1 : oneCaStep3 past2 st2 ({1, 2}, {0}, {0}, b12) 1 = ({1, 2}, {0}, {0}, b12) := by
      have hu : Function.update b12 1 {0, 1} = b12 := Function.update_eq_self 1 b12
      dsimp only [oneCaStep3]
      simp only [show (1 : Fin 3) ∈ st2.winners by decide, ↓reduceIte, sqrt_fin4,
        show (b12 1 : Finset (Fin 4)) = {0, 1} from rfl, hu,
        show ({0, 1} : Finset (Fin 4)).card ≤ 2 by decide, hnotfW01, hnotfM01]
    have hstep2 : oneCaStep3 past2 st2 ({1, 2}, {0}, {0}, b12) 2 =
        ({1, 2}, {0, 2}, {0, 2}, b12) := by
      have hu : Function.update b12 2 {2, 3} = b12 := Function.update_eq_self 2 b12
      have hnotfW2 : ¬ ({2, 3} : Finset (Fin 4)) ⊆ freeItems ({1, 2} : Finset (Fin 3)) b12 := by
        intro h
        have := h (by decide : (2 : Fin 4) ∈ ({2, 3} : Finset (Fin 4)))
        simp only [freeItems, Finset.mem_sdiff, Finset.mem_biUnion] at this
        exact this.2 ⟨2, by decide, by decide⟩
      have hfMG2 : ({2, 3} : Finset (Fin 4)) ⊆ freeItems ({0} : Finset (Fin 3)) b12 := by
        intro x hx
        simp only [freeItems, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion,
          Finset.mem_singleton, exists_eq_left]
        fin_cases x <;> simp_all [b12]
      dsimp only [oneCaStep3]
      simp only [show (2 : Fin 3) ∈ st2.winners by decide, ↓reduceIte, sqrt_fin4,
        show (b12 2 : Finset (Fin 4)) = {2, 3} from rfl, hu,
        show ({2, 3} : Finset (Fin 4)).card ≤ 2 by decide, hnotfW2, hfMG2]
      have hins : insert (2 : Fin 3) ({0} : Finset (Fin 3)) = {0, 2} := by decide
      rw [hins]
    have hfold2 : ([0, 1, 2] : List (Fin 3)).foldl (oneCaStep3 past2 st2)
        (st2.winners, {0}, ∅, st2.bundle) = ({1, 2}, {0, 2}, {0, 2}, b12) := by
      rw [List.foldl_cons, hstep0, List.foldl_cons, hstep1, List.foldl_cons, hstep2,
        List.foldl_nil]
    have hproc2 : oneCaProc.proc oneCaGoodStrat past2 st2 = ({1, 2}, b12) := by
      rw [oneCaProc_proc_of_fold3 past2 st2 0 1 2 (by decide)
        (fun x => by fin_cases x <;> decide) (by decide) hfold2]
      have hsumW : ∑ k ∈ ({1, 2} : Finset (Fin 3)), st2.val k = 3 := by decide
      have hsumM : ∑ k ∈ ({0, 2} : Finset (Fin 3)), st2.val k = 3 := by decide
      simp only [hsumW, hsumM, le_refl, and_self, ↓reduceIte]
    simp only [hproc2, WrapperState.mk.injEq]
    refine ⟨?_, trivial, trivial, ?_⟩
    · funext i; fin_cases i <;> decide
    · ext i; fin_cases i <;> decide
  have h3T : TerminatedAt oneCaProc oneCaGoodStrat 3 := by
    rw [TerminatedAt, hst3]; decide
  have hJ : termRound oneCaProc oneCaGoodStrat = 3 := by
    have hle : termRound oneCaProc oneCaGoodStrat ≤ 3 := termRound_le_of_terminatedAt h3T
    have hsp : TerminatedAt oneCaProc oneCaGoodStrat (termRound oneCaProc oneCaGoodStrat) :=
      termRound_spec ⟨3, h3T⟩
    interval_cases h : termRound oneCaProc oneCaGoodStrat
    · exact absurd (h ▸ hsp) h0T
    · exact absurd (h ▸ hsp) h1T
    · exact absurd (h ▸ hsp) h2T
    · rfl
  exact ⟨by rw [hst1], by rw [hst1]; rfl, by rw [hst1]; rfl, by rw [hst1]; rfl,
    by rw [hst2], by rw [hst2]; rfl, by rw [hst2]; rfl,
    h2T, h3T, hJ, by rw [hst3], by rw [hst3]⟩

/-- An out-of-`D` strategy for bidder `0` that shrinks to the undesired singleton `{0}` and always
doubles. -/
private def badOneCaStrat : OneCaStrategy (Fin 3) (Fin 4) where
  shrink := fun _ => some {0}
  double := fun _ _ _ _ => true

example : badOneCaStrat ∉ oneCaStrategyClass (oneCaPlayers 0) 0 := by
  intro hmem
  let st : WrapperState (Fin 3) (Fin 4) := initState (fun _ => Finset.univ)
  let view : OneCaShrinkView (Fin 3) (Fin 4) := ⟨[], st, ∅, {0}, ∅, st.bundle⟩
  have hsqrt4 : Nat.sqrt (Fintype.card (Fin 4)) = 2 := by
    rw [Fintype.card_fin]
    exact (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  have hval : IsValidShrink view.currentGreedy view.currentBundles (view.state.bundle 0) {0} :=
    ⟨by decide, by decide, by rw [hsqrt4]; decide⟩
  have hdes : ({0} : Finset (Fin 4)) ∈ (oneCaPlayers 0).desired := hmem.1 view {0} rfl hval
  rcases hdes with h | h
  · exact absurd (h (by decide : (1 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)))) (by decide)
  · exact absurd (h (by decide : (2 : Fin 4) ∈ ({2, 3} : Finset (Fin 4)))) (by decide)

/-- Explicit weak dominance of `dominateOneCaStrategy` over `badOneCaStrat`, and **Theorem 12.51**
instantiated on `oneCaPlayers` (`v_max = 4`, `m = 4`, `√4 = 2`, factor
`1 + 2 * 5 * 6 * (3 + 2 * 2) = 421`). -/
example :
    dominateOneCaStrategy (oneCaPlayers 0) 0 badOneCaStrat ∈
      oneCaStrategyClass (oneCaPlayers 0) 0 ∧
    (oneCaProc (N := Fin 3) (M := Fin 4)).WeaklyDominates (oneCaPlayers 0) 0
      (dominateOneCaStrategy (oneCaPlayers 0) 0 badOneCaStrat) badOneCaStrat ∧
    (oneCaProc (N := Fin 3) (M := Fin 4)).IsUndominatedImpl oneCaPlayers
      (fun i => oneCaStrategyClass (oneCaPlayers i) i) 421 := by
  refine ⟨dominateOneCaStrategy_mem (oneCaPlayers 0) 0 badOneCaStrat,
    dominateOneCaStrategy_weaklyDominates (oneCaPlayers 0) 0 badOneCaStrat, ?_⟩
  have h := oneCaProc_isUndominatedImpl oneCaPlayers oneCaPlayers_le_four
  have hlog : Nat.log 2 ⌊(4 : ℝ)⌋₊ = 2 := by
    have hf : ⌊(4 : ℝ)⌋₊ = 4 := by norm_num
    rw [hf]; decide
  have hsqrt : Real.sqrt (Fintype.card (Fin 4) : ℝ) = 2 := by
    rw [Fintype.card_fin]
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simpa only [hlog, hsqrt, Nat.cast_ofNat,
    show (1 : ℝ) + 2 * (2 * 2 + 1) * (2 * 2 + 2) * (3 + 2 * 2) = 421 by norm_num] using h

/-! ### 4. Tight `v_max = 1` boundary test -/

private def unitPlayers : Fin 2 → SingleValuePlayer (Fin 2)
  | 0 => SingleValuePlayer.singleMinded {0, 1} (by decide) 1 le_rfl
  | 1 => SingleValuePlayer.singleMinded {0, 1} (by decide) 1 le_rfl

private def unitStrat : Fin 2 → OneCaStrategy (Fin 2) (Fin 2) := fun i =>
  { shrink := fun _ => none
    double := fun _ st _ _ => decide (2 * st.val i < 1) }

private theorem unitStrat_mem (i : Fin 2) : unitStrat i ∈ oneCaStrategyClass (unitPlayers i) i := by
  refine ⟨fun _ _ hsh _ => by simp only [unitStrat, reduceCtorEq] at hsh, ?_, ?_⟩
  · intro _ _ ⟨b, hvb, hdes⟩
    have hdes' : ({0, 1} : Finset (Fin 2)) ⊆ b := by fin_cases i <;> exact hdes
    have hcard : ({0, 1} : Finset (Fin 2)).card ≤ b.card := Finset.card_le_card hdes'
    have hle : b.card ≤ Nat.sqrt (Fintype.card (Fin 2)) := hvb.2.2
    have h1 : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
    have h2 : Nat.sqrt (Fintype.card (Fin 2)) = 1 := by
      rw [Fintype.card_fin]
      exact (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
    omega
  · intro _ st _ _
    have hval : (unitPlayers i).value = 1 := by fin_cases i <;> rfl
    simp only [unitStrat, hval]
    constructor
    · intro hgt
      rw [decide_eq_false_iff_not]
      intro hlt
      have : ((2 * st.val i : ℕ) : ℝ) < (1 : ℕ) := by exact_mod_cast hlt
      push_cast at this; linarith
    · intro hlt
      rw [decide_eq_true_iff]
      have : ((2 * st.val i : ℕ) : ℝ) < (1 : ℕ) := by push_cast; linarith
      exact_mod_cast this

/-- At `v_max = 1` (`Nat.log 2 ⌊1⌋₊ = 0`), Lemma 12.38 gives the sharp bound `termRound ≤ 1`:
our 2-bidder `unitPlayers` instance does not terminate at `j = 0` and terminates at `j = 1`,
with bidder `0` winning `{0, 1}` and bidder `1` retiring immediately. Moreover, Theorem 12.51
yields the explicit non-vacuous factor `13 + 8 * √2` (whereas the textbook's `5 * log₂(v_max)`
vanishes at `v_max = 1`). -/
example :
    2 * Nat.log 2 ⌊(1 : ℝ)⌋₊ + 1 = 1 ∧
    ¬ TerminatedAt oneCaProc unitStrat 0 ∧
    TerminatedAt oneCaProc unitStrat 1 ∧
    termRound oneCaProc unitStrat = 1 ∧
    (wrapperState oneCaProc unitStrat 1).winners = {0} ∧
    (wrapperState oneCaProc unitStrat 1).losers = {1} ∧
    (oneCaProc (N := Fin 2) (M := Fin 2)).IsUndominatedImpl unitPlayers
      (fun i => oneCaStrategyClass (unitPlayers i) i) (13 + 8 * Real.sqrt 2) := by
  have hlog : Nat.log 2 ⌊(1 : ℝ)⌋₊ = 0 := by
    have hf : ⌊(1 : ℝ)⌋₊ = 1 := by norm_num
    rw [hf]; decide
  have hsqrt2 : Nat.sqrt (Fintype.card (Fin 2)) = 1 := by
    rw [Fintype.card_fin]
    exact (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  have hst0 : wrapperState oneCaProc unitStrat 0 =
      ⟨fun _ => 1, fun _ => Finset.univ, ∅, ∅⟩ := rfl
  have h0 : ¬ TerminatedAt oneCaProc unitStrat 0 := by
    rw [TerminatedAt, hst0]; decide
  have hst1 : wrapperState oneCaProc unitStrat 1 =
      ⟨![1, 0], fun _ => Finset.univ, {0}, {1}⟩ := by
    have hstep : wrapperState oneCaProc unitStrat 1 =
        wrapperNext oneCaProc unitStrat [] (wrapperState oneCaProc unitStrat 0) := rfl
    rw [hstep, hst0, wrapperNext]
    have hnt : (∅ : Finset (Fin 2)) ∪ ∅ ≠ Finset.univ := by decide
    simp only [hnt, ↓reduceIte]
    have hproc : oneCaProc.proc unitStrat [] ⟨fun _ => 1, fun _ => Finset.univ, ∅, ∅⟩ =
        ({0}, fun _ => Finset.univ) := by
      dsimp only [oneCaProc]
      rw [finset_sort_eq ([0, 1] : List (Fin 2))]
      swap; · decide
      swap; · intro x; fin_cases x <;> decide
      swap; · decide
      simp only [List.foldl_cons, List.foldl_nil, unitStrat, Finset.notMem_empty, ↓reduceIte,
        hsqrt2, Function.update_eq_self, show ¬ (Finset.univ : Finset (Fin 2)).card ≤ 1 by decide,
        Finset.sum_empty, Finset.sum_singleton, show ¬ (1 : ℕ) ≤ 0 by decide, false_and,
        Nat.zero_le]
    simp only [hproc, WrapperState.mk.injEq]
    refine ⟨?_, trivial, trivial, ?_⟩
    · funext i; fin_cases i <;> decide
    · ext i; fin_cases i <;> decide
  have h1 : TerminatedAt oneCaProc unitStrat 1 := by
    rw [TerminatedAt, hst1]; decide
  have hJ : termRound oneCaProc unitStrat = 1 := by
    have hle : termRound oneCaProc unitStrat ≤ 1 := termRound_le_of_terminatedAt h1
    have hsp : TerminatedAt oneCaProc unitStrat (termRound oneCaProc unitStrat) :=
      termRound_spec ⟨1, h1⟩
    interval_cases h : termRound oneCaProc unitStrat
    · exact absurd (h ▸ hsp) h0
    · rfl
  have himpl : (oneCaProc (N := Fin 2) (M := Fin 2)).IsUndominatedImpl unitPlayers
      (fun i => oneCaStrategyClass (unitPlayers i) i) (13 + 8 * Real.sqrt 2) := by
    have h := oneCaProc_isUndominatedImpl unitPlayers (v_max := 1) fun i => by
      fin_cases i <;> rfl
    have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by rw [Fintype.card_fin]; norm_num
    rw [hlog, hcard] at h
    convert h using 1
    ring
  exact ⟨by rw [hlog], h0, h1, hJ, by rw [hst1], by rw [hst1], himpl⟩

/-- **Theorem 12.45** at `v_max = 1` gives the non-vacuous factor `1 + 2 * 1 * 1 = 3` (using the
exact max-bidder algorithm over two overlapping unit-value bidders). -/
example :
    let bundle : Fin 2 → Finset (Fin 2) := fun _ => {0, 1}
    let v : Fin 2 → ℝ := fun _ => 1
    let alg : (Fin 2 → ℝ) → Finset (Fin 2) := fun w => by
      classical exact if w 1 ≤ w 0 then {0} else {1}
    let players := fun i => SingleValuePlayer.singleMinded (bundle i) (by decide) (v i) le_rfl
    (ksmProc bundle alg).IsDominantStrategyImpl players
      (fun i => ksmDominantStrategy i (v i)) 3 := by
  intro bundle v alg players
  have hlog : Nat.log 2 ⌊(1 : ℝ)⌋₊ = 0 := by
    have hf : ⌊(1 : ℝ)⌋₊ = 1 := by norm_num
    rw [hf]; decide
  have h := ksmProc_isDominantStrategyImpl bundle (fun _ => by decide) v (fun _ => le_rfl)
    (v_max := 1) (fun _ => le_rfl) (alg := alg) (c := 1) (by norm_num)
    (fun w _ => by
      classical
      simp only [alg]
      split_ifs <;> simp only [Finset.coe_singleton, Set.pairwiseDisjoint_singleton])
    (fun w hw W hpw => by
      classical
      rw [one_mul]
      have hcard : W.card ≤ 1 := by
        by_contra hgt
        obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.1 (Nat.lt_of_not_ge hgt)
        have hd : Disjoint (bundle a) (bundle b) := hpw ha hb hne
        exact Finset.disjoint_left.1 hd (by decide : (0 : Fin 2) ∈ bundle a) (by decide)
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hcard with h0 | h1
      · rw [Finset.card_eq_zero.1 h0, Finset.sum_empty]
        exact Finset.sum_nonneg fun i _ => hw i
      · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 h1
        rw [Finset.sum_singleton]
        simp only [alg]
        split_ifs with h01
        · rw [Finset.sum_singleton]
          match i with
          | 0 => exact le_rfl
          | 1 => exact h01
        · rw [Finset.sum_singleton]
          match i with
          | 0 => linarith
          | 1 => exact le_rfl)
  simpa only [hlog, Nat.cast_zero, mul_zero, zero_add, mul_one,
    show (1 : ℝ) + 2 = 3 by norm_num] using h

end CslibFrontierTests.GameTheory.WrapperMechanisms
