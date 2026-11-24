/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.GameTheory.Extensive.PerfectInfoEmbedding
public import CslibFrontier.GameTheory.Extensive.SequenceFormLP
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Checked tests for `PerfectInfoEmbedding` and `SequenceFormLP`

Non-vacuous checked examples exercising [vonStengel2007], Chapter 3:

* Perfect-information embedding (`entryChanceTree`): embeds a finite two-player perfect-information
  game with both decision and chance nodes into `ExtensiveTree`, checks `IsSingletonInfoSet`
  (`toExtensiveTree_isSingletonInfoSet`), `PerfectRecall`, `NoRepeatedInfoSet`,
  `PureStrategy.toExtensiveEquiv`, `leafPathEquivTerminal`, payoff agreement
  (`toExtensiveTree_evalPure`), backward-induction Nash equilibrium
  (`toExtensiveTree_backwardInduction_isPureNash`), pure/mixed Nash equivalences
  (`toExtensiveTree_isPureNash_iff`, `toExtensiveTree_isMixedNash_iff`), and Kuhn's theorem on the
  embedded tree (`toExtensiveTree_kuhn_theorem`).
* Two-player zero-sum sequential imperfect-information game (`zeroSeqGame`): player `false`
  chooses `Stay` (`0`) or `Play`, followed by simultaneous asymmetric matching pennies with
  minimax value `1 / 3`. Exercises `ExtensiveTree.IsZeroSum`, `isBehaviorNash_iff_isSeqNash`,
  `isMixedNash_toCostGame_iff_isSeqNash`, `isSeqNash_iff_complementarity`,
  `isSeqBestResponseFalse_iff_dual` (both optimal acceptance and non-vacuous deviation rejection),
  `IsZeroSum.seq_weak_duality`, `IsZeroSum.exists_seq_lp_minimax`,
  `IsZeroSum.exists_behavior_minimax`, `exists_isSeqNash`, and `exists_isBehaviorNash`.
-/

public section

namespace CslibFrontierTests.GameTheory.ExtensiveSequenceLP

open Cslib.GameTheory Cslib.GameTheory.Extensive Finset Matrix

/-! ### 1. Embedding a finite perfect-information game with chance nodes -/

/-- Fair coin distribution on `Bool`. -/
theorem fairCoin_isMixed : IsMixedStrategy (fun _ : Bool => (1 / 2 : ℝ)) :=
  isMixedStrategy_iff.2 ⟨fun _ => by norm_num, by norm_num⟩

/-- Subgame after chance chooses `true` in `entryChanceTree`: player `1` chooses `Accommodate`
(`false`, payoff `(2, 1)`) or `Fight` (`true`, payoff `(0, 0)`). -/
@[expose, reducible] noncomputable def entryChanceSub : PerfectInfoTree (Fin 2) :=
  .decision (1 : Fin 2) fun
    | false => .leaf ![2, 1]
    | true => .leaf ![0, 0]

/-- Two-player perfect-information game with both decision and chance moves:
* player `0` plays `Out` (`false`, payoff `(2, 2)`) or `Enter` (`true`);
* upon `Enter`, chance flips a fair coin: `false` gives `(3, 1)`, while `true` leads to player
  `1` choosing `Accommodate` (`false`, payoff `(2, 1)`) or `Fight` (`true`, payoff `(0, 0)`). -/
@[expose, reducible] noncomputable def entryChanceTree : PerfectInfoTree (Fin 2) :=
  .decision 0 fun
    | false => .leaf ![2, 2]
    | true =>
      .chance (fun _ : Bool => (1 / 2 : ℝ)) fairCoin_isMixed fun
        | false => .leaf ![3, 1]
        | true => entryChanceSub

/-- Subgame-perfect strategy profile for `entryChanceTree`: player `0` plays `Enter` (`true`) and
player `1` plays `Accommodate` (`false`), giving expected payoff `(5 / 2, 1)`. -/
@[expose, reducible] noncomputable def entryChanceSPE :
    ∀ i : Fin 2, PerfectInfoTree.PureStrategy i entryChanceTree :=
  fun _ => .decision (fun _ => true) fun
    | false => .leaf
    | true => .chance fun
        | false => .leaf
        | true => .decision (fun _ => false) fun
            | false => .leaf
            | true => .leaf

/-- Non-SPE pure Nash equilibrium `(Out, Fight)`: deviating to `Enter` yields `3 / 2 ≤ 2`. -/
@[expose, reducible] noncomputable def entryChanceThreat :
    ∀ i : Fin 2, PerfectInfoTree.PureStrategy i entryChanceTree :=
  fun _ => .decision (fun _ => false) fun
    | false => .leaf
    | true => .chance fun
        | false => .leaf
        | true => .decision (fun _ => true) fun
            | false => .leaf
            | true => .leaf

private theorem eval_entryChanceSPE :
    entryChanceTree.expectedPayoff entryChanceSPE = ![5 / 2, 1] := by
  rw [PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq (a := true)
    (by simp [entryChanceSPE])]
  ext i
  simp only [PerfectInfoTree.expectedPayoff_chance, Fintype.sum_bool,
    PerfectInfoTree.expectedPayoff_leaf]
  rw [PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq (a := false)
    (by simp [entryChanceSPE])]
  fin_cases i <;> simp <;> norm_num

theorem entryChanceSPE_isPureSPE : entryChanceTree.IsPureSPE entryChanceSPE := by
  rw [PerfectInfoTree.isPureSPE_iff_oneShot]
  refine ⟨fun a => ?_, fun b => ?_⟩
  · have h0 : (entryChanceSPE 0).headChoice = true := by simp [entryChanceSPE]
    rw [h0]
    simp only [PerfectInfoTree.expectedPayoff_chance, Fintype.sum_bool,
      PerfectInfoTree.expectedPayoff_leaf]
    rw [PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq (a := false)
      (by simp [entryChanceSPE])]
    cases a
    · simp
      norm_num
    · rw [PerfectInfoTree.expectedPayoff_chance, Fintype.sum_bool,
        PerfectInfoTree.expectedPayoff_leaf,
        PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq (a := false)
          (by simp [entryChanceSPE])]
  · cases b
    · trivial
    · intro c
      cases c
      · trivial
      · refine ⟨fun f => ?_, fun f => ?_⟩
        · dsimp only
          have h1 : (((entryChanceSPE 1).childDecision true).childChance true).headChoice =
              false := by simp [entryChanceSPE]
          rw [h1]
          cases f <;> simp
        · cases f <;> trivial

private theorem entryChanceSub_hasNoContinuationTies : entryChanceSub.HasNoContinuationTies := by
  have hdet : entryChanceSub.IsDeterministic := fun b => by cases b <;> trivial
  have hdist : entryChanceSub.HasDistinctLeafPayoffs := by
    intro z₁ z₂ hne i
    dsimp only [entryChanceSub] at z₁ z₂
    rcases z₁ with _ | ⟨b₁, sub₁⟩ | ⟨⟩
    rcases z₂ with _ | ⟨b₂, sub₂⟩ | ⟨⟩
    cases b₁ <;> cases b₂ <;> cases sub₁ <;> cases sub₂
    · exact absurd rfl hne
    · fin_cases i <;> simp
    · fin_cases i <;> simp
    · exact absurd rfl hne
  exact hdet.hasNoContinuationTies hdist

private theorem entryChanceSub_backwardInduction_payoff :
    entryChanceSub.backwardInduction.payoff = ![2, 1] := by
  let strat : ∀ i : Fin 2, PerfectInfoTree.PureStrategy i entryChanceSub :=
    fun _ => .decision (fun _ => false) fun
      | false => .leaf
      | true => .leaf
  have hspe : entryChanceSub.IsPureSPE strat := by
    rw [PerfectInfoTree.isPureSPE_iff_oneShot]
    refine ⟨fun a => ?_, fun b => ?_⟩
    · have hs1 : (strat 1).headChoice = false := by simp [strat]
      rw [hs1]
      cases a <;> simp
    · cases b <;> trivial
  have hbi : strat = entryChanceSub.backwardInduction.strategy :=
    PerfectInfoTree.eq_backwardInduction_of_isPureSPE entryChanceSub_hasNoContinuationTies hspe
  rw [PerfectInfoTree.backwardInduction_payoff, ← hbi,
    PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq (a := false) (by simp [strat])]
  ext i
  fin_cases i <;> simp

theorem entryChanceTree_hasNoContinuationTies : entryChanceTree.HasNoContinuationTies := by
  refine ⟨fun a₁ a₂ hne => ?_, fun b => ?_⟩
  · cases a₁ <;> cases a₂
    · exact absurd rfl hne
    · simp only [PerfectInfoTree.backwardInduction_leaf_payoff,
        PerfectInfoTree.backwardInduction_chance_payoff, Fintype.sum_bool,
        entryChanceSub_backwardInduction_payoff]
      norm_num
    · simp only [PerfectInfoTree.backwardInduction_leaf_payoff,
        PerfectInfoTree.backwardInduction_chance_payoff, Fintype.sum_bool,
        entryChanceSub_backwardInduction_payoff]
      norm_num
    · exact absurd rfl hne
  · cases b
    · trivial
    · intro c
      cases c
      · trivial
      · exact entryChanceSub_hasNoContinuationTies

theorem entryChanceTree_backwardInduction_eq :
    entryChanceTree.backwardInduction.strategy = entryChanceSPE := by
  obtain ⟨_, _, hu⟩ := PerfectInfoTree.existsUnique_isPureSPE_of_hasNoContinuationTies
    entryChanceTree_hasNoContinuationTies
  rw [hu _ (PerfectInfoTree.isPureSPE_backwardInduction entryChanceTree),
    hu _ entryChanceSPE_isPureSPE]

/-- Structural, Nash, backward-induction, and path-payoff properties of the embedded extensive
game `entryChanceTree.toExtensiveTree`. -/
theorem entryChance_embedding_properties :
    (∀ {i : Fin 2} {h : entryChanceTree.InfoSet i} {v₁ v₂ : Node entryChanceTree.toExtensiveTree},
        v₁.IsDecisionOf i h → v₂.IsDecisionOf i h → v₁ = v₂) ∧
      entryChanceTree.toExtensiveTree.PerfectRecall 0 ∧
      entryChanceTree.toExtensiveTree.PerfectRecall 1 ∧
      entryChanceTree.toExtensiveTree.NoRepeatedInfoSet 0 ∧
      entryChanceTree.toExtensiveTree.evalPure (fun i => (entryChanceSPE i).toExtensive) =
        ![5 / 2, 1] ∧
      entryChanceTree.toExtensiveTree.toCostGame.IsPureNash
        (fun i => (entryChanceSPE i).toExtensive) ∧
      entryChanceTree.toExtensiveTree.toCostGame.IsPureNash
        (fun i => (entryChanceThreat i).toExtensive) ∧
      (∀ z : PerfectInfoTree.LeafPath entryChanceTree,
        (PerfectInfoTree.leafPathEquivTerminal entryChanceTree z).payoff = z.payoff) := by
  have heval : entryChanceTree.toExtensiveTree.evalPure (fun i => (entryChanceSPE i).toExtensive) =
      ![5 / 2, 1] := by
    rw [PerfectInfoTree.toExtensiveTree_evalPure, eval_entryChanceSPE]
  have hbi_nash :
      entryChanceTree.toExtensiveTree.toCostGame.IsPureNash
        (fun i => (entryChanceSPE i).toExtensive) := by
    have h := PerfectInfoTree.toExtensiveTree_backwardInduction_isPureNash entryChanceTree
    rwa [entryChanceTree_backwardInduction_eq] at h
  have hthreat_pi : entryChanceTree.toCostGame.IsPureNash entryChanceThreat := by
    intro i s'
    match i with
    | ⟨0, _⟩ =>
      simp only [PerfectInfoTree.toCostGame_cost, neg_le_neg_iff]
      change entryChanceTree.expectedPayoff (Function.update entryChanceThreat 0 s') 0 ≤
        entryChanceTree.expectedPayoff entryChanceThreat 0
      rw [PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq
        (s := Function.update entryChanceThreat 0 s') (a := s'.headChoice) (by simp),
        PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq
          (s := entryChanceThreat) (a := false) (by simp [entryChanceThreat])]
      cases s'.headChoice
      · simp
      · rw [PerfectInfoTree.expectedPayoff_chance, Fintype.sum_bool,
          PerfectInfoTree.expectedPayoff_leaf, PerfectInfoTree.expectedPayoff_leaf,
          PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq (a := true)
            (by simp [Function.update, entryChanceThreat])]
        simp
        norm_num
    | ⟨1, hi⟩ =>
      simp only [PerfectInfoTree.toCostGame_cost, neg_le_neg_iff]
      change entryChanceTree.expectedPayoff (Function.update entryChanceThreat ⟨1, hi⟩ s') 1 ≤
        entryChanceTree.expectedPayoff entryChanceThreat 1
      rw [PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq
        (s := Function.update entryChanceThreat ⟨1, hi⟩ s') (a := false)
        (by simp [entryChanceThreat]),
        PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq
          (s := entryChanceThreat) (a := false) (by simp [entryChanceThreat])]
      simp
  have hthreat_ext :
      entryChanceTree.toExtensiveTree.toCostGame.IsPureNash
        (fun i => (entryChanceThreat i).toExtensive) :=
    (PerfectInfoTree.toExtensiveTree_isPureNash_iff entryChanceTree entryChanceThreat).2 hthreat_pi
  exact ⟨fun hv₁ hv₂ => PerfectInfoTree.toExtensiveTree_isSingletonInfoSet entryChanceTree hv₁ hv₂,
    PerfectInfoTree.toExtensiveTree_perfectRecall entryChanceTree 0,
    PerfectInfoTree.toExtensiveTree_perfectRecall entryChanceTree 1,
    PerfectInfoTree.toExtensiveTree_noRepeatedInfoSet entryChanceTree 0,
    heval, hbi_nash, hthreat_ext, fun z => PerfectInfoTree.leafPathEquivTerminal_payoff z⟩

open Classical in
/-- Kuhn's theorem applied directly to a mixed strategy on the embedded tree
`entryChanceTree.toExtensiveTree`, together with `toExtensiveTree_isMixedNash_iff`. -/
theorem entryChance_embedded_kuhn_and_mixed :
    let T := entryChanceTree.toExtensiveTree
    let sOut := (entryChanceThreat (0 : Fin 2)).toExtensive
    let sEnter := (entryChanceSPE (0 : Fin 2)).toExtensive
    let μ₀ : PureStrategy (fun j => entryChanceTree.InfoSet j) (fun _ h => h.Act) 0 → ℝ :=
      fun s => if s = sOut then 1 / 2 else if s = sEnter then 1 / 2 else 0
    IsBehaviorStrategy
        (T.realizationPlanToBehavior (0 : Fin 2) (entryChanceTree.toExtensiveTree_perfectRecall 0)
          (T.mixedToRealizationPlan (0 : Fin 2) μ₀)) ∧
      T.RealizationEquivMixedBehavior (0 : Fin 2) μ₀
        (T.realizationPlanToBehavior (0 : Fin 2) (entryChanceTree.toExtensiveTree_perfectRecall 0)
          (T.mixedToRealizationPlan (0 : Fin 2) μ₀)) ∧
      T.toCostGame.IsMixedNash
        (fun i sE =>
          Pi.single (M := fun _ => ℝ) (entryChanceSPE i) (1 : ℝ)
            (PerfectInfoTree.PureStrategy.ofExtensive entryChanceTree sE)) := by
  have hsNe : (entryChanceThreat (0 : Fin 2)).toExtensive ≠
      (entryChanceSPE (0 : Fin 2)).toExtensive := by
    intro h
    have h0 := congrFun h PerfectInfoTree.InfoSet.here
    simp [entryChanceThreat, entryChanceSPE] at h0
  let μ₀ :
      PureStrategy (fun j => entryChanceTree.InfoSet j) (fun _ h => h.Act) (0 : Fin 2) → ℝ :=
    fun s =>
      if s = (entryChanceThreat (0 : Fin 2)).toExtensive then 1 / 2
      else if s = (entryChanceSPE (0 : Fin 2)).toExtensive then 1 / 2 else 0
  have hμ₀ : IsMixedStrategy μ₀ := by
    refine isMixedStrategy_iff.2 ⟨fun s => ?_, ?_⟩
    · dsimp only [μ₀]
      split_ifs <;> norm_num
    · have hsum : (∑ s, μ₀ s) =
          μ₀ (entryChanceThreat 0).toExtensive + μ₀ (entryChanceSPE 0).toExtensive := by
        rw [← add_sum_erase univ _ (mem_univ (entryChanceThreat 0).toExtensive)]
        congr 1
        rw [sum_eq_single (entryChanceSPE 0).toExtensive]
        · intro s hs hne
          have hne1 : s ≠ (entryChanceThreat 0).toExtensive := ne_of_mem_erase hs
          simp [μ₀, hne1, hne]
        · intro hmem
          exact absurd (mem_erase.2 ⟨hsNe.symm, mem_univ _⟩) hmem
      rw [hsum]
      simp [μ₀, hsNe.symm]
      norm_num
  have hk := PerfectInfoTree.toExtensiveTree_kuhn_theorem entryChanceTree hμ₀
  have hmix_nash_pi :
      entryChanceTree.toCostGame.IsMixedNash
        (fun i => Pi.single (M := fun _ => ℝ) (entryChanceSPE i) (1 : ℝ)) := by
    rw [CostGame.isMixedNash_single_iff]
    exact entryChanceSPE_isPureSPE.isPureNash
  have hmix_nash_ext :=
    (PerfectInfoTree.toExtensiveTree_isMixedNash_iff entryChanceTree
      (fun i => Pi.single (M := fun _ => ℝ) (entryChanceSPE i) (1 : ℝ))).2 hmix_nash_pi
  exact ⟨hk.1, hk.2, hmix_nash_ext⟩

/-! ### 2. Two-player zero-sum sequential game: LP minimax & complementarity -/

/-- Information sets for `zeroSeqGame`: player `false` acts at `false` (Stay/Play) and `true`
(L/R); player `true` acts at `()` without observing player `false`'s L/R move. -/
abbrev zsH : Bool → Type
  | false => Bool
  | true => Unit

instance (i : Bool) : Fintype (zsH i) := by cases i <;> infer_instance
instance (i : Bool) : DecidableEq (zsH i) := by cases i <;> infer_instance

/-- Binary action sets in `zeroSeqGame`. -/
abbrev zsAct : ∀ i : Bool, zsH i → Type := fun _ _ => Bool

instance (i : Bool) (h : zsH i) : Fintype (zsAct i h) := by dsimp [zsAct]; infer_instance
instance (i : Bool) (h : zsH i) : DecidableEq (zsAct i h) := by dsimp [zsAct]; infer_instance
instance (i : Bool) (h : zsH i) : Nonempty (zsAct i h) := by dsimp [zsAct]; exact ⟨false⟩

/-- Asymmetric zero-sum payoff kernel for `zeroSeqGame`: matrix `[[1, -1], [-1, 3]]` for player
`false`, negated for player `true`, with minimax value `1 / 3`. -/
@[expose] def zsLeafPayoff (a₁ a₂ : Bool) : Bool → ℝ
  | false => if !a₁ && !a₂ then 1 else if a₁ && a₂ then 3 else -1
  | true => -(if !a₁ && !a₂ then 1 else if a₁ && a₂ then 3 else -1)

/-- Zero-sum imperfect-information game with an outside option `Stay` (`0`) vs sequential
hidden-move asymmetric matching pennies (`Play`, minimax value `1 / 3`). -/
abbrev zeroSeqGame : ExtensiveTree Bool zsH zsAct :=
  .decision false (false : Bool) fun
    | false => .leaf (fun _ => 0)
    | true =>
      .decision false (true : Bool) fun a₁ =>
        .decision true () fun a₂ =>
          .leaf (zsLeafPayoff a₁ a₂)

theorem zeroSeqGame_isZeroSum : zeroSeqGame.IsZeroSum := by
  intro z
  rcases z with _ | ⟨⟩ | ⟨_ | _, sub⟩
  · cases sub
    simp
  · rcases sub with _ | ⟨⟩ | ⟨a₁, sub'⟩
    rcases sub' with _ | ⟨⟩ | ⟨a₂, sub''⟩
    cases sub''
    simp [zsLeafPayoff]

theorem zeroSeqGame_perfectRecall_false : zeroSeqGame.PerfectRecall false := by
  intro h v₁ v₂ hv₁ hv₂
  cases h
  · rcases v₁ with _ | ⟨⟩ | ⟨_ | _, sub₁⟩
    · rcases v₂ with _ | ⟨⟩ | ⟨_ | _, sub₂⟩
      · rfl
      · cases sub₂; simp at hv₂
      · rcases sub₂ with _ | ⟨⟩ | ⟨c₂, sub₂'⟩
        · simp at hv₂
        · rcases sub₂' with _ | ⟨⟩ | ⟨d₂, sub₂''⟩
          · simp at hv₂
          · cases sub₂''; simp at hv₂
    · cases sub₁; simp at hv₁
    · rcases sub₁ with _ | ⟨⟩ | ⟨c₁, sub₁'⟩
      · simp at hv₁
      · rcases sub₁' with _ | ⟨⟩ | ⟨d₁, sub₁''⟩
        · simp at hv₁
        · cases sub₁''; simp at hv₁
  · rcases v₁ with _ | ⟨⟩ | ⟨_ | _, sub₁⟩
    · simp at hv₁
    · cases sub₁; simp at hv₁
    · rcases v₂ with _ | ⟨⟩ | ⟨_ | _, sub₂⟩
      · simp at hv₂
      · cases sub₂; simp at hv₂
      · rcases sub₁ with _ | ⟨⟩ | ⟨c₁, sub₁'⟩
        · rcases sub₂ with _ | ⟨⟩ | ⟨c₂, sub₂'⟩
          · rfl
          · rcases sub₂' with _ | ⟨⟩ | ⟨d₂, sub₂''⟩
            · simp at hv₂
            · cases sub₂''; simp at hv₂
        · rcases sub₁' with _ | ⟨⟩ | ⟨d₁, sub₁''⟩
          · simp at hv₁
          · cases sub₁''; simp at hv₁

theorem zeroSeqGame_perfectRecall_true : zeroSeqGame.PerfectRecall true := by
  intro h v₁ v₂ hv₁ hv₂
  cases h
  have hseq : ∀ v : Node zeroSeqGame, v.IsDecisionOf true () → v.playerSeq true = [] := by
    intro v hv
    rcases v with _ | ⟨⟩ | ⟨_ | _, sub⟩
    · simp at hv
    · cases sub; simp at hv
    · rcases sub with _ | ⟨⟩ | ⟨c, sub'⟩
      · simp at hv
      · rcases sub' with _ | ⟨⟩ | ⟨d, sub''⟩
        · rfl
        · cases sub''; simp at hv
  rw [hseq v₁ hv₁, hseq v₂ hv₂]

private theorem zeroSeqGame_perfectRecall : ∀ i, zeroSeqGame.PerfectRecall i
  | false => zeroSeqGame_perfectRecall_false
  | true => zeroSeqGame_perfectRecall_true

/-- Minimax behavioral strategy profile for `zeroSeqGame`: player `false` chooses `Play` at `false`
and `(2/3, 1/3)` at `true`; player `true` chooses `(2/3, 1/3)` at `()`. -/
@[expose] noncomputable def zsOptB : ∀ i : Bool, ∀ h : zsH i, zsAct i h → ℝ
  | false, false => fun a => if a then 1 else 0
  | false, true => fun a => if a then 1 / 3 else 2 / 3
  | true, () => fun a => if a then 1 / 3 else 2 / 3

/-- Suboptimal behavioral strategy for player `false`: choose `Stay` (`0`) at root. -/
@[expose] noncomputable def zsStayB : ∀ h : zsH false, zsAct false h → ℝ
  | false => fun a => if a then 0 else 1
  | true => fun a => if a then 1 / 3 else 2 / 3

theorem zsOptB_isBehavior : ∀ i, IsBehaviorStrategy (zsOptB i) := by
  intro i h
  refine isMixedStrategy_iff.2 ⟨fun a => ?_, ?_⟩
  · cases i with
    | false =>
      cases h with
      | false => cases a <;> simp [zsOptB]
      | true => dsimp [zsOptB]; split_ifs <;> norm_num
    | true =>
      cases h
      dsimp [zsOptB]; split_ifs <;> norm_num
  · cases i with
    | false =>
      cases h with
      | false => simp [zsOptB]
      | true => simp [zsOptB]; norm_num
    | true =>
      cases h
      simp [zsOptB]; norm_num

theorem zsStayB_isBehavior : IsBehaviorStrategy zsStayB := by
  intro h
  refine isMixedStrategy_iff.2 ⟨fun a => ?_, ?_⟩
  · cases h with
    | false => cases a <;> simp [zsStayB]
    | true => dsimp [zsStayB]; split_ifs <;> norm_num
  · cases h with
    | false => simp [zsStayB]
    | true => simp [zsStayB]; norm_num

private theorem zs_evalBehavior_false (β₀ : ∀ h : zsH false, zsAct false h → ℝ)
    (β₁ : ∀ h : zsH true, zsAct true h → ℝ) :
    zeroSeqGame.evalBehavior (fun | false => β₀ | true => β₁) false =
      β₀ false true *
        (β₀ true false * (β₁ () false * 1 + β₁ () true * (-1)) +
          β₀ true true * (β₁ () false * (-1) + β₁ () true * 3)) := by
  simp only [zeroSeqGame, ExtensiveTree.evalBehavior_decision, ExtensiveTree.evalBehavior_leaf,
    Fintype.sum_bool, zsLeafPayoff, Bool.not_false, Bool.not_true, Bool.and_false, Bool.and_true,
    ↓reduceIte, Bool.false_eq_true]
  ring

private theorem zs_evalBehavior_true (β₀ : ∀ h : zsH false, zsAct false h → ℝ)
    (β₁ : ∀ h : zsH true, zsAct true h → ℝ) :
    zeroSeqGame.evalBehavior (fun | false => β₀ | true => β₁) true =
      -(zeroSeqGame.evalBehavior (fun | false => β₀ | true => β₁) false) :=
  zeroSeqGame_isZeroSum.evalBehavior_true _

/-- `zsOptB` achieves value `(1/3, -1/3)` and is a behavioral Nash equilibrium of `zeroSeqGame`,
so its realization plans `(x*, y*)` form a sequence-form Nash equilibrium and mixed Nash
equilibrium, while `Stay` strictly fails `IsSeqBestResponseFalse`. -/
theorem zeroSeqGame_equilibria_and_deviation :
    let xStar := zeroSeqGame.behaviorToRealizationPlan false (zsOptB false)
    let yStar := zeroSeqGame.behaviorToRealizationPlan true (zsOptB true)
    let xStay := zeroSeqGame.behaviorToRealizationPlan false zsStayB
    let μOpt : ∀ i, PureStrategy zsH zsAct i → ℝ := fun i => behaviorToMixed (zsOptB i)
    zeroSeqGame.IsBehaviorNash zsOptB ∧
      zeroSeqGame.evalBehavior zsOptB false = 1 / 3 ∧
      zeroSeqGame.evalBehavior zsOptB true = -(1 / 3) ∧
      zeroSeqGame.IsSeqNash xStar yStar ∧
      zeroSeqGame.toCostGame.IsMixedNash μOpt ∧
      ¬ zeroSeqGame.IsSeqBestResponseFalse xStay yStar ∧
      (∃ (q : Option {h : zsH false // zeroSeqGame.OccursInfoSet false h} → ℝ)
          (p : Option {h : zsH true // zeroSeqGame.OccursInfoSet true h} → ℝ),
        zeroSeqGame.seqPayoffMat false *ᵥ yStar ≤ (seqMat zeroSeqGame false)ᵀ *ᵥ q ∧
          (zeroSeqGame.seqPayoffMat true)ᵀ *ᵥ xStar ≤ (seqMat zeroSeqGame true)ᵀ *ᵥ p ∧
          (∀ σ, xStar σ = 0 ∨
            ((seqMat zeroSeqGame false)ᵀ *ᵥ q) σ = (zeroSeqGame.seqPayoffMat false *ᵥ yStar) σ) ∧
          (∀ τ, yStar τ = 0 ∨
            ((seqMat zeroSeqGame true)ᵀ *ᵥ p) τ =
              ((zeroSeqGame.seqPayoffMat true)ᵀ *ᵥ xStar) τ)) := by
  intro xStar yStar xStay μOpt
  have hval0 : zeroSeqGame.evalBehavior zsOptB false = 1 / 3 := by
    have heq : zsOptB = fun | false => zsOptB false | true => zsOptB true := by
      funext i; cases i <;> rfl
    rw [heq, zs_evalBehavior_false]
    simp [zsOptB]
    norm_num
  have hval1 : zeroSeqGame.evalBehavior zsOptB true = -(1 / 3) := by
    rw [zeroSeqGame_isZeroSum.evalBehavior_true, hval0]
  have hbnash : zeroSeqGame.IsBehaviorNash zsOptB := by
    refine ⟨zsOptB_isBehavior, fun i β' hβ' => ?_⟩
    cases i with
    | false =>
      have heq : Function.update zsOptB false β' = fun | false => β' | true => zsOptB true := by
        funext j; cases j <;> simp
      rw [heq, zs_evalBehavior_false, hval0]
      have hsumF : β' false true + β' false false = 1 := by
        simpa [Fintype.sum_bool] using (hβ' false).sum_eq_one
      have hsumT : β' true true + β' true false = 1 := by
        simpa [Fintype.sum_bool] using (hβ' true).sum_eq_one
      have hnnF : 0 ≤ β' false false := (hβ' false).nonneg false
      have hft : β' false true ≤ 1 := by linarith
      have hsub : β' true false * (zsOptB true () false * 1 + zsOptB true () true * (-1)) +
          β' true true * (zsOptB true () false * (-1) + zsOptB true () true * 3) = 1 / 3 := by
        simp only [zsOptB, Bool.false_eq_true, ↓reduceIte]
        linear_combination (1 / 3 : ℝ) * hsumT
      rw [hsub]
      linarith
    | true =>
      have heq : Function.update zsOptB true β' = fun | false => zsOptB false | true => β' := by
        funext j; cases j <;> simp
      rw [heq, zs_evalBehavior_true, zs_evalBehavior_false, hval1]
      have hsum2 : β' () true + β' () false = 1 := by
        simpa [Fintype.sum_bool] using (hβ' ()).sum_eq_one
      simp only [zsOptB, Bool.false_eq_true, ↓reduceIte]
      linarith
  have hsnash : zeroSeqGame.IsSeqNash xStar yStar :=
    ((isBehaviorNash_iff_isSeqNash zeroSeqGame_perfectRecall zsOptB).1 hbnash).2
  have hcomp :=
    (isSeqNash_iff_complementarity zeroSeqGame_perfectRecall xStar yStar).1 hsnash
  have hmix_plan : ∀ i,
      zeroSeqGame.mixedToRealizationPlan i (μOpt i) =
        zeroSeqGame.behaviorToRealizationPlan i (zsOptB i) := by
    intro i
    ext σ
    rw [ExtensiveTree.mixedToRealizationPlan_def, ExtensiveTree.behaviorToRealizationPlan_apply]
    obtain ⟨z, _, hz⟩ := σ.property
    have hzn := (zeroSeqGame_perfectRecall i).noRepeatedInfoSet z
    rw [← hz, List.map_append] at hzn
    exact realizationProbMixed_behaviorToMixed (zsOptB_isBehavior i)
      (List.Nodup.of_append_left hzn)
  have hmnash : zeroSeqGame.toCostGame.IsMixedNash μOpt := by
    refine (isMixedNash_toCostGame_iff_isSeqNash zeroSeqGame_perfectRecall μOpt).2
      ⟨fun i => isMixedStrategy_behaviorToMixed (zsOptB_isBehavior i), ?_⟩
    rw [hmix_plan false, hmix_plan true]
    exact hsnash
  have hstay_not_br : ¬ zeroSeqGame.IsSeqBestResponseFalse xStay yStar := by
    intro hbr
    have hle := hbr.2 xStar
      (isRealizationPlan_behaviorToRealizationPlan (zeroSeqGame_perfectRecall false)
        (zsOptB_isBehavior false))
    have hev1 : xStar ⬝ᵥ (zeroSeqGame.seqPayoffMat false *ᵥ yStar) = 1 / 3 := by
      rw [← evalBehavior_eq_seqPayoffMat, hval0]
    have hev0 : xStay ⬝ᵥ (zeroSeqGame.seqPayoffMat false *ᵥ yStar) = 0 := by
      have hstay_prof :
          zeroSeqGame.evalBehavior (fun | false => zsStayB | true => zsOptB true) false =
            xStay ⬝ᵥ (zeroSeqGame.seqPayoffMat false *ᵥ yStar) :=
        evalBehavior_eq_seqPayoffMat zeroSeqGame _ false
      rw [← hstay_prof, zs_evalBehavior_false]
      simp [zsStayB]
    linarith
  exact ⟨hbnash, hval0, hval1, hsnash, hmnash, hstay_not_br, hcomp.2.2⟩

private theorem zeroSeqGame_terminal_seq_cases (z : Terminal zeroSeqGame) :
    (z.seq false = [⟨false, false⟩] ∧ z.seq true = [] ∧ z.chanceWeight * z.payoff false = 0) ∨
    (∃ a₁ a₂ : Bool,
      z.seq false = [⟨false, true⟩, ⟨true, a₁⟩] ∧ z.seq true = [⟨(), a₂⟩] ∧
      z.chanceWeight * z.payoff false = zsLeafPayoff a₁ a₂ false) := by
  rcases z with _ | ⟨⟩ | ⟨_ | _, sub⟩
  · cases sub
    exact .inl ⟨by simp, by simp, by simp⟩
  · rcases sub with _ | ⟨⟩ | ⟨a₁, sub'⟩
    rcases sub' with _ | ⟨⟩ | ⟨a₂, sub''⟩
    cases sub''
    exact .inr ⟨a₁, a₂, by simp, by simp, by simp⟩

private theorem zsTerminal_payoff_false (a₁ a₂ : Bool) :
    (Terminal.decision true (Terminal.decision a₁ (Terminal.decision a₂ Terminal.leaf)) :
        Terminal zeroSeqGame).payoff false = zsLeafPayoff a₁ a₂ false := by
  simp

private theorem zs_seqVar_true_cases (τ : SeqVar zeroSeqGame true) :
    τ.val = [] ∨ τ.val = [⟨(), false⟩] ∨ τ.val = [⟨(), true⟩] := by
  obtain ⟨z, rem, hz⟩ := τ.property
  rcases zeroSeqGame_terminal_seq_cases z with ⟨_, hz1, _⟩ | ⟨_, _, _, hz1, _⟩
  · rw [hz1] at hz
    rcases hτ : τ.val with _ | ⟨x, tl⟩
    · exact .inl rfl
    · rw [hτ] at hz; simp at hz
  · rw [hz1] at hz
    rcases hτ : τ.val with _ | ⟨⟨⟨⟩, b⟩, _ | ⟨y, tl⟩⟩
    · exact .inl rfl
    · cases b
      · exact .inr (.inl rfl)
      · exact .inr (.inr rfl)
    · rw [hτ] at hz; simp at hz

private theorem zs_seqVar_false_cases (σ : SeqVar zeroSeqGame false) :
    σ.val = [] ∨ σ.val = [⟨false, false⟩] ∨ σ.val = [⟨false, true⟩] ∨
      σ.val = [⟨false, true⟩, ⟨true, false⟩] ∨ σ.val = [⟨false, true⟩, ⟨true, true⟩] := by
  obtain ⟨z, rem, hz⟩ := σ.property
  rcases zeroSeqGame_terminal_seq_cases z with ⟨hz0, _, _⟩ | ⟨_, _, hz0, _, _⟩
  · rw [hz0] at hz
    rcases hσ : σ.val with _ | ⟨⟨_ | _, b⟩, _ | ⟨y, tl⟩⟩
    · exact .inl rfl
    · cases b
      · exact .inr (.inl rfl)
      · rw [hσ] at hz; simp at hz
    · rw [hσ] at hz; simp at hz
    · rw [hσ] at hz; simp at hz
    · rw [hσ] at hz; simp at hz
  · rw [hz0] at hz
    rcases hσ : σ.val with _ | ⟨⟨_ | _, b⟩, tl⟩
    · exact .inl rfl
    · rcases htl : tl with _ | ⟨⟨_ | _, c⟩, _ | ⟨y, tl'⟩⟩
      · cases b
        · rw [hσ, htl] at hz; simp at hz
        · exact .inr (.inr (.inl rfl))
      · rw [hσ, htl] at hz; simp at hz
      · rw [hσ, htl] at hz; simp at hz
      · cases b
        · rw [hσ, htl] at hz; simp at hz
        · cases c
          · exact .inr (.inr (.inr (.inl rfl)))
          · exact .inr (.inr (.inr (.inr rfl)))
      · rw [hσ, htl] at hz; simp at hz
    · rw [hσ] at hz; simp at hz

open Classical in
private theorem sum_terminal_add (z₁ z₂ : Terminal zeroSeqGame) (hne : z₁ ≠ z₂) (v₁ v₂ : ℝ) :
    (∑ z : Terminal zeroSeqGame, if z = z₁ then v₁ else if z = z₂ then v₂ else 0) = v₁ + v₂ := by
  rw [← add_sum_erase univ _ (mem_univ z₁)]
  simp only [↓reduceIte]
  congr 1
  rw [sum_eq_single z₂ (fun z hz hne2 => by simp [ne_of_mem_erase hz, hne2])
    (fun hm => absurd (mem_erase.2 ⟨hne.symm, mem_univ z₂⟩) hm)]
  simp [hne.symm]

open Classical in
/-- Constant `1 / 3` dual multiplier satisfies the primal/dual LP inequalities for `zsOptB`, proving
explicitly via `IsZeroSum.exists_seq_lp_minimax` and `IsZeroSum.exists_behavior_minimax` that the
minimax value of `zeroSeqGame` is exactly `1 / 3` (and existence theorems `exists_isSeqNash`,
`exists_isBehaviorNash` apply). -/
theorem zeroSeqGame_lp_minimax_value :
    (∃ v x y q p,
      zeroSeqGame.IsRealizationPlan false x ∧ zeroSeqGame.IsRealizationPlan true y ∧
      (seqMat zeroSeqGame true)ᵀ *ᵥ q ≤ (zeroSeqGame.seqPayoffMat false)ᵀ *ᵥ x ∧
      zeroSeqGame.seqPayoffMat false *ᵥ y ≤ (seqMat zeroSeqGame false)ᵀ *ᵥ p ∧
      x ⬝ᵥ (zeroSeqGame.seqPayoffMat false *ᵥ y) = v ∧ q none = v ∧ p none = v ∧
      zeroSeqGame.IsSeqNash x y ∧ v = 1 / 3) ∧
      (∃ (v : ℝ) (β : ∀ i, ∀ h : zsH i, zsAct i h → ℝ),
        zeroSeqGame.IsBehaviorNash β ∧
          zeroSeqGame.evalBehavior β false = v ∧ zeroSeqGame.evalBehavior β true = -v ∧
          v = 1 / 3) ∧
      (∃ x y, zeroSeqGame.IsSeqNash x y) ∧
      (∃ β : ∀ i, ∀ h : zsH i, zsAct i h → ℝ, zeroSeqGame.IsBehaviorNash β) := by
  let xStar := zeroSeqGame.behaviorToRealizationPlan false (zsOptB false)
  let yStar := zeroSeqGame.behaviorToRealizationPlan true (zsOptB true)
  let qConst : Option {h : zsH true // zeroSeqGame.OccursInfoSet true h} → ℝ := fun _ => 1 / 3
  let pConst : Option {h : zsH false // zeroSeqGame.OccursInfoSet false h} → ℝ := fun _ => 1 / 3
  have hxStar : zeroSeqGame.IsRealizationPlan false xStar :=
    isRealizationPlan_behaviorToRealizationPlan (zeroSeqGame_perfectRecall false)
      (zsOptB_isBehavior false)
  have hyStar : zeroSeqGame.IsRealizationPlan true yStar :=
    isRealizationPlan_behaviorToRealizationPlan (zeroSeqGame_perfectRecall true)
      (zsOptB_isBehavior true)
  have hunit_occ : zeroSeqGame.OccursInfoSet true () :=
    ⟨.decision true (.decision true .here), rfl⟩
  have hinfo_unit : zeroSeqGame.infoSeq true () = [] := by
    have hv : (.decision true (.decision true .here) : Node zeroSeqGame).IsDecisionOf true () := rfl
    rw [← (zeroSeqGame_perfectRecall true).playerSeq_eq_infoSeq hv]
    rfl
  have hF_occ : zeroSeqGame.OccursInfoSet false false := ⟨.here, rfl⟩
  have hT_occ : zeroSeqGame.OccursInfoSet false true := ⟨.decision true .here, rfl⟩
  have hinfo_F : zeroSeqGame.infoSeq false false = [] := by
    have hv : (.here : Node zeroSeqGame).IsDecisionOf false false := rfl
    rw [← (zeroSeqGame_perfectRecall false).playerSeq_eq_infoSeq hv]
    rfl
  have hinfo_T : zeroSeqGame.infoSeq false true = [⟨false, true⟩] := by
    have hv : (.decision true .here : Node zeroSeqGame).IsDecisionOf false true := rfl
    rw [← (zeroSeqGame_perfectRecall false).playerSeq_eq_infoSeq hv]
    rfl
  have hqConst_feas : (seqMat zeroSeqGame true)ᵀ *ᵥ qConst ≤
      (zeroSeqGame.seqPayoffMat false)ᵀ *ᵥ xStar := by
    intro τ
    have hrow : ((seqMat zeroSeqGame true)ᵀ *ᵥ qConst) τ =
        qConst none * (seqMat zeroSeqGame true *ᵥ Pi.single τ (1 : ℝ)) none +
          (1 / 3 : ℝ) * (seqMat zeroSeqGame true *ᵥ Pi.single τ (1 : ℝ))
            (some ⟨(), hunit_occ⟩) := by
      have hdot : ((seqMat zeroSeqGame true)ᵀ *ᵥ qConst) τ =
          ((seqMat zeroSeqGame true)ᵀ *ᵥ qConst) ⬝ᵥ Pi.single τ (1 : ℝ) := by
        rw [dotProduct, sum_eq_single τ (fun _ _ h => by simp [h]) (fun h => absurd (mem_univ _) h)]
        simp
      rw [hdot, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, dotProduct, Fintype.sum_option]
      congr 1
      rw [sum_eq_single ⟨(), hunit_occ⟩]
      · intro h _ hne; rcases h with ⟨⟨⟩, _⟩; exact absurd rfl hne
      · intro hm; exact absurd (mem_univ _) hm
    have hArow : ((zeroSeqGame.seqPayoffMat false)ᵀ *ᵥ xStar) τ =
        ∑ z : Terminal zeroSeqGame,
          (z.chanceWeight * realizationProbBehavior (zsOptB false) (z.seq false) *
            (if z.seq true = τ.val then 1 else 0)) * z.payoff false := by
      have hdot : ((zeroSeqGame.seqPayoffMat false)ᵀ *ᵥ xStar) τ =
          xStar ⬝ᵥ (zeroSeqGame.seqPayoffMat false *ᵥ Pi.single τ (1 : ℝ)) := by
        have hs : ((zeroSeqGame.seqPayoffMat false)ᵀ *ᵥ xStar) τ =
            ((zeroSeqGame.seqPayoffMat false)ᵀ *ᵥ xStar) ⬝ᵥ Pi.single τ (1 : ℝ) := by
          rw [dotProduct, sum_eq_single τ (fun _ _ h => by simp [h])
            (fun h => absurd (mem_univ _) h)]
          simp
        rw [hs, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
      have hcol : Pi.single (M := fun _ => ℝ) τ (1 : ℝ) =
          fun τ₁ => if τ₁.val = τ.val then 1 else 0 := by
        ext τ₁
        simp only [Pi.single_apply, Subtype.ext_iff, eq_comm]
      have hxStar_eq : xStar = fun σ => realizationProbBehavior (zsOptB false) σ.val := by
        ext σ; exact ExtensiveTree.behaviorToRealizationPlan_apply _ _ _ _
      rw [hdot, hxStar_eq, hcol]
      exact seqPayoffMat_bilinear zeroSeqGame false (realizationProbBehavior (zsOptB false))
        (fun t => if t = τ.val then 1 else 0)
    have hcol_q : ((seqMat zeroSeqGame true)ᵀ *ᵥ qConst) τ =
        if τ.val = [] then 0 else 1 / 3 := by
      rw [hrow, seqMat_mulVec_none,
        seqMat_mulVec_some (zeroSeqGame_perfectRecall true) ⟨(), hunit_occ⟩]
      have hinf_eq : SeqVar.infoSeq (zeroSeqGame_perfectRecall true) hunit_occ =
          SeqVar.nil zeroSeqGame true := by
        apply Subtype.ext; rw [SeqVar.infoSeq_val, hinfo_unit]; simp
      rw [hinf_eq]
      rcases zs_seqVar_true_cases τ with h | h | h
      · have hτ : τ = SeqVar.nil zeroSeqGame true := Subtype.ext (by simp [h])
        have hne_nil : ∀ a : zsAct true (),
            SeqVar.infoSeqExt (zeroSeqGame_perfectRecall true) hunit_occ a ≠
              SeqVar.nil zeroSeqGame true := fun a he =>
          seqVar_infoSeqExt_ne_nil (zeroSeqGame_perfectRecall true) hunit_occ a
            (by simpa using congrArg Subtype.val he)
        have hrhs : (if τ.val = [] then (0 : ℝ) else 1 / 3) = 0 := by simp [h]
        rw [hrhs, hτ]
        simp [qConst, hne_nil, Pi.single_eq_same, Pi.single_eq_of_ne]
      · have hτ : τ = SeqVar.infoSeqExt (zeroSeqGame_perfectRecall true) hunit_occ false :=
          Subtype.ext (by simp [SeqVar.infoSeqExt_val, hinfo_unit, h])
        have hne_nil : SeqVar.nil zeroSeqGame true ≠ τ := fun he => by
          have := congrArg Subtype.val he
          rw [h] at this; exact absurd this.symm (by simp)
        have hne_tf : SeqVar.infoSeqExt (zeroSeqGame_perfectRecall true) hunit_occ true ≠ τ := by
          rw [hτ]
          intro he
          exact Bool.false_ne_true.symm
            (eq_of_heq (Sigma.mk.inj_iff.1 (seqVar_infoSeqExt_inj _ he)).2)
        have hrhs : (if τ.val = [] then (0 : ℝ) else 1 / 3) = 1 / 3 := by simp [h]
        rw [hrhs, hτ]
        rw [hτ] at hne_nil hne_tf
        simp [qConst, hne_nil, hne_tf, Pi.single_eq_same, Pi.single_eq_of_ne]
      · have hτ : τ = SeqVar.infoSeqExt (zeroSeqGame_perfectRecall true) hunit_occ true :=
          Subtype.ext (by simp [SeqVar.infoSeqExt_val, hinfo_unit, h])
        have hne_nil : SeqVar.nil zeroSeqGame true ≠ τ := fun he => by
          have := congrArg Subtype.val he
          rw [h] at this; exact absurd this.symm (by simp)
        have hne_ft : SeqVar.infoSeqExt (zeroSeqGame_perfectRecall true) hunit_occ false ≠ τ := by
          rw [hτ]
          intro he
          exact Bool.false_ne_true
            (eq_of_heq (Sigma.mk.inj_iff.1 (seqVar_infoSeqExt_inj _ he)).2)
        have hrhs : (if τ.val = [] then (0 : ℝ) else 1 / 3) = 1 / 3 := by simp [h]
        rw [hrhs, hτ]
        rw [hτ] at hne_nil hne_ft
        simp [qConst, hne_nil, hne_ft, Pi.single_eq_same, Pi.single_eq_of_ne]
    have hA_val : ((zeroSeqGame.seqPayoffMat false)ᵀ *ᵥ xStar) τ =
        if τ.val = [] then 0 else 1 / 3 := by
      rw [hArow]
      rcases zs_seqVar_true_cases τ with h | h | h
      · simp only [h, ↓reduceIte]
        refine sum_eq_zero fun z _ => ?_
        rcases zeroSeqGame_terminal_seq_cases z with ⟨_, _, hz0⟩ | ⟨_, _, _, hz1, _⟩
        · have : (z.chanceWeight * realizationProbBehavior (zsOptB false) (z.seq false) *
              (if z.seq true = [] then (1 : ℝ) else 0)) * z.payoff false =
              (z.chanceWeight * z.payoff false) *
                (realizationProbBehavior (zsOptB false) (z.seq false) *
                  (if z.seq true = [] then 1 else 0)) := by ring
          rw [this, hz0, zero_mul]
        · simp [hz1]
      · rw [h]
        simp only [List.cons_ne_self, ↓reduceIte]
        have hterm : ∀ z : Terminal zeroSeqGame,
            (z.chanceWeight * realizationProbBehavior (zsOptB false) (z.seq false) *
              (if z.seq true = [⟨(), false⟩] then (1 : ℝ) else 0)) * z.payoff false =
            if z = .decision true (.decision false (.decision false .leaf)) then 2 / 3
            else if z = .decision true (.decision true (.decision false .leaf)) then -(1 / 3)
            else 0 := fun z => by
          rcases z with _ | ⟨⟩ | ⟨_ | _, sub⟩
          · cases sub; simp
          · rcases sub with _ | ⟨⟩ | ⟨c₁, sub'⟩
            rcases sub' with _ | ⟨⟩ | ⟨c₂, sub''⟩
            cases sub''
            cases c₁ <;> cases c₂ <;>
              simp [zsOptB, zsTerminal_payoff_false, zsLeafPayoff]
        simp_rw [hterm]
        rw [sum_terminal_add _ _ (by simp)]
        norm_num
      · rw [h]
        simp only [List.cons_ne_self, ↓reduceIte]
        have hterm : ∀ z : Terminal zeroSeqGame,
            (z.chanceWeight * realizationProbBehavior (zsOptB false) (z.seq false) *
              (if z.seq true = [⟨(), true⟩] then (1 : ℝ) else 0)) * z.payoff false =
            if z = .decision true (.decision false (.decision true .leaf)) then -(2 / 3)
            else if z = .decision true (.decision true (.decision true .leaf)) then 1
            else 0 := fun z => by
          rcases z with _ | ⟨⟩ | ⟨_ | _, sub⟩
          · cases sub; simp
          · rcases sub with _ | ⟨⟩ | ⟨c₁, sub'⟩
            rcases sub' with _ | ⟨⟩ | ⟨c₂, sub''⟩
            cases sub''
            cases c₁ <;> cases c₂ <;>
              simp [zsOptB, zsTerminal_payoff_false, zsLeafPayoff]
        simp_rw [hterm]
        rw [sum_terminal_add _ _ (by simp)]
        norm_num
    rw [hcol_q, hA_val]
  have hpConst_feas : zeroSeqGame.seqPayoffMat false *ᵥ yStar ≤
      (seqMat zeroSeqGame false)ᵀ *ᵥ pConst := by
    intro σ
    have hrow : ((seqMat zeroSeqGame false)ᵀ *ᵥ pConst) σ =
        pConst none * (seqMat zeroSeqGame false *ᵥ Pi.single σ (1 : ℝ)) none +
          ((1 / 3 : ℝ) *
              (seqMat zeroSeqGame false *ᵥ Pi.single σ (1 : ℝ)) (some ⟨false, hF_occ⟩) +
            (1 / 3 : ℝ) *
              (seqMat zeroSeqGame false *ᵥ Pi.single σ (1 : ℝ)) (some ⟨true, hT_occ⟩)) := by
      have hdot : ((seqMat zeroSeqGame false)ᵀ *ᵥ pConst) σ =
          ((seqMat zeroSeqGame false)ᵀ *ᵥ pConst) ⬝ᵥ Pi.single σ (1 : ℝ) := by
        rw [dotProduct, sum_eq_single σ (fun _ _ h => by simp [h]) (fun h => absurd (mem_univ _) h)]
        simp
      rw [hdot, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, dotProduct, Fintype.sum_option]
      congr 1
      rw [← add_sum_erase univ _ (mem_univ ⟨false, hF_occ⟩)]
      congr 1
      rw [sum_eq_single ⟨true, hT_occ⟩]
      · intro h hm hne
        rcases h with ⟨_ | _, _⟩
        · exact absurd rfl (ne_of_mem_erase hm)
        · exact absurd rfl hne
      · intro hm
        exact absurd
          (mem_erase.2 ⟨fun he => Bool.false_ne_true (congrArg Subtype.val he).symm, mem_univ _⟩)
          hm
    have hArow : (zeroSeqGame.seqPayoffMat false *ᵥ yStar) σ =
        ∑ z : Terminal zeroSeqGame,
          (z.chanceWeight * (if z.seq false = σ.val then 1 else 0) *
            realizationProbBehavior (zsOptB true) (z.seq true)) * z.payoff false := by
      have hdot : (zeroSeqGame.seqPayoffMat false *ᵥ yStar) σ =
          Pi.single σ (1 : ℝ) ⬝ᵥ (zeroSeqGame.seqPayoffMat false *ᵥ yStar) := by
        rw [dotProduct, sum_eq_single σ (fun _ _ h => by simp [h]) (fun h => absurd (mem_univ _) h)]
        simp
      have hcol : Pi.single (M := fun _ => ℝ) σ (1 : ℝ) =
          fun σ₁ => if σ₁.val = σ.val then 1 else 0 := by
        ext σ₁; simp only [Pi.single_apply, Subtype.ext_iff, eq_comm]
      have hyStar_eq : yStar = fun τ => realizationProbBehavior (zsOptB true) τ.val := by
        ext τ; exact ExtensiveTree.behaviorToRealizationPlan_apply _ _ _ _
      rw [hdot, hyStar_eq, hcol]
      exact seqPayoffMat_bilinear zeroSeqGame false (fun s => if s = σ.val then 1 else 0)
        (realizationProbBehavior (zsOptB true))
    have hcol_p : ((seqMat zeroSeqGame false)ᵀ *ᵥ pConst) σ =
        if σ.val = [] ∨ σ.val = [⟨false, true⟩] then 0 else 1 / 3 := by
      rw [hrow, seqMat_mulVec_none,
        seqMat_mulVec_some (zeroSeqGame_perfectRecall false) ⟨false, hF_occ⟩,
        seqMat_mulVec_some (zeroSeqGame_perfectRecall false) ⟨true, hT_occ⟩]
      have hinfF_eq : SeqVar.infoSeq (zeroSeqGame_perfectRecall false) hF_occ =
          SeqVar.nil zeroSeqGame false := by
        apply Subtype.ext; rw [SeqVar.infoSeq_val, hinfo_F]; simp
      have hinfT_eq : SeqVar.infoSeq (zeroSeqGame_perfectRecall false) hT_occ =
          SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hF_occ true := by
        apply Subtype.ext; rw [SeqVar.infoSeq_val, SeqVar.infoSeqExt_val, hinfo_F, hinfo_T]; rfl
      rw [hinfF_eq, hinfT_eq]
      have hinj_diff : ∀ {a₁ : zsAct false false} {a₂ : zsAct false true},
          SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hF_occ a₁ ≠
            SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hT_occ a₂ := fun he =>
        Bool.false_ne_true
          (congrArg Subtype.val (Sigma.mk.inj_iff.1 (seqVar_infoSeqExt_inj _ he)).1)
      rcases zs_seqVar_false_cases σ with h | h | h | h | h
      · have hσ : σ = SeqVar.nil zeroSeqGame false := Subtype.ext (by simp [h])
        have hF : ∀ a, SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hF_occ a ≠
            SeqVar.nil zeroSeqGame false := fun a he =>
          seqVar_infoSeqExt_ne_nil (zeroSeqGame_perfectRecall false) hF_occ a
            (by simpa using congrArg Subtype.val he)
        have hT : ∀ a, SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hT_occ a ≠
            SeqVar.nil zeroSeqGame false := fun a he =>
          seqVar_infoSeqExt_ne_nil (zeroSeqGame_perfectRecall false) hT_occ a
            (by simpa using congrArg Subtype.val he)
        have hrhs : (if σ.val = [] ∨ σ.val = [⟨false, true⟩] then (0 : ℝ) else 1 / 3) = 0 := by
          simp [h]
        rw [hrhs, hσ]
        simp [pConst, Pi.single_eq_same, Pi.single_eq_of_ne, hF, hT]
      · have hσ : σ = SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hF_occ false :=
          Subtype.ext (by simp [SeqVar.infoSeqExt_val, hinfo_F, h])
        have hnil : SeqVar.nil zeroSeqGame false ≠
            SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hF_occ false := fun he =>
          seqVar_infoSeqExt_ne_nil _ hF_occ false (by simpa using (congrArg Subtype.val he).symm)
        have hft : SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hF_occ true ≠
            SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hF_occ false := fun he =>
          Bool.false_ne_true.symm
            (eq_of_heq (Sigma.mk.inj_iff.1 (seqVar_infoSeqExt_inj _ he)).2)
        have hT : ∀ a, SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hT_occ a ≠
            SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hF_occ false :=
          fun a he => (hinj_diff he.symm).elim
        have hrhs : (if σ.val = [] ∨ σ.val = [⟨false, true⟩] then (0 : ℝ) else 1 / 3) = 1 / 3 := by
          simp [h]
        rw [hrhs, hσ]
        simp [pConst, Pi.single_eq_same, Pi.single_eq_of_ne, hnil, hft, hT]
      · have hσ : σ = SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hF_occ true :=
          Subtype.ext (by simp [SeqVar.infoSeqExt_val, hinfo_F, h])
        have hnil : SeqVar.nil zeroSeqGame false ≠
            SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hF_occ true := fun he =>
          seqVar_infoSeqExt_ne_nil _ hF_occ true (by simpa using (congrArg Subtype.val he).symm)
        have htf : SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hF_occ false ≠
            SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hF_occ true := fun he =>
          Bool.false_ne_true
            (eq_of_heq (Sigma.mk.inj_iff.1 (seqVar_infoSeqExt_inj _ he)).2)
        have hT : ∀ a, SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hT_occ a ≠
            SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hF_occ true :=
          fun a he => (hinj_diff he.symm).elim
        have hrhs : (if σ.val = [] ∨ σ.val = [⟨false, true⟩] then (0 : ℝ) else 1 / 3) = 0 := by
          simp [h]
        rw [hrhs, hσ]
        simp [pConst, Pi.single_eq_same, Pi.single_eq_of_ne, hnil, htf, hT]
      · have hσ : σ = SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hT_occ false :=
          Subtype.ext (by simp [SeqVar.infoSeqExt_val, hinfo_T, h])
        have hnil : SeqVar.nil zeroSeqGame false ≠
            SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hT_occ false := fun he =>
          seqVar_infoSeqExt_ne_nil _ hT_occ false (by simpa using (congrArg Subtype.val he).symm)
        have hF : ∀ a, SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hF_occ a ≠
            SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hT_occ false :=
          fun a he => hinj_diff he
        have htf : SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hT_occ true ≠
            SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hT_occ false := fun he =>
          Bool.false_ne_true.symm
            (eq_of_heq (Sigma.mk.inj_iff.1 (seqVar_infoSeqExt_inj _ he)).2)
        have hrhs : (if σ.val = [] ∨ σ.val = [⟨false, true⟩] then (0 : ℝ) else 1 / 3) = 1 / 3 := by
          simp [h]
        rw [hrhs, hσ]
        simp [pConst, Pi.single_eq_same, Pi.single_eq_of_ne, hnil, hF, htf]
      · have hσ : σ = SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hT_occ true :=
          Subtype.ext (by simp [SeqVar.infoSeqExt_val, hinfo_T, h])
        have hnil : SeqVar.nil zeroSeqGame false ≠
            SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hT_occ true := fun he =>
          seqVar_infoSeqExt_ne_nil _ hT_occ true (by simpa using (congrArg Subtype.val he).symm)
        have hF : ∀ a, SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hF_occ a ≠
            SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hT_occ true :=
          fun a he => hinj_diff he
        have hft : SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hT_occ false ≠
            SeqVar.infoSeqExt (zeroSeqGame_perfectRecall false) hT_occ true := fun he =>
          Bool.false_ne_true
            (eq_of_heq (Sigma.mk.inj_iff.1 (seqVar_infoSeqExt_inj _ he)).2)
        have hrhs : (if σ.val = [] ∨ σ.val = [⟨false, true⟩] then (0 : ℝ) else 1 / 3) = 1 / 3 := by
          simp [h]
        rw [hrhs, hσ]
        simp [pConst, Pi.single_eq_same, Pi.single_eq_of_ne, hnil, hF, hft]
    have hA_val : (zeroSeqGame.seqPayoffMat false *ᵥ yStar) σ =
        if σ.val = [] ∨ σ.val = [⟨false, false⟩] ∨ σ.val = [⟨false, true⟩] then 0 else 1 / 3 := by
      rw [hArow]
      rcases zs_seqVar_false_cases σ with h | h | h | h | h
      · simp only [h, true_or, ↓reduceIte]
        refine sum_eq_zero fun z _ => ?_
        rcases zeroSeqGame_terminal_seq_cases z with ⟨hz0, _, _⟩ | ⟨_, _, hz0, _, _⟩ <;> simp [hz0]
      · simp only [h, true_or, or_true, ↓reduceIte]
        refine sum_eq_zero fun z _ => ?_
        rcases zeroSeqGame_terminal_seq_cases z with ⟨_, _, hz0⟩ | ⟨_, _, hz0, _, _⟩
        · have : (z.chanceWeight * (if z.seq false = [⟨false, false⟩] then (1 : ℝ) else 0) *
              realizationProbBehavior (zsOptB true) (z.seq true)) * z.payoff false =
              (z.chanceWeight * z.payoff false) *
                ((if z.seq false = [⟨false, false⟩] then (1 : ℝ) else 0) *
                  realizationProbBehavior (zsOptB true) (z.seq true)) := by ring
          rw [this, hz0, zero_mul]
        · simp [hz0]
      · simp only [h, or_true, ↓reduceIte]
        refine sum_eq_zero fun z _ => ?_
        rcases zeroSeqGame_terminal_seq_cases z with ⟨hz0, _, _⟩ | ⟨_, _, hz0, _, _⟩ <;> simp [hz0]
      · have hrhs :
            (if σ.val = [] ∨ σ.val = [⟨false, false⟩] ∨ σ.val = [⟨false, true⟩] then (0 : ℝ)
              else 1 / 3) = 1 / 3 := by simp [h]
        rw [hrhs, h]
        have hterm : ∀ z : Terminal zeroSeqGame,
            (z.chanceWeight *
              (if z.seq false = [⟨false, true⟩, ⟨true, false⟩] then (1 : ℝ) else 0) *
              realizationProbBehavior (zsOptB true) (z.seq true)) * z.payoff false =
            if z = .decision true (.decision false (.decision false .leaf)) then 2 / 3
            else if z = .decision true (.decision false (.decision true .leaf)) then -(1 / 3)
            else 0 := fun z => by
          rcases z with _ | ⟨⟩ | ⟨_ | _, sub⟩
          · cases sub; simp
          · rcases sub with _ | ⟨⟩ | ⟨c₁, sub'⟩
            rcases sub' with _ | ⟨⟩ | ⟨c₂, sub''⟩
            cases sub''
            cases c₁ <;> cases c₂ <;>
              simp [zsOptB, zsTerminal_payoff_false, zsLeafPayoff]
        simp_rw [hterm]
        rw [sum_terminal_add _ _ (by simp)]
        norm_num
      · have hrhs :
            (if σ.val = [] ∨ σ.val = [⟨false, false⟩] ∨ σ.val = [⟨false, true⟩] then (0 : ℝ)
              else 1 / 3) = 1 / 3 := by simp [h]
        rw [hrhs, h]
        have hterm : ∀ z : Terminal zeroSeqGame,
            (z.chanceWeight *
              (if z.seq false = [⟨false, true⟩, ⟨true, true⟩] then (1 : ℝ) else 0) *
              realizationProbBehavior (zsOptB true) (z.seq true)) * z.payoff false =
            if z = .decision true (.decision true (.decision false .leaf)) then -(2 / 3)
            else if z = .decision true (.decision true (.decision true .leaf)) then 1
            else 0 := fun z => by
          rcases z with _ | ⟨⟩ | ⟨_ | _, sub⟩
          · cases sub; simp
          · rcases sub with _ | ⟨⟩ | ⟨c₁, sub'⟩
            rcases sub' with _ | ⟨⟩ | ⟨c₂, sub''⟩
            cases sub''
            cases c₁ <;> cases c₂ <;>
              simp [zsOptB, zsTerminal_payoff_false, zsLeafPayoff]
        simp_rw [hterm]
        rw [sum_terminal_add _ _ (by simp)]
        norm_num
    rw [hcol_p, hA_val]
    rcases zs_seqVar_false_cases σ with h | h | h | h | h <;> simp [h]
  obtain ⟨vLP, xLP, yLP, qLP, pLP, hxLP, hyLP, hqLP, hpLP, hmidLP, hqvalLP, hpvalLP, hnashLP,
      hmaxLP, hminLP⟩ := zeroSeqGame_isZeroSum.exists_seq_lp_minimax zeroSeqGame_perfectRecall
  have hv_lo : (1 / 3 : ℝ) ≤ vLP := hmaxLP.2 ⟨(xStar, qConst), ⟨hxStar, hqConst_feas⟩, rfl⟩
  have hv_hi : vLP ≤ 1 / 3 := hminLP.2 ⟨(yStar, pConst), ⟨hyStar, hpConst_feas⟩, rfl⟩
  have hv_eq : vLP = 1 / 3 := le_antisymm hv_hi hv_lo
  obtain ⟨vB, βB, hβB_nash, hβB_0, hβB_1⟩ :=
    zeroSeqGame_isZeroSum.exists_behavior_minimax zeroSeqGame_perfectRecall
  have hβB_val : vB = 1 / 3 := by
    have hseqB := ((isBehaviorNash_iff_isSeqNash zeroSeqGame_perfectRecall βB).1 hβB_nash).2
    let xB := zeroSeqGame.behaviorToRealizationPlan false (βB false)
    let yB := zeroSeqGame.behaviorToRealizationPlan true (βB true)
    have hxb : zeroSeqGame.IsRealizationPlan false xB := hseqB.1.1
    have hyb : zeroSeqGame.IsRealizationPlan true yB := hseqB.2.1
    have _ := ExtensiveTree.IsZeroSum.seq_weak_duality hxStar hyStar hqConst_feas hpConst_feas
    have hwd1 : (1 / 3 : ℝ) ≤ xStar ⬝ᵥ (zeroSeqGame.seqPayoffMat false *ᵥ yB) := by
      calc (1 / 3 : ℝ) = qConst none := rfl
        _ = seqRhs zeroSeqGame true ⬝ᵥ qConst := (seqRhs_dotProduct _ true qConst).symm
        _ = (seqMat zeroSeqGame true *ᵥ yB) ⬝ᵥ qConst := by rw [hyb.2]
        _ = yB ⬝ᵥ ((seqMat zeroSeqGame true)ᵀ *ᵥ qConst) := by
            rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
        _ ≤ yB ⬝ᵥ ((zeroSeqGame.seqPayoffMat false)ᵀ *ᵥ xStar) :=
            dotProduct_le_dotProduct_of_nonneg_left hqConst_feas hyb.1
        _ = xStar ⬝ᵥ (zeroSeqGame.seqPayoffMat false *ᵥ yB) := by
            rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]
    have hwd2 : xB ⬝ᵥ (zeroSeqGame.seqPayoffMat false *ᵥ yStar) ≤ 1 / 3 := by
      calc xB ⬝ᵥ (zeroSeqGame.seqPayoffMat false *ᵥ yStar)
          ≤ xB ⬝ᵥ ((seqMat zeroSeqGame false)ᵀ *ᵥ pConst) :=
            dotProduct_le_dotProduct_of_nonneg_left hpConst_feas hxb.1
        _ = (seqMat zeroSeqGame false *ᵥ xB) ⬝ᵥ pConst := by
            rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
        _ = seqRhs zeroSeqGame false ⬝ᵥ pConst := by rw [hxb.2]
        _ = pConst none := seqRhs_dotProduct _ false pConst
        _ = 1 / 3 := rfl
    have hbr0 : xStar ⬝ᵥ (zeroSeqGame.seqPayoffMat false *ᵥ yB) ≤
        xB ⬝ᵥ (zeroSeqGame.seqPayoffMat false *ᵥ yB) := hseqB.1.2 xStar hxStar
    have hbr1 : xB ⬝ᵥ (zeroSeqGame.seqPayoffMat false *ᵥ yB) ≤
        xB ⬝ᵥ (zeroSeqGame.seqPayoffMat false *ᵥ yStar) := by
      have hmat := zeroSeqGame_isZeroSum.seqPayoffMat_true_of_perfectRecall
        zeroSeqGame_perfectRecall
      have h := hseqB.2.2 yStar hyStar
      rw [hmat, neg_mulVec, dotProduct_neg, neg_mulVec, dotProduct_neg, neg_le_neg_iff] at h
      exact h
    have hev : xB ⬝ᵥ (zeroSeqGame.seqPayoffMat false *ᵥ yB) = vB := by
      rw [← evalBehavior_eq_seqPayoffMat, hβB_0]
    linarith
  exact ⟨⟨vLP, xLP, yLP, qLP, pLP, hxLP, hyLP, hqLP, hpLP, hmidLP, hqvalLP, hpvalLP, hnashLP,
      hv_eq⟩,
    ⟨vB, βB, hβB_nash, hβB_0, hβB_1, hβB_val⟩,
    exists_isSeqNash zeroSeqGame_perfectRecall,
    exists_isBehaviorNash zeroSeqGame_perfectRecall⟩

end CslibFrontierTests.GameTheory.ExtensiveSequenceLP
