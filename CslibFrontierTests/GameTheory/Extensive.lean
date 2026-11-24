/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.Extensive.PerfectInfo
import CslibFrontier.GameTheory.Extensive.Basic
import CslibFrontier.GameTheory.Extensive.SequenceForm
import Mathlib.Data.Fin.VecNotation

/-!
# Extensive-form games, backward induction, sequence form, and Kuhn's theorem

Non-vacuous checked examples exercising finite extensive-form games and [vonStengel2007], Chapter 3:

* Entry deterrence (`entryTree`): classic finite deterministic perfect-information game with
  distinct leaf payoffs. Backward induction ([vonStengel2007], Algorithm 3.9) and uniqueness yield
  the unique subgame-perfect equilibrium `(Enter, Accommodate)` with payoff `(2, 1)`, whereas the
  non-credible threat `(Out, Fight)` is a pure Nash equilibrium of `entryTree.toCostGame` that
  fails to be subgame-perfect.
* Chance tree with distinct leaf payoffs (`chanceTieTree`): distinct leaf payoffs alone do not
  rule out continuation ties once chance nodes are present, so `IsDeterministic` cannot be dropped
  from `existsUnique_isPureSPE`; Zermelo's existence theorem (`exists_isPureSPE`) still applies.
* Sequential hidden-move game (`seqGame`): two-player extensive game with perfect recall
  ([vonStengel2007], Sections 3.7, 3.9–3.10). Checks reduced strategic-form equivalence
  (`ReducedEquiv`, `evalPure_eq_of_reducedEquiv`), sequence count (`card_seqVar`), flow
  conservation (`IsRealizationPlan`), mixed realization equivalence
  (`realizationEquivMixed_iff_mixedToRealizationPlan_eq`, Proposition 3.11), behavioral uniqueness
  (`realizationPlanToBehavior_unique`, Proposition 3.10), explicit behavioral reconstruction via
  Kuhn's theorem (`kuhn_theorem`), two-player bilinear sequence form
  (`evalBehavior_eq_seqPayoffMat`, `evalMixed_eq_seqPayoffMat`), and extreme-point / vertex
  separation (`isVertex_seqPolyMat_iff`).
* Imperfect-recall counterexample (`forgetfulGame`): a single-player game violating
  `PerfectRecall` (while still satisfying `NoRepeatedInfoSet`, so not absent-mindedness in the
  repeated-information-set sense) in which a mixed strategy `½(false, false) + ½(true, true)` has no
  realization-equivalent behavior strategy, showing perfect recall cannot be dropped from Kuhn's
  theorem.
-/

namespace CslibFrontierTests.GameTheory.Extensive

open Cslib.GameTheory Cslib.GameTheory.Extensive Finset Matrix

/-! ### 1. Perfect-information entry deterrence and non-credible threats -/

/-- Entry-deterrence game: player `0` (Entrant) chooses `Out` (`false`, payoff `(1, 2)`) or
`Enter` (`true`); upon entry, player `1` (Incumbent) chooses `Accommodate` (`false`, payoff
`(2, 1)`) or `Fight` (`true`, payoff `(0, 0)`). -/
abbrev entryTree : PerfectInfoTree (Fin 2) :=
  .decision 0 fun
    | false => .leaf ![1, 2]
    | true => .decision 1 fun
        | false => .leaf ![2, 1]
        | true => .leaf ![0, 0]

/-- Unique subgame-perfect equilibrium strategy profile: `(Enter, Accommodate)`. -/
abbrev entrySPE : ∀ i : Fin 2, PerfectInfoTree.PureStrategy i entryTree :=
  fun _ => .decision (fun _ => true) fun
    | false => .leaf
    | true => .decision (fun _ => false) fun
        | false => .leaf
        | true => .leaf

/-- Non-credible threat profile `(Out, Fight)`. -/
abbrev entryThreat : ∀ i : Fin 2, PerfectInfoTree.PureStrategy i entryTree :=
  fun _ => .decision (fun _ => false) fun
    | false => .leaf
    | true => .decision (fun _ => true) fun
        | false => .leaf
        | true => .leaf

theorem entryTree_isDeterministic : entryTree.IsDeterministic := by
  intro b
  cases b
  · trivial
  · intro f
    cases f <;> trivial

theorem entryTree_hasDistinctLeafPayoffs : entryTree.HasDistinctLeafPayoffs := by
  intro z₁ z₂ hne i
  rcases z₁ with _ | ⟨b₁, sub₁⟩ | ⟨⟩
  rcases z₂ with _ | ⟨b₂, sub₂⟩ | ⟨⟩
  cases b₁ <;> cases b₂
  · cases sub₁
    cases sub₂
    exact absurd rfl hne
  · cases sub₁
    rcases sub₂ with _ | ⟨f₂, leaf₂⟩ | ⟨⟩
    cases f₂ <;> cases leaf₂ <;> fin_cases i <;> simp
  · rcases sub₁ with _ | ⟨f₁, leaf₁⟩ | ⟨⟩
    cases sub₂
    cases f₁ <;> cases leaf₁ <;> fin_cases i <;> simp
  · rcases sub₁ with _ | ⟨f₁, leaf₁⟩ | ⟨⟩
    rcases sub₂ with _ | ⟨f₂, leaf₂⟩ | ⟨⟩
    cases f₁ <;> cases f₂ <;> cases leaf₁ <;> cases leaf₂
    · exact absurd rfl hne
    · fin_cases i <;> simp
    · fin_cases i <;> simp
    · exact absurd rfl hne

theorem entrySPE_isPureSPE : entryTree.IsPureSPE entrySPE := by
  rw [PerfectInfoTree.isPureSPE_iff_oneShot]
  refine ⟨fun a => ?_, fun b => ?_⟩
  · cases a
    · dsimp only [entrySPE]
      rw [PerfectInfoTree.PureStrategy.headChoice_decision]
      simp only [PerfectInfoTree.PureStrategy.childDecision_decision,
        PerfectInfoTree.expectedPayoff_decision]
      rw [PerfectInfoTree.PureStrategy.headChoice_decision]
      simp
    · dsimp only [entrySPE]
      rw [PerfectInfoTree.PureStrategy.headChoice_decision]
  · cases b
    · trivial
    · refine ⟨fun f => ?_, fun f => ?_⟩
      · dsimp only [entrySPE]
        rw [PerfectInfoTree.PureStrategy.childDecision_decision,
          PerfectInfoTree.PureStrategy.headChoice_decision]
        cases f <;> simp
      · cases f <;> trivial

/-- Every pure SPE (in particular backward induction) equals `entrySPE`, with payoff `(2, 1)`. -/
theorem entryTree_unique_spe :
    entryTree.backwardInduction.strategy = entrySPE ∧
      (∀ s, entryTree.IsPureSPE s → s = entrySPE) ∧
      entryTree.expectedPayoff entrySPE = ![2, 1] := by
  obtain ⟨u, _, hu_uniq⟩ :=
    PerfectInfoTree.existsUnique_isPureSPE entryTree_isDeterministic
      entryTree_hasDistinctLeafPayoffs
  have hbi : entryTree.backwardInduction.strategy = entrySPE := by
    rw [hu_uniq _ (PerfectInfoTree.isPureSPE_backwardInduction entryTree),
      hu_uniq _ entrySPE_isPureSPE]
  refine ⟨hbi, fun s hs => ?_, ?_⟩
  · rw [hu_uniq s hs, hu_uniq entrySPE entrySPE_isPureSPE]
  · ext i
    rw [PerfectInfoTree.expectedPayoff_decision]
    dsimp only [entrySPE]
    rw [PerfectInfoTree.PureStrategy.headChoice_decision]
    simp only [PerfectInfoTree.PureStrategy.childDecision_decision,
      PerfectInfoTree.expectedPayoff_decision]
    rw [PerfectInfoTree.PureStrategy.headChoice_decision]
    fin_cases i <;> simp

/-- `(Out, Fight)` is a pure Nash equilibrium of the strategic form yet fails `IsPureSPE`. -/
theorem entryThreat_isPureNash_not_isPureSPE :
    entryTree.toCostGame.IsPureNash entryThreat ∧ ¬ entryTree.IsPureSPE entryThreat := by
  constructor
  · intro i s'
    match i with
    | ⟨0, hi⟩ =>
      simp only [PerfectInfoTree.toCostGame_cost, neg_le_neg_iff]
      have hupd0 : (Function.update entryThreat ⟨0, hi⟩ s' 0).headChoice = s'.headChoice := by
        simp
      rw [PerfectInfoTree.expectedPayoff_decision, hupd0, PerfectInfoTree.expectedPayoff_decision]
      dsimp only [entryThreat]
      rw [PerfectInfoTree.PureStrategy.headChoice_decision]
      cases s'.headChoice
      · simp [Function.update]
      · simp only [PerfectInfoTree.PureStrategy.childDecision_decision,
          PerfectInfoTree.expectedPayoff_decision]
        have h1 : (Function.update entryThreat ⟨0, hi⟩ s' 1).childDecision true =
            (entryThreat 1).childDecision true := by
          simp [Function.update]
        dsimp only [entryThreat] at h1 ⊢
        rw [h1, PerfectInfoTree.PureStrategy.childDecision_decision,
          PerfectInfoTree.PureStrategy.headChoice_decision]
        simp
    | ⟨1, hi⟩ =>
      simp only [PerfectInfoTree.toCostGame_cost, neg_le_neg_iff]
      rw [PerfectInfoTree.expectedPayoff_decision, PerfectInfoTree.expectedPayoff_decision]
      have h0 : (Function.update entryThreat ⟨1, hi⟩ s' 0).headChoice = false := by
        have hne : (0 : Fin 2) ≠ ⟨1, hi⟩ := Fin.ne_of_val_ne Nat.zero_ne_one
        rw [Function.update_of_ne hne]
        simp [entryThreat]
      have h0' : (entryThreat 0).headChoice = false := by
        simp [entryThreat]
      rw [h0, h0']
      simp [Function.update]
  · intro hspe
    exact absurd (entryTree_unique_spe.2.1 entryThreat hspe) (by
      intro heq
      have hhc := congrArg PerfectInfoTree.PureStrategy.headChoice (congrFun heq 0)
      simp at hhc)

/-! ### 2. Chance nodes can cause continuation ties despite distinct leaf payoffs -/

private theorem fairCoin_isMixed : IsMixedStrategy (fun _ : Bool => (1 / 2 : ℝ)) :=
  isMixedStrategy_iff.2 ⟨fun _ => by norm_num, by norm_num⟩

/-- Deterministic-leaf game with a chance move in each branch: all 4 leaves have pairwise
distinct payoffs, yet both root actions yield expected payoff `2` to player `0`. -/
@[reducible] noncomputable def chanceTieTree : PerfectInfoTree (Fin 2) :=
  .decision 0 fun
    | false =>
      .chance (fun _ : Bool => (1 / 2 : ℝ)) fairCoin_isMixed fun
        | false => .leaf ![4, 1]
        | true => .leaf ![0, 2]
    | true =>
      .chance (fun _ : Bool => (1 / 2 : ℝ)) fairCoin_isMixed fun
        | false => .leaf ![3, 4]
        | true => .leaf ![1, 5]

/-- Pure strategy profile for `chanceTieTree` picking root branch `choice0 : Bool`. -/
@[reducible] noncomputable def chanceTieStrat (choice0 : Bool) :
    ∀ i : Fin 2, PerfectInfoTree.PureStrategy i chanceTieTree :=
  fun _ => .decision (fun _ => choice0) fun
    | false => .chance fun
        | false => .leaf
        | true => .leaf
    | true => .chance fun
        | false => .leaf
        | true => .leaf

theorem chanceTieTree_hasDistinctLeafPayoffs : chanceTieTree.HasDistinctLeafPayoffs := by
  intro z₁ z₂ hne i
  rcases z₁ with _ | ⟨b₁, sub₁⟩ | ⟨⟩
  rcases z₂ with _ | ⟨b₂, sub₂⟩ | ⟨⟩
  cases b₁ <;> cases b₂
  · rcases sub₁ with _ | _ | ⟨c₁, l₁⟩
    rcases sub₂ with _ | _ | ⟨c₂, l₂⟩
    cases c₁ <;> cases c₂ <;> cases l₁ <;> cases l₂
    · exact absurd rfl hne
    · fin_cases i <;> simp
    · fin_cases i <;> simp
    · exact absurd rfl hne
  · rcases sub₁ with _ | _ | ⟨c₁, l₁⟩
    rcases sub₂ with _ | _ | ⟨c₂, l₂⟩
    cases c₁ <;> cases c₂ <;> cases l₁ <;> cases l₂ <;> fin_cases i <;> simp
  · rcases sub₁ with _ | _ | ⟨c₁, l₁⟩
    rcases sub₂ with _ | _ | ⟨c₂, l₂⟩
    cases c₁ <;> cases c₂ <;> cases l₁ <;> cases l₂ <;> fin_cases i <;> simp
  · rcases sub₁ with _ | _ | ⟨c₁, l₁⟩
    rcases sub₂ with _ | _ | ⟨c₂, l₂⟩
    cases c₁ <;> cases c₂ <;> cases l₁ <;> cases l₂
    · exact absurd rfl hne
    · fin_cases i <;> simp
    · fin_cases i <;> simp
    · exact absurd rfl hne

theorem chanceTieStrat_isPureSPE (b : Bool) : chanceTieTree.IsPureSPE (chanceTieStrat b) := by
  rw [PerfectInfoTree.isPureSPE_iff_oneShot]
  refine ⟨fun a => ?_, fun br => ?_⟩
  · dsimp only [chanceTieStrat]
    rw [PerfectInfoTree.PureStrategy.headChoice_decision]
    cases b <;> cases a <;>
      simp [PerfectInfoTree.PureStrategy.childDecision_decision] <;> norm_num
  · cases br <;> intro c <;> cases c <;> trivial

theorem chanceTieTree_not_hasNoContinuationTies : ¬ chanceTieTree.HasNoContinuationTies := by
  intro htie
  have heq : chanceTieStrat false = chanceTieStrat true := by
    rw [PerfectInfoTree.eq_backwardInduction_of_isPureSPE htie (chanceTieStrat_isPureSPE false),
      PerfectInfoTree.eq_backwardInduction_of_isPureSPE htie (chanceTieStrat_isPureSPE true)]
  have hhc := congrArg PerfectInfoTree.PureStrategy.headChoice (congrFun heq 0)
  simp [chanceTieStrat] at hhc

/-! ### 3. Imperfect information, sequence form, and Kuhn's theorem -/

/-- Information sets for `seqGame`: player `false` acts at `false` (Stay/Play) and `true` (L/R);
player `true` acts at `()` without observing player `false`'s L/R choice. -/
abbrev seqH : Bool → Type
  | false => Bool
  | true => Unit

instance (i : Bool) : Fintype (seqH i) := by cases i <;> infer_instance
instance (i : Bool) : DecidableEq (seqH i) := by cases i <;> infer_instance

/-- Actions in `seqGame`: binary at every information set. -/
abbrev seqAct : ∀ i : Bool, seqH i → Type := fun _ _ => Bool

instance (i : Bool) (h : seqH i) : Fintype (seqAct i h) := by
  dsimp [seqAct]; infer_instance
instance (i : Bool) (h : seqH i) : DecidableEq (seqAct i h) := by
  dsimp [seqAct]; infer_instance
instance (i : Bool) (h : seqH i) : Nonempty (seqAct i h) := by
  dsimp [seqAct]; exact ⟨false⟩

/-- Two-player imperfect-information extensive game with perfect recall ([vonStengel2007], §3.7).
Player `false` moves `Stay` (`false`) for payoff `(1, 1)` or `Play` (`true`), then players
`false` and `true` play simultaneous matching pennies with payoffs `(2, 0)` on match and `(0, 2)`
on mismatch. -/
abbrev seqGame : ExtensiveTree Bool seqH seqAct :=
  .decision false (false : Bool) fun
    | false => .leaf (fun _ => 1)
    | true =>
      .decision false (true : Bool) fun a₁ =>
        .decision true () fun a₂ =>
          .leaf (fun
            | false => if a₁ == a₂ then 2 else 0
            | true => if a₁ == a₂ then 0 else 2)

private theorem seqGame_perfectRecall_false : seqGame.PerfectRecall false := by
  intro h v₁ v₂ hv₁ hv₂
  cases h
  · rcases v₁ with _ | ⟨⟩ | ⟨_ | _, sub₁⟩
    · rcases v₂ with _ | ⟨⟩ | ⟨_ | _, sub₂⟩
      · rfl
      · cases sub₂
        simp at hv₂
      · rcases sub₂ with _ | ⟨⟩ | ⟨c₂, sub₂'⟩
        · simp at hv₂
        · rcases sub₂' with _ | ⟨⟩ | ⟨d₂, sub₂''⟩
          · simp at hv₂
          · cases sub₂''
            simp at hv₂
    · cases sub₁
      simp at hv₁
    · rcases sub₁ with _ | ⟨⟩ | ⟨c₁, sub₁'⟩
      · simp at hv₁
      · rcases sub₁' with _ | ⟨⟩ | ⟨d₁, sub₁''⟩
        · simp at hv₁
        · cases sub₁''
          simp at hv₁
  · rcases v₁ with _ | ⟨⟩ | ⟨_ | _, sub₁⟩
    · simp at hv₁
    · cases sub₁
      simp at hv₁
    · rcases v₂ with _ | ⟨⟩ | ⟨_ | _, sub₂⟩
      · simp at hv₂
      · cases sub₂
        simp at hv₂
      · rcases sub₁ with _ | ⟨⟩ | ⟨c₁, sub₁'⟩
        · rcases sub₂ with _ | ⟨⟩ | ⟨c₂, sub₂'⟩
          · rfl
          · rcases sub₂' with _ | ⟨⟩ | ⟨d₂, sub₂''⟩
            · simp at hv₂
            · cases sub₂''
              simp at hv₂
        · rcases sub₁' with _ | ⟨⟩ | ⟨d₁, sub₁''⟩
          · simp at hv₁
          · cases sub₁''
            simp at hv₁

private theorem seqGame_perfectRecall_true : seqGame.PerfectRecall true := by
  intro h v₁ v₂ hv₁ hv₂
  cases h
  have hseq : ∀ (v : Node seqGame), v.IsDecisionOf true () → v.playerSeq true = [] := by
    intro v hv
    rcases v with _ | ⟨⟩ | ⟨_ | _, sub⟩
    · simp at hv
    · cases sub
      simp at hv
    · rcases sub with _ | ⟨⟩ | ⟨c, sub'⟩
      · simp at hv
      · rcases sub' with _ | ⟨⟩ | ⟨d, sub''⟩
        · rfl
        · cases sub''
          simp at hv
  rw [hseq v₁ hv₁, hseq v₂ hv₂]

/-- Concrete mixed strategy for player `false`: weights `1/2` on `(Stay, L)`, `0` on `(Stay, R)`,
`1/6` on `(Play, L)`, `1/3` on `(Play, R)`. -/
noncomputable def seqMixed : PureStrategy seqH seqAct false → ℝ := fun s =>
  if !s false then if !s true then 1 / 2 else 0
  else if !s true then 1 / 6 else 1 / 3

private theorem sum_bool_fun_cases (P : (Bool → Bool) → ℝ) :
    (∑ s : Bool → Bool, P s) =
      P (fun _ => false) + P (fun b => b) + P (fun b => !b) + P (fun _ => true) := by
  have huniv : (univ : Finset (Bool → Bool)) =
      {(fun _ => false), (fun b => b), (fun b => !b), (fun _ => true)} := by
    ext f
    simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    cases hf0 : f false <;> cases hf1 : f true
    · exact Or.inl (funext fun b => by cases b <;> assumption)
    · exact Or.inr (Or.inl (funext fun b => by cases b <;> assumption))
    · exact Or.inr (Or.inr (Or.inl (funext fun b => by cases b <;> assumption)))
    · exact Or.inr (Or.inr (Or.inr (funext fun b => by cases b <;> assumption)))
  rw [huniv]
  rw [Finset.sum_insert (by
    simp only [mem_insert, mem_singleton, not_or]
    refine ⟨fun h => Bool.false_ne_true (congrFun h true),
      fun h => Bool.false_ne_true (congrFun h false),
      fun h => Bool.false_ne_true (congrFun h false)⟩)]
  rw [Finset.sum_insert (by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨fun h => Bool.false_ne_true (congrFun h false),
      fun h => Bool.false_ne_true (congrFun h false)⟩)]
  rw [Finset.sum_insert (by
    simp only [mem_singleton]
    exact fun h => Bool.false_ne_true (congrFun h true))]
  rw [Finset.sum_singleton]
  ring

theorem seqMixed_isMixed : IsMixedStrategy seqMixed := by
  refine isMixedStrategy_iff.2 ⟨fun s => ?_, ?_⟩
  · dsimp [seqMixed]
    cases s false <;> cases s true <;> norm_num
  · change (∑ s : Bool → Bool, seqMixed s) = 1
    rw [sum_bool_fun_cases]
    norm_num [seqMixed]

/-- Player `false`'s strategies `(Stay, L)` and `(Stay, R)` differ at `true`, yet agree in the
reduced strategic form (`ReducedEquiv`). -/
theorem seqGame_reducedEquiv_stay :
    seqGame.ReducedEquiv false (fun _ => false) (fun b => b) := by
  rw [reducedEquiv_iff_agree_on_reachable seqGame_perfectRecall_false]
  intro h _ hm
  cases h
  · rfl
  · exfalso
    have hv : (Node.decision (true : Bool) (Node.here (T := _)) : Node seqGame).IsDecisionOf
        false (true : Bool) := rfl
    have hinf := seqGame_perfectRecall_false.playerSeq_eq_infoSeq hv
    rw [← hinf] at hm
    have hp := hm ⟨false, true⟩ (by simp [Node.playerSeq])
    simp at hp

/-- Under `seqGame_reducedEquiv_stay`, `(Stay, L)` and `(Stay, R)` yield identical payoffs
against any opponent strategy (`evalPure_eq_of_reducedEquiv`), and the corresponding pure mixed
strategies are realization-equivalent (`realizationEquivMixed_iff_mixedToRealizationPlan_eq`). -/
theorem seqGame_reduced_and_prop311 :
    (∀ s : ∀ j, PureStrategy seqH seqAct j, ∀ k,
      seqGame.evalPure (Function.update s false fun _ => false) k =
        seqGame.evalPure (Function.update s false fun b => b) k) ∧
    seqGame.RealizationEquivMixed false
      (Pi.single (fun _ : Bool => false) (1 : ℝ))
      (Pi.single (fun b : Bool => b) (1 : ℝ)) := by
  refine ⟨fun s k => evalPure_eq_of_reducedEquiv seqGame_reducedEquiv_stay s k, ?_⟩
  have hpos : seqGame.HasPositiveChance := by
    intro b
    cases b
    · trivial
    · intro a₁ a₂
      trivial
  have hnr : ∀ j ≠ false, seqGame.NoRepeatedInfoSet j := by
    intro j hj
    cases j
    · exact absurd rfl hj
    · exact seqGame_perfectRecall_true.noRepeatedInfoSet
  rw [realizationEquivMixed_iff_mixedToRealizationPlan_eq hpos hnr]
  rw [← pureToRealizationPlan_eq_mixedToRealizationPlan,
    ← pureToRealizationPlan_eq_mixedToRealizationPlan]
  exact seqGame_reducedEquiv_stay

open Classical in
/-- For player `false` in `seqGame`, the 2 occurring binary information sets yield `1 + 4 = 5`
realized sequences (`card_seqVar`). -/
theorem seqGame_card_seqVar : Fintype.card (SeqVar seqGame false) = 5 := by
  rw [card_seqVar seqGame_perfectRecall_false]
  have hocc : ∀ h : seqH false, seqGame.OccursInfoSet false h := by
    intro h
    cases h
    · exact ⟨Node.here, rfl⟩
    · exact ⟨Node.decision true Node.here, rfl⟩
  let e : {h : seqH false // seqGame.OccursInfoSet false h} ≃ Bool :=
    { toFun := fun h => h.1
      invFun := fun b => ⟨b, hocc b⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.sum_equiv e _ (fun _ => Fintype.card Bool) (fun _ => rfl)]
  simp [Fintype.card_bool]

/-- Kuhn's theorem produces an explicit behavioral realization-equivalent strategy `β` for
`seqMixed`, matching its realization plan `x`, bilinear sequence-form payoffs, and separating
pure polytope vertices from strictly mixed realization plans (`isVertex_seqPolyMat_iff`). -/
theorem seqGame_kuhn_and_sequenceForm :
    let x := seqGame.mixedToRealizationPlan false seqMixed
    let β := seqGame.realizationPlanToBehavior false seqGame_perfectRecall_false x
    let βOpp : ∀ _ : seqH true, seqAct true () → ℝ := fun _ _ => 1 / 2
    let profB : ∀ i, ∀ h : seqH i, seqAct i h → ℝ := fun
      | false => β
      | true => βOpp
    let profM : ∀ i, PureStrategy seqH seqAct i → ℝ := fun
      | false => seqMixed
      | true => behaviorToMixed βOpp
    seqGame.IsRealizationPlan false x ∧
      IsBehaviorStrategy β ∧
      seqGame.RealizationEquivMixedBehavior false seqMixed β ∧
      β false false = 1 / 2 ∧
      β true false = 1 / 3 ∧
      β true true = 2 / 3 ∧
      seqGame.evalBehavior profB false = 1 ∧
      seqGame.evalMixed profM false = 1 ∧
      (seqGame.behaviorToRealizationPlan false β ⬝ᵥ
        seqGame.seqPayoffMat false *ᵥ seqGame.behaviorToRealizationPlan true βOpp) = 1 ∧
      (x ⬝ᵥ seqGame.seqPayoffMat false *ᵥ seqGame.mixedToRealizationPlan true (profM true)) =
        1 ∧
      (∀ β' : ∀ h : seqH false, seqAct false h → ℝ,
        seqGame.behaviorToRealizationPlan false β' = x →
        β' false = β false ∧ β' true = β true) ∧
      Matrix.IsVertex (seqPolyMat seqGame false) (seqPolyRhs seqGame false)
        (seqGame.pureToRealizationPlan false fun _ => false) ∧
      ¬ Matrix.IsVertex (seqPolyMat seqGame false) (seqPolyRhs seqGame false) x := by
  intro x β βOpp profB profM
  have hk := kuhn_theorem seqGame_perfectRecall_false seqMixed_isMixed
  have hx : seqGame.IsRealizationPlan false x :=
    isRealizationPlan_mixedToRealizationPlan seqGame_perfectRecall_false seqMixed_isMixed
  have hv0 : (Node.here (T := seqGame)).IsDecisionOf false (false : Bool) := rfl
  have hinfo0 : seqGame.infoSeq false false = [] :=
    (seqGame_perfectRecall_false.playerSeq_eq_infoSeq hv0).symm
  have hv1 :
      (Node.decision (true : Bool) (Node.here (T := _)) : Node seqGame).IsDecisionOf false true :=
    rfl
  have hinfo1 : seqGame.infoSeq false true = [⟨false, true⟩] := by
    simpa [Node.playerSeq] using (seqGame_perfectRecall_false.playerSeq_eq_infoSeq hv1).symm
  have hnil : realizationProbMixed seqMixed [] = 1 :=
    realizationProbMixed_nil seqMixed_isMixed
  have hx1_val : realizationProbMixed seqMixed [⟨false, true⟩] = 1 / 2 := by
    rw [realizationProbMixed_def]
    change (∑ s : Bool → Bool, _) = 1 / 2
    rw [sum_bool_fun_cases]
    norm_num [seqMixed, MatchesSeq]
  have hx0f_val : realizationProbMixed seqMixed [⟨false, false⟩] = 1 / 2 := by
    rw [realizationProbMixed_def]
    change (∑ s : Bool → Bool, _) = 1 / 2
    rw [sum_bool_fun_cases]
    norm_num [seqMixed, MatchesSeq]
  have hx1f_val : realizationProbMixed seqMixed [⟨false, true⟩, ⟨true, false⟩] = 1 / 6 := by
    rw [realizationProbMixed_def]
    change (∑ s : Bool → Bool, _) = 1 / 6
    rw [sum_bool_fun_cases]
    norm_num [seqMixed, MatchesSeq]
  have hx1t_val : realizationProbMixed seqMixed [⟨false, true⟩, ⟨true, true⟩] = 1 / 3 := by
    rw [realizationProbMixed_def]
    change (∑ s : Bool → Bool, _) = 1 / 3
    rw [sum_bool_fun_cases]
    norm_num [seqMixed, MatchesSeq]
  have hh0 : seqGame.OccursInfoSet false false := ⟨_, hv0⟩
  have hh1 : seqGame.OccursInfoSet false true := ⟨_, hv1⟩
  have hpos0 : 0 < x (SeqVar.infoSeq seqGame_perfectRecall_false hh0) := by
    dsimp only [x]
    rw [ExtensiveTree.mixedToRealizationPlan_def, SeqVar.infoSeq_val, hinfo0, hnil]
    norm_num
  have hpos1 : 0 < x (SeqVar.infoSeq seqGame_perfectRecall_false hh1) := by
    dsimp only [x]
    rw [ExtensiveTree.mixedToRealizationPlan_def, SeqVar.infoSeq_val, hinfo1, hx1_val]
    norm_num
  have hβ0f : β false false = 1 / 2 := by
    dsimp only [β]
    rw [ExtensiveTree.realizationPlanToBehavior_eq_div seqGame_perfectRecall_false hh0 hpos0 false]
    simp only [x, ExtensiveTree.mixedToRealizationPlan_def, SeqVar.infoSeq_val,
      SeqVar.infoSeqExt_val, hinfo0, List.nil_append, hnil, hx0f_val]
    norm_num
  have hβ1f : β true false = 1 / 3 := by
    dsimp only [β]
    rw [ExtensiveTree.realizationPlanToBehavior_eq_div seqGame_perfectRecall_false hh1 hpos1 false]
    simp only [x, ExtensiveTree.mixedToRealizationPlan_def, SeqVar.infoSeq_val,
      SeqVar.infoSeqExt_val, hinfo1, List.cons_append, List.nil_append, hx1_val, hx1f_val]
    norm_num
  have hβ1t : β true true = 2 / 3 := by
    dsimp only [β]
    rw [ExtensiveTree.realizationPlanToBehavior_eq_div seqGame_perfectRecall_false hh1 hpos1 true]
    simp only [x, ExtensiveTree.mixedToRealizationPlan_def, SeqVar.infoSeq_val,
      SeqVar.infoSeqExt_val, hinfo1, List.cons_append, List.nil_append, hx1_val, hx1t_val]
    norm_num
  have hβ0t : β false true = 1 / 2 := by
    have hsum := (hk.1 false).sum_eq_one
    rw [Fintype.sum_bool] at hsum
    change β false true + β false false = 1 at hsum
    rw [hβ0f] at hsum
    linarith
  have hevalB : seqGame.evalBehavior profB false = 1 := by
    simp only [profB, ExtensiveTree.evalBehavior, Fintype.sum_bool]
    rw [hβ0f, hβ0t, hβ1f, hβ1t]
    norm_num [βOpp]
  have hevalM : seqGame.evalMixed profM false = 1 := by
    have hβOpp : IsBehaviorStrategy βOpp := fun _ => fairCoin_isMixed
    have hprofM : profM = Function.update
        (fun j : Bool => match j with
          | false => behaviorToMixed β
          | true => behaviorToMixed βOpp : ∀ j, PureStrategy seqH seqAct j → ℝ)
        false seqMixed := by
      ext i s
      cases i <;> simp [profM, Function.update]
    rw [hprofM, hk.2.2.evalMixed_eq _ false]
    have hother :
        (∑ z : Terminal seqGame,
          (z.chanceWeight * realizationProbBehavior β (z.seq false) *
            ∏ j ∈ univ.erase false,
              realizationProbMixed ((fun j : Bool => match j with
                | false => behaviorToMixed β
                | true => behaviorToMixed βOpp : ∀ j, PureStrategy seqH seqAct j → ℝ) j)
                (z.seq j)) * z.payoff false) =
          seqGame.evalBehavior profB false := by
      rw [seqGame.evalBehavior_eq_sum_terminal profB false]
      refine sum_congr rfl fun z _ => ?_
      rw [terminalProbBehavior_eq, ← mul_prod_erase univ _ (mem_univ false)]
      congr 1
      have herase : (univ.erase false : Finset Bool) = {true} := by decide
      rw [herase, prod_singleton, prod_singleton]
      have hnodup : ((z.seq true).map Sigma.fst).Nodup :=
        seqGame_perfectRecall_true.noRepeatedInfoSet z
      rw [realizationProbMixed_behaviorToMixed hβOpp hnodup]
      simp [profB]
      ring
    rw [hother, hevalB]
  have hbilinB :
      (seqGame.behaviorToRealizationPlan false β ⬝ᵥ
        seqGame.seqPayoffMat false *ᵥ seqGame.behaviorToRealizationPlan true βOpp) = 1 := by
    have hb := evalBehavior_eq_seqPayoffMat seqGame profB false
    change seqGame.evalBehavior profB false =
      seqGame.behaviorToRealizationPlan false β ⬝ᵥ
        seqGame.seqPayoffMat false *ᵥ seqGame.behaviorToRealizationPlan true βOpp at hb
    rw [hevalB] at hb
    exact hb.symm
  have hbilin :
      (x ⬝ᵥ seqGame.seqPayoffMat false *ᵥ seqGame.mixedToRealizationPlan true (profM true)) =
        1 := by
    have hm := evalMixed_eq_seqPayoffMat seqGame profM false
    have hmx0 : seqGame.mixedToRealizationPlan false (profM false) = x := by
      simp [profM, x]
    rw [hmx0, hevalM] at hm
    exact hm.symm
  have huniqB :
      ∀ β' : ∀ h : seqH false, seqAct false h → ℝ,
        seqGame.behaviorToRealizationPlan false β' = x →
        β' false = β false ∧ β' true = β true := fun β' hreal =>
    ⟨realizationPlanToBehavior_unique seqGame_perfectRecall_false hreal hh0 hpos0,
     realizationPlanToBehavior_unique seqGame_perfectRecall_false hreal hh1 hpos1⟩
  have hvtx_pure : Matrix.IsVertex (seqPolyMat seqGame false) (seqPolyRhs seqGame false)
      (seqGame.pureToRealizationPlan false fun _ => false) :=
    (isVertex_seqPolyMat_iff seqGame_perfectRecall_false _).2 ⟨fun _ => false, rfl⟩
  have hnot_vtx_x : ¬ Matrix.IsVertex (seqPolyMat seqGame false) (seqPolyRhs seqGame false) x := by
    intro hvtx
    obtain ⟨s, hs⟩ := (isVertex_seqPolyMat_iff seqGame_perfectRecall_false x).1 hvtx
    let σ1 : SeqVar seqGame false := SeqVar.infoSeqExt seqGame_perfectRecall_false hh0 true
    have hval := congrFun hs σ1
    have hlhs : x σ1 = 1 / 2 := by
      dsimp only [x]
      rw [ExtensiveTree.mixedToRealizationPlan_def, SeqVar.infoSeqExt_val, hinfo0, List.nil_append,
        hx1_val]
    rw [ExtensiveTree.pureToRealizationPlan_def, SeqVar.infoSeqExt_val, hinfo0,
      List.nil_append, hlhs] at hval
    split_ifs at hval <;> norm_num at hval
  refine ⟨hx, hk.1, hk.2.2, hβ0f, hβ1f, hβ1t, hevalB, hevalM, hbilinB, hbilin, huniqB,
    hvtx_pure, hnot_vtx_x⟩

/-! ### 4. Imperfect-recall counterexample to Kuhn's theorem -/

/-- Information sets for `forgetfulGame`. -/
abbrev forgetfulH : Unit → Type := fun _ => Bool

/-- Actions for `forgetfulGame`. -/
abbrev forgetfulAct : ∀ i : Unit, forgetfulH i → Type := fun _ _ => Bool

/-- Classic one-player imperfect-recall counterexample to Kuhn's theorem: at root information set
`false` the player picks `false`/`true`, then at second information set `true` forgets the first
choice and picks `false`/`true`. Payoff is `1` when the two choices agree and `0` otherwise. -/
abbrev forgetfulGame : ExtensiveTree Unit forgetfulH forgetfulAct :=
  .decision () false fun a₀ =>
    .decision () true fun a₁ =>
      .leaf fun _ => if a₀ == a₁ then 1 else 0

theorem forgetfulGame_not_perfectRecall : ¬ forgetfulGame.PerfectRecall () := by
  intro hpr
  have hv₁ : (Node.decision false (Node.here (T := _)) : Node forgetfulGame).IsDecisionOf () true :=
    rfl
  have hv₂ : (Node.decision true (Node.here (T := _)) : Node forgetfulGame).IsDecisionOf () true :=
    rfl
  have heq := hpr hv₁ hv₂
  simp [Node.playerSeq] at heq

theorem forgetfulGame_noRepeatedInfoSet : forgetfulGame.NoRepeatedInfoSet () := by
  intro z
  rcases z with _ | ⟨⟩ | ⟨a₀, sub⟩
  rcases sub with _ | ⟨⟩ | ⟨a₁, leaf⟩
  cases leaf
  simp

/-- Mixed strategy `½(false, false) + ½(true, true)` in `forgetfulGame`. -/
noncomputable def forgetfulMixed : PureStrategy forgetfulH forgetfulAct () → ℝ :=
  fun s => if s false == s true then 1 / 2 else 0

theorem forgetfulMixed_isMixed : IsMixedStrategy forgetfulMixed := by
  refine isMixedStrategy_iff.2 ⟨fun s => ?_, ?_⟩
  · dsimp [forgetfulMixed]
    split_ifs <;> norm_num
  · change (∑ s : Bool → Bool, forgetfulMixed s) = 1
    rw [sum_bool_fun_cases]
    norm_num [forgetfulMixed]

/-- Perfect recall cannot be dropped in Kuhn's theorem: no behavior strategy is
realization-equivalent to `forgetfulMixed` in `forgetfulGame`. -/
theorem forgetfulGame_no_realizationEquiv_behavior :
    ¬ ∃ β : ∀ h : forgetfulH (), forgetfulAct () h → ℝ,
      IsBehaviorStrategy β ∧ forgetfulGame.RealizationEquivMixedBehavior () forgetfulMixed β := by
  rintro ⟨β, _, heq⟩
  let s₀ : ∀ _ : Unit, PureStrategy forgetfulH forgetfulAct () := fun _ _ => false
  let zff : Terminal forgetfulGame := .decision false (.decision false .leaf)
  let zft : Terminal forgetfulGame := .decision false (.decision true .leaf)
  let ztf : Terminal forgetfulGame := .decision true (.decision false .leaf)
  let ztt : Terminal forgetfulGame := .decision true (.decision true .leaf)
  have eq_of_z : ∀ z : Terminal forgetfulGame,
      realizationProbMixed forgetfulMixed (z.seq ()) = realizationProbBehavior β (z.seq ()) := by
    intro z
    have h := heq s₀ z
    rw [terminalProbWithFactor_def, terminalProbWithFactor_def] at h
    have hcw : z.chanceWeight = 1 := by
      rcases z with _ | ⟨⟩ | ⟨a₀, sub⟩
      rcases sub with _ | ⟨⟩ | ⟨a₁, leaf⟩
      cases leaf
      rfl
    have herase : (univ.erase () : Finset Unit) = ∅ := by decide
    simp only [hcw, one_mul, herase, Finset.prod_empty, mul_one] at h
    exact h
  have hff : (1 / 2 : ℝ) = β false false * β true false := by
    have h := eq_of_z zff
    rw [realizationProbMixed_def] at h
    change (∑ s : Bool → Bool, _) = _ at h
    rw [sum_bool_fun_cases] at h
    simp only [zff, Terminal.seq_decision_self, Terminal.seq_leaf] at h
    simp only [realizationProbBehavior_cons, realizationProbBehavior_nil, mul_one,
      forgetfulMixed] at h
    norm_num at h
    exact h
  have hft : (0 : ℝ) = β false false * β true true := by
    have h := eq_of_z zft
    rw [realizationProbMixed_def] at h
    change (∑ s : Bool → Bool, _) = _ at h
    rw [sum_bool_fun_cases] at h
    simp only [zft, Terminal.seq_decision_self, Terminal.seq_leaf] at h
    simp only [realizationProbBehavior_cons, realizationProbBehavior_nil, mul_one,
      forgetfulMixed] at h
    norm_num at h
    rcases h with h0 | h0 <;> simp [h0]
  have htf : (0 : ℝ) = β false true * β true false := by
    have h := eq_of_z ztf
    rw [realizationProbMixed_def] at h
    change (∑ s : Bool → Bool, _) = _ at h
    rw [sum_bool_fun_cases] at h
    simp only [ztf, Terminal.seq_decision_self, Terminal.seq_leaf] at h
    simp only [realizationProbBehavior_cons, realizationProbBehavior_nil, mul_one,
      forgetfulMixed] at h
    norm_num at h
    rcases h with h0 | h0 <;> simp [h0]
  have htt : (1 / 2 : ℝ) = β false true * β true true := by
    have h := eq_of_z ztt
    rw [realizationProbMixed_def] at h
    change (∑ s : Bool → Bool, _) = _ at h
    rw [sum_bool_fun_cases] at h
    simp only [ztt, Terminal.seq_decision_self, Terminal.seq_leaf] at h
    simp only [realizationProbBehavior_cons, realizationProbBehavior_nil, mul_one,
      forgetfulMixed] at h
    norm_num at h
    exact h
  have hcontra : (1 / 4 : ℝ) = 0 := by
    calc (1 / 4 : ℝ) = (1 / 2) * (1 / 2) := by norm_num
      _ = (β false false * β true false) * (β false true * β true true) := by rw [← hff, ← htt]
      _ = (β false false * β true true) * (β false true * β true false) := by ring
      _ = 0 * 0 := by rw [← hft, ← htf]
      _ = 0 := by norm_num
  norm_num at hcontra

end CslibFrontierTests.GameTheory.Extensive
