/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.GameTheory.Extensive.ZeroSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Checked tests for zero-sum extensive-form games, sequence form minimax, and subgame perfection

Non-vacuous checked examples exercising `CslibFrontier.GameTheory.Extensive.ZeroSum`
([vonStengel1996], §3; [vonStengel2007], Chapter 3):

* **Witness 1 — Full 3-card Kuhn poker (`kuhnGame`)**: 6 uniform chance deals over `(J, Q, K)`
  with 30 terminal leaves (`Fintype.card (Terminal kuhnGame) = 30`), contrasting the linear
  `≤ 30` sparse support bound of `seqPayoffMat` (`card_support_seqPayoffMat_le_card_terminal`)
  against `64 × 64 = 4096` normal-form pure strategy pairs. Certifies `kuhnGame_perfectRecall`,
  `kuhnGame_isZeroSum`, and two distinct minimax behavioral equilibria (`α = 0` and `α = 1 / 3`
  for player `false`) via `isBehaviorNash_of_saddle`, establishing exact game value `-1 / 18`,
  `IsBehaviorNash`, `IsSeqNash`, `isBehaviorNash_iff_maximin_minimax`,
  `isSeqNash_iff_maximin_minimax`, and `seq_iSup_iInf_eq_iInf_iSup = -1 / 18`.
* **Witness 2 — Zero-sum perfect-information tree with chance & off-path non-SPE Nash
  (`zeroPerfectTree`)**: verifies `PerfectInfoTree.IsZeroSum`, `isPureSPE_iff_isBehaviorSPE`,
  `backwardInduction_isBehaviorSPE`, `backwardInduction_isSeqNash`,
  `backwardInduction_payoff_eq_seq_minimax` (value `2`),
  `isPureNash_expectedPayoff_eq_backwardInduction`,
  `isMixedNash_expectedPayoff_eq_backwardInduction`, and a non-credible off-path behavioral Nash
  equilibrium with the same minimax payoff `2` that fails `IsBehaviorSPE` and `IsPureSPE`.
* **Witness 3 — Deterministic (`HasNoChance`) sequential asymmetric matching pennies
  (`detSeqMP`)**: exercises `HasNoChance.leafSeqPair_injective`,
  `HasNoChance.seqPayoffMat_leafSeqPair` at concrete terminal leaves,
  `card_support_seqPayoffMat_le_card_terminal (≤ 5)`, sparse-support and leaf-sum bilinear
  evaluation (`dotProduct_seqPayoffMat_mulVec_eq_sum_support`,
  `dotProduct_seqPayoffMat_mulVec_eq_sum_terminal`), and equality of mixed, behavioral, and
  sequence-form minimax values (`1 / 3`) via `mixed_minimax_eq_behavior_minimax` and
  `mixed_iSup_iInf_eq_iInf_iSup`.
* **Witness 4 — Full two-player equilibrium interchangeability (`biGame`)**: `3 × 3` zero-sum
  extensive game with strictly dominated actions (`a = 2`) and two equilibria `(0, 0)` and `(1, 1)`
  differing in **both** players (`β₁ false ≠ β₂ false` and `β₁ true ≠ β₂ true`), exercising
  `IsBehaviorNash.interchange` and `IsSeqNash.interchange`.
-/

@[expose] public section

namespace CslibFrontierTests.GameTheory.ExtensiveZeroSum

open Cslib.GameTheory Cslib.GameTheory.Extensive Finset Matrix

/-- Helper constructor for zero-sum leaf payoff vectors `false ↦ v`, `true ↦ -v`. -/
@[reducible] def zsPayoff (v : ℝ) : Bool → ℝ
  | false => v
  | true => -v

/-! ### 1. Full 3-Card Kuhn Poker (`-1 / 18` minimax value & equilibrium family) -/

/-- Six equally likely ordered deals of `(J = 0, Q = 1, K = 2)`. -/
@[reducible] def kuhnCard₀ : Fin 6 → Fin 3
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2

/-- Second player's card for each of the six deals in `kuhnCard₀`. -/
@[reducible] def kuhnCard₁ : Fin 6 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 2
  | 4 => 0
  | 5 => 1

theorem uniformSix_isMixed : IsMixedStrategy (fun _ : Fin 6 => (1 / 6 : ℝ)) :=
  isMixedStrategy_iff.2 ⟨fun _ => by norm_num, by norm_num⟩

theorem fairCoin_isMixed : IsMixedStrategy (fun _ : Bool => (1 / 2 : ℝ)) :=
  isMixedStrategy_iff.2 ⟨fun _ => by norm_num, by norm_num⟩

/-- Kuhn poker information sets: for player `false`, `(card, afterCheckBet)`; for player `true`,
`(card, afterBet)` where `false` means facing a check and `true` means facing a bet. -/
@[reducible] def kuhnH : Bool → Type := fun _ => Fin 3 × Bool

/-- Two actions (`false = Check/Fold`, `true = Bet/Call`) at every information set. -/
@[reducible] def kuhnAct : ∀ i, kuhnH i → Type := fun _ _ => Bool

/-- Showdown payoff with pot size `pot` (`1` after Check–Check, `2` after a called Bet). -/
@[reducible] def kuhnShowdown (c₀ c₁ : Fin 3) (pot : ℝ) : Bool → ℝ :=
  zsPayoff (if c₁ < c₀ then pot else -pot)

/-- Subtree of 3-card Kuhn poker after dealing card `c₀` to player `false` and `c₁` to `true`. -/
@[reducible] noncomputable def kuhnDealTree (c₀ c₁ : Fin 3) : ExtensiveTree Bool kuhnH kuhnAct :=
  .decision false (c₀, false) fun
    | false => .decision true (c₁, false) fun
      | false => .leaf (kuhnShowdown c₀ c₁ 1)
      | true => .decision false (c₀, true) fun
        | false => .leaf (zsPayoff (-1))
        | true => .leaf (kuhnShowdown c₀ c₁ 2)
    | true => .decision true (c₁, true) fun
      | false => .leaf (zsPayoff 1)
      | true => .leaf (kuhnShowdown c₀ c₁ 2)

/-- Full 3-card Kuhn poker extensive-form game with 6 uniform deals and 30 terminal leaves. -/
@[reducible] noncomputable def kuhnGame : ExtensiveTree Bool kuhnH kuhnAct :=
  .chance (fun _ : Fin 6 => (1 / 6 : ℝ)) uniformSix_isMixed fun d =>
    kuhnDealTree (kuhnCard₀ d) (kuhnCard₁ d)

theorem kuhnGame_isZeroSum : kuhnGame.IsZeroSum := by
  intro z
  cases z with
  | chance _ sub =>
    cases sub with
    | decision a₀ sub₁ =>
      cases a₀ with
      | false =>
        cases sub₁ with
        | decision a₁ sub₂ =>
          cases a₁ with
          | false => cases sub₂; simp [kuhnShowdown, zsPayoff]
          | true =>
            cases sub₂ with
            | decision a₂ sub₃ => cases a₂ <;> (cases sub₃; simp [kuhnShowdown, zsPayoff])
      | true =>
        cases sub₁ with
        | decision a₁ sub₂ => cases a₁ <;> (cases sub₂; simp [kuhnShowdown, zsPayoff])

private theorem kuhnDealTree_playerSeq_false (c₀ c₁ c : Fin 3) (b : Bool)
    {v : Node (kuhnDealTree c₀ c₁)} (hv : v.IsDecisionOf false (c, b)) :
    v.playerSeq false = if b then [⟨(c, false), false⟩] else [] := by
  cases v with
  | here =>
    have hh : ((c₀, false) : Fin 3 × Bool) = (c, b) :=
      eq_of_heq (Sigma.mk.inj_iff.1 hv).2
    cases (Prod.ext_iff.1 hh).2
    rfl
  | decision a₀ sub₁ =>
    cases a₀ with
    | false =>
      cases sub₁ with
      | here => exact absurd hv (by simp)
      | decision a₁ sub₂ =>
        cases a₁ with
        | false => cases sub₂; exact absurd hv (by simp)
        | true =>
          cases sub₂ with
          | here =>
            have hh : ((c₀, true) : Fin 3 × Bool) = (c, b) :=
              eq_of_heq (Sigma.mk.inj_iff.1 hv).2
            obtain ⟨hc, hb⟩ := Prod.ext_iff.1 hh
            subst hc hb
            rfl
          | decision a₂ sub₃ =>
            cases a₂ <;> (cases sub₃; exact absurd hv (by simp))
    | true =>
      cases sub₁ with
      | here => exact absurd hv (by simp)
      | decision a₁ sub₂ =>
        cases a₁ <;> (cases sub₂; exact absurd hv (by simp))

private theorem kuhnDealTree_playerSeq_true (c₀ c₁ c : Fin 3) (b : Bool)
    {v : Node (kuhnDealTree c₀ c₁)} (hv : v.IsDecisionOf true (c, b)) :
    v.playerSeq true = [] := by
  cases v with
  | here => exact absurd hv (by simp)
  | decision a₀ sub₁ =>
    cases a₀ with
    | false =>
      cases sub₁ with
      | here => rfl
      | decision a₁ sub₂ =>
        cases a₁ with
        | false => cases sub₂; exact absurd hv (by simp)
        | true =>
          cases sub₂ with
          | here => exact absurd hv (by simp)
          | decision a₂ sub₃ =>
            cases a₂ <;> (cases sub₃; exact absurd hv (by simp))
    | true =>
      cases sub₁ with
      | here => rfl
      | decision a₁ sub₂ =>
        cases a₁ <;> (cases sub₂; exact absurd hv (by simp))

theorem kuhnGame_perfectRecall (i : Bool) : kuhnGame.PerfectRecall i := by
  intro h v₁ v₂ hv₁ hv₂
  rcases h with ⟨c, b⟩
  cases i with
  | false =>
    cases v₁ with
    | here => exact absurd hv₁ (by simp)
    | chance d₁ sub₁ =>
      cases v₂ with
      | here => exact absurd hv₂ (by simp)
      | chance d₂ sub₂ =>
        rw [Node.playerSeq_chance, Node.playerSeq_chance,
          kuhnDealTree_playerSeq_false (kuhnCard₀ d₁) (kuhnCard₁ d₁) c b hv₁,
          kuhnDealTree_playerSeq_false (kuhnCard₀ d₂) (kuhnCard₁ d₂) c b hv₂]
  | true =>
    cases v₁ with
    | here => exact absurd hv₁ (by simp)
    | chance d₁ sub₁ =>
      cases v₂ with
      | here => exact absurd hv₂ (by simp)
      | chance d₂ sub₂ =>
        rw [Node.playerSeq_chance, Node.playerSeq_chance,
          kuhnDealTree_playerSeq_true (kuhnCard₀ d₁) (kuhnCard₁ d₁) c b hv₁,
          kuhnDealTree_playerSeq_true (kuhnCard₀ d₂) (kuhnCard₁ d₂) c b hv₂]

private noncomputable def kuhnTermEquiv : Fin 6 × Fin 5 ≃ Terminal kuhnGame where
  toFun p := .chance p.1 <| match p.2 with
    | 0 => .decision false (.decision false .leaf)
    | 1 => .decision false (.decision true (.decision false .leaf))
    | 2 => .decision false (.decision true (.decision true .leaf))
    | 3 => .decision true (.decision false .leaf)
    | 4 => .decision true (.decision true .leaf)
  invFun z := match z with
    | .chance d (.decision false (.decision false .leaf)) => (d, 0)
    | .chance d (.decision false (.decision true (.decision false .leaf))) => (d, 1)
    | .chance d (.decision false (.decision true (.decision true .leaf))) => (d, 2)
    | .chance d (.decision true (.decision false .leaf)) => (d, 3)
    | .chance d (.decision true (.decision true .leaf)) => (d, 4)
  left_inv p := by
    rcases p with ⟨d, k⟩
    fin_cases k <;> rfl
  right_inv z := by
    cases z with
    | chance d sub =>
      cases sub with
      | decision a₀ sub₁ =>
        cases a₀ with
        | false =>
          cases sub₁ with
          | decision a₁ sub₂ =>
            cases a₁ with
            | false => cases sub₂; rfl
            | true =>
              cases sub₂ with
              | decision a₂ sub₃ => cases a₂ <;> cases sub₃ <;> rfl
        | true =>
          cases sub₁ with
          | decision a₁ sub₂ => cases a₁ <;> cases sub₂ <;> rfl

open Classical in
/-- Kuhn poker has 30 terminal leaves (`Fintype.card (Terminal kuhnGame) = 30`), so the
sequence-form payoff matrix `kuhnGame.seqPayoffMat false` has at most 30 nonzero entries (compared
to `64 × 64 = 4096` entries in normal form). -/
theorem kuhnGame_card_support_le_30 :
    Fintype.card (Terminal kuhnGame) = 30 ∧
      (univ.filter (fun e : SeqVar kuhnGame false × SeqVar kuhnGame true =>
          kuhnGame.seqPayoffMat false e.1 e.2 ≠ 0)).card ≤ 30 := by
  have hcard : Fintype.card (Terminal kuhnGame) = 30 := by
    rw [← Fintype.card_congr kuhnTermEquiv]
    decide
  exact ⟨hcard, (card_support_seqPayoffMat_le_card_terminal kuhnGame false).trans_eq hcard⟩

/-- Deal-wise expected payoff to player `false` in `kuhnDealTree c₀ c₁`. -/
@[reducible] noncomputable def kuhnDealPayoff (β : ∀ i, ∀ h : kuhnH i, kuhnAct i h → ℝ)
    (c₀ c₁ : Fin 3) : ℝ :=
  let s := if c₁ < c₀ then (1 : ℝ) else (-1 : ℝ)
  β false (c₀, false) false *
      (β true (c₁, false) false * s +
        β true (c₁, false) true *
          (β false (c₀, true) false * (-1) + β false (c₀, true) true * (2 * s))) +
    β false (c₀, false) true *
      (β true (c₁, true) false * 1 + β true (c₁, true) true * (2 * s))

private theorem kuhnDealTree_evalBehavior_false (β : ∀ i, ∀ h : kuhnH i, kuhnAct i h → ℝ)
    (c₀ c₁ : Fin 3) :
    (kuhnDealTree c₀ c₁).evalBehavior β false = kuhnDealPayoff β c₀ c₁ := by
  simp only [kuhnDealTree, ExtensiveTree.evalBehavior_decision, ExtensiveTree.evalBehavior_leaf,
    Fintype.sum_bool, kuhnShowdown, zsPayoff, kuhnDealPayoff]
  split_ifs <;> ring

private theorem kuhnGame_evalBehavior_false (β : ∀ i, ∀ h : kuhnH i, kuhnAct i h → ℝ) :
    kuhnGame.evalBehavior β false =
      (1 / 6 : ℝ) *
        (kuhnDealPayoff β 0 1 + kuhnDealPayoff β 0 2 +
         kuhnDealPayoff β 1 0 + kuhnDealPayoff β 1 2 +
         kuhnDealPayoff β 2 0 + kuhnDealPayoff β 2 1) := by
  simp only [kuhnGame, ExtensiveTree.evalBehavior_chance, Fin.sum_univ_six, kuhnCard₀, kuhnCard₁,
    kuhnDealTree_evalBehavior_false]
  ring

/-- Player `false`'s parameterized family of minimax behavioral strategies (`0 ≤ α ≤ 1 / 3`) in
3-card Kuhn poker. -/
@[reducible] noncomputable def kuhnOptFalse (α : ℝ) :
    ∀ h : kuhnH false, kuhnAct false h → ℝ
  | (0, false), a => if a then α else 1 - α
  | (0, true), a => if a then 0 else 1
  | (1, false), a => if a then 0 else 1
  | (1, true), a => if a then α + 1 / 3 else 2 / 3 - α
  | (2, false), a => if a then 3 * α else 1 - 3 * α
  | (2, true), a => if a then 1 else 0

/-- Player `true`'s unique minimax behavioral strategy in 3-card Kuhn poker. -/
@[reducible] noncomputable def kuhnOptTrue : ∀ h : kuhnH true, kuhnAct true h → ℝ
  | (0, false), a => if a then 1 / 3 else 2 / 3
  | (0, true), a => if a then 0 else 1
  | (1, false), a => if a then 0 else 1
  | (1, true), a => if a then 1 / 3 else 2 / 3
  | (2, false), a => if a then 1 else 0
  | (2, true), a => if a then 1 else 0

/-- Combined behavioral strategy profile `(kuhnOptFalse α, kuhnOptTrue)` for Kuhn poker. -/
@[reducible] noncomputable def kuhnOptProfile (α : ℝ) :
    ∀ i, ∀ h : kuhnH i, kuhnAct i h → ℝ
  | false => kuhnOptFalse α
  | true => kuhnOptTrue

private theorem kuhnOptFalse_isBehavior {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 3) :
    IsBehaviorStrategy (kuhnOptFalse α) := by
  rintro ⟨c, b⟩
  refine isMixedStrategy_iff.2 ⟨fun a => ?_, ?_⟩
  · fin_cases c <;> cases b <;> cases a <;> simp [kuhnOptFalse] <;> linarith
  · (fin_cases c <;> cases b <;> simp [kuhnOptFalse]); ring

private theorem kuhnOptTrue_isBehavior : IsBehaviorStrategy kuhnOptTrue := by
  rintro ⟨c, b⟩
  refine isMixedStrategy_iff.2 ⟨fun a => ?_, ?_⟩
  · fin_cases c <;> cases b <;> cases a <;> simp [kuhnOptTrue] <;> norm_num
  · fin_cases c <;> cases b <;> simp [kuhnOptTrue] <;> norm_num

private theorem kuhn_bool_coords {i : Bool} {β : ∀ h : kuhnH i, kuhnAct i h → ℝ}
    (hβ : IsBehaviorStrategy β) (c : Fin 3) (b : Bool) :
    β (c, b) false + β (c, b) true = 1 ∧ 0 ≤ β (c, b) false ∧ β (c, b) false ≤ 1 ∧
      0 ≤ β (c, b) true ∧ β (c, b) true ≤ 1 := by
  have hsum : β (c, b) false + β (c, b) true = 1 := by
    simpa [Fintype.sum_bool, add_comm] using (hβ (c, b)).sum_eq_one
  have hnf := (hβ (c, b)).nonneg false
  have hnt := (hβ (c, b)).nonneg true
  exact ⟨hsum, hnf, by linarith, hnt, by linarith⟩

private theorem kuhnOptTrue_upper_bound (β₀ : ∀ h : kuhnH false, kuhnAct false h → ℝ)
    (hβ₀ : IsBehaviorStrategy β₀) :
    kuhnGame.evalBehavior (fun | false => β₀ | true => kuhnOptTrue) false ≤ -(1 / 18 : ℝ) := by
  rw [kuhnGame_evalBehavior_false]
  obtain ⟨hs00, _, _, _, hp0_le⟩ := kuhn_bool_coords hβ₀ 0 false
  obtain ⟨hs01, _, _, hq0_nn, _⟩ := kuhn_bool_coords hβ₀ 0 true
  obtain ⟨hs10, _, _, hp1_nn, _⟩ := kuhn_bool_coords hβ₀ 1 false
  obtain ⟨hs11, _⟩ := kuhn_bool_coords hβ₀ 1 true
  obtain ⟨hs20, _, _, _, hp2_le⟩ := kuhn_bool_coords hβ₀ 2 false
  obtain ⟨hs21, _, _, _, hq2_le⟩ := kuhn_bool_coords hβ₀ 2 true
  set p0 := β₀ (0, false) true
  set q0 := β₀ (0, true) true
  set p1 := β₀ (1, false) true
  set q1 := β₀ (1, true) true
  set p2 := β₀ (2, false) true
  set q2 := β₀ (2, true) true
  have hc0f : β₀ (0, false) false = 1 - p0 := by linarith
  have hc0t : β₀ (0, true) false = 1 - q0 := by linarith
  have hc1f : β₀ (1, false) false = 1 - p1 := by linarith
  have hc1t : β₀ (1, true) false = 1 - q1 := by linarith
  have hc2f : β₀ (2, false) false = 1 - p2 := by linarith
  have hc2t : β₀ (2, true) false = 1 - q2 := by linarith
  dsimp only [kuhnDealPayoff, kuhnOptTrue]
  simp only [hc0f, hc0t, hc1f, hc1t, hc2f, hc2t, ite_true]
  norm_num
  have h1 : 0 ≤ (1 - p0) * q0 := mul_nonneg (sub_nonneg.2 hp0_le) hq0_nn
  have h2 : 0 ≤ (1 - p2) * (1 - q2) := mul_nonneg (sub_nonneg.2 hp2_le) (sub_nonneg.2 hq2_le)
  linarith

private theorem kuhnOptFalse_lower_bound {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 3)
    (β₁ : ∀ h : kuhnH true, kuhnAct true h → ℝ) (hβ₁ : IsBehaviorStrategy β₁) :
    -(1 / 18 : ℝ) ≤
      kuhnGame.evalBehavior (fun | false => kuhnOptFalse α | true => β₁) false := by
  rw [kuhnGame_evalBehavior_false]
  obtain ⟨hs00, _⟩ := kuhn_bool_coords hβ₁ 0 false
  obtain ⟨hs01, _, _, hq0_nn, _⟩ := kuhn_bool_coords hβ₁ 0 true
  obtain ⟨hs10, _, _, hr1_nn, _⟩ := kuhn_bool_coords hβ₁ 1 false
  obtain ⟨hs11, _⟩ := kuhn_bool_coords hβ₁ 1 true
  obtain ⟨hs20, _, _, _, hr2_le⟩ := kuhn_bool_coords hβ₁ 2 false
  obtain ⟨hs21, _, _, _, hq2_le⟩ := kuhn_bool_coords hβ₁ 2 true
  set r0 := β₁ (0, false) true
  set q0 := β₁ (0, true) true
  set r1 := β₁ (1, false) true
  set q1 := β₁ (1, true) true
  set r2 := β₁ (2, false) true
  set q2 := β₁ (2, true) true
  have hc0f : β₁ (0, false) false = 1 - r0 := by linarith
  have hc0t : β₁ (0, true) false = 1 - q0 := by linarith
  have hc1f : β₁ (1, false) false = 1 - r1 := by linarith
  have hc1t : β₁ (1, true) false = 1 - q1 := by linarith
  have hc2f : β₁ (2, false) false = 1 - r2 := by linarith
  have hc2t : β₁ (2, true) false = 1 - q2 := by linarith
  dsimp only [kuhnDealPayoff, kuhnOptFalse]
  simp only [hc0f, hc0t, hc1f, hc1t, hc2f, hc2t, ite_true]
  norm_num
  have ha0 : 0 ≤ α * q0 := mul_nonneg h0 hq0_nn
  have ha1 : 0 ≤ (1 - 3 * α) * r1 := mul_nonneg (by linarith) hr1_nn
  have ha2 : 0 ≤ (1 / 3 + α) * (1 - r2) := mul_nonneg (by linarith) (by linarith)
  have ha3 : 0 ≤ α * (1 - q2) := mul_nonneg h0 (by linarith)
  linarith

private theorem kuhnOptProfile_saddle {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 3) :
    kuhnGame.IsBehaviorNash (kuhnOptProfile α) ∧
      kuhnGame.IsSeqNash (kuhnGame.behaviorToRealizationPlan false (kuhnOptFalse α))
        (kuhnGame.behaviorToRealizationPlan true kuhnOptTrue) ∧
      kuhnGame.evalBehavior (kuhnOptProfile α) false = -(1 / 18 : ℝ) ∧
      (⨆ β₀ : {β₀ : ∀ h : kuhnH false, kuhnAct false h → ℝ // IsBehaviorStrategy β₀},
        kuhnGame.behaviorLowerVal β₀.val) = -(1 / 18 : ℝ) ∧
      (⨆ x : {x : SeqVar kuhnGame false → ℝ // kuhnGame.IsRealizationPlan false x},
        kuhnGame.seqLowerVal x.val) = -(1 / 18 : ℝ) := by
  have hbeh : ∀ i, IsBehaviorStrategy (kuhnOptProfile α i) := fun
    | false => kuhnOptFalse_isBehavior h0 h1
    | true => kuhnOptTrue_isBehavior
  exact kuhnGame_isZeroSum.isBehaviorNash_of_saddle kuhnGame_perfectRecall (-(1 / 18 : ℝ))
    hbeh kuhnOptTrue_upper_bound (kuhnOptFalse_lower_bound h0 h1)

open Classical in
/-- Full 3-card Kuhn poker minimax certification:
* both `kuhnOptProfile 0` (`α = 0`) and `kuhnOptProfile (1 / 3)` (`α = 1 / 3`) are distinct
  behavioral and sequence-form Nash equilibria with exact minimax value `-1 / 18`;
* `isBehaviorNash_iff_maximin_minimax` and `isSeqNash_iff_maximin_minimax` certify maximin/minimax
  extremality (`IsGreatest` / `IsLeast`) in both behavioral and sequence form;
* `seq_iSup_iInf_eq_iInf_iSup`, `behavior_iSup_iInf_eq_iInf_iSup`, and `seqLowerVal` /
  `behaviorLowerVal` all agree on `-1 / 18`;
* equilibrium interchangeability (`IsBehaviorNash.interchange`) preserves both `IsBehaviorNash`
  and the value `-1 / 18`. -/
theorem kuhnGame_minimax_and_equilibria :
    kuhnGame.IsBehaviorNash (kuhnOptProfile 0) ∧
      kuhnGame.IsBehaviorNash (kuhnOptProfile (1 / 3)) ∧
      kuhnOptProfile 0 ≠ kuhnOptProfile (1 / 3) ∧
      kuhnGame.IsSeqNash (kuhnGame.behaviorToRealizationPlan false (kuhnOptFalse 0))
        (kuhnGame.behaviorToRealizationPlan true kuhnOptTrue) ∧
      kuhnGame.IsSeqNash (kuhnGame.behaviorToRealizationPlan false (kuhnOptFalse (1 / 3)))
        (kuhnGame.behaviorToRealizationPlan true kuhnOptTrue) ∧
      IsGreatest (kuhnGame.behaviorLowerVal '' {β₀ | IsBehaviorStrategy β₀})
        (kuhnGame.behaviorLowerVal (kuhnOptFalse 0)) ∧
      IsLeast (kuhnGame.behaviorUpperVal '' {β₁ | IsBehaviorStrategy β₁})
        (kuhnGame.behaviorUpperVal kuhnOptTrue) ∧
      IsGreatest (kuhnGame.seqLowerVal '' {x' | kuhnGame.IsRealizationPlan false x'})
        (kuhnGame.seqLowerVal (kuhnGame.behaviorToRealizationPlan false (kuhnOptFalse 0))) ∧
      IsLeast (kuhnGame.seqUpperVal '' {y' | kuhnGame.IsRealizationPlan true y'})
        (kuhnGame.seqUpperVal (kuhnGame.behaviorToRealizationPlan true kuhnOptTrue)) ∧
      kuhnGame.evalBehavior (kuhnOptProfile 0) false = -(1 / 18 : ℝ) ∧
      kuhnGame.evalBehavior (kuhnOptProfile (1 / 3)) false = -(1 / 18 : ℝ) ∧
      (⨆ x : {x : SeqVar kuhnGame false → ℝ // kuhnGame.IsRealizationPlan false x},
          ⨅ y : {y : SeqVar kuhnGame true → ℝ // kuhnGame.IsRealizationPlan true y},
            x.val ⬝ᵥ (kuhnGame.seqPayoffMat false *ᵥ y.val)) = -(1 / 18 : ℝ) ∧
      (⨅ y : {y : SeqVar kuhnGame true → ℝ // kuhnGame.IsRealizationPlan true y},
          ⨆ x : {x : SeqVar kuhnGame false → ℝ // kuhnGame.IsRealizationPlan false x},
            x.val ⬝ᵥ (kuhnGame.seqPayoffMat false *ᵥ y.val)) = -(1 / 18 : ℝ) ∧
      kuhnGame.IsBehaviorNash
        (fun | false => kuhnOptProfile (1 / 3) false | true => kuhnOptProfile 0 true) ∧
      kuhnGame.evalBehavior
        (fun | false => kuhnOptProfile (1 / 3) false | true => kuhnOptProfile 0 true) false =
          -(1 / 18 : ℝ) := by
  obtain ⟨hn0, hs0, hev0, _, hseq_mm⟩ :=
    kuhnOptProfile_saddle (α := (0 : ℝ)) le_rfl (by norm_num)
  obtain ⟨hn1, hs1, hev1, _, _⟩ :=
    kuhnOptProfile_saddle (α := (1 / 3 : ℝ)) (by norm_num) le_rfl
  obtain ⟨⟨_, hb_max⟩, ⟨_, hb_min⟩⟩ :=
    (kuhnGame_isZeroSum.isBehaviorNash_iff_maximin_minimax
      kuhnGame_perfectRecall (kuhnOptProfile 0)).1 hn0
  obtain ⟨⟨_, hs_max⟩, ⟨_, hs_min⟩⟩ :=
    (kuhnGame_isZeroSum.isSeqNash_iff_maximin_minimax kuhnGame_perfectRecall _ _).1 hs0
  have hne : kuhnOptProfile 0 ≠ kuhnOptProfile (1 / 3) := by
    intro heq
    have h0 := congrFun (congrFun (congrFun heq false) (0, false)) true
    norm_num [kuhnOptProfile, kuhnOptFalse] at h0
  have hsup_eq :
      (⨆ x : {x : SeqVar kuhnGame false → ℝ // kuhnGame.IsRealizationPlan false x},
          ⨅ y : {y : SeqVar kuhnGame true → ℝ // kuhnGame.IsRealizationPlan true y},
            x.val ⬝ᵥ (kuhnGame.seqPayoffMat false *ᵥ y.val)) = -(1 / 18 : ℝ) :=
    hseq_mm
  have hinf_eq :
      (⨅ y : {y : SeqVar kuhnGame true → ℝ // kuhnGame.IsRealizationPlan true y},
          ⨆ x : {x : SeqVar kuhnGame false → ℝ // kuhnGame.IsRealizationPlan false x},
            x.val ⬝ᵥ (kuhnGame.seqPayoffMat false *ᵥ y.val)) = -(1 / 18 : ℝ) :=
    (kuhnGame_isZeroSum.seq_iSup_iInf_eq_iInf_iSup kuhnGame_perfectRecall).symm.trans hsup_eq
  obtain ⟨hint_n, hint_v⟩ := hn1.interchange kuhnGame_perfectRecall kuhnGame_isZeroSum hn0
  exact ⟨hn0, hn1, hne, hs0, hs1, hb_max, hb_min, hs_max, hs_min,
    hev0, hev1, hsup_eq, hinf_eq, hint_n, hint_v.trans hev1⟩

/-! ### 2. Zero-sum perfect-information tree with chance & off-path non-SPE Nash -/

/-- Off-root subgame where player `true` compares `false ↦ (1, -1)` and `true ↦ (0, 0)`. -/
@[reducible] noncomputable def zeroPerfectSub : PerfectInfoTree Bool :=
  .decision true fun
    | false => .leaf (zsPayoff 1)
    | true => .leaf (zsPayoff 0)

/-- Zero-sum perfect-information tree with chance node (`1/2`) and unique SPE value `(2, -2)`:
* root `false` picks `Safe` (`false`, payoff `(2, -2)`) vs `Risky` (`true`);
* upon `Risky`, a fair coin pays `(2, -2)` vs letting player `true` act in `zeroPerfectSub`. -/
@[reducible] noncomputable def zeroPerfectTree : PerfectInfoTree Bool :=
  .decision false fun
    | false => .leaf (zsPayoff 2)
    | true => .chance (fun _ : Bool => (1 / 2 : ℝ)) fairCoin_isMixed fun
        | false => .leaf (zsPayoff 2)
        | true => zeroPerfectSub

theorem zeroPerfectTree_isZeroSum : zeroPerfectTree.IsZeroSum := by
  intro z
  cases z with
  | decision a sub =>
    cases a with
    | false => cases sub; simp [zsPayoff]
    | true =>
      cases sub with
      | chance c sub' =>
        cases c with
        | false => cases sub'; simp [zsPayoff]
        | true =>
          cases sub' with
          | decision b sub'' => cases b <;> cases sub'' <;> simp [zsPayoff]

/-- Unique SPE strategy `(Safe, true)` of `zeroPerfectTree`. -/
@[reducible] noncomputable def zeroPerfectSPE :
    ∀ i : Bool, PerfectInfoTree.PureStrategy i zeroPerfectTree :=
  fun _ => .decision (fun _ => false) fun
    | false => .leaf
    | true => .chance fun
        | false => .leaf
        | true => .decision (fun _ => true) fun
            | false => .leaf
            | true => .leaf

/-- Off-path non-SPE Nash strategy `(Safe, false)`: credible threat fails in `zeroPerfectSub`,
giving deviation payoff `3 / 2 ≤ 2` so `(Safe, false)` is still a behavioral Nash equilibrium with
the exact same minimax value `2`. -/
@[reducible] noncomputable def zeroPerfectThreat :
    ∀ i : Bool, PerfectInfoTree.PureStrategy i zeroPerfectTree :=
  fun _ => .decision (fun _ => false) fun
    | false => .leaf
    | true => .chance fun
        | false => .leaf
        | true => .decision (fun _ => false) fun
            | false => .leaf
            | true => .leaf

theorem zeroPerfectSPE_isPureSPE : zeroPerfectTree.IsPureSPE zeroPerfectSPE := by
  rw [PerfectInfoTree.isPureSPE_iff_oneShot]
  have hsub : zeroPerfectSub.expectedPayoff
      (fun i => ((zeroPerfectSPE i).childDecision true).childChance true) = zsPayoff 0 := by
    rw [PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq (a := true)
      (by simp [zeroPerfectSPE]), PerfectInfoTree.expectedPayoff_leaf]
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [show (zeroPerfectSPE false).headChoice = false by simp [zeroPerfectSPE],
      PerfectInfoTree.expectedPayoff_leaf]
    cases a
    · simp [zsPayoff]
    · simp only [PerfectInfoTree.expectedPayoff_chance, Fintype.sum_bool,
        PerfectInfoTree.expectedPayoff_leaf, hsub, zsPayoff]
      norm_num
  · cases a
    · trivial
    · intro c
      cases c
      · trivial
      · refine ⟨fun b => ?_, fun b => ?_⟩
        · dsimp only
          rw [show (((zeroPerfectSPE true).childDecision true).childChance true).headChoice = true
            by simp [zeroPerfectSPE], PerfectInfoTree.expectedPayoff_leaf]
          cases b <;> simp [zsPayoff]
        · cases b <;> trivial

theorem zeroPerfectThreat_isPureNash : zeroPerfectTree.toCostGame.IsPureNash zeroPerfectThreat := by
  have hroot : zeroPerfectTree.expectedPayoff zeroPerfectThreat = zsPayoff 2 := by
    rw [PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq (a := false)
      (by simp [zeroPerfectThreat]), PerfectInfoTree.expectedPayoff_leaf]
  intro i σ'
  cases i with
  | false =>
    simp only [PerfectInfoTree.toCostGame_cost, neg_le_neg_iff, hroot]
    cases h : σ'.headChoice
    · rw [PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq (a := false)
        (by simp [h]), PerfectInfoTree.expectedPayoff_leaf]
    · rw [PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq (a := true)
        (by simp [h]), PerfectInfoTree.expectedPayoff_chance, Fintype.sum_bool,
        PerfectInfoTree.expectedPayoff_leaf,
        PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq (a := false)
          (by simp [zeroPerfectThreat]),
        PerfectInfoTree.expectedPayoff_leaf]
      simp only [zsPayoff]
      norm_num
  | true =>
    simp only [PerfectInfoTree.toCostGame_cost, neg_le_neg_iff, hroot]
    rw [PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq (a := false)
      (by simp [zeroPerfectThreat]), PerfectInfoTree.expectedPayoff_leaf]

theorem zeroPerfectThreat_not_isPureSPE : ¬ zeroPerfectTree.IsPureSPE zeroPerfectThreat := by
  intro hspe
  rw [PerfectInfoTree.isPureSPE_iff_oneShot] at hspe
  have hsub := (hspe.2 true true).1 true
  dsimp only at hsub
  rw [show (((zeroPerfectThreat true).childDecision true).childChance true).headChoice = false
    by simp [zeroPerfectThreat]] at hsub
  simp only [PerfectInfoTree.expectedPayoff_leaf, zsPayoff] at hsub
  norm_num at hsub

open Classical in
/-- Connects `zeroPerfectTree.backwardInduction` to `IsBehaviorSPE`,
`PerfectInfoTree.backwardInduction_isSeqNash`, sequence-form LP minimax (value `2`), `IsPureNash`,
`IsMixedNash`, and certifies the off-path non-SPE Nash equilibrium `zeroPerfectThreat`. -/
theorem zeroPerfectTree_spe_vs_threat :
    zeroPerfectTree.IsBehaviorSPE (zeroPerfectTree.toExtensiveBehavior zeroPerfectSPE) ∧
      zeroPerfectTree.toExtensiveTree.IsSeqNash
        (zeroPerfectTree.toExtensiveTree.behaviorToRealizationPlan false
          (zeroPerfectTree.toExtensiveBehavior zeroPerfectTree.backwardInduction.strategy false))
        (zeroPerfectTree.toExtensiveTree.behaviorToRealizationPlan true
          (zeroPerfectTree.toExtensiveBehavior zeroPerfectTree.backwardInduction.strategy true)) ∧
      zeroPerfectTree.backwardInduction.payoff false = 2 ∧
      (⨆ x : {x : SeqVar zeroPerfectTree.toExtensiveTree false → ℝ //
          zeroPerfectTree.toExtensiveTree.IsRealizationPlan false x},
        zeroPerfectTree.toExtensiveTree.seqLowerVal x.val) = 2 ∧
      (⨅ y : {y : SeqVar zeroPerfectTree.toExtensiveTree true → ℝ //
          zeroPerfectTree.toExtensiveTree.IsRealizationPlan true y},
        zeroPerfectTree.toExtensiveTree.seqUpperVal y.val) = 2 ∧
      (zeroPerfectTree.toExtensiveTree.IsBehaviorNash
        (zeroPerfectTree.toExtensiveBehavior zeroPerfectThreat)) ∧
      (¬ zeroPerfectTree.IsBehaviorSPE (zeroPerfectTree.toExtensiveBehavior zeroPerfectThreat)) ∧
      (zeroPerfectTree.toExtensiveTree.evalBehavior
        (zeroPerfectTree.toExtensiveBehavior zeroPerfectThreat) =
          zeroPerfectTree.backwardInduction.payoff) ∧
      (zeroPerfectTree.expectedPayoff zeroPerfectSPE = zeroPerfectTree.backwardInduction.payoff) ∧
      (zeroPerfectTree.toExtensiveTree.evalMixed
        (fun i sE => (Pi.single (zeroPerfectSPE i) (1 : ℝ) :
            PerfectInfoTree.PureStrategy i zeroPerfectTree → ℝ)
          (PerfectInfoTree.PureStrategy.ofExtensive zeroPerfectTree sE)) =
          zeroPerfectTree.backwardInduction.payoff) := by
  have hspeB := (PerfectInfoTree.isPureSPE_iff_isBehaviorSPE zeroPerfectTree zeroPerfectSPE).1
    zeroPerfectSPE_isPureSPE
  have hbi_seq := PerfectInfoTree.backwardInduction_isSeqNash zeroPerfectTree
  have hbi_eq : zeroPerfectTree.backwardInduction.payoff = zsPayoff 2 := by
    have heq := zeroPerfectTree_isZeroSum.isPureNash_expectedPayoff_eq_backwardInduction
      zeroPerfectSPE_isPureSPE.isPureNash
    rw [← heq, PerfectInfoTree.expectedPayoff_decision_of_headChoice_eq (a := false)
      (by simp [zeroPerfectSPE]), PerfectInfoTree.expectedPayoff_leaf]
  have hbi0 : zeroPerfectTree.backwardInduction.payoff false = 2 := by
    rw [hbi_eq]
  obtain ⟨hs_lo, hs_hi, _⟩ := zeroPerfectTree_isZeroSum.backwardInduction_payoff_eq_seq_minimax
  have hthreatB : zeroPerfectTree.toExtensiveTree.IsBehaviorNash
      (zeroPerfectTree.toExtensiveBehavior zeroPerfectThreat) :=
    (PerfectInfoTree.toExtensiveTree_isBehaviorNash_pure_iff zeroPerfectTree zeroPerfectThreat).2
      zeroPerfectThreat_isPureNash
  have hthreat_not_spe : ¬ zeroPerfectTree.IsBehaviorSPE
      (zeroPerfectTree.toExtensiveBehavior zeroPerfectThreat) := by
    rw [← PerfectInfoTree.isPureSPE_iff_isBehaviorSPE]
    exact zeroPerfectThreat_not_isPureSPE
  have hthreat_ev : zeroPerfectTree.toExtensiveTree.evalBehavior
      (zeroPerfectTree.toExtensiveBehavior zeroPerfectThreat) =
        zeroPerfectTree.backwardInduction.payoff :=
    zeroPerfectTree_isZeroSum.isBehaviorNash_evalBehavior_eq_backwardInduction hthreatB
  have hspe_ev : zeroPerfectTree.expectedPayoff zeroPerfectSPE =
      zeroPerfectTree.backwardInduction.payoff :=
    zeroPerfectTree_isZeroSum.isPureNash_expectedPayoff_eq_backwardInduction
      zeroPerfectSPE_isPureSPE.isPureNash
  have hmix_ev :=
    zeroPerfectTree_isZeroSum.isMixedNash_expectedPayoff_eq_backwardInduction
      ((CostGame.isMixedNash_single_iff _ zeroPerfectSPE).2
        zeroPerfectSPE_isPureSPE.isPureNash)
  exact ⟨hspeB, hbi_seq, hbi0, hs_lo.symm.trans hbi0, hs_hi.symm.trans hbi0, hthreatB,
    hthreat_not_spe, hthreat_ev, hspe_ev, hmix_ev⟩

/-! ### 3. Chance-free (`HasNoChance`) sequential asymmetric matching pennies (`1 / 3`) -/

/-- Player `false` has two info sets `Bool` (`false`: Stay vs Play; `true`: row move);
player `true` has one info set `Unit` (simultaneous column move). -/
@[reducible] def detH : Bool → Type
  | false => Bool
  | true => Unit

instance instFintypeDetH : ∀ i, Fintype (detH i)
  | false => inferInstanceAs (Fintype Bool)
  | true => inferInstanceAs (Fintype Unit)

instance instDecidableEqDetH : ∀ i, DecidableEq (detH i)
  | false => inferInstanceAs (DecidableEq Bool)
  | true => inferInstanceAs (DecidableEq Unit)

/-- Binary action space (`false` / `true`) at every information set of `detSeqMP`. -/
@[reducible] def detAct : ∀ i, detH i → Type := fun _ _ => Bool

/-- Zero-sum leaf payoffs for the asymmetric matching-pennies subgame of `detSeqMP`. -/
@[reducible] def detPayoff (a₁ a₂ : Bool) : Bool → ℝ :=
  zsPayoff (match a₁, a₂ with
    | false, false => 1
    | false, true => -1
    | true, false => -1
    | true, true => 3)

/-- Chance-free sequential asymmetric matching pennies (5 leaves, exact minimax value `1 / 3`). -/
@[reducible] def detSeqMP : ExtensiveTree Bool detH detAct :=
  .decision false false fun
    | false => .leaf (zsPayoff 0)
    | true => .decision false true fun a₁ =>
        .decision true () fun a₂ => .leaf (detPayoff a₁ a₂)

theorem detSeqMP_hasNoChance : detSeqMP.HasNoChance := by
  intro a₀
  cases a₀
  · trivial
  · exact fun _ _ => trivial

theorem detSeqMP_isZeroSum : detSeqMP.IsZeroSum := by
  intro z
  cases z with
  | decision a₀ sub =>
    cases a₀ with
    | false => cases sub; simp [zsPayoff]
    | true =>
      cases sub with
      | decision a₁ sub' =>
        cases sub' with
        | decision a₂ sub'' => cases a₁ <;> cases a₂ <;> (cases sub''; simp [detPayoff, zsPayoff])

private theorem detSeqMP_playerSeq_false (h : detH false) {v : Node detSeqMP}
    (hv : v.IsDecisionOf false h) :
    v.playerSeq false = if h then [⟨false, true⟩] else [] := by
  cases v with
  | here =>
    have hh : (false : detH false) = h := eq_of_heq (Sigma.mk.inj_iff.1 hv).2
    subst hh
    rfl
  | decision a₀ sub =>
    cases a₀ with
    | false => cases sub; exact absurd hv (by simp)
    | true =>
      cases sub with
      | here =>
        have hh : (true : detH false) = h := eq_of_heq (Sigma.mk.inj_iff.1 hv).2
        subst hh
        rfl
      | decision a₁ sub' =>
        cases sub' with
        | here => exact absurd hv (by simp)
        | decision a₂ sub'' => cases sub''; exact absurd hv (by simp)

private theorem detSeqMP_playerSeq_true (h : detH true) {v : Node detSeqMP}
    (hv : v.IsDecisionOf true h) :
    v.playerSeq true = [] := by
  cases v with
  | here => exact absurd hv (by simp)
  | decision a₀ sub =>
    cases a₀ with
    | false => cases sub; exact absurd hv (by simp)
    | true =>
      cases sub with
      | here => exact absurd hv (by simp)
      | decision a₁ sub' =>
        cases sub' with
        | here => rfl
        | decision a₂ sub'' => cases sub''; exact absurd hv (by simp)

theorem detSeqMP_perfectRecall (i : Bool) : detSeqMP.PerfectRecall i := by
  intro h v₁ v₂ hv₁ hv₂
  cases i with
  | false => rw [detSeqMP_playerSeq_false h hv₁, detSeqMP_playerSeq_false h hv₂]
  | true => rw [detSeqMP_playerSeq_true h hv₁, detSeqMP_playerSeq_true h hv₂]

noncomputable def detOptB : ∀ i, ∀ h : detH i, detAct i h → ℝ
  | false, false, a => if a then 1 else 0
  | false, true, a => if a then 1 / 3 else 2 / 3
  | true, (), a => if a then 1 / 3 else 2 / 3

private theorem detOptB_isBehavior : ∀ i, IsBehaviorStrategy (detOptB i) := by
  intro i h
  refine isMixedStrategy_iff.2 ⟨fun a => ?_, ?_⟩
  · cases i with
    | false =>
      cases h
      · cases a <;> simp [detOptB]
      · (cases a <;> simp [detOptB]); norm_num
    | true => (cases a <;> simp [detOptB]); norm_num
  · cases i with
    | false =>
      cases h
      · simp [detOptB]
      · simp [detOptB]; norm_num
    | true => simp [detOptB]; norm_num

private theorem detSeqMP_evalBehavior_false (β : ∀ i, ∀ h : detH i, detAct i h → ℝ) :
    detSeqMP.evalBehavior β false =
      β false false true *
        (β false true false * (β true () false * 1 + β true () true * (-1)) +
          β false true true * (β true () false * (-1) + β true () true * 3)) := by
  simp only [detSeqMP, ExtensiveTree.evalBehavior_decision, ExtensiveTree.evalBehavior_leaf,
    Fintype.sum_bool, detPayoff, zsPayoff]
  ring

private noncomputable def detTermEquiv : Fin 5 ≃ Terminal detSeqMP where
  toFun
    | 0 => .decision false .leaf
    | 1 => .decision true (.decision false (.decision false .leaf))
    | 2 => .decision true (.decision false (.decision true .leaf))
    | 3 => .decision true (.decision true (.decision false .leaf))
    | 4 => .decision true (.decision true (.decision true .leaf))
  invFun
    | .decision false .leaf => 0
    | .decision true (.decision false (.decision false .leaf)) => 1
    | .decision true (.decision false (.decision true .leaf)) => 2
    | .decision true (.decision true (.decision false .leaf)) => 3
    | .decision true (.decision true (.decision true .leaf)) => 4
  left_inv k := by fin_cases k <;> rfl
  right_inv z := by
    cases z with
    | decision a₀ s =>
      cases a₀ with
      | false => cases s; rfl
      | true =>
        cases s with
        | decision a₁ s₁ =>
          cases a₁ <;> cases s₁ with
          | decision a₂ s₂ => cases a₂ <;> cases s₂ <;> rfl

open Classical in
/-- Chance-free witness: `detSeqMP.HasNoChance` injects leaves into sequence pairs
(`leafSeqPair_injective`), each matrix cell `detSeqMP.seqPayoffMat false` at a leaf's
`leafSeqPair` equals the exact leaf payoff `z.payoff false`, the nonzero support has cardinality
`≤ 5`, sparse-support and leaf-indexed bilinear sums
(`dotProduct_seqPayoffMat_mulVec_eq_sum_support`, `dotProduct_seqPayoffMat_mulVec_eq_sum_terminal`)
both evaluate to `1 / 3`, and mixed, behavioral, and sequence-form minimax values all equal
`1 / 3`. -/
theorem detSeqMP_sparse_and_mixed_minimax :
    Fintype.card (Terminal detSeqMP) = 5 ∧
      (univ.filter (fun e : SeqVar detSeqMP false × SeqVar detSeqMP true =>
          detSeqMP.seqPayoffMat false e.1 e.2 ≠ 0)).card ≤ 5 ∧
      Function.Injective detSeqMP.leafSeqPair ∧
      (detSeqMP.seqPayoffMat false
        (detSeqMP.leafSeqPair (.decision true (.decision true (.decision true .leaf)))).1
        (detSeqMP.leafSeqPair (.decision true (.decision true (.decision true .leaf)))).2 = 3) ∧
      (∑ e ∈ univ.filter (fun e : SeqVar detSeqMP false × SeqVar detSeqMP true =>
          detSeqMP.seqPayoffMat false e.1 e.2 ≠ 0),
        detSeqMP.behaviorToRealizationPlan false (detOptB false) e.1 *
          detSeqMP.seqPayoffMat false e.1 e.2 *
          detSeqMP.behaviorToRealizationPlan true (detOptB true) e.2) = 1 / 3 ∧
      (∑ z : Terminal detSeqMP,
        (z.chanceWeight *
          detSeqMP.behaviorToRealizationPlan false (detOptB false) (detSeqMP.leafSeqPair z).1 *
          detSeqMP.behaviorToRealizationPlan true (detOptB true) (detSeqMP.leafSeqPair z).2) *
          z.payoff false) = 1 / 3 ∧
      (⨆ μ₀ : {μ₀ : PureStrategy detH detAct false → ℝ // IsMixedStrategy μ₀},
          ⨅ μ₁ : {μ₁ : PureStrategy detH detAct true → ℝ // IsMixedStrategy μ₁},
            detSeqMP.evalMixed (fun | false => μ₀.val | true => μ₁.val) false) = 1 / 3 ∧
      (⨅ μ₁ : {μ₁ : PureStrategy detH detAct true → ℝ // IsMixedStrategy μ₁},
          ⨆ μ₀ : {μ₀ : PureStrategy detH detAct false → ℝ // IsMixedStrategy μ₀},
            detSeqMP.evalMixed (fun | false => μ₀.val | true => μ₁.val) false) = 1 / 3 := by
  have hcard : Fintype.card (Terminal detSeqMP) = 5 := by
    rw [← Fintype.card_congr detTermEquiv]
    decide
  have hsupp : (univ.filter (fun e : SeqVar detSeqMP false × SeqVar detSeqMP true =>
      detSeqMP.seqPayoffMat false e.1 e.2 ≠ 0)).card ≤ 5 :=
    (card_support_seqPayoffMat_le_card_terminal detSeqMP false).trans_eq hcard
  have hinj : Function.Injective detSeqMP.leafSeqPair :=
    detSeqMP_hasNoChance.leafSeqPair_injective
  have hentry : detSeqMP.seqPayoffMat false
      (detSeqMP.leafSeqPair (.decision true (.decision true (.decision true .leaf)))).1
      (detSeqMP.leafSeqPair (.decision true (.decision true (.decision true .leaf)))).2 = 3 := by
    rw [detSeqMP_hasNoChance.seqPayoffMat_leafSeqPair]
    simp [detPayoff, zsPayoff]
  obtain ⟨_, _, hev, hbv, _⟩ :=
    detSeqMP_isZeroSum.isBehaviorNash_of_saddle detSeqMP_perfectRecall (1 / 3 : ℝ)
      detOptB_isBehavior
      (fun β₀ hβ₀ => by
        rw [detSeqMP_evalBehavior_false]
        have hsumF : β₀ false false + β₀ false true = 1 := by
          simpa [Fintype.sum_bool, add_comm] using (hβ₀ false).sum_eq_one
        have hsumT : β₀ true false + β₀ true true = 1 := by
          simpa [Fintype.sum_bool, add_comm] using (hβ₀ true).sum_eq_one
        have hsub : β₀ true false * (detOptB true () false * 1 + detOptB true () true * (-1)) +
            β₀ true true * (detOptB true () false * (-1) + detOptB true () true * 3) = 1 / 3 := by
          simp only [detOptB, ↓reduceIte, Bool.false_eq_true]
          linear_combination (1 / 3 : ℝ) * hsumT
        dsimp only
        rw [hsub]
        have hf0 := (hβ₀ false).nonneg false
        have hf1 := (hβ₀ false).nonneg true
        linarith)
      (fun β₁ hβ₁ => by
        rw [detSeqMP_evalBehavior_false]
        have hsum1 : β₁ () false + β₁ () true = 1 := by
          simpa [Fintype.sum_bool, add_comm] using (hβ₁ ()).sum_eq_one
        simp only [detOptB, ↓reduceIte, Bool.false_eq_true]
        linarith)
  have hbilin : detSeqMP.behaviorToRealizationPlan false (detOptB false) ⬝ᵥ
      (detSeqMP.seqPayoffMat false *ᵥ
        detSeqMP.behaviorToRealizationPlan true (detOptB true)) = 1 / 3 :=
    (evalBehavior_eq_seqPayoffMat detSeqMP detOptB false).symm.trans hev
  have hsum_supp :=
    (dotProduct_seqPayoffMat_mulVec_eq_sum_support detSeqMP false
      (detSeqMP.behaviorToRealizationPlan false (detOptB false))
      (detSeqMP.behaviorToRealizationPlan true (detOptB true))).symm.trans hbilin
  have hsum_term :=
    (dotProduct_seqPayoffMat_mulVec_eq_sum_terminal detSeqMP false
      (detSeqMP.behaviorToRealizationPlan false (detOptB false))
      (detSeqMP.behaviorToRealizationPlan true (detOptB true))).symm.trans hbilin
  have hmix_lo :
      (⨆ μ₀ : {μ₀ : PureStrategy detH detAct false → ℝ // IsMixedStrategy μ₀},
          ⨅ μ₁ : {μ₁ : PureStrategy detH detAct true → ℝ // IsMixedStrategy μ₁},
            detSeqMP.evalMixed (fun | false => μ₀.val | true => μ₁.val) false) = 1 / 3 := by
    change (⨆ μ₀ : {μ₀ // IsMixedStrategy μ₀}, detSeqMP.mixedLowerVal μ₀.val) = 1 / 3
    rw [detSeqMP_isZeroSum.mixed_minimax_eq_behavior_minimax detSeqMP_perfectRecall, hbv]
  have hmix_hi :
      (⨅ μ₁ : {μ₁ : PureStrategy detH detAct true → ℝ // IsMixedStrategy μ₁},
          ⨆ μ₀ : {μ₀ : PureStrategy detH detAct false → ℝ // IsMixedStrategy μ₀},
            detSeqMP.evalMixed (fun | false => μ₀.val | true => μ₁.val) false) = 1 / 3 :=
    (detSeqMP_isZeroSum.mixed_iSup_iInf_eq_iInf_iSup detSeqMP_perfectRecall).symm.trans hmix_lo
  exact ⟨hcard, hsupp, hinj, hentry, hsum_supp, hsum_term, hmix_lo, hmix_hi⟩

/-! ### 4. Two-player equilibrium interchangeability with distinct strategies for both players -/

/-- Singleton information sets for a `3 × 3` simultaneous-move zero-sum extensive game. -/
@[reducible] def biH : Bool → Type := fun _ => Unit

/-- Three actions (`0`, `1` optimal, `2` strictly dominated) for each player. -/
@[reducible] def biAct : ∀ i, biH i → Type := fun _ _ => Fin 3

/-- Zero-sum payoff where `{0, 1} × {0, 1}` pays `1`, `a₀ = 2` pays `-1` against `{0, 1}`, and
`a₁ = 2` pays `3` against `{0, 1}` (strictly suboptimal for player `true`). -/
@[reducible] def biPayoff (a₀ a₁ : Fin 3) : Bool → ℝ :=
  zsPayoff (if a₀ = 2 then (if a₁ = 2 then 0 else -1) else (if a₁ = 2 then 3 else 1))

/-- Two-player zero-sum extensive game admitting distinct optimal strategies for both players while
strictly dominating action `2` for both players. -/
@[reducible] def biGame : ExtensiveTree Bool biH biAct :=
  .decision false () fun a₀ => .decision true () fun a₁ => .leaf (biPayoff a₀ a₁)

theorem biGame_isZeroSum : biGame.IsZeroSum := by
  intro z
  cases z with
  | decision a₀ s =>
    cases s with
    | decision a₁ s' => cases s'; simp [biPayoff, zsPayoff]

theorem biGame_perfectRecall (i : Bool) : biGame.PerfectRecall i := by
  intro h v₁ v₂ hv₁ hv₂
  cases i with
  | false =>
    have seq_nil : ∀ {v : Node biGame}, v.IsDecisionOf false () → v.playerSeq false = [] := by
      intro v hv
      cases v with
      | here => rfl
      | decision _ s =>
        cases s with
        | here => exact absurd hv (by simp)
        | decision _ s' => cases s'; exact absurd hv (by simp)
    rw [seq_nil hv₁, seq_nil hv₂]
  | true =>
    have seq_nil : ∀ {v : Node biGame}, v.IsDecisionOf true () → v.playerSeq true = [] := by
      intro v hv
      cases v with
      | here => exact absurd hv (by simp)
      | decision _ s =>
        cases s with
        | here => rfl
        | decision _ s' => cases s'; exact absurd hv (by simp)
    rw [seq_nil hv₁, seq_nil hv₂]

/-- Deterministic behavior strategy placing weight `1` on action `k : Fin 3`. -/
@[reducible] def biPureStrat (k : Fin 3) : ∀ _ : Unit, Fin 3 → ℝ :=
  fun _ a => if a = k then 1 else 0

/-- Profile in `biGame` where both players play action `k`. -/
@[reducible] def biPureProf (k : Fin 3) : ∀ i, ∀ h : biH i, biAct i h → ℝ :=
  fun _ => biPureStrat k

private theorem biPureStrat_isBehavior (i : Bool) (k : Fin 3) :
    IsBehaviorStrategy (H := biH) (Act := biAct) (i := i) (biPureStrat k) := by
  intro _
  refine isMixedStrategy_iff.2 ⟨fun a => ?_, ?_⟩
  · fin_cases k <;> fin_cases a <;> simp [biPureStrat]
  · fin_cases k <;> simp [biPureStrat]

private theorem biGame_evalBehavior_false (β : ∀ i, ∀ h : biH i, biAct i h → ℝ) :
    biGame.evalBehavior β false =
      (β false () 0 + β false () 1) * ((β true () 0 + β true () 1) * 1 + β true () 2 * 3) +
        β false () 2 * ((β true () 0 + β true () 1) * (-1)) := by
  simp only [biGame, ExtensiveTree.evalBehavior_decision, ExtensiveTree.evalBehavior_leaf,
    Fin.sum_univ_three, biPayoff, zsPayoff]
  norm_num
  ring

private theorem biPureProf_nash_of_ne_two {k : Fin 3} (hk : k ≠ 2) :
    biGame.IsBehaviorNash (biPureProf k) ∧
      biGame.IsSeqNash (biGame.behaviorToRealizationPlan false (biPureStrat k))
        (biGame.behaviorToRealizationPlan true (biPureStrat k)) ∧
      biGame.evalBehavior (biPureProf k) false = 1 := by
  have hk_sum : biPureStrat k () 0 + biPureStrat k () 1 = 1 ∧ biPureStrat k () 2 = 0 := by
    fin_cases k
    · simp [biPureStrat]
    · simp [biPureStrat]
    · exact absurd rfl hk
  obtain ⟨hn, hs, hev, _, _⟩ :=
    biGame_isZeroSum.isBehaviorNash_of_saddle biGame_perfectRecall (β := biPureProf k) 1
      (fun i => biPureStrat_isBehavior i k)
      (fun β₀ hβ₀ => by
        rw [biGame_evalBehavior_false]
        have hsum : β₀ () 0 + β₀ () 1 + β₀ () 2 = 1 := by
          simpa [Fin.sum_univ_three, add_assoc] using (hβ₀ ()).sum_eq_one
        have h2 := (hβ₀ ()).nonneg 2
        dsimp only [biPureProf]
        rw [hk_sum.1, hk_sum.2]
        linarith)
      (fun β₁ hβ₁ => by
        rw [biGame_evalBehavior_false]
        have hsum : β₁ () 0 + β₁ () 1 + β₁ () 2 = 1 := by
          simpa [Fin.sum_univ_three, add_assoc] using (hβ₁ ()).sum_eq_one
        have h2 := (hβ₁ ()).nonneg 2
        dsimp only [biPureProf]
        rw [hk_sum.1, hk_sum.2]
        linarith)
  exact ⟨hn, hs, hev⟩

open Classical in
/-- Exercises `IsBehaviorNash.interchange` and `IsSeqNash.interchange` on two equilibria
`biPureProf 0` and `biPureProf 1` that differ in **both** player `false` and player `true`, while
confirming that dominated profile `biPureProf 2` is not a Nash equilibrium. -/
theorem biGame_two_sided_interchange :
    biPureProf 0 false ≠ biPureProf 1 false ∧
      biPureProf 0 true ≠ biPureProf 1 true ∧
      biGame.IsBehaviorNash (fun | false => biPureProf 0 false | true => biPureProf 1 true) ∧
      biGame.evalBehavior (fun | false => biPureProf 0 false | true => biPureProf 1 true) false =
        1 ∧
      biGame.IsSeqNash (biGame.behaviorToRealizationPlan false (biPureStrat 0))
        (biGame.behaviorToRealizationPlan true (biPureStrat 1)) ∧
      biGame.behaviorToRealizationPlan false (biPureStrat 0) ⬝ᵥ
        (biGame.seqPayoffMat false *ᵥ
          biGame.behaviorToRealizationPlan true (biPureStrat 1)) = 1 ∧
      ¬ biGame.IsBehaviorNash (biPureProf 2) := by
  obtain ⟨hn0, hs0, hev0⟩ := biPureProf_nash_of_ne_two (k := 0) (by decide)
  obtain ⟨hn1, hs1, _⟩ := biPureProf_nash_of_ne_two (k := 1) (by decide)
  have hneF : biPureProf 0 false ≠ biPureProf 1 false := by
    intro h
    have h0 := congrFun (congrFun h ()) 0
    norm_num [biPureProf, biPureStrat] at h0
  have hneT : biPureProf 0 true ≠ biPureProf 1 true := hneF
  obtain ⟨hintB, hvB⟩ := hn0.interchange biGame_perfectRecall biGame_isZeroSum hn1
  obtain ⟨hintS, hvS⟩ := hs0.interchange biGame_perfectRecall biGame_isZeroSum hs1
  have hvS_one : biGame.behaviorToRealizationPlan false (biPureStrat 0) ⬝ᵥ
      (biGame.seqPayoffMat false *ᵥ
        biGame.behaviorToRealizationPlan true (biPureStrat 1)) = 1 :=
    hvS.trans ((evalBehavior_eq_seqPayoffMat biGame (biPureProf 0) false).symm.trans hev0)
  have hnot2 : ¬ biGame.IsBehaviorNash (biPureProf 2) := by
    intro hn2
    have hopt := ((biGame_isZeroSum.isBehaviorNash_iff_saddlePoint (biPureProf 2)).1 hn2).2.1
      (biPureStrat 0) (biPureStrat_isBehavior false 0)
    rw [biGame_evalBehavior_false, biGame_evalBehavior_false] at hopt
    norm_num [biPureProf, biPureStrat] at hopt
  exact ⟨hneF, hneT, hintB, hvB.trans hev0, hintS, hvS_one, hnot2⟩

end CslibFrontierTests.GameTheory.ExtensiveZeroSum
