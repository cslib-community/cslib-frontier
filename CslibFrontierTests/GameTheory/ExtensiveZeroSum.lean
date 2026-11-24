/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.Extensive.ZeroSum

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
  `IsBehaviorNash`, `IsSeqNash`, `seq_iSup_iInf_eq_iInf_iSup = -1 / 18`, and
  `IsBehaviorNash.interchange`.
* **Witness 2 — Zero-sum perfect-information tree with chance & off-path non-SPE Nash
  (`zeroPerfectTree`)**: verifies `PerfectInfoTree.IsZeroSum`, `isPureSPE_iff_isBehaviorSPE`,
  `backwardInduction_isBehaviorSPE`, `backwardInduction_isSeqNash`,
  `backwardInduction_snd_eq_seq_minimax` (value `2`),
  `isPureNash_expectedPayoff_eq_backwardInduction`,
  `isMixedNash_expectedPayoff_eq_backwardInduction`, and a non-credible off-path behavioral Nash
  equilibrium with the same minimax payoff `2` that fails `IsBehaviorSPE` and `IsPureSPE`.
* **Witness 3 — Deterministic (`HasNoChance`) sequential asymmetric matching pennies
  (`detSeqMP`)**: exercises `HasNoChance.leafSeqPair_injective`,
  `HasNoChance.seqPayoffMat_leafSeqPair` at concrete terminal leaves,
  `card_support_seqPayoffMat_le_card_terminal (≤ 5)`, and equality of mixed, behavioral, and
  sequence-form minimax values (`1 / 3`) via `mixed_minimax_eq_behavior_minimax` and
  `mixed_iSup_iInf_eq_iInf_iSup`.
-/

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

private theorem uniformSix_isMixed : IsMixedStrategy (fun _ : Fin 6 => (1 / 6 : ℝ)) :=
  isMixedStrategy_iff.2 ⟨fun _ => by norm_num, by norm_num⟩

private theorem fairCoin_isMixed : IsMixedStrategy (fun _ : Bool => (1 / 2 : ℝ)) :=
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
          | false => cases sub₂; exact add_neg_cancel _
          | true =>
            cases sub₂ with
            | decision a₂ sub₃ => cases a₂ <;> (cases sub₃; exact add_neg_cancel _)
      | true =>
        cases sub₁ with
        | decision a₁ sub₂ => cases a₁ <;> (cases sub₂; exact add_neg_cancel _)

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
  simp only [ExtensiveTree.evalBehavior, Fintype.sum_bool, kuhnShowdown, zsPayoff, kuhnDealPayoff]
  split_ifs <;> ring

private theorem kuhnGame_evalBehavior_false (β : ∀ i, ∀ h : kuhnH i, kuhnAct i h → ℝ) :
    kuhnGame.evalBehavior β false =
      (1 / 6 : ℝ) *
        (kuhnDealPayoff β 0 1 + kuhnDealPayoff β 0 2 +
         kuhnDealPayoff β 1 0 + kuhnDealPayoff β 1 2 +
         kuhnDealPayoff β 2 0 + kuhnDealPayoff β 2 1) := by
  dsimp only [kuhnGame]
  rw [ExtensiveTree.evalBehavior]
  simp only [Fin.sum_univ_six, kuhnCard₀, kuhnCard₁, kuhnDealTree_evalBehavior_false]
  ring

/-- Player `false`'s parameterized family of minimax behavioral strategies (`0 ≤ α ≤ 1 / 3`) in
3-card Kuhn poker ([vonStengel2007], Example 3.1). -/
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
        kuhnGame.behaviorLowerVal β₀.1) = -(1 / 18 : ℝ) ∧
      (⨆ x : {x : SeqVar kuhnGame false → ℝ // kuhnGame.IsRealizationPlan false x},
        kuhnGame.seqLowerVal x.1) = -(1 / 18 : ℝ) := by
  have hbeh : ∀ i, IsBehaviorStrategy (kuhnOptProfile α i) := fun
    | false => kuhnOptFalse_isBehavior h0 h1
    | true => kuhnOptTrue_isBehavior
  exact kuhnGame_isZeroSum.isBehaviorNash_of_saddle kuhnGame_perfectRecall (-(1 / 18 : ℝ))
    hbeh kuhnOptTrue_upper_bound (kuhnOptFalse_lower_bound h0 h1)

open Classical in
/-- Full 3-card Kuhn poker minimax certification:
* both `kuhnOptProfile 0` (`α = 0`) and `kuhnOptProfile (1 / 3)` (`α = 1 / 3`) are distinct
  behavioral and sequence-form Nash equilibria with exact minimax value `-1 / 18`;
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
      kuhnGame.evalBehavior (kuhnOptProfile 0) false = -(1 / 18 : ℝ) ∧
      kuhnGame.evalBehavior (kuhnOptProfile (1 / 3)) false = -(1 / 18 : ℝ) ∧
      (⨆ x : {x : SeqVar kuhnGame false → ℝ // kuhnGame.IsRealizationPlan false x},
          ⨅ y : {y : SeqVar kuhnGame true → ℝ // kuhnGame.IsRealizationPlan true y},
            x.1 ⬝ᵥ (kuhnGame.seqPayoffMat false *ᵥ y.1)) = -(1 / 18 : ℝ) ∧
      (⨅ y : {y : SeqVar kuhnGame true → ℝ // kuhnGame.IsRealizationPlan true y},
          ⨆ x : {x : SeqVar kuhnGame false → ℝ // kuhnGame.IsRealizationPlan false x},
            x.1 ⬝ᵥ (kuhnGame.seqPayoffMat false *ᵥ y.1)) = -(1 / 18 : ℝ) ∧
      kuhnGame.IsBehaviorNash
        (fun | false => kuhnOptProfile (1 / 3) false | true => kuhnOptProfile 0 true) ∧
      kuhnGame.evalBehavior
        (fun | false => kuhnOptProfile (1 / 3) false | true => kuhnOptProfile 0 true) false =
          -(1 / 18 : ℝ) := by
  obtain ⟨hn0, hs0, hev0, _, hseq_mm⟩ :=
    kuhnOptProfile_saddle (α := (0 : ℝ)) le_rfl (by norm_num)
  obtain ⟨hn1, hs1, hev1, _, _⟩ :=
    kuhnOptProfile_saddle (α := (1 / 3 : ℝ)) (by norm_num) le_rfl
  have hne : kuhnOptProfile 0 ≠ kuhnOptProfile (1 / 3) := by
    intro heq
    have h0 := congrFun (congrFun (congrFun heq false) (0, false)) true
    norm_num [kuhnOptProfile, kuhnOptFalse] at h0
  have hsup_eq :
      (⨆ x : {x : SeqVar kuhnGame false → ℝ // kuhnGame.IsRealizationPlan false x},
          ⨅ y : {y : SeqVar kuhnGame true → ℝ // kuhnGame.IsRealizationPlan true y},
            x.1 ⬝ᵥ (kuhnGame.seqPayoffMat false *ᵥ y.1)) = -(1 / 18 : ℝ) :=
    hseq_mm
  have hinf_eq :
      (⨅ y : {y : SeqVar kuhnGame true → ℝ // kuhnGame.IsRealizationPlan true y},
          ⨆ x : {x : SeqVar kuhnGame false → ℝ // kuhnGame.IsRealizationPlan false x},
            x.1 ⬝ᵥ (kuhnGame.seqPayoffMat false *ᵥ y.1)) = -(1 / 18 : ℝ) :=
    (kuhnGame_isZeroSum.seq_iSup_iInf_eq_iInf_iSup kuhnGame_perfectRecall).symm.trans hsup_eq
  obtain ⟨hint_n, hint_v⟩ := hn1.interchange kuhnGame_perfectRecall kuhnGame_isZeroSum hn0
  exact ⟨hn0, hn1, hne, hs0, hs1, hev0, hev1, hsup_eq, hinf_eq, hint_n, hint_v.trans hev1⟩

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
  refine ⟨fun a => ?_, fun a => ?_⟩
  · cases a <;> simp [zeroPerfectSPE, zsPayoff]
  · cases a
    · trivial
    · intro c
      cases c
      · trivial
      · refine ⟨fun b => ?_, fun b => ?_⟩
        · cases b <;> simp [zeroPerfectSPE, zsPayoff]
        · cases b <;> trivial

theorem zeroPerfectThreat_isPureNash : zeroPerfectTree.toCostGame.IsPureNash zeroPerfectThreat := by
  intro i σ'
  cases i with
  | false =>
    simp only [PerfectInfoTree.toCostGame, neg_le_neg_iff]
    rw [PerfectInfoTree.expectedPayoff_decision, PerfectInfoTree.expectedPayoff_decision,
      Function.update_self]
    cases h : σ'.headChoice
    · simp [zeroPerfectThreat]
    · rw [PerfectInfoTree.expectedPayoff_chance, Fintype.sum_bool,
        PerfectInfoTree.expectedPayoff_leaf, PerfectInfoTree.expectedPayoff_decision]
      rw [Function.update_of_ne Bool.false_ne_true.symm]
      simp only [zeroPerfectThreat, PerfectInfoTree.PureStrategy.headChoice_decision,
        PerfectInfoTree.PureStrategy.childDecision_decision,
        PerfectInfoTree.PureStrategy.childChance_chance,
        PerfectInfoTree.expectedPayoff_leaf, zsPayoff]
      norm_num
  | true =>
    simp only [PerfectInfoTree.toCostGame, neg_le_neg_iff]
    rw [PerfectInfoTree.expectedPayoff_decision, Function.update_of_ne Bool.false_ne_true]
    rfl

theorem zeroPerfectThreat_not_isPureSPE : ¬ zeroPerfectTree.IsPureSPE zeroPerfectThreat := by
  intro hspe
  rw [PerfectInfoTree.isPureSPE_iff_oneShot] at hspe
  have hsub := (hspe.2 true true).1 true
  simp only [zeroPerfectThreat, PerfectInfoTree.PureStrategy.childDecision_decision,
    PerfectInfoTree.PureStrategy.childChance_chance,
    PerfectInfoTree.PureStrategy.headChoice_decision,
    PerfectInfoTree.expectedPayoff_leaf, zsPayoff] at hsub
  norm_num at hsub

open Classical in
/-- Connects `zeroPerfectTree.backwardInduction` to `IsBehaviorSPE`, sequence-form LP minimax
(value `2`), `IsPureNash`, `IsMixedNash`, and certifies the off-path non-SPE Nash equilibrium
`zeroPerfectThreat`. -/
theorem zeroPerfectTree_spe_vs_threat :
    zeroPerfectTree.IsBehaviorSPE (zeroPerfectTree.toExtensiveBehavior zeroPerfectSPE) ∧
      (zeroPerfectTree.backwardInduction).2 false = 2 ∧
      (⨆ x : {x : SeqVar zeroPerfectTree.toExtensiveTree false → ℝ //
          zeroPerfectTree.toExtensiveTree.IsRealizationPlan false x},
        zeroPerfectTree.toExtensiveTree.seqLowerVal x.1) = 2 ∧
      (⨅ y : {y : SeqVar zeroPerfectTree.toExtensiveTree true → ℝ //
          zeroPerfectTree.toExtensiveTree.IsRealizationPlan true y},
        zeroPerfectTree.toExtensiveTree.seqUpperVal y.1) = 2 ∧
      (zeroPerfectTree.toExtensiveTree.IsBehaviorNash
        (zeroPerfectTree.toExtensiveBehavior zeroPerfectThreat)) ∧
      (¬ zeroPerfectTree.IsBehaviorSPE (zeroPerfectTree.toExtensiveBehavior zeroPerfectThreat)) ∧
      (zeroPerfectTree.toExtensiveTree.evalBehavior
        (zeroPerfectTree.toExtensiveBehavior zeroPerfectThreat) =
          (zeroPerfectTree.backwardInduction).2) ∧
      (zeroPerfectTree.expectedPayoff zeroPerfectSPE = (zeroPerfectTree.backwardInduction).2) ∧
      (zeroPerfectTree.toExtensiveTree.evalMixed
        (fun i sE => (Pi.single (zeroPerfectSPE i) (1 : ℝ) :
            PerfectInfoTree.PureStrategy i zeroPerfectTree → ℝ)
          (PerfectInfoTree.PureStrategy.ofExtensive zeroPerfectTree sE)) =
          (zeroPerfectTree.backwardInduction).2) := by
  have hspeB := (PerfectInfoTree.isPureSPE_iff_isBehaviorSPE zeroPerfectTree zeroPerfectSPE).1
    zeroPerfectSPE_isPureSPE
  have hbi_eq : (zeroPerfectTree.backwardInduction).2 = zsPayoff 2 := by
    have heq := zeroPerfectTree_isZeroSum.isPureNash_expectedPayoff_eq_backwardInduction
      zeroPerfectSPE_isPureSPE.isPureNash
    rw [← heq]
    ext i
    cases i <;> simp [zeroPerfectSPE, zsPayoff]
  have hbi0 : (zeroPerfectTree.backwardInduction).2 false = 2 := by
    rw [hbi_eq]
  obtain ⟨hs_lo, hs_hi, _⟩ := zeroPerfectTree_isZeroSum.backwardInduction_snd_eq_seq_minimax
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
        (zeroPerfectTree.backwardInduction).2 :=
    zeroPerfectTree_isZeroSum.isBehaviorNash_evalBehavior_eq_backwardInduction hthreatB
  have hspe_ev : zeroPerfectTree.expectedPayoff zeroPerfectSPE =
      (zeroPerfectTree.backwardInduction).2 :=
    zeroPerfectTree_isZeroSum.isPureNash_expectedPayoff_eq_backwardInduction
      zeroPerfectSPE_isPureSPE.isPureNash
  have hmix_ev :=
    zeroPerfectTree_isZeroSum.isMixedNash_expectedPayoff_eq_backwardInduction
      ((CostGame.isMixedNash_single_iff _ zeroPerfectSPE).2
        zeroPerfectSPE_isPureSPE.isPureNash)
  exact ⟨hspeB, hbi0, hs_lo.symm.trans hbi0, hs_hi.symm.trans hbi0, hthreatB,
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
    | false => cases sub; exact add_neg_cancel _
    | true =>
      cases sub with
      | decision a₁ sub' =>
        cases sub' with
        | decision a₂ sub'' => cases a₁ <;> cases a₂ <;> (cases sub''; exact add_neg_cancel _)

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

private noncomputable def detOptB : ∀ i, ∀ h : detH i, detAct i h → ℝ
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
  simp only [ExtensiveTree.evalBehavior, Fintype.sum_bool, detPayoff, zsPayoff]
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
`≤ 5`, and mixed, behavioral, and sequence-form minimax values all equal `1 / 3`. -/
theorem detSeqMP_sparse_and_mixed_minimax :
    Fintype.card (Terminal detSeqMP) = 5 ∧
      (univ.filter (fun e : SeqVar detSeqMP false × SeqVar detSeqMP true =>
          detSeqMP.seqPayoffMat false e.1 e.2 ≠ 0)).card ≤ 5 ∧
      Function.Injective detSeqMP.leafSeqPair ∧
      (detSeqMP.seqPayoffMat false
        (detSeqMP.leafSeqPair (.decision true (.decision true (.decision true .leaf)))).1
        (detSeqMP.leafSeqPair (.decision true (.decision true (.decision true .leaf)))).2 = 3) ∧
      (⨆ μ₀ : {μ₀ : PureStrategy detH detAct false → ℝ // IsMixedStrategy μ₀},
          ⨅ μ₁ : {μ₁ : PureStrategy detH detAct true → ℝ // IsMixedStrategy μ₁},
            detSeqMP.evalMixed (fun | false => μ₀.1 | true => μ₁.1) false) = 1 / 3 ∧
      (⨅ μ₁ : {μ₁ : PureStrategy detH detAct true → ℝ // IsMixedStrategy μ₁},
          ⨆ μ₀ : {μ₀ : PureStrategy detH detAct false → ℝ // IsMixedStrategy μ₀},
            detSeqMP.evalMixed (fun | false => μ₀.1 | true => μ₁.1) false) = 1 / 3 := by
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
    rfl
  obtain ⟨_, _, _, hbv, _⟩ :=
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
  have hmix_lo :
      (⨆ μ₀ : {μ₀ : PureStrategy detH detAct false → ℝ // IsMixedStrategy μ₀},
          ⨅ μ₁ : {μ₁ : PureStrategy detH detAct true → ℝ // IsMixedStrategy μ₁},
            detSeqMP.evalMixed (fun | false => μ₀.1 | true => μ₁.1) false) = 1 / 3 := by
    change (⨆ μ₀ : {μ₀ // IsMixedStrategy μ₀}, detSeqMP.mixedLowerVal μ₀.1) = 1 / 3
    rw [detSeqMP_isZeroSum.mixed_minimax_eq_behavior_minimax detSeqMP_perfectRecall, hbv]
  have hmix_hi :
      (⨅ μ₁ : {μ₁ : PureStrategy detH detAct true → ℝ // IsMixedStrategy μ₁},
          ⨆ μ₀ : {μ₀ : PureStrategy detH detAct false → ℝ // IsMixedStrategy μ₀},
            detSeqMP.evalMixed (fun | false => μ₀.1 | true => μ₁.1) false) = 1 / 3 :=
    (detSeqMP_isZeroSum.mixed_iSup_iInf_eq_iInf_iSup detSeqMP_perfectRecall).symm.trans hmix_lo
  exact ⟨hcard, hsupp, hinj, hentry, hmix_lo, hmix_hi⟩

end CslibFrontierTests.GameTheory.ExtensiveZeroSum
