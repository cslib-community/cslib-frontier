/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Infinitely Repeated Prisoner's Dilemma, Reputations, and Whitewashing

Formalizes the infinitely repeated Prisoner's Dilemma, reputational trigger strategies, and the
cheap-pseudonym whitewashing / Pay-Your-Dues (`PYD`) model from Sections 27.2–27.3 and
Exercises 27.1–27.5 of Eric Friedman, Paul Resnick, and Rahul Sami, *"Manipulation-Resistant
Reputation Systems"*, Chapter 27 of *Algorithmic Game Theory* [FriedmanResnickSami2007], following
[FriedmanResnick2001].

## Model and source mapping

* **Stage Prisoner's Dilemma (`PDAction`, `pdPayoff`, `pdWelfare`):** matches
  [FriedmanResnickSami2007, §27.2, p. 680] verbatim: `π(C, C) = 1`, `π(D, D) = 0`, `π(D, C) = 2`,
  and `π(C, D) = -1`, with social welfare `2`, `0`, and `1` on `(C, C)`, `(D, D)`, and asymmetric
  outcomes `(D, C)` / `(C, D)` respectively.
* **Normalized discounted payoff (`discountedPayoff`):** `(1 - δ) * ∑' t, δ ^ t * u t` for
  `0 ≤ δ < 1` [FriedmanResnickSami2007, §27.2, p. 681], satisfying `discountedPayoff δ (fun _ => c)
  = c` (Exercise 27.1, p. 696) and the one-step Bellman decomposition `discountedPayoff_cons`.
* **Subgame-perfect Nash equilibrium (`IsSPNE`) and one-shot deviation principle
  (`isSPNE_iff_noOneShotDev`):** public-history strategies `PDStrategy` in the infinitely repeated
  game, proved equivalent to absence of profitable one-shot deviations at every finite history via
  contraction of `contPayoff₁` / `contPayoff₂` at rate `δ < 1` [FriedmanResnickSami2007, §27.2,
  p. 681].
* **Trigger and Tit-for-Tat characterizations:**
  * `(grim, grim)` is an SPNE iff `1 / 2 ≤ δ` (`isSPNE_grim_iff`, §27.2, p. 681).
  * Naive opponent-only Grim (`naiveGrim₁`, `naiveGrim₂`) is *never* an SPNE for `0 ≤ δ < 1`
    (`not_isSPNE_naiveGrim`, Exercise 27.3, p. 696).
  * Tit-for-Tat (`titForTat₁`, `titForTat₂`) is an SPNE iff `δ = 1 / 2` (`isSPNE_titForTat_iff`,
    `not_isSPNE_titForTat_of_ne`): under NRTV's stage payoffs `(1, 2, 0, -1)`, temptation threshold
    `(T - R) / (R - S) = 1 / 2` coincides with forgiveness indifference at `(C, D)`, so `(TFT, TFT)`
    holds at the single knife-edge `δ = 1 / 2` and fails for every `δ ∈ [0, 1) \ {1 / 2}` (refining
    the statement of Exercise 27.2, p. 696).
  * Under uniform random pairing among `N ≥ 1` potential opponents (§27.2, p. 681; Exercise 27.5,
    p. 697), Personalized-Grim deters one-shot defection iff `(N : ℝ) / (N + 1) ≤ δ`
    (`personalizedGrim_incentive_iff`, correcting the `1 - 1 / (2N)` slip on p. 681), whereas
    shared Reputational-Grim requires only `1 / 2 ≤ δ` independently of `N`.
* **Whitewashing entry fees and Pay-Your-Dues (`§27.3`, p. 682; Exercise 27.4, p. 697):**
  * With registration fee `f`, Reputational-Grim deters both one-shot and perpetual whitewashing
    iff `1 / δ ≤ f` (`entryFee_deters_whitewashing_iff`,
    `entryFee_deters_perpetual_whitewashing_iff`).
  * With free pseudonyms, Pay-Your-Dues (`pydAction`, `pydNextStanding`) gives a `goodVeteran` a
    stage-payoff advantage of `2` over a `newcomer` against veteran partners
    (`pyd_goodVeteran_vs_newcomer_gap`), makes truthful `PYD` without whitewashing at `.newcomer`
    and `.goodVeteran` standings optimal across all partner standings iff `1 / 2 ≤ δ`
    (`pyd_incentive_iff`, strictly optimal on cooperative prescriptions for `1 / 2 < δ`), and incurs
    newcomer–veteran welfare `1 < 2` (`pyd_newcomer_welfare_bounds`).
  * *Model scope note:* Unlike the full public-history strategy `IsSPNE` theorems above,
    `personalizedGrim_incentive_iff`, `entryFee_deters_*`, and `pyd_incentive_iff` verify the
    closed-form discounted stream and one-step Bellman inequalities against the explicit expressions
    `personalizedGrimDevPayoff`, `honestEntryPayoff` / `oneShotWhitewashPayoff` /
    `perpetualWhitewashPayoff`, and `pydContValue` rather than deriving continuation payoffs from an
    explicit `N`-player random-matching or pseudonym-reset repeated game.

## Main definitions

* `Cslib.GameTheory.Reputation.PDAction`, `pdPayoff`, `pdWelfare`, `PDRound`, `PDHistory`,
  `PDStrategy`
* `Cslib.GameTheory.Reputation.discountedPayoff`, `contPayoff₁`, `contPayoff₂`, `NoOneShotDev`,
  `IsSPNE`
* `Cslib.GameTheory.Reputation.grim`, `naiveGrim₁`, `naiveGrim₂`, `titForTat₁`, `titForTat₂`
* `Cslib.GameTheory.Reputation.personalizedGrimDevPayoff`, `honestEntryPayoff`,
  `oneShotWhitewashPayoff`, `ReputationStanding`, `pydAction`, `pydNextStanding`, `pydContValue`

## Main results

* `Cslib.GameTheory.Reputation.discountedPayoff_const`: Exercise 27.1.
* `Cslib.GameTheory.Reputation.isSPNE_iff_noOneShotDev`: one-shot deviation characterization of
  SPNE.
* `Cslib.GameTheory.Reputation.isSPNE_grim_iff`: `(grim, grim)` SPNE iff `1 / 2 ≤ δ`.
* `Cslib.GameTheory.Reputation.not_isSPNE_naiveGrim`: Exercise 27.3.
* `Cslib.GameTheory.Reputation.isSPNE_titForTat_iff`: Exercise 27.2 exact characterization
  (`δ = 1 / 2`).
* `Cslib.GameTheory.Reputation.personalizedGrim_incentive_iff`: Exercise 27.5 (`N / (N + 1) ≤ δ`).
* `Cslib.GameTheory.Reputation.entryFee_deters_whitewashing_iff`: §27.3 (`1 / δ ≤ f`).
* `Cslib.GameTheory.Reputation.pyd_incentive_iff`, `pyd_strict_incentive_of_gt_half`: §27.3 and
  Exercise 27.4 (`1 / 2 ≤ δ` and strict optimality for `1 / 2 < δ`).

## References

* [E. Friedman, P. Resnick, and R. Sami, *Manipulation-Resistant Reputation
  Systems*][FriedmanResnickSami2007]
* [E. J. Friedman and P. Resnick, *The Social Cost of Cheap Pseudonyms*][FriedmanResnick2001]
-/

public section

namespace Cslib.GameTheory.Reputation

/-! ### Stage Prisoner's Dilemma -/

/-- Stage-game action in the Prisoner's Dilemma [FriedmanResnickSami2007, §27.2, p. 680]. -/
inductive PDAction : Type
  | cooperate
  | defect
  deriving DecidableEq, Repr

/-- Stage payoff to the row player in the Prisoner's Dilemma of [FriedmanResnickSami2007, §27.2,
p. 680]: `π(C, C) = 1`, `π(D, D) = 0`, `π(D, C) = 2`, and `π(C, D) = -1`. -/
@[expose] def pdPayoff : PDAction → PDAction → ℝ
  | .cooperate, .cooperate => 1
  | .defect, .defect => 0
  | .defect, .cooperate => 2
  | .cooperate, .defect => -1

/-- Sum of both players' stage payoffs [FriedmanResnickSami2007, §27.3, p. 682]. -/
@[expose] def pdWelfare (a b : PDAction) : ℝ :=
  pdPayoff a b + pdPayoff b a

theorem pdPayoff_defect_gt_cooperate (b : PDAction) :
    pdPayoff .cooperate b < pdPayoff .defect b := by
  cases b <;> norm_num [pdPayoff]

theorem abs_pdPayoff_le_two (a b : PDAction) : |pdPayoff a b| ≤ 2 := by
  cases a <;> cases b <;> norm_num [pdPayoff]

theorem pdWelfare_le_two (a b : PDAction) : pdWelfare a b ≤ 2 := by
  cases a <;> cases b <;> norm_num [pdWelfare, pdPayoff]

theorem pdWelfare_eq_two_iff (a b : PDAction) :
    pdWelfare a b = 2 ↔ a = .cooperate ∧ b = .cooperate := by
  cases a <;> cases b <;> norm_num [pdWelfare, pdPayoff]

/-! ### Normalized discounted average payoffs -/

/-- Normalized discounted average payoff `(1 - δ) * ∑_{t=0}^∞ δ^t u_t`
[FriedmanResnickSami2007, §27.2, p. 681]. -/
noncomputable def discountedPayoff (δ : ℝ) (u : ℕ → ℝ) : ℝ :=
  (1 - δ) * ∑' t : ℕ, δ ^ t * u t

theorem summable_pow_mul_of_bdd {δ B : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) {u : ℕ → ℝ}
    (hu : ∀ t, |u t| ≤ B) : Summable fun t : ℕ => δ ^ t * u t := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hδ₀ hδ₁).mul_left B) fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ₀ t), mul_comm]
  exact mul_le_mul_of_nonneg_right (hu t) (pow_nonneg hδ₀ t)

/-- **Exercise 27.1** ([FriedmanResnickSami2007, p. 696]): if the stage payoff is constant `c`,
then the normalized discounted average payoff equals `c`. -/
@[simp]
theorem discountedPayoff_const {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (c : ℝ) :
    discountedPayoff δ (fun _ => c) = c := by
  have hne : 1 - δ ≠ 0 := sub_ne_zero.mpr hδ₁.ne'
  rw [discountedPayoff, tsum_mul_right, tsum_geometric_of_lt_one hδ₀ hδ₁, ← mul_assoc,
    mul_inv_cancel₀ hne, one_mul]

/-- One-step Bellman decomposition of `discountedPayoff` on bounded streams. -/
theorem discountedPayoff_cons {δ B : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) {u : ℕ → ℝ}
    (hu : ∀ t, |u t| ≤ B) :
    discountedPayoff δ u = (1 - δ) * u 0 + δ * discountedPayoff δ (fun t => u (t + 1)) := by
  have hsum := summable_pow_mul_of_bdd hδ₀ hδ₁ hu
  have htail : (fun t : ℕ => δ ^ (t + 1) * u (t + 1)) = fun t => δ * (δ ^ t * u (t + 1)) :=
    funext fun _ => by ring
  rw [discountedPayoff, hsum.tsum_eq_zero_add, pow_zero, one_mul, htail, tsum_mul_left,
    discountedPayoff]
  ring

private theorem discountedPayoff_ite_zero {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (a c : ℝ) :
    discountedPayoff δ (fun t => if t = 0 then a else c) = (1 - δ) * a + δ * c := by
  have hbd : ∀ t : ℕ, |(if t = 0 then a else c)| ≤ |a| + |c| := fun t => by
    split_ifs <;> linarith [abs_nonneg a, abs_nonneg c]
  rw [discountedPayoff_cons hδ₀ hδ₁ hbd]
  simp [discountedPayoff_const hδ₀ hδ₁]

theorem discountedPayoff_le_of_forall_le {δ B : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) {u v : ℕ → ℝ}
    (hu : ∀ t, |u t| ≤ B) (hv : ∀ t, |v t| ≤ B) (huv : ∀ t, u t ≤ v t) :
    discountedPayoff δ u ≤ discountedPayoff δ v :=
  mul_le_mul_of_nonneg_left
    ((summable_pow_mul_of_bdd hδ₀ hδ₁ hu).tsum_le_tsum
      (fun t => mul_le_mul_of_nonneg_left (huv t) (pow_nonneg hδ₀ t))
      (summable_pow_mul_of_bdd hδ₀ hδ₁ hv))
    (by linarith)

theorem abs_discountedPayoff_le {δ B : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) {u : ℕ → ℝ}
    (hu : ∀ t, |u t| ≤ B) : |discountedPayoff δ u| ≤ B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hu 0)
  refine abs_le.mpr ⟨?_, ?_⟩
  · simpa [discountedPayoff_const hδ₀ hδ₁] using discountedPayoff_le_of_forall_le hδ₀ hδ₁
      (fun _ => by simp [abs_of_nonneg hB]) hu fun t => (abs_le.mp (hu t)).1
  · simpa [discountedPayoff_const hδ₀ hδ₁] using discountedPayoff_le_of_forall_le hδ₀ hδ₁
      hu (fun _ => by simp [abs_of_nonneg hB]) fun t => (abs_le.mp (hu t)).2

/-! ### Public histories, continuation payoffs, and the one-shot deviation principle -/

/-- Outcome of a single round of the repeated Prisoner's Dilemma. -/
structure PDRound where
  /-- Action played by player 1. -/
  act₁ : PDAction
  /-- Action played by player 2. -/
  act₂ : PDAction
  deriving DecidableEq, Repr

/-- Swap the two players' coordinates of a stage outcome. -/
def PDRound.swap (r : PDRound) : PDRound :=
  ⟨r.act₂, r.act₁⟩

@[simp]
theorem PDRound.swap_swap (r : PDRound) : r.swap.swap = r := by
  cases r; rfl

/-- Finite public history of past stage outcomes, in chronological order. -/
abbrev PDHistory := List PDRound

/-- Pure public-history strategy in the infinitely repeated Prisoner's Dilemma. -/
abbrev PDStrategy := PDHistory → PDAction

/-- Public history after `t` additional rounds of play from `h` under `(σ₁, σ₂)`. -/
def historyAfter (σ₁ σ₂ : PDStrategy) (h : PDHistory) : ℕ → PDHistory
  | 0 => h
  | t + 1 => historyAfter σ₁ σ₂ (h ++ [⟨σ₁ h, σ₂ h⟩]) t

/-- Stage outcome `t` rounds after `h` under `(σ₁, σ₂)`. -/
def roundAt (σ₁ σ₂ : PDStrategy) (h : PDHistory) (t : ℕ) : PDRound :=
  let ht := historyAfter σ₁ σ₂ h t
  ⟨σ₁ ht, σ₂ ht⟩

@[simp]
theorem historyAfter_zero (σ₁ σ₂ : PDStrategy) (h : PDHistory) :
    historyAfter σ₁ σ₂ h 0 = h := by
  rfl

@[simp]
theorem roundAt_zero (σ₁ σ₂ : PDStrategy) (h : PDHistory) :
    roundAt σ₁ σ₂ h 0 = ⟨σ₁ h, σ₂ h⟩ := by
  rfl

@[simp]
theorem roundAt_succ (σ₁ σ₂ : PDStrategy) (h : PDHistory) (t : ℕ) :
    roundAt σ₁ σ₂ h (t + 1) = roundAt σ₁ σ₂ (h ++ [⟨σ₁ h, σ₂ h⟩]) t := by
  rfl

theorem length_le_length_historyAfter (σ₁ σ₂ : PDStrategy) (h : PDHistory) (t : ℕ) :
    h.length ≤ (historyAfter σ₁ σ₂ h t).length := by
  induction t generalizing h with
  | zero => exact le_rfl
  | succ t ih => exact (by simp : h.length ≤ (h ++ [PDRound.mk (σ₁ h) (σ₂ h)]).length).trans (ih _)

/-- Player 1's normalized discounted continuation payoff from public history `h`. -/
noncomputable def contPayoff₁ (δ : ℝ) (σ₁ σ₂ : PDStrategy) (h : PDHistory) : ℝ :=
  discountedPayoff δ fun t => pdPayoff (roundAt σ₁ σ₂ h t).act₁ (roundAt σ₁ σ₂ h t).act₂

/-- Player 2's normalized discounted continuation payoff from public history `h`. -/
noncomputable def contPayoff₂ (δ : ℝ) (σ₁ σ₂ : PDStrategy) (h : PDHistory) : ℝ :=
  discountedPayoff δ fun t => pdPayoff (roundAt σ₁ σ₂ h t).act₂ (roundAt σ₁ σ₂ h t).act₁

private def swapStrategy (σ : PDStrategy) : PDStrategy :=
  fun h => σ (h.map PDRound.swap)

private theorem historyAfter_swapStrategy (σ₁ σ₂ : PDStrategy) (h : PDHistory) (t : ℕ) :
    historyAfter (swapStrategy σ₂) (swapStrategy σ₁) (h.map PDRound.swap) t =
      (historyAfter σ₁ σ₂ h t).map PDRound.swap := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    simp only [historyAfter, ← ih]
    congr 1
    simp [swapStrategy, List.map_map, Function.comp_def, PDRound.swap]

private theorem contPayoff₂_eq_contPayoff₁_swap (δ : ℝ) (σ₁ σ₂ : PDStrategy) (h : PDHistory) :
    contPayoff₂ δ σ₁ σ₂ h =
      contPayoff₁ δ (swapStrategy σ₂) (swapStrategy σ₁) (h.map PDRound.swap) := by
  unfold contPayoff₂ contPayoff₁ roundAt
  congr 1; ext t
  simp [swapStrategy, historyAfter_swapStrategy, List.map_map, Function.comp_def, PDRound.swap]

theorem contPayoff₁_bellman {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (σ₁ σ₂ : PDStrategy)
    (h : PDHistory) :
    contPayoff₁ δ σ₁ σ₂ h =
      (1 - δ) * pdPayoff (σ₁ h) (σ₂ h) + δ * contPayoff₁ δ σ₁ σ₂ (h ++ [⟨σ₁ h, σ₂ h⟩]) :=
  discountedPayoff_cons hδ₀ hδ₁ fun _ => abs_pdPayoff_le_two _ _

theorem contPayoff₂_bellman {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (σ₁ σ₂ : PDStrategy)
    (h : PDHistory) :
    contPayoff₂ δ σ₁ σ₂ h =
      (1 - δ) * pdPayoff (σ₂ h) (σ₁ h) + δ * contPayoff₂ δ σ₁ σ₂ (h ++ [⟨σ₁ h, σ₂ h⟩]) :=
  discountedPayoff_cons hδ₀ hδ₁ fun _ => abs_pdPayoff_le_two _ _

theorem abs_contPayoff₁_le_two {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (σ₁ σ₂ : PDStrategy)
    (h : PDHistory) : |contPayoff₁ δ σ₁ σ₂ h| ≤ 2 :=
  abs_discountedPayoff_le hδ₀ hδ₁ fun _ => abs_pdPayoff_le_two _ _

theorem abs_contPayoff₂_le_two {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (σ₁ σ₂ : PDStrategy)
    (h : PDHistory) : |contPayoff₂ δ σ₁ σ₂ h| ≤ 2 :=
  abs_discountedPayoff_le hδ₀ hδ₁ fun _ => abs_pdPayoff_le_two _ _

/-- Strategy pair `(σ₁, σ₂)` is a **subgame-perfect Nash equilibrium (SPNE)** at discount factor
`δ` if neither player can strictly increase their continuation payoff after any finite public
history `h` [FriedmanResnickSami2007, §27.2, p. 681]. -/
def IsSPNE (δ : ℝ) (σ₁ σ₂ : PDStrategy) : Prop :=
  (∀ h : PDHistory, ∀ σ₁' : PDStrategy, contPayoff₁ δ σ₁' σ₂ h ≤ contPayoff₁ δ σ₁ σ₂ h) ∧
    ∀ h : PDHistory, ∀ σ₂' : PDStrategy, contPayoff₂ δ σ₁ σ₂' h ≤ contPayoff₂ δ σ₁ σ₂ h

/-- Absence of profitable one-shot deviations for both players at every finite public history `h`
[FriedmanResnickSami2007, §27.2, p. 681]. -/
def NoOneShotDev (δ : ℝ) (σ₁ σ₂ : PDStrategy) : Prop :=
  (∀ h : PDHistory, ∀ a : PDAction,
    (1 - δ) * pdPayoff a (σ₂ h) + δ * contPayoff₁ δ σ₁ σ₂ (h ++ [⟨a, σ₂ h⟩]) ≤
      contPayoff₁ δ σ₁ σ₂ h) ∧
  ∀ h : PDHistory, ∀ b : PDAction,
    (1 - δ) * pdPayoff b (σ₁ h) + δ * contPayoff₂ δ σ₁ σ₂ (h ++ [⟨σ₁ h, b⟩]) ≤
      contPayoff₂ δ σ₁ σ₂ h

private theorem historyAfter_congr_of_gt {σ₁ σ₁' σ₂ σ₂' : PDStrategy} {n : ℕ}
    (h₁ : ∀ h', n < h'.length → σ₁' h' = σ₁ h')
    (h₂ : ∀ h', n < h'.length → σ₂' h' = σ₂ h') :
    ∀ t (h : PDHistory), n < h.length →
      historyAfter σ₁' σ₂' h t = historyAfter σ₁ σ₂ h t := by
  intro t
  induction t with
  | zero => intro _ _; rfl
  | succ t ih =>
    intro h hn
    simp only [historyAfter, h₁ h hn, h₂ h hn]
    exact ih _ (by simp [List.length_append]; omega)

private theorem roundAt_congr_of_gt {σ₁ σ₁' σ₂ σ₂' : PDStrategy} {n : ℕ}
    (h₁ : ∀ h', n < h'.length → σ₁' h' = σ₁ h')
    (h₂ : ∀ h', n < h'.length → σ₂' h' = σ₂ h') {h : PDHistory} (hn : n < h.length) (t : ℕ) :
    roundAt σ₁' σ₂' h t = roundAt σ₁ σ₂ h t := by
  have hlen : n < (historyAfter σ₁ σ₂ h t).length :=
    hn.trans_le (length_le_length_historyAfter σ₁ σ₂ h t)
  have heq := historyAfter_congr_of_gt h₁ h₂ t h hn
  simp only [roundAt, heq, h₁ _ hlen, h₂ _ hlen]

private theorem forall_contPayoff₁_le_iff {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
    (σ₁ σ₂ : PDStrategy) :
    (∀ h : PDHistory, ∀ σ₁' : PDStrategy, contPayoff₁ δ σ₁' σ₂ h ≤ contPayoff₁ δ σ₁ σ₂ h) ↔
      ∀ h : PDHistory, ∀ a : PDAction,
        (1 - δ) * pdPayoff a (σ₂ h) + δ * contPayoff₁ δ σ₁ σ₂ (h ++ [⟨a, σ₂ h⟩]) ≤
          contPayoff₁ δ σ₁ σ₂ h := by
  refine ⟨fun h₁ h a => ?_, fun h₁ h σ₁' => ?_⟩
  · let σ₁' : PDStrategy := fun h' => if h' = h then a else σ₁ h'
    have hgt (h' : PDHistory) (hlen : h.length < h'.length) : σ₁' h' = σ₁ h' :=
      ite_eq_right fun heq => Nat.lt_irrefl _ (heq ▸ hlen)
    have htail : contPayoff₁ δ σ₁' σ₂ (h ++ [⟨a, σ₂ h⟩]) =
        contPayoff₁ δ σ₁ σ₂ (h ++ [⟨a, σ₂ h⟩]) :=
      congrArg (discountedPayoff δ) (funext fun t => by
        rw [roundAt_congr_of_gt hgt (fun _ _ => rfl) (by simp)])
    have hle := h₁ h σ₁'
    rwa [contPayoff₁_bellman hδ₀ hδ₁ σ₁' σ₂ h, show σ₁' h = a from ite_eq_left rfl, htail] at hle
  · have hbd (n : ℕ) : ∀ h' : PDHistory,
        contPayoff₁ δ σ₁' σ₂ h' - contPayoff₁ δ σ₁ σ₂ h' ≤ 4 * δ ^ n := by
      induction n with
      | zero =>
        intro h'
        linarith [(abs_le.mp (abs_contPayoff₁_le_two hδ₀ hδ₁ σ₁' σ₂ h')).2,
          (abs_le.mp (abs_contPayoff₁_le_two hδ₀ hδ₁ σ₁ σ₂ h')).1, pow_zero δ]
      | succ n ih =>
        intro h'
        rw [contPayoff₁_bellman hδ₀ hδ₁ σ₁' σ₂ h', pow_succ']
        linarith [mul_le_mul_of_nonneg_left (ih (h' ++ [⟨σ₁' h', σ₂ h'⟩])) hδ₀, h₁ h' (σ₁' h')]
    have hlim : Filter.Tendsto (fun n : ℕ => 4 * δ ^ n) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ₀ hδ₁).const_mul 4
    linarith [le_of_tendsto_of_tendsto' tendsto_const_nhds hlim fun n => hbd n h]

/-- **One-shot deviation principle** for the infinitely repeated Prisoner's Dilemma
([FriedmanResnickSami2007, §27.2, p. 681]): for `0 ≤ δ < 1`, `(σ₁, σ₂)` is an SPNE if and only if
neither player has a profitable one-shot deviation after any finite history. -/
theorem isSPNE_iff_noOneShotDev {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (σ₁ σ₂ : PDStrategy) :
    IsSPNE δ σ₁ σ₂ ↔ NoOneShotDev δ σ₁ σ₂ := by
  have hmap_inv (h : PDHistory) : (h.map PDRound.swap).map PDRound.swap = h := by
    simp [List.map_map, Function.comp_def]
  have hsw_inv (σ : PDStrategy) : swapStrategy (swapStrategy σ) = σ := by
    ext h
    simp [swapStrategy, hmap_inv]
  refine and_congr (forall_contPayoff₁_le_iff hδ₀ hδ₁ σ₁ σ₂) ?_
  have h2 := forall_contPayoff₁_le_iff hδ₀ hδ₁ (swapStrategy σ₂) (swapStrategy σ₁)
  refine ⟨fun hp2 h b => ?_, fun hosd2 h σ₂' => ?_⟩
  · have hstep := (h2.mp fun h' τ => by
      have := hp2 (h'.map PDRound.swap) (swapStrategy τ)
      rwa [contPayoff₂_eq_contPayoff₁_swap, contPayoff₂_eq_contPayoff₁_swap,
        hsw_inv, hmap_inv] at this) (h.map PDRound.swap) b
    rw [contPayoff₂_eq_contPayoff₁_swap, contPayoff₂_eq_contPayoff₁_swap]
    simpa [swapStrategy, hmap_inv, PDRound.swap] using hstep
  · rw [contPayoff₂_eq_contPayoff₁_swap, contPayoff₂_eq_contPayoff₁_swap]
    exact (h2.mpr fun h' b => by
      have := hosd2 (h'.map PDRound.swap) b
      rw [contPayoff₂_eq_contPayoff₁_swap, contPayoff₂_eq_contPayoff₁_swap] at this
      simpa [swapStrategy, hmap_inv, PDRound.swap] using this) _ _

private theorem noOneShotDev_of_swapStrategy {δ : ℝ} {σ₁ σ₂ : PDStrategy}
    (hsw₁ : swapStrategy σ₁ = σ₂) (hsw₂ : swapStrategy σ₂ = σ₁)
    (h₁ : ∀ h a, (1 - δ) * pdPayoff a (σ₂ h) + δ * contPayoff₁ δ σ₁ σ₂ (h ++ [⟨a, σ₂ h⟩]) ≤
      contPayoff₁ δ σ₁ σ₂ h) :
    NoOneShotDev δ σ₁ σ₂ := by
  refine ⟨h₁, fun h b => ?_⟩
  have hsym := h₁ (h.map PDRound.swap) b
  have hs1 : σ₂ (h.map PDRound.swap) = σ₁ h := congrFun hsw₂ h
  rw [contPayoff₂_eq_contPayoff₁_swap, contPayoff₂_eq_contPayoff₁_swap, hsw₁, hsw₂]
  simpa [hs1, PDRound.swap] using hsym

/-! ### Grim trigger, Naive Grim, and Tit-for-Tat -/

/-- Whether every round in history `h` was mutual cooperation `(C, C)`. -/
def allCooperated (h : PDHistory) : Bool :=
  h.all fun r => decide (r.act₁ = .cooperate ∧ r.act₂ = .cooperate)

/-- **Grim trigger** strategy: cooperate unless *any* player has defected in a previous round
[FriedmanResnickSami2007, §27.2, p. 681]. -/
def grim (h : PDHistory) : PDAction :=
  if allCooperated h then .cooperate else .defect

private theorem allCooperated_snoc (h : PDHistory) (a b : PDAction) :
    allCooperated (h ++ [⟨a, b⟩]) =
      (allCooperated h && decide (a = .cooperate ∧ b = .cooperate)) := by
  simp only [allCooperated, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

private theorem historyAfter_grim_of_allCooperated {h : PDHistory} (hc : allCooperated h = true)
    (t : ℕ) : allCooperated (historyAfter grim grim h t) = true := by
  induction t generalizing h with
  | zero => exact hc
  | succ t ih =>
    exact ih (by
      simp only [allCooperated_snoc, grim, hc, ↓reduceIte, and_self, decide_true, Bool.and_self])

private theorem historyAfter_grim_of_not_allCooperated {h : PDHistory}
    (hc : allCooperated h = false) (t : ℕ) :
    allCooperated (historyAfter grim grim h t) = false := by
  induction t generalizing h with
  | zero => exact hc
  | succ t ih => exact ih (by simp only [allCooperated_snoc, hc, Bool.false_and])

private theorem allCooperated_map_swap (h : PDHistory) :
    allCooperated (h.map PDRound.swap) = allCooperated h := by
  simp only [allCooperated, List.all_map]
  exact congrArg h.all (funext fun ⟨a₁, a₂⟩ => by cases a₁ <;> cases a₂ <;> rfl)

private theorem swapStrategy_grim : swapStrategy grim = grim := by
  ext h
  simp [swapStrategy, grim, allCooperated_map_swap]

theorem contPayoff₁_grim {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (h : PDHistory) :
    contPayoff₁ δ grim grim h = if allCooperated h then 1 else 0 := by
  cases hc : allCooperated h
  · simp [contPayoff₁, roundAt, grim, historyAfter_grim_of_not_allCooperated hc, pdPayoff,
      discountedPayoff_const hδ₀ hδ₁]
  · simp [contPayoff₁, roundAt, grim, historyAfter_grim_of_allCooperated hc, pdPayoff,
      discountedPayoff_const hδ₀ hδ₁]

theorem contPayoff₂_grim {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (h : PDHistory) :
    contPayoff₂ δ grim grim h = if allCooperated h then 1 else 0 := by
  rw [contPayoff₂_eq_contPayoff₁_swap, swapStrategy_grim, contPayoff₁_grim hδ₀ hδ₁,
    allCooperated_map_swap]

/-- **Grim trigger SPNE characterization** ([FriedmanResnickSami2007, §27.2, p. 681]):
for `0 ≤ δ < 1`, `(grim, grim)` is a subgame-perfect Nash equilibrium if and only if
`1 / 2 ≤ δ`. -/
theorem isSPNE_grim_iff {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) :
    IsSPNE δ grim grim ↔ 1 / 2 ≤ δ := by
  rw [isSPNE_iff_noOneShotDev hδ₀ hδ₁]
  constructor
  · intro h
    have hosd := h.1 [] .defect
    rw [contPayoff₁_grim hδ₀ hδ₁, contPayoff₁_grim hδ₀ hδ₁] at hosd
    simp only [grim, allCooperated, List.nil_append, List.all_nil, List.all_cons, reduceCtorEq,
      false_and, decide_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, pdPayoff] at hosd
    linarith
  · intro hδ
    refine noOneShotDev_of_swapStrategy swapStrategy_grim swapStrategy_grim fun h a => ?_
    rw [contPayoff₁_grim hδ₀ hδ₁ h, contPayoff₁_grim hδ₀ hδ₁, allCooperated_snoc]
    cases hc : allCooperated h <;> cases a <;>
      simp only [grim, hc, Bool.false_and, Bool.true_and, and_self, and_false, false_and,
        reduceCtorEq, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, pdPayoff] <;>
      linarith

/-- Naive Grim for player 1: cooperate unless *player 2* has defected in a previous round
[FriedmanResnickSami2007, Exercise 27.3, p. 696]. -/
def naiveGrim₁ (h : PDHistory) : PDAction :=
  if h.all (fun r => decide (r.act₂ = .cooperate)) then .cooperate else .defect

/-- Naive Grim for player 2: cooperate unless *player 1* has defected in a previous round
[FriedmanResnickSami2007, Exercise 27.3, p. 696]. -/
def naiveGrim₂ (h : PDHistory) : PDAction :=
  if h.all (fun r => decide (r.act₁ = .cooperate)) then .cooperate else .defect

private theorem roundAt_naiveGrim_both_defected {h : PDHistory}
    (h₁ : h.all (fun r => decide (r.act₁ = .cooperate)) = false)
    (h₂ : h.all (fun r => decide (r.act₂ = .cooperate)) = false) (t : ℕ) :
    roundAt naiveGrim₁ naiveGrim₂ h t = ⟨.defect, .defect⟩ := by
  induction t generalizing h with
  | zero => simp [roundAt_zero, naiveGrim₁, naiveGrim₂, h₁, h₂]
  | succ t ih =>
    exact ih
      (by simp [List.all_append, h₁])
      (by simp [List.all_append, h₂])

/-- **Exercise 27.3** ([FriedmanResnickSami2007, p. 696]): defining Grim as "cooperate unless the
*other* player has defected" fails subgame perfection for *every* `0 ≤ δ < 1`, because after the
off-path history `[⟨D, C⟩]` player 1 is required to cooperate once against player 2's permanent
defection (`-1` instead of `0`). -/
theorem not_isSPNE_naiveGrim {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) :
    ¬ IsSPNE δ naiveGrim₁ naiveGrim₂ := by
  rw [isSPNE_iff_noOneShotDev hδ₀ hδ₁]
  rintro ⟨h₁, _⟩
  let h0 : PDHistory := [⟨.defect, .cooperate⟩]
  have hzero (a : PDAction) :
      contPayoff₁ δ naiveGrim₁ naiveGrim₂ (h0 ++ [⟨a, .defect⟩]) = 0 := by
    simp [contPayoff₁, roundAt_naiveGrim_both_defected (h := h0 ++ [⟨a, .defect⟩]) rfl rfl,
      pdPayoff, discountedPayoff_const hδ₀ hδ₁]
  have hosd := h₁ h0 .defect
  rw [contPayoff₁_bellman hδ₀ hδ₁ naiveGrim₁ naiveGrim₂ h0] at hosd
  simp only [naiveGrim₁, naiveGrim₂, h0, List.all_cons, List.all_nil, reduceCtorEq, decide_true,
    decide_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, hzero, pdPayoff] at hosd
  linarith

/-- **Tit-for-Tat** for player 1: cooperate initially, then copy player 2's last action
[FriedmanResnickSami2007, Exercise 27.2, p. 696]. -/
def titForTat₁ (h : PDHistory) : PDAction :=
  match h.getLast? with
  | none => .cooperate
  | some r => r.act₂

/-- **Tit-for-Tat** for player 2: cooperate initially, then copy player 1's last action
[FriedmanResnickSami2007, Exercise 27.2, p. 696]. -/
def titForTat₂ (h : PDHistory) : PDAction :=
  match h.getLast? with
  | none => .cooperate
  | some r => r.act₁

private theorem roundAt_titForTat_of_getLast {h : PDHistory} {r : PDRound}
    (hl : h.getLast? = some r) :
    ∀ t, roundAt titForTat₁ titForTat₂ h t = if Even t then r.swap else r := by
  intro t
  induction t generalizing h r with
  | zero =>
    rw [roundAt_zero]
    simp [titForTat₁, titForTat₂, hl, PDRound.swap]
  | succ t ih =>
    have hl' : (h ++ [PDRound.mk (titForTat₁ h) (titForTat₂ h)]).getLast? = some r.swap := by
      simp [titForTat₁, titForTat₂, hl, PDRound.swap]
    rw [roundAt_succ, ih hl']
    by_cases ht : Even t <;> simp [Nat.even_add_one, ht]

private theorem contPayoff₁_titForTat_some {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) {h : PDHistory}
    {r : PDRound} (hl : h.getLast? = some r) :
    contPayoff₁ δ titForTat₁ titForTat₂ h =
      (pdPayoff r.act₂ r.act₁ + δ * pdPayoff r.act₁ r.act₂) / (1 + δ) := by
  have h1 : contPayoff₁ δ titForTat₁ titForTat₂ h =
      (1 - δ) * pdPayoff r.act₂ r.act₁ +
        δ * contPayoff₁ δ titForTat₁ titForTat₂ (h ++ [⟨r.act₂, r.act₁⟩]) := by
    simpa [titForTat₁, titForTat₂, hl] using contPayoff₁_bellman hδ₀ hδ₁ titForTat₁ titForTat₂ h
  set h1Hist := h ++ [⟨r.act₂, r.act₁⟩]
  have hl1 : h1Hist.getLast? = some ⟨r.act₂, r.act₁⟩ := List.getLast?_concat ..
  have h2 : contPayoff₁ δ titForTat₁ titForTat₂ h1Hist =
      (1 - δ) * pdPayoff r.act₁ r.act₂ +
        δ * contPayoff₁ δ titForTat₁ titForTat₂ (h1Hist ++ [⟨r.act₁, r.act₂⟩]) := by
    simpa [titForTat₁, titForTat₂, hl1] using
      contPayoff₁_bellman hδ₀ hδ₁ titForTat₁ titForTat₂ h1Hist
  set h2Hist := h1Hist ++ [⟨r.act₁, r.act₂⟩]
  have hl2 : h2Hist.getLast? = some r := by
    cases r; exact List.getLast?_concat ..
  have hper : contPayoff₁ δ titForTat₁ titForTat₂ h2Hist =
      contPayoff₁ δ titForTat₁ titForTat₂ h :=
    congrArg (discountedPayoff δ) (funext fun t => by
      rw [roundAt_titForTat_of_getLast hl2 t, roundAt_titForTat_of_getLast hl t])
  rw [hper] at h2
  rw [h2] at h1
  field_simp [(by linarith : (1 + δ) ≠ 0)]
  nlinarith

private theorem swapStrategy_titForTat₁ : swapStrategy titForTat₁ = titForTat₂ := by
  ext h
  simp only [swapStrategy, titForTat₁, titForTat₂, List.getLast?_map]
  cases h.getLast? <;> rfl

private theorem swapStrategy_titForTat₂ : swapStrategy titForTat₂ = titForTat₁ := by
  ext h
  simp only [swapStrategy, titForTat₁, titForTat₂, List.getLast?_map]
  cases h.getLast? <;> rfl

private theorem contPayoff₂_titForTat_some {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) {h : PDHistory}
    {r : PDRound} (hl : h.getLast? = some r) :
    contPayoff₂ δ titForTat₁ titForTat₂ h =
      (pdPayoff r.act₁ r.act₂ + δ * pdPayoff r.act₂ r.act₁) / (1 + δ) := by
  rw [contPayoff₂_eq_contPayoff₁_swap, swapStrategy_titForTat₂, swapStrategy_titForTat₁,
    contPayoff₁_titForTat_some hδ₀ hδ₁ (r := r.swap) (by simp [List.getLast?_map, hl])]
  rfl

private theorem contPayoff₁_titForTat_nil {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) :
    contPayoff₁ δ titForTat₁ titForTat₂ [] = 1 := by
  rw [contPayoff₁_bellman hδ₀ hδ₁,
    contPayoff₁_titForTat_some hδ₀ hδ₁ (List.getLast?_concat ..)]
  have hpos : 0 < 1 + δ := by linarith
  simp only [titForTat₁, titForTat₂, List.getLast?_nil, pdPayoff]
  field_simp [hpos.ne']
  ring

private theorem contPayoff₂_titForTat_nil {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) :
    contPayoff₂ δ titForTat₁ titForTat₂ [] = 1 := by
  rw [contPayoff₂_eq_contPayoff₁_swap, swapStrategy_titForTat₂, swapStrategy_titForTat₁]
  exact contPayoff₁_titForTat_nil hδ₀ hδ₁

/-- **Tit-for-Tat SPNE characterization** ([FriedmanResnickSami2007, Exercise 27.2, p. 696]):
under NRTV's stage payoffs `(1, 2, 0, -1)`, `(titForTat₁, titForTat₂)` is an SPNE if and only if
`δ = 1 / 2`. For `δ < 1 / 2`, player 1 profitably defects at `[]`; for `1 / 2 < δ < 1`, player 2
profitably forgives (plays `C`) after `[⟨D, C⟩]` to restore `(C, C)` instead of alternating. -/
theorem isSPNE_titForTat_iff {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) :
    IsSPNE δ titForTat₁ titForTat₂ ↔ δ = 1 / 2 := by
  rw [isSPNE_iff_noOneShotDev hδ₀ hδ₁]
  have hpos : 0 < 1 + δ := by linarith
  constructor
  · rintro ⟨h₁, h₂⟩
    have hlo : 1 / 2 ≤ δ := by
      have hosd := mul_le_mul_of_nonneg_right (h₁ [] .defect) hpos.le
      rw [contPayoff₁_titForTat_nil hδ₀ hδ₁,
        contPayoff₁_titForTat_some hδ₀ hδ₁ (List.getLast?_concat ..)] at hosd
      simp only [titForTat₂, List.getLast?_nil, pdPayoff] at hosd
      field_simp [hpos.ne'] at hosd
      nlinarith
    have hhi : δ ≤ 1 / 2 := by
      let h0 : PDHistory := [⟨.defect, .cooperate⟩]
      have hl0 : h0.getLast? = some ⟨.defect, .cooperate⟩ := rfl
      have hosd := mul_le_mul_of_nonneg_right (h₂ h0 .cooperate) hpos.le
      rw [contPayoff₂_titForTat_some hδ₀ hδ₁ hl0,
        contPayoff₂_titForTat_some hδ₀ hδ₁ (List.getLast?_concat ..)] at hosd
      simp only [titForTat₁, hl0, pdPayoff] at hosd
      field_simp [hpos.ne'] at hosd
      nlinarith
    linarith
  · rintro rfl
    refine noOneShotDev_of_swapStrategy swapStrategy_titForTat₁ swapStrategy_titForTat₂
      fun h a => ?_
    cases hl : h.getLast? with
    | none =>
      obtain rfl := List.getLast?_eq_none_iff.mp hl
      rw [contPayoff₁_titForTat_nil hδ₀ hδ₁,
        contPayoff₁_titForTat_some hδ₀ hδ₁ (List.getLast?_concat ..)]
      cases a <;> norm_num [titForTat₂, pdPayoff]
    | some r =>
      rcases r with ⟨a₁, a₂⟩
      rw [contPayoff₁_titForTat_some hδ₀ hδ₁ hl,
        contPayoff₁_titForTat_some hδ₀ hδ₁ (List.getLast?_concat ..)]
      cases a₁ <;> cases a₂ <;> cases a <;> norm_num [titForTat₂, hl, pdPayoff]

theorem not_isSPNE_titForTat_of_ne {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (hne : δ ≠ 1 / 2) :
    ¬ IsSPNE δ titForTat₁ titForTat₂ :=
  mt (isSPNE_titForTat_iff hδ₀ hδ₁).mp hne

/-! ### Personalized-Grim under random matching (§27.2 & Exercise 27.5) -/

/-- Expected normalized discounted payoff from defecting once against a current partner under
`personalized-Grim` in a population of `N + 1` players (`N` potential partners, matched uniformly
with probability `1 / N` in each subsequent period): immediate payoff `2`, followed by expected
stage payoff `(N - 1) / N` in every future period [FriedmanResnickSami2007, §27.2, p. 681;
Exercise 27.5, p. 697]. -/
noncomputable def personalizedGrimDevPayoff (δ : ℝ) (N : ℕ) : ℝ :=
  discountedPayoff δ fun t => if t = 0 then 2 else ((N : ℝ) - 1) / (N : ℝ)

/-- **Exercise 27.5** ([FriedmanResnickSami2007, §27.2, p. 681 & p. 697]): in the closed-form
expected stream `personalizedGrimDevPayoff δ N` for `N ≥ 1` potential partners under uniform
`1 / N` matching, Personalized-Grim deters a one-shot defection
(`personalizedGrimDevPayoff δ N ≤ 1`) if and only if `(N : ℝ) / (N + 1) ≤ δ`. -/
theorem personalizedGrim_incentive_iff {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) {N : ℕ}
    (hN : 1 ≤ N) :
    personalizedGrimDevPayoff δ N ≤ 1 ↔ (N : ℝ) / ((N : ℝ) + 1) ≤ δ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  rw [personalizedGrimDevPayoff, discountedPayoff_ite_zero hδ₀ hδ₁, div_le_iff₀ (by positivity)]
  constructor <;> intro h
  · have hmul := mul_le_mul_of_nonneg_right h hNpos.le
    have := div_mul_cancel₀ ((N : ℝ) - 1) hNpos.ne'
    nlinarith
  · rw [show (1 - δ) * 2 + δ * (((N : ℝ) - 1) / (N : ℝ)) =
      (2 * (1 - δ) * (N : ℝ) + δ * ((N : ℝ) - 1)) / (N : ℝ) by field_simp [hNpos.ne'],
      div_le_one hNpos]
    nlinarith

/-! ### Whitewashing entry fees and Pay-Your-Dues (§27.3 & Exercise 27.4) -/

/-- Normalized discounted payoff of paying upfront registration fee `f` once at `t = 0` and
cooperating forever under Reputational-Grim [FriedmanResnickSami2007, §27.3, p. 682]. -/
noncomputable def honestEntryPayoff (δ f : ℝ) : ℝ :=
  discountedPayoff δ fun t => if t = 0 then 1 - f else 1

/-- Normalized discounted payoff of paying `f` at `t = 0`, defecting in round `0` for `2 - f`,
paying `f` again at `t = 1` to whitewash, and cooperating thereafter
[FriedmanResnickSami2007, §27.3, p. 682]. -/
noncomputable def oneShotWhitewashPayoff (δ f : ℝ) : ℝ :=
  discountedPayoff δ fun t => if t = 0 then 2 - f else if t = 1 then 1 - f else 1

/-- Normalized discounted payoff of defecting and whitewashing in every period (`2 - f` per round)
[FriedmanResnickSami2007, §27.3, p. 682]. -/
noncomputable def perpetualWhitewashPayoff (δ f : ℝ) : ℝ :=
  discountedPayoff δ fun _ => 2 - f

theorem honestEntryPayoff_eq {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (f : ℝ) :
    honestEntryPayoff δ f = 1 - (1 - δ) * f := by
  rw [honestEntryPayoff, discountedPayoff_ite_zero hδ₀ hδ₁]
  ring

theorem oneShotWhitewashPayoff_eq {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (f : ℝ) :
    oneShotWhitewashPayoff δ f = 1 + (1 - δ) * (1 - (1 + δ) * f) := by
  have hbd : ∀ t : ℕ,
      |(if t = 0 then 2 - f else if t = 1 then 1 - f else (1 : ℝ))| ≤ |2 - f| + |1 - f| + 1 := by
    intro t
    split_ifs <;> linarith [abs_nonneg (2 - f), abs_nonneg (1 - f), abs_one (α := ℝ)]
  rw [oneShotWhitewashPayoff, discountedPayoff_cons hδ₀ hδ₁ hbd]
  simp only [↓reduceIte, Nat.succ_ne_zero, Nat.add_eq_right]
  rw [discountedPayoff_ite_zero hδ₀ hδ₁]
  ring

/-- **Entry-fee deterrence of whitewashing** ([FriedmanResnickSami2007, §27.3, p. 682];
[FriedmanResnick2001]): for `0 < δ < 1`, in the closed-form discounted streams above, upfront
registration fee `f` deters one-shot whitewashing
(`oneShotWhitewashPayoff δ f ≤ honestEntryPayoff δ f`) if and only if `1 / δ ≤ f`. -/
theorem entryFee_deters_whitewashing_iff {δ f : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    oneShotWhitewashPayoff δ f ≤ honestEntryPayoff δ f ↔ 1 / δ ≤ f := by
  rw [honestEntryPayoff_eq hδ₀.le hδ₁, oneShotWhitewashPayoff_eq hδ₀.le hδ₁, div_le_iff₀ hδ₀]
  have h1 : 0 < 1 - δ := by linarith
  constructor <;> intro h <;> nlinarith

/-- In the closed-form discounted stream `perpetualWhitewashPayoff`, perpetual defect-and-whitewash
is deterred by the exact same registration threshold `1 / δ ≤ f`
[FriedmanResnickSami2007, §27.3, p. 682]. -/
theorem entryFee_deters_perpetual_whitewashing_iff {δ f : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    perpetualWhitewashPayoff δ f ≤ honestEntryPayoff δ f ↔ 1 / δ ≤ f := by
  rw [perpetualWhitewashPayoff, discountedPayoff_const hδ₀.le hδ₁,
    honestEntryPayoff_eq hδ₀.le hδ₁, div_le_iff₀ hδ₀]
  constructor <;> intro h <;> nlinarith

/-- Reputation standing of a pseudonym in the Pay-Your-Dues (`PYD`) norm
[FriedmanResnickSami2007, §27.3, p. 682]. -/
inductive ReputationStanding : Type
  | newcomer
  | goodVeteran
  | badVeteran
  deriving DecidableEq, Repr

/-- **Pay-Your-Dues (`PYD`)** action rule [FriedmanResnickSami2007, §27.3, p. 682]:
cooperate with `goodVeteran`s, defect against `badVeteran`s, and against a `newcomer` cooperate
only if one is also a `newcomer` (veterans defect against newcomers). -/
@[expose] def pydAction (selfStanding partnerStanding : ReputationStanding) : PDAction :=
  match partnerStanding with
  | .goodVeteran => .cooperate
  | .badVeteran => .defect
  | .newcomer =>
    match selfStanding with
    | .newcomer => .cooperate
    | .goodVeteran | .badVeteran => .defect

/-- Next-period standing under `PYD`, allowing optional free whitewashing (`whitewash = true`
resets the pseudonym to `.newcomer`) [FriedmanResnickSami2007, §27.3, p. 682]. -/
@[expose] def pydNextStanding (selfStanding partnerStanding : ReputationStanding) (act : PDAction)
    (whitewash : Bool) : ReputationStanding :=
  if whitewash then .newcomer
  else if selfStanding ≠ .badVeteran ∧ act = pydAction selfStanding partnerStanding then
    .goodVeteran
  else .badVeteran

/-- Stage-payoff gap in the hint to **Exercise 27.4** ([FriedmanResnickSami2007, p. 697]):
against a `goodVeteran` partner playing `PYD`, a `goodVeteran` earns `1` whereas a `newcomer`
paying dues earns `-1`, a gap of `2`. -/
theorem pyd_goodVeteran_vs_newcomer_gap :
    pdPayoff (pydAction .goodVeteran .goodVeteran) (pydAction .goodVeteran .goodVeteran) -
      pdPayoff (pydAction .newcomer .goodVeteran) (pydAction .goodVeteran .newcomer) = 2 := by
  norm_num [pydAction, pdPayoff]

/-- Welfare cost of cheap pseudonyms ([FriedmanResnickSami2007, §27.3, p. 682];
[FriedmanResnick2001]): a veteran–newcomer `PYD` interaction `(D, C)` achieves welfare `1`,
strictly exceeding mutual defection `(0)` while losing `1` unit relative to full cooperation `(2)`.
-/
theorem pyd_newcomer_welfare_bounds :
    pdWelfare .defect .defect <
        pdWelfare (pydAction .goodVeteran .newcomer) (pydAction .newcomer .goodVeteran) ∧
      pdWelfare (pydAction .goodVeteran .newcomer) (pydAction .newcomer .goodVeteran) = 1 ∧
      pdWelfare (pydAction .goodVeteran .newcomer) (pydAction .newcomer .goodVeteran) <
        pdWelfare .cooperate .cooperate := by
  norm_num [pydAction, pdWelfare, pdPayoff]

/-- Continuation value against a community of `goodVeteran` partners when playing `PYD` (with
`badVeteran` whitewashing to `newcomer` when `1 / 2 ≤ δ`, or `max 0 (2 * δ - 1)` in general)
[FriedmanResnickSami2007, §27.3, p. 682; Exercise 27.4, p. 697]. -/
@[expose] def pydContValue (δ : ℝ) : ReputationStanding → ℝ
  | .goodVeteran => 1
  | .newcomer => 2 * δ - 1
  | .badVeteran => 0

/-- **Pay-Your-Dues one-step Bellman threshold** ([FriedmanResnickSami2007, §27.3, p. 682 &
Exercise 27.4, p. 697]; [FriedmanResnick2001]): for `0 ≤ δ < 1`, under the closed-form continuation
values `pydContValue δ`, following `pydAction` without whitewashing at `.newcomer` and
`.goodVeteran` weakly dominates every stage action `a : PDAction` and whitewashing choice
`w : Bool` across all partner standings `partner : ReputationStanding` if and only if
`1 / 2 ≤ δ`. -/
theorem pyd_incentive_iff {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) :
    (∀ s ∈ ({ReputationStanding.newcomer, .goodVeteran} : Set ReputationStanding),
      ∀ (partner : ReputationStanding) (a : PDAction) (w : Bool),
        (1 - δ) * pdPayoff a (pydAction partner s) +
            δ * pydContValue δ (pydNextStanding s partner a w) ≤
          (1 - δ) * pdPayoff (pydAction s partner) (pydAction partner s) +
            δ * pydContValue δ (pydNextStanding s partner (pydAction s partner) false)) ↔
      1 / 2 ≤ δ := by
  constructor
  · intro h
    have hdev := h .goodVeteran (by simp) .goodVeteran .defect true
    simp only [pydAction, pydNextStanding, ↓reduceIte, Bool.false_eq_true, ne_eq, reduceCtorEq,
      not_false_eq_true, and_self, pydContValue, pdPayoff] at hdev
    nlinarith
  · intro hδ s hs partner a w
    rcases hs with rfl | rfl <;>
      cases partner <;> cases a <;> cases w <;>
      simp only [pydAction, pydNextStanding, pydContValue, pdPayoff, ↓reduceIte,
        Bool.false_eq_true, ne_eq, reduceCtorEq, not_false_eq_true, and_self, and_false] <;>
      nlinarith

/-- Strict optimality of `PYD` cooperation in **Exercise 27.4** ([FriedmanResnickSami2007, p. 697]):
when `1 / 2 < δ < 1`, defecting instead of cooperating as a `goodVeteran` or `newcomer` is
strictly unprofitable under any subsequent whitewashing choice `w : Bool`. -/
theorem pyd_strict_incentive_of_gt_half {δ : ℝ} (hδ₀ : 1 / 2 < δ) (hδ₁ : δ < 1)
    (s partner : ReputationStanding)
    (hs : s = .newcomer ∨ s = .goodVeteran)
    (hc : pydAction s partner = .cooperate) (w : Bool) :
    (1 - δ) * pdPayoff .defect (pydAction partner s) +
        δ * pydContValue δ (pydNextStanding s partner .defect w) <
      (1 - δ) * pdPayoff .cooperate (pydAction partner s) +
        δ * pydContValue δ (pydNextStanding s partner .cooperate false) := by
  rcases hs with rfl | rfl <;> cases partner <;> cases w <;>
    simp only [pydAction, reduceCtorEq] at hc <;>
    simp only [pydAction, pydNextStanding, pydContValue, pdPayoff, ↓reduceIte,
      Bool.false_eq_true, ne_eq, reduceCtorEq, not_false_eq_true, and_self, and_false] <;>
    nlinarith

end Cslib.GameTheory.Reputation
