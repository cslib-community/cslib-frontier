/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Bimatrix.Symmetric
public import CslibFrontier.GameTheory.Strategic.ApproxNash
public import CslibFrontier.GameTheory.Strategic.Correlated
public import CslibFrontier.GameTheory.Strategic.Dominance
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for strategic dominance, approximate Nash equilibria, and symmetric games

Nonvacuous checked examples exercising `Strategic.Dominance`, `Strategic.ApproxNash`,
`Strategic.Correlated` (convexity), `Strategic.Symmetric`, and `Bimatrix.Symmetric` as an ordinary
`module` client:

1. **Prisoner's Dilemma (`IDoSDS`, `IsApproxMixedNash`, and Theorem 4.13)**: simultaneous `IDoSDS`
   reduces the Prisoner's Dilemma to mutual defection in one step, certifying mutual defection as
   the unique pure and mixed Nash equilibrium (`IDoSDS.isPureNash_iff_eq_of_singleton`,
   `IDoSDS.isMixedNash_iff_eq_single_of_singleton`); cooperation is `1`-strictly dominated, so
   Theorem 4.13 bounds its time-averaged weight under swap regret `R` by `R / T`; and mutual
   cooperation is a `3`-approximate mixed Nash equilibrium but not a `2`-approximate one.
2. **Order-dependence and simultaneous limit of `IDoWDS` on a `2 × 2` game**: in the payoff game
   `[[(1, 1), (0, 1)], [(0, 2), (0, 0)]]`, one `IDoWDS` schedule eliminates player 2's second
   column and then player 1's second row to reach `{(false, false)}`, whereas deleting player 1's
   weakly dominated second row first reaches `{false} × {false, true}`, where `IDoWDSStep` is
   terminal; simultaneous `idowdsSeq` reaches `fun _ => {false}` at stage `1` and stabilizes there
   (`idowdsLimit`).
3. **Example 2.2 of [Papadimitriou2007] and `IsEmpty` player-set witness**: the `3 × 3` symmetric
   bimatrix game with matrix `[[0, 3, 0], [0, 0, 3], [2, 2, 2]]` has symmetric Nash equilibrium
   `(0, 1/3, 2/3)`; on an empty player set (`Fin 0`), `CostGame.IsSymmetricMixedNash` still rejects
   non-mixed vectors.
4. **DMP `(1/2)`-Nash, cost-game bridge, and convexity of correlated equilibria**: concrete `[0, 1]`
   Battle of the Sexes instantiation of `isApproxNash_half_dmp`, transport to
   `CostGame.IsApproxMixedNash` via `BimatrixGame.isApproxNash_iff_isApproxMixedNash`, and convex
   combination of pure Nash equilibria via `IsCorrelatedEquilibrium.convexCombPair`.
5. **Equilibrium-correspondence step of [Papadimitriou2007], Theorem 2.4 (`symmReduction`)**:
   equilibrium lift and recovery on shifted Matching Pennies (`1 ≤ A, B`), and
   `exists_addConst_symmReduction` on signed Matching Pennies (`±1`).
6. **Mixed-strategy `ε`-dominance (`mixedDomGame`), [vonStengel2007] `(3.7)`, and unnormalized
   Exercise 1.6**: action `2` is `1`-strictly dominated by `(1/2, 1/2, 0)` while undominated by
   any pure action; symmetric equilibria of `[[3, 3, 0], [4, 0, 1], [0, 4, 5]]`; and
   `exists_uniformMultiset_isApproxNash_of_nonneg` on unnormalized `[0, 3]` payoffs.
-/

public section

namespace CslibFrontierTests.GameTheory.DominanceSymmetric

open Cslib.GameTheory Finset Function Matrix

/-! ### 1. Prisoner's Dilemma: `IDoSDS`, `IsApproxMixedNash`, and Theorem 4.13 -/

/-- Prisoner's Dilemma in cost form (`false` = cooperate, `true` = defect): against cooperation,
defecting lowers cost from `-6` to `-9` (saving `3`); against defection, defecting lowers cost from
`0` to `-1` (saving `1`). -/
def pd : CostGame (Fin 2) (fun _ => Bool) where
  cost i s :=
    match s 0, s 1 with
    | false, false => -6
    | false, true => if i = 0 then 0 else -9
    | true, false => if i = 0 then -9 else 0
    | true, true => -1

private theorem pd_profile_eq (s : Fin 2 → Bool) : s = ![s 0, s 1] := by
  funext j
  fin_cases j <;> rfl

/-- Defect (`true`) `1`-strictly dominates cooperate (`false`) for both players in `pd`. -/
theorem pd_cooperate_isEpsStrictlyDominated (i : Fin 2) :
    pd.IsEpsStrictlyDominated 1 i false := by
  refine ⟨true, fun s => ?_⟩
  rw [pd_profile_eq s]
  fin_cases i <;> cases s 0 <;> cases s 1 <;> norm_num [pd, Function.update]

/-- Defect (`true`) is a strictly dominant equilibrium of `pd`. -/
theorem pd_defect_isStrictlyDominantEquilibrium :
    pd.IsStrictlyDominantEquilibrium (fun _ => true) := by
  intro i s b hb
  have hbf : b = false := by cases b <;> simp_all
  subst hbf
  rw [pd_profile_eq s]
  fin_cases i <;> cases s 0 <;> cases s 1 <;> norm_num [pd, Function.update]

/-- Simultaneous `IDoSDS` eliminates `false` for both players in one step, leaving `{true}`. -/
theorem pd_idosds_singleton :
    pd.IDoSDS (fun _ => Set.univ) (fun _ => {true}) := by
  refine Relation.ReflTransGen.single ⟨fun _ _ _ => trivial, fun i a _ hnot => ?_⟩
  have haf : a = false := by
    cases a
    · rfl
    · exact (hnot rfl).elim
  subst haf
  refine ⟨true, trivial, rfl, fun s => ?_⟩
  simp only [CostGame.restrict_cost]
  fin_cases i <;> cases h0 : (s 0).1 <;> cases h1 : (s 1).1 <;>
    norm_num [pd, Function.update, h0, h1]

/-- Also exercise `idosdsStep_simultaneous` on `pd`. -/
example : pd.IDoSDSStep (fun _ => Set.univ)
    (fun i => {a | ∃ ha : a ∈ (Set.univ : Set Bool),
      ¬ (pd.restrict (fun _ => Set.univ)).IsStrictlyDominated i ⟨a, ha⟩}) :=
  pd.idosdsStep_simultaneous (fun _ => Set.univ)

/-- By `IDoSDS`, mutual defection is the unique pure Nash equilibrium of `pd`. -/
theorem pd_unique_pureNash (s : Fin 2 → Bool) :
    pd.IsPureNash s ↔ s = fun _ => true :=
  pd_idosds_singleton.isPureNash_iff_eq_of_singleton s

/-- By `IDoSDS`, point masses on mutual defection form the unique mixed Nash equilibrium of `pd`. -/
theorem pd_unique_mixedNash (p : Fin 2 → Bool → ℝ) :
    pd.IsMixedNash p ↔ p = fun _ => Pi.single true 1 :=
  pd_idosds_singleton.isMixedNash_iff_eq_single_of_singleton p

/-- Mutual cooperation in `pd` is a `3`-approximate mixed Nash equilibrium (defecting saves `3`),
and is not a `2`-approximate mixed Nash equilibrium. -/
theorem pd_cooperate_approxMixedNash_boundary :
    pd.IsApproxMixedNash 3 (fun _ => Pi.single false 1) ∧
      ¬ pd.IsApproxMixedNash 2 (fun _ => Pi.single false 1) := by
  constructor
  · refine ⟨fun _ => isMixedStrategy_single false, fun i a => ?_⟩
    rw [CostGame.expectedCost_single, CostGame.deviationCost_single]
    fin_cases i <;> cases a <;> norm_num [pd, Function.update]
  · intro h
    have h0 := h.2 0 true
    rw [CostGame.expectedCost_single, CostGame.deviationCost_single] at h0
    norm_num [pd, Function.update] at h0

/-- Nonvacuous instantiation of **Theorem 4.13** on `pd`: under swap regret at most `R` over
`T > 0` rounds, player `0` places time-averaged weight at most `R / T` on cooperation. -/
theorem pd_swapRegret_cooperate_decay {p : ℕ → Fin 2 → Bool → ℝ} {T : ℕ} (hT : 0 < T)
    (hp : ∀ t j, IsMixedStrategy (p t j)) {R : ℝ}
    (hR : ∀ δ : Bool → Bool,
      ∑ t ∈ range T, ∑ b, p t 0 b * pd.deviationCost (p t) 0 b
        ≤ ∑ t ∈ range T, ∑ b, p t 0 b * pd.deviationCost (p t) 0 (δ b) + R) :
    (∑ t ∈ range T, p t 0 false) / (T : ℝ) ≤ R / T := by
  have h := pd.timeAverage_weight_isEpsStrictlyDominatedMixed_le hT hp zero_lt_one hR
    (pd_cooperate_isEpsStrictlyDominated 0).isEpsStrictlyDominatedMixed
  simpa only [one_mul] using h

/-- `3 × 3` cost game illustrating **mixed-strategy** `ε`-strict dominance ([BlumMansour2007AGT],
Section 4.4.4, p. 91): against opponent action `0`, row `0` costs `0` and row `1` costs `6`; against
`1` or `2`, row `0` costs `6` and row `1` costs `0`; row `2` always costs `4`. Row `2` is NOT
strictly dominated by any pure action, yet it is `1`-strictly dominated by the mixed strategy
`(1/2, 1/2, 0)` (expected cost `3` against every opponent action, versus `4`). -/
def mixedDomGame : CostGame (Fin 2) (fun _ => Fin 3) where
  cost i s :=
    if i = 0 then
      match s 0, s 1 with
      | 0, 0 => 0
      | 0, _ => 6
      | 1, 0 => 6
      | 1, _ => 0
      | 2, _ => 4
    else 0

theorem mixedDomGame_not_pure_dominated :
    ¬ mixedDomGame.IsStrictlyDominated 0 (2 : Fin 3) := by
  rintro ⟨b, hb⟩
  fin_cases b
  · have h := hb ![2, 1]
    norm_num [mixedDomGame, Function.update] at h
  · have h := hb ![2, 0]
    norm_num [mixedDomGame, Function.update] at h
  · have h := hb ![2, 0]
    exact lt_irrefl _ h

theorem mixedDomGame_isEpsStrictlyDominatedMixed :
    mixedDomGame.IsEpsStrictlyDominatedMixed 1 0 (2 : Fin 3) := by
  refine ⟨![1 / 2, 1 / 2, 0], isMixedStrategy_iff.2 ⟨fun i => ?_, ?_⟩, fun s => ?_⟩
  · fin_cases i <;> norm_num
  · rw [Fin.sum_univ_three]
    norm_num
  · have hs : s = ![s 0, s 1] := by
      funext j
      fin_cases j <;> rfl
    rw [hs]
    have h1 : s 1 = 0 ∨ s 1 = 1 ∨ s 1 = 2 := by
      generalize s 1 = y
      fin_cases y <;> decide
    rcases h1 with h | h | h <;>
      norm_num [mixedDomGame, Fin.sum_univ_three, Function.update, h]

/-- Theorem 4.13 applies even when an action is only dominated by a *mixed* strategy. -/
theorem mixedDomGame_swapRegret_decay {p : ℕ → Fin 2 → Fin 3 → ℝ}
    {T : ℕ} (hT : 0 < T) (hp : ∀ t j, IsMixedStrategy (p t j)) {R : ℝ}
    (hR : ∀ δ : Fin 3 → Fin 3,
      ∑ t ∈ range T, ∑ b, p t 0 b * mixedDomGame.deviationCost (p t) 0 b
        ≤ ∑ t ∈ range T, ∑ b, p t 0 b * mixedDomGame.deviationCost (p t) 0 (δ b) + R) :
    (∑ t ∈ range T, p t 0 (2 : Fin 3)) / (T : ℝ) ≤ R / T := by
  have h := mixedDomGame.timeAverage_weight_isEpsStrictlyDominatedMixed_le hT hp zero_lt_one hR
    mixedDomGame_isEpsStrictlyDominatedMixed
  simpa only [one_mul] using h

/-! ### 2. Order-dependence and simultaneous limit of `IDoWDS` on a `2 × 2` game -/

/-- `2 × 2` game in cost form corresponding to payoffs `[[(1, 1), (0, 1)], [(0, 2), (0, 0)]]`:
for player 0 (`false` = top, `true` = bottom), `false` weakly dominates `true`;
for player 1 (`false` = left, `true` = right), `false` weakly dominates `true`. -/
def orderDepGame : CostGame (Fin 2) (fun _ => Bool) where
  cost i s :=
    match i, s 0, s 1 with
    | 0, false, false => -1
    | 0, false, true => 0
    | 0, true, _ => 0
    | 1, false, _ => -1
    | 1, true, false => -2
    | 1, true, true => 0

/-- Schedule 1: deleting `true` for player 1 first and then `true` for player 0 reaches the
singleton `{(false, false)}` via `IDoWDS`. -/
theorem orderDepGame_idowds_singleton :
    orderDepGame.IDoWDS (fun _ => Set.univ) (fun _ => {false}) := by
  let A₁ : Fin 2 → Set Bool := fun i => if i = 1 then {false} else Set.univ
  have hstep1 : orderDepGame.IDoWDSStep (fun _ => Set.univ) A₁ := by
    refine ⟨fun i _ _ => trivial, fun i a _ hnot => ?_⟩
    fin_cases i
    · exact (hnot trivial).elim
    · have hat : a = true := by
        cases a
        · exact (hnot rfl).elim
        · rfl
      subst hat
      refine ⟨⟨false, trivial⟩, fun s => ?_, ⟨fun _ => ⟨true, trivial⟩, ?_⟩⟩
      · simp only [CostGame.restrict_cost]
        cases h0 : (s 0).1 <;> norm_num [orderDepGame, Function.update, h0]
      · simp only [CostGame.restrict_cost]
        norm_num [orderDepGame, Function.update]
  have hstep2 : orderDepGame.IDoWDSStep A₁ (fun _ => {false}) := by
    refine ⟨fun i b hb => ?_, fun i a ha hnot => ?_⟩
    · fin_cases i
      · trivial
      · exact hb
    · fin_cases i
      · have hat : a = true := by
          cases a
          · exact (hnot rfl).elim
          · rfl
        subst hat
        have hfalseA : false ∈ A₁ 0 := trivial
        refine ⟨⟨false, hfalseA⟩, fun s => ?_, ⟨fun j => if hj : j = 0 then ⟨false, hj ▸ hfalseA⟩
          else ⟨false, by fin_cases j <;> simp_all [A₁]⟩, ?_⟩⟩
        · have hs1 : (s 1).1 = false := (s 1).2
          simp only [CostGame.restrict_cost]
          norm_num [orderDepGame, Function.update, hs1]
        · simp only [CostGame.restrict_cost]
          norm_num [orderDepGame, Function.update]
      · exact (hnot ha).elim
  exact (Relation.ReflTransGen.single hstep1).tail hstep2

/-- Schedule 2: deleting `true` for player 0 first reaches `A₂ = ({false}, Set.univ)`, which is a
distinct **terminal** `IDoWDS` state (`orderDepGame.IDoWDSStep A₂ B → B = A₂`) in which `(false,
true)` survives alongside `(false, false)`. -/
theorem orderDepGame_idowds_other_terminal :
    let A₂ : Fin 2 → Set Bool := fun i => if i = 0 then {false} else Set.univ
    orderDepGame.IDoWDS (fun _ => Set.univ) A₂ ∧
      true ∈ A₂ 1 ∧
      ∀ B, orderDepGame.IDoWDSStep A₂ B → B = A₂ := by
  intro A₂
  refine ⟨Relation.ReflTransGen.single ?_, trivial, fun B hB => ?_⟩
  · refine ⟨fun _ _ _ => trivial, fun i a _ hnot => ?_⟩
    fin_cases i
    · have hat : a = true := by
        cases a
        · exact (hnot rfl).elim
        · rfl
      subst hat
      refine ⟨⟨false, trivial⟩, fun s => ?_, ⟨fun _ => ⟨false, trivial⟩, ?_⟩⟩
      · simp only [CostGame.restrict_cost]
        cases h1 : (s 1).1 <;> norm_num [orderDepGame, Function.update, h1]
      · simp only [CostGame.restrict_cost]
        norm_num [orderDepGame, Function.update]
    · exact (hnot trivial).elim
  · funext i
    ext a
    refine ⟨fun ha => hB.1 i ha, fun ha => ?_⟩
    by_contra hnot
    obtain ⟨b, hb⟩ := hB.2 i a ha hnot
    obtain ⟨_, s, hlt⟩ := hb
    fin_cases i
    · have ha_eq : a = false := ha
      have hb_eq : b.1 = false := b.2
      have hab : (⟨a, ha⟩ : A₂ 0) = b := Subtype.ext (ha_eq.trans hb_eq.symm)
      rw [hab] at hlt
      exact lt_irrefl _ hlt
    · have hs0 : (s 0).1 = false := (s 0).2
      simp only [CostGame.restrict_cost] at hlt
      cases a <;> cases b.1 <;> norm_num [orderDepGame, Function.update, hs0] at hlt

/-- Simultaneous `IDoWDS` (`idowdsSeq`) eliminates `true` for both players in one step on
`orderDepGame`, leaving `fun _ => {false}` at stage `1`. -/
theorem orderDepGame_idowdsSeq_one :
    orderDepGame.idowdsSeq 1 = fun _ => {false} := by
  funext i
  ext a
  rw [CostGame.idowdsSeq_succ, CostGame.idowdsSeq_zero]
  simp only [Set.mem_ofPred_eq, Set.mem_univ, exists_true_left, Set.mem_singleton_iff]
  fin_cases i
  · cases a
    · simp only [iff_true]
      rintro ⟨⟨b, _⟩, hle, _, hlt⟩
      cases b
      · exact lt_irrefl _ hlt
      · have h0 := hle fun _ => ⟨false, trivial⟩
        simp only [CostGame.restrict_cost] at h0
        norm_num [orderDepGame, Function.update] at h0
    · simp only [Bool.true_eq_false, iff_false, not_not]
      refine ⟨⟨false, trivial⟩, fun s => ?_, ⟨fun _ => ⟨false, trivial⟩, ?_⟩⟩
      · simp only [CostGame.restrict_cost]
        cases h1 : (s 1).1 <;> norm_num [orderDepGame, Function.update, h1]
      · simp only [CostGame.restrict_cost]
        norm_num [orderDepGame, Function.update]
  · cases a
    · simp only [iff_true]
      rintro ⟨⟨b, _⟩, hle, _, hlt⟩
      cases b
      · exact lt_irrefl _ hlt
      · have h0 := hle fun _ => ⟨true, trivial⟩
        simp only [CostGame.restrict_cost] at h0
        norm_num [orderDepGame, Function.update] at h0
    · simp only [Bool.true_eq_false, iff_false, not_not]
      refine ⟨⟨false, trivial⟩, fun s => ?_, ⟨fun _ => ⟨true, trivial⟩, ?_⟩⟩
      · simp only [CostGame.restrict_cost]
        cases h0 : (s 0).1 <;> norm_num [orderDepGame, Function.update, h0]
      · simp only [CostGame.restrict_cost]
        norm_num [orderDepGame, Function.update]

/-- Simultaneous `IDoWDS` stabilizes after stage `1` on `orderDepGame`, so
`orderDepGame.idowdsLimit` is the singleton `fun _ => {false}` (contrasting with the sequential
terminal state `A₂` above). -/
theorem orderDepGame_idowdsLimit :
    orderDepGame.idowdsLimit = fun _ => {false} := by
  have hsucc : ∀ k, orderDepGame.idowdsSeq (k + 1) = fun _ => {false} := by
    intro k
    induction k with
    | zero => exact orderDepGame_idowdsSeq_one
    | succ k ih =>
      funext i
      ext a
      rw [CostGame.idowdsSeq_succ, ih]
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · exact fun h => h.1
      · rintro rfl
        refine ⟨rfl, ?_⟩
        rintro ⟨⟨b, hb⟩, _, _, hlt⟩
        have hbf : b = false := hb
        subst hbf
        exact lt_irrefl _ hlt
  funext i
  ext a
  rw [CostGame.mem_idowdsLimit_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have h1 := h 1
    rw [orderDepGame_idowdsSeq_one] at h1
    exact h1
  · rintro rfl k
    cases k with
    | zero => simp only [CostGame.idowdsSeq_zero, Set.mem_univ]
    | succ k => rw [hsucc k]; rfl

/-! ### 3. NRTV Example 2.2 and `IsEmpty` player-set witness -/

/-- Example 2.2 of [Papadimitriou2007] (p. 30): symmetric `3 × 3` game with matrix
`[[0, 3, 0], [0, 0, 3], [2, 2, 2]]`. -/
def example2_2 : BimatrixGame (Fin 3) (Fin 3) :=
  BimatrixGame.ofSymmetric !![0, 3, 0; 0, 0, 3; 2, 2, 2]

/-- `(0, 1/3, 2/3)` is a symmetric Nash equilibrium of `example2_2` with equilibrium payoff `2`. -/
theorem example2_2_isSymmetricNash :
    example2_2.IsSymmetricNash ![0, 1 / 3, 2 / 3] := by
  have hsym : example2_2.IsSymmetric := BimatrixGame.isSymmetric_ofSymmetric _
  rw [hsym.isSymmetricNash_iff]
  have hx : IsMixedStrategy (![0, 1 / 3, 2 / 3] : Fin 3 → ℝ) := by
    refine isMixedStrategy_iff.2 ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> norm_num
    · rw [Fin.sum_univ_three]
      norm_num
  have hpay : example2_2.payoff₁ ![0, 1 / 3, 2 / 3] ![0, 1 / 3, 2 / 3] = 2 := by
    rw [BimatrixGame.payoff₁_eq_dotProduct, example2_2, BimatrixGame.ofSymmetric_A]
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  refine ⟨hx, fun i => ?_⟩
  rw [hpay, example2_2, BimatrixGame.ofSymmetric_A]
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- On an empty player set (`Fin 0`), `CostGame.IsSymmetricMixedNash` still requires a mixed
strategy `x`, rejecting negative vectors. -/
theorem emptyPlayers_not_isSymmetricMixedNash :
    ¬ ({ cost := fun i _ => isEmptyElim i } : CostGame (Fin 0) (fun _ => Bool)).IsSymmetricMixedNash
      (fun _ => -1) := by
  intro h
  have hnn := h.1.nonneg false
  norm_num at hnn

/-! ### 4. DMP `(1/2)`-Nash, cost-game bridge, and convex combination of Nash equilibria -/

/-- `[0, 1]`-normalized Battle of the Sexes bimatrix game. -/
noncomputable def bosBimatrix : BimatrixGame Bool Bool where
  A := fun i j => match i, j with
    | false, false => 1
    | true, true => 1 / 2
    | _, _ => 0
  B := fun i j => match i, j with
    | false, false => 1 / 2
    | true, true => 1
    | _, _ => 0

/-- DMP `(1/2)`-approximate Nash construction instantiated on `bosBimatrix` starting from
`i₀ = true` (`j₀ = true`, `i₁ = true`). -/
theorem bosBimatrix_dmp_half_nash :
    bosBimatrix.IsApproxNash (1 / 2)
      ((1 / 2 : ℝ) • Pi.single true 1 + (1 / 2 : ℝ) • Pi.single true 1)
      (Pi.single true 1) := by
  refine bosBimatrix.isApproxNash_half_dmp (fun i j => ?_) (fun i j => ?_) true
    (j₀ := true) (fun j => ?_) (i₁ := true) (fun i => ?_)
  · cases i <;> cases j <;> norm_num [bosBimatrix]
  · cases i <;> cases j <;> norm_num [bosBimatrix]
  · cases j <;> norm_num [bosBimatrix]
  · cases i <;> norm_num [bosBimatrix]

/-- Transporting `bosBimatrix_dmp_half_nash` to `CostGame.IsApproxMixedNash` via
`BimatrixGame.isApproxNash_iff_isApproxMixedNash`. -/
theorem bosBimatrix_toCostGame_isApproxMixedNash :
    bosBimatrix.toCostGame.IsApproxMixedNash (1 / 2)
      (BimatrixGame.profile
        ((1 / 2 : ℝ) • Pi.single true 1 + (1 / 2 : ℝ) • Pi.single true 1)
        (Pi.single true 1)) :=
  BimatrixGame.isApproxNash_iff_isApproxMixedNash.1 bosBimatrix_dmp_half_nash

/-- Coordination game in cost form: both `(false, false)` and `(true, true)` are pure (hence mixed)
Nash equilibria, and their `1/2`–`1/2` convex combination is a correlated equilibrium. -/
def coordCostGame : CostGame (Fin 2) (fun _ => Bool) where
  cost _ s := if s 0 = s 1 then -1 else 0

theorem coordCostGame_half_ce :
    ∃ σ : Convexity.StdSimplex ℝ (Fin 2 → Bool), coordCostGame.IsCorrelatedEquilibrium σ := by
  have hp₁ : coordCostGame.IsPureNash (fun _ => false) := by
    intro i a
    fin_cases i <;> cases a <;> norm_num [coordCostGame, Function.update]
  have hp₂ : coordCostGame.IsPureNash (fun _ => true) := by
    intro i a
    fin_cases i <;> cases a <;> norm_num [coordCostGame, Function.update]
  exact ⟨_, hp₁.isMixedNash.isCorrelatedEquilibrium.convexCombPair
    hp₂.isMixedNash.isCorrelatedEquilibrium (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)⟩

/-! ### 5. Equilibrium-correspondence step of [Papadimitriou2007], Theorem 2.4 (`symmReduction`) -/

/-- Shifted Matching Pennies with payoffs in `{1, 3} ⊆ [1, ∞)`. -/
def shiftedPennies : BimatrixGame Bool Bool where
  A i j := if i = j then 3 else 1
  B i j := if i = j then 1 else 3

/-- Uniform mixing `(1/2, 1/2)` by both players is a Nash equilibrium of `shiftedPennies`. -/
theorem shiftedPennies_isNash_uniform :
    shiftedPennies.IsNash (fun _ => 1 / 2) (fun _ => 1 / 2) := by
  have humix : IsMixedStrategy (fun _ : Bool => (1 / 2 : ℝ)) := by
    refine isMixedStrategy_iff.2 ⟨fun _ => by norm_num, ?_⟩
    rw [Fintype.sum_bool]
    norm_num
  refine BimatrixGame.isNash_iff.2
    ⟨BimatrixGame.isBestResponse₁_iff_le_payoff₁.2 ⟨humix, fun i => ?_⟩,
      BimatrixGame.isBestResponse₂_iff_le_payoff₂.2 ⟨humix, fun j => ?_⟩⟩
  · rw [BimatrixGame.payoff₁_eq_dotProduct]
    cases i <;> norm_num [shiftedPennies, Matrix.mulVec, dotProduct, Fintype.sum_bool]
  · rw [BimatrixGame.payoff₂_eq_dotProduct]
    cases j <;> norm_num [shiftedPennies, Matrix.vecMul, dotProduct, Fintype.sum_bool]

/-- Round-trip instantiation of the algebraic equilibrium correspondence behind Theorem 2.4:
lifting `shiftedPennies_isNash_uniform` to `shiftedPennies.symmReduction` and recovering a Nash
equilibrium via `symmReduction_pos_and_isNash`. -/
theorem shiftedPennies_symmReduction_roundtrip :
    ∃ z : Bool ⊕ Bool → ℝ,
      shiftedPennies.symmReduction.IsSymmetricNash z ∧
        shiftedPennies.IsNash (BimatrixGame.symmProj₁ z) (BimatrixGame.symmProj₂ z) := by
  have hA : ∀ i j, 0 < shiftedPennies.A i j := by
    intro i j
    cases i <;> cases j <;> norm_num [shiftedPennies]
  have hB : ∀ i j, 0 < shiftedPennies.B i j := by
    intro i j
    cases i <;> cases j <;> norm_num [shiftedPennies]
  have hsym := BimatrixGame.isSymmetricNash_symmReduction_of_isNash hA hB
    shiftedPennies_isNash_uniform
  obtain ⟨-, -, hNash⟩ := BimatrixGame.symmReduction_pos_and_isNash hA hB hsym
  exact ⟨_, hsym, hNash⟩

/-- Standard Matching Pennies (with negative payoffs `-1` and `1`) exercises
`exists_addConst_symmReduction` without pre-shifting. -/
def signedPennies : BimatrixGame Bool Bool where
  A i j := if i = j then 1 else -1
  B i j := if i = j then -1 else 1

theorem signedPennies_symmReduction_shift :
    ∃ c : ℝ,
      ∀ z : Bool ⊕ Bool → ℝ, (signedPennies.addConst c).symmReduction.IsSymmetricNash z →
        signedPennies.IsNash (BimatrixGame.symmProj₁ z) (BimatrixGame.symmProj₂ z) := by
  obtain ⟨c, hfwd, _⟩ := signedPennies.exists_addConst_symmReduction
  exact ⟨c, fun z hz => (hfwd z hz).2.2⟩

/-! ### 6. Symmetric 3×3 game (3.7) of von Stengel and unnormalized Exercise 1.6 -/

/-- The `3 × 3` symmetric game `A = Bᵀ = [[3, 3, 0], [4, 0, 1], [0, 4, 5]]` from
`[vonStengel2007]`, eq. (3.7), pp. 62–63, with symmetric Nash equilibria `(0, 0, 1)`,
`(1/2, 1/4, 1/4)`, and `(3/4, 1/4, 0)`. -/
def vonStengel37 : BimatrixGame (Fin 3) (Fin 3) :=
  BimatrixGame.ofSymmetric !![3, 3, 0; 4, 0, 1; 0, 4, 5]

theorem vonStengel37_isSymmetricNash_eqs :
    vonStengel37.IsSymmetricNash ![0, 0, 1] ∧
      vonStengel37.IsSymmetricNash ![1 / 2, 1 / 4, 1 / 4] ∧
      vonStengel37.IsSymmetricNash ![3 / 4, 1 / 4, 0] := by
  have hsym : vonStengel37.IsSymmetric := BimatrixGame.isSymmetric_ofSymmetric _
  refine ⟨hsym.isSymmetricNash_iff.2 ⟨isMixedStrategy_iff.2 ⟨fun i => ?_, ?_⟩, fun i => ?_⟩,
    hsym.isSymmetricNash_iff.2 ⟨isMixedStrategy_iff.2 ⟨fun i => ?_, ?_⟩, fun i => ?_⟩,
    hsym.isSymmetricNash_iff.2 ⟨isMixedStrategy_iff.2 ⟨fun i => ?_, ?_⟩, fun i => ?_⟩⟩
  · fin_cases i <;> norm_num
  · rw [Fin.sum_univ_three]; norm_num
  · rw [BimatrixGame.payoff₁_eq_dotProduct, vonStengel37, BimatrixGame.ofSymmetric_A]
    fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · fin_cases i <;> norm_num
  · rw [Fin.sum_univ_three]; norm_num
  · rw [BimatrixGame.payoff₁_eq_dotProduct, vonStengel37, BimatrixGame.ofSymmetric_A]
    fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · fin_cases i <;> norm_num
  · rw [Fin.sum_univ_three]; norm_num
  · rw [BimatrixGame.payoff₁_eq_dotProduct, vonStengel37, BimatrixGame.ofSymmetric_A]
    fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Unnormalized nonnegative payoff instantiation of Exercise 1.6 on `shiftedPennies` (`[0, 3]`):
at `ε = 1/10`, there exist uniform multisets of size `lmmSampleSize Bool Bool (1/10)` forming a
`(3/10)`-approximate Nash equilibrium. -/
theorem shiftedPennies_lmm_unnormalized :
    ∃ (m₁ m₂ : Multiset Bool),
      m₁.card = BimatrixGame.lmmSampleSize Bool Bool (1 / 10) ∧
        m₂.card = BimatrixGame.lmmSampleSize Bool Bool (1 / 10) ∧
        shiftedPennies.IsApproxNash (3 / 10) (uniformMultiset m₁) (uniformMultiset m₂) := by
  have h := shiftedPennies.exists_uniformMultiset_isApproxNash_of_nonneg (K := 3) (by norm_num)
    (fun i j => by cases i <;> cases j <;> norm_num [shiftedPennies])
    (fun i j => by cases i <;> cases j <;> norm_num [shiftedPennies])
    (ε := 1 / 10) (by norm_num)
  simpa only [show (1 / 10 : ℝ) * 3 = 3 / 10 by norm_num] using h

end CslibFrontierTests.GameTheory.DominanceSymmetric
