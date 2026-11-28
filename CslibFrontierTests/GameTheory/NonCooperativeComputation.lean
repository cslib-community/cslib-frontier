/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.RationalCrypto.NonCooperativeComputation
import Mathlib.Tactic.NormNum

/-!
# Tests for Correlated Equilibrium Min-Max Bounds and Non-Cooperatively Computable Functions

Concrete finite witnesses exercising `Cslib.GameTheory.PayoffGame.correlatedMinMax` (Claim 8.4)
and `Cslib.GameTheory.RationalCrypto.IsNCC` / `IsKNCC` (Theorem 8.6 and `k-NCC`):

1. **Game of Chicken** (`[[4, 1], [5, 0]]`, [DodisRabin2007], p. 195): exact correlated min-max
   value `correlatedMinMax chicken 0 = 1`, verified on the 50–50 correlated equilibrium
   (tight at `false` with conditional payoff `1 = v_0`, strict at `true` with `5 > 1`).
2. **Concrete NCC utilities and uniform priors**: a concrete family of correctness/exclusivity
   utilities satisfying `CorrectnessExclusivity` and `HighCorrectnessPriority` for uniform priors
   on `Fin n → Bool`, checking:
   - `3`-player majority is `IsNCC`;
   - `2`-player parity is `¬ IsNCC` (via reversibility);
   - `2`-player `OR` (`threshold 2 1`) and `AND` (`threshold 2 2`) are `¬ IsNCC` (via domination and
     Footnote 8);
   - `5`-player majority is `2-NCC` and fails `3-NCC`.
3. **Boundary witnesses**:
   - Constant function `fun _ : BitString 2 => true` violates `EveryInputMatters` (and
     non-constancy), is `IsDominated`, yet IS `IsNCC` under the constant-`true` fallback (showing
     non-constancy / `EveryInputMatters` is genuinely necessary in Theorem 8.6).
   - Single-player (`Fin 1`) parity is `IsReversible`, yet IS `IsNCC` (showing `2 ≤ Fintype.card ι`
     is genuinely necessary in Theorem 8.6).
-/

public section

namespace CslibFrontierTests.GameTheory.NonCooperativeComputation

open Cslib.GameTheory
open Cslib.GameTheory.PayoffGame
open Cslib.GameTheory.RationalCrypto

/-! ### 1. Claim 8.4 on the Game of Chicken (`[[4, 1], [5, 0]]`) -/

/-- Symmetric Game of Chicken in payoff form (`false` = Swerve, `true` = Dare):
payoff matrix `[[4, 1], [5, 0]]` for each player. -/
def chickenPayoff (i : Fin 2) (s : Fin 2 → Bool) : ℝ :=
  match s i, s (1 - i) with
  | false, false => 4
  | false, true => 1
  | true, false => 5
  | true, true => 0

def chicken : PayoffGame (Fin 2) (fun _ => Bool) := ⟨chickenPayoff⟩

/-- Player `0`'s correlated min-max value in Chicken is `1` (enforced by player `1` playing
Dare = `true`, and guaranteed to player `0` by playing Swerve = `false`). -/
theorem chicken_correlatedMinMax_zero : chicken.correlatedMinMax 0 = 1 := by
  have hval : Cslib.Probability.IsMinimaxValue
      (fun (s : ∀ j : { j : Fin 2 // j ≠ 0 }, Bool) (a : Bool) =>
        chicken.payoff 0 (insertAction 0 a s)) (1 : ℝ) := by
    refine ⟨⟨Convexity.StdSimplex.single (fun _ => true), fun a => ?_⟩,
      ⟨Convexity.StdSimplex.single false, fun s => ?_⟩⟩
    · simp only [Convexity.StdSimplex.weights_single, Finsupp.single_apply, ite_mul, one_mul,
        zero_mul]
      cases a <;> norm_num [chicken, chickenPayoff, insertAction]
    · simp only [Convexity.StdSimplex.weights_single, Finsupp.single_apply, ite_mul, one_mul,
        zero_mul]
      have h1 : (1 : Fin 2) ≠ 0 := by decide
      cases hs : s ⟨1, h1⟩ <;> norm_num [chicken, chickenPayoff, insertAction, hs]
  exact (chicken.isMinimaxValue_correlatedMinMax 0).unique hval

/-- The 50–50 correlated equilibrium of Chicken on `(Swerve, Dare)` and `(Dare, Swerve)`. -/
noncomputable def chickenHalfCE : Convexity.StdSimplex ℝ (Fin 2 → Bool) :=
  .duple ![false, true] ![true, false] (s := 1 / 2) (t := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)

private theorem chickenHalfCE_sum (f : (Fin 2 → Bool) → ℝ) :
    chickenHalfCE.weights.sum (fun s w => w * f s) =
      1 / 2 * f ![false, true] + 1 / 2 * f ![true, false] := by
  rw [chickenHalfCE, Convexity.StdSimplex.duple,
    Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
    Finsupp.sum_single_index (zero_mul _), Finsupp.sum_single_index (zero_mul _)]

theorem chicken_isCorrelatedEquilibrium_half :
    chicken.toCostGame.IsCorrelatedEquilibrium chickenHalfCE := by
  intro i δ
  rw [chickenHalfCE_sum, chickenHalfCE_sum]
  fin_cases i <;> cases hT : δ true <;> cases hF : δ false <;>
    norm_num [chicken, chickenPayoff, PayoffGame.toCostGame_cost, Function.update, hT, hF]

/-- Claim 8.4 verified on Chicken's 50–50 CE: both actions have marginal weight `1 / 2 > 0`,
with conditional payoffs `1 = v_0` at `false` (tight) and `5 > 1 = v_0` at `true`. -/
example :
    marginalWeight chickenHalfCE 0 false = 1 / 2 ∧
      marginalWeight chickenHalfCE 0 true = 1 / 2 ∧
      chicken.condPayoff chickenHalfCE 0 false = 1 ∧
      chicken.correlatedMinMax 0 ≤ chicken.condPayoff chickenHalfCE 0 false ∧
      chicken.correlatedMinMax 0 ≤ chicken.condPayoff chickenHalfCE 0 true ∧
      chicken.condPayoff chickenHalfCE 0 true = 5 := by
  have hmF : marginalWeight chickenHalfCE 0 false = 1 / 2 := by
    have heq : (∑ s : Fin 2 → Bool, if s 0 = false then chickenHalfCE.weights s else 0) =
        chickenHalfCE.weights.sum (fun s w => w * if s 0 = false then (1 : ℝ) else 0) := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs <;> ring
    rw [marginalWeight_eq, heq, chickenHalfCE_sum]
    norm_num
  have hmT : marginalWeight chickenHalfCE 0 true = 1 / 2 := by
    have heq : (∑ s : Fin 2 → Bool, if s 0 = true then chickenHalfCE.weights s else 0) =
        chickenHalfCE.weights.sum (fun s w => w * if s 0 = true then (1 : ℝ) else 0) := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs <;> ring
    rw [marginalWeight_eq, heq, chickenHalfCE_sum]
    norm_num
  have hcondF : chicken.condPayoff chickenHalfCE 0 false = 1 := by
    have hnum : (∑ s : Fin 2 → Bool,
          if s 0 = false then chickenHalfCE.weights s * chicken.payoff 0 s else 0) =
        chickenHalfCE.weights.sum
          (fun s w => w * if s 0 = false then chicken.payoff 0 s else 0) := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs <;> ring
    rw [condPayoff_eq, hnum, chickenHalfCE_sum, hmF]
    norm_num [chicken, chickenPayoff]
  have hcondT : chicken.condPayoff chickenHalfCE 0 true = 5 := by
    have hnum : (∑ s : Fin 2 → Bool,
          if s 0 = true then chickenHalfCE.weights s * chicken.payoff 0 s else 0) =
        chickenHalfCE.weights.sum
          (fun s w => w * if s 0 = true then chicken.payoff 0 s else 0) := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs <;> ring
    rw [condPayoff_eq, hnum, chickenHalfCE_sum, hmT]
    norm_num [chicken, chickenPayoff]
  exact ⟨hmF, hmT, hcondF,
    chicken.correlatedMinMax_le_condPayoff chicken_isCorrelatedEquilibrium_half 0
      (by rw [hmF]; norm_num),
    chicken.correlatedMinMax_le_condPayoff chicken_isCorrelatedEquilibrium_half 0
      (by rw [hmT]; norm_num),
    hcondT⟩

/-! ### 2. Concrete NCC utilities, Theorem 8.6, and `k-NCC` witnesses -/

/-- Concrete utility family with high correctness reward `M` and unit exclusivity bonus per wrong
opponent: `u i c = (if c i then M else 0) + #{j ≠ i | c j = false}`. -/
def nccUtil (n : ℕ) (M : ℝ) (i : Fin n) (c : Fin n → Bool) : ℝ :=
  (if c i = true then M else 0) +
    ((Finset.univ.filter fun j : Fin n => j ≠ i ∧ c j = false).card : ℝ)

theorem correctnessExclusivity_nccUtil {n : ℕ} {M : ℝ} (hM : (n : ℝ) < M) :
    CorrectnessExclusivity (nccUtil n M) where
  correctness i c c' hc hc' := by
    have hcard : ((Finset.univ.filter fun j : Fin n => j ≠ i ∧ c' j = false).card : ℝ) ≤ n := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
    have h0 : (0 : ℝ) ≤ ((Finset.univ.filter fun j : Fin n => j ≠ i ∧ c j = false).card : ℝ) :=
      Nat.cast_nonneg _
    simp only [nccUtil, hc, hc', ↓reduceIte, Bool.false_eq_true]
    linarith
  exclusivity i c c' hci hsub h := by
    obtain ⟨j₀, hj₀ne, hj₀c, hj₀c'⟩ := h
    simp only [nccUtil, hci, add_lt_add_iff_left, Nat.cast_lt]
    refine Finset.card_lt_card ⟨?_, ?_⟩
    · intro j hj
      obtain ⟨-, hjne, hjf⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjne, ?_⟩
      cases hcj : c j
      · rfl
      · exact absurd (hsub j hjne hcj) (by simp [hjf])
    · intro hle
      have hj0_mem : j₀ ∈ Finset.univ.filter fun j : Fin n => j ≠ i ∧ c j = false :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₀ne, hj₀c⟩
      have := (Finset.mem_filter.mp (hle hj0_mem)).2.2
      simp [hj₀c'] at this

/-- Uniform prior on `BitString n`. -/
noncomputable def uniformPrior (n : ℕ) : Cslib.BitString n → ℝ :=
  fun _ => (1 : ℝ) / (2 ^ n : ℝ)

theorem isMixedStrategy_uniformPrior (n : ℕ) : IsMixedStrategy (uniformPrior n) := by
  refine isMixedStrategy_iff.mpr ⟨fun _ => by unfold uniformPrior; positivity, ?_⟩
  simp only [uniformPrior, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_one_div_cancel (by positivity)

theorem uniformPrior_pos (n : ℕ) (t : Cslib.BitString n) : 0 < uniformPrior n t := by
  unfold uniformPrior
  positivity

theorem highCorrectnessPriority_nccUtil {n : ℕ} {M : ℝ} (hM : (n : ℝ) * (2 ^ n : ℝ) < M) :
    HighCorrectnessPriority (nccUtil n M) (uniformPrior n) := by
  intro i c c' c'' _ hc hc' hc''
  have hc'card : ((Finset.univ.filter fun j : Fin n => j ≠ i ∧ c' j = false).card : ℝ) ≤ n := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have hc''card : ((Finset.univ.filter fun j : Fin n => j ≠ i ∧ c'' j = false).card : ℝ) ≤ n := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have hccard : (0 : ℝ) ≤
      ((Finset.univ.filter fun j : Fin n => j ≠ i ∧ c j = false).card : ℝ) :=
    Nat.cast_nonneg _
  have hpow : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
  have hstep : (n : ℝ) < M / (2 ^ n : ℝ) := (lt_div_iff₀ hpow).mpr hM
  simp only [nccUtil, uniformPrior, hc, hc', hc'', ↓reduceIte, Bool.false_eq_true, zero_add]
  have h1 : (1 - 1 / (2 ^ n : ℝ)) * (M + ((Finset.univ.filter
        fun j : Fin n => j ≠ i ∧ c' j = false).card : ℝ)) +
      1 / (2 ^ n : ℝ) * ((Finset.univ.filter
        fun j : Fin n => j ≠ i ∧ c'' j = false).card : ℝ) ≤
      (1 - 1 / (2 ^ n : ℝ)) * (M + n) + 1 / (2 ^ n : ℝ) * n := by
    have hnonneg : (0 : ℝ) ≤ 1 - 1 / (2 ^ n : ℝ) := by
      have : (1 : ℝ) ≤ (2 ^ n : ℝ) := by exact_mod_cast Nat.one_le_two_pow
      rw [sub_nonneg, div_le_one hpow]
      exact this
    nlinarith [div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hpow.le]
  have h2 : (1 - 1 / (2 ^ n : ℝ)) * (M + n) + 1 / (2 ^ n : ℝ) * n =
      M + n - M / (2 ^ n : ℝ) := by ring
  linarith

/-- Concrete 3-player majority is `NCC` under `nccUtil 3 100` and `uniformPrior 3`, for any
fallback rule. -/
example (fallback : Fin 3 → Bool → Bool) :
    IsNCC (Cslib.majority 3) (nccUtil 3 100) (uniformPrior 3) fallback :=
  isNCC_majority (m := 1) le_rfl
    (correctnessExclusivity_nccUtil (by norm_num))
    (isMixedStrategy_uniformPrior 3)
    (highCorrectnessPriority_nccUtil (by norm_num))

/-- Concrete 2-player parity is NOT `NCC` (via reversibility). -/
example (fallback : Fin 2 → Bool → Bool) :
    ¬ IsNCC (Cslib.parity 2) (nccUtil 2 100) (uniformPrior 2) fallback :=
  not_isNCC_parity le_rfl (correctnessExclusivity_nccUtil (by norm_num)) (uniformPrior_pos 2)

/-- Concrete 2-player `OR` (`threshold 2 1`) and `AND` (`threshold 2 2`) are NOT `NCC`
(via domination and Footnote 8). -/
example (fallback : Fin 2 → Bool → Bool) :
    ¬ IsNCC (Cslib.threshold 2 1) (nccUtil 2 100) (uniformPrior 2) fallback ∧
      ¬ IsNCC (Cslib.threshold 2 2) (nccUtil 2 100) (uniformPrior 2) fallback :=
  ⟨not_isNCC_or le_rfl (correctnessExclusivity_nccUtil (by norm_num)) (uniformPrior_pos 2),
    not_isNCC_and le_rfl (correctnessExclusivity_nccUtil (by norm_num)) (uniformPrior_pos 2)⟩

/-- Concrete 5-player majority is `2-NCC` and fails `3-NCC` (`isKNCC_majority_iff`). -/
example (fallback : Fin 5 → Bool → Bool) :
    IsKNCC (Cslib.majority 5) 2 (nccUtil 5 500) (uniformPrior 5) fallback ∧
      ¬ IsKNCC (Cslib.majority 5) 3 (nccUtil 5 500) (uniformPrior 5) fallback := by
  have hiff := fun k => isKNCC_majority_iff (m := 2) (k := k) (by omega)
    (fallback := fallback)
    (correctnessExclusivity_nccUtil (M := 500) (by norm_num))
    (isMixedStrategy_uniformPrior 5)
    (highCorrectnessPriority_nccUtil (M := 500) (by norm_num))
  exact ⟨(hiff 2).mpr le_rfl, fun h => by have := (hiff 3).mp h; omega⟩

/-! ### 3. Boundary witnesses for Theorem 8.6 hypotheses -/

/-- Boundary witness 1 (necessity of non-constancy / `EveryInputMatters`): the constant function
`fun _ : BitString 2 => true` is dominated, fails `EveryInputMatters`, and IS `IsNCC` when honest
players use the optimal fallback `fun _ _ => true`. -/
example :
    IsDominated (fun _ : Cslib.BitString 2 => true) ∧
      ¬ EveryInputMatters (fun _ : Cslib.BitString 2 => true) ∧
      IsNCC (fun _ : Cslib.BitString 2 => true) (nccUtil 2 100) (uniformPrior 2)
        (fun _ _ => true) := by
  refine ⟨⟨0, false, true, fun _ _ => rfl⟩, fun h => ?_, ?_⟩
  · obtain ⟨_, _, hne⟩ := h 0
    exact hne rfl
  · intro i dev
    have hD := isMixedStrategy_uniformPrior 2
    rw [payoff_mediatedGame_honest_eq _ _ hD, mediatedGame_payoff]
    let prof := Function.update (honestProfile fun _ _ => true) i dev
    have hle : ∀ t : Cslib.BitString 2,
        nccUtil 2 100 i (fun j =>
          decide ((prof j).interpret (t j) (mediatorReply (fun _ => true) prof t) = true)) ≤
          nccUtil 2 100 i (fun _ => true) := by
      intro t
      have hout : ∀ j, j ≠ i →
          (prof j).interpret (t j) (mediatorReply (fun _ => true) prof t) = true := by
        intro j hj
        simp only [prof]
        rw [Function.update_of_ne hj, mediatorReply_update_honest]
        cases dev.report (t i) <;> rfl
      have hcard0 : (Finset.univ.filter fun j : Fin 2 => j ≠ i ∧
          decide ((prof j).interpret (t j)
            (mediatorReply (fun _ => true) prof t) = true) = false).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _
        rintro ⟨hj, hfalse⟩
        simp [hout j hj] at hfalse
      have hcard_hon :
          (Finset.univ.filter fun j : Fin 2 => j ≠ i ∧ (true : Bool) = false).card = 0 := by
        simp
      simp only [nccUtil, hcard0, hcard_hon, Nat.cast_zero, add_zero]
      split_ifs <;> norm_num
    calc ∑ t : Cslib.BitString 2, uniformPrior 2 t * _
        ≤ ∑ t : Cslib.BitString 2, uniformPrior 2 t * nccUtil 2 100 i (fun _ => true) :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hle t) (hD.nonneg t)
      _ = nccUtil 2 100 i (fun _ => true) := by
          rw [← Finset.sum_mul, hD.sum_eq_one, one_mul]

/-- Boundary witness 2 (necessity of `2 ≤ Fintype.card ι`): single-player parity (`n = 1`) is
reversible yet IS `IsNCC`, because there is no other player to exclude. -/
example (fallback : Fin 1 → Bool → Bool) :
    IsReversible (Cslib.parity 1) ∧
      IsNCC (Cslib.parity 1) (nccUtil 1 100) (uniformPrior 1) fallback := by
  refine ⟨isReversible_parity le_rfl, fun i dev => ?_⟩
  have hD := isMixedStrategy_uniformPrior 1
  rw [payoff_mediatedGame_honest_eq _ _ hD, mediatedGame_payoff]
  have hle : ∀ t : Cslib.BitString 1,
      nccUtil 1 100 i (fun j =>
        decide ((Function.update (honestProfile fallback) i dev j).interpret (t j)
          (mediatorReply (Cslib.parity 1) (Function.update (honestProfile fallback) i dev) t)
          = Cslib.parity 1 t)) ≤ nccUtil 1 100 i (fun _ => true) := by
    intro t
    have hempty : ∀ c : Fin 1 → Bool,
        (Finset.univ.filter fun j : Fin 1 => j ≠ i ∧ c j = false).card = 0 := fun c => by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ h
      exact h.1 (Subsingleton.elim j i)
    simp only [nccUtil, hempty, Nat.cast_zero, add_zero]
    split_ifs <;> norm_num
  calc ∑ t : Cslib.BitString 1, uniformPrior 1 t * _
      ≤ ∑ t : Cslib.BitString 1, uniformPrior 1 t * nccUtil 1 100 i (fun _ => true) :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hle t) (hD.nonneg t)
    _ = nccUtil 1 100 i (fun _ => true) := by
        rw [← Finset.sum_mul, hD.sum_eq_one, one_mul]

end CslibFrontierTests.GameTheory.NonCooperativeComputation
