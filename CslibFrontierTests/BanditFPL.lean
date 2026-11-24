/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.MachineLearning.OnlineLearning.Bandit
import CslibFrontier.MachineLearning.OnlineLearning.FPL
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Worked examples and boundary tests for multi-armed bandits and Follow the Perturbed Leader

Ordinary-module client tests for `Bandit` and `FPL` (compiled without `import all`):

* `Bandit`:
  - `mabPlay_apply_explore` and `mabPlay_apply_exploit` on `Fin 2` inside blocks of length `m = 3`;
  - `mabPlay_bandit_congr` invariance when altering losses on unplayed arms, exploitation rounds,
    and current/future rounds (even outside `[0, 1]`);
  - observed-arm sensitivity counterexample showing that changing the single observed arm's loss at
    an earlier exploration round changes `mabPlay` (`1 / 2` vs. `2 / 3`);
  - non-divisible horizon `T = 7 = 2 * 3 + 1` for `mabPlay_expected_loss_le`;
  - Theorem 4.17 (`mabMW_expected_loss_le`) on concrete horizon `T = 16` (`N = 2`, exact `K = 4`,
    `m = 4`) and on the single-arm boundary `N = 1` (`Unit`, where regret is `0`).
* `FPL`:
  - `fplLeader` lexicographic tie-breaking and positive scale invariance (`fplLeader_smul_pos`);
  - combinatorial online linear optimization over 2-element subsets of `Fin 3`
    (`fpl_regret_le_sqrt`);
  - `fpl_experts_regret_le_sqrt` on `Fin 2`, `T = 8` (`2 * √(2 * 8) = 8`);
  - `isOnlineAlgorithm_fplExpertsProb` causality composed with `exists_dynamic_regret_ge`
    (Theorem 4.1) and `fplProb_congr` future-loss invariance.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.BanditFPL

open Finset Real
open Cslib.MachineLearning.OnlineLearning.Experts
open Cslib.MachineLearning.OnlineLearning.FPL
open scoped BigOperators

/-! ### Shared test loss sequences -/

/-- Alternating two-expert binary losses `(1, 0), (0, 1), (1, 0), (0, 1), …`. -/
private def altLoss (t : ℕ) (i : Fin 2) : ℝ :=
  if t % 2 = 0 then (if i = 0 then 1 else 0) else (if i = 1 then 1 else 0)

private lemma altLoss_mem_Icc (t : ℕ) (i : Fin 2) : altLoss t i ∈ Set.Icc (0 : ℝ) 1 := by
  unfold altLoss
  split_ifs <;> norm_num

private lemma isOnlineAlgorithm_pw_half {ι : Type*} [Fintype ι] [Nonempty ι] :
    IsOnlineAlgorithm (prob (mwFactor (1 / 2)) : (ℕ → ι → ℝ) → ℕ → ι → ℝ) :=
  isOnlineAlgorithm_prob fun x hx => by
    rw [mwFactor_apply]
    linarith [hx.2]

/-! ### Partial-information (bandit) block-exploration reduction (`Bandit.lean`) -/

/-- Canonical injection `0 ↦ 0, 1 ↦ 1` of `Fin 2` into `Fin 3`. -/
private def emb23 : Fin 2 ↪ Fin 3 := Fin.castLEEmb (by decide)

/-- Uniform injection schedule for `Fin 2` inside blocks of length `m = 3`. -/
private noncomputable def sched23 : ExplorationSchedule (Fin 2) 3 (Fin 2 ↪ Fin 3) :=
  uniformInjExplorationSchedule (by omega : 0 < 3) (by decide : Fintype.card (Fin 2) ≤ 3)

/-- Concrete block average over `m = 3`: block `0` of `altLoss` has `(1, 0), (0, 1), (1, 0)`,
giving `(2 / 3, 1 / 3)`. -/
example : blockAvgLoss 3 altLoss 0 0 = 2 / 3 ∧ blockAvgLoss 3 altLoss 0 1 = 1 / 3 := by
  simp only [blockAvgLoss_apply, Fin.sum_univ_three]
  norm_num [altLoss]

/-- Under `ω = ![emb23, emb23]`, in block `0` round `0` explores arm `0`, round `1` explores arm
`1`, and round `2` (`r = 2`) exploits with `H`. -/
example (H : (ℕ → Fin 2 → ℝ) → ℕ → Fin 2 → ℝ) :
    let ω : Fin 2 → (Fin 2 ↪ Fin 3) := ![emb23, emb23]
    mabPlay (by omega : 0 < 3) sched23 H ω altLoss 0 0 = 1 ∧
      mabPlay (by omega : 0 < 3) sched23 H ω altLoss 1 1 = 1 ∧
      mabPlay (by omega : 0 < 3) sched23 H ω altLoss 2 0 =
        H (exploredLoss sched23 ω altLoss) 0 0 := by
  intro ω
  refine ⟨?_, ?_, ?_⟩
  · have h := mabPlay_apply_explore (by omega : 0 < 3) sched23 H ω altLoss 0 0 0
    have h0 : (sched23.time (ω 0) 0).val = 0 := by
      simp only [sched23, uniformInjExplorationSchedule_time, emb23, ω]
      decide
    simpa only [Fin.val_zero, zero_mul, zero_add, h0, ↓reduceIte] using h
  · have h := mabPlay_apply_explore (by omega : 0 < 3) sched23 H ω altLoss 0 1 1
    have h1 : (sched23.time (ω 0) 1).val = 1 := by
      simp only [sched23, uniformInjExplorationSchedule_time, emb23, ω]
      decide
    simpa only [Fin.val_zero, zero_mul, zero_add, h1, ↓reduceIte] using h
  · have h := mabPlay_apply_exploit (by omega : 0 < 3) sched23 H ω altLoss 0
      (r := (2 : Fin 3)) (fun i => by
        simp only [sched23, uniformInjExplorationSchedule_time, emb23, ω]
        fin_cases i <;> decide) 0
    simpa only [Fin.val_zero, Fin.val_two, zero_mul, zero_add] using h

/-- **Bandit-feedback invariance (`mabPlay_bandit_congr`)**: under `ω = ![emb23, emb23]`, in block
`0` only `(t = 0, i = 0)` and `(t = 1, i = 1)` are observed. Replacing every other entry of
`altLoss` (the unplayed arms `(0, 1)` and `(1, 0)`, both arms at exploitation round `2`, and all
rounds `t ≥ 3`) with `42` leaves `mabPlay` at round `5` (`τ = 1, r = 2`) completely unchanged. -/
example :
    let ω : Fin 2 → (Fin 2 ↪ Fin 3) := ![emb23, emb23]
    let ℓ_unobs : ℕ → Fin 2 → ℝ := fun t i =>
      if (t = 0 ∧ i = 0) ∨ (t = 1 ∧ i = 1) then altLoss t i else 42
    mabPlay (by omega : 0 < 3) sched23 (prob (mwFactor (1 / 2))) ω altLoss 5 =
      mabPlay (by omega : 0 < 3) sched23 (prob (mwFactor (1 / 2))) ω ℓ_unobs 5 := by
  intro ω ℓ_unobs
  refine mabPlay_bandit_congr (by omega : 0 < 3) sched23 isOnlineAlgorithm_pw_half ω
    (fun σ _ i => altLoss_mem_Icc _ i) fun σ hσ i => ?_
  fin_cases σ
  · fin_cases i
    · have h0 : (sched23.time (ω 0) 0).val = 0 := by
        simp only [sched23, uniformInjExplorationSchedule_time, emb23, ω]
        decide
      change altLoss (0 * 3 + (sched23.time (ω 0) 0).val) 0 =
        ℓ_unobs (0 * 3 + (sched23.time (ω 0) 0).val) 0
      rw [h0]
      rfl
    · have h1 : (sched23.time (ω 0) 1).val = 1 := by
        simp only [sched23, uniformInjExplorationSchedule_time, emb23, ω]
        decide
      change altLoss (0 * 3 + (sched23.time (ω 0) 1).val) 1 =
        ℓ_unobs (0 * 3 + (sched23.time (ω 0) 1).val) 1
      rw [h1]
      rfl
  · change 1 < 5 / 3 at hσ
    omega

/-- **Observed-arm sensitivity witness**: flipping *only* the observed arm's loss at `(0, 0)`
from `altLoss 0 0 = 1` to `0` changes `mabPlay` in block `1` (round `5`) from `(1 / 2, 1 / 2)` to
`(2 / 3, 1 / 3)`, proving `mabPlay_bandit_congr`'s hypothesis cannot omit observed exploration
entries. -/
example :
    let ω : Fin 2 → (Fin 2 ↪ Fin 3) := ![emb23, emb23]
    let ℓ_obsFlip : ℕ → Fin 2 → ℝ := fun t i =>
      if t = 0 ∧ i = 0 then 0 else altLoss t i
    mabPlay (by omega : 0 < 3) sched23 (prob (mwFactor (1 / 2))) ω altLoss 5 0 = 1 / 2 ∧
      mabPlay (by omega : 0 < 3) sched23 (prob (mwFactor (1 / 2))) ω ℓ_obsFlip 5 0 = 2 / 3 ∧
      mabPlay (by omega : 0 < 3) sched23 (prob (mwFactor (1 / 2))) ω altLoss 5 ≠
        mabPlay (by omega : 0 < 3) sched23 (prob (mwFactor (1 / 2))) ω ℓ_obsFlip 5 := by
  intro ω ℓ_obsFlip
  have hnoexp : ∀ i : Fin 2, sched23.time (ω 1) i ≠ (2 : Fin 3) := fun i => by
    simp only [sched23, uniformInjExplorationSchedule_time, emb23, ω]
    fin_cases i <;> decide
  have hexpl_alt : mabPlay (by omega : 0 < 3) sched23 (prob (mwFactor (1 / 2))) ω altLoss 5 0 =
      prob (mwFactor (1 / 2)) (exploredLoss sched23 ω altLoss) 1 0 := by
    simpa only [Fin.isValue, Fin.val_one, Fin.val_two, one_mul, Nat.reduceAdd] using
      mabPlay_apply_exploit (by omega : 0 < 3) sched23 (prob (mwFactor (1 / 2))) ω altLoss 1
        hnoexp 0
  have hexpl_flip : mabPlay (by omega : 0 < 3) sched23 (prob (mwFactor (1 / 2))) ω ℓ_obsFlip 5 0 =
      prob (mwFactor (1 / 2)) (exploredLoss sched23 ω ℓ_obsFlip) 1 0 := by
    simpa only [Fin.isValue, Fin.val_one, Fin.val_two, one_mul, Nat.reduceAdd] using
      mabPlay_apply_exploit (by omega : 0 < 3) sched23 (prob (mwFactor (1 / 2))) ω ℓ_obsFlip 1
        hnoexp 0
  have ht0 : (sched23.time (ω ⟨0, by omega⟩) 0).val = 0 := by
    simp only [sched23, uniformInjExplorationSchedule_time, emb23, ω]
    decide
  have ht1 : (sched23.time (ω ⟨0, by omega⟩) 1).val = 1 := by
    simp only [sched23, uniformInjExplorationSchedule_time, emb23, ω]
    decide
  have hc_alt0 : exploredLoss sched23 ω altLoss 0 0 = 1 := by
    rw [exploredLoss_of_lt sched23 ω altLoss (by omega : 0 < 2) 0, zero_mul, zero_add, ht0]
    norm_num [altLoss]
  have hc_alt1 : exploredLoss sched23 ω altLoss 0 1 = 1 := by
    rw [exploredLoss_of_lt sched23 ω altLoss (by omega : 0 < 2) 1, zero_mul, zero_add, ht1]
    norm_num [altLoss]
  have hc_flip0 : exploredLoss sched23 ω ℓ_obsFlip 0 0 = 0 := by
    rw [exploredLoss_of_lt sched23 ω ℓ_obsFlip (by omega : 0 < 2) 0, zero_mul, zero_add, ht0]
    simp only [ℓ_obsFlip, and_self, ↓reduceIte]
  have hc_flip1 : exploredLoss sched23 ω ℓ_obsFlip 0 1 = 1 := by
    rw [exploredLoss_of_lt sched23 ω ℓ_obsFlip (by omega : 0 < 2) 1, zero_mul, zero_add, ht1]
    norm_num [ℓ_obsFlip, altLoss]
  have hval_alt : mabPlay (by omega : 0 < 3) sched23 (prob (mwFactor (1 / 2))) ω altLoss 5 0 =
      1 / 2 := by
    rw [hexpl_alt, prob, potential, Fin.sum_univ_two, weight_succ, weight_succ, weight_zero,
      weight_zero, hc_alt0, hc_alt1]
    norm_num [mwFactor_apply]
  have hval_flip : mabPlay (by omega : 0 < 3) sched23 (prob (mwFactor (1 / 2))) ω ℓ_obsFlip 5 0 =
      2 / 3 := by
    rw [hexpl_flip, prob, potential, Fin.sum_univ_two, weight_succ, weight_succ, weight_zero,
      weight_zero, hc_flip0, hc_flip1]
    norm_num [mwFactor_apply]
  refine ⟨hval_alt, hval_flip, fun heq => ?_⟩
  have hcongr := congrFun heq 0
  rw [hval_alt, hval_flip] at hcongr
  norm_num at hcongr

/-- Generic block reduction `mabPlay_expected_loss_le` on a non-divisible horizon
`T = 7 = 2 * 3 + 1` with capped Polynomial Weights (`mw_regret_le_sqrt_of_mem_Icc`). -/
example :
    have : Nonempty (Fin 2 ↪ Fin 3) := ⟨emb23⟩
    (𝔼 ω : Fin 2 → (Fin 2 ↪ Fin 3),
        ∑ t ∈ range 7, ∑ j,
          mabPlay (by omega : 0 < 3) sched23
            (prob (mwFactor (min √(log (Fintype.card (Fin 2)) / (2 : ℕ)) (1 / 2))))
            ω altLoss t j * altLoss t j) ≤
      minCumLoss altLoss 7 + 2 * 2 + 1 + 3 * (2 * √(2 * log 2)) := by
  have : Nonempty (Fin 2 ↪ Fin 3) := ⟨emb23⟩
  have halg : IsOnlineAlgorithm
      (prob (mwFactor (min √(log (Fintype.card (Fin 2)) / (2 : ℕ)) (1 / 2))) :
        (ℕ → Fin 2 → ℝ) → ℕ → Fin 2 → ℝ) :=
    isOnlineAlgorithm_prob fun x hx => by
      rw [mwFactor_apply]
      have hnn : 0 ≤ min √(log (Fintype.card (Fin 2)) / (2 : ℕ)) (1 / 2) :=
        le_min (sqrt_nonneg _) (by norm_num)
      have hle : min √(log (Fintype.card (Fin 2)) / (2 : ℕ)) (1 / 2) ≤ 1 / 2 := min_le_right _ _
      nlinarith [hx.2]
  have h := mabPlay_expected_loss_le (ι := Fin 2) (m := 3) (K := 2) (T := 7)
    (by omega) (by omega) sched23 halg (ℓ := altLoss) (fun t _ i => altLoss_mem_Icc t i)
    (R := 2 * √((2 : ℕ) * log (Fintype.card (Fin 2))))
    (fun c hc k => mw_regret_le_sqrt_of_mem_Icc hc k)
  simpa only [Fintype.card_fin, Nat.cast_ofNat, Nat.reduceMul, Nat.reduceSub, Nat.cast_one] using h

/-- Concrete Theorem 4.17 (`mabMW_expected_loss_le`) on `Fin 2` at `T = 16`: since
`16^{2/3} * 2^{1/3} = (16^2 * 2)^{1/3} = 8`, expected regret is at most `56 * log 2`. -/
example :
    let N := Fintype.card (Fin 2)
    let K := mabBlockCount N 16
    let m := mabBlockLen N 16
    let sched := uniformInjExplorationSchedule (ι := Fin 2)
      (mabBlockLen_pos Fintype.card_pos (by decide : N ≤ 16))
      (le_mabBlockLen Fintype.card_pos (by decide : N ≤ 16))
    let H := prob (mwFactor (min √(log N / K) (1 / 2)))
    (𝔼 ω : Fin K → (Fin 2 ↪ Fin m),
        ∑ t ∈ range 16, ∑ j, mabPlay (mabBlockLen_pos Fintype.card_pos (by decide : N ≤ 16))
          sched H ω altLoss t j * altLoss t j) ≤
      minCumLoss altLoss 16 + 56 * log 2 := by
  have h := mabMW_expected_loss_le (ι := Fin 2) (T := 16) (by decide)
    (ℓ := altLoss) (fun t _ i => altLoss_mem_Icc t i)
  have hpow16 : (16 : ℝ) ^ ((2 : ℝ) / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3) = 8 := by
    have h16 : (16 : ℝ) = 2 ^ (4 : ℝ) := by norm_num
    rw [h16, ← rpow_mul (by norm_num), ← rpow_add (by norm_num)]
    norm_num
  dsimp only at h ⊢
  refine h.trans_eq ?_
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  calc minCumLoss altLoss 16 +
        7 * (16 : ℝ) ^ ((2 : ℝ) / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3) * log 2
      = minCumLoss altLoss 16 +
          7 * ((16 : ℝ) ^ ((2 : ℝ) / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3)) * log 2 := by ring
    _ = minCumLoss altLoss 16 + 56 * log 2 := by rw [hpow16]; ring

/-- Single-arm degenerate boundary `N = 1` (`Unit`, `T = 5`) for `mabMW_expected_loss_le`: since
`log 1 = 0`, Theorem 4.17 gives exact zero regret `𝔼[L_MAB^5] ≤ minCumLoss ℓ 5`. -/
example (ℓ : ℕ → Unit → ℝ) (hℓ : ∀ t < 5, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) :
    let N := Fintype.card Unit
    let K := mabBlockCount N 5
    let m := mabBlockLen N 5
    let sched := uniformInjExplorationSchedule (ι := Unit)
      (mabBlockLen_pos Fintype.card_pos (by decide : N ≤ 5))
      (le_mabBlockLen Fintype.card_pos (by decide : N ≤ 5))
    let H := prob (mwFactor (min √(log N / K) (1 / 2)))
    (𝔼 ω : Fin K → (Unit ↪ Fin m),
        ∑ t ∈ range 5, ∑ j, mabPlay (mabBlockLen_pos Fintype.card_pos (by decide : N ≤ 5))
          sched H ω ℓ t j * ℓ t j) ≤
      minCumLoss ℓ 5 := by
  have h := mabMW_expected_loss_le (ι := Unit) (T := 5) (by decide) hℓ
  simpa only [Fintype.card_unit, Nat.cast_one, log_one, mul_zero, add_zero] using h

/-! ### Follow the Perturbed Leader (`FPL.lean`) -/

/-- Lexicographic tie-breaking and strict preference of `fplLeader`, plus positive scale invariance
(`fplLeader_smul_pos`). -/
example :
    fplLeader (fun a : Fin 2 => Pi.single a (1 : ℝ)) ![3, 3] = 0 ∧
      fplLeader (fun a : Fin 2 => Pi.single a (1 : ℝ)) ![4, 3] = 1 ∧
      fplLeader (fun a : Fin 2 => Pi.single a (1 : ℝ)) ((5 : ℝ) • ![4, 3]) = 1 := by
  have htie : fplLeader (fun a : Fin 2 => Pi.single a (1 : ℝ)) ![3, 3] = 0 := by
    rw [fplLeader_eq_iff]
    refine ⟨fun b => ?_, fun b hb => absurd hb (Fin.not_lt_zero b)⟩
    fin_cases b <;> norm_num [single_dotProduct]
  have hstrict : fplLeader (fun a : Fin 2 => Pi.single a (1 : ℝ)) ![4, 3] = 1 := by
    rw [fplLeader_eq_iff]
    refine ⟨fun b => ?_, fun b hb => ?_⟩
    · fin_cases b <;> norm_num [single_dotProduct]
    · fin_cases b
      · norm_num [single_dotProduct]
      · exact absurd hb (lt_irrefl _)
  exact ⟨htie, hstrict, (fplLeader_smul_pos _ (by norm_num : (0 : ℝ) < 5) _).trans hstrict⟩

/-- Combinatorial online linear optimization example: choosing a 2-element subset `Fin 3 \ {a}`
(`twoEdgeVec a i = if i = a then 0 else 1`) against `[0, 1]^3` edge costs over `T = 6` rounds
(`D = 1`, `R = 1`, `A = 3`, so `2 * √(1 * 1 * 3 * 6) = 2 * √18`). -/
private def twoEdgeVec (a i : Fin 3) : ℝ :=
  if i = a then 0 else 1

example (ℓ : ℕ → Fin 3 → ℝ) (hℓ : ∀ t < 6, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) (a_star : Fin 3) :
    let ε := √((1 : ℝ) / (1 * 3 * (6 : ℕ)))
    ∑ t ∈ range 6, ∑ a : Fin 3, fplProb twoEdgeVec ε ℓ t a * (twoEdgeVec a ⬝ᵥ ℓ t) ≤
      ∑ t ∈ range 6, (twoEdgeVec a_star ⬝ᵥ ℓ t) + 2 * √(18 : ℝ) := by
  have hdot : ∀ (c : Fin 3 → ℝ) (a : Fin 3), twoEdgeVec a ⬝ᵥ c = (∑ i, c i) - c a := fun c a => by
    have h1 : ∑ i : Fin 3, c i = c a + twoEdgeVec a ⬝ᵥ c := by
      have ha : c a = ∑ i : Fin 3, if i = a then c i else 0 := by
        simp only [sum_ite_eq', mem_univ, ↓reduceIte]
      rw [ha, dotProduct, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => by unfold twoEdgeVec; split_ifs <;> ring
    linarith
  have hspan_box : ∀ {u : Fin 3 → ℝ}, (∀ i, u i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ a b : Fin 3, twoEdgeVec a ⬝ᵥ u - twoEdgeVec b ⬝ᵥ u ≤ 1 := by
    intro u hu a b
    rw [hdot u a, hdot u b]
    linarith [(hu a).1, (hu b).2]
  have h := fpl_regret_le_sqrt twoEdgeVec (D := 1) (R := 1) (A := 3)
    zero_lt_one zero_lt_one (by norm_num) (ℓ := ℓ) (T := 6) (by omega)
    (fun a b u hu => hspan_box (fun i => ⟨hu.1 i, hu.2 i⟩) a b)
    (fun t ht a b => hspan_box (hℓ t ht) a b)
    (fun t ht => by
      calc ∑ i : Fin 3, |ℓ t i| ≤ ∑ _i : Fin 3, (1 : ℝ) := sum_le_sum fun i _ => by
            rw [abs_of_nonneg (hℓ t ht i).1]; exact (hℓ t ht i).2
        _ = 3 := by norm_num)
    a_star
  simpa only [Nat.cast_ofNat, show (1 : ℝ) * (1 * 3 * 6) = 18 by norm_num] using h

/-- Tuned FPL experts regret `fpl_experts_regret_le_sqrt` on `Fin 2`, `T = 8`: at most `8`. -/
example : ∑ t ∈ range 8, ∑ a : Fin 2,
      fplExpertsProb √(1 / (2 * 8)) altLoss t a * altLoss t a ≤
    ∑ t ∈ range 8, altLoss t 0 + 8 := by
  have h := fpl_experts_regret_le_sqrt (ι := Fin 2) (ℓ := altLoss) (T := 8) (by omega)
    (fun t _ i => altLoss_mem_Icc t i) 0
  have hsqrt : (2 : ℝ) * √(2 * 8) = 8 := by
    rw [show (2 : ℝ) * 8 = 4 ^ 2 by norm_num, sqrt_sq (by norm_num)]
    norm_num
  simpa only [Fintype.card_fin, Nat.cast_ofNat, hsqrt] using h

/-- Causality of `fplExpertsProb` (`isOnlineAlgorithm_fplExpertsProb`): future loss modifications
leave round-`t` distributions invariant (`fplProb_congr` via `fplExpertsProb_def`), and
`fplExpertsProb` satisfies Theorem 4.1's dynamic-regret lower bound (`exists_dynamic_regret_ge`). -/
example :
    (fplExpertsProb (ι := Fin 2) 1 altLoss 3 =
      fplExpertsProb (ι := Fin 2) 1 (fun s i => if s < 3 then altLoss s i else 99) 3) ∧
    ∃ (ℓ : ℕ → Fin 3 → ℝ) (g : ℕ → Fin 3),
      (∀ t < 6, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
      (∑ t ∈ range 6, ℓ t (g t) = 0) ∧
      (4 : ℝ) ≤ ∑ t ∈ range 6, ∑ i, fplExpertsProb 1 ℓ t i * ℓ t i := by
  refine ⟨?_, ?_⟩
  · rw [fplExpertsProb_def, fplExpertsProb_def]
    exact fplProb_congr _ 1 fun s hs => by
      funext i
      simp only [hs, ↓reduceIte]
  · obtain ⟨ℓ, g, h01, hg, hlb⟩ :=
      exists_dynamic_regret_ge (ι := Fin 3) (isOnlineAlgorithm_fplExpertsProb 1) 6
    refine ⟨ℓ, g, h01, hg, ?_⟩
    simp only [Fintype.card_fin, Nat.cast_ofNat] at hlb
    linarith

end CslibFrontierTests.BanditFPL
