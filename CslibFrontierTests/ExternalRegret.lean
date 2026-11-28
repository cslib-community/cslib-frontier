/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.MachineLearning.OnlineLearning.Greedy
import CslibFrontier.MachineLearning.OnlineLearning.Hedge
import CslibFrontier.MachineLearning.OnlineLearning.LowerBounds
import CslibFrontier.MachineLearning.OnlineLearning.MultiplicativeWeights
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Worked examples and boundary tests for external regret

Ordinary-module client tests for `Greedy`, `LowerBounds`, and `mw_regret_le_sqrt_of_mem_Icc`:

* `Greedy`: exact `minCumLoss`, `leaders`, `greedyPlay` tie-breaking, Theorem 4.2 on alternating
  losses plus a non-leader failure witness, Randomized Greedy probabilities and Theorem 4.4 on
  binary losses, and a `[0, 1]` perturbation witness showing Theorem 4.4 requires `{0, 1}` losses.
* `MultiplicativeWeights`: `mw_regret_le_sqrt_of_mem_Icc` in the small-horizon capped regime
  `T = 1 < 4 ln 2`, the uncapped regime `T = 4`, and the degenerate boundaries `T = 0` and `N = 1`.
* `LowerBounds`: `IsOnlineAlgorithm` satisfied by Polynomial Weights (`prob (mwFactor (1 / 2))`),
  Hedge, and `randGreedyProb`, and falsified by a non-causal (clairvoyant) learner; Theorems 4.1,
  4.3, 4.7 (boundary `N = 2 ^ T`), 4.8 (`N = 2`), and Exercise 4.5 (`T = N = 4`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.ExternalRegret

open Finset Real Cslib.MachineLearning.OnlineLearning.Experts
open scoped BigOperators

/-! ### Greedy (Theorem 4.2) and Randomized Greedy (Theorem 4.4) -/

/-- Alternating two-expert binary losses `(1, 0), (0, 1), (1, 0), (0, 1), …`. -/
private def altLoss (t : ℕ) (i : Fin 2) : ℝ :=
  if t % 2 = 0 then (if i = 0 then 1 else 0) else (if i = 1 then 1 else 0)

private lemma altLoss_mem_Icc (t : ℕ) (i : Fin 2) : altLoss t i ∈ Set.Icc (0 : ℝ) 1 := by
  unfold altLoss
  split_ifs <;> norm_num

private lemma altLoss_binary (t : ℕ) (i : Fin 2) : altLoss t i = 0 ∨ altLoss t i = 1 := by
  unfold altLoss
  split_ifs <;> simp

/-- Exact `minCumLoss`, `leaders`, and `greedyPlay` tie-breaking at `t = 0, 1, 4`. -/
example :
    minCumLoss altLoss 4 = 2 ∧
      greedyPlay altLoss 0 = 0 ∧
      greedyPlay altLoss 1 = 1 := by
  have h04 : ∑ s ∈ range 4, altLoss s 0 = 2 := by
    simp only [sum_range_succ, range_zero, sum_empty, zero_add]
    norm_num [altLoss]
  have h14 : ∑ s ∈ range 4, altLoss s 1 = 2 := by
    simp only [sum_range_succ, range_zero, sum_empty, zero_add]
    norm_num [altLoss]
  have hmin4 : minCumLoss altLoss 4 = 2 := by
    apply le_antisymm
    · exact (minCumLoss_le altLoss 4 0).trans_eq h04
    · refine le_minCumLoss_iff.mpr fun i => ?_
      fin_cases i
      · exact h04.ge
      · exact h14.ge
  have hg0 : greedyPlay altLoss 0 = 0 := by
    have hle : greedyPlay altLoss 0 ≤ 0 :=
      greedyPlay_le (by simp only [leaders_zero, mem_univ])
    exact le_antisymm hle (Fin.zero_le _)
  have hmin1 : minCumLoss altLoss 1 = 0 := by
    apply le_antisymm
    · have h11 : ∑ s ∈ range 1, altLoss s 1 = 0 := by norm_num [altLoss]
      exact (minCumLoss_le altLoss 1 1).trans_eq h11
    · exact minCumLoss_nonneg fun s _ i => (altLoss_mem_Icc s i).1
  have hmem1 : greedyPlay altLoss 1 ∈ leaders altLoss 1 := greedyPlay_mem_leaders altLoss 1
  have hg1 : greedyPlay altLoss 1 = 1 := by
    have hsum := mem_leaders.mp hmem1
    rw [hmin1] at hsum
    generalize hval : greedyPlay altLoss 1 = v
    rw [hval] at hsum
    fin_cases v
    · exfalso
      norm_num [altLoss] at hsum
    · rfl
  exact ⟨hmin4, hg0, hg1⟩

/-- Theorem 4.2 on `altLoss` over `T = 4`: `L_Greedy^4 ≤ 2 * L_min^4 + 1`. -/
example : ∑ t ∈ range 4, altLoss t (greedyPlay altLoss t) ≤
    (2 : ℝ) * minCumLoss altLoss 4 + (2 - 1) := by
  have h := greedyPlay_loss_le (ι := Fin 2) (ℓ := altLoss) (T := 4) fun t _ i => altLoss_mem_Icc t i
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using h

/-- Non-leader failure witness for Theorem 4.2: always choosing expert `1` against constant losses
`(0, 1)` suffers loss `4 > 2 * 0 + (2 - 1) = 1`. -/
example : ¬ (∑ _t ∈ range 4, (fun (i : Fin 2) => if i = 0 then (0 : ℝ) else 1) 1 ≤
    (Fintype.card (Fin 2) : ℝ) * minCumLoss (fun _ (i : Fin 2) => if i = 0 then 0 else 1) 4 +
      ((Fintype.card (Fin 2) : ℝ) - 1)) := by
  have hmin : minCumLoss (fun _ (i : Fin 2) => if i = 0 then (0 : ℝ) else 1) 4 ≤ 0 := by
    have h0 := minCumLoss_le (fun _ (i : Fin 2) => if i = 0 then (0 : ℝ) else 1) 4 0
    simpa only [↓reduceIte, sum_const_zero] using h0
  simp only [Fintype.card_fin, Nat.cast_ofNat, sum_const, card_range, nsmul_eq_mul]
  norm_num at hmin ⊢
  linarith

/-- Concrete `randGreedyProb` evaluation through the public `of_mem`/`of_notMem` interface and
Theorem 4.4 on `altLoss` over `T = 2`. -/
example :
    randGreedyProb altLoss 0 0 = 1 / 2 ∧
      ∑ t ∈ range 2, ∑ i : Fin 2, randGreedyProb altLoss t i * altLoss t i ≤
        log (Fintype.card (Fin 2)) + (1 + log (Fintype.card (Fin 2))) * minCumLoss altLoss 2 := by
  refine ⟨?_, randGreedy_loss_le_log fun t _ i => altLoss_binary t i⟩
  rw [randGreedyProb_of_mem (by simp only [leaders_zero, mem_univ]), leaders_zero, card_univ,
    Fintype.card_fin]
  norm_num

/-- Perturbed `[0, 1]` losses on `Fin 2`: round `0` breaks the tie by `1 / 100`, after which
every round `t ≥ 1` has a unique leader that incurs loss `1`, witnessing that Theorem 4.4's
`ln N + (1 + ln N) L_min` bound requires `{0, 1}` losses. -/
private noncomputable def perturbedAltLoss (t : ℕ) (i : Fin 2) : ℝ :=
  if t = 0 then (if i = 0 then 0 else 1 / 100)
  else if t % 2 = 1 then (if i = 0 then 1 else 0)
  else (if i = 1 then 1 else 0)

/-- Boundary witness: `perturbedAltLoss` lies in `[0, 1]` yet `randGreedyProb` violates Theorem 4.4
at `T = 7` (`L_RG^7 = 6 + 1 / 200 > ln 2 + (1 + ln 2) * 3`). -/
example :
    (∀ t i, perturbedAltLoss t i ∈ Set.Icc (0 : ℝ) 1) ∧
      ¬ (∑ t ∈ range 7, ∑ i : Fin 2, randGreedyProb perturbedAltLoss t i * perturbedAltLoss t i ≤
        log (Fintype.card (Fin 2)) +
          (1 + log (Fintype.card (Fin 2))) * minCumLoss perturbedAltLoss 7) := by
  refine ⟨fun t i => by unfold perturbedAltLoss; split_ifs <;> norm_num, ?_⟩
  have hsum_step : ∀ (t : ℕ) (j k : Fin 2), j ≠ k →
      (∑ s ∈ range t, perturbedAltLoss s j) < (∑ s ∈ range t, perturbedAltLoss s k) →
      ∑ i : Fin 2, randGreedyProb perturbedAltLoss t i * perturbedAltLoss t i =
        perturbedAltLoss t j := by
    intro t j k hjk hlt
    have hall : ∀ i : Fin 2, i = j ∨ i = k := fun i => by
      have hi := i.isLt
      have hj := j.isLt
      have hk := k.isLt
      have hne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
      rcases eq_or_ne i.val j.val with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext (by omega))
    have hmin : minCumLoss perturbedAltLoss t = ∑ s ∈ range t, perturbedAltLoss s j := by
      apply le_antisymm (minCumLoss_le _ t j)
      refine le_minCumLoss_iff.mpr fun i => ?_
      rcases hall i with rfl | rfl
      · exact le_rfl
      · exact hlt.le
    have hlead : leaders perturbedAltLoss t = {j} := by
      ext i
      rw [mem_leaders, mem_singleton, hmin]
      rcases hall i with rfl | rfl
      · exact iff_of_true rfl rfl
      · exact ⟨fun h => absurd h hlt.ne', fun h => absurd h hjk.symm⟩
    rw [sum_eq_single j]
    · rw [randGreedyProb_of_mem (by rw [hlead, mem_singleton]), hlead, card_singleton,
        Nat.cast_one, div_one, one_mul]
    · intro i _ hij
      rw [randGreedyProb_of_notMem (by rw [hlead, mem_singleton]; exact hij), zero_mul]
    · intro hj
      exact absurd (mem_univ j) hj
  have hr0 : ∑ i : Fin 2, randGreedyProb perturbedAltLoss 0 i * perturbedAltLoss 0 i = 1 / 200 := by
    rw [Fin.sum_univ_two,
      randGreedyProb_of_mem (by simp only [leaders_zero, mem_univ]),
      randGreedyProb_of_mem (by simp only [leaders_zero, mem_univ]),
      leaders_zero, card_univ, Fintype.card_fin]
    norm_num [perturbedAltLoss]
  have hr1 : ∑ i : Fin 2, randGreedyProb perturbedAltLoss 1 i * perturbedAltLoss 1 i = 1 := by
    rw [hsum_step 1 0 1 (by decide) (by norm_num [perturbedAltLoss])]
    norm_num [perturbedAltLoss]
  have hr2 : ∑ i : Fin 2, randGreedyProb perturbedAltLoss 2 i * perturbedAltLoss 2 i = 1 := by
    rw [hsum_step 2 1 0 (by decide) (by
      simp only [sum_range_succ, range_zero, sum_empty, zero_add]
      norm_num [perturbedAltLoss])]
    norm_num [perturbedAltLoss]
  have hr3 : ∑ i : Fin 2, randGreedyProb perturbedAltLoss 3 i * perturbedAltLoss 3 i = 1 := by
    rw [hsum_step 3 0 1 (by decide) (by
      simp only [sum_range_succ, range_zero, sum_empty, zero_add]
      norm_num [perturbedAltLoss])]
    norm_num [perturbedAltLoss]
  have hr4 : ∑ i : Fin 2, randGreedyProb perturbedAltLoss 4 i * perturbedAltLoss 4 i = 1 := by
    rw [hsum_step 4 1 0 (by decide) (by
      simp only [sum_range_succ, range_zero, sum_empty, zero_add]
      norm_num [perturbedAltLoss])]
    norm_num [perturbedAltLoss]
  have hr5 : ∑ i : Fin 2, randGreedyProb perturbedAltLoss 5 i * perturbedAltLoss 5 i = 1 := by
    rw [hsum_step 5 0 1 (by decide) (by
      simp only [sum_range_succ, range_zero, sum_empty, zero_add]
      norm_num [perturbedAltLoss])]
    norm_num [perturbedAltLoss]
  have hr6 : ∑ i : Fin 2, randGreedyProb perturbedAltLoss 6 i * perturbedAltLoss 6 i = 1 := by
    rw [hsum_step 6 1 0 (by decide) (by
      simp only [sum_range_succ, range_zero, sum_empty, zero_add]
      norm_num [perturbedAltLoss])]
    norm_num [perturbedAltLoss]
  have hRG : ∑ t ∈ range 7, ∑ i : Fin 2,
      randGreedyProb perturbedAltLoss t i * perturbedAltLoss t i = 1 / 200 + 6 := by
    simp only [sum_range_succ, range_zero, sum_empty, zero_add, hr0, hr1, hr2, hr3, hr4, hr5, hr6]
    ring
  have hmin7 : minCumLoss perturbedAltLoss 7 ≤ 3 := by
    refine (minCumLoss_le perturbedAltLoss 7 0).trans_eq ?_
    simp only [sum_range_succ, range_zero, sum_empty, zero_add]
    norm_num [perturbedAltLoss]
  have hlog2 := log_two_lt_d9
  have hlog2_nn : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  intro hle
  rw [hRG, Fintype.card_fin, Nat.cast_ofNat] at hle
  nlinarith

/-! ### Tuned Multiplicative Weights on `[0, 1]` losses (`mw_regret_le_sqrt_of_mem_Icc`) -/

/-- Small-horizon capped regime `T = 1 < 4 ln 2` on `Bool`, where `mw_regret_le_sqrt` does not
apply: `min √(ln 2 / 1) (1 / 2) = 1 / 2`. -/
example (ℓ : ℕ → Bool → ℝ) (hℓ : ∀ s < 1, ∀ i, ℓ s i ∈ Set.Icc (0 : ℝ) 1) (i : Bool) :
    ∑ t ∈ range 1, ∑ j,
        prob (mwFactor (min √(log (Fintype.card Bool) / (1 : ℕ)) (1 / 2))) ℓ t j * ℓ t j ≤
      ∑ t ∈ range 1, ℓ t i + 2 * √((1 : ℕ) * log (Fintype.card Bool)) :=
  mw_regret_le_sqrt_of_mem_Icc hℓ i

/-- Uncapped regime `T = 4 ≥ 4 ln 2` on `altLoss`. -/
example :
    ∑ t ∈ range 4, ∑ j : Fin 2,
        prob (mwFactor (min √(log (Fintype.card (Fin 2)) / (4 : ℕ)) (1 / 2))) altLoss t j *
          altLoss t j ≤
      ∑ t ∈ range 4, altLoss t 0 + 2 * √((4 : ℕ) * log (Fintype.card (Fin 2))) :=
  mw_regret_le_sqrt_of_mem_Icc (fun s _ i => altLoss_mem_Icc s i) 0

/-- Degenerate boundaries `T = 0` and `N = 1` (`Unit`). -/
example (ℓ : ℕ → Unit → ℝ) (hℓ : ∀ s < 5, ∀ i, ℓ s i ∈ Set.Icc (0 : ℝ) 1) :
    (∑ t ∈ range 0, ∑ j : Unit,
        prob (mwFactor (min √(log (Fintype.card Unit) / (0 : ℕ)) (1 / 2))) ℓ t j * ℓ t j ≤
      ∑ t ∈ range 0, ℓ t () + 2 * √((0 : ℕ) * log (Fintype.card Unit))) ∧
    (∑ t ∈ range 5, ∑ j : Unit,
        prob (mwFactor (min √(log (Fintype.card Unit) / (5 : ℕ)) (1 / 2))) ℓ t j * ℓ t j ≤
      ∑ t ∈ range 5, ℓ t () + 2 * √((5 : ℕ) * log (Fintype.card Unit))) :=
  ⟨mw_regret_le_sqrt_of_mem_Icc (fun s hs => absurd hs (Nat.not_lt_zero s)) (),
    mw_regret_le_sqrt_of_mem_Icc hℓ ()⟩

/-! ### `IsOnlineAlgorithm` witnesses and lower bounds (Theorems 4.1, 4.3, 4.7, 4.8, Ex. 4.5) -/

/-- Polynomial Weights (`mwFactor (1 / 2)`) and Hedge (`hedgeFactor 1`) both satisfy
`IsOnlineAlgorithm` on `[0, 1]` losses. -/
private lemma isOnlineAlgorithm_pw_half {ι : Type*} [Fintype ι] [Nonempty ι] :
    IsOnlineAlgorithm (prob (mwFactor (1 / 2)) : (ℕ → ι → ℝ) → ℕ → ι → ℝ) :=
  isOnlineAlgorithm_prob fun x hx => by
    rw [mwFactor_apply]
    linarith [hx.2]

private lemma isOnlineAlgorithm_hedge_one {ι : Type*} [Fintype ι] [Nonempty ι] :
    IsOnlineAlgorithm (prob (hedgeFactor 1) : (ℕ → ι → ℝ) → ℕ → ι → ℝ) :=
  isOnlineAlgorithm_prob fun x _ => by
    rw [hedgeFactor_apply]
    exact exp_pos _

/-- Negative witness for `IsOnlineAlgorithm`: a clairvoyant learner that peeks at the current
round's loss vector `ℓ t` fails causality (`congr`). -/
example :
    ¬ IsOnlineAlgorithm (fun (ℓ : ℕ → Bool → ℝ) (t : ℕ) (i : Bool) =>
      if ℓ t false ≤ ℓ t true then (if i = false then 1 else 0)
      else (if i = true then 1 else 0)) := by
  intro h
  let ℓ₁ : ℕ → Bool → ℝ := fun _ i => if i = false then 0 else 1
  let ℓ₂ : ℕ → Bool → ℝ := fun _ i => if i = false then 1 else 0
  have heq := h.congr (ℓ := ℓ₁) (ℓ' := ℓ₂) (t := 0)
    (fun _ hs => absurd hs (Nat.not_lt_zero _))
    (fun _ hs => absurd hs (Nat.not_lt_zero _))
  have hf := congrFun heq false
  norm_num [ℓ₁, ℓ₂] at hf

/-- Theorem 4.1 applied to Polynomial Weights (`prob (mwFactor (1 / 2))`) on `Fin 3`, `T = 6`:
dynamic regret at least `4`. -/
example : ∃ (ℓ : ℕ → Fin 3 → ℝ) (g : ℕ → Fin 3),
    (∀ t < 6, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
    (∑ t ∈ range 6, ℓ t (g t) = 0) ∧
    (4 : ℝ) ≤ ∑ t ∈ range 6, ∑ i, prob (mwFactor (1 / 2)) ℓ t i * ℓ t i := by
  obtain ⟨ℓ, g, h01, hg, hlb⟩ :=
    exists_dynamic_regret_ge (ι := Fin 3) isOnlineAlgorithm_pw_half 6
  refine ⟨ℓ, g, h01, hg, ?_⟩
  simp only [Fintype.card_fin, Nat.cast_ofNat] at hlb
  linarith

/-- Theorem 4.3 applied to `greedyPlay` on `Fin 3`, `T = 7`: total loss `7` and exact
`minCumLoss ℓ 7 = ⌊7 / 3⌋ = 2`. -/
example : ∃ ℓ : ℕ → Fin 3 → ℝ,
    (∀ t < 7, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
    (∑ t ∈ range 7, ℓ t (greedyPlay ℓ t) = 7) ∧
    minCumLoss ℓ 7 = 2 := by
  obtain ⟨ℓ, h01, hloss, hmin⟩ := exists_deterministic_loss_eq_and_minCumLoss_eq (ι := Fin 3)
    (D := greedyPlay) (fun {_ _ _} _ h => greedyPlay_congr h) 7
  refine ⟨ℓ, h01, by simpa only [Nat.cast_ofNat] using hloss, ?_⟩
  simp only [Fintype.card_fin] at hmin
  norm_num at hmin
  exact hmin

/-- Theorem 4.7 boundary case `N = 8 = 2 ^ 3`, `T = 3`: expected loss `3 / 2` for every online
algorithm (including Polynomial Weights) while `minCumLoss = 0` deterministically. -/
example : ∃ ℓ : (Fin 3 → Bool) → ℕ → Fin 8 → ℝ,
    (∀ w t i, ℓ w t i = 0 ∨ ℓ w t i = 1) ∧
    (∀ w, minCumLoss (ℓ w) 3 = 0) ∧
    (𝔼 w : Fin 3 → Bool,
      ∑ t ∈ range 3, ∑ i, prob (mwFactor (1 / 2)) (ℓ w) t i * ℓ w t i) = 3 / 2 := by
  obtain ⟨ℓ, h01, hmin, hexp⟩ :=
    exists_stochastic_loss_eq_half_minCumLoss_zero (ι := Fin 8) (T := 3) (by decide)
  exact ⟨ℓ, h01, hmin, by simpa only [Nat.cast_ofNat] using hexp _ isOnlineAlgorithm_pw_half⟩

/-- Theorem 4.8 at `N = 2` (`Bool`), `T = 16`: expected loss `8` and expected external regret at
least `2 / e` for every online algorithm (in particular Hedge). -/
example : ∃ ℓ : (Fin 16 → Bool) → ℕ → Bool → ℝ,
    (∀ w t i, ℓ w t i = 0 ∨ ℓ w t i = 1) ∧
    (𝔼 w : Fin 16 → Bool,
      ∑ t ∈ range 16, ∑ i, prob (hedgeFactor 1) (ℓ w) t i * ℓ w t i) = 8 ∧
    2 / Real.exp 1 ≤ 𝔼 w : Fin 16 → Bool,
      ((∑ t ∈ range 16, ∑ i, prob (hedgeFactor 1) (ℓ w) t i * ℓ w t i) - minCumLoss (ℓ w) 16) := by
  obtain ⟨ℓ, h01, hspec⟩ := exists_two_experts_stochastic_regret_ge (ι := Bool) (by simp) 16
  obtain ⟨hexp, hreg⟩ := hspec _ isOnlineAlgorithm_hedge_one
  refine ⟨ℓ, h01, ?_, ?_⟩
  · exact hexp.trans (by norm_num)
  · have h16 : √((16 : ℕ) : ℝ) = 4 := by
      rw [Nat.cast_ofNat, show (16 : ℝ) = 4 ^ 2 by norm_num, sqrt_sq (by norm_num)]
    rw [h16] at hreg
    have hcoef : (1 / (2 * Real.exp 1)) * 4 = 2 / Real.exp 1 := by ring
    linarith

/-- Exercise 4.5 at `N = 4`, `T = 4` (`T ≥ N`, hence `Nat.log 2 4 = 2 ≤ 4`): expected regret at
least `(1 / (4 e)) * √(4 ln 4)` for every online algorithm (including `randGreedyProb`). -/
example : ∃ ℓ : (Fin 4 → Bool) → ℕ → Fin 4 → ℝ,
    (∀ w t i, ℓ w t i = 0 ∨ ℓ w t i = 1) ∧
    (1 / (4 * Real.exp 1)) * √((4 : ℝ) * log 4) ≤ 𝔼 w : Fin 4 → Bool,
      ((∑ t ∈ range 4, ∑ i, randGreedyProb (ℓ w) t i * ℓ w t i) - minCumLoss (ℓ w) 4) := by
  obtain ⟨ℓ, h01, hspec⟩ :=
    exists_stochastic_regret_ge_sqrt_mul_log (ι := Fin 4) (T := 4) (by simp) (by decide)
  refine ⟨ℓ, h01, ?_⟩
  have h := hspec _ isOnlineAlgorithm_randGreedyProb
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using h

end CslibFrontierTests.ExternalRegret
