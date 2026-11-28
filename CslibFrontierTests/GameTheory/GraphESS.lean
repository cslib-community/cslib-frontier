/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Evolutionary.GraphESS
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Evolutionary game theory over graphs: checked instances

Ordinary `module` client of
`CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.EdgeConcentration` and
`CslibFrontier.GameTheory.Evolutionary.GraphESS` exercising:

1. Concrete finite-graph witnesses for `graphFitness` and `survivingMutants` on a non-regular
   4-vertex graph with an isolated vertex (edges `{0, 1}` and `{1, 2}`, vertex `3` isolated):
   verifies exact neighborhood averages, `0` fitness at the isolated vertex, and survival of a
   mutant whose only neighbor has lower fitness.
2. Complete-graph `{K_n}` characterization (`isGraphESS_complete_iff`, `IsESS.isGraphESS_complete`,
   `IsGraphESS.isESS_of_complete`, `exists_isGraphESS_complete_not_isESS`):
   * `hawkDove 4 2` (pure Hawk `![1, 0]` is a graph ESS on `{K_n}`, pure Dove `![0, 1]` is not);
   * coordination game `!![1, 0; 0, 1]` (`![1, 0]` is a graph ESS on `{K_n}`, mixed `![1/2, 1/2]`
     is not);
   * boundary counterexample `!![0, 1; 0, 1]`, where `![1, 0]` is a graph ESS on loopless `{K_n}`
     despite not being a classical ESS.
3. Random-graph edge concentration and Bollobás Theorem 2.15 / [Suri2007] Theorem 29.18
   (`SimpleGraph.binomialRandom_real_edgeCount_abs_sub_ge_mul`,
   `SimpleGraph.tendsto_binomialRandom_real_forall_nonNeighborhood_le`).
4. Unconditional Lemma 29.17 (`tendsto_binomialRandom_real_forall_abnormalFitness_additive_le`,
   `tendsto_binomialRandom_real_forall_abnormalFitness_mul_le`) and Theorem 29.16
   (`binomialRandom_infinitePi_isGraphESS`), instantiated on `hawkDove 2 4` (which has both a
   negative entry `-1` and a zero entry `0`, with mixed ESS `![1 / 2, 1 / 2]`) for `c = 0`
   (`p n = 1 / 2`) and `c = 1 / 2` (`p n = 1 / √(n + 1)`).
5. Exercise 29.7 witnesses: concrete fitness computation on `survivorWitnessGame`, linear-size
   adversarial mutant instantiation at `p n = 1 / 2`, unconstrained-size instantiation at `p n = 1`,
   and the `p = 1` (`K_n`) boundary theorem `IsESS.eventually_forall_graphFitness_lt_complete`.
-/

public section

namespace CslibFrontierTests.GameTheory.GraphESS

open Cslib.GameTheory Cslib.GameTheory.BimatrixGame Matrix SimpleGraph
open Filter MeasureTheory ProbabilityTheory unitInterval
open scoped Finset Topology

private theorem isMixedStrategy_fin2 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 1) :
    IsMixedStrategy ![a, b] :=
  isMixedStrategy_iff.2 ⟨fun i => by fin_cases i <;> simpa, by simpa [Fin.sum_univ_two] using h⟩

/-! ### 1. Finite-graph fitness and surviving-mutant witnesses -/

/-- A 4-vertex non-regular graph: path `0 - 1 - 2` plus an isolated vertex `3`. -/
@[expose] def pathWithIsolated : SimpleGraph (Fin 4) where
  Adj u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1)
  symm := ⟨fun _ _ h => by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto⟩
  loopless := ⟨fun _ h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all⟩

instance : DecidableRel pathWithIsolated.Adj := fun u v => by
  change Decidable ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1))
  infer_instance

/-- On `pathWithIsolated`, vertex `3` is isolated and has fitness `0`. -/
theorem graphFitness_isolated_vertex :
    survivorWitnessGame.graphFitness pathWithIsolated
      (fun u => if u ∈ ({0} : Finset (Fin 4)) then ![0, 1] else ![1, 0]) 3 = 0 := by
  refine graphFitness_eq_zero_of_isIsolated _ _ _ fun v hv => ?_
  rcases hv with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)

/-- On `pathWithIsolated` under `survivorWitnessGame` with `M = {0}`, mutant `0` (only neighbor
`1`, incumbent) earns fitness `3`, whereas incumbent `1` (neighbors `0` and `2`) earns `(2 + 3)/2
= 5 / 2 < 3`, so `0 ∈ survivingMutants`. -/
theorem graphFitness_path_values_and_survival :
    survivorWitnessGame.graphFitness pathWithIsolated
        (fun u => if u ∈ ({0} : Finset (Fin 4)) then ![0, 1] else ![1, 0]) 0 = 3 ∧
      survivorWitnessGame.graphFitness pathWithIsolated
        (fun u => if u ∈ ({0} : Finset (Fin 4)) then ![0, 1] else ![1, 0]) 1 = 5 / 2 ∧
      (0 : Fin 4) ∈ survivorWitnessGame.survivingMutants pathWithIsolated {0} ![1, 0] ![0, 1] := by
  have hnb0 : pathWithIsolated.neighborFinset 0 = {1} := by
    ext v; simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    fin_cases v <;> decide
  have hnb1 : pathWithIsolated.neighborFinset 1 = {0, 2} := by
    ext v; simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    fin_cases v <;> decide
  have h0 : survivorWitnessGame.graphFitness pathWithIsolated
      (fun u => if u ∈ ({0} : Finset (Fin 4)) then ![0, 1] else ![1, 0]) 0 = 3 := by
    rw [graphFitness_eq, hnb0]
    norm_num [payoff₁_eq_dotProduct, dotProduct, mulVec, survivorWitnessGame_A, Fin.sum_univ_two]
  have h1 : survivorWitnessGame.graphFitness pathWithIsolated
      (fun u => if u ∈ ({0} : Finset (Fin 4)) then ![0, 1] else ![1, 0]) 1 = 5 / 2 := by
    rw [graphFitness_eq, hnb1]
    norm_num [payoff₁_eq_dotProduct, dotProduct, mulVec, survivorWitnessGame_A, Fin.sum_univ_two]
  refine ⟨h0, h1, ?_⟩
  rw [mem_survivingMutants_iff]
  refine ⟨Finset.mem_singleton_self _, ?_⟩
  rintro ⟨i, hiM, h0i, hlt⟩
  have hi1 : i = 1 := by
    rcases h0i with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · rfl
    all_goals exact absurd h (by decide)
  subst hi1
  linarith

/-! ### 2. Complete-graph `{K_n}` characterization and counterexample -/

/-- Coordination game `!![1, 0; 0, 1]`. -/
def coordGame : BimatrixGame (Fin 2) (Fin 2) :=
  ⟨!![1, 0; 0, 1], !![1, 0; 0, 1]ᵀ⟩

theorem coordGame_isGraphESS_complete_zero : coordGame.IsGraphESS (fun _ => ⊤) ![1, 0] := by
  apply IsESS.isGraphESS_complete
  rw [isESS_fin_two_iff]
  refine ⟨isMixedStrategy_fin2 zero_le_one le_rfl (by norm_num), Or.inl ⟨rfl, Or.inl ?_⟩⟩
  norm_num [coordGame]

theorem coordGame_not_isGraphESS_complete_half :
    ¬coordGame.IsGraphESS (fun _ => ⊤) ![1 / 2, 1 / 2] := by
  rw [isGraphESS_complete_iff]
  rintro ⟨-, h⟩
  have hne : (![1, 0] : Fin 2 → ℝ) ≠ ![1 / 2, 1 / 2] := fun heq => by
    have h0 := congrFun heq 0; norm_num at h0
  have h0 := h ![1, 0] (isMixedStrategy_fin2 zero_le_one le_rfl (by norm_num)) hne
  norm_num [payoff₁_eq_dotProduct, dotProduct, mulVec, coordGame, Fin.sum_univ_two] at h0

theorem hawkDove_gt_isGraphESS_complete_hawk :
    (hawkDove 4 2).IsGraphESS (fun _ => ⊤) ![1, 0] :=
  ((isESS_hawkDove_iff_of_lt (by norm_num) (by norm_num)).2 rfl).isGraphESS_complete

theorem complete_counterexample_client :
    ∃ (F : BimatrixGame (Fin 2) (Fin 2)) (s : Fin 2 → ℝ),
      F.B = F.Aᵀ ∧ F.IsGraphESS (fun _ => ⊤) s ∧ ¬F.IsESS s :=
  exists_isGraphESS_complete_not_isESS

/-! ### 3. Edge concentration and Bollobás Theorem 2.15 / NRTV Theorem 29.18 -/

theorem edgeCount_chernoff_instance :
    let p : I := ⟨1 / 2, by norm_num, by norm_num⟩
    let S : Finset (Sym2 (Fin 4)) := {s(0, 1), s(1, 2), s(2, 3)}
    G(Fin 4, p).real {G | (1 / 2 : ℝ) * ((#S : ℝ) * (p : ℝ)) ≤
      |(((S : Set (Sym2 (Fin 4))) ∩ G.edgeSet).ncard : ℝ) - (#S : ℝ) * (p : ℝ)|} ≤
      2 * Real.exp (-((1 / 2 : ℝ) ^ 2 * ((#S : ℝ) * (p : ℝ)) / 3)) := by
  intro p S
  refine binomialRandom_real_edgeCount_abs_sub_ge_mul p S ?_ (by norm_num) (by norm_num)
  intro e he
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl <;> decide

theorem bollobas_nonNeighborhood_instance :
    let p : ℕ → I := fun _ => ⟨1 / 2, by norm_num, by norm_num⟩
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | ∀ U : Finset (Fin n),
      #U = ⌈((n : ℝ) / 8) / (p n : ℝ)⌉₊ →
        (({x : Fin n | x ∉ U ∧
          Disjoint (G.neighborSet x) (U : Set (Fin n))} : Set (Fin n)).ncard : ℝ) ≤
          (n : ℝ) ^ (-(1 / 2 : ℝ)) * n}) atTop (𝓝 1) := by
  intro p
  have hδ : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
  have hlog : ∀ᶠ n : ℕ in atTop,
      3 * Real.log n ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * (p n : ℝ) * n := by
    have hlim : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop
    filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 6)),
      eventually_ge_atTop 1] with n hn hn1
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h1 := (div_le_iff₀ (Real.rpow_pos_of_pos hn_pos (1 / 2 : ℝ))).1 hn
    have hrpow : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := by
      calc (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)
          = (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (n : ℝ) ^ (-(1 / 2 : ℝ) + 1) := (Real.rpow_add hn_pos _ _).symm
        _ = (n : ℝ) ^ (1 / 2 : ℝ) := by norm_num
    change 3 * Real.log (n : ℝ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / 2 : ℝ) * (n : ℝ)
    linarith [show (n : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / 2 : ℝ) * (n : ℝ) =
      (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) by rw [← hrpow]; ring]
  have hClog : ∀ᶠ n : ℕ in atTop,
      3 * Real.log (Real.exp 1 / (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ (n : ℝ) / 8 := by
    have hlim : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp
          tendsto_natCast_atTop_atTop
    filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 24)),
      eventually_ge_atTop 48] with n hn hn48
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h1 := (div_le_iff₀ hn_pos).1 hn
    have hδ_pos : 0 < (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hn_pos _
    have hlog_eq : Real.log (Real.exp 1 / (n : ℝ) ^ (-(1 / 2 : ℝ))) =
        1 + (1 / 2 : ℝ) * Real.log (n : ℝ) := by
      rw [Real.log_div (Real.exp_pos 1).ne' hδ_pos.ne', Real.log_exp, Real.log_rpow hn_pos]
      ring
    rw [hlog_eq]
    have : (48 : ℝ) ≤ n := by exact_mod_cast hn48
    linarith
  have hinf : Tendsto (fun n : ℕ => ((n : ℝ) / 8) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * n) atTop atTop := by
    have hbase : Tendsto (fun n : ℕ => (1 / 8 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ)) atTop atTop :=
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp
        tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
    refine hbase.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hrpow : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) := by
      calc (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) ^ ((1 : ℝ) + -(1 / 2 : ℝ) + (1 : ℝ)) := by norm_num
        _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_add hn_pos, Real.rpow_add hn_pos]
        _ = (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) := by rw [Real.rpow_one]
    rw [hrpow]; ring
  exact tendsto_binomialRandom_real_forall_nonNeighborhood_le hδ hlog hClog hinf

/-! ### 4. Unconditional Theorem 29.16 and Lemma 29.17 instantiations -/

/-- Unconditional Theorem 29.16 on `hawkDove 2 4` (payoffs `-1, 2, 0, 1`, mixed ESS
`![1 / 2, 1 / 2]`) with `p n = 1 / 2` (`c = 0`). -/
theorem theorem_29_16_hawkDove_mixed_const_p :
    let p : ℕ → I := fun _ => ⟨1 / 2, by norm_num, by norm_num⟩
    (Measure.infinitePi fun n : ℕ => G(Fin n, p n))
      {G | (hawkDove 2 4).IsGraphESS G ![1 / 2, 1 / 2]} = 1 := by
  have hess : (hawkDove 2 4).IsESS ![1 / 2, 1 / 2] := by
    rw [isESS_hawkDove_iff_of_le (by norm_num) (by norm_num)]
    ext i; fin_cases i <;> norm_num
  refine binomialRandom_infinitePi_isGraphESS (c := 0) (by norm_num) ?_ (hawkDove 2 4) hess
  refine ⟨1 / 2, by norm_num, Eventually.of_forall fun n => ?_⟩
  simp

/-- Unconditional Theorem 29.16 on `hawkDove 2 4` with sparse `p n = 1 / √(n + 1)` (`c = 1 / 2`). -/
theorem theorem_29_16_hawkDove_mixed_sparse_p :
    let p : ℕ → I := fun n =>
      ⟨((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)),
        Real.rpow_nonneg (by positivity) _,
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) n])
          (by norm_num)⟩
    (Measure.infinitePi fun n : ℕ => G(Fin n, p n))
      {G | (hawkDove 2 4).IsGraphESS G ![1 / 2, 1 / 2]} = 1 := by
  intro p
  have hess : (hawkDove 2 4).IsESS ![1 / 2, 1 / 2] := by
    rw [isESS_hawkDove_iff_of_le (by norm_num) (by norm_num)]
    ext i; fin_cases i <;> norm_num
  refine binomialRandom_infinitePi_isGraphESS (c := 1 / 2) (by norm_num) ?_
    (hawkDove 2 4) hess
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hle : (n : ℝ) + 1 ≤ 4 * (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hrpow : ((n : ℝ) + 1) ^ (1 / 2 : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    calc ((n : ℝ) + 1) ^ (1 / 2 : ℝ) ≤ (4 * (n : ℝ)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hle (by norm_num)
      _ = (4 : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) :=
          Real.mul_rpow (by norm_num) hn_pos.le
      _ = 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
          have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
            rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
            norm_num
          rw [h4]
  change (1 / 2 : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ) ≤ ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ))
  rw [Real.rpow_neg (by positivity), ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- Unconditional multiplicative Lemma 29.17 instantiated on `survivorWitnessGame` (`0 < A i j`). -/
theorem lemma_29_17_mul_instance :
    let p : ℕ → I := fun _ => ⟨1 / 2, by norm_num, by norm_num⟩
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | ∀ M : Finset (Fin n),
      min (1 / 4 : ℝ) (1 - 1 / 4) * (n : ℝ) ≤ (#M : ℝ) →
        min (1 / 4 : ℝ) (1 - 1 / 4) * (n : ℝ) ≤ (#Mᶜ : ℝ) →
          (({u : Fin n | u ∉ M ∧ ¬(
            (1 - 1 / 12 : ℝ) *
                ((1 - (#M : ℝ) / n) * survivorWitnessGame.payoff₁ ![1, 0] ![1, 0] +
                  ((#M : ℝ) / n) * survivorWitnessGame.payoff₁ ![1, 0] ![0, 1]) ≤
              survivorWitnessGame.graphFitness G (fun v => if v ∈ M then ![0, 1] else ![1, 0]) u ∧
            survivorWitnessGame.graphFitness G (fun v => if v ∈ M then ![0, 1] else ![1, 0]) u ≤
              (1 + 1 / 12 : ℝ) *
                ((1 - (#M : ℝ) / n) * survivorWitnessGame.payoff₁ ![1, 0] ![1, 0] +
                  ((#M : ℝ) / n) * survivorWitnessGame.payoff₁ ![1, 0] ![0, 1]))} :
            Set (Fin n)).ncard : ℝ) ≤ 24 * Real.log (n : ℝ) / ((1 / 12 : ℝ) ^ 2 * (p n : ℝ)) ∧
          (({u : Fin n | u ∈ M ∧ ¬(
            (1 - 1 / 12 : ℝ) *
                ((1 - (#M : ℝ) / n) * survivorWitnessGame.payoff₁ ![0, 1] ![1, 0] +
                  ((#M : ℝ) / n) * survivorWitnessGame.payoff₁ ![0, 1] ![0, 1]) ≤
              survivorWitnessGame.graphFitness G (fun v => if v ∈ M then ![0, 1] else ![1, 0]) u ∧
            survivorWitnessGame.graphFitness G (fun v => if v ∈ M then ![0, 1] else ![1, 0]) u ≤
              (1 + 1 / 12 : ℝ) *
                ((1 - (#M : ℝ) / n) * survivorWitnessGame.payoff₁ ![0, 1] ![1, 0] +
                  ((#M : ℝ) / n) * survivorWitnessGame.payoff₁ ![0, 1] ![0, 1]))} :
            Set (Fin n)).ncard : ℝ) ≤ 24 * Real.log (n : ℝ) / ((1 / 12 : ℝ) ^ 2 * (p n : ℝ))})
      atTop (𝓝 1) := by
  refine tendsto_binomialRandom_real_forall_abnormalFitness_mul_le (c := 0) (by norm_num)
    ⟨1 / 2, by norm_num, Eventually.of_forall fun _ => by simp⟩
    survivorWitnessGame ?_ (isMixedStrategy_fin2 zero_le_one le_rfl (by norm_num))
    (isMixedStrategy_fin2 le_rfl zero_le_one (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [survivorWitnessGame_A]

/-! ### 5. Exercise 29.7 witnesses and `p = 1` boundary -/

theorem exercise_29_7_linear_half :
    ∃ (F : BimatrixGame (Fin 2) (Fin 2)) (s t : Fin 2 → ℝ),
      F.B = F.Aᵀ ∧ F.IsESS s ∧ IsMixedStrategy t ∧ t ≠ s ∧
      (Measure.infinitePi fun n : ℕ => G(Fin n, (⟨1 / 2, by norm_num, by norm_num⟩ : I)))
        {G | ∀ ε' > 0, ∃ M : ∀ n, Finset (Fin n), IsEpsLinear ε' M ∧
          ∀ᶠ n : ℕ in atTop, ∃ j ∈ M n,
            (∃ i, i ∉ M n ∧ (G n).Adj j i) ∧
            ∀ i, i ∉ M n → (G n).Adj j i →
              F.graphFitness (G n) (fun u => if u ∈ M n then t else s) i <
                F.graphFitness (G n) (fun u => if u ∈ M n then t else s) j} = 1 := by
  obtain ⟨F, s, t, hsym, hess, ht, hne, h⟩ :=
    exists_game_adversarial_linear_mutant_beats_all_incumbent_neighbors
  exact ⟨F, s, t, hsym, hess, ht, hne,
    h (c := 0) (by norm_num) ⟨1 / 2, by norm_num, Eventually.of_forall fun _ => by simp⟩
      ⟨1 / 2, by norm_num, Eventually.of_forall fun _ => le_rfl⟩⟩

theorem exercise_29_7_unconstrained_one :
    ∃ (F : BimatrixGame (Fin 2) (Fin 2)) (s t : Fin 2 → ℝ),
      F.B = F.Aᵀ ∧ F.IsESS s ∧ IsMixedStrategy t ∧ t ≠ s ∧
      Tendsto (fun n : ℕ => G(Fin n, (1 : I)).real {G | ∃ M : Finset (Fin n), ∃ j ∈ M,
        (∃ i, i ∉ M ∧ G.Adj j i) ∧
        ∀ i, i ∉ M → G.Adj j i →
          F.graphFitness G (fun u => if u ∈ M then t else s) i <
            F.graphFitness G (fun u => if u ∈ M then t else s) j}) atTop (𝓝 1) := by
  obtain ⟨F, s, t, hsym, hess, ht, hne, h⟩ :=
    exists_game_adversarial_mutant_beats_all_incumbent_neighbors
  exact ⟨F, s, t, hsym, hess, ht, hne,
    h (c := 0) (by norm_num) ⟨1, by norm_num, Eventually.of_forall fun _ => by simp⟩⟩

/-- Boundary at `p = 1` (`K_n`): on `survivorWitnessGame`, every mutant in any `ε_t`-linear mutant
family eventually has strictly lower fitness than every incumbent. -/
theorem exercise_29_7_boundary_complete :
    ∃ εt > 0, ∀ M, IsEpsLinear εt M →
      ∀ᶠ n : ℕ in atTop, ∀ j ∈ M n, ∀ i, i ∉ M n →
        survivorWitnessGame.graphFitness (⊤ : SimpleGraph (Fin n))
            (fun u => if u ∈ M n then ![0, 1] else ![1, 0]) j <
          survivorWitnessGame.graphFitness (⊤ : SimpleGraph (Fin n))
            (fun u => if u ∈ M n then ![0, 1] else ![1, 0]) i :=
  survivorWitnessGame_isESS.eventually_forall_graphFitness_lt_complete
    (isMixedStrategy_fin2 le_rfl zero_le_one (by norm_num))
    (fun h => by have h0 := congrFun h 0; norm_num at h0)

end CslibFrontierTests.GameTheory.GraphESS
