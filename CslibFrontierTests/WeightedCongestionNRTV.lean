/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Congestion.WeightedAffine
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Checked tests for weighted atomic congestion games (NRTV Chapter 18)

Concrete boundary and witness checks for `CslibFrontier.GameTheory.Congestion.Weighted` and
`CslibFrontier.GameTheory.Congestion.WeightedAffine`:

1. Zero-weight player boundary (`weight = (0, 3)`), verifying zero individual cost and exact
   `affinePotential = 2 * socialCost` tightness on a single-user linear edge.
2. Explicit four-profile strict `CostGame.Improves` cycle in Goemans–Mirrokni–Vetta's `gmvGame`
   (`(3, 0) → (3, 1) → (2, 1) → (2, 0) → (3, 0)`).
3. Concrete three-player asymmetric game (`weights = (1, 2, 3)`) on two parallel affine links,
   checking pure Nash equilibrium and social cost `42`.
4. Separation `5 / 2 < (3 + √5) / 2` instantiated on `aaeTriangleGame` (`(φ, 1)` strictly
   exceeding `5 / 2`) and two-player weighted separation at `weights = (4, 5)`
   (`twoPlayerRatio 4 5 = 549 / 269 > 2`, strictly exceeding the unweighted two-player bound `2`).
-/

public section

namespace Cslib.GameTheory.WeightedCongestionTests

open Cslib.GameTheory Cslib.GameTheory.WeightedCongestionGame

/-! ### 1. Zero-weight boundary and `affinePotential = 2 * socialCost` witness -/

/-- Two-player single-resource linear game with zero-weight player `0` and weight-`3` player `1`. -/
@[expose] def zeroWeightGame : WeightedCongestionGame (Fin 2) (fun _ => Bool) Unit where
  resources _ b := if b then {()} else ∅
  weight i := if i = 0 then 0 else 3
  latency _ x := 2 * x

theorem zeroWeightGame_player0_cost_zero (s : Fin 2 → Bool) :
    zeroWeightGame.toCostGame.cost 0 s = 0 := by
  simp [zeroWeightGame]

theorem zeroWeightGame_affinePotential_eq_two_mul :
    let s : Fin 2 → Bool := fun _ => true
    zeroWeightGame.toCostGame.socialCost s = 18 ∧
      zeroWeightGame.affinePotential s = 36 := by
  intro s
  have h1 : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have hload : zeroWeightGame.load s () = 3 := by
    rw [zeroWeightGame.load_eq_ite_add_erase s 0 (), h1, Finset.sum_singleton]
    norm_num [zeroWeightGame, s]
  constructor
  · rw [zeroWeightGame.socialCost_toCostGame s, Finset.univ_unique, Finset.sum_singleton]
    change zeroWeightGame.load s () * zeroWeightGame.latency () (zeroWeightGame.load s ()) = 18
    rw [hload]
    norm_num [zeroWeightGame]
  · rw [zeroWeightGame.affinePotential_def s, Finset.univ_unique, Finset.sum_singleton]
    have hself : (∑ i with () ∈ zeroWeightGame.resources i (s i),
        zeroWeightGame.weight i * zeroWeightGame.latency () (zeroWeightGame.weight i)) = 18 := by
      have heq : (∑ i with () ∈ zeroWeightGame.resources i (s i),
            zeroWeightGame.weight i * zeroWeightGame.latency () (zeroWeightGame.weight i)) =
          ∑ i : Fin 2, if () ∈ zeroWeightGame.resources i (s i) then
            zeroWeightGame.weight i * zeroWeightGame.latency () (zeroWeightGame.weight i)
          else 0 := by
        rw [← Finset.sum_filter]
      have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
      rw [heq, huniv]
      norm_num [zeroWeightGame, s]
    change zeroWeightGame.load s () * zeroWeightGame.latency () (zeroWeightGame.load s ()) +
      (∑ i with () ∈ zeroWeightGame.resources i (s i),
        zeroWeightGame.weight i * zeroWeightGame.latency () (zeroWeightGame.weight i)) = 36
    rw [hload, hself]
    norm_num [zeroWeightGame]

/-! ### 2. Explicit 4-state strict improvement cycle in `gmvGame` -/

/-- First profile `(3, 0)` of the four-state strict improvement cycle in `gmvGame`. -/
@[expose] def gmvState0 : Fin 2 → Fin 4 := fun i => if i = 0 then 3 else 0
/-- Second profile `(3, 1)` of the four-state strict improvement cycle in `gmvGame`. -/
@[expose] def gmvState1 : Fin 2 → Fin 4 := fun i => if i = 0 then 3 else 1
/-- Third profile `(2, 1)` of the four-state strict improvement cycle in `gmvGame`. -/
@[expose] def gmvState2 : Fin 2 → Fin 4 := fun i => if i = 0 then 2 else 1
/-- Fourth profile `(2, 0)` of the four-state strict improvement cycle in `gmvGame`. -/
@[expose] def gmvState3 : Fin 2 → Fin 4 := fun i => if i = 0 then 2 else 0

private lemma gmvTestLoad (s : Fin 2 → Fin 4) (e : Fin 6) :
    gmvGame.load s e =
      (if e ∈ gmvPaths (s 0) then 1 else 0) + (if e ∈ gmvPaths (s 1) then 2 else 0) := by
  rw [gmvGame.load_eq_ite_add_erase s 0 e]
  have h1 : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  rw [h1, Finset.sum_singleton]
  simp [gmvGame]

theorem gmvGame_four_cycle_improves :
    gmvGame.toCostGame.Improves gmvState1 gmvState0 ∧
      gmvGame.toCostGame.Improves gmvState2 gmvState1 ∧
      gmvGame.toCostGame.Improves gmvState3 gmvState2 ∧
      gmvGame.toCostGame.Improves gmvState0 gmvState3 := by
  refine ⟨⟨1, 1, ?_, ?_⟩, ⟨0, 2, ?_, ?_⟩, ⟨1, 0, ?_, ?_⟩, ⟨0, 3, ?_, ?_⟩⟩
  · funext i; fin_cases i <;> rfl
  · simp only [toCostGame_cost, unitCost, gmvTestLoad]
    norm_num [gmvGame, gmvPaths, gmvLatency, gmvState0, gmvState1, Fin.isValue]
  · funext i; fin_cases i <;> rfl
  · simp only [toCostGame_cost, unitCost, gmvTestLoad]
    norm_num [gmvGame, gmvPaths, gmvLatency, gmvState1, gmvState2, Fin.isValue]
  · funext i; fin_cases i <;> rfl
  · simp only [toCostGame_cost, unitCost, gmvTestLoad]
    norm_num [gmvGame, gmvPaths, gmvLatency, gmvState2, gmvState3, Fin.isValue]
  · funext i; fin_cases i <;> rfl
  · simp only [toCostGame_cost, unitCost, gmvTestLoad]
    norm_num [gmvGame, gmvPaths, gmvLatency, gmvState3, gmvState0, Fin.isValue]

/-! ### 3. Three-player asymmetric parallel-link game `(weights = 1, 2, 3)` -/

/-- Three-player congestion game with weights `(1, 2, 3)` on two parallel affine links. -/
@[expose] def parallelAffine3 : WeightedCongestionGame (Fin 3) (fun _ => Bool) Bool where
  resources _ b := {b}
  weight i := (i.val + 1 : ℝ)
  latency b x := if b then 2 * x + 1 else x + 4

theorem hasAffineLatencies_parallelAffine3 : parallelAffine3.HasAffineLatencies := by
  refine ⟨fun b => if b then 2 else 1, fun b => if b then 1 else 4,
    fun b => by cases b <;> norm_num, fun b => by cases b <;> norm_num,
    fun b x => by cases b <;> simp [parallelAffine3]⟩

theorem parallelAffine3_balanced_isPureNash :
    let s : Fin 3 → Bool := fun i => decide (i ≠ 2)
    parallelAffine3.toCostGame.IsPureNash s ∧
      parallelAffine3.toCostGame.socialCost s = 42 := by
  intro s
  have hsum3 : ∀ f : Fin 3 → ℝ, ∑ i : Fin 3, f i = f 0 + f 1 + f 2 := fun f => by
    have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  have hload : ∀ (t : Fin 3 → Bool) (b : Bool),
      parallelAffine3.load t b =
        (if t 0 = b then 1 else 0) + (if t 1 = b then 2 else 0) + (if t 2 = b then 3 else 0) :=
    fun t b => by
      have heq : parallelAffine3.load t b =
          ∑ i : Fin 3, if b ∈ parallelAffine3.resources i (t i) then
            parallelAffine3.weight i else 0 := by
        rw [load, ← Finset.sum_filter]
      rw [heq, hsum3]
      cases b <;> cases t 0 <;> cases t 1 <;> cases t 2 <;>
        norm_num [parallelAffine3, Fin.isValue]
  constructor
  · intro i a
    fin_cases i <;> cases a <;>
      simp only [toCostGame_cost, unitCost, hload] <;>
      norm_num [parallelAffine3, s, Function.update, Fin.isValue]
  · rw [CostGame.socialCost, hsum3]
    simp only [toCostGame_cost, unitCost, hload]
    norm_num [parallelAffine3, s, Fin.isValue]

/-! ### 4. Strict separation `5 / 2 < (3 + √5) / 2` and two-player `(4, 5)` separation `> 2` -/

theorem five_halves_lt_golden_poa : (5 / 2 : ℝ) < (3 + Real.sqrt 5) / 2 := by
  have h2 : (2 : ℝ) < Real.sqrt 5 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem aaeTriangleGame_weighted_exceeds_five_halves :
    let φ := (1 + Real.sqrt 5) / 2
    (aaeTriangleGame φ 1).toCostGame.IsPureNash (fun _ => false) ∧
      5 / 2 * (aaeTriangleGame φ 1).toCostGame.socialCost (fun _ => true) <
        (aaeTriangleGame φ 1).toCostGame.socialCost (fun _ => false) := by
  intro φ
  obtain ⟨hne, hpos, heq⟩ := aaeTriangleGame_weighted_golden
  refine ⟨hne, ?_⟩
  rw [heq]
  exact mul_lt_mul_of_pos_right five_halves_lt_golden_poa hpos

theorem twoPlayerRatio_four_five_gt_two :
    twoPlayerRatio 4 5 = 549 / 269 ∧ (2 : ℝ) < twoPlayerRatio 4 5 ∧
      twoPlayerRatio 4 5 ≤ 21 / 10 := by
  have heq : twoPlayerRatio 4 5 = 549 / 269 := by
    norm_num [twoPlayerRatio]
  refine ⟨heq, ?_, twoPlayerRatio_le_twenty_one_tenths (by norm_num) (by norm_num)⟩
  rw [heq]
  norm_num

theorem twoPlayerTightGame_four_five_exceeds_two :
    (twoPlayerTightGame 4 5).toCostGame.IsPureNash (fun _ => false) ∧
      2 * (twoPlayerTightGame 4 5).toCostGame.socialCost (fun _ => true) <
        (twoPlayerTightGame 4 5).toCostGame.socialCost (fun _ => false) := by
  obtain ⟨hne, hpos, heq⟩ :=
    exists_two_player_socialCost_eq_twoPlayerRatio_mul (by norm_num : (0 : ℝ) < 4)
      (by norm_num : (0 : ℝ) < 5)
  refine ⟨hne, ?_⟩
  rw [heq, twoPlayerRatio_four_five_gt_two.1]
  linarith

end Cslib.GameTheory.WeightedCongestionTests
