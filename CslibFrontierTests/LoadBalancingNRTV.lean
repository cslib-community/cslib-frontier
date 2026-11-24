/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.LoadBalancing.Basic
import CslibFrontier.GameTheory.LoadBalancing.MixedNash
import CslibFrontier.GameTheory.LoadBalancing.PureNash
import CslibFrontier.GameTheory.LoadBalancing.PurePoA

/-!
# Selfish load-balancing games: non-vacuity and boundary witnesses

Concrete checked witnesses exercising `CslibFrontier.GameTheory.LoadBalancing`:

* Tight Finn–Horowitz pure Nash witnesses for `m = 1, 2, 3` identical machines (`1`, `4/3`, `3/2`).
* Tight Koutsoupias–Papadimitriou `3/2` mixed Nash witness on `2` identical machines.
* Tight golden-ratio `(1 + √5) / 2` pure Nash witness on `2` uniformly related machines.
* Empty job set (`Fin 0`) and zero-weight job boundary cases, including a strictly improving
  zero-weight move leaving all machine loads unchanged.
* Non-uniqueness of totally mixed Nash equilibria for `1` job on `2` identical machines
  (demonstrating necessity of `Fintype.card ι ≠ 1` in `eq_of_isTotallyMixedNash`).
* Boundary cases of `twoUnitRelated` (`s = 1`, `s = 1/2`, `s = 2`).
* Unrelated-machine unbounded pure PoA witness (`K = 100`) and non-equilibrium counterexamples.
* LPT pure Nash equilibrium and max-weight best-response convergence checks.
-/

namespace CslibFrontierTests.LoadBalancingNRTV

open Cslib.GameTheory
open Cslib.GameTheory.LoadBalancingGame

section IdenticalTightWitnesses

/-- `m = 1`: Finn–Horowitz ratio `2 * 1 / (1 + 1) = 1`. -/
example : (finnHorowitzTight 1).toCostGame.IsPureNash (finnHorowitzTightNE 1) ∧
    (finnHorowitzTight 1).makespan (finnHorowitzTightNE 1) = 2 ∧
    (finnHorowitzTight 1).optMakespan = 2 := by
  refine ⟨isPureNash_finnHorowitzTightNE 1, ?_, ?_⟩
  · simpa using makespan_finnHorowitzTightNE 1
  · rw [optMakespan_finnHorowitzTight 1]
    norm_num

/-- `m = 2`: Finn–Horowitz ratio `2 * 2 / (2 + 1) = 4 / 3`. -/
example : (finnHorowitzTight 2).toCostGame.IsPureNash (finnHorowitzTightNE 2) ∧
    (finnHorowitzTight 2).makespan (finnHorowitzTightNE 2) =
      4 / 3 * (finnHorowitzTight 2).optMakespan := by
  refine ⟨isPureNash_finnHorowitzTightNE 2, ?_⟩
  have h := makespan_finnHorowitzTightNE_eq_ratio 2
  norm_num at h
  exact h

/-- `m = 3`: Finn–Horowitz ratio `2 * 3 / (3 + 1) = 3 / 2`. -/
example : (finnHorowitzTight 3).toCostGame.IsPureNash (finnHorowitzTightNE 3) ∧
    (finnHorowitzTight 3).makespan (finnHorowitzTightNE 3) =
      3 / 2 * (finnHorowitzTight 3).optMakespan := by
  refine ⟨isPureNash_finnHorowitzTightNE 3, ?_⟩
  have h := makespan_finnHorowitzTightNE_eq_ratio 3
  norm_num at h
  exact h

end IdenticalTightWitnesses

section MixedAndRelatedWitnesses

/-- `m = 2` identical machines mixed NE attains the exact `3 / 2` Koutsoupias–Papadimitriou bound.
-/
example : kpTwoUnit.toCostGame.IsMixedNash kpTwoUnitUniform ∧
    kpTwoUnit.expectedMakespan kpTwoUnitUniform = 3 / 2 * kpTwoUnit.optMakespan ∧
    kpTwoUnit.optMakespan = 1 :=
  ⟨isMixedNash_kpTwoUnitUniform, expectedMakespan_kpTwoUnitUniform, optMakespan_kpTwoUnit⟩

/-- The `3 / 2` upper bound applies to `kpTwoUnitUniform`. -/
example : kpTwoUnit.expectedMakespan kpTwoUnitUniform ≤ 3 / 2 * kpTwoUnit.optMakespan := by
  have hId : kpTwoUnit.IsIdentical := fun _ => rfl
  exact hId.expectedMakespan_le_three_halves_mul_optMakespan isMixedNash_kpTwoUnitUniform

/-- `m = 2` uniformly related machines attains the exact golden ratio `(1 + √5) / 2`. -/
example : goldenRatioTight.toCostGame.IsPureNash goldenRatioTightNE ∧
    goldenRatioTight.makespan goldenRatioTightNE =
      ((1 + √5) / 2) * goldenRatioTight.optMakespan ∧
    goldenRatioTight.optMakespan = 1 :=
  ⟨isPureNash_goldenRatioTightNE, makespan_goldenRatioTightNE, optMakespan_goldenRatioTight⟩

/-- `twoUnitRelated` boundary: `s = 1` has unique totally mixed NE `1/2`; `s = 1/2` and `s = 2`
have no totally mixed NE. -/
example : ∃ p, (twoUnitRelated 1 zero_lt_one).toCostGame.IsTotallyMixedNash p :=
  (exists_isTotallyMixedNash_twoUnitRelated_iff zero_lt_one).mpr (by norm_num)

example : ¬ ∃ p, (twoUnitRelated (1 / 2) (by norm_num)).toCostGame.IsTotallyMixedNash p := by
  rw [exists_isTotallyMixedNash_twoUnitRelated_iff]
  norm_num

example : ¬ ∃ p, (twoUnitRelated 2 (by norm_num)).toCostGame.IsTotallyMixedNash p := by
  rw [exists_isTotallyMixedNash_twoUnitRelated_iff]
  norm_num

end MixedAndRelatedWitnesses

section BoundaryCases

/-- Empty job set (`Fin 0` jobs on `Fin 3` machines): trivial pure NE with `optMakespan = 0`. -/
def emptyJobsGame : LoadBalancingGame (Fin 0) (Fin 3) :=
  LoadBalancingGame.identical Fin.elim0 (fun i => i.elim0)

example : emptyJobsGame.toCostGame.HasFIP ∧
    emptyJobsGame.toCostGame.IsPureNash Fin.elim0 ∧
    emptyJobsGame.optMakespan = 0 := by
  refine ⟨emptyJobsGame.hasFIP, fun i => i.elim0, ?_⟩
  refine le_antisymm ?_ emptyJobsGame.optMakespan_nonneg
  exact (emptyJobsGame.optMakespan_le Fin.elim0).trans
    ((emptyJobsGame.makespan_le_iff Fin.elim0).mpr fun j => by
      simp [emptyJobsGame, load, UnrelatedLoadBalancingGame.load])

/-- Mixed zero-weight and positive-weight jobs: job `0` has weight `0` and job `1` has weight `2`
on `2` identical machines. Moving job `0` off machine `0` strictly improves its cost while keeping
all machine loads identical. -/
def zeroAndPosGame : LoadBalancingGame (Fin 2) (Fin 2) :=
  LoadBalancingGame.identical ![0, 2] (fun i => by fin_cases i <;> norm_num)

example : zeroAndPosGame.toCostGame.Improves ![1, 0] ![0, 0] ∧
    zeroAndPosGame.load ![1, 0] = zeroAndPosGame.load ![0, 0] ∧
    zeroAndPosGame.toCostGame.HasFIP := by
  have hload0 : ∀ j : Fin 2, zeroAndPosGame.load ![0, 0] j = if j = 0 then 2 else 0 := fun j => by
    rw [LoadBalancingGame.load_eq_sum_div, Finset.sum_filter, Fin.sum_univ_two]
    fin_cases j <;> simp [zeroAndPosGame, identical]
  have hload1 : ∀ j : Fin 2, zeroAndPosGame.load ![1, 0] j = if j = 0 then 2 else 0 := fun j => by
    rw [LoadBalancingGame.load_eq_sum_div, Finset.sum_filter, Fin.sum_univ_two]
    fin_cases j <;> simp [zeroAndPosGame, identical]
  refine ⟨⟨0, 1, ?_, ?_⟩, funext fun j => by rw [hload1 j, hload0 j], zeroAndPosGame.hasFIP⟩
  · ext i; fin_cases i <;> rfl
  · change zeroAndPosGame.load ![1, 0] 1 < zeroAndPosGame.load ![0, 0] 0
    rw [hload1 1, hload0 0]
    norm_num

/-- Non-uniqueness boundary for `eq_of_isTotallyMixedNash`: with `1` positive-weight job on `2`
identical machines (`Fintype.card ι = 1`), distinct totally mixed Nash equilibria exist. -/
def singleJobTwoMachines : LoadBalancingGame (Fin 1) (Fin 2) :=
  LoadBalancingGame.identical (fun _ => 1) (fun _ => zero_le_one)

example : ∃ p q, p ≠ q ∧
    singleJobTwoMachines.toCostGame.IsTotallyMixedNash p ∧
    singleJobTwoMachines.toCostGame.IsTotallyMixedNash q := by
  let p : Fin 1 → Fin 2 → ℝ := fun _ => ![1 / 2, 1 / 2]
  let q : Fin 1 → Fin 2 → ℝ := fun _ => ![1 / 3, 2 / 3]
  have hp : singleJobTwoMachines.toCostGame.IsTotallyMixedNash p := by
    rw [CostGame.isTotallyMixedNash_iff]
    refine ⟨fun _ j => by fin_cases j <;> norm_num [p],
      fun _ => by simp [Fin.sum_univ_two, p]; norm_num, fun i a b => ?_⟩
    have hp1 : ∀ k, ∑ m, p k m = 1 := fun _ => by simp [Fin.sum_univ_two, p]; norm_num
    rw [singleJobTwoMachines.deviationCost_toCostGame hp1 i a,
      singleJobTwoMachines.deviationCost_toCostGame hp1 i b]
    fin_cases i; fin_cases a <;> fin_cases b <;>
      simp [expectedLoad, singleJobTwoMachines, identical, p]
  have hq : singleJobTwoMachines.toCostGame.IsTotallyMixedNash q := by
    rw [CostGame.isTotallyMixedNash_iff]
    refine ⟨fun _ j => by fin_cases j <;> norm_num [q],
      fun _ => by simp [Fin.sum_univ_two, q]; norm_num, fun i a b => ?_⟩
    have hq1 : ∀ k, ∑ m, q k m = 1 := fun _ => by simp [Fin.sum_univ_two, q]; norm_num
    rw [singleJobTwoMachines.deviationCost_toCostGame hq1 i a,
      singleJobTwoMachines.deviationCost_toCostGame hq1 i b]
    fin_cases i; fin_cases a <;> fin_cases b <;>
      simp [expectedLoad, singleJobTwoMachines, identical, q]
  refine ⟨p, q, ?_, hp, hq⟩
  intro h
  have h0 : p 0 0 = q 0 0 := congrFun (congrFun h 0) 0
  norm_num [p, q] at h0

end BoundaryCases

section CounterexamplesAndAlgorithms

/-- Non-equilibrium counterexample on identical machines: placing both unit jobs on machine `0` is
not a pure Nash equilibrium because job `0` strictly improves by moving to machine `1`. -/
example : ¬ kpTwoUnit.toCostGame.IsPureNash (fun _ => 0) := by
  intro h
  have h0 := (kpTwoUnit.isPureNash_iff _).mp h 0 1 (by decide)
  have hl0 : kpTwoUnit.load (fun _ => 0) 0 = 2 := by
    rw [LoadBalancingGame.load_eq_sum_div, Finset.sum_filter, Fin.sum_univ_two]
    norm_num [kpTwoUnit, identical]
  have hl1 : kpTwoUnit.load (fun _ => 0) 1 = 0 := by
    rw [LoadBalancingGame.load_eq_sum_div, Finset.sum_filter, Fin.sum_univ_two]
    norm_num [kpTwoUnit, identical]
  rw [hl0, hl1] at h0
  norm_num [kpTwoUnit, identical] at h0

/-- Unrelated machines: concrete `K = 100` instance with pure Nash equilibrium `100` times worse
than `optMakespan = 1`. -/
example : ∃ (U : UnrelatedLoadBalancingGame (Fin 2) (Fin 2)) (A : Fin 2 → Fin 2),
    U.toCostGame.IsPureNash A ∧ U.makespan A = 100 * U.optMakespan ∧ U.optMakespan = 1 :=
  UnrelatedLoadBalancingGame.exists_isPureNash_makespan_eq_mul_optMakespan (by norm_num)

/-- LPT ordering produces a pure Nash equilibrium on `3` jobs and `2` identical machines, and by
`makespan_eq_opt_of_three_jobs_two_machines` it is optimal. -/
example :
    let w : Fin 3 → ℝ := ![3, 2, 2]
    let hw : ∀ i, 0 ≤ w i := fun i => by fin_cases i <;> norm_num [w]
    let G := LoadBalancingGame.identical (M := Fin 2) w hw
    ∃ A : Fin 3 → Fin 2, G.toCostGame.IsPureNash A ∧ G.makespan A = G.optMakespan := by
  intro w hw G
  obtain ⟨A, -, hNE⟩ := G.exists_isPureNash_of_lptOrder
  exact ⟨A, hNE,
    (isIdentical_identical (M := Fin 2) w hw).makespan_eq_opt_of_three_jobs_two_machines hNE⟩

/-- Computable `Scheduling.lptSchedule` on unsorted weights `![2, 5, 3, 2, 3]` over `3` identical
machines is itself a pure Nash equilibrium and satisfies Graham's `4 / 3 - 1 / 9 = 11 / 9` bound.
-/
example :
    let w : Fin 5 → ℝ := ![2, 5, 3, 2, 3]
    let hw : ∀ i, 0 ≤ w i := fun i => by fin_cases i <;> norm_num [w]
    let G := LoadBalancingGame.identical (M := Fin 3) w hw
    let A := Cslib.Algorithms.Lean.Scheduling.lptSchedule (m := 3) w
    (G.IsRelatedLPT (Cslib.Algorithms.Lean.Scheduling.listSchedule (m := 3) w)) ∧
      G.toCostGame.IsPureNash A ∧
      G.makespan A ≤ 11 / 9 * G.optMakespan := by
  intro w hw G A
  have hId : G.IsIdentical := isIdentical_identical (M := Fin 3) w hw
  refine ⟨(hId.isRelatedLPT_iff_isListSchedule _).mpr
      (Cslib.Algorithms.Lean.Scheduling.isListSchedule_listSchedule w),
    hId.isPureNash_lptSchedule, ?_⟩
  have h := hId.makespan_lptSchedule_le
  norm_num at h
  exact h

/-- Price of stability `1` and max-weight best-response convergence on `kpTwoUnit`. -/
example : ∃ A, kpTwoUnit.toCostGame.IsPureNash A ∧ kpTwoUnit.makespan A = kpTwoUnit.optMakespan :=
  kpTwoUnit.exists_isPureNash_makespan_eq_optMakespan

example : ∃ (T : ℕ) (γ : Fin (T + 1) → (Fin 2 → Fin 2)) (move : Fin T → Fin 2),
    T ≤ 2 ∧ γ 0 = (fun _ => 0) ∧
    (∀ t : Fin T, kpTwoUnit.IsMaxWeightBestResponseStep (γ t.succ) (γ t.castSucc) (move t)) ∧
    kpTwoUnit.toCostGame.IsPureNash (γ (Fin.last T)) :=
  (isIdentical_identical (M := Fin 2) (fun _ => (1 : ℝ)) _).exists_maxWeightBestResponse_isPureNash
    (fun _ => 0)

/-- The general uniformly related `O(log m / log log m)` pure PoA bound applies to `m = 3`. -/
example : (finnHorowitzTight 3).makespan (finnHorowitzTightNE 3) ≤
    (4 * Real.log 3 / Real.log (Real.log 3) + 3) * (finnHorowitzTight 3).optMakespan := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    (finnHorowitzTight 3).makespan_le_log_div_log_log_mul_optMakespan (by decide)
      (isPureNash_finnHorowitzTightNE 3)

end CounterexamplesAndAlgorithms

end CslibFrontierTests.LoadBalancingNRTV
