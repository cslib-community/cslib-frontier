/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.GameTheory.LoadBalancing.BallsIntoBins
public import CslibFrontier.GameTheory.LoadBalancing.MixedPoA
public import CslibFrontier.GameTheory.LoadBalancing.RelatedPureLower
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

/-!
# Asymptotic selfish load-balancing bounds: witnesses and boundary checks

Concrete checked witnesses exercising:

* `CslibFrontier.GameTheory.LoadBalancing.RelatedPureLower` ([Vocking2007], Theorem 20.9):
  `k = 1, 2, 3` instances (`|M| = 3, 13, 79`), distinct-speed non-identical witness, exact `m = 13`
  and padded `m = 20` instantiations of `exists_relatedPureNash_makespan_ge_log_div_log_log`.
* `CslibFrontier.GameTheory.LoadBalancing.BallsIntoBins` ([Vocking2007], Proposition 20.11 and
  Theorem 20.12): `m = 1, 2, 3, 4` uniform totally mixed Nash witnesses, `m = 24, k = 2` lower-tail
  threshold (`3 * 2 ^ 2 * 2! = 24`), and the `m = 3` lower bound.
* `CslibFrontier.GameTheory.LoadBalancing.MixedPoA` ([Vocking2007], Theorem 20.13 and Lemma 20.14):
  expected-load bound, Chernoff tail check, two-sided `Θ(log m / log log m)` sandwich on
  `unitIdenticalGame m` for `m ≥ 3`, and zero-weight degenerate boundary (`optMakespan = 0`).
-/

public section

namespace CslibFrontierTests.LoadBalancingAsymptoticNRTV

open Cslib.GameTheory
open Cslib.GameTheory.LoadBalancingGame

section RelatedPureLowerWitnesses

/-- `k = 1`: `3` machines (`m_0 = 2`, `m_1 = 1`), pure NE with makespan `1` and `0 < OPT ≤ 1`. -/
example : (relatedPureLower 1).toCostGame.IsPureNash (relatedPureLowerNE 1) ∧
    (relatedPureLower 1).makespan (relatedPureLowerNE 1) = 1 ∧
    0 < (relatedPureLower 1).optMakespan ∧
    (relatedPureLower 1).optMakespan ≤ 1 ∧
    Fintype.card (relatedPureLowerMachine 1) = 3 := by
  refine ⟨isPureNash_relatedPureLowerNE 1, by simpa using makespan_relatedPureLowerNE 1,
    optMakespan_relatedPureLower_pos le_rfl, optMakespan_relatedPureLower_le_one 1, ?_⟩
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_two]
  norm_num [relatedPureLowerTierCount, Nat.factorial]

/-- `k = 2`: `13` machines (`m_0 = 8`, `m_1 = 4`, `m_2 = 1`), pure NE with makespan `2`, not
identical, satisfying the `(1 / 3) * log |M| / log (log |M|)` lower bound. -/
theorem relatedPureLower_two_witness :
    (relatedPureLower 2).toCostGame.IsPureNash (relatedPureLowerNE 2) ∧
    (relatedPureLower 2).makespan (relatedPureLowerNE 2) = 2 ∧
    ¬ (relatedPureLower 2).IsIdentical ∧
    (1 / 3 : ℝ) *
      (Real.log (Fintype.card (relatedPureLowerMachine 2)) /
        Real.log (Real.log (Fintype.card (relatedPureLowerMachine 2)))) *
      (relatedPureLower 2).optMakespan ≤
        (relatedPureLower 2).makespan (relatedPureLowerNE 2) := by
  refine ⟨isPureNash_relatedPureLowerNE 2, by simpa using makespan_relatedPureLowerNE 2, ?_,
    makespan_relatedPureLowerNE_ge_log_div_log_log le_rfl⟩
  intro hId
  have h := hId ⟨⟨1, by omega⟩, ⟨0, by norm_num [relatedPureLowerTierCount, Nat.factorial]⟩⟩
  norm_num [relatedPureLower_speed] at h

/-- `k = 3`: `79` machines (`48 + 24 + 6 + 1 ≤ 96`), pure NE with makespan `3`. -/
example : (relatedPureLower 3).toCostGame.IsPureNash (relatedPureLowerNE 3) ∧
    (relatedPureLower 3).makespan (relatedPureLowerNE 3) = 3 ∧
    Fintype.card (relatedPureLowerMachine 3) = 79 := by
  refine ⟨isPureNash_relatedPureLowerNE 3, by simpa using makespan_relatedPureLowerNE 3, ?_⟩
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_four]
  norm_num [relatedPureLowerTierCount, Nat.factorial]

/-- Arbitrary-`m` Theorem 20.9 witness at the exact threshold `m = 13` and at a padded machine
count `m = 20` (between `M_2 = 13` and `M_3 = 79`). -/
example : ∃ (n : ℕ) (G : LoadBalancingGame (Fin n) (Fin 13)) (A : Fin n → Fin 13),
    G.toCostGame.IsPureNash A ∧
    0 < G.optMakespan ∧
    (1 / 5 : ℝ) * (Real.log 13 / Real.log (Real.log 13)) * G.optMakespan ≤ G.makespan A := by
  simpa using exists_relatedPureNash_makespan_ge_log_div_log_log (m := 13) (by omega)

example : ∃ (n : ℕ) (G : LoadBalancingGame (Fin n) (Fin 20)) (A : Fin n → Fin 20),
    G.toCostGame.IsPureNash A ∧
    0 < G.optMakespan ∧
    (1 / 5 : ℝ) * (Real.log 20 / Real.log (Real.log 20)) * G.optMakespan ≤ G.makespan A := by
  simpa using exists_relatedPureNash_makespan_ge_log_div_log_log (m := 20) (by omega)

end RelatedPureLowerWitnesses

section BallsIntoBinsAndMixedPoAWitnesses

/-- `m = 1` and `m = 3`: uniform profile is totally mixed Nash with `OPT = 1`. -/
example : (unitIdenticalGame 1).toCostGame.IsTotallyMixedNash (uniformMixedProfile 1) ∧
    (unitIdenticalGame 1).optMakespan = 1 :=
  ⟨isTotallyMixedNash_uniformMixedProfile 1, optMakespan_unitIdenticalGame 1⟩

example : (unitIdenticalGame 3).toCostGame.IsTotallyMixedNash (uniformMixedProfile 3) ∧
    (unitIdenticalGame 3).optMakespan = 1 :=
  ⟨isTotallyMixedNash_uniformMixedProfile 3, optMakespan_unitIdenticalGame 3⟩

/-- `m = 24, k = 2` (`3 * 2^2 * 2! = 24`): exercises the exact factorial threshold of the
Paley–Zygmund balls-into-bins lower tail (`Pr[makespan ≥ 2] ≥ 1 / 2`) and expectation bound. -/
example :
    ((1 / 2 : ℝ) ≤
      ∑ A : Fin 24 → Fin 24,
        if (2 : ℝ) ≤ (unitIdenticalGame 24).makespan A then
          productWeight (uniformMixedProfile 24) A
        else 0) ∧
    1 ≤ (unitIdenticalGame 24).expectedMakespan (uniformMixedProfile 24) := by
  refine ⟨?_, ?_⟩
  · simpa using ballsIntoBins_tail_ge_half (m := 24) (k := 2) (by omega)
      (by norm_num [Nat.factorial])
  · have h := ballsIntoBins_expectedMakespan_ge_half_of_factorial (m := 24) (k := 2) (by omega)
      (by norm_num [Nat.factorial])
    norm_num at h
    exact h

/-- Two-sided `Θ(log m / log log m)` sandwich on `unitIdenticalGame m` for every `m ≥ 3`. -/
example (m : ℕ) [NeZero m] (hm : 3 ≤ m) :
    (1 / 20 : ℝ) * (Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))) *
        (unitIdenticalGame m).optMakespan ≤
      (unitIdenticalGame m).expectedMakespan (uniformMixedProfile m) ∧
    (unitIdenticalGame m).expectedMakespan (uniformMixedProfile m) ≤
      (12 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)) + 1) *
        (unitIdenticalGame m).optMakespan := by
  refine ⟨expectedMakespan_uniformMixedProfile_ge_log_div_log_log hm, ?_⟩
  simpa only [Fintype.card_fin] using
    (isIdentical_unitIdenticalGame m).expectedMakespan_le_log_div_log_log
      (by simpa only [Fintype.card_fin] using hm) (isMixedNash_uniformMixedProfile m)

/-- Expected-load bound and Chernoff upper tail on `unitIdenticalGame 3`. -/
example :
    (unitIdenticalGame 3).expectedLoad (uniformMixedProfile 3) 0 ≤
      2 * (unitIdenticalGame 3).optMakespan ∧
    (∑ A : Fin 3 → Fin 3,
      if 4 * (unitIdenticalGame 3).optMakespan ≤ (unitIdenticalGame 3).load A 0 then
        productWeight (uniformMixedProfile 3) A else 0) ≤
      Real.exp (4 - 2 - 4 * Real.log (4 / 2)) := by
  refine ⟨(isIdentical_unitIdenticalGame 3).expectedLoad_le_two_mul_optMakespan
      (isMixedNash_uniformMixedProfile 3) 0, ?_⟩
  have hopt : 0 < (unitIdenticalGame 3).optMakespan := by
    rw [optMakespan_unitIdenticalGame]
    exact zero_lt_one
  exact (isIdentical_unitIdenticalGame 3).prob_load_ge_le_exp_chernoff
    (isMixedNash_uniformMixedProfile 3) hopt 0 (by norm_num)

/-- Zero-weight degenerate boundary (`optMakespan = 0`) on `3` identical machines. -/
example :
    let G : LoadBalancingGame (Fin 2) (Fin 3) :=
      LoadBalancingGame.identical (fun _ => 0) (fun _ => le_rfl)
    let p : Fin 2 → Fin 3 → ℝ := fun _ _ => 1 / 3
    G.toCostGame.IsMixedNash p ∧
    G.expectedMakespan p ≤
      (12 * Real.log 3 / Real.log (Real.log 3) + 1) * G.optMakespan := by
  intro G p
  have hId : G.IsIdentical := fun _ => rfl
  have hp : G.toCostGame.IsMixedNash p := by
    rw [G.isMixedNash_iff]
    refine ⟨fun _ => isMixedStrategy_iff.mpr ⟨fun _ => by norm_num [p], ?_⟩, fun i j _ k => ?_⟩
    · simp only [Fin.sum_univ_three, p]; norm_num
    · simp [expectedLoad, G, identical]
  refine ⟨hp, ?_⟩
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    hId.expectedMakespan_le_log_div_log_log (by decide) hp

end BallsIntoBinsAndMixedPoAWitnesses

end CslibFrontierTests.LoadBalancingAsymptoticNRTV
