/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.LoadBalancing.MixedPoA
public import CslibFrontier.GameTheory.LoadBalancing.RelatedMixedLower
public import CslibFrontier.GameTheory.LoadBalancing.RelatedMixedPoA
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Uniformly related mixed PoA and small-weight identical PoA: witnesses and boundary checks

Concrete checked witnesses exercising:

* `CslibFrontier.GameTheory.LoadBalancing.MixedPoA` ([Vocking2007], Exercise 20.6(b)):
  small-weight identical-machine mixed PoA `expectedMakespan p ≤ 7 * optMakespan` on `m = 2` and
  `m = 4` identical machines with a nontrivial mixed Nash equilibrium.
* `CslibFrontier.GameTheory.LoadBalancing.RelatedMixedPoA` ([CzumajVocking2002]; [Vocking2007],
  Theorem 20.15, Lemma 20.16, and Lemma 20.17): expected-load upper bound, speed doubling
  `2 * s(0) < s(2)` on a concrete non-identical mixed instance (`relatedMixedLower 4 2`),
  small-probability job-size cap `weight i ≤ 12 * speed j * optMakespan` on a non-identical mixed
  NE with `0 < p i j = 1 / 5 < 1 / 4` (`relatedMixedLower 2 5`), zero-weight degenerate boundary
  (`optMakespan = 0`) at `m = 16`, and general `m ≥ 16` upper bound.
* `CslibFrontier.GameTheory.LoadBalancing.RelatedMixedLower` ([CzumajVocking2002]; [Vocking2007],
  Theorem 20.18): concrete non-identical `(k = 2, B = 5)` mixed NE witness (`n ≤ m`,
  `0 < OPT ≤ 1`, distinct machine speeds), universal `m = 16` and `m = 1000` witnesses, and
  two-sided `Θ(log m / log log log m)` sandwich for all `m ≥ 16`.
-/

public section

namespace CslibFrontierTests.LoadBalancingRelatedMixedNRTV

open Cslib.GameTheory
open Cslib.GameTheory.LoadBalancingGame
open Finset

section Exercise20_6bWitnesses

/-- Exercise 20.6(b) on `m = 4` identical machines with `8` jobs of weight `1 / 2` (`OPT = 1`,
`1 / 2 ≤ 1 / log 4 ≈ 0.721`), under the uniform mixed Nash equilibrium. -/
example :
    let G : LoadBalancingGame (Fin 8) (Fin 4) :=
      LoadBalancingGame.identical (fun _ => 1 / 2) (fun _ => by norm_num)
    let p : Fin 8 → Fin 4 → ℝ := fun _ _ => 1 / 4
    G.toCostGame.IsMixedNash p ∧
    G.optMakespan = 1 ∧
    G.expectedMakespan p ≤ 7 * G.optMakespan := by
  intro G p
  have hId : G.IsIdentical := fun _ => rfl
  have hp : G.toCostGame.IsMixedNash p := by
    rw [G.isMixedNash_iff]
    refine ⟨fun _ => isMixedStrategy_iff.mpr ⟨fun _ => by norm_num [p], ?_⟩, fun i j _ k => ?_⟩
    · simp only [Fin.sum_univ_four, p]; norm_num
    · simp [expectedLoad, G, identical, p]
  have hopt : G.optMakespan = 1 := by
    refine le_antisymm ?_ ?_
    · let A : Fin 8 → Fin 4 := fun i => ⟨i.val % 4, Nat.mod_lt _ (by omega)⟩
      refine (G.optMakespan_le A).trans ((G.makespan_le_iff A).mpr fun j => ?_)
      rw [G.load_eq_sum_div, hId j, div_one, Finset.sum_filter]
      fin_cases j <;> simp [Fin.sum_univ_eight, G, identical, A] <;> norm_num
    · have hvol := hId.sum_weight_le_card_mul_optMakespan
      have hsum : ∑ i : Fin 8, G.weight i = 4 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, G, identical]
        norm_num
      rw [hsum, Fintype.card_fin] at hvol
      norm_num at hvol
      linarith
  have hw : ∀ i : Fin 8, G.weight i ≤ G.optMakespan / Real.log (Fintype.card (Fin 4)) := by
    intro _
    rw [hopt, Fintype.card_fin, Nat.cast_ofNat]
    have hlog4_pos : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    have hlog4_lt2 : Real.log (4 : ℝ) ≤ 2 := by
      have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith
      linarith
    simp only [G, identical]
    rw [le_div_iff₀ hlog4_pos]
    linarith
  exact ⟨hp, hopt, hId.expectedMakespan_le_seven_mul_optMakespan_of_weight_le (by decide) hp hw⟩

end Exercise20_6bWitnesses

section RelatedMixedUpperAndLowerWitnesses

/-- Concrete non-identical `(k = 2, B = 5)` witness of `relatedMixedLower`: `65` machines, `55`
jobs (`n ≤ m`), distinct machine speeds, mixed Nash equilibrium with `0 < OPT ≤ 1`, and a
small-probability job (`p i j = 1 / 5 < 1 / 4`) satisfying Lemma 20.17 (`w_i ≤ 12 s_j OPT`). -/
example :
    (relatedMixedLower 2 5).toCostGame.IsMixedNash (relatedMixedLowerNE 2 5) ∧
    ¬ (relatedMixedLower 2 5).IsIdentical ∧
    Fintype.card (RelatedMixedLowerJob 2 5) ≤ Fintype.card (RelatedMixedLowerMachine 2 5) ∧
    0 < (relatedMixedLower 2 5).optMakespan ∧
    (relatedMixedLower 2 5).optMakespan ≤ 1 ∧
    (relatedMixedLower 2 5).weight (Sum.inr 0) ≤
      12 * (relatedMixedLower 2 5).speed
          ⟨Fin.last 2, ⟨0, by norm_num [relatedPureLowerTierCount]⟩, 0⟩ *
        (relatedMixedLower 2 5).optMakespan := by
  have hp : (relatedMixedLower 2 5).toCostGame.IsMixedNash (relatedMixedLowerNE 2 5) :=
    isMixedNash_relatedMixedLowerNE (by omega)
  refine ⟨hp, ?_, card_relatedMixedLowerJob_le_card_machine 2 5,
    optMakespan_relatedMixedLower_pos 2 5 (by omega),
    optMakespan_relatedMixedLower_le_one 2 5, ?_⟩
  · intro hId
    have h := hId ⟨⟨1, by omega⟩, ⟨0, by norm_num [relatedPureLowerTierCount, Nat.factorial]⟩, 0⟩
    norm_num [relatedMixedLower] at h
  · let jtop : RelatedMixedLowerMachine 2 5 :=
      ⟨Fin.last 2, ⟨0, by norm_num [relatedPureLowerTierCount]⟩, 0⟩
    have hpos : 0 < relatedMixedLowerNE 2 5 (Sum.inr 0) jtop := by
      simp [relatedMixedLowerNE, jtop]
    have hlt : relatedMixedLowerNE 2 5 (Sum.inr 0) jtop < 1 / 4 := by
      simp only [relatedMixedLowerNE, jtop, ↓reduceIte]
      norm_num
    exact (relatedMixedLower 2 5).weight_le_twelve_mul_speed_mul_optMakespan hp jtop (Sum.inr 0)
      hpos hlt

/-- Concrete Lemma 20.16 (`speed_doubling_expectedGroup`) witness on `relatedMixedLower 4 2`
(`k = 0`): `G_0` and `L_3` are nonempty, so `G_2` is nonempty with `2 * s(0) < s(2)`. -/
example :
    let G := relatedMixedLower 4 2
    let p := relatedMixedLowerNE 4 2
    ∃ (hG0 : (G.expectedSpeedPrefix p 0 \ G.expectedSpeedPrefix p 1).Nonempty)
      (hG2 : (G.expectedSpeedPrefix p 2 \ G.expectedSpeedPrefix p 3).Nonempty),
      2 * (G.expectedSpeedPrefix p 0 \ G.expectedSpeedPrefix p 1).sup' hG0 G.speed <
        (G.expectedSpeedPrefix p 2 \ G.expectedSpeedPrefix p 3).sup' hG2 G.speed := by
  classical
  intro G p
  have hp : G.toCostGame.IsMixedNash p := isMixedNash_relatedMixedLowerNE (by omega)
  have hopt_pos : 0 < G.optMakespan := optMakespan_relatedMixedLower_pos 4 2 (by omega)
  have hopt_le1 : G.optMakespan ≤ 1 := optMakespan_relatedMixedLower_le_one 4 2
  let j0 : RelatedMixedLowerMachine 4 2 :=
    ⟨0, ⟨0, by norm_num [relatedPureLowerTierCount, Nat.factorial]⟩, 0⟩
  let j4 : RelatedMixedLowerMachine 4 2 :=
    ⟨Fin.last 4, ⟨0, by norm_num [relatedPureLowerTierCount, Nat.factorial]⟩, 0⟩
  have hG0 : (G.expectedSpeedPrefix p 0 \ G.expectedSpeedPrefix p 1).Nonempty := by
    refine ⟨j0, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · rw [expectedSpeedPrefix, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun j' _ => ?_⟩
      rw [Nat.cast_zero, zero_mul]
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg ((hp.1 i).nonneg j') (div_nonneg (G.weight_nonneg i) (G.speed_pos j').le)
    · rw [expectedSpeedPrefix, Finset.mem_filter]
      intro h
      have h1 := h.2 j0 le_rfl
      have hE0 : G.expectedLoad p j0 = 0 := by
        rw [expectedLoad_relatedMixedLowerNE (by omega)]
        simp [j0]
      rw [hE0, Nat.cast_one, one_mul] at h1
      linarith
  have hL3 : (G.expectedSpeedPrefix p 3).Nonempty := by
    refine ⟨j4, ?_⟩
    rw [expectedSpeedPrefix, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun j' hj' => ?_⟩
    have hj'_last : j'.tier = Fin.last 4 := by
      have hsp : (2 : ℝ) ^ (4 : ℕ) ≤ (2 : ℝ) ^ j'.tier.val := by
        simpa [G, relatedMixedLower, j4] using hj'
      have hle4 : 4 ≤ j'.tier.val := by
        by_contra hlt
        push Not at hlt
        have : (2 : ℝ) ^ j'.tier.val < (2 : ℝ) ^ (4 : ℕ) :=
          pow_lt_pow_right₀ (by norm_num) hlt
        linarith
      exact Fin.ext (by have := j'.tier.isLt; simp only [Fin.val_last]; omega)
    rw [expectedLoad_relatedMixedLowerNE (by omega), ite_eq_left hj'_last]
    push_cast
    linarith
  obtain ⟨hG2, hlt⟩ := G.speed_doubling_expectedGroup hp hopt_pos hG0 hL3
  exact ⟨hG0, hG2, hlt⟩

/-- Exact multi-ball boundary witness for `ballsIntoBins_mul_tail_ge_half` with `a = 2, B = 216,
d = 4` (`3 ^ 2 * 2 ^ 4 * 4! = 3456 = 216 * 2 ^ 4`). -/
example :
    (1 / 2 : ℝ) ≤
      ∑ A : Fin 432 → Fin 216,
        if ∃ j : Fin 216, 4 ≤ #(Finset.univ.filter fun i : Fin 432 => A i = j) then
          (1 / (216 : ℝ)) ^ 432
        else 0 :=
  ballsIntoBins_mul_tail_ge_half (n := 432) (a := 2) (B := 216) (d := 4)
    (by norm_num) (by omega) (by omega) (by omega) (by omega) (by norm_num [Nat.factorial])

/-- Zero-weight degenerate boundary (`optMakespan = 0`) for Theorem 20.15 on `16` non-identical
machines. -/
example :
    let G : LoadBalancingGame (Fin 2) (Fin 16) :=
      { weight := fun _ => 0
        speed := fun j => (j.val : ℝ) + 1
        weight_nonneg := fun _ => le_rfl
        speed_pos := fun _ => by positivity }
    let p : Fin 2 → Fin 16 → ℝ := fun _ _ => 1 / 16
    G.toCostGame.IsMixedNash p ∧
    ¬ G.IsIdentical ∧
    G.expectedMakespan p ≤
      (120 * Real.log 16 / Real.log (Real.log (Real.log 16))) * G.optMakespan := by
  intro G p
  have hp : G.toCostGame.IsMixedNash p := by
    rw [G.isMixedNash_iff]
    refine ⟨fun _ => isMixedStrategy_iff.mpr ⟨fun _ => by norm_num [p], ?_⟩, fun i j _ k => ?_⟩
    · simp only [p, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
    · simp [expectedLoad, G]
  refine ⟨hp, ?_, ?_⟩
  · intro hId
    have h := hId 1
    norm_num [G] at h
  · simpa only [Fintype.card_fin, Nat.cast_ofNat] using
      G.expectedMakespan_le_log_div_log_log_log (by decide) hp

/-- Two-sided `Θ(log m / log log log m)` sandwich (Theorems 20.15 and 20.18) for every `m ≥ 16`,
showing existence of an `n ≤ m` instance attaining the lower bound and simultaneous satisfaction of
the upper bound. -/
example (m : ℕ) [NeZero m] (hm : 16 ≤ m) :
    ∃ (n : ℕ) (_ : n ≤ m) (G : LoadBalancingGame (Fin n) (Fin m)) (p : Fin n → Fin m → ℝ),
      G.toCostGame.IsMixedNash p ∧
      0 < G.optMakespan ∧
      (1 / 3200 : ℝ) * (Real.log (m : ℝ) / Real.log (Real.log (Real.log (m : ℝ)))) *
          G.optMakespan ≤
        G.expectedMakespan p ∧
      G.expectedMakespan p ≤
        (120 * Real.log (m : ℝ) / Real.log (Real.log (Real.log (m : ℝ)))) * G.optMakespan := by
  obtain ⟨n, hn, G, p, hp, hopt, hlo⟩ :=
    exists_relatedMixedNash_makespan_ge_log_div_log_log_log (m := m) hm
  refine ⟨n, hn, G, p, hp, hopt, hlo, ?_⟩
  simpa only [Fintype.card_fin] using
    G.expectedMakespan_le_log_div_log_log_log (by simpa only [Fintype.card_fin] using hm) hp

/-- Concrete Theorem 20.18 witnesses at the threshold `m = 16` and at `m = 1000`. -/
example :
    ∃ (n : ℕ) (_ : n ≤ 16) (G : LoadBalancingGame (Fin n) (Fin 16)) (p : Fin n → Fin 16 → ℝ),
      G.toCostGame.IsMixedNash p ∧
      0 < G.optMakespan ∧
      (1 / 3200 : ℝ) * (Real.log 16 / Real.log (Real.log (Real.log 16))) * G.optMakespan ≤
        G.expectedMakespan p := by
  simpa using exists_relatedMixedNash_makespan_ge_log_div_log_log_log (m := 16) le_rfl

example :
    ∃ (n : ℕ) (_ : n ≤ 1000) (G : LoadBalancingGame (Fin n) (Fin 1000)) (p : Fin n → Fin 1000 → ℝ),
      G.toCostGame.IsMixedNash p ∧
      0 < G.optMakespan ∧
      (1 / 3200 : ℝ) * (Real.log 1000 / Real.log (Real.log (Real.log 1000))) * G.optMakespan ≤
        G.expectedMakespan p := by
  simpa using exists_relatedMixedNash_makespan_ge_log_div_log_log_log (m := 1000) (by omega)

end RelatedMixedUpperAndLowerWitnesses

end CslibFrontierTests.LoadBalancingRelatedMixedNRTV
