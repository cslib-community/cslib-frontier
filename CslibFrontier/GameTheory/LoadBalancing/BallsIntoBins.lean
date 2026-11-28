/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.LoadBalancing.MixedNash
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpOneSubInvPow
import CslibFrontier.Foundations.Analysis.SpecialFunctions.LogDivLogLog
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Balls-into-bins lower bound and identical-machine mixed PoA

This module formalizes the classical balls-into-bins lower bound on the expected maximum load of
`m` balls thrown independently and uniformly into `m` bins ([Vocking2007], Proposition 20.11;
locator not re-verified against primary PDF) and applies it to obtain the `Ω(log m / log log m)`
lower bound on the mixed Nash price of anarchy for `m` identical machines
([KoutsoupiasPapadimitriou1999]; [CzumajVocking2002]; [Vocking2007], Theorem 20.12).

## Proof overview

Consider `unitIdenticalGame m`: `m` unit-weight jobs on `m` identical machines (`optMakespan = 1`),
with the uniform profile `uniformMixedProfile m` (`p i j = 1 / m`), which is a totally mixed Nash
equilibrium for every `m ≥ 1`.

For any integer `k ≥ 2` with `2 * k ≤ m`, let `Y_k(A) = #{j : Fin m | #{i | A i = j} = k}` count
bins receiving exact load `k`:

1. Exact single-bin and two-bin occupancy counts give
   `p_k = Pr[L_j = k] = C(m, k) * (1 / m) ^ k * (1 - 1 / m) ^ (m - k)` and
   `q_k = Pr[L_{j₁} = k ∧ L_{j₂} = k]` equals
   `C(m, k) * C(m - k, k) * (1 / m) ^ (2k) * (1 - 2 / m) ^ (m - 2k)` (for `j₁ ≠ j₂`).
2. **Negative correlation** (`q_k ≤ p_k ^ 2` for `k ≥ 2` and `2 * k ≤ m`): each factor
   `(m - k - i) / (m - i) ≤ 1 - k / m ≤ 1 - 2 / m ≤ (1 - 1 / m) ^ 2` and
   `1 - 2 / m ≤ (1 - 1 / m) ^ 2`, yielding `E[Y_k ^ 2] ≤ E[Y_k] + (E[Y_k]) ^ 2`.
3. **Paley–Zygmund** (`(E[Y_k]) ^ 2 ≤ E[Y_k ^ 2] * Pr[Y_k ≥ 1]`): whenever `E[Y_k] = m * p_k ≥ 1`,
   `Pr[max_j L_j ≥ k] ≥ Pr[Y_k ≥ 1] ≥ 1 / 2`, so `E[max_j L_j] ≥ k / 2`.
4. Using `Real.exp_neg_one_le_one_sub_inv_pow` (`(1 - 1 / m) ^ (m - k) ≥ e⁻¹ > 1 / 3`) and
   `(m)_k / m ^ k ≥ (1 / 2) ^ k`, the condition `3 * 2 ^ k * k! ≤ m` guarantees `m * p_k ≥ 1`,
   producing `E[max_j L_j] ≥ (1 / 20) * (log m / log (log m))` for every `m ≥ 3`.

## Main definitions

* `Cslib.GameTheory.LoadBalancingGame.unitIdenticalGame`: `m` unit-weight jobs on `m` identical
  machines.
* `Cslib.GameTheory.LoadBalancingGame.uniformMixedProfile`: the uniform mixed strategy `1 / m`.

## Main results

* `Cslib.GameTheory.LoadBalancingGame.optMakespan_unitIdenticalGame`: `optMakespan = 1`.
* `Cslib.GameTheory.LoadBalancingGame.isTotallyMixedNash_uniformMixedProfile`,
  `Cslib.GameTheory.LoadBalancingGame.isMixedNash_uniformMixedProfile`: the uniform profile is a
  totally mixed Nash equilibrium.
* `Cslib.GameTheory.LoadBalancingGame.ballsIntoBins_mul_tail_ge_half`,
  `Cslib.GameTheory.LoadBalancingGame.ballsIntoBins_tail_ge_half`,
  `Cslib.GameTheory.LoadBalancingGame.ballsIntoBins_expectedMakespan_ge_half_of_factorial`
  ([Vocking2007], Proposition 20.11): lower tail `Pr[max_j L_j ≥ d] ≥ 1 / 2` for `n = a * B` balls
  into `B` bins (when `3 ^ a * 2 ^ d * d! ≤ B * a ^ d`), specialized to `n = m` bins and
  expectation bound `E[max_j L_j] ≥ k / 2`.
* `Cslib.GameTheory.LoadBalancingGame.expectedMakespan_uniformMixedProfile_ge_log_div_log_log`
  ([KoutsoupiasPapadimitriou1999]; [CzumajVocking2002]; [Vocking2007], Proposition 20.11 and
  Theorem 20.12): for every `m ≥ 3`,
  `expectedMakespan ≥ (1 / 20) * (log m / log (log m)) * optMakespan`.

## References

* [CzumajVocking2002]
* [KoutsoupiasPapadimitriou1999]
* [Vocking2007]
-/

public section

namespace Cslib.GameTheory.LoadBalancingGame

open Finset

/-- `m` unit-weight jobs on `m` identical machines (balls-into-bins instance; [Vocking2007],
§20.3.1). -/
def unitIdenticalGame (m : ℕ) : LoadBalancingGame (Fin m) (Fin m) :=
  LoadBalancingGame.identical (fun _ => 1) (fun _ => zero_le_one)

@[simp] theorem unitIdenticalGame_weight (m : ℕ) (i : Fin m) :
    (unitIdenticalGame m).weight i = 1 := by
  simp [unitIdenticalGame, identical]

@[simp] theorem unitIdenticalGame_speed (m : ℕ) (j : Fin m) :
    (unitIdenticalGame m).speed j = 1 := by
  simp [unitIdenticalGame, identical]

/-- The uniform mixed strategy profile `p i j = 1 / m` on `m` identical machines. -/
noncomputable def uniformMixedProfile (m : ℕ) : Fin m → Fin m → ℝ :=
  fun _ _ => 1 / (m : ℝ)

@[simp] theorem uniformMixedProfile_apply (m : ℕ) (i j : Fin m) :
    uniformMixedProfile m i j = 1 / (m : ℝ) := by
  simp [uniformMixedProfile]

theorem isIdentical_unitIdenticalGame (m : ℕ) : (unitIdenticalGame m).IsIdentical :=
  unitIdenticalGame_speed m

/-- Optimal makespan of `m` unit jobs on `m` identical machines (`m ≥ 1`) is `1`. -/
theorem optMakespan_unitIdenticalGame (m : ℕ) [NeZero m] :
    (unitIdenticalGame m).optMakespan = 1 := by
  refine le_antisymm ?_ ?_
  · refine ((unitIdenticalGame m).optMakespan_le id).trans
      (((unitIdenticalGame m).makespan_le_iff id).mpr fun j => ?_)
    rw [LoadBalancingGame.load_eq_sum_div]
    simp only [unitIdenticalGame, identical, div_one, id_eq]
    have hfilt : (univ.filter fun i : Fin m => i = j) = {j} := by
      ext i; simp
    rw [hfilt, sum_singleton]
  · have h := (isIdentical_unitIdenticalGame m).weight_le_optMakespan (0 : Fin m)
    simpa only [unitIdenticalGame, identical] using h

/-- For `m ≥ 1`, the uniform mixed profile `1 / m` is a totally mixed Nash equilibrium of
`unitIdenticalGame m`. -/
theorem isTotallyMixedNash_uniformMixedProfile (m : ℕ) [NeZero m] :
    (unitIdenticalGame m).toCostGame.IsTotallyMixedNash (uniformMixedProfile m) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (NeZero.pos m)
  rw [CostGame.isTotallyMixedNash_iff]
  have hp1 : ∀ k : Fin m, ∑ j : Fin m, uniformMixedProfile m k j = 1 := fun _ => by
    simp only [uniformMixedProfile, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨fun _ _ => by simp only [uniformMixedProfile]; positivity, hp1, fun i a b => ?_⟩
  rw [(unitIdenticalGame m).deviationCost_toCostGame hp1 i a,
    (unitIdenticalGame m).deviationCost_toCostGame hp1 i b]
  simp [expectedLoad, unitIdenticalGame, identical, uniformMixedProfile]

/-- For `m ≥ 1`, the uniform mixed profile `1 / m` is a mixed Nash equilibrium of
`unitIdenticalGame m`. -/
theorem isMixedNash_uniformMixedProfile (m : ℕ) [NeZero m] :
    (unitIdenticalGame m).toCostGame.IsMixedNash (uniformMixedProfile m) :=
  (isTotallyMixedNash_uniformMixedProfile m).1

private theorem productWeight_uniformMixedProfile (m : ℕ) (A : Fin m → Fin m) :
    productWeight (uniformMixedProfile m) A = (1 / (m : ℝ)) ^ m := by
  rw [productWeight_def]
  simp only [uniformMixedProfile, prod_const, card_univ, Fintype.card_fin]

private theorem load_unitIdenticalGame_eq_card (m : ℕ) (A : Fin m → Fin m) (j : Fin m) :
    (unitIdenticalGame m).load A j = (#(univ.filter fun i : Fin m => A i = j) : ℝ) := by
  rw [LoadBalancingGame.load_eq_sum_div]
  simp only [unitIdenticalGame, identical, div_one, sum_const, nsmul_eq_mul, mul_one]

/-- Exact count of assignments `Fin n → Fin B` sending exactly `d` balls to bin `j`. -/
private theorem card_filter_binLoad_eq (n B d : ℕ) (j : Fin B) :
    #(univ.filter fun A : Fin n → Fin B => #(univ.filter fun i : Fin n => A i = j) = d) =
      n.choose d * (B - 1) ^ (n - d) := by
  classical
  let fibre (S : Finset (Fin n)) : Finset (Fin n → Fin B) :=
    univ.filter fun A => (univ.filter fun i => A i = j) = S
  have hpart :
      (univ.filter fun A : Fin n → Fin B => #(univ.filter fun i : Fin n => A i = j) = d) =
        (univ.powersetCard d).biUnion fibre := by
    ext A
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_powersetCard, subset_univ,
      fibre]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨S, hSd, hAS⟩ => hAS ▸ hSd⟩
  have hdisj :
      Set.PairwiseDisjoint
        ((univ.powersetCard d : Finset (Finset (Fin n))) : Set (Finset (Fin n))) fibre := by
    intro S₁ _ S₂ _ hne
    exact Finset.disjoint_left.2 fun A h1 h2 =>
      hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
  rw [hpart, card_biUnion hdisj]
  have hfib_card : ∀ S ∈ univ.powersetCard d, #(fibre S) = (B - 1) ^ (n - d) := by
    intro S hS
    have hSd : #S = d := (mem_powersetCard.mp hS).2
    let e : {A : Fin n → Fin B // A ∈ fibre S} ≃
        ({i : Fin n // i ∉ S} → {x : Fin B // x ≠ j}) :=
      { toFun := fun ⟨A, hA⟩ ⟨i, hi⟩ =>
          ⟨A i, fun hij => hi <| by
            have hA' : (univ.filter fun r => A r = j) = S := (mem_filter.mp hA).2
            rw [← hA']
            exact mem_filter.mpr ⟨mem_univ i, hij⟩⟩
        invFun := fun f =>
          ⟨fun i => if hi : i ∈ S then j else (f ⟨i, hi⟩).val, by
            simp only [fibre, mem_filter, mem_univ, true_and]
            ext i
            simp only [mem_filter, mem_univ, true_and]
            by_cases hi : i ∈ S
            · simp [hi]
            · simp only [hi, ↓reduceDIte, iff_false]
              exact (f ⟨i, hi⟩).property⟩
        left_inv := fun ⟨A, hA⟩ => by
          apply Subtype.ext
          funext i
          dsimp only
          have hA' : (univ.filter fun r => A r = j) = S := (mem_filter.mp hA).2
          by_cases hi : i ∈ S
          · rw [dite_eq_left hi]
            rw [← hA'] at hi
            exact (mem_filter.mp hi).2.symm
          · rw [dite_eq_right hi]
        right_inv := fun f => by
          funext ⟨i, hi⟩
          apply Subtype.ext
          dsimp only
          simp only [dite_eq_right hi] }
    have hcard_dom : Fintype.card {i : Fin n // i ∉ S} = n - d := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hSd]
    have hcard_cod : Fintype.card {x : Fin B // x ≠ j} = B - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fun, hcard_dom, hcard_cod]
  rw [sum_congr rfl hfib_card, sum_const, card_powersetCard, card_univ, Fintype.card_fin,
    smul_eq_mul]

/-- Exact count of assignments `Fin n → Fin B` sending `d` balls to `j₁` and `d` balls to `j₂`
(`j₁ ≠ j₂`). -/
private theorem card_filter_binLoad_pair_eq (n B d : ℕ) {j₁ j₂ : Fin B} (hne : j₁ ≠ j₂) :
    #(univ.filter fun A : Fin n → Fin B =>
        #(univ.filter fun i : Fin n => A i = j₁) = d ∧
        #(univ.filter fun i : Fin n => A i = j₂) = d) =
      n.choose d * (n - d).choose d * (B - 2) ^ (n - 2 * d) := by
  classical
  let pairs : Finset (Finset (Fin n) × Finset (Fin n)) :=
    (univ.powersetCard d).biUnion fun S₁ =>
      ((univ \ S₁).powersetCard d).image fun S₂ => (S₁, S₂)
  let fibre (P : Finset (Fin n) × Finset (Fin n)) : Finset (Fin n → Fin B) :=
    univ.filter fun A =>
      (univ.filter fun i => A i = j₁) = P.1 ∧ (univ.filter fun i => A i = j₂) = P.2
  have hpart :
      (univ.filter fun A : Fin n → Fin B =>
          #(univ.filter fun i : Fin n => A i = j₁) = d ∧
          #(univ.filter fun i : Fin n => A i = j₂) = d) =
        pairs.biUnion fibre := by
    ext A
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, pairs, mem_image, mem_powersetCard,
      subset_univ, fibre]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(univ.filter fun i => A i = j₁, univ.filter fun i => A i = j₂), ?_, rfl, rfl⟩
      refine ⟨_, h1, _, ⟨?_, h2⟩, rfl⟩
      intro i hi
      simp only [mem_sdiff, mem_univ, true_and, mem_filter] at hi ⊢
      intro h1i
      exact hne (h1i.symm.trans hi)
    · rintro ⟨⟨S₁, S₂⟩, ⟨S₁', hS₁', S₂', ⟨_, hS₂'⟩, hpair⟩, hA1, hA2⟩
      rw [hA1, hA2, ← congrArg Prod.fst hpair, ← congrArg Prod.snd hpair]
      exact ⟨hS₁', hS₂'⟩
  have hdisj : Set.PairwiseDisjoint (pairs : Set (Finset (Fin n) × Finset (Fin n))) fibre := by
    intro P₁ _ P₂ _ hPne
    refine Finset.disjoint_left.2 fun A h1 h2 => hPne ?_
    simp only [fibre, mem_filter, mem_univ, true_and] at h1 h2
    exact Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)
  rw [hpart, card_biUnion hdisj]
  have hfib_card : ∀ P ∈ pairs, #(fibre P) = (B - 2) ^ (n - 2 * d) := by
    intro ⟨S₁, S₂⟩ hP
    simp only [pairs, mem_biUnion, mem_powersetCard, subset_univ, true_and, mem_image,
      Prod.mk.injEq] at hP
    obtain ⟨S₁', hS₁', S₂', ⟨hsub, hS₂'⟩, rfl, rfl⟩ := hP
    have hdisjS : Disjoint S₁' S₂' :=
      Finset.disjoint_left.2 fun i hi1 hi2 => (mem_sdiff.mp (hsub hi2)).2 hi1
    let e : {A : Fin n → Fin B // A ∈ fibre (S₁', S₂')} ≃
        ({i : Fin n // i ∉ S₁' ∪ S₂'} → {x : Fin B // x ≠ j₁ ∧ x ≠ j₂}) :=
      { toFun := fun ⟨A, hA⟩ ⟨i, hi⟩ =>
          ⟨A i, by
            obtain ⟨hA1, hA2⟩ := (mem_filter.mp hA).2
            dsimp only at hA1 hA2
            rw [mem_union, not_or] at hi
            refine ⟨fun h1 => hi.1 ?_, fun h2 => hi.2 ?_⟩
            · rw [← hA1]; exact mem_filter.mpr ⟨mem_univ i, h1⟩
            · rw [← hA2]; exact mem_filter.mpr ⟨mem_univ i, h2⟩⟩
        invFun := fun f =>
          ⟨fun i =>
            if h1 : i ∈ S₁' then j₁
            else if h2 : i ∈ S₂' then j₂
            else (f ⟨i, by simp [mem_union, h1, h2]⟩).val, by
            simp only [fibre, mem_filter, mem_univ, true_and]
            constructor
            · ext i
              simp only [mem_filter, mem_univ, true_and]
              by_cases h1 : i ∈ S₁'
              · simp [h1]
              · by_cases h2 : i ∈ S₂'
                · simp [h1, h2, hne.symm]
                · simp only [h1, h2, ↓reduceDIte, iff_false]
                  exact (f ⟨i, by simp [mem_union, h1, h2]⟩).property.1
            · ext i
              simp only [mem_filter, mem_univ, true_and]
              by_cases h1 : i ∈ S₁'
              · have hnot2 : i ∉ S₂' := Finset.disjoint_left.mp hdisjS h1
                simp [h1, hnot2, hne]
              · by_cases h2 : i ∈ S₂'
                · simp [h1, h2]
                · simp only [h1, h2, ↓reduceDIte, iff_false]
                  exact (f ⟨i, by simp [mem_union, h1, h2]⟩).property.2⟩
        left_inv := fun ⟨A, hA⟩ => by
          apply Subtype.ext
          funext i
          dsimp only
          obtain ⟨hA1, hA2⟩ := (mem_filter.mp hA).2
          dsimp only at hA1 hA2
          by_cases h1 : i ∈ S₁'
          · rw [dite_eq_left h1]
            rw [← hA1] at h1
            exact (mem_filter.mp h1).2.symm
          · rw [dite_eq_right h1]
            by_cases h2 : i ∈ S₂'
            · rw [dite_eq_left h2]
              rw [← hA2] at h2
              exact (mem_filter.mp h2).2.symm
            · rw [dite_eq_right h2]
        right_inv := fun f => by
          funext ⟨i, hi⟩
          apply Subtype.ext
          dsimp only
          have hnot : i ∉ S₁' ∧ i ∉ S₂' := by simpa [mem_union] using hi
          simp only [dite_eq_right hnot.1, dite_eq_right hnot.2] }
    have hcard_union : #(S₁' ∪ S₂') = 2 * d := by
      rw [card_union_of_disjoint hdisjS, hS₁', hS₂']
      ring
    have hcard_dom : Fintype.card {i : Fin n // i ∉ S₁' ∪ S₂'} = n - 2 * d := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hcard_union]
    have hcard_cod : Fintype.card {x : Fin B // x ≠ j₁ ∧ x ≠ j₂} = B - 2 := by
      have heq : (univ.filter fun x : Fin B => x ≠ j₁ ∧ x ≠ j₂) = univ \ {j₁, j₂} := by
        ext x
        simp [mem_sdiff, mem_insert, mem_singleton, not_or]
      rw [Fintype.card_subtype, heq, card_sdiff_of_subset (subset_univ _), card_univ,
        Fintype.card_fin, card_pair hne]
    calc #(fibre (S₁', S₂'))
        = Fintype.card ({i : Fin n // i ∉ S₁' ∪ S₂'} → {x : Fin B // x ≠ j₁ ∧ x ≠ j₂}) := by
          rw [← Fintype.card_coe, Fintype.card_congr e]
      _ = (B - 2) ^ (n - 2 * d) := by
          rw [Fintype.card_fun, hcard_dom, hcard_cod]
  have hcard_pairs : #pairs = n.choose d * (n - d).choose d := by
    have hdisjP :
        Set.PairwiseDisjoint
          ((univ.powersetCard d : Finset (Finset (Fin n))) : Set (Finset (Fin n)))
          (fun S₁ => ((univ \ S₁).powersetCard d).image fun S₂ => (S₁, S₂)) := by
      intro S₁ _ S₁' _ hneS
      refine Finset.disjoint_left.2 fun P h1 h2 => ?_
      obtain ⟨_, _, rfl⟩ := mem_image.mp h1
      obtain ⟨_, _, hEq⟩ := mem_image.mp h2
      exact hneS (congrArg Prod.fst hEq).symm
    dsimp only [pairs]
    rw [card_biUnion hdisjP]
    have hinner : ∀ S₁ ∈ (univ : Finset (Fin n)).powersetCard d,
        #(((univ \ S₁).powersetCard d).image fun S₂ => (S₁, S₂)) = (n - d).choose d := by
      intro S₁ hS₁
      rw [card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h), card_powersetCard,
        card_sdiff_of_subset (subset_univ S₁), card_univ, Fintype.card_fin,
        (mem_powersetCard.mp hS₁).2]
    rw [sum_congr rfl hinner, sum_const, card_powersetCard, card_univ, Fintype.card_fin,
      smul_eq_mul]
  rw [sum_congr rfl hfib_card, sum_const, smul_eq_mul, hcard_pairs]

/-- Negative correlation of exact-load events for two distinct bins when `n = a * B` balls are
thrown uniformly into `B ≥ 2` bins, with `2 * a ≤ d` and `2 * d ≤ n`:
`Pr[L_{j₁} = d ∧ L_{j₂} = d] ≤ Pr[L_j = d] ^ 2`. -/
private theorem pair_prob_le_sq_single_prob {n a B d : ℕ} (hn : n = a * B)
    (hB : 2 ≤ B) (hd : 2 * a ≤ d) (h2d : 2 * d ≤ n) :
    ((n.choose d : ℝ) * ((n - d).choose d : ℝ) * ((B - 2 : ℕ) : ℝ) ^ (n - 2 * d)) /
        (B : ℝ) ^ n ≤
      (((n.choose d : ℝ) * ((B - 1 : ℕ) : ℝ) ^ (n - d)) / (B : ℝ) ^ n) ^ 2 := by
  have hB_pos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  -- Step 1: `(B - 2) * B ≤ (B - 1) ^ 2`.
  have hquad : ((B - 2 : ℕ) : ℝ) * (B : ℝ) ≤ ((B - 1 : ℕ) : ℝ) ^ 2 := by
    rw [Nat.cast_sub hB, Nat.cast_sub (by omega : 1 ≤ B)]
    push_cast
    nlinarith
  have hpow1 : (((B - 2 : ℕ) : ℝ) * (B : ℝ)) ^ (n - 2 * d) ≤
      (((B - 1 : ℕ) : ℝ) ^ 2) ^ (n - 2 * d) :=
    pow_le_pow_left₀ (by positivity) hquad (n - 2 * d)
  -- Step 2: `C(n - d, d) * B^(2d) ≤ C(n, d) * (B - 1)^(2d)`.
  have hchoose : ((n - d).choose d : ℝ) * (B : ℝ) ^ (2 * d) ≤
      (n.choose d : ℝ) * ((B - 1 : ℕ) : ℝ) ^ (2 * d) := by
    have hfac_pos : (0 : ℝ) < (d.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos d)
    suffices hdesc : ((n - d).descFactorial d : ℝ) * (B : ℝ) ^ (2 * d) ≤
        (n.descFactorial d : ℝ) * ((B - 1 : ℕ) : ℝ) ^ (2 * d) by
      have h1 : (d.factorial : ℝ) * ((n - d).choose d : ℝ) = ((n - d).descFactorial d : ℝ) := by
        exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose (n - d) d).symm
      have h2 : (d.factorial : ℝ) * (n.choose d : ℝ) = (n.descFactorial d : ℝ) := by
        exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose n d).symm
      rw [← h1, ← h2] at hdesc
      exact le_of_mul_le_mul_left (by linarith :
        (d.factorial : ℝ) * (((n - d).choose d : ℝ) * (B : ℝ) ^ (2 * d)) ≤
        (d.factorial : ℝ) * ((n.choose d : ℝ) * ((B - 1 : ℕ) : ℝ) ^ (2 * d))) hfac_pos
    rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range, Nat.cast_prod,
      Nat.cast_prod]
    have hpow_B : (B : ℝ) ^ (2 * d) = ∏ _i ∈ range d, ((B : ℝ) ^ 2) := by
      rw [prod_const, card_range, ← pow_mul]
    have hpow_B1 : ((B - 1 : ℕ) : ℝ) ^ (2 * d) = ∏ _i ∈ range d, (((B - 1 : ℕ) : ℝ) ^ 2) := by
      rw [prod_const, card_range, ← pow_mul]
    rw [hpow_B, hpow_B1, ← prod_mul_distrib, ← prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i hi => ?_
    rw [mem_range] at hi
    rw [Nat.cast_sub (by omega : i ≤ n - d), Nat.cast_sub (by omega : d ≤ n),
      Nat.cast_sub (by omega : i ≤ n), Nat.cast_sub (by omega : 1 ≤ B)]
    push_cast
    have h2a_r : (2 : ℝ) * (a : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hn_r : (n : ℝ) = (a : ℝ) * (B : ℝ) := by exact_mod_cast hn
    have hB_r : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    have hi_nn : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    -- RHS - LHS = (d - 2a) * B^2 + n + i * (2B - 1) ≥ 0.
    nlinarith
  -- Combine Step 1 and Step 2.
  have hexp_n : n - 2 * d + 2 * d = n := by omega
  have hexp_B1 : 2 * (n - 2 * d) + 2 * d = 2 * (n - d) := by omega
  have hnum :
      (n.choose d : ℝ) * ((n - d).choose d : ℝ) * ((B - 2 : ℕ) : ℝ) ^ (n - 2 * d) * (B : ℝ) ^ n ≤
      (n.choose d : ℝ) ^ 2 * ((B - 1 : ℕ) : ℝ) ^ (2 * (n - d)) := by
    have h1 : ((B - 2 : ℕ) : ℝ) ^ (n - 2 * d) * (B : ℝ) ^ (n - 2 * d) ≤
        ((B - 1 : ℕ) : ℝ) ^ (2 * (n - 2 * d)) := by
      simpa only [mul_pow, ← pow_mul] using hpow1
    have hprod :
        (((n - d).choose d : ℝ) * (B : ℝ) ^ (2 * d)) *
          (((B - 2 : ℕ) : ℝ) ^ (n - 2 * d) * (B : ℝ) ^ (n - 2 * d)) ≤
        ((n.choose d : ℝ) * ((B - 1 : ℕ) : ℝ) ^ (2 * d)) *
          ((B - 1 : ℕ) : ℝ) ^ (2 * (n - 2 * d)) :=
      mul_le_mul hchoose h1 (by positivity) (by positivity)
    have hlhs :
        (n.choose d : ℝ) * ((n - d).choose d : ℝ) * ((B - 2 : ℕ) : ℝ) ^ (n - 2 * d) *
          (B : ℝ) ^ n =
        (n.choose d : ℝ) *
          ((((n - d).choose d : ℝ) * (B : ℝ) ^ (2 * d)) *
            (((B - 2 : ℕ) : ℝ) ^ (n - 2 * d) * (B : ℝ) ^ (n - 2 * d))) := by
      have hB_split : (B : ℝ) ^ n = (B : ℝ) ^ (2 * d) * (B : ℝ) ^ (n - 2 * d) := by
        rw [← pow_add, add_comm, hexp_n]
      rw [hB_split]
      ring
    have hrhs :
        (n.choose d : ℝ) ^ 2 * ((B - 1 : ℕ) : ℝ) ^ (2 * (n - d)) =
        (n.choose d : ℝ) *
          (((n.choose d : ℝ) * ((B - 1 : ℕ) : ℝ) ^ (2 * d)) *
            ((B - 1 : ℕ) : ℝ) ^ (2 * (n - 2 * d))) := by
      have hB1_split : ((B - 1 : ℕ) : ℝ) ^ (2 * (n - d)) =
          ((B - 1 : ℕ) : ℝ) ^ (2 * d) * ((B - 1 : ℕ) : ℝ) ^ (2 * (n - 2 * d)) := by
        rw [← pow_add, add_comm, hexp_B1]
      rw [hB1_split]
      ring
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
  rw [div_pow, mul_pow, ← pow_mul, mul_comm (n - d) 2]
  rw [div_le_div_iff₀ (pow_pos hB_pos n) (pow_pos (pow_pos hB_pos n) 2)]
  have hcancel :
      (n.choose d : ℝ) * ((n - d).choose d : ℝ) * ((B - 2 : ℕ) : ℝ) ^ (n - 2 * d) *
        ((B : ℝ) ^ n) ^ 2 =
      ((n.choose d : ℝ) * ((n - d).choose d : ℝ) * ((B - 2 : ℕ) : ℝ) ^ (n - 2 * d) *
        (B : ℝ) ^ n) * (B : ℝ) ^ n := by ring
  rw [hcancel]
  exact mul_le_mul_of_nonneg_right hnum (by positivity)

/-- Lower bound on `B * p_d` for `n = a * B` balls thrown uniformly into `B ≥ 2` bins: whenever
`1 ≤ a`, `2 * a ≤ d`, `2 * d ≤ n`, and `3 ^ a * 2 ^ d * d! ≤ B * a ^ d`, the expected number of
bins receiving exact load `d` is at least `1`. -/
private theorem one_le_expected_count_exact {n a B d : ℕ} (hn : n = a * B)
    (ha : 1 ≤ a) (hB : 2 ≤ B) (hd : 2 * a ≤ d) (h2d : 2 * d ≤ n)
    (hcond : 3 ^ a * 2 ^ d * d.factorial ≤ B * a ^ d) :
    1 ≤ (B : ℝ) * (((n.choose d : ℝ) * ((B - 1 : ℕ) : ℝ) ^ (n - d)) / (B : ℝ) ^ n) := by
  have hB_pos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by rw [hn]; exact Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  -- `((B - 1) / B)^(n - d) ≥ ((B - 1) / B)^(a * (B - 1)) = ((1 - B⁻¹)^(B - 1))^a ≥ (1 / 3)^a`.
  have hpow_ge : (1 / 3 : ℝ) ^ a ≤ (((B - 1 : ℕ) : ℝ) / (B : ℝ)) ^ (n - d) := by
    have hdiv_eq : ((B - 1 : ℕ) : ℝ) / (B : ℝ) = 1 - (B : ℝ)⁻¹ := by
      rw [Nat.cast_sub (by omega : 1 ≤ B), Nat.cast_one, sub_div, div_self hB_pos.ne', one_div]
    rw [hdiv_eq]
    have hbase_nn : 0 ≤ 1 - (B : ℝ)⁻¹ := by
      rw [sub_nonneg, inv_le_one_iff₀]
      right
      exact_mod_cast (by omega : 1 ≤ B)
    have hbase_le1 : 1 - (B : ℝ)⁻¹ ≤ 1 := by
      have : 0 ≤ (B : ℝ)⁻¹ := inv_nonneg.mpr hB_pos.le
      linarith
    have hexp_le : n - d ≤ a * (B - 1) := by
      have hmul : a * B = a * (B - 1) + a := by
        cases B with
        | zero => omega
        | succ B' => simp [Nat.mul_succ]
      omega
    have hmono : (1 - (B : ℝ)⁻¹) ^ (a * (B - 1)) ≤ (1 - (B : ℝ)⁻¹) ^ (n - d) :=
      pow_le_pow_of_le_one hbase_nn hbase_le1 hexp_le
    have hstep : (1 / 3 : ℝ) ≤ (1 - (B : ℝ)⁻¹) ^ (B - 1) := by
      have hB1 : ((B - 1 : ℕ) : ℝ) + 1 ≤ (B : ℝ) := by
        exact_mod_cast (by omega : B - 1 + 1 ≤ B)
      have hexp1 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      have heinv : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
        rw [Real.exp_neg, one_div]
        exact inv_anti₀ (Real.exp_pos 1) hexp1.le
      exact heinv.trans (Real.exp_neg_one_le_one_sub_inv_pow hB1)
    calc (1 / 3 : ℝ) ^ a
        ≤ ((1 - (B : ℝ)⁻¹) ^ (B - 1)) ^ a := pow_le_pow_left₀ (by norm_num) hstep a
      _ = (1 - (B : ℝ)⁻¹) ^ (a * (B - 1)) := by rw [← pow_mul, mul_comm]
      _ ≤ (1 - (B : ℝ)⁻¹) ^ (n - d) := hmono
  -- `(n)_d / n^d ≥ (1 / 2)^d`, since `i < d ≤ n / 2`.
  have hdesc_ge : (1 / 2 : ℝ) ^ d ≤ (n.descFactorial d : ℝ) / (n : ℝ) ^ d := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hhalf : (1 / 2 : ℝ) ^ d = ∏ _i ∈ range d, (1 / 2 : ℝ) := by rw [prod_const, card_range]
    have hpow_n : (n : ℝ) ^ d = ∏ _i ∈ range d, (n : ℝ) := by rw [prod_const, card_range]
    rw [hhalf, hpow_n, ← Finset.prod_div_distrib]
    refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i hi => ?_
    rw [mem_range] at hi
    rw [div_le_div_iff₀ (by norm_num) hn_pos, Nat.cast_sub (by omega : i ≤ n)]
    have h2i : (2 : ℝ) * (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 * i ≤ n)
    linarith
  have hchoose_eq : (n.choose d : ℝ) = (n.descFactorial d : ℝ) / (d.factorial : ℝ) := by
    rw [eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)), mul_comm]
    exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose n d).symm
  have hB_split : (B : ℝ) ^ n = (B : ℝ) ^ d * (B : ℝ) ^ (n - d) := by
    rw [← pow_add, Nat.add_sub_of_le (by omega : d ≤ n)]
  have hn_cast : (n : ℝ) = (a : ℝ) * (B : ℝ) := by exact_mod_cast hn
  have hrew :
      ((n.choose d : ℝ) * ((B - 1 : ℕ) : ℝ) ^ (n - d)) / (B : ℝ) ^ n =
        ((n.descFactorial d : ℝ) / (n : ℝ) ^ d) * ((a : ℝ) ^ d / (d.factorial : ℝ)) *
          (((B - 1 : ℕ) : ℝ) / (B : ℝ)) ^ (n - d) := by
    rw [hchoose_eq, hB_split, div_pow, hn_cast, mul_pow]
    field_simp [hB_pos.ne', ha_pos.ne', Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)]
  rw [hrew]
  have hfac_pos : (0 : ℝ) < (d.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos d)
  have hcond_r : (3 : ℝ) ^ a * (2 : ℝ) ^ d * (d.factorial : ℝ) ≤ (B : ℝ) * (a : ℝ) ^ d := by
    exact_mod_cast hcond
  have hprod_ge :
      (1 / 2 : ℝ) ^ d * ((a : ℝ) ^ d / (d.factorial : ℝ)) * (1 / 3 : ℝ) ^ a ≤
        ((n.descFactorial d : ℝ) / (n : ℝ) ^ d) * ((a : ℝ) ^ d / (d.factorial : ℝ)) *
          (((B - 1 : ℕ) : ℝ) / (B : ℝ)) ^ (n - d) := by gcongr
  have hsimp :
      (B : ℝ) * ((1 / 2 : ℝ) ^ d * ((a : ℝ) ^ d / (d.factorial : ℝ)) * (1 / 3 : ℝ) ^ a) =
        ((B : ℝ) * (a : ℝ) ^ d) / ((3 : ℝ) ^ a * (2 : ℝ) ^ d * (d.factorial : ℝ)) := by
    rw [one_div_pow, one_div_pow]
    field_simp
  have hge1 : 1 ≤ ((B : ℝ) * (a : ℝ) ^ d) / ((3 : ℝ) ^ a * (2 : ℝ) ^ d * (d.factorial : ℝ)) :=
    (one_le_div (by positivity)).mpr hcond_r
  calc (1 : ℝ) ≤ (B : ℝ) * ((1 / 2 : ℝ) ^ d * ((a : ℝ) ^ d / (d.factorial : ℝ)) *
          (1 / 3 : ℝ) ^ a) := by
        rw [hsimp]; exact hge1
    _ ≤ (B : ℝ) * (((n.descFactorial d : ℝ) / (n : ℝ) ^ d) * ((a : ℝ) ^ d / (d.factorial : ℝ)) *
          (((B - 1 : ℕ) : ℝ) / (B : ℝ)) ^ (n - d)) :=
        mul_le_mul_of_nonneg_left hprod_ge hB_pos.le

/-- **General balls-into-bins lower tail for `n = a * B` balls in `B` bins** ([Vocking2007],
Proposition 20.11; locator not re-verified against primary PDF): when `n = a * B` balls (`a ≥ 1`)
are thrown independently and uniformly into `B ≥ 2` bins, if `2 * a ≤ d`, `2 * d ≤ n`, and
`3 ^ a * 2 ^ d * d! ≤ B * a ^ d`, then some bin receives at least `d` balls with probability at
least `1 / 2`. -/
theorem ballsIntoBins_mul_tail_ge_half {n a B d : ℕ} [NeZero B] (hn : n = a * B)
    (ha : 1 ≤ a) (hB : 2 ≤ B) (hd : 2 * a ≤ d) (h2d : 2 * d ≤ n)
    (hcond : 3 ^ a * 2 ^ d * d.factorial ≤ B * a ^ d) :
    (1 / 2 : ℝ) ≤
      ∑ A : Fin n → Fin B,
        if ∃ j : Fin B, d ≤ #(univ.filter fun i : Fin n => A i = j) then
          (1 / (B : ℝ)) ^ n
        else 0 := by
  have hB_pos : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr (NeZero.pos B)
  set w : ℝ := (1 / (B : ℝ)) ^ n
  have hw_nn : 0 ≤ w := by positivity
  let ind (A : Fin n → Fin B) (j : Fin B) : ℝ :=
    if #(univ.filter fun i : Fin n => A i = j) = d then 1 else 0
  let Y (A : Fin n → Fin B) : ℝ := ∑ j : Fin B, ind A j
  let good : Finset (Fin n → Fin B) := univ.filter fun A => 0 < Y A
  set p : ℝ := ((n.choose d : ℝ) * ((B - 1 : ℕ) : ℝ) ^ (n - d)) / (B : ℝ) ^ n
  set q : ℝ :=
    ((n.choose d : ℝ) * ((n - d).choose d : ℝ) * ((B - 2 : ℕ) : ℝ) ^ (n - 2 * d)) / (B : ℝ) ^ n
  have hbin : ∀ j : Fin B, ∑ A : Fin n → Fin B, w * ind A j = p := fun j => by
    simp only [ind, mul_ite, mul_one, mul_zero, ← sum_filter, sum_const, nsmul_eq_mul,
      card_filter_binLoad_eq]
    simp only [w, p, one_div_pow, Nat.cast_mul, Nat.cast_pow]
    ring
  have hEY : ∑ A : Fin n → Fin B, w * Y A = (B : ℝ) * p := by
    simp only [Y, mul_sum]
    rw [sum_comm]
    simp only [hbin, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hEY2 : ∑ A : Fin n → Fin B, w * (Y A) ^ 2 =
      (B : ℝ) * p + (B : ℝ) * ((B : ℝ) - 1) * q := by
    have hsq : ∀ A : Fin n → Fin B,
        w * (Y A) ^ 2 =
          (∑ j : Fin B, w * ind A j) +
          ∑ j₁ : Fin B, ∑ j₂ ∈ univ.erase j₁, w * (ind A j₁ * ind A j₂) := fun A => by
      have h1 : (Y A) ^ 2 = ∑ j₁ : Fin B, ∑ j₂ : Fin B, ind A j₁ * ind A j₂ := by
        simp only [Y, sq, sum_mul_sum]
      rw [h1, mul_sum]
      have hsplit : ∀ j₁ : Fin B,
          w * ∑ j₂ : Fin B, ind A j₁ * ind A j₂ =
            w * ind A j₁ + ∑ j₂ ∈ univ.erase j₁, w * (ind A j₁ * ind A j₂) := fun j₁ => by
        rw [← add_sum_erase _ _ (mem_univ j₁), mul_add, mul_sum]
        congr 1
        simp only [ind]
        split_ifs <;> ring
      simp_rw [hsplit, sum_add_distrib]
    simp_rw [hsq, sum_add_distrib]
    congr 1
    · rw [sum_comm]
      simp only [hbin, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    · rw [sum_comm]
      have houter : ∀ j₁ : Fin B,
          ∑ A : Fin n → Fin B, ∑ j₂ ∈ univ.erase j₁, w * (ind A j₁ * ind A j₂) =
            ((B : ℝ) - 1) * q := fun j₁ => by
        rw [sum_comm]
        have hpair : ∀ j₂ ∈ univ.erase j₁,
            ∑ A : Fin n → Fin B, w * (ind A j₁ * ind A j₂) = q := fun j₂ hj₂ => by
          have hne : j₁ ≠ j₂ := (ne_of_mem_erase hj₂).symm
          have hind : ∀ A : Fin n → Fin B,
              w * (ind A j₁ * ind A j₂) =
                if #(univ.filter fun i : Fin n => A i = j₁) = d ∧
                   #(univ.filter fun i : Fin n => A i = j₂) = d then w else 0 := fun A => by
            simp only [ind]
            split_ifs <;> simp_all
          simp_rw [hind]
          rw [← sum_filter, sum_const, nsmul_eq_mul, card_filter_binLoad_pair_eq n B d hne]
          simp only [w, q, one_div_pow, Nat.cast_mul, Nat.cast_pow]
          ring
        rw [sum_congr rfl hpair, sum_const, card_erase_of_mem (mem_univ j₁), card_univ,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (NeZero.pos B), Nat.cast_one]
      simp only [houter, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  have hY_nn : ∀ A, 0 ≤ Y A := fun A =>
    sum_nonneg fun j _ => by simp only [ind]; split_ifs <;> norm_num
  have hEY_good : ∑ A ∈ good, w * Y A = ∑ A : Fin n → Fin B, w * Y A := by
    refine sum_subset (subset_univ good) fun A _ hA => ?_
    simp only [good, mem_filter, mem_univ, true_and, not_lt] at hA
    rw [le_antisymm hA (hY_nn A), mul_zero]
  have hCS : (∑ A ∈ good, w * Y A) ^ 2 ≤
      (∑ A ∈ good, w) * (∑ A ∈ good, w * (Y A) ^ 2) := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq good
      (fun _ => Real.sqrt w) (fun A => Real.sqrt w * Y A)
    have hlhs : ∑ A ∈ good, Real.sqrt w * (Real.sqrt w * Y A) = ∑ A ∈ good, w * Y A :=
      sum_congr rfl fun A _ => by
        rw [← mul_assoc, Real.mul_self_sqrt hw_nn]
    have hrhs1 : ∑ A ∈ good, (Real.sqrt w) ^ 2 = ∑ A ∈ good, w :=
      sum_congr rfl fun _ _ => Real.sq_sqrt hw_nn
    have hrhs2 : ∑ A ∈ good, (Real.sqrt w * Y A) ^ 2 = ∑ A ∈ good, w * (Y A) ^ 2 :=
      sum_congr rfl fun A _ => by rw [mul_pow, Real.sq_sqrt hw_nn]
    rwa [hlhs, hrhs1, hrhs2] at h1
  have hEY2_mono : ∑ A ∈ good, w * (Y A) ^ 2 ≤ ∑ A : Fin n → Fin B, w * (Y A) ^ 2 :=
    sum_le_univ_sum_of_nonneg fun A => mul_nonneg hw_nn (sq_nonneg _)
  have hPZ : ((B : ℝ) * p) ^ 2 ≤
      (∑ A ∈ good, w) * ((B : ℝ) * p + (B : ℝ) * ((B : ℝ) - 1) * q) := by
    calc ((B : ℝ) * p) ^ 2
        = (∑ A ∈ good, w * Y A) ^ 2 := by rw [hEY_good, hEY]
      _ ≤ (∑ A ∈ good, w) * (∑ A ∈ good, w * (Y A) ^ 2) := hCS
      _ ≤ (∑ A ∈ good, w) * (∑ A : Fin n → Fin B, w * (Y A) ^ 2) :=
          mul_le_mul_of_nonneg_left hEY2_mono (sum_nonneg fun _ _ => hw_nn)
      _ = (∑ A ∈ good, w) * ((B : ℝ) * p + (B : ℝ) * ((B : ℝ) - 1) * q) := by rw [hEY2]
  have hq_le : q ≤ p ^ 2 := pair_prob_le_sq_single_prob hn hB hd h2d
  have hBp_ge1 : 1 ≤ (B : ℝ) * p := one_le_expected_count_exact hn ha hB hd h2d hcond
  have hEY2_le : (B : ℝ) * p + (B : ℝ) * ((B : ℝ) - 1) * q ≤ 2 * ((B : ℝ) * p) ^ 2 := by
    have hB1_nn : 0 ≤ (B : ℝ) - 1 := by
      linarith [(Nat.one_le_cast.mpr (NeZero.pos B) : (1 : ℝ) ≤ B)]
    have hq_term : (B : ℝ) * ((B : ℝ) - 1) * q ≤ ((B : ℝ) * p) ^ 2 := by
      linarith [mul_le_mul_of_nonneg_left hq_le (mul_nonneg hB_pos.le hB1_nn),
        mul_nonneg hB_pos.le (sq_nonneg p)]
    nlinarith
  have hprob_good : (1 / 2 : ℝ) ≤ ∑ A ∈ good, w := by
    have hsum_nn : 0 ≤ ∑ A ∈ good, w := sum_nonneg fun _ _ => hw_nn
    have hcomb : ((B : ℝ) * p) ^ 2 ≤ (∑ A ∈ good, w) * (2 * ((B : ℝ) * p) ^ 2) :=
      hPZ.trans (mul_le_mul_of_nonneg_left hEY2_le hsum_nn)
    have hpos_sq : 0 < ((B : ℝ) * p) ^ 2 := by nlinarith
    nlinarith
  have hgood_sub : ∀ A ∈ good, ∃ j : Fin B, d ≤ #(univ.filter fun i : Fin n => A i = j) := by
    intro A hA
    simp only [good, mem_filter, mem_univ, true_and] at hA
    obtain ⟨j, -, hj⟩ := exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℝ))
      (by simpa only [sum_const_zero] using hA)
    exact ⟨j, (not_ne_iff.1 fun hne => by simp [ind, hne] at hj).ge⟩
  calc (1 / 2 : ℝ) ≤ ∑ A ∈ good, w := hprob_good
    _ = ∑ A ∈ good,
          if ∃ j : Fin B, d ≤ #(univ.filter fun i : Fin n => A i = j) then w else 0 := by
        exact sum_congr rfl fun A hA => (ite_eq_left (hgood_sub A hA)).symm
    _ ≤ ∑ A : Fin n → Fin B,
          if ∃ j : Fin B, d ≤ #(univ.filter fun i : Fin n => A i = j) then w else 0 := by
        refine sum_le_univ_sum_of_nonneg fun A => ?_
        split_ifs
        · exact hw_nn
        · exact le_rfl

/-- **Balls-into-bins lower tail** ([Vocking2007], Proposition 20.11; locator not re-verified
against primary PDF): when `m` balls are thrown uniformly and independently into `m` bins, if
`2 ≤ k` and `3 * 2 ^ k * k! ≤ m`, then the maximum bin load is at least `k` with probability at
least `1 / 2`. -/
theorem ballsIntoBins_tail_ge_half {m k : ℕ} [NeZero m] (hk : 2 ≤ k)
    (hm : 3 * 2 ^ k * k.factorial ≤ m) :
    (1 / 2 : ℝ) ≤
      ∑ A : Fin m → Fin m,
        if (k : ℝ) ≤ (unitIdenticalGame m).makespan A then
          productWeight (uniformMixedProfile m) A
        else 0 := by
  have h2k : 2 * k ≤ m := by
    have hk_le : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    have hfac : 2 ≤ k.factorial := Nat.factorial_le hk
    nlinarith
  have hm2 : 2 ≤ m := by omega
  have hmul := ballsIntoBins_mul_tail_ge_half (n := m) (a := 1) (B := m) (d := k)
    (one_mul m).symm le_rfl hm2 (by omega) h2k (by simpa using hm)
  refine hmul.trans (sum_le_sum fun A _ => ?_)
  rw [productWeight_uniformMixedProfile]
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso
    obtain ⟨j, hj⟩ := h1
    apply h2
    calc (k : ℝ) ≤ (#(univ.filter fun i : Fin m => A i = j) : ℝ) := by exact_mod_cast hj
      _ = (unitIdenticalGame m).load A j := (load_unitIdenticalGame_eq_card m A j).symm
      _ ≤ (unitIdenticalGame m).makespan A := (unitIdenticalGame m).load_le_makespan A j
  · positivity
  · exact le_rfl

/-- Expectation consequence of the balls-into-bins lower tail: if `2 ≤ k` and `3 * 2 ^ k * k! ≤ m`,
then `expectedMakespan ≥ k / 2`. -/
theorem ballsIntoBins_expectedMakespan_ge_half_of_factorial {m k : ℕ} [NeZero m] (hk : 2 ≤ k)
    (hm : 3 * 2 ^ k * k.factorial ≤ m) :
    (k : ℝ) / 2 ≤ (unitIdenticalGame m).expectedMakespan (uniformMixedProfile m) := by
  have htail := ballsIntoBins_tail_ge_half (m := m) hk hm
  have hpt : ∀ A : Fin m → Fin m,
      (k : ℝ) * (if (k : ℝ) ≤ (unitIdenticalGame m).makespan A then
          productWeight (uniformMixedProfile m) A else 0) ≤
        productWeight (uniformMixedProfile m) A * (unitIdenticalGame m).makespan A := fun A => by
    have hw_nn : 0 ≤ productWeight (uniformMixedProfile m) A := by
      rw [productWeight_uniformMixedProfile]; positivity
    split_ifs with h
    · nlinarith
    · rw [mul_zero]
      exact mul_nonneg hw_nn ((unitIdenticalGame m).makespan_nonneg A)
  calc (k : ℝ) / 2 = (k : ℝ) * (1 / 2 : ℝ) := by ring
    _ ≤ (k : ℝ) * ∑ A : Fin m → Fin m,
          if (k : ℝ) ≤ (unitIdenticalGame m).makespan A then
            productWeight (uniformMixedProfile m) A else 0 :=
        mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg k)
    _ = ∑ A : Fin m → Fin m, (k : ℝ) *
          (if (k : ℝ) ≤ (unitIdenticalGame m).makespan A then
            productWeight (uniformMixedProfile m) A else 0) := mul_sum _ _ _
    _ ≤ ∑ A : Fin m → Fin m,
          productWeight (uniformMixedProfile m) A * (unitIdenticalGame m).makespan A :=
        sum_le_sum fun A _ => hpt A
    _ = (unitIdenticalGame m).expectedMakespan (uniformMixedProfile m) := rfl

/-- On `m ≥ 1` identical machines with `m` unit jobs, the uniform profile has expected makespan at
least `1`. -/
theorem one_le_expectedMakespan_unitIdenticalGame (m : ℕ) [NeZero m] :
    1 ≤ (unitIdenticalGame m).expectedMakespan (uniformMixedProfile m) := by
  have hp1 : ∀ i : Fin m, ∑ j : Fin m, uniformMixedProfile m i j = 1 := fun _ => by
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (NeZero.pos m)
    simp only [uniformMixedProfile, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hms1 : ∀ A : Fin m → Fin m, 1 ≤ (unitIdenticalGame m).makespan A := fun A => by
    have h := (unitIdenticalGame m).optMakespan_le A
    rwa [optMakespan_unitIdenticalGame] at h
  calc (1 : ℝ) = ∑ A : Fin m → Fin m, productWeight (uniformMixedProfile m) A * 1 := by
        simp [sum_productWeight hp1]
    _ ≤ ∑ A : Fin m → Fin m,
          productWeight (uniformMixedProfile m) A * (unitIdenticalGame m).makespan A := by
        refine sum_le_sum fun A _ => mul_le_mul_of_nonneg_left (hms1 A) ?_
        rw [productWeight_uniformMixedProfile]
        positivity
    _ = (unitIdenticalGame m).expectedMakespan (uniformMixedProfile m) := rfl

/-- **Balls-into-bins & identical-machine mixed PoA lower bound** ([KoutsoupiasPapadimitriou1999];
[CzumajVocking2002]; [Vocking2007], Proposition 20.11 and Theorem 20.12; locator not re-verified
against primary PDF): for every `m ≥ 3`, the uniform totally mixed Nash equilibrium on `m` unit
jobs and `m` identical machines achieves expected makespan at least
`(1 / 20) * (log m / log (log m)) * optMakespan`. -/
theorem expectedMakespan_uniformMixedProfile_ge_log_div_log_log {m : ℕ} [NeZero m] (hm : 3 ≤ m) :
    (1 / 20 : ℝ) * (Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))) *
      (unitIdenticalGame m).optMakespan ≤
        (unitIdenticalGame m).expectedMakespan (uniformMixedProfile m) := by
  rw [optMakespan_unitIdenticalGame, mul_one]
  by_cases hm24 : 24 ≤ m
  · -- Large `m ≥ 24`: choose maximal `k ≥ 2` with `3 * 2^k * k! ≤ m`.
    let f : ℕ → ℕ := fun k => 3 * 2 ^ k * k.factorial
    have hS_ne : ((range (m + 1)).filter fun k => 2 ≤ k ∧ f k ≤ m).Nonempty := by
      refine ⟨2, mem_filter.mpr ⟨mem_range.mpr (by omega), le_rfl, ?_⟩⟩
      norm_num [f, Nat.factorial]
      omega
    obtain ⟨k, hk_mem, hk_max⟩ :=
      exists_max_image ((range (m + 1)).filter fun k => 2 ≤ k ∧ f k ≤ m) id hS_ne
    obtain ⟨_, hk2, hfk_le⟩ := mem_filter.mp hk_mem
    have hm_lt_next : m < f (k + 1) := by
      by_contra hle
      push Not at hle
      have hk1_lt : k + 1 < m + 1 := by
        have hlin : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
        have h1 : 2 ^ (k + 1) ≤ f (k + 1) := by
          have hfac : 1 ≤ (k + 1).factorial := Nat.factorial_pos (k + 1)
          dsimp only [f]
          nlinarith
        omega
      have hk1_mem : k + 1 ∈ (range (m + 1)).filter fun r => 2 ≤ r ∧ f r ≤ m :=
        mem_filter.mpr ⟨mem_range.mpr hk1_lt, by omega, hle⟩
      have := hk_max (k + 1) hk1_mem
      dsimp only [id_eq] at this
      omega
    have hk_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hexp1 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hexp_lt_m : Real.exp (k : ℝ) < (m : ℝ) := by
      have hexpk : Real.exp (k : ℝ) < (3 : ℝ) ^ k := by
        rw [show (k : ℝ) = (k : ℕ) * (1 : ℝ) by ring, Real.exp_nat_mul]
        exact pow_lt_pow_left₀ hexp1 (Real.exp_pos 1).le (by omega)
      have h3le : 3 ^ k ≤ m := by
        have h4 := Nat.four_pow_le_two_mul_two_pow_mul_factorial (by omega : 1 ≤ k)
        have h34 : 3 ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) k
        have hfk' : 3 * (2 ^ k * k.factorial) ≤ m := by
          dsimp only [f] at hfk_le
          linarith
        omega
      have h3le_real : (3 : ℝ) ^ k ≤ (m : ℝ) := by exact_mod_cast h3le
      exact hexpk.trans_le h3le_real
    have hm_pos_real : (0 : ℝ) < (m : ℝ) := (Real.exp_pos _).trans hexp_lt_m
    have hlog3_le : Real.log 3 ≤ (k : ℝ) * Real.log (k : ℝ) := by
      have hlogk_pos : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
      calc Real.log 3 ≤ Real.log ((k : ℝ) ^ 2) := Real.log_le_log (by norm_num) (by nlinarith)
        _ = 2 * Real.log (k : ℝ) := by rw [Real.log_pow]; norm_num
        _ ≤ (k : ℝ) * Real.log (k : ℝ) := by nlinarith
    have hm_le_nat : m ≤ 3 * 2 ^ (k + 1) * (k + 1) ^ (k + 1) :=
      hm_lt_next.le.trans (Nat.mul_le_mul_left _ (Nat.factorial_le_pow (k + 1)))
    have hm_le : (m : ℝ) ≤ 3 * (2 : ℝ) ^ (k + 1) * ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by
      exact_mod_cast hm_le_nat
    have hlogm_le : Real.log (m : ℝ) ≤ 6 * (k : ℝ) * Real.log (k : ℝ) := by
      have h1 := Real.add_mul_log_two_le (d := 1) hk_real zero_le_one
      have h2 := Real.add_one_mul_log_add_one_le hk_real
      calc Real.log (m : ℝ)
          ≤ Real.log (3 * (2 : ℝ) ^ (k + 1) * ((k + 1 : ℕ) : ℝ) ^ (k + 1)) :=
            Real.log_le_log hm_pos_real hm_le
        _ = Real.log 3 + ((k : ℝ) + 1) * Real.log 2 +
              ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1) := by
            rw [Real.log_mul (by positivity) (by positivity),
              Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
            push_cast; ring
        _ ≤ 6 * (k : ℝ) * Real.log (k : ℝ) := by
            nlinarith [Real.log_pos (by linarith : (1 : ℝ) < k)]
    obtain ⟨hloglogm_pos, hratio_le_k⟩ :=
      Real.inv_mul_log_div_log_log_le hk_real (by norm_num : (0 : ℝ) < 6) hexp_lt_m hlogm_le
    have hk_bound := ballsIntoBins_expectedMakespan_ge_half_of_factorial (m := m) hk2 hfk_le
    have hratio_nn : 0 ≤ Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)) := by positivity
    linarith
  · -- Small `3 ≤ m ≤ 23`: `1 ≤ expectedMakespan` and `(1 / 20) * (log m / log (log m)) ≤ 1`.
    have h1 := one_le_expectedMakespan_unitIdenticalGame m
    suffices hsmall : Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)) ≤ 20 by linarith
    by_cases hm3 : m = 3
    · subst hm3
      -- `13 / 12 < log 3 < 1.4` and `log (13 / 12) ≥ 1 / 13`, so `log 3 / log (log 3) < 18.2 < 20`.
      have hexp_1_12 : Real.exp (1 / 12 : ℝ) ≤ 12 / 11 := by
        have h1 : (11 / 12 : ℝ) ≤ Real.exp (-(1 / 12 : ℝ)) := by
          linarith [Real.add_one_le_exp (-(1 / 12 : ℝ))]
        rw [Real.exp_neg] at h1
        have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 11 / 12) h1
        rw [inv_inv] at hinv
        linarith [show (11 / 12 : ℝ)⁻¹ = 12 / 11 by norm_num]
      have hexp_13_12 : Real.exp (13 / 12 : ℝ) < 3 := by
        rw [show (13 / 12 : ℝ) = 1 + 1 / 12 by norm_num, Real.exp_add]
        have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        nlinarith [Real.exp_pos (1 / 12 : ℝ)]
      have hlog3_gt : (13 / 12 : ℝ) < Real.log 3 := by
        rw [← Real.log_exp (13 / 12 : ℝ)]
        exact Real.log_lt_log (Real.exp_pos _) hexp_13_12
      have hlog3_lt : Real.log 3 < 1.4 := by
        have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num
        have hlt : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
        linarith [Real.log_two_lt_d9]
      have hloglog3_ge : (1 / 13 : ℝ) ≤ Real.log (Real.log 3) := by
        have hinv : Real.log ((13 / 12 : ℝ)⁻¹) ≤ (13 / 12 : ℝ)⁻¹ - 1 :=
          Real.log_le_sub_one_of_pos (by norm_num)
        rw [Real.log_inv] at hinv
        have hmono : Real.log (13 / 12 : ℝ) ≤ Real.log (Real.log 3) :=
          Real.log_le_log (by norm_num) hlog3_gt.le
        linarith [show (13 / 12 : ℝ)⁻¹ = 12 / 13 by norm_num]
      push_cast
      rw [div_le_iff₀ (by linarith)]
      linarith
    · -- `4 ≤ m ≤ 23`: `4 / 3 < log m < 3.5` and `log (log m) ≥ 1 / 4`, so ratio `≤ 14 ≤ 20`.
      have hm4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 4 ≤ m)
      have hm32 : (m : ℝ) ≤ 32 := by exact_mod_cast (by omega : m ≤ 32)
      have hlogm_gt : (4 / 3 : ℝ) < Real.log (m : ℝ) := by
        have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num
        have hle : Real.log 4 ≤ Real.log (m : ℝ) := Real.log_le_log (by norm_num) hm4
        linarith [Real.log_two_gt_d9]
      have hlogm_lt : Real.log (m : ℝ) < 3.5 := by
        have hlog32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
          rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
          norm_num
        have hle : Real.log (m : ℝ) ≤ Real.log 32 := Real.log_le_log (by linarith) hm32
        linarith [Real.log_two_lt_d9]
      have hloglogm_ge : (1 / 4 : ℝ) ≤ Real.log (Real.log (m : ℝ)) := by
        have hinv : Real.log ((4 / 3 : ℝ)⁻¹) ≤ (4 / 3 : ℝ)⁻¹ - 1 :=
          Real.log_le_sub_one_of_pos (by norm_num)
        rw [Real.log_inv] at hinv
        have hmono : Real.log (4 / 3 : ℝ) ≤ Real.log (Real.log (m : ℝ)) :=
          Real.log_le_log (by norm_num) hlogm_gt.le
        linarith [show (4 / 3 : ℝ)⁻¹ = 3 / 4 by norm_num]
      rw [div_le_iff₀ (by linarith)]
      linarith

end Cslib.GameTheory.LoadBalancingGame
