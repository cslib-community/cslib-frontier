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
* `Cslib.GameTheory.LoadBalancingGame.ballsIntoBins_tail_ge_half`,
  `Cslib.GameTheory.LoadBalancingGame.ballsIntoBins_expectedMakespan_ge_half_of_factorial`
  ([Vocking2007], Proposition 20.11): lower tail `Pr[max_j L_j ≥ k] ≥ 1 / 2` and expectation bound
  `E[max_j L_j] ≥ k / 2` whenever `2 ≤ k` and `3 * 2 ^ k * k! ≤ m`.
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
@[expose] def unitIdenticalGame (m : ℕ) : LoadBalancingGame (Fin m) (Fin m) :=
  LoadBalancingGame.identical (fun _ => 1) (fun _ => zero_le_one)

/-- The uniform mixed strategy profile `p i j = 1 / m` on `m` identical machines. -/
@[expose] noncomputable def uniformMixedProfile (m : ℕ) : Fin m → Fin m → ℝ :=
  fun _ _ => 1 / (m : ℝ)

theorem isIdentical_unitIdenticalGame (m : ℕ) : (unitIdenticalGame m).IsIdentical :=
  fun _ => rfl

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

/-- Exact count of assignments `Fin m → Fin m` sending exactly `k` balls to bin `j`. -/
private theorem card_filter_binLoad_eq (m k : ℕ) (j : Fin m) :
    #(univ.filter fun A : Fin m → Fin m => #(univ.filter fun i : Fin m => A i = j) = k) =
      m.choose k * (m - 1) ^ (m - k) := by
  classical
  let fibre (S : Finset (Fin m)) : Finset (Fin m → Fin m) :=
    univ.filter fun A => (univ.filter fun i => A i = j) = S
  have hpart :
      (univ.filter fun A : Fin m → Fin m => #(univ.filter fun i : Fin m => A i = j) = k) =
        (univ.powersetCard k).biUnion fibre := by
    ext A
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_powersetCard, subset_univ,
      fibre]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨S, hSk, hAS⟩ => hAS ▸ hSk⟩
  have hdisj :
      Set.PairwiseDisjoint
        ((univ.powersetCard k : Finset (Finset (Fin m))) : Set (Finset (Fin m))) fibre := by
    intro S₁ _ S₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro A h1 h2
    simp only [fibre, mem_filter, mem_univ, true_and] at h1 h2
    exact hne (h1.symm.trans h2)
  rw [hpart, card_biUnion hdisj]
  have hfib_card : ∀ S ∈ univ.powersetCard k, #(fibre S) = (m - 1) ^ (m - k) := by
    intro S hS
    have hSk : #S = k := (mem_powersetCard.mp hS).2
    let e : {A : Fin m → Fin m // A ∈ fibre S} ≃
        ({i : Fin m // i ∉ S} → {x : Fin m // x ≠ j}) :=
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
    have hcard_dom : Fintype.card {i : Fin m // i ∉ S} = m - k := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hSk]
    have hcard_cod : Fintype.card {x : Fin m // x ≠ j} = m - 1 := by
      have heq : (univ.filter fun x : Fin m => x ≠ j) = univ.erase j := by
        ext x
        simp [mem_erase]
      rw [Fintype.card_subtype, heq, card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
    calc #(fibre S) = Fintype.card {A : Fin m → Fin m // A ∈ fibre S} :=
          (Fintype.card_coe (fibre S)).symm
      _ = Fintype.card ({i : Fin m // i ∉ S} → {x : Fin m // x ≠ j}) := Fintype.card_congr e
      _ = (Fintype.card {x : Fin m // x ≠ j}) ^ (Fintype.card {i : Fin m // i ∉ S}) :=
          Fintype.card_fun
      _ = (m - 1) ^ (m - k) := by rw [hcard_dom, hcard_cod]
  rw [sum_congr rfl hfib_card, sum_const, card_powersetCard, card_univ, Fintype.card_fin,
    smul_eq_mul]

/-- Exact count of assignments `Fin m → Fin m` sending `k` balls to `j₁` and `k` balls to `j₂`
(`j₁ ≠ j₂`). -/
private theorem card_filter_binLoad_pair_eq (m k : ℕ) {j₁ j₂ : Fin m} (hne : j₁ ≠ j₂) :
    #(univ.filter fun A : Fin m → Fin m =>
        #(univ.filter fun i : Fin m => A i = j₁) = k ∧
        #(univ.filter fun i : Fin m => A i = j₂) = k) =
      m.choose k * (m - k).choose k * (m - 2) ^ (m - 2 * k) := by
  classical
  let pairs : Finset (Finset (Fin m) × Finset (Fin m)) :=
    (univ.powersetCard k).biUnion fun S₁ =>
      ((univ \ S₁).powersetCard k).image fun S₂ => (S₁, S₂)
  let fibre (P : Finset (Fin m) × Finset (Fin m)) : Finset (Fin m → Fin m) :=
    univ.filter fun A =>
      (univ.filter fun i => A i = j₁) = P.1 ∧ (univ.filter fun i => A i = j₂) = P.2
  have hpart :
      (univ.filter fun A : Fin m → Fin m =>
          #(univ.filter fun i : Fin m => A i = j₁) = k ∧
          #(univ.filter fun i : Fin m => A i = j₂) = k) =
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
      have h1 : S₁' = S₁ := congrArg Prod.fst hpair
      have h2 : S₂' = S₂ := congrArg Prod.snd hpair
      rw [hA1, hA2, ← h1, ← h2]
      exact ⟨hS₁', hS₂'⟩
  have hdisj : Set.PairwiseDisjoint (pairs : Set (Finset (Fin m) × Finset (Fin m))) fibre := by
    intro P₁ _ P₂ _ hPne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro A h1 h2
    simp only [fibre, mem_filter, mem_univ, true_and] at h1 h2
    exact hPne (Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2))
  rw [hpart, card_biUnion hdisj]
  have hfib_card : ∀ P ∈ pairs, #(fibre P) = (m - 2) ^ (m - 2 * k) := by
    intro ⟨S₁, S₂⟩ hP
    simp only [pairs, mem_biUnion, mem_powersetCard, subset_univ, true_and, mem_image,
      Prod.mk.injEq] at hP
    obtain ⟨S₁', hS₁', S₂', ⟨hsub, hS₂'⟩, rfl, rfl⟩ := hP
    have hdisjS : Disjoint S₁' S₂' := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      exact (mem_sdiff.mp (hsub hi2)).2 hi1
    let e : {A : Fin m → Fin m // A ∈ fibre (S₁', S₂')} ≃
        ({i : Fin m // i ∉ S₁' ∪ S₂'} → {x : Fin m // x ≠ j₁ ∧ x ≠ j₂}) :=
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
    have hcard_union : #(S₁' ∪ S₂') = 2 * k := by
      rw [card_union_of_disjoint hdisjS, hS₁', hS₂']
      ring
    have hcard_dom : Fintype.card {i : Fin m // i ∉ S₁' ∪ S₂'} = m - 2 * k := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hcard_union]
    have hcard_cod : Fintype.card {x : Fin m // x ≠ j₁ ∧ x ≠ j₂} = m - 2 := by
      have heq : (univ.filter fun x : Fin m => x ≠ j₁ ∧ x ≠ j₂) = univ \ {j₁, j₂} := by
        ext x
        simp [mem_sdiff, mem_insert, mem_singleton, not_or]
      rw [Fintype.card_subtype, heq, card_sdiff_of_subset (subset_univ _), card_univ,
        Fintype.card_fin, card_pair hne]
    calc #(fibre (S₁', S₂')) = Fintype.card {A : Fin m → Fin m // A ∈ fibre (S₁', S₂')} :=
          (Fintype.card_coe _).symm
      _ = Fintype.card ({i : Fin m // i ∉ S₁' ∪ S₂'} → {x : Fin m // x ≠ j₁ ∧ x ≠ j₂}) :=
          Fintype.card_congr e
      _ = (Fintype.card {x : Fin m // x ≠ j₁ ∧ x ≠ j₂}) ^
            (Fintype.card {i : Fin m // i ∉ S₁' ∪ S₂'}) := Fintype.card_fun
      _ = (m - 2) ^ (m - 2 * k) := by rw [hcard_dom, hcard_cod]
  have hcard_pairs : #pairs = m.choose k * (m - k).choose k := by
    have hdisjP :
        Set.PairwiseDisjoint
          ((univ.powersetCard k : Finset (Finset (Fin m))) : Set (Finset (Fin m)))
          (fun S₁ => ((univ \ S₁).powersetCard k).image fun S₂ => (S₁, S₂)) := by
      intro S₁ _ S₁' _ hneS
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro P h1 h2
      simp only [mem_image] at h1 h2
      obtain ⟨_, _, rfl⟩ := h1
      obtain ⟨_, _, hEq⟩ := h2
      exact hneS (congrArg Prod.fst hEq).symm
    dsimp only [pairs]
    rw [card_biUnion hdisjP]
    have hinner : ∀ S₁ ∈ (univ : Finset (Fin m)).powersetCard k,
        #(((univ \ S₁).powersetCard k).image fun S₂ => (S₁, S₂)) = (m - k).choose k := by
      intro S₁ hS₁
      rw [card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h), card_powersetCard,
        card_sdiff_of_subset (subset_univ S₁), card_univ, Fintype.card_fin,
        (mem_powersetCard.mp hS₁).2]
    rw [sum_congr rfl hinner, sum_const, card_powersetCard, card_univ, Fintype.card_fin,
      smul_eq_mul]
  rw [sum_congr rfl hfib_card, sum_const, smul_eq_mul, hcard_pairs]

/-- Negative correlation of exact-load events for two distinct bins: for `2 ≤ k` and `2 * k ≤ m`,
`Pr[L_{j₁} = k ∧ L_{j₂} = k] ≤ Pr[L_j = k] ^ 2`. -/
private theorem pair_prob_le_sq_single_prob {m k : ℕ} (hk : 2 ≤ k) (h2k : 2 * k ≤ m) :
    ((m.choose k : ℝ) * ((m - k).choose k : ℝ) * ((m - 2 : ℕ) : ℝ) ^ (m - 2 * k)) /
        (m : ℝ) ^ m ≤
      (((m.choose k : ℝ) * ((m - 1 : ℕ) : ℝ) ^ (m - k)) / (m : ℝ) ^ m) ^ 2 := by
  have hm4 : 4 ≤ m := by omega
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
    linarith
  have hm2_nn : (0 : ℝ) ≤ (m : ℝ) - 2 := by
    have : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
    linarith
  -- Step 1: `(m - 2) * m ≤ (m - 1) ^ 2` gives `(m - 2)^(m - 2k) * m^(m - 2k) ≤ (m - 1)^(2m - 4k)`.
  have hquad : ((m - 2 : ℕ) : ℝ) * (m : ℝ) ≤ ((m - 1 : ℕ) : ℝ) ^ 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ m), Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast
    nlinarith
  have hpow1 : (((m - 2 : ℕ) : ℝ) * (m : ℝ)) ^ (m - 2 * k) ≤
      (((m - 1 : ℕ) : ℝ) ^ 2) ^ (m - 2 * k) :=
    pow_le_pow_left₀ (by positivity) hquad (m - 2 * k)
  -- Step 2: `C(m - k, k) * m^(2k) ≤ C(m, k) * (m - 1)^(2k)`.
  have hchoose : ((m - k).choose k : ℝ) * (m : ℝ) ^ (2 * k) ≤
      (m.choose k : ℝ) * ((m - 1 : ℕ) : ℝ) ^ (2 * k) := by
    have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
    suffices hdesc : ((m - k).descFactorial k : ℝ) * (m : ℝ) ^ (2 * k) ≤
        (m.descFactorial k : ℝ) * ((m - 1 : ℕ) : ℝ) ^ (2 * k) by
      have h1 : (k.factorial : ℝ) * ((m - k).choose k : ℝ) = ((m - k).descFactorial k : ℝ) := by
        exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose (m - k) k).symm
      have h2 : (k.factorial : ℝ) * (m.choose k : ℝ) = (m.descFactorial k : ℝ) := by
        exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose m k).symm
      rw [← h1, ← h2] at hdesc
      exact le_of_mul_le_mul_left (by linarith :
        (k.factorial : ℝ) * (((m - k).choose k : ℝ) * (m : ℝ) ^ (2 * k)) ≤
        (k.factorial : ℝ) * ((m.choose k : ℝ) * ((m - 1 : ℕ) : ℝ) ^ (2 * k))) hfac_pos
    rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range, Nat.cast_prod,
      Nat.cast_prod]
    have hpow_m : (m : ℝ) ^ (2 * k) = ∏ _i ∈ range k, ((m : ℝ) ^ 2) := by
      rw [prod_const, card_range, ← pow_mul]
    have hpow_m1 : ((m - 1 : ℕ) : ℝ) ^ (2 * k) = ∏ _i ∈ range k, (((m - 1 : ℕ) : ℝ) ^ 2) := by
      rw [prod_const, card_range, ← pow_mul]
    rw [hpow_m, hpow_m1, ← prod_mul_distrib, ← prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i hi => ?_
    rw [mem_range] at hi
    rw [Nat.cast_sub (by omega : i ≤ m - k), Nat.cast_sub (by omega : k ≤ m),
      Nat.cast_sub (by omega : i ≤ m), Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast
    have hk_r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hi_nn : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hi_le : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : i ≤ m)
    -- Show `(m - k - i) * m^2 ≤ (m - i) * (m - 1)^2`:
    -- RHS - LHS = (k - 2) * m^2 + (m + 2i) * m - i ≥ 0 since `k ≥ 2` and `i ≤ m`.
    nlinarith
  -- Combine Step 1 and Step 2.
  have hexp_m : m - 2 * k + 2 * k = m := by omega
  have hexp_m1 : 2 * (m - 2 * k) + 2 * k = 2 * (m - k) := by omega
  have hnum :
      (m.choose k : ℝ) * ((m - k).choose k : ℝ) * ((m - 2 : ℕ) : ℝ) ^ (m - 2 * k) * (m : ℝ) ^ m ≤
      (m.choose k : ℝ) ^ 2 * ((m - 1 : ℕ) : ℝ) ^ (2 * (m - k)) := by
    have h1 : ((m - 2 : ℕ) : ℝ) ^ (m - 2 * k) * (m : ℝ) ^ (m - 2 * k) ≤
        ((m - 1 : ℕ) : ℝ) ^ (2 * (m - 2 * k)) := by
      simpa only [mul_pow, ← pow_mul] using hpow1
    have hprod :
        (((m - k).choose k : ℝ) * (m : ℝ) ^ (2 * k)) *
          (((m - 2 : ℕ) : ℝ) ^ (m - 2 * k) * (m : ℝ) ^ (m - 2 * k)) ≤
        ((m.choose k : ℝ) * ((m - 1 : ℕ) : ℝ) ^ (2 * k)) *
          ((m - 1 : ℕ) : ℝ) ^ (2 * (m - 2 * k)) :=
      mul_le_mul hchoose h1 (by positivity) (by positivity)
    have hlhs :
        (m.choose k : ℝ) * ((m - k).choose k : ℝ) * ((m - 2 : ℕ) : ℝ) ^ (m - 2 * k) *
          (m : ℝ) ^ m =
        (m.choose k : ℝ) *
          ((((m - k).choose k : ℝ) * (m : ℝ) ^ (2 * k)) *
            (((m - 2 : ℕ) : ℝ) ^ (m - 2 * k) * (m : ℝ) ^ (m - 2 * k))) := by
      have hm_split : (m : ℝ) ^ m = (m : ℝ) ^ (2 * k) * (m : ℝ) ^ (m - 2 * k) := by
        rw [← pow_add, add_comm, hexp_m]
      rw [hm_split]
      ring
    have hrhs :
        (m.choose k : ℝ) ^ 2 * ((m - 1 : ℕ) : ℝ) ^ (2 * (m - k)) =
        (m.choose k : ℝ) *
          (((m.choose k : ℝ) * ((m - 1 : ℕ) : ℝ) ^ (2 * k)) *
            ((m - 1 : ℕ) : ℝ) ^ (2 * (m - 2 * k))) := by
      have hm1_split : ((m - 1 : ℕ) : ℝ) ^ (2 * (m - k)) =
          ((m - 1 : ℕ) : ℝ) ^ (2 * k) * ((m - 1 : ℕ) : ℝ) ^ (2 * (m - 2 * k)) := by
        rw [← pow_add, add_comm, hexp_m1]
      rw [hm1_split]
      ring
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
  rw [div_pow, mul_pow, ← pow_mul, mul_comm (m - k) 2]
  rw [div_le_div_iff₀ (pow_pos hm_pos m) (pow_pos (pow_pos hm_pos m) 2)]
  have hcancel :
      (m.choose k : ℝ) * ((m - k).choose k : ℝ) * ((m - 2 : ℕ) : ℝ) ^ (m - 2 * k) *
        ((m : ℝ) ^ m) ^ 2 =
      ((m.choose k : ℝ) * ((m - k).choose k : ℝ) * ((m - 2 : ℕ) : ℝ) ^ (m - 2 * k) *
        (m : ℝ) ^ m) * (m : ℝ) ^ m := by ring
  rw [hcancel]
  exact mul_le_mul_of_nonneg_right hnum (by positivity)

/-- Lower bound on `m * p_k`: when `2 ≤ k` and `3 * 2 ^ k * k! ≤ m`, the expected number of bins
receiving exact load `k` is at least `1`. -/
private theorem one_le_expected_count_exact {m k : ℕ} (hk : 2 ≤ k)
    (hm : 3 * 2 ^ k * k.factorial ≤ m) :
    1 ≤ (m : ℝ) * (((m.choose k : ℝ) * ((m - 1 : ℕ) : ℝ) ^ (m - k)) / (m : ℝ) ^ m) := by
  have h2k : 2 * k ≤ m := by
    have h1 : 2 * k ≤ 2 ^ k * k.factorial := by
      have hk_le : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
      have hfac : 2 ≤ k.factorial := by
        have := Nat.factorial_le hk
        norm_num [Nat.factorial] at this
        exact this
      nlinarith
    have h3 : 2 ^ k * k.factorial ≤ 3 * 2 ^ k * k.factorial := by nlinarith
    omega
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  -- `(m - 1)^(m - k) / m^(m - k) = (1 - m⁻¹)^(m - k) ≥ e⁻¹ > 1 / 3`.
  have hpow_ge : (1 / 3 : ℝ) ≤ (((m - 1 : ℕ) : ℝ) / (m : ℝ)) ^ (m - k) := by
    have hdiv_eq : ((m - 1 : ℕ) : ℝ) / (m : ℝ) = 1 - (m : ℝ)⁻¹ := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one, sub_div, div_self hm_pos.ne', one_div]
    rw [hdiv_eq]
    have ha : ((m - k : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast (by omega : m - k + 1 ≤ m)
    have hexp1 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have heinv : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (Real.exp_pos 1) hexp1.le
    exact heinv.trans (Real.exp_neg_one_le_one_sub_inv_pow ha)
  -- `(m)_k / m^k ≥ (1 / 2)^k`, since each factor `(m - i) / m ≥ 1 / 2` for `i < k ≤ m / 2`.
  have hdesc_ge : (1 / 2 : ℝ) ^ k ≤ (m.descFactorial k : ℝ) / (m : ℝ) ^ k := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hhalf : (1 / 2 : ℝ) ^ k = ∏ _i ∈ range k, (1 / 2 : ℝ) := by rw [prod_const, card_range]
    have hpow_m : (m : ℝ) ^ k = ∏ _i ∈ range k, (m : ℝ) := by rw [prod_const, card_range]
    rw [hhalf, hpow_m, ← Finset.prod_div_distrib]
    refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i hi => ?_
    rw [mem_range] at hi
    rw [div_le_div_iff₀ (by norm_num) hm_pos, Nat.cast_sub (by omega : i ≤ m)]
    have h2i : (2 : ℝ) * (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 * i ≤ m)
    linarith
  have hchoose_eq : (m.choose k : ℝ) = (m.descFactorial k : ℝ) / (k.factorial : ℝ) := by
    rw [eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)), mul_comm]
    exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose m k).symm
  have hm_split : (m : ℝ) ^ m = (m : ℝ) ^ k * (m : ℝ) ^ (m - k) := by
    rw [← pow_add, Nat.add_sub_of_le (by omega : k ≤ m)]
  have hrew :
      ((m.choose k : ℝ) * ((m - 1 : ℕ) : ℝ) ^ (m - k)) / (m : ℝ) ^ m =
        ((m.descFactorial k : ℝ) / (m : ℝ) ^ k) / (k.factorial : ℝ) *
          (((m - 1 : ℕ) : ℝ) / (m : ℝ)) ^ (m - k) := by
    rw [hchoose_eq, hm_split, div_pow]
    field_simp
  rw [hrew]
  have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hm_ge : (3 : ℝ) * (2 : ℝ) ^ k * (k.factorial : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hprod_ge :
      (1 / 2 : ℝ) ^ k / (k.factorial : ℝ) * (1 / 3 : ℝ) ≤
        ((m.descFactorial k : ℝ) / (m : ℝ) ^ k) / (k.factorial : ℝ) *
          (((m - 1 : ℕ) : ℝ) / (m : ℝ)) ^ (m - k) :=
    mul_le_mul (div_le_div_of_nonneg_right hdesc_ge hfac_pos.le) hpow_ge (by positivity)
      (by positivity)
  have hsimp : (m : ℝ) * ((1 / 2 : ℝ) ^ k / (k.factorial : ℝ) * (1 / 3 : ℝ)) =
      (m : ℝ) / ((3 : ℝ) * (2 : ℝ) ^ k * (k.factorial : ℝ)) := by
    rw [one_div_pow]
    field_simp
  have hge1 : 1 ≤ (m : ℝ) / ((3 : ℝ) * (2 : ℝ) ^ k * (k.factorial : ℝ)) :=
    (one_le_div (by positivity)).mpr hm_ge
  calc (1 : ℝ) ≤ (m : ℝ) * ((1 / 2 : ℝ) ^ k / (k.factorial : ℝ) * (1 / 3 : ℝ)) := by
        rw [hsimp]; exact hge1
    _ ≤ (m : ℝ) * (((m.descFactorial k : ℝ) / (m : ℝ) ^ k) / (k.factorial : ℝ) *
          (((m - 1 : ℕ) : ℝ) / (m : ℝ)) ^ (m - k)) :=
        mul_le_mul_of_nonneg_left hprod_ge hm_pos.le

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
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (NeZero.pos m)
  have h2k : 2 * k ≤ m := by
    have hk_le : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    have hfac : 2 ≤ k.factorial := by
      have := Nat.factorial_le hk
      norm_num [Nat.factorial] at this
      exact this
    nlinarith
  set w : ℝ := (1 / (m : ℝ)) ^ m
  have hw_nn : 0 ≤ w := by positivity
  -- Indicator of `load A j = k` and count `Y A = #{j | load A j = k}`.
  let ind (A : Fin m → Fin m) (j : Fin m) : ℝ :=
    if #(univ.filter fun i : Fin m => A i = j) = k then 1 else 0
  let Y (A : Fin m → Fin m) : ℝ := ∑ j : Fin m, ind A j
  let good : Finset (Fin m → Fin m) := univ.filter fun A => 0 < Y A
  set p : ℝ := ((m.choose k : ℝ) * ((m - 1 : ℕ) : ℝ) ^ (m - k)) / (m : ℝ) ^ m
  set q : ℝ :=
    ((m.choose k : ℝ) * ((m - k).choose k : ℝ) * ((m - 2 : ℕ) : ℝ) ^ (m - 2 * k)) / (m : ℝ) ^ m
  -- Compute `E[Y] = m * p`.
  have hEY : ∑ A : Fin m → Fin m, w * Y A = (m : ℝ) * p := by
    simp only [Y, mul_sum]
    rw [sum_comm]
    have hbin : ∀ j : Fin m, ∑ A : Fin m → Fin m, w * ind A j = p := fun j => by
      simp only [ind, mul_ite, mul_one, mul_zero, ← sum_filter, sum_const, nsmul_eq_mul,
        card_filter_binLoad_eq]
      simp only [w, p, one_div_pow, Nat.cast_mul, Nat.cast_pow]
      ring
    simp only [hbin, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Compute `E[Y^2] = m * p + m * (m - 1) * q`.
  have hEY2 : ∑ A : Fin m → Fin m, w * (Y A) ^ 2 =
      (m : ℝ) * p + (m : ℝ) * ((m : ℝ) - 1) * q := by
    have hsq : ∀ A : Fin m → Fin m,
        w * (Y A) ^ 2 =
          (∑ j : Fin m, w * ind A j) +
          ∑ j₁ : Fin m, ∑ j₂ ∈ univ.erase j₁, w * (ind A j₁ * ind A j₂) := fun A => by
      have h1 : (Y A) ^ 2 = ∑ j₁ : Fin m, ∑ j₂ : Fin m, ind A j₁ * ind A j₂ := by
        simp only [Y, sq, sum_mul_sum]
      rw [h1, mul_sum]
      have hsplit : ∀ j₁ : Fin m,
          w * ∑ j₂ : Fin m, ind A j₁ * ind A j₂ =
            w * ind A j₁ + ∑ j₂ ∈ univ.erase j₁, w * (ind A j₁ * ind A j₂) := fun j₁ => by
        rw [← add_sum_erase _ _ (mem_univ j₁), mul_add, mul_sum]
        congr 1
        simp only [ind]
        split_ifs <;> ring
      simp_rw [hsplit, sum_add_distrib]
    simp_rw [hsq, sum_add_distrib]
    congr 1
    · rw [sum_comm]
      have hbin : ∀ j : Fin m, ∑ A : Fin m → Fin m, w * ind A j = p := fun j => by
        simp only [ind, mul_ite, mul_one, mul_zero, ← sum_filter, sum_const, nsmul_eq_mul,
          card_filter_binLoad_eq]
        simp only [w, p, one_div_pow, Nat.cast_mul, Nat.cast_pow]
        ring
      simp only [hbin, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    · rw [sum_comm]
      have houter : ∀ j₁ : Fin m,
          ∑ A : Fin m → Fin m, ∑ j₂ ∈ univ.erase j₁, w * (ind A j₁ * ind A j₂) =
            ((m : ℝ) - 1) * q := fun j₁ => by
        rw [sum_comm]
        have hpair : ∀ j₂ ∈ univ.erase j₁,
            ∑ A : Fin m → Fin m, w * (ind A j₁ * ind A j₂) = q := fun j₂ hj₂ => by
          have hne : j₁ ≠ j₂ := (ne_of_mem_erase hj₂).symm
          have hind : ∀ A : Fin m → Fin m,
              w * (ind A j₁ * ind A j₂) =
                if #(univ.filter fun i : Fin m => A i = j₁) = k ∧
                   #(univ.filter fun i : Fin m => A i = j₂) = k then w else 0 := fun A => by
            simp only [ind]
            split_ifs <;> simp_all
          simp_rw [hind]
          rw [← sum_filter, sum_const, nsmul_eq_mul, card_filter_binLoad_pair_eq m k hne]
          simp only [w, q, one_div_pow, Nat.cast_mul, Nat.cast_pow]
          ring
        rw [sum_congr rfl hpair, sum_const, card_erase_of_mem (mem_univ j₁), card_univ,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (NeZero.pos m), Nat.cast_one]
      simp only [houter, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  -- Paley–Zygmund via Cauchy–Schwarz: `(E[Y])^2 ≤ E[Y^2] * Pr[Y > 0]`.
  have hY_nn : ∀ A, 0 ≤ Y A := fun A =>
    sum_nonneg fun j _ => by simp only [ind]; split_ifs <;> norm_num
  have hEY_good : ∑ A ∈ good, w * Y A = ∑ A : Fin m → Fin m, w * Y A := by
    refine sum_subset (subset_univ good) fun A _ hA => ?_
    simp only [good, mem_filter, mem_univ, true_and, not_lt] at hA
    have h0 : Y A = 0 := le_antisymm hA (hY_nn A)
    rw [h0, mul_zero]
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
    rw [hlhs, hrhs1, hrhs2] at h1
    exact h1
  have hEY2_mono : ∑ A ∈ good, w * (Y A) ^ 2 ≤ ∑ A : Fin m → Fin m, w * (Y A) ^ 2 :=
    sum_le_univ_sum_of_nonneg fun A => mul_nonneg hw_nn (sq_nonneg _)
  have hPZ : ((m : ℝ) * p) ^ 2 ≤
      (∑ A ∈ good, w) * ((m : ℝ) * p + (m : ℝ) * ((m : ℝ) - 1) * q) := by
    calc ((m : ℝ) * p) ^ 2
        = (∑ A ∈ good, w * Y A) ^ 2 := by rw [hEY_good, hEY]
      _ ≤ (∑ A ∈ good, w) * (∑ A ∈ good, w * (Y A) ^ 2) := hCS
      _ ≤ (∑ A ∈ good, w) * (∑ A : Fin m → Fin m, w * (Y A) ^ 2) :=
          mul_le_mul_of_nonneg_left hEY2_mono (sum_nonneg fun _ _ => hw_nn)
      _ = (∑ A ∈ good, w) * ((m : ℝ) * p + (m : ℝ) * ((m : ℝ) - 1) * q) := by rw [hEY2]
  -- Apply negative correlation `q ≤ p^2` and `1 ≤ m * p`.
  have hq_le : q ≤ p ^ 2 := pair_prob_le_sq_single_prob hk h2k
  have hmp_ge1 : 1 ≤ (m : ℝ) * p := one_le_expected_count_exact hk hm
  have hEY2_le : (m : ℝ) * p + (m : ℝ) * ((m : ℝ) - 1) * q ≤ 2 * ((m : ℝ) * p) ^ 2 := by
    have hm1_nn : 0 ≤ (m : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (m : ℝ) := Nat.one_le_cast.mpr (NeZero.pos m)
      linarith
    have hq_term : (m : ℝ) * ((m : ℝ) - 1) * q ≤ ((m : ℝ) * p) ^ 2 := by
      calc (m : ℝ) * ((m : ℝ) - 1) * q
          ≤ (m : ℝ) * ((m : ℝ) - 1) * p ^ 2 :=
            mul_le_mul_of_nonneg_left hq_le (mul_nonneg hm_pos.le hm1_nn)
        _ ≤ (m : ℝ) * (m : ℝ) * p ^ 2 := by nlinarith [sq_nonneg p]
        _ = ((m : ℝ) * p) ^ 2 := by ring
    nlinarith
  have hprob_good : (1 / 2 : ℝ) ≤ ∑ A ∈ good, w := by
    have hsum_nn : 0 ≤ ∑ A ∈ good, w := sum_nonneg fun _ _ => hw_nn
    have hcomb : ((m : ℝ) * p) ^ 2 ≤ (∑ A ∈ good, w) * (2 * ((m : ℝ) * p) ^ 2) :=
      hPZ.trans (mul_le_mul_of_nonneg_left hEY2_le hsum_nn)
    have hpos_sq : 0 < ((m : ℝ) * p) ^ 2 := by nlinarith
    nlinarith
  -- Every `A ∈ good` has some bin of load `k`, so `k ≤ makespan A`.
  have hgood_sub : ∀ A ∈ good, (k : ℝ) ≤ (unitIdenticalGame m).makespan A := by
    intro A hA
    simp only [good, mem_filter, mem_univ, true_and] at hA
    have hex : ∃ j : Fin m, 0 < ind A j := by
      by_contra hall
      push Not at hall
      have h0 : Y A = 0 := sum_eq_zero fun j _ =>
        le_antisymm (hall j) (by simp only [ind]; split_ifs <;> norm_num)
      linarith
    obtain ⟨j, hj⟩ := hex
    have hload_k : #(univ.filter fun i : Fin m => A i = j) = k := by
      by_contra hne
      simp only [ind, ite_eq_right hne] at hj
      exact lt_irrefl 0 hj
    calc (k : ℝ) = (unitIdenticalGame m).load A j := by
          rw [load_unitIdenticalGame_eq_card, hload_k]
      _ ≤ (unitIdenticalGame m).makespan A := (unitIdenticalGame m).load_le_makespan A j
  calc (1 / 2 : ℝ) ≤ ∑ A ∈ good, w := hprob_good
    _ = ∑ A ∈ good,
          if (k : ℝ) ≤ (unitIdenticalGame m).makespan A then
            productWeight (uniformMixedProfile m) A
          else 0 := by
        refine sum_congr rfl fun A hA => ?_
        rw [ite_eq_left (hgood_sub A hA), productWeight_uniformMixedProfile]
    _ ≤ ∑ A : Fin m → Fin m,
          if (k : ℝ) ≤ (unitIdenticalGame m).makespan A then
            productWeight (uniformMixedProfile m) A
          else 0 := by
        refine sum_le_univ_sum_of_nonneg fun A => ?_
        split_ifs
        · rw [productWeight_uniformMixedProfile]; exact hw_nn
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

private theorem one_le_expectedMakespan_unitIdenticalGame (m : ℕ) [NeZero m] :
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
      have hfac : 2 ^ (k - 1) ≤ k.factorial := by
        have h := Nat.factorial_mul_pow_le_factorial (m := 1) (n := k - 1)
        have hadd : 1 + (k - 1) = k := by omega
        simpa only [Nat.factorial_one, one_mul, hadd] using h
      have h3le : 3 ^ k ≤ m := by
        have h4 : 4 ^ k ≤ 2 * (2 ^ k * k.factorial) := by
          have hpow : 4 ^ k = 2 * 2 ^ k * 2 ^ (k - 1) := by
            have h2k : 2 * k = 1 + k + (k - 1) := by omega
            rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, h2k, pow_add, pow_add, pow_one]
          rw [hpow, mul_assoc]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hfac)
        have h34 : 3 ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) k
        have hfk' : 3 * (2 ^ k * k.factorial) ≤ m := by
          dsimp only [f] at hfk_le
          linarith
        omega
      have h3le_real : (3 : ℝ) ^ k ≤ (m : ℝ) := by exact_mod_cast h3le
      exact hexpk.trans_le h3le_real
    have hm_pos_real : (0 : ℝ) < (m : ℝ) := (Real.exp_pos _).trans hexp_lt_m
    have hk_lt_logm : (k : ℝ) < Real.log (m : ℝ) := by
      rw [← Real.log_exp (k : ℝ)]
      exact Real.log_lt_log (Real.exp_pos _) hexp_lt_m
    have hlogm_gt1 : 1 < Real.log (m : ℝ) := by linarith
    have hloglogm_pos : 0 < Real.log (Real.log (m : ℝ)) := Real.log_pos hlogm_gt1
    have hlogk_lt : Real.log (k : ℝ) < Real.log (Real.log (m : ℝ)) :=
      Real.log_lt_log (by linarith) hk_lt_logm
    have hlog2_le_logk : Real.log 2 ≤ Real.log (k : ℝ) :=
      Real.log_le_log (by norm_num) hk_real
    have hlogk_pos : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
    have hlog3_le : Real.log 3 ≤ (k : ℝ) * Real.log (k : ℝ) := by
      have h3le : (3 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
      calc Real.log 3 ≤ Real.log ((k : ℝ) ^ 2) := Real.log_le_log (by norm_num) h3le
        _ = 2 * Real.log (k : ℝ) := by rw [Real.log_pow]; norm_num
        _ ≤ (k : ℝ) * Real.log (k : ℝ) := by nlinarith
    have hlog_k1 : Real.log ((k + 1 : ℕ) : ℝ) ≤ 2 * Real.log (k : ℝ) := by
      have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 := by push_cast; nlinarith
      calc Real.log ((k + 1 : ℕ) : ℝ)
          ≤ Real.log ((k : ℝ) ^ 2) := Real.log_le_log (by positivity) hk1_le
        _ = 2 * Real.log (k : ℝ) := by rw [Real.log_pow]; norm_num
    have hm_le_nat : m ≤ 3 * 2 ^ (k + 1) * (k + 1) ^ (k + 1) :=
      hm_lt_next.le.trans (Nat.mul_le_mul_left _ (Nat.factorial_le_pow (k + 1)))
    have hm_le : (m : ℝ) ≤ 3 * (2 : ℝ) ^ (k + 1) * ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by
      exact_mod_cast hm_le_nat
    have hlogm_le : Real.log (m : ℝ) ≤ 6 * (k : ℝ) * Real.log (Real.log (m : ℝ)) := by
      calc Real.log (m : ℝ)
          ≤ Real.log (3 * (2 : ℝ) ^ (k + 1) * ((k + 1 : ℕ) : ℝ) ^ (k + 1)) :=
            Real.log_le_log hm_pos_real hm_le
        _ = Real.log 3 + ((k + 1 : ℕ) : ℝ) * Real.log 2 +
              ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) := by
            rw [Real.log_mul (by positivity) (by positivity),
              Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
        _ ≤ (k : ℝ) * Real.log (k : ℝ) +
              ((3 / 2 : ℝ) * (k : ℝ)) * Real.log (k : ℝ) +
              ((3 / 2 : ℝ) * (k : ℝ)) * (2 * Real.log (k : ℝ)) := by
            push_cast
            have h1 : ((k : ℝ) + 1) * Real.log 2 ≤ ((3 / 2 : ℝ) * (k : ℝ)) * Real.log (k : ℝ) := by
              calc ((k : ℝ) + 1) * Real.log 2
                  ≤ ((k : ℝ) + 1) * Real.log (k : ℝ) :=
                    mul_le_mul_of_nonneg_left hlog2_le_logk (by linarith)
                _ ≤ ((3 / 2 : ℝ) * (k : ℝ)) * Real.log (k : ℝ) :=
                    mul_le_mul_of_nonneg_right (by linarith) hlogk_pos.le
            have h2 : ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1) ≤
                ((3 / 2 : ℝ) * (k : ℝ)) * (2 * Real.log (k : ℝ)) := by
              have hlog_k1' : Real.log ((k : ℝ) + 1) ≤ 2 * Real.log (k : ℝ) := by
                simpa only [Nat.cast_add, Nat.cast_one] using hlog_k1
              calc ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)
                  ≤ ((k : ℝ) + 1) * (2 * Real.log (k : ℝ)) :=
                    mul_le_mul_of_nonneg_left hlog_k1' (by linarith)
                _ ≤ ((3 / 2 : ℝ) * (k : ℝ)) * (2 * Real.log (k : ℝ)) :=
                    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            linarith
        _ ≤ 6 * (k : ℝ) * Real.log (k : ℝ) := by nlinarith
        _ ≤ 6 * (k : ℝ) * Real.log (Real.log (m : ℝ)) := by nlinarith
    have hdiv : Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)) ≤ 6 * (k : ℝ) :=
      (div_le_iff₀ hloglogm_pos).mpr hlogm_le
    have hk_bound := ballsIntoBins_expectedMakespan_ge_half_of_factorial (m := m) hk2 hfk_le
    have hratio_pos : 0 < Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)) := by positivity
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
