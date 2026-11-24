/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Matroid.Intersection.Konig
import CslibFrontier.Algorithms.Lean.Matroid.Union
import Mathlib.Tactic.FinCases

/-!
# Checked witness tests for Edmonds' matroid union, partitioning, and base-packing theorems

Covers:
1. Rank-1 uniform matroid `U_{1,3}` on `Fin 3`: `matroidUnion` of two copies has rank `2` on
   `univ`, `{0, 1}` is union-independent, `univ` cannot be `2`-partitioned, and `U_{1,3}` admits
   `3` disjoint bases but not `4`.
2. Non-trivial proper bottleneck subset `∅ ⊂ T ⊂ S`: parallel-class matroid `M₄` of rank `2` on
   `Fin 4` where `{0, 1, 2}` has rank `1`; `|S| = 4 ≤ 2 * rk(S)` holds at `T = S`, yet `2`-partition
   fails via `T = {0, 1, 2}` and `eRk(S) = 3 < 4`.
3. Boundary case `ι = Empty` (ground set `∅`, partition only for `S = ∅`, `0` bases trivially
   exist) and infinite ground type `α = ℕ`.
-/

namespace CslibFrontierTests.MatroidUnion

open Cslib.Algorithms.Lean.Matroid Finset Set

/-! ## 1. Rank-1 uniform matroid on `Fin 3` -/

private def u13 : Matroid (Fin 3) :=
  unitPartitionMatroid (fun _ : Fin 3 => ())

private theorem u13_indep_iff {I : Set (Fin 3)} :
    u13.Indep I ↔ I.Subsingleton := by
  simp [u13, unitPartitionMatroid_indep_iff, Set.InjOn, Set.Subsingleton]

private theorem u13_eRk_of_nonempty {X : Set (Fin 3)} (hX : X.Nonempty) : u13.eRk X = 1 := by
  rw [u13, unitPartitionMatroid_eRk]
  have himg : (fun _ : Fin 3 => ()) '' X = {()} := by
    ext ⟨⟩
    obtain ⟨x, hx⟩ := hX
    simp only [Set.mem_image, Set.mem_singleton_iff]
    exact ⟨fun _ => trivial, fun _ => ⟨x, hx, trivial⟩⟩
  rw [himg, Set.encard_singleton]

private theorem u13_eRank : u13.eRank = 1 := by
  rw [Matroid.eRank_def]
  have hE : u13.E = Set.univ := rfl
  rw [hE, u13_eRk_of_nonempty Set.univ_nonempty]

example : (matroidUnion (fun _ : Fin 2 => u13)).Indep ({0, 1} : Finset (Fin 3)) := by
  rw [matroidUnion_indep_iff_of_finite _ (Finset.finite_toSet _)]
  refine ⟨fun i => if i = 0 then {0} else {1}, fun i => ?_, ?_⟩
  · fin_cases i <;> simp [u13_indep_iff]
  · ext x
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, Set.mem_iUnion,
      Fin.exists_fin_two]
    fin_cases x <;> simp

example : (matroidUnion (fun _ : Fin 2 => u13)).eRk (Set.univ : Set (Fin 3)) = 2 := by
  rw [matroidUnion_eRk_eq_iInf _ Set.finite_univ]
  refine le_antisymm ?_ ?_
  · calc ⨅ (T : Set (Fin 3)) (_ : T ⊆ Set.univ),
          ((Set.univ \ T).encard + ∑ _i : Fin 2, u13.eRk T)
        ≤ ((Set.univ : Set (Fin 3)) \ Set.univ).encard + ∑ _i : Fin 2, u13.eRk Set.univ :=
            iInf₂_le (f := fun T (_ : T ⊆ Set.univ) =>
              (Set.univ \ T).encard + ∑ _i : Fin 2, u13.eRk T) Set.univ Set.Subset.rfl
      _ = 2 := by
          rw [Set.sdiff_self, Set.encard_empty, zero_add, u13_eRk_of_nonempty Set.univ_nonempty,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
          rfl
  · refine le_iInf₂ fun T _ => ?_
    by_cases hT : T.Nonempty
    · rw [u13_eRk_of_nonempty hT]
      simp [Finset.sum_const, nsmul_eq_mul]
    · have hTe : T = ∅ := Set.not_nonempty_iff_eq_empty.1 hT
      subst hTe
      rw [Set.sdiff_empty, Matroid.eRk_empty, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fin, mul_zero, add_zero, ← Finset.coe_univ, Set.encard_coe_eq_coe_finsetCard,
        Finset.card_fin]
      exact_mod_cast (by decide : 2 ≤ 3)

example : ¬ ∃ P : Fin 2 → Finset (Fin 3), (∀ i, u13.Indep (P i : Set (Fin 3))) ∧
    Pairwise (Function.onFun Disjoint P) ∧ Finset.univ.biUnion P = Finset.univ := by
  rw [exists_partition_indep_const_iff]
  push Not
  refine ⟨Finset.univ, Finset.Subset.rfl, ?_⟩
  have hne : ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).Nonempty := ⟨0, Finset.mem_univ _⟩
  rw [u13_eRk_of_nonempty hne, Finset.card_fin, mul_one]
  exact_mod_cast (by decide : 2 < 3)

-- `u13` admits 3 pairwise disjoint bases, but not 4.
example : ∃ B : Fin 3 → Set (Fin 3),
    (∀ i, u13.IsBase (B i)) ∧ Pairwise (Function.onFun Disjoint B) := by
  rw [exists_disjoint_isBase_iff _ Set.finite_univ 3]
  intro T _
  rw [u13_eRank]
  by_cases hT : T.Nonempty
  · rw [u13_eRk_of_nonempty hT]
    simp
  · rw [Set.not_nonempty_iff_eq_empty.1 hT, Set.sdiff_empty, Matroid.eRk_empty,
      show u13.E = Set.univ from rfl, ← Finset.coe_univ, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_fin]
    exact_mod_cast (by decide : 3 * 1 ≤ 3 + 3 * 0)

example : ¬ ∃ B : Fin 4 → Set (Fin 3),
    (∀ i, u13.IsBase (B i)) ∧ Pairwise (Function.onFun Disjoint B) := by
  rw [exists_disjoint_isBase_iff _ Set.finite_univ 4]
  push Not
  refine ⟨∅, Set.empty_subset _, ?_⟩
  rw [u13_eRank, Matroid.eRk_empty, Set.sdiff_empty, show u13.E = Set.univ from rfl,
    ← Finset.coe_univ, Set.encard_coe_eq_coe_finsetCard, Finset.card_fin]
  exact_mod_cast (by decide : 3 + 4 * 0 < 4 * 1)

/-! ## 2. Proper bottleneck subset witness on `Fin 4` -/

private def bottleneckKey (v : Fin 4) : Fin 2 :=
  if v.val < 3 then 0 else 1

private def m4 : Matroid (Fin 4) :=
  unitPartitionMatroid bottleneckKey

example : (matroidUnion (fun _ : Fin 2 => m4)).eRk (Set.univ : Set (Fin 4)) = 3 := by
  rw [matroidUnion_eRk_eq_iInf _ Set.finite_univ]
  refine le_antisymm ?_ ?_
  · let T : Set (Fin 4) := ({0, 1, 2} : Finset (Fin 4))
    have hT_rk : m4.eRk T = 1 := by
      rw [m4, unitPartitionMatroid_eRk]
      have himg : bottleneckKey '' T = {0} := by
        ext k
        simp only [T, Finset.coe_insert, Finset.coe_singleton, Set.mem_image,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨v, rfl | rfl | rfl, rfl⟩ <;> decide
        · rintro rfl
          exact ⟨0, .inl rfl, rfl⟩
      rw [himg, Set.encard_singleton]
    have hdiff : (Set.univ \ T).encard = 1 := by
      have : Set.univ \ T = ({3} : Set (Fin 4)) := by
        ext v
        simp only [T, Set.mem_sdiff, Set.mem_univ, Finset.mem_coe, Finset.mem_insert,
          Finset.mem_singleton, true_and, Set.mem_singleton_iff]
        fin_cases v <;> decide
      rw [this, Set.encard_singleton]
    refine (iInf₂_le T (Set.subset_univ _)).trans_eq ?_
    rw [hdiff, hT_rk, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    exact_mod_cast (by decide : 1 + 2 * 1 = 3)
  · refine le_iInf₂ fun U _ => ?_
    rw [m4, unitPartitionMatroid_eRk]
    have hUfin : U.Finite := Set.toFinite U
    let Uf : Finset (Fin 4) := hUfin.toFinset
    have hUf : (Uf : Set (Fin 4)) = U := hUfin.coe_toFinset
    have hcard : (Set.univ \ U).encard = ((Finset.univ \ Uf).card : ℕ∞) := by
      rw [← hUf, ← Finset.coe_univ, ← Finset.coe_sdiff, Set.encard_coe_eq_coe_finsetCard]
    have himg : (bottleneckKey '' U).encard = ((Uf.image bottleneckKey).card : ℕ∞) := by
      rw [← hUf, ← Finset.coe_image, Set.encard_coe_eq_coe_finsetCard]
    rw [hcard, himg]
    have hnat : 3 ≤ (Finset.univ \ Uf).card + 2 * (Uf.image bottleneckKey).card := by
      by_cases h3 : (3 : Fin 4) ∈ Uf
      · by_cases h012 : (0 : Fin 4) ∈ Uf ∨ 1 ∈ Uf ∨ 2 ∈ Uf
        · have himg2 : 2 ≤ (Uf.image bottleneckKey).card := by
            rcases h012 with h0 | h1 | h2
            · exact Finset.one_lt_card.2 ⟨0, Finset.mem_image.2 ⟨0, h0, rfl⟩,
                1, Finset.mem_image.2 ⟨3, h3, rfl⟩, by decide⟩
            · exact Finset.one_lt_card.2 ⟨0, Finset.mem_image.2 ⟨1, h1, rfl⟩,
                1, Finset.mem_image.2 ⟨3, h3, rfl⟩, by decide⟩
            · exact Finset.one_lt_card.2 ⟨0, Finset.mem_image.2 ⟨2, h2, rfl⟩,
                1, Finset.mem_image.2 ⟨3, h3, rfl⟩, by decide⟩
          omega
        · have hsub : Finset.univ \ Uf = {0, 1, 2} := by
            ext v
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton]
            fin_cases v <;> tauto
          have hcard3 : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
          rw [hsub, hcard3]
          omega
      · by_cases hne : Uf.Nonempty
        · have h1 : 1 ≤ (Uf.image bottleneckKey).card :=
            Finset.card_pos.2 (hne.image bottleneckKey)
          have hs3 : (3 : Fin 4) ∈ Finset.univ \ Uf := Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h3⟩
          have hs_pos : 1 ≤ (Finset.univ \ Uf).card := Finset.card_pos.2 ⟨3, hs3⟩
          omega
        · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sdiff_empty]
          decide
    have hle : (3 : ℕ∞) ≤ ((Finset.univ \ Uf).card : ℕ∞) +
        ((2 * (Uf.image bottleneckKey).card : ℕ) : ℕ∞) := by
      exact_mod_cast hnat
    simpa [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, Nat.cast_mul] using hle

/-! ## 3. Boundary cases: empty family and infinite ground type `ℕ` -/

example : (matroidUnion (fun i : Empty => i.elim : Empty → Matroid ℕ)).E = ∅ := by
  simp

example :
    (∃ P : Empty → Finset ℕ, (∀ i : Empty, (i.elim : Matroid ℕ).Indep (P i : Set ℕ)) ∧
      Pairwise (Function.onFun Disjoint P) ∧ Finset.univ.biUnion P = ({0} : Finset ℕ)) →
    False := by
  rw [exists_partition_indep_iff]
  intro h
  have := h {0} Finset.Subset.rfl
  simp at this

example :
    ∃ P : Fin 2 → Finset ℕ, (∀ i, (unitPartitionMatroid (fun n : ℕ => n / 2)).Indep (P i : Set ℕ)) ∧
      Pairwise (Function.onFun Disjoint P) ∧ Finset.univ.biUnion P = ({0, 1, 2, 3} : Finset ℕ) := by
  rw [exists_partition_indep_const_iff]
  intro T _
  rw [unitPartitionMatroid_eRk, ← Finset.coe_image, Set.encard_coe_eq_coe_finsetCard]
  have hle : T.card ≤ 2 * (T.image (fun x => x / 2)).card := by
    have hfib : T ⊆ (T.image (fun x => x / 2)).biUnion fun q => {2 * q, 2 * q + 1} := by
      intro x hx
      refine Finset.mem_biUnion.2 ⟨x / 2, Finset.mem_image_of_mem _ hx, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    calc T.card
        ≤ ((T.image (fun x => x / 2)).biUnion fun q => ({2 * q, 2 * q + 1} : Finset ℕ)).card :=
          Finset.card_le_card hfib
      _ ≤ ∑ _q ∈ T.image (fun x => x / 2), 2 := by
          refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun q _ => ?_)
          exact Finset.card_le_two
      _ = 2 * (T.image (fun x => x / 2)).card := by simp [Finset.sum_const, mul_comm]
  exact_mod_cast hle

end CslibFrontierTests.MatroidUnion
