/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.CellProbe.OuterGame
import CslibFrontier.Foundations.Data.Finset.OrderEmb
import CslibFrontier.Foundations.Data.List.Counting

/-!
# Candidate Segment Replay and State Multiplicity Fibers

Helper definitions and replay lemmas for Section 8.1 of [LiLiangYuZhou2023]: the decoded-state
memory fiber `stateFiber`, cardinality helpers for `activeKeys`, `insertedSet`, and `deletedSet`,
and validity/replay equivalence for `modeCandidateOps`.

## Main definitions

* `Cslib.DataStructure.Dictionary.CellProbe.stateFiber`: finset of memories whose decoded
  dictionary equals `st` at step `stepIdx`.

## Main results

* `Cslib.DataStructure.Dictionary.CellProbe.sum_card_stateFiber_le`: upper bound on fiber counts.
* `Cslib.DataStructure.Dictionary.CellProbe.run_take_modeOps_eq_ite`: dictionary state after taking
  the segment prefix of `modeOps`.
* `Cslib.DataStructure.Dictionary.CellProbe.validHistory_and_run_modeCandidateOps`: exact replay of
  candidate segment operations `modeCandidateOps`.
-/

public section

open scoped BigOperators ENNReal

namespace Cslib.DataStructure.Dictionary.CellProbe

open Cslib.CellProbe Cslib.DataStructure Cslib.DataStructure.Dictionary
open Finset (orderSubset orderSubset_apply image_orderSubset embSetPermEquiv)

/-! #### Candidate segment replay and dictionary-state multiplicity fibers -/

open Classical in
/-- Finset of memories decoding to dictionary state `st` at step `stepIdx`. -/
@[expose] noncomputable def stateFiber {U cells w : ℕ}
    (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w) (stepIdx : ℕ)
    (st : Dictionary.State U) : Finset (Mem cells w) :=
  Finset.univ.filter fun C => decodeDict D_det stepIdx C = st

open Classical in
theorem sum_card_stateFiber_le {U V n cells w : ℕ}
    (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w) (stepIdx : ℕ) :
    (∑ p : SizedDict U V n, (stateFiber D_det stepIdx p.val).card) ≤
      2 ^ (cells * w) := by
  have hdisj : ((Finset.univ : Finset (SizedDict U V n)) :
      Set (SizedDict U V n)).PairwiseDisjoint
      (fun p => stateFiber D_det stepIdx p.val) := by
    intro p₁ _ p₂ _ hne
    refine Finset.disjoint_left.mpr fun C h₁ h₂ => hne (Subtype.ext ?_)
    dsimp only [stateFiber] at h₁ h₂
    rw [Finset.mem_filter] at h₁ h₂
    exact h₁.2.symm.trans h₂.2
  calc (∑ p : SizedDict U V n, (stateFiber D_det stepIdx p.val).card)
      = ((Finset.univ : Finset (SizedDict U V n)).biUnion
          (fun p => stateFiber D_det stepIdx p.val)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset (Mem cells w)).card := Finset.card_le_univ _
    _ = 2 ^ (cells * w) := by
        simp only [Finset.card_univ, Mem, Fintype.card_pi, Fintype.card_fin,
          Finset.prod_const]
        rw [← pow_mul, mul_comm]

private def modeCandUnit (withQueries : Bool) {U V m : ℕ}
    (d b : Fin m → Fin U) (kv : Fin U → Fin V) (r : Fin m) : List (Dynamic.Op U) :=
  if withQueries then
    [.query (d r), .delete (d r), .insert (b r) (kv (b r)).val]
  else
    [.delete (d r), .insert (b r) (kv (b r)).val]

private def modeCandPrefix (withQueries : Bool) {U V m : ℕ}
    (d b : Fin m → Fin U) (kv : Fin U → Fin V) (k : ℕ) : List (Dynamic.Op U) :=
  ((List.finRange m).take k).flatMap (modeCandUnit withQueries d b kv)

private theorem modeCandPrefix_full (withQueries : Bool) {U V m : ℕ}
    (d b : Fin m → Fin U) (kv : Fin U → Fin V) :
    modeCandPrefix withQueries d b kv m =
      if withQueries then candidateQueryDeleteInsertOps d b kv
      else candidateDeleteInsertOps d b kv := by
  have htk : (List.finRange m).take m = List.finRange m :=
    List.take_of_length_le (by simp only [List.length_finRange, le_rfl])
  cases withQueries <;> (dsimp only [modeCandPrefix, ↓reduceIte, Bool.false_eq_true]; rw [htk]; rfl)

private theorem modeCandPrefix_succ (withQueries : Bool) {U V m : ℕ}
    (d b : Fin m → Fin U) (kv : Fin U → Fin V) {k : ℕ} (hk : k < m) :
    modeCandPrefix withQueries d b kv (k + 1) =
      modeCandPrefix withQueries d b kv k ++ modeCandUnit withQueries d b kv ⟨k, hk⟩ := by
  dsimp only [modeCandPrefix]
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp only [List.length_finRange]; exact hk),
    Option.toList_some, List.flatMap_append, List.flatMap_singleton, List.getElem_finRange]
  rfl

open Classical in
theorem dom_ite_eq {U V : ℕ} (S : Finset (Fin U)) (kv : Fin U → Fin V) :
    Dictionary.dom (fun u => if u ∈ S then some (kv u).val else none) = S := by
  ext u; rw [Dictionary.mem_dom_iff]
  by_cases hu : u ∈ S <;>
    simp only [hu, ↓reduceIte, Option.some.injEq, exists_eq', reduceCtorEq, exists_false]

theorem card_activeKeys {U V n t₀ : ℕ} (s : HardKeyValSeed U V n) (ht₀ : t₀ ≤ n) :
    (s.activeKeys t₀ ht₀).card = n := by
  simp only [HardKeyValSeed.activeKeys, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem card_insertedSet {U V n t₀ r : ℕ} (s : HardKeyValSeed U V n) (hr : t₀ + r ≤ n) :
    (s.insertedSet t₀ r hr).card = r :=
  (Finset.card_image_of_injective _ (segInsertedKeys s.keys t₀ r hr).injective).trans
    (by simp only [Finset.card_univ, Fintype.card_fin])

theorem card_deletedSet {U V n t₀ m : ℕ} (s : HardKeyValSeed U V n) (ht₀ : t₀ + m ≤ n) :
    (Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)).card = m :=
  (Finset.card_image_of_injective _ (segDeletedKeys s.keys s.delPerm t₀ m ht₀).injective).trans
    (by simp only [Finset.card_univ, Fintype.card_fin])

private theorem segDeletedKeys_mem_activeKeys {U V n t₀ m : ℕ} (s : HardKeyValSeed U V n)
    (ht₀ : t₀ + m ≤ n) (r : Fin m) :
    segDeletedKeys s.keys s.delPerm t₀ m ht₀ r ∈
      s.activeKeys t₀ (Nat.le_of_add_right_le ht₀) := by
  refine Finset.mem_map.mpr ⟨⟨r.val, by omega⟩, Finset.mem_univ _, ?_⟩
  rw [windowEmb_apply]
  simp only [segDeletedKeys_apply, HardKeyValSeed.permKeyEmb,
    Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  rw [liftDelPerm_apply_lt s.delPerm (by omega)]

theorem segDeletedKeys_subset_activeKeys {U V n t₀ m : ℕ} (s : HardKeyValSeed U V n)
    (ht₀ : t₀ + m ≤ n) :
    Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀) ⊆
      s.activeKeys t₀ (Nat.le_of_add_right_le ht₀) := fun _ hu => by
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hu
  exact segDeletedKeys_mem_activeKeys s ht₀ r

theorem run_take_modeOps_eq_ite (withQueries : Bool) {U V n t₀ : ℕ}
    (s : HardKeyValSeed U V n) (ht₀ : t₀ ≤ n) :
    ((Dynamic.spec U V n).run (Dictionary.empty U)
      ((s.modeOps withQueries).take (n + modeStride withQueries * t₀))).1 =
      fun u => if u ∈ s.activeKeys t₀ ht₀ then some (s.kv u).val else none := by
  rw [s.run_take_modeOps_fst withQueries ht₀, windowDict_coe]
  funext u
  by_cases hu : u ∈ s.activeKeys t₀ ht₀
  · simp only [hu, ↓reduceIte]
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hu
    rw [dictOfEmb_apply_self, windowVals_apply, windowEmb_apply]
  · simp only [hu, ↓reduceIte]
    exact dictOfEmb_apply_eq_none _ _ fun k heq =>
      hu (Finset.mem_map.mpr ⟨k, Finset.mem_univ k, heq⟩)

theorem validHistory_and_run_modeCandidateOps (withQueries : Bool) {U V n t₀ m : ℕ}
    (s : HardKeyValSeed U V n) (ht₀ : t₀ + m ≤ n) {B : Finset (Fin U)} (hB : B.card = m)
    (hdisj : Disjoint B (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀))) :
    let stride := modeStride withQueries
    let pref_bef := (s.modeOps withQueries).take (n + stride * t₀)
    let ops_B := s.modeCandidateOps withQueries t₀ m ht₀ B hB
    let D_set := Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)
    (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) (pref_bef ++ ops_B) ∧
      (pref_bef ++ ops_B).length = n + stride * (t₀ + m) ∧
      ((Dynamic.spec U V n).run (Dictionary.empty U) (pref_bef ++ ops_B)).1 =
        fun u => if u ∈ (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀) \ D_set) ∪ B
          then some (s.kv u).val else none := by
  let stride := modeStride withQueries
  let ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
  let pref_bef := (s.modeOps withQueries).take (n + stride * t₀)
  let d := segDeletedKeys s.keys s.delPerm t₀ m ht₀
  let π := (embSetPermEquiv (Fin U) m (segInsertedKeys s.keys t₀ m ht₀)).2
  let b := orderSubset B hB π
  let K := s.activeKeys t₀ ht₀_n
  have hpref_vh := s.validHistory_take_modeOps withQueries ht₀_n
  have hpref_len := s.length_take_modeOps withQueries ht₀_n
  have hpref_st := run_take_modeOps_eq_ite withQueries s ht₀_n
  have hd_mem_K (r : Fin m) : d r ∈ K := segDeletedKeys_mem_activeKeys s ht₀ r
  have hb_mem_B (r : Fin m) : b r ∈ B := by
    dsimp only [b]; rw [orderSubset_apply]; exact Finset.orderEmbOfFin_mem B hB (π r)
  have hloop : ∀ k : ℕ, (hk : k ≤ m) →
      let D_k := (Finset.univ.filter fun r : Fin m => r.val < k).image d
      let B_k := (Finset.univ.filter fun r : Fin m => r.val < k).image b
      (Dynamic.spec U V n).ValidHistory (Dictionary.empty U)
        (pref_bef ++ modeCandPrefix withQueries d b s.kv k) ∧
      ((Dynamic.spec U V n).run (Dictionary.empty U)
        (pref_bef ++ modeCandPrefix withQueries d b s.kv k)).1 =
        (fun u => if u ∈ (K \ D_k) ∪ B_k then some (s.kv u).val else none) := by
    intro k hk
    induction k with
    | zero =>
      have hf : ∀ g : Fin m → Fin U,
          (Finset.univ.filter fun r : Fin m => r.val < 0).image g = ∅ := fun _ => by
        simp only [Nat.not_lt_zero, Finset.filter_false, Finset.image_empty]
      simp only [modeCandPrefix, List.take_zero, List.flatMap_nil, List.append_nil,
        hf d, hf b, Finset.sdiff_empty, Finset.union_empty]
      exact ⟨hpref_vh, hpref_st⟩
    | succ k ih =>
      have hk_lt : k < m := hk
      obtain ⟨hvh_k, hst_k⟩ := ih (Nat.le_of_succ_le hk)
      set D_k := (Finset.univ.filter fun r : Fin m => r.val < k).image d
      set B_k := (Finset.univ.filter fun r : Fin m => r.val < k).image b
      set s_k := ((Dynamic.spec U V n).run (Dictionary.empty U)
        (pref_bef ++ modeCandPrefix withQueries d b s.kv k)).1
      let r₀ : Fin m := ⟨k, hk_lt⟩
      have hdr_not_Dk : d r₀ ∉ D_k := by
        simp only [D_k, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        rintro ⟨r', hr', heq⟩
        have := congrArg Fin.val (d.injective heq); dsimp only [r₀] at this; omega
      have hdr_in : d r₀ ∈ (K \ D_k) ∪ B_k :=
        Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hd_mem_K r₀, hdr_not_Dk⟩)
      have hdr_some : (s_k (d r₀)).isSome := by
        rw [hst_k]; simp only [hdr_in, ↓reduceIte, Option.isSome_some]
      have hflt_lt : (Finset.univ.filter fun r : Fin m => r.val < k) = Finset.Iio r₀ := by
        simpa only [Fin.lt_def] using
          (Finset.filter_gt_eq_Iio : Finset.univ.filter (· < r₀) = Finset.Iio r₀)
      have hflt_le : (Finset.univ.filter fun r : Fin m => r.val < k + 1) = Finset.Iic r₀ := by
        simpa only [Nat.lt_succ_iff, Fin.le_def] using
          (Finset.filter_ge_eq_Iic : Finset.univ.filter (· ≤ r₀) = Finset.Iic r₀)
      have hcard_D : D_k.card = k := by
        rw [Finset.card_image_of_injective _ d.injective, hflt_lt, Fin.card_Iio]
      have hcard_B : B_k.card = k := by
        rw [Finset.card_image_of_injective _ b.injective, hflt_lt, Fin.card_Iio]
      have hdom_sk : Dictionary.dom s_k = (K \ D_k) ∪ B_k := by
        rw [show s_k = _ from hst_k]; exact dom_ite_eq _ _
      have hcard_sk : (Dictionary.dom s_k).card = n := by
        rw [hdom_sk, Finset.card_union_of_disjoint, Finset.card_sdiff]
        · have hsubD : D_k ⊆ K := fun _ hx => by
            obtain ⟨r', _, rfl⟩ := Finset.mem_image.mp hx; exact hd_mem_K r'
          rw [Finset.inter_eq_left.mpr hsubD, card_activeKeys s ht₀_n, hcard_D, hcard_B]; omega
        · refine Finset.disjoint_left.mpr fun x hxK hxB => ?_
          obtain ⟨r', _, rfl⟩ := Finset.mem_image.mp hxB
          exact Finset.disjoint_left.mp hdisj (hb_mem_B r') (Finset.mem_sdiff.mp hxK).1
      have hcard_del : (Dictionary.dom (Function.update s_k (d r₀) none)).card < n := by
        rw [Dynamic.card_dom_delete_eq_of_isSome hdr_some, hcard_sk]; omega
      have hupd_st : Function.update (Function.update s_k (d r₀) none) (b r₀)
          (some (s.kv (b r₀)).val) =
          (fun u => if u ∈ (K \ (Finset.univ.filter fun r : Fin m => r.val < k + 1).image d) ∪
            (Finset.univ.filter fun r : Fin m => r.val < k + 1).image b
            then some (s.kv u).val else none) := by
        funext u
        have himg_succ (f : Fin m ↪ Fin U) :
            (Finset.univ.filter fun r : Fin m => r.val < k + 1).image f =
              insert (f r₀) ((Finset.univ.filter fun r : Fin m => r.val < k).image f) := by
          rw [hflt_le, hflt_lt, ← Finset.insert_Iio, Finset.image_insert]
        rw [himg_succ d, himg_succ b]
        by_cases hub : u = b r₀
        · subst hub
          rw [Function.update_self,
            ite_eq_left (Finset.mem_union_right _ (Finset.mem_insert_self _ _))]
        · rw [Function.update_of_ne hub]
          by_cases hud : u = d r₀
          · subst hud
            have hnotB : d r₀ ∉ B_k := fun hxB => by
              obtain ⟨r', _, heq⟩ := Finset.mem_image.mp hxB
              exact Finset.disjoint_left.mp hdisj (heq ▸ hb_mem_B r') (hd_mem_K r₀)
            rw [Function.update_self, ite_eq_right]
            simpa only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, true_or,
              not_true_eq_false, and_false, hub, false_or] using hnotB
          · rw [Function.update_of_ne hud, show s_k = _ from hst_k]
            dsimp only
            by_cases hu : u ∈ (K \ D_k) ∪ B_k
            · rw [ite_eq_left hu, ite_eq_left]
              simpa only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, hud, false_or,
                hub] using hu
            · rw [ite_eq_right hu, ite_eq_right]
              simpa only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, hud, false_or,
                hub] using hu
      rw [modeCandPrefix_succ withQueries d b s.kv hk_lt, ← List.append_assoc,
        StateTransitionSpec.validHistory_append,
        (Dynamic.spec U V n).run_append (Dictionary.empty U)
          (pref_bef ++ modeCandPrefix withQueries d b s.kv k)]
      dsimp only
      cases withQueries
      · simp only [modeCandUnit, Bool.false_eq_true, ↓reduceIte,
          StateTransitionSpec.validHistory_cons, StateTransitionSpec.validHistory_nil,
          Dynamic.spec]
        exact ⟨⟨hvh_k, trivial, ⟨Or.inl hcard_del, (s.kv (b r₀)).isLt⟩, trivial⟩, hupd_st⟩
      · simp only [modeCandUnit, ↓reduceIte,
          StateTransitionSpec.validHistory_cons, StateTransitionSpec.validHistory_nil,
          Dynamic.spec]
        exact ⟨⟨hvh_k, trivial, trivial, ⟨Or.inl hcard_del, (s.kv (b r₀)).isLt⟩, trivial⟩,
          hupd_st⟩
  obtain ⟨hvh_m, hst_m⟩ := hloop m le_rfl
  have hfull : modeCandPrefix withQueries d b s.kv m =
      s.modeCandidateOps withQueries t₀ m ht₀ B hB := by
    rw [modeCandPrefix_full, HardKeyValSeed.modeCandidateOps_eq]
    cases withQueries
    · simp only [Bool.false_eq_true, ↓reduceIte, HardKeyValSeed.candidateUpdateOps_eq]; rfl
    · simp only [↓reduceIte, HardKeyValSeed.candidateOps_eq]; rfl
  have huniv_flt : (Finset.univ.filter fun r : Fin m => r.val < m) = Finset.univ := by
    ext r; simp only [Finset.mem_filter, Finset.mem_univ, Fin.isLt, and_self]
  rw [hfull] at hvh_m hst_m
  rw [huniv_flt, image_orderSubset B hB π] at hst_m
  have hlen_B : (s.modeCandidateOps withQueries t₀ m ht₀ B hB).length = stride * m := by
    rw [← hfull]
    have htk : (List.finRange m).take m = List.finRange m :=
      List.take_of_length_le (by simp only [List.length_finRange, le_rfl])
    dsimp only [modeCandPrefix, stride, modeStride]
    rw [htk]
    cases withQueries
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [List.length_flatMap_of_forall_length_eq (k := 2) (fun _ _ => rfl),
        List.length_finRange, Nat.mul_comm]
    · simp only [↓reduceIte]
      rw [List.length_flatMap_of_forall_length_eq (k := 3) (fun _ _ => rfl),
        List.length_finRange, Nat.mul_comm]
  refine ⟨hvh_m, ?_, hst_m⟩
  rw [List.length_append, hpref_len, hlen_B]; ring

end Cslib.DataStructure.Dictionary.CellProbe
