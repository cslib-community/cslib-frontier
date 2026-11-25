/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound.CandidateReplay
public import Mathlib.Algebra.Group.Fin.Basic
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import Mathlib.Logic.Equiv.Fintype

/-!
# Query-Free Inner Pool Symmetry and `stateFiber` Markov Bound

Equivariance (`actSeed8Equiv`) for the Section 8.1 candidate-pool distribution, uniformity of the
post-segment dictionary `pairBOf`, and Markov sub-conditioning on decoded-state fiber multiplicities
(`prob_gt_cap_stateFiber_le`).

## Main definitions

* `Cslib.DataStructure.Dictionary.CellProbe.actSeed8Equiv`: key-permutation and value-shift action
  on `HardKeyValSeed`.
* `Cslib.DataStructure.Dictionary.CellProbe.pairBOf`: post-segment `SizedDict` extracted from
  `(s, B)`.
* `Cslib.DataStructure.Dictionary.CellProbe.PoolCtx`: equivariant `P_size`-element pool context.

## Main results

* `Cslib.DataStructure.Dictionary.CellProbe.toReal_innerPoolDist_actSeed8Equiv`: invariance of the
  query-free pool distribution under `actSeed8Equiv`.
* `Cslib.DataStructure.Dictionary.CellProbe.prob_gt_cap_stateFiber_le`: Markov bound restricting the
  multiplicity of `stateFiber` relative to its uniform marginal.
-/

public section

open scoped BigOperators ENNReal

namespace Cslib.DataStructure.Dictionary.CellProbe

open Cslib.CellProbe Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.Probability

/-! #### Query-free inner pool symmetry, `T_B` uniformity, and Markov sub-conditioning -/

/-- Seed equivalence permuting keys by `τ` and shifting values by `δ`. -/
@[expose] def actSeed8Equiv {U V n : ℕ} [NeZero V] (τ : Equiv.Perm (Fin U)) (δ : Fin U → Fin V) :
    HardKeyValSeed U V n ≃ HardKeyValSeed U V n where
  toFun s :=
    { keys := s.keys.trans τ.toEmbedding
      kv := fun u => s.kv (τ.symm u) + δ u
      delPerm := s.delPerm }
  invFun s :=
    { keys := s.keys.trans τ.symm.toEmbedding
      kv := fun u => s.kv (τ u) - δ (τ u)
      delPerm := s.delPerm }
  left_inv s := by
    cases s; simp only [HardKeyValSeed.mk.injEq, and_true]
    exact ⟨by ext i; simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
        Equiv.symm_apply_apply],
      by funext u; simp only [Equiv.symm_apply_apply, add_sub_cancel_right]⟩
  right_inv s := by
    cases s; simp only [HardKeyValSeed.mk.injEq, and_true]
    exact ⟨by ext i; simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
        Equiv.apply_symm_apply],
      by funext u; simp only [Equiv.apply_symm_apply, sub_add_cancel]⟩

theorem actSeed8Equiv_activeKeys {U V n : ℕ} [NeZero V] (τ : Equiv.Perm (Fin U))
    (δ : Fin U → Fin V) (s : HardKeyValSeed U V n) (t₀ : ℕ) (ht : t₀ ≤ n) :
    (actSeed8Equiv τ δ s).activeKeys t₀ ht = (s.activeKeys t₀ ht).map τ.toEmbedding := by
  ext u
  simp only [HardKeyValSeed.activeKeys, HardKeyValSeed.permKeyEmb, actSeed8Equiv,
    Equiv.coe_fn_mk, Finset.mem_map, windowEmb_apply, Function.Embedding.trans_apply,
    Equiv.coe_toEmbedding]
  exact ⟨fun ⟨k, _, hk⟩ => ⟨_, ⟨k, Finset.mem_univ k, rfl⟩, hk⟩,
    fun ⟨_, ⟨k, _, rfl⟩, hk⟩ => ⟨k, Finset.mem_univ k, hk⟩⟩

theorem actSeed8Equiv_insertedSet {U V n : ℕ} [NeZero V] (τ : Equiv.Perm (Fin U))
    (δ : Fin U → Fin V) (s : HardKeyValSeed U V n) (t₀ r : ℕ) (hr : t₀ + r ≤ n) :
    (actSeed8Equiv τ δ s).insertedSet t₀ r hr = (s.insertedSet t₀ r hr).map τ.toEmbedding := by
  ext u
  simp only [HardKeyValSeed.insertedSet, segInsertedKeys_apply, actSeed8Equiv, Equiv.coe_fn_mk,
    Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and,
    Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  exact ⟨fun ⟨j, hj⟩ => ⟨_, ⟨j, rfl⟩, hj⟩, fun ⟨_, ⟨j, rfl⟩, hj⟩ => ⟨j, hj⟩⟩

theorem actSeed8Equiv_deletedSet {U V n : ℕ} [NeZero V] (τ : Equiv.Perm (Fin U))
    (δ : Fin U → Fin V) (s : HardKeyValSeed U V n) (t₀ m : ℕ) (ht₀ : t₀ + m ≤ n) :
    Finset.univ.image (segDeletedKeys (actSeed8Equiv τ δ s).keys (actSeed8Equiv τ δ s).delPerm
        t₀ m ht₀) =
      (Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)).map τ.toEmbedding := by
  ext u
  simp only [segDeletedKeys_apply, actSeed8Equiv, Equiv.coe_fn_mk,
    Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and,
    Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  exact ⟨fun ⟨j, hj⟩ => ⟨_, ⟨j, rfl⟩, hj⟩, fun ⟨_, ⟨j, rfl⟩, hj⟩ => ⟨j, hj⟩⟩

open Classical in
private noncomputable def sizedDictOfFinset {U V n : ℕ} (S : Finset (Fin U)) (hS : S.card = n)
    (kv : Fin U → Fin V) : SizedDict U V n :=
  ⟨fun u => if u ∈ S then some (kv u).val else none,
   by rw [dom_ite_eq]; exact hS,
   fun u w hw => by
     by_cases hu : u ∈ S
     · simp only [hu, ↓reduceIte, Option.some.injEq] at hw; exact hw ▸ (kv u).isLt
     · simp only [hu, ↓reduceIte, reduceCtorEq] at hw⟩

open Classical in
private theorem dom_sizedDictOfFinset {U V n : ℕ} (S : Finset (Fin U)) (hS : S.card = n)
    (kv : Fin U → Fin V) : Dictionary.dom (sizedDictOfFinset S hS kv).val = S :=
  dom_ite_eq S kv

open Classical in
private theorem sizedDictOfFinset_apply {U V n : ℕ} (S : Finset (Fin U)) (hS : S.card = n)
    (kv : Fin U → Fin V) (u : Fin U) :
    (sizedDictOfFinset S hS kv).val u = if u ∈ S then some (kv u).val else none := rfl

open Classical in
private noncomputable def dictKV {U V n : ℕ} [NeZero V] (p : SizedDict U V n) (u : Fin U) :
    Fin V :=
  if h : (p.val u).isSome then ⟨(p.val u).get h, p.2.2 u _ (Option.some_get h).symm⟩
  else ⟨0, NeZero.pos V⟩

open Classical in
private theorem sizedDict_val_eq_ite {U V n : ℕ} [NeZero V] (p : SizedDict U V n) (u : Fin U) :
    p.val u = if u ∈ Dictionary.dom p.val then some (dictKV p u).val else none := by
  by_cases hu : u ∈ Dictionary.dom p.val
  · have his : (p.val u).isSome := Dictionary.mem_dom_iff_isSome.mp hu
    simp only [hu, ↓reduceIte, dictKV, dite_eq_left his]
    exact (Option.some_get his).symm
  · rw [ite_eq_right hu]; exact Dictionary.notMem_dom_iff.mp hu

open Classical in
private theorem dictKV_sizedDictOfFinset {U V n : ℕ} [NeZero V] (S : Finset (Fin U))
    (hS : S.card = n) (kv : Fin U → Fin V) {u : Fin U} (hu : u ∈ S) :
    dictKV (sizedDictOfFinset S hS kv) u = kv u := by
  apply Fin.ext
  have his : ((sizedDictOfFinset S hS kv).val u).isSome := by
    simp only [sizedDictOfFinset, hu, ↓reduceIte, Option.isSome_some]
  simp only [dictKV, dite_eq_left his]
  exact Option.some.inj (by
    rw [Option.some_get]
    simp only [sizedDictOfFinset, hu, ↓reduceIte])

open Classical in
private theorem sizedDictOfFinset_ext {U V n : ℕ} {S₁ S₂ : Finset (Fin U)} (hS₁ : S₁.card = n)
    (hS₂ : S₂.card = n) {kv₁ kv₂ : Fin U → Fin V}
    (hS : S₁ = S₂) (hkv : ∀ u ∈ S₁, kv₁ u = kv₂ u) :
    sizedDictOfFinset S₁ hS₁ kv₁ = sizedDictOfFinset S₂ hS₂ kv₂ := by
  subst hS; refine Subtype.ext (funext fun u => ?_)
  by_cases hu : u ∈ S₁
  · simp only [sizedDictOfFinset, hu, ↓reduceIte, hkv u hu]
  · simp only [sizedDictOfFinset, hu, ↓reduceIte]

open Classical in
private noncomputable def actSizedDictEquiv {U V n : ℕ} [NeZero V]
    (τ : Equiv.Perm (Fin U)) (δ : Fin U → Fin V) : SizedDict U V n ≃ SizedDict U V n where
  toFun p := sizedDictOfFinset ((Dictionary.dom p.val).map τ.toEmbedding)
    (by rw [Finset.card_map]; exact p.2.1) (fun u => dictKV p (τ.symm u) + δ u)
  invFun p := sizedDictOfFinset ((Dictionary.dom p.val).map τ.symm.toEmbedding)
    (by rw [Finset.card_map]; exact p.2.1) (fun u => dictKV p (τ u) - δ (τ u))
  left_inv p := by
    refine Subtype.ext (funext fun u => ?_)
    rw [sizedDict_val_eq_ite p u]
    dsimp only
    rw [sizedDictOfFinset_apply, dom_sizedDictOfFinset]
    by_cases hu : u ∈ Dictionary.dom p.val
    · have hτu : τ u ∈ (Dictionary.dom p.val).map τ.toEmbedding :=
        Finset.mem_map.mpr ⟨u, hu, rfl⟩
      have hu' : u ∈ ((Dictionary.dom p.val).map τ.toEmbedding).map τ.symm.toEmbedding :=
        Finset.mem_map.mpr ⟨τ u, hτu, τ.symm_apply_apply u⟩
      simp only [hu', hu, ↓reduceIte, dictKV_sizedDictOfFinset _ _ _ hτu,
        Equiv.symm_apply_apply, add_sub_cancel_right]
    · have hu' : u ∉ ((Dictionary.dom p.val).map τ.toEmbedding).map τ.symm.toEmbedding := by
        intro hmem
        obtain ⟨y, hy, hyu⟩ := Finset.mem_map.mp hmem
        obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
        simp only [Equiv.coe_toEmbedding] at hxy hyu
        rw [← hxy, Equiv.symm_apply_apply] at hyu
        exact hu (hyu ▸ hx)
      simp only [hu', hu, ↓reduceIte]
  right_inv p := by
    refine Subtype.ext (funext fun u => ?_)
    rw [sizedDict_val_eq_ite p u]
    dsimp only
    rw [sizedDictOfFinset_apply, dom_sizedDictOfFinset]
    by_cases hu : u ∈ Dictionary.dom p.val
    · have hτu : τ.symm u ∈ (Dictionary.dom p.val).map τ.symm.toEmbedding :=
        Finset.mem_map.mpr ⟨u, hu, rfl⟩
      have hu' : u ∈ ((Dictionary.dom p.val).map τ.symm.toEmbedding).map τ.toEmbedding :=
        Finset.mem_map.mpr ⟨τ.symm u, hτu, τ.apply_symm_apply u⟩
      simp only [hu', hu, ↓reduceIte, dictKV_sizedDictOfFinset _ _ _ hτu,
        Equiv.apply_symm_apply, sub_add_cancel]
    · have hu' : u ∉ ((Dictionary.dom p.val).map τ.symm.toEmbedding).map τ.toEmbedding := by
        intro hmem
        obtain ⟨y, hy, hyu⟩ := Finset.mem_map.mp hmem
        obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
        simp only [Equiv.coe_toEmbedding] at hxy hyu
        rw [← hxy, Equiv.apply_symm_apply] at hyu
        exact hu (hyu ▸ hx)
      simp only [hu', hu, ↓reduceIte]

open Classical in
private theorem exists_actSizedDictEquiv {U V n : ℕ} [NeZero V] (p₁ p₂ : SizedDict U V n) :
    ∃ (τ : Equiv.Perm (Fin U)) (δ : Fin U → Fin V), actSizedDictEquiv τ δ p₁ = p₂ := by
  obtain ⟨τ, hτ_map⟩ := Equiv.Perm.exists_map_finset_eq
    (Dictionary.dom p₁.val) (Dictionary.dom p₂.val) (p₁.2.1.trans p₂.2.1.symm)
  let δ (u : Fin U) : Fin V := dictKV p₂ u - dictKV p₁ (τ.symm u)
  refine ⟨τ, δ, Subtype.ext (funext fun u => ?_)⟩
  rw [sizedDict_val_eq_ite p₂ u]
  dsimp only [actSizedDictEquiv, Equiv.coe_fn_mk]
  rw [sizedDictOfFinset_apply, hτ_map]
  by_cases hu : u ∈ Dictionary.dom p₂.val
  · simp only [hu, ↓reduceIte, δ, add_sub_cancel]
  · simp only [hu, ↓reduceIte]

open Classical in
/-- Decoded post-segment `SizedDict` built from `(s, B)` by replacing deleted keys with `B`. -/
noncomputable def pairBOf {U V n : ℕ} (t₀ m : ℕ) (ht₀ : t₀ + m ≤ n)
    (sb : HardKeyValSeed U V n × Finset (Fin U)) : SizedDict U V n :=
  let K_cand := (sb.1.activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
    Finset.univ.image (segDeletedKeys sb.1.keys sb.1.delPerm t₀ m ht₀)) ∪ sb.2
  if hK : K_cand.card = n then
    sizedDictOfFinset K_cand hK sb.1.kv
  else
    sizedDictOfFinset (sb.1.activeKeys t₀ (Nat.le_of_add_right_le ht₀))
      (card_activeKeys sb.1 (Nat.le_of_add_right_le ht₀)) sb.1.kv

open Classical in
private theorem actSizedDictEquiv_pairBOf {U V n t₀ m : ℕ} [NeZero V] (ht₀ : t₀ + m ≤ n)
    (τ : Equiv.Perm (Fin U)) (δ : Fin U → Fin V)
    (sb : HardKeyValSeed U V n × Finset (Fin U)) :
    pairBOf t₀ m ht₀ (actSeed8Equiv τ δ sb.1, sb.2.map τ.toEmbedding) =
      actSizedDictEquiv τ δ (pairBOf t₀ m ht₀ sb) := by
  rcases sb with ⟨s, B⟩
  let S₀ := (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
    Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)) ∪ B
  have hmap_S₀ : (((actSeed8Equiv τ δ s).activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
        Finset.univ.image (segDeletedKeys (actSeed8Equiv τ δ s).keys
          (actSeed8Equiv τ δ s).delPerm t₀ m ht₀)) ∪ B.map τ.toEmbedding) =
      S₀.map τ.toEmbedding := by
    dsimp only [S₀]
    rw [actSeed8Equiv_activeKeys, actSeed8Equiv_deletedSet, Finset.map_union, Finset.map_sdiff]
  dsimp only [pairBOf, actSizedDictEquiv, Equiv.coe_fn_mk]
  by_cases hc : S₀.card = n
  · have hc' : (((actSeed8Equiv τ δ s).activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
        Finset.univ.image (segDeletedKeys (actSeed8Equiv τ δ s).keys
          (actSeed8Equiv τ δ s).delPerm t₀ m ht₀)) ∪ B.map τ.toEmbedding).card = n := by
      rw [hmap_S₀, Finset.card_map]; exact hc
    rw [dite_eq_left hc', dite_eq_left hc]
    refine sizedDictOfFinset_ext _ _ (by rw [dom_sizedDictOfFinset, hmap_S₀]) fun u hu => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp (hmap_S₀ ▸ hu)
    simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    rw [dictKV_sizedDictOfFinset S₀ hc s.kv hx]
    simp only [actSeed8Equiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  · have hc' : (((actSeed8Equiv τ δ s).activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
        Finset.univ.image (segDeletedKeys (actSeed8Equiv τ δ s).keys
          (actSeed8Equiv τ δ s).delPerm t₀ m ht₀)) ∪ B.map τ.toEmbedding).card ≠ n := by
      rw [hmap_S₀, Finset.card_map]; exact hc
    rw [dite_eq_right hc', dite_eq_right hc]
    refine sizedDictOfFinset_ext _ _
      (by rw [dom_sizedDictOfFinset, actSeed8Equiv_activeKeys]) fun u hu => ?_
    have hu' := actSeed8Equiv_activeKeys τ δ s t₀ (Nat.le_of_add_right_le ht₀) ▸ hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hu'
    simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    rw [dictKV_sizedDictOfFinset _ (card_activeKeys s _) s.kv hx]
    simp only [actSeed8Equiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply]

private theorem card_sdiff_deleted_union_eq {U V n t₀ m : ℕ} (s : HardKeyValSeed U V n)
    (ht₀ : t₀ + m ≤ n) {B : Finset (Fin U)} (hB : B.card = m)
    (hdisj : Disjoint B (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀))) :
    ((s.activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
      Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)) ∪ B).card = n := by
  let ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
  have hdisj' : Disjoint (s.activeKeys t₀ ht₀_n \
      Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)) B :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset hdisj.symm
  rw [Finset.card_union_of_disjoint hdisj', Finset.card_sdiff,
    Finset.inter_eq_left.mpr (segDeletedKeys_subset_activeKeys s ht₀),
    card_activeKeys s ht₀_n, card_deletedSet s ht₀, hB]
  omega

open Classical in
theorem val_pairBOf_eq {U V n t₀ m : ℕ} (s : HardKeyValSeed U V n)
    (ht₀ : t₀ + m ≤ n) {B : Finset (Fin U)} (hB : B.card = m)
    (hdisj : Disjoint B (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀))) :
    (pairBOf t₀ m ht₀ (s, B)).val =
      fun u => if u ∈ (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
          Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)) ∪ B
        then some (s.kv u).val else none := by
  dsimp only [pairBOf]
  rw [dite_eq_left (card_sdiff_deleted_union_eq s ht₀ hB hdisj)]
  rfl

/-- Symmetry-closed candidate pool context parameterizing the query-free inner game. -/
structure PoolCtx (U V n t₀ m g P_size : ℕ) (ht₀ : t₀ + m ≤ n) where
  /-- Seed-indexed candidate pool of unused keys of cardinality `P_size`. -/
  pool : HardKeyValSeed U V n → Finset (Fin U)
  hcard : ∀ s, (pool s).card = P_size
  hA : ∀ s, s.insertedSet t₀ m ht₀ ⊆ pool s
  hdisj : ∀ s, Disjoint (pool s) (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀))
  hact : ∀ [NeZero V] (τ : Equiv.Perm (Fin U)) (δ : Fin U → Fin V) s,
    pool (actSeed8Equiv τ δ s) = (pool s).map τ.toEmbedding
  /-- Family of `m`-element subsets of `pool s` meeting `insertedSet` in `g` keys. -/
  Fg : HardKeyValSeed U V n → Finset (Finset (Fin U))
  hFg : ∀ s, Fg s = ((pool s).powersetCard m).filter fun B =>
    (s.insertedSet t₀ m ht₀ ∩ B).card = g
  hne : ∀ s, (Fg s).Nonempty

open Classical in
theorem toReal_innerPoolDist_actSeed8Equiv {U V n t₀ m g P_size : ℕ} [NeZero V]
    (hU : 2 * n ≤ U) (hV : 1 ≤ V) {ht₀ : t₀ + m ≤ n} (ctx : PoolCtx U V n t₀ m g P_size ht₀)
    (τ : Equiv.Perm (Fin U)) (δ : Fin U → Fin V)
    (s : HardKeyValSeed U V n) (B : Finset (Fin U)) :
    (innerPoolDist hU hV ctx.Fg ctx.hne (actSeed8Equiv τ δ s, B.map τ.toEmbedding)).toReal =
      (innerPoolDist hU hV ctx.Fg ctx.hne (s, B)).toReal := by
  have hFg_card (s' : HardKeyValSeed U V n) :
      (ctx.Fg s').card = m.choose g * (P_size - m).choose (m - g) := by
    rw [ctx.hFg s', card_inter_filter_powersetCard (ctx.hA s') (card_insertedSet s' ht₀),
      ctx.hcard s']
  have hmem_iff : B.map τ.toEmbedding ∈ ctx.Fg (actSeed8Equiv τ δ s) ↔ B ∈ ctx.Fg s := by
    rw [ctx.hFg, ctx.hFg, ctx.hact τ δ s, actSeed8Equiv_insertedSet]
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.card_map,
      ← Finset.map_inter, Finset.map_subset_map]
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨s⟩
  rw [toReal_innerPoolDist_apply, toReal_innerPoolDist_apply, hFg_card, hFg_card]
  have hunif_s : ((PMF.uniformOfFintype (HardKeyValSeed U V n)) (actSeed8Equiv τ δ s)) =
      (PMF.uniformOfFintype (HardKeyValSeed U V n)) s := by
    simp only [PMF.uniformOfFintype_apply]
  rw [hunif_s]
  by_cases hB : B ∈ ctx.Fg s
  · rw [ite_eq_left (hmem_iff.mpr hB), ite_eq_left hB]
  · rw [ite_eq_right (mt hmem_iff.mp hB), ite_eq_right hB]

open Classical in
theorem prob_gt_cap_stateFiber_le {U V n t₀ m g P_size cells w : ℕ} {γ R : ℝ}
    (hU : 2 * n ≤ U) (hU_pos_nat : 1 ≤ U) (hV : 1 ≤ V) {ht₀ : t₀ + m ≤ n}
    (hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
    (ctx : PoolCtx U V n t₀ m g P_size ht₀)
    (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w) (stepIdx : ℕ) :
    let μ_g := innerPoolDist hU hV ctx.Fg ctx.hne
    let M_cap := (2 : ℝ) ^ (R + 1) * (U : ℝ) ^ (γ * (m : ℝ))
    (((μ_g.map fun sb => decide (M_cap <
      ((stateFiber D_det stepIdx (pairBOf t₀ m ht₀ sb).val).card : ℝ))) true).toReal) ≤
      (1 / 2) * (U : ℝ) ^ (-γ * (m : ℝ)) := by
  let _ : NeZero V := ⟨by omega⟩
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
  let μ_g := innerPoolDist hU hV ctx.Fg ctx.hne
  let M_cap := (2 : ℝ) ^ (R + 1) * (U : ℝ) ^ (γ * (m : ℝ))
  have hunif_pair (p₁ p₂ : SizedDict U V n) :
      ((μ_g.map (pairBOf t₀ m ht₀)) p₁).toReal = ((μ_g.map (pairBOf t₀ m ht₀)) p₂).toReal := by
    obtain ⟨τ, δ, hp_eq⟩ := exists_actSizedDictEquiv p₁ p₂
    let e_sb : (HardKeyValSeed U V n × Finset (Fin U)) ≃
        (HardKeyValSeed U V n × Finset (Fin U)) :=
      (actSeed8Equiv τ δ).prodCongr
        { toFun := fun B => B.map τ.toEmbedding
          invFun := fun B => B.map τ.symm.toEmbedding
          left_inv := fun B => by
            ext x; simp only [Finset.mem_map, Equiv.coe_toEmbedding]
            exact ⟨fun ⟨y, ⟨z, hz, hyz⟩, hyx⟩ => by
              rwa [← hyx, ← hyz, τ.symm_apply_apply],
              fun hx => ⟨τ x, ⟨x, hx, rfl⟩, τ.symm_apply_apply x⟩⟩
          right_inv := fun B => by
            ext x; simp only [Finset.mem_map, Equiv.coe_toEmbedding]
            exact ⟨fun ⟨y, ⟨z, hz, hyz⟩, hyx⟩ => by
              rwa [← hyx, ← hyz, τ.apply_symm_apply],
              fun hx => ⟨τ.symm x, ⟨x, hx, rfl⟩, τ.apply_symm_apply x⟩⟩ }
    have hpair_act (sb : HardKeyValSeed U V n × Finset (Fin U)) :
        pairBOf t₀ m ht₀ (e_sb sb) = p₂ ↔ pairBOf t₀ m ht₀ sb = p₁ := by
      rcases sb with ⟨s, B⟩
      change pairBOf t₀ m ht₀ (actSeed8Equiv τ δ s, B.map τ.toEmbedding) = p₂ ↔
        pairBOf t₀ m ht₀ (s, B) = p₁
      rw [actSizedDictEquiv_pairBOf ht₀ τ δ (s, B), ← hp_eq,
        (actSizedDictEquiv τ δ).injective.eq_iff]
    rw [PMF.map_apply_toReal, PMF.map_apply_toReal]
    conv_rhs => rw [← e_sb.sum_comp]
    refine Finset.sum_congr rfl fun sb _ => ?_
    by_cases h1 : p₁ = pairBOf t₀ m ht₀ sb
    · have h2 : p₂ = pairBOf t₀ m ht₀ (e_sb sb) := ((hpair_act sb).mpr h1.symm).symm
      rw [ite_eq_left h1, ite_eq_left h2]
      exact (toReal_innerPoolDist_actSeed8Equiv hU hV ctx τ δ sb.1 sb.2).symm
    · have h2 : p₂ ≠ pairBOf t₀ m ht₀ (e_sb sb) :=
        fun h => h1 ((hpair_act sb).mp h.symm).symm
      rw [ite_eq_right h1, ite_eq_right h2]
  let N_tot := Fintype.card (SizedDict U V n)
  have hN_eq : N_tot = U.choose n * V ^ n := card_sizedDict U V n
  have hN_pos : (0 : ℝ) < (N_tot : ℝ) := by
    rw [hN_eq]; exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.pow_pos hV)
  have hpair_prob (p : SizedDict U V n) :
      ((μ_g.map (pairBOf t₀ m ht₀)) p).toReal = (N_tot : ℝ)⁻¹ := by
    have hsum := PMF.sum_toReal (μ_g.map (pairBOf t₀ m ht₀))
    have hconst : (∑ q : SizedDict U V n, ((μ_g.map (pairBOf t₀ m ht₀)) q).toReal) =
        (N_tot : ℝ) * ((μ_g.map (pairBOf t₀ m ht₀)) p).toReal := by
      rw [Finset.sum_congr rfl fun q _ => hunif_pair q p, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    rw [hconst] at hsum
    exact eq_inv_of_mul_eq_one_right hsum
  have hexp_fiber : (∑ sb : HardKeyValSeed U V n × Finset (Fin U),
      (μ_g sb).toReal *
        ((stateFiber D_det stepIdx (pairBOf t₀ m ht₀ sb).val).card : ℝ)) ≤
      (2 : ℝ) ^ R := by
    have hpush : (∑ sb, (μ_g sb).toReal *
          ((stateFiber D_det stepIdx (pairBOf t₀ m ht₀ sb).val).card : ℝ)) =
        ∑ p : SizedDict U V n, ((μ_g.map (pairBOf t₀ m ht₀)) p).toReal *
          ((stateFiber D_det stepIdx p.val).card : ℝ) := by
      simp_rw [PMF.map_apply_toReal, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun sb _ => ?_
      have h1 (p : SizedDict U V n) :
          (if p = pairBOf t₀ m ht₀ sb then (μ_g sb).toReal else 0) *
            ((stateFiber D_det stepIdx p.val).card : ℝ) =
          if p = pairBOf t₀ m ht₀ sb then
            (μ_g sb).toReal * ((stateFiber D_det stepIdx p.val).card : ℝ)
          else 0 := by
        split_ifs <;> ring
      simp_rw [h1]
      rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]
    rw [hpush]
    simp_rw [hpair_prob, ← Finset.mul_sum]
    have hsum_le : (∑ p : SizedDict U V n,
        ((stateFiber D_det stepIdx p.val).card : ℝ)) ≤ (2 : ℝ) ^ (cells * w) := by
      exact_mod_cast sum_card_stateFiber_le D_det stepIdx
    have h2cw : (2 : ℝ) ^ (cells * w) ≤ (N_tot : ℝ) * (2 : ℝ) ^ R := by
      have hc_ne : ((U.choose n : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (by omega)).ne'
      have hv_ne : ((V : ℝ) ^ n) ≠ 0 := by positivity
      have hlogN : Real.logb 2 (N_tot : ℝ) = benchmarkBits U V n := by
        rw [hN_eq, Nat.cast_mul, Nat.cast_pow, Real.logb_mul hc_ne hv_ne,
          Real.logb_pow, benchmarkBits_eq]
      have hrpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hspace
      rw [Real.rpow_natCast] at hrpow
      rw [← hlogN, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hN_pos] at hrpow
      exact hrpow
    calc (N_tot : ℝ)⁻¹ * ∑ p : SizedDict U V n, ((stateFiber D_det stepIdx p.val).card : ℝ)
        ≤ (N_tot : ℝ)⁻¹ * (2 : ℝ) ^ (cells * w) :=
          mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hN_pos.le)
      _ ≤ (N_tot : ℝ)⁻¹ * ((N_tot : ℝ) * (2 : ℝ) ^ R) :=
          mul_le_mul_of_nonneg_left h2cw (inv_nonneg.mpr hN_pos.le)
      _ = (2 : ℝ) ^ R := inv_mul_cancel_left₀ hN_pos.ne' _
  have hU_pos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU_pos_nat
  have hM_pos : 0 < M_cap := mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos hU_pos _)
  have hmarkov : (((μ_g.map fun sb => decide (M_cap <
      ((stateFiber D_det stepIdx (pairBOf t₀ m ht₀ sb).val).card : ℝ))) true).toReal) *
        M_cap ≤
      ∑ sb, (μ_g sb).toReal *
        ((stateFiber D_det stepIdx (pairBOf t₀ m ht₀ sb).val).card : ℝ) := by
    rw [PMF.map_apply_toReal, Finset.sum_mul]
    refine Finset.sum_le_sum fun sb _ => ?_
    by_cases hgt : M_cap < ((stateFiber D_det stepIdx (pairBOf t₀ m ht₀ sb).val).card : ℝ)
    · simp only [hgt, decide_true, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left hgt.le ENNReal.toReal_nonneg
    · simp only [hgt, decide_false, Bool.true_eq_false, ↓reduceIte, zero_mul]
      exact mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)
  have hdiv : (2 : ℝ) ^ R / M_cap = (1 / 2) * (U : ℝ) ^ (-γ * (m : ℝ)) := by
    dsimp only [M_cap]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
      show -γ * (m : ℝ) = -(γ * (m : ℝ)) by ring, Real.rpow_neg hU_pos.le]
    field_simp
  rw [← hdiv, le_div_iff₀ hM_pos]
  exact hmarkov.trans hexp_fiber

end Cslib.DataStructure.Dictionary.CellProbe
