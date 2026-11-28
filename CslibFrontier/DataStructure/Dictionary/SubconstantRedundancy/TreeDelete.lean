/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.TreeInsert

/-!
# Quotient-Recovering Deletion (`Algorithm 3`) in the Multi-Level Dictionary Tree

This file formalizes `Algorithm 3` (`deleteAndGetQuotient`) and normal-path deletion
(`normalDeleteMem`) of Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic
Dictionary with Subconstant Wasted Bits per Key* ([LiLiangYuZhou2024, Section 5.3, Algorithm 3];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF p. 31 / printed p. 30).

## Main definitions

* `TreeSchedule.TreeState.deleteAndGetQuotient`: recursive upward deletion and quotient recovery
  (`Algorithm 3`).
* `TreeSchedule.TreeState.normalDeleteMem`: normal-path deletion starting at leaf level `depth`.

## Main results

* `TreeSchedule.TreeState.deleteAndGetQuotient_spec`: exact quotient-and-value recovery
  (`(q_out, v_out) = (quotAt ℓ z, v_z)`) and prefix invariant preservation across levels `1 .. ℓ`.
* `TreeSchedule.TreeState.wellFormedPadded_normalDeleteMem`: preservation of `WellFormedPadded`
  under non-underflowing deletion.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Finset

private theorem image_erase_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S F : Finset α} (hFS : F ⊆ S) {f : α → β} (hinj : Set.InjOn f S) {x : α} (hx : x ∈ S) :
    (F.image f).erase (f x) = (F.erase x).image f := by
  ext b
  simp only [mem_erase, mem_image]
  grind [Set.InjOn]

private theorem mem_image_filter_of_injOn {α β : Type*} [DecidableEq β] {S : Finset α}
    {f : α → β} (hinj : Set.InjOn f S) {p : α → Prop} [DecidablePred p] {x : α} (hx : x ∈ S) :
    f x ∈ (S.filter p).image f ↔ p x := by
  simp only [mem_image, mem_filter]
  exact ⟨fun ⟨a, ⟨ha, hpa⟩, e⟩ => hinj ha hx e ▸ hpa, fun h => ⟨x, ⟨hx, h⟩, rfl⟩⟩

namespace TreeSchedule.TreeState

variable {P : TreeSchedule}
/-! ## Section 2: `Algorithm 3` (`deleteAndGetQuotient`) and `normalDeleteMem` -/

/-- **`Algorithm 3` (`DeleteAndGetQuotient`, [LiLiangYuZhou2024, Section 5.3], PDF p. 31 /
printed p. 30)**: recursively deletes `z_id` from levels `1 .. ℓ` along `u`'s ancestor path while
maintaining full capacity at levels `2 .. ℓ` via waiting-list replacement and returning
`(st', z_quot^[ℓ], z_val)`. -/
noncomputable def deleteAndGetQuotient
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) :
    ∀ (ℓ : ℕ), 1 ≤ ℓ → ℓ ≤ P.depth → Fin (P.numNodes ℓ) → Fin (2 ^ P.idBits ℓ) →
      P.TreeState × Fin (P.quotUniv ℓ) × Fin P.valBound
  | 0, h1, _, _, _ => False.elim (by omega)
  | 1, _, _, u₁, z_id =>
    let qv := ((st.roots u₁).table.query z_id).getD (⟨0, P.quotUniv_pos 1⟩, ⟨0, P.val_pos⟩)
    (st.updateRoot u₁ { (st.roots u₁) with table := (st.roots u₁).table.delete z_id },
      qv.1, qv.2)
  | m + 2, _, hℓ, u_cur, z_id =>
    have h2 : 2 ≤ m + 2 := by omega
    have h1_prev : 1 ≤ m + 1 := by omega
    have hlt_prev : m + 1 < P.depth := by omega
    let u_prev := P.parentNode (m + 1) u_cur
    let w := st.nodeWait (m + 2) h2 hℓ u_cur
    match w.lookup z_id with
    | some z_id_prev =>
      let res := st.deleteAndGetQuotient scheme (m + 1) h1_prev hlt_prev.le u_prev z_id_prev
      let z_quot_cur :=
        (st.seeds.stepCoordEquiv h1_prev hlt_prev (u_prev, z_id_prev, res.2.1)).2.2
      (res.1.removeWaitAtNode (m + 2) h2 hℓ u_cur z_id, z_quot_cur, res.2.2)
    | none =>
      let z_qv := (st.nodeQuery scheme (m + 2) (by omega) hℓ u_cur z_id).getD
        (⟨0, P.quotUniv_pos (m + 2)⟩, ⟨0, P.val_pos⟩)
      if hne : w.dom.Nonempty then
        let popRes := w.pop hne
        let y_id_cur := popRes.1.1
        let y_id_prev := popRes.1.2
        let wait' := popRes.2
        let res := st.deleteAndGetQuotient scheme (m + 1) h1_prev hlt_prev.le u_prev y_id_prev
        let y_quot_cur :=
          (st.seeds.stepCoordEquiv h1_prev hlt_prev (u_prev, y_id_prev, res.2.1)).2.2
        (res.1.replaceAtNode scheme (m + 2) h2 hℓ u_cur wait' z_id y_id_cur
          (y_quot_cur, res.2.2), z_qv.1, z_qv.2)
      else
        (st, z_qv.1, z_qv.2)

private theorem stepCoordEquiv_quotAt (seeds : P.SeedAssignment) {m : ℕ} (h1 : 1 ≤ m)
    (hlt : m < P.depth) (u_cur : Fin (P.numNodes (m + 1))) (w : Fin P.paddedUniv)
    (hnw : seeds.nodeAt (m + 1) hlt w = u_cur) :
    (seeds.stepCoordEquiv h1 hlt
      (P.parentNode m u_cur, seeds.idAt m h1 hlt.le w, seeds.quotAt m h1 hlt.le w)).2.2 =
      seeds.quotAt (m + 1) (by omega) hlt w := by
  subst hnw
  rw [seeds.parentNode_nodeAt hlt w, ← seeds.levelCoordEquiv_fst h1 hlt.le w]
  exact congrArg (fun c => (c w).2.2) (seeds.levelCoordEquiv_succ h1 hlt).symm

/-- Inductive prefix postcondition of `deleteAndGetQuotient` at level `ℓ` (`1 ≤ ℓ ≤ depth`). -/
structure DeletePrefixPost
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st st' : P.TreeState) (d : P.PaddedDict) (storeLvl storeLvl' : Fin P.paddedUniv → ℕ)
    (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) (z : Fin P.paddedUniv) : Prop where
  seeds_eq : st'.seeds = st.seeds
  sentCount_eq : st'.sentCount = st.sentCount
  storeLvl_zero_z : storeLvl' z = 0
  storeLvl_outside : ∀ w, w ∉ (P.paddedDom d).erase z → storeLvl' w = 0
  storeLvl_le_bounds : ∀ w ∈ (P.paddedDom d).erase z, storeLvl w ≤ ℓ →
    1 ≤ storeLvl' w ∧ storeLvl' w ≤ ℓ
  storeLvl_gt_eq : ∀ w ∈ (P.paddedDom d).erase z, ℓ < storeLvl w → storeLvl' w = storeLvl w
  above_dom_eq : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hjd : j ≤ P.depth), ℓ < j →
    ∀ u, st'.nodeDom j hj1 hjd u = st.nodeDom j hj1 hjd u
  above_query_eq : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hjd : j ≤ P.depth), ℓ < j →
    ∀ u k, st'.nodeQuery scheme j hj1 hjd u k = st.nodeQuery scheme j hj1 hjd u k
  above_wait_eq : ∀ (j : ℕ) (hj2 : 2 ≤ j) (hjd : j ≤ P.depth), ℓ < j →
    ∀ u, st'.nodeWait j hj2 hjd u = st.nodeWait j hj2 hjd u
  le_dom_eq : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hjℓ : j ≤ ℓ) (u : Fin (P.numNodes j)),
    st'.nodeDom j hj1 (hjℓ.trans hℓ) u =
      ((st.seeds.activeAt ((P.paddedDom d).erase z) j (hjℓ.trans hℓ) u).filter
        fun w => storeLvl' w = j).image (st.seeds.idAt j hj1 (hjℓ.trans hℓ))
  le_query_eq : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hjℓ : j ≤ ℓ) (u : Fin (P.numNodes j))
    (w : Fin P.paddedUniv) (vw : Fin P.valBound),
    Function.update d z none w = some vw → st.seeds.nodeAt j (hjℓ.trans hℓ) w = u →
      storeLvl' w = j →
      st'.nodeQuery scheme j hj1 (hjℓ.trans hℓ) u (st.seeds.idAt j hj1 (hjℓ.trans hℓ) w) =
        some (st.seeds.quotAt j hj1 (hjℓ.trans hℓ) w, vw)
  le_inner_full : ∀ (j : ℕ) (hj2 : 2 ≤ j) (hjlt : j < P.depth), j ≤ ℓ →
    ∀ u, ((st'.inner j hj2 hjlt u).table.tableMeta.dom).card = P.tableCap j
  le_wait_dom_eq : ∀ (j : ℕ) (hj2 : 2 ≤ j) (hjℓ : j ≤ ℓ) (u : Fin (P.numNodes j)),
    (st'.nodeWait j hj2 (hjℓ.trans hℓ) u).dom =
      ((st.seeds.activeAt ((P.paddedDom d).erase z) j (hjℓ.trans hℓ) u).filter
        fun w => storeLvl' w < j).image (st.seeds.idAt j (by omega) (hjℓ.trans hℓ))
  le_wait_lookup_eq : ∀ (j : ℕ) (hj2 : 2 ≤ j) (hjℓ : j ≤ ℓ) (u : Fin (P.numNodes j))
    (w : Fin P.paddedUniv),
    w ∈ st.seeds.activeAt ((P.paddedDom d).erase z) j (hjℓ.trans hℓ) u → storeLvl' w < j →
      (st'.nodeWait j hj2 (hjℓ.trans hℓ) u).lookup
        (st.seeds.idAt j (by omega) (hjℓ.trans hℓ) w) =
        some (st.seeds.idAt (j - 1) (by omega) (by omega) w)

/-- A hit of `Function.update d z none` at `w` is a hit of `d` at a key `w ≠ z`. -/
private theorem of_update_none_eq_some {d : P.PaddedDict} {z w : Fin P.paddedUniv}
    {vw : Fin P.valBound} (h : Function.update d z none w = some vw) :
    w ≠ z ∧ d w = some vw ∧ w ∈ P.paddedDom d := by
  have hwz : w ≠ z := fun h' => by subst h'; simp at h
  rw [Function.update_of_ne hwz] at h
  exact ⟨hwz, h, (P.mem_paddedDom_iff d w).mpr (by simp [h])⟩

/-- Seen from any level `j` above `ℓ`, a prefix deletion up to `ℓ` leaves the storage levels of
the keys other than `z` unchanged. -/
private theorem DeletePrefixPost.storeLvl_iff
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st st' : P.TreeState} {d : P.PaddedDict} {storeLvl storeLvl' : Fin P.paddedUniv → ℕ}
    {ℓ : ℕ} {hℓ : ℓ ≤ P.depth} {z : Fin P.paddedUniv}
    (hpost : DeletePrefixPost scheme st st' d storeLvl storeLvl' ℓ hℓ z)
    (hwf : st.WellFormedPadded scheme d storeLvl) {w : Fin P.paddedUniv} (hwz : w ≠ z)
    {j : ℕ} (hj : ℓ < j) :
    (storeLvl' w = j ↔ storeLvl w = j) ∧ (storeLvl' w < j ↔ storeLvl w < j) := by
  by_cases hw : w ∈ P.paddedDom d
  · have := hpost.storeLvl_le_bounds w (mem_erase.mpr ⟨hwz, hw⟩)
    have := hpost.storeLvl_gt_eq w (mem_erase.mpr ⟨hwz, hw⟩)
    omega
  · simp [hpost.storeLvl_outside w (mt mem_of_mem_erase hw), hwf.storeLvl_outside w hw]

/-- After a prefix deletion every inner table is still full, at every level. -/
private theorem DeletePrefixPost.card_nodeDom
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st st' : P.TreeState} {d : P.PaddedDict} {storeLvl storeLvl' : Fin P.paddedUniv → ℕ}
    {ℓ : ℕ} {hℓ : ℓ ≤ P.depth} {z : Fin P.paddedUniv}
    (hpost : DeletePrefixPost scheme st st' d storeLvl storeLvl' ℓ hℓ z)
    (hwf : st.WellFormedPadded scheme d storeLvl) {j : ℕ} (hj2 : 2 ≤ j) (hjlt : j < P.depth)
    (u : Fin (P.numNodes j)) :
    (st'.nodeDom j (by omega) hjlt.le u).card = P.tableCap j := by
  by_cases hj : j ≤ ℓ
  · rw [nodeDom_inner _ _ hj2 hjlt]
    exact hpost.le_inner_full j hj2 hjlt hj u
  · rw [hpost.above_dom_eq j _ _ (by omega) u, nodeDom_inner _ _ hj2 hjlt]
    exact hwf.inner_full j hj2 hjlt u

/-- Base case of `Algorithm 3`: deleting `z` from the table of its root deletes it from
level `1`. -/
private theorem deletePrefixPost_updateRoot
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) (hℓ : 1 ≤ P.depth) {z : Fin P.paddedUniv}
    {u₁ : Fin (P.numNodes 1)} (hz : z ∈ st.seeds.activeAt (P.paddedDom d) 1 hℓ u₁) :
    DeletePrefixPost scheme st
      (st.updateRoot u₁
        { (st.roots u₁) with table := (st.roots u₁).table.delete (st.seeds.idAt 1 le_rfl hℓ z) })
      d storeLvl (Function.update storeLvl z 0) 1 hℓ z := by
  have hinj := st.seeds.injOn_idAt_activeAt hwf.goodSeeds le_rfl hℓ u₁
  refine
    { seeds_eq := st.seeds_updateRoot_of_seed_eq _ _ rfl
      sentCount_eq := rfl
      storeLvl_zero_z := Function.update_self ..
      storeLvl_outside := fun w hw => by have := hwf.storeLvl_outside w; grind
      storeLvl_le_bounds := fun w hw hle => by have := hwf.storeLvl_bounds w; grind
      storeLvl_gt_eq := fun w hw _ => Function.update_of_ne (mem_erase.mp hw).1 ..
      above_dom_eq := fun j hj1 hjd hgt u =>
        st.nodeDom_updateRoot_other u₁ _ hj1 hjd u fun h_eq => by omega
      above_query_eq := fun j hj1 hjd hgt u k =>
        st.nodeQuery_updateRoot_other scheme u₁ _ hj1 hjd u k fun h_eq => by omega
      above_wait_eq := fun j hj2 hjd _ u => st.nodeWait_updateRoot u₁ _ hj2 hjd u
      le_dom_eq := fun j hj1 hjℓ u => by
        obtain rfl : j = 1 := by omega
        have hd := hwf.dom_eq 1 le_rfl hℓ u
        rw [nodeDom_one] at hd ⊢
        dsimp only [updateRoot]
        by_cases hu : u = u₁
        · subst hu
          rw [Function.update_self, StorageTable.dom_delete, hd,
            image_erase_of_injOn (filter_subset _ _) hinj hz]
          congr 1; grind [SeedAssignment.mem_activeAt_iff]
        · rw [Function.update_of_ne hu, hd]
          congr 1; grind [SeedAssignment.mem_activeAt_iff]
      le_query_eq := fun j hj1 hjℓ u w vw hdw hnw hslw => by
        obtain rfl : j = 1 := by omega
        obtain ⟨hwz, hdw, hwin⟩ := of_update_none_eq_some hdw
        rw [Function.update_of_ne hwz] at hslw
        have hq := hwf.query_eq_of_storeLvl 1 le_rfl hℓ u w vw hdw hnw hslw
        rw [nodeQuery_one] at hq ⊢
        dsimp only [updateRoot]
        by_cases hu : u = u₁
        · subst hu
          rw [Function.update_self, StorageTable.query_delete, Function.update_of_ne
            (hinj.ne (SeedAssignment.mem_activeAt_iff.mpr ⟨hwin, hnw⟩) hz hwz), hq]
        · rw [Function.update_of_ne hu, hq]
      le_inner_full := fun j hj2 _ hjℓ => by omega
      le_wait_dom_eq := fun j hj2 hjℓ => by omega
      le_wait_lookup_eq := fun j hj2 hjℓ => by omega }

/-- Branch 1 of `Algorithm 3`: once `z` is deleted from levels `1 .. m + 1`, removing its entry
from the waiting list of its level-`(m + 2)` node deletes it from levels `1 .. m + 2`. -/
private theorem DeletePrefixPost.removeWaitAtNode
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st st₁ : P.TreeState} {d : P.PaddedDict} {storeLvl storeLvl' : Fin P.paddedUniv → ℕ}
    {m : ℕ} {hℓ : m + 2 ≤ P.depth} {z : Fin P.paddedUniv}
    (hpost : DeletePrefixPost scheme st st₁ d storeLvl storeLvl' (m + 1) (by omega) z)
    (hwf : st.WellFormedPadded scheme d storeLvl) {u₀ : Fin (P.numNodes (m + 2))}
    (hz : z ∈ st.seeds.activeAt (P.paddedDom d) (m + 2) hℓ u₀) (hslz : storeLvl z < m + 2) :
    DeletePrefixPost scheme st
      (st₁.removeWaitAtNode (m + 2) (by omega) hℓ u₀ (st.seeds.idAt (m + 2) (by omega) hℓ z))
      d storeLvl storeLvl' (m + 2) hℓ z := by
  have h2 : 2 ≤ m + 2 := by omega
  have hinj := st.seeds.injOn_idAt_activeAt hwf.goodSeeds (by omega) hℓ u₀
  have hsl := fun w (hwz : w ≠ z) => hpost.storeLvl_iff hwf hwz (j := m + 2) (by omega)
  refine
    { seeds_eq := (st₁.seeds_removeWaitAtNode h2 hℓ ..).trans hpost.seeds_eq
      sentCount_eq := (st₁.sentCount_removeWaitAtNode h2 hℓ ..).trans hpost.sentCount_eq
      storeLvl_zero_z := hpost.storeLvl_zero_z
      storeLvl_outside := hpost.storeLvl_outside
      storeLvl_le_bounds := fun w hw hle => by
        have := hpost.storeLvl_le_bounds w hw; have := hpost.storeLvl_gt_eq w hw; omega
      storeLvl_gt_eq := fun w hw hgt => hpost.storeLvl_gt_eq w hw (by omega)
      above_dom_eq := fun j hj1 hjd hgt u =>
        (st₁.nodeDom_removeWaitAtNode h2 hℓ _ _ hj1 hjd u).trans
          (hpost.above_dom_eq j hj1 hjd (by omega) u)
      above_query_eq := fun j hj1 hjd hgt u k =>
        (st₁.nodeQuery_removeWaitAtNode scheme h2 hℓ _ _ hj1 hjd u k).trans
          (hpost.above_query_eq j hj1 hjd (by omega) u k)
      above_wait_eq := fun j hj2 hjd hgt u =>
        (st₁.nodeWait_removeWaitAtNode_other h2 hℓ _ _ hj2 hjd u fun h => by omega).trans
          (hpost.above_wait_eq j hj2 hjd (by omega) u)
      le_dom_eq := fun j hj1 hjℓ u => by
        rw [nodeDom_removeWaitAtNode]
        obtain rfl | hlt := hjℓ.eq_or_lt
        · rw [hpost.above_dom_eq (m + 2) hj1 hℓ (by omega) u, hwf.dom_eq (m + 2) hj1 hℓ u]
          congr 1; grind [SeedAssignment.mem_activeAt_iff]
        · exact hpost.le_dom_eq j hj1 (by omega) u
      le_query_eq := fun j hj1 hjℓ u w vw hdw hnw hslw => by
        rw [nodeQuery_removeWaitAtNode]
        obtain rfl | hlt := hjℓ.eq_or_lt
        · obtain ⟨hwz, hdw, -⟩ := of_update_none_eq_some hdw
          rw [hpost.above_query_eq (m + 2) hj1 hℓ (by omega) u]
          exact hwf.query_eq_of_storeLvl (m + 2) hj1 hℓ u w vw hdw hnw ((hsl w hwz).1.mp hslw)
        · exact hpost.le_query_eq j hj1 (by omega) u w vw hdw hnw hslw
      le_inner_full := fun j hj2 hjlt _ u => by
        rw [← nodeDom_inner _ (by omega) hj2 hjlt hjlt.le, nodeDom_removeWaitAtNode]
        exact hpost.card_nodeDom hwf hj2 hjlt u
      le_wait_dom_eq := fun j hj2 hjℓ u => ?_
      le_wait_lookup_eq := fun j hj2 hjℓ u w hw hslw => ?_ }
  -- waiting-list domains: only the list at `(m + 2, u₀)` loses `z`
  · obtain rfl | hlt := hjℓ.eq_or_lt
    · by_cases hu : u = u₀
      · subst hu
        rw [nodeWait_removeWaitAtNode_same, hpost.above_wait_eq (m + 2) h2 hℓ (by omega) u,
          WaitingList.dom_remove, hwf.wait_dom_eq (m + 2) h2 hℓ u,
          image_erase_of_injOn (filter_subset _ _) hinj hz]
        congr 1; grind [SeedAssignment.mem_activeAt_iff]
      · rw [nodeWait_removeWaitAtNode_other _ h2 hℓ _ _ h2 hℓ u fun _ => hu,
          hpost.above_wait_eq (m + 2) h2 hℓ (by omega) u, hwf.wait_dom_eq (m + 2) h2 hℓ u]
        congr 1; grind [SeedAssignment.mem_activeAt_iff]
    · rw [nodeWait_removeWaitAtNode_other _ h2 hℓ _ _ hj2 _ u fun h => by omega]
      exact hpost.le_wait_dom_eq j hj2 (by omega) u
  -- waiting-list lookups of the remaining keys are unchanged
  · obtain rfl | hlt := hjℓ.eq_or_lt
    · obtain ⟨hw_er, hnw⟩ := SeedAssignment.mem_activeAt_iff.mp hw
      obtain ⟨hwz, hwin⟩ := mem_erase.mp hw_er
      have hw_act := SeedAssignment.mem_activeAt_iff.mpr ⟨hwin, hnw⟩
      have hlk := hwf.wait_lookup_eq (m + 2) h2 hℓ u w hw_act ((hsl w hwz).2.mp hslw)
      by_cases hu : u = u₀
      · subst hu
        rw [nodeWait_removeWaitAtNode_same, hpost.above_wait_eq (m + 2) h2 hℓ (by omega) u,
          WaitingList.lookup_remove, Function.update_of_ne (hinj.ne hw_act hz hwz), hlk]
      · rw [nodeWait_removeWaitAtNode_other _ h2 hℓ _ _ h2 hℓ u fun _ => hu,
          hpost.above_wait_eq (m + 2) h2 hℓ (by omega) u, hlk]
    · rw [nodeWait_removeWaitAtNode_other _ h2 hℓ _ _ hj2 _ u fun h => by omega]
      exact hpost.le_wait_lookup_eq j hj2 (by omega) u w hw hslw

/-- Branch 2 of `Algorithm 3`: once a waiting key `y` of `z`'s level-`(m + 2)` node is deleted
from levels `1 .. m + 1`, replacing `z` by `y` in that node's table and dropping `y` from its
waiting list deletes `z` from levels `1 .. m + 2`. -/
private theorem DeletePrefixPost.replaceAtNode
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st st₁ : P.TreeState} {d : P.PaddedDict} {storeLvl storeLvl_y : Fin P.paddedUniv → ℕ}
    {m : ℕ} {hℓ : m + 2 ≤ P.depth} {y z : Fin P.paddedUniv} {vy : Fin P.valBound}
    (hpost : DeletePrefixPost scheme st st₁ d storeLvl storeLvl_y (m + 1) (by omega) y)
    (hwf : st.WellFormedPadded scheme d storeLvl) {u₀ : Fin (P.numNodes (m + 2))}
    (hz : z ∈ st.seeds.activeAt (P.paddedDom d) (m + 2) hℓ u₀) (hslz : storeLvl z = m + 2)
    (hy : y ∈ st.seeds.activeAt (P.paddedDom d) (m + 2) hℓ u₀) (hsly : storeLvl y < m + 2)
    (hdy : d y = some vy)
    {k : Fin (2 ^ P.idBits (m + 2))} (hk : st.seeds.idAt (m + 2) (by omega) hℓ y = k)
    {wait' : WaitingList (P.idBits (m + 2)) (P.idBits (m + 2 - 1)) (P.waitCap (m + 2))}
    (hwd : wait'.dom = (st.nodeWait (m + 2) (by omega) hℓ u₀).dom.erase k)
    (hwl : ∀ k', wait'.lookup k' =
      Function.update (st.nodeWait (m + 2) (by omega) hℓ u₀).lookup k none k') :
    DeletePrefixPost scheme st
      (st₁.replaceAtNode scheme (m + 2) (by omega) hℓ u₀ wait'
        (st.seeds.idAt (m + 2) (by omega) hℓ z) k (st.seeds.quotAt (m + 2) (by omega) hℓ y, vy))
      d storeLvl (Function.update (Function.update storeLvl_y y (m + 2)) z 0) (m + 2) hℓ z := by
  subst hk
  have h2 : 2 ≤ m + 2 := by omega
  have hinj := st.seeds.injOn_idAt_activeAt hwf.goodSeeds (by omega) hℓ u₀
  have hyz : y ≠ z := fun h => by subst h; omega
  have hsl := fun w (hwy : w ≠ y) => hpost.storeLvl_iff hwf hwy (j := m + 2) (by omega)
  obtain ⟨hold, hnew⟩ :
      st.seeds.idAt (m + 2) (by omega) hℓ z ∈ st₁.nodeDom (m + 2) (by omega) hℓ u₀ ∧
      st.seeds.idAt (m + 2) (by omega) hℓ y ∉ st₁.nodeDom (m + 2) (by omega) hℓ u₀ := by
    rw [hpost.above_dom_eq (m + 2) (by omega) hℓ (by omega) u₀,
      hwf.dom_eq (m + 2) (by omega) hℓ u₀, mem_image_filter_of_injOn hinj hz,
      mem_image_filter_of_injOn hinj hy]
    exact ⟨hslz, by omega⟩
  replace hnew := mt (mem_of_mem_erase (a := st.seeds.idAt (m + 2) (by omega) hℓ z)) hnew
  refine
    { seeds_eq := (st₁.seeds_replaceAtNode scheme h2 hℓ ..).trans hpost.seeds_eq
      sentCount_eq := (st₁.sentCount_replaceAtNode scheme h2 hℓ ..).trans hpost.sentCount_eq
      storeLvl_zero_z := Function.update_self ..
      storeLvl_outside := fun w hw => by
        have := hpost.storeLvl_outside w; grind [SeedAssignment.mem_activeAt_iff]
      storeLvl_le_bounds := fun w hw hle => by
        have := hpost.storeLvl_le_bounds w; have := hpost.storeLvl_gt_eq w; grind
      storeLvl_gt_eq := fun w hw hgt => by have := hpost.storeLvl_gt_eq w; grind
      above_dom_eq := fun j hj1 hjd hgt u =>
        (st₁.nodeDom_replaceAtNode_other scheme h2 hℓ _ _ _ _ _ hj1 hjd u fun h => by omega).trans
          (hpost.above_dom_eq j hj1 hjd (by omega) u)
      above_query_eq := fun j hj1 hjd hgt u k =>
        (st₁.nodeQuery_replaceAtNode_other scheme h2 hℓ _ _ _ _ _ hj1 hjd u k
          fun h => by omega).trans (hpost.above_query_eq j hj1 hjd (by omega) u k)
      above_wait_eq := fun j hj2 hjd hgt u =>
        (st₁.nodeWait_replaceAtNode_other scheme h2 hℓ _ _ _ _ _ hj2 hjd u fun h => by omega).trans
          (hpost.above_wait_eq j hj2 hjd (by omega) u)
      le_dom_eq := fun j hj1 hjℓ u => ?_
      le_query_eq := fun j hj1 hjℓ u w vw hdw hnw hslw => ?_
      le_inner_full := fun j hj2 hjlt hjℓ u => ?_
      le_wait_dom_eq := fun j hj2 hjℓ u => ?_
      le_wait_lookup_eq := fun j hj2 hjℓ u w hw hslw => ?_ }
  -- table domains: `(m + 2, u₀)` trades `z` for `y`; below, `y` is gone instead of `z`
  · obtain rfl | hlt := hjℓ.eq_or_lt
    · by_cases hu : u = u₀
      · subst hu
        rw [nodeDom_replaceAtNode_same scheme _ hj1 h2 hℓ _ _ _ _ _ hold hnew,
          hpost.above_dom_eq (m + 2) hj1 hℓ (by omega) u, hwf.dom_eq (m + 2) hj1 hℓ u,
          image_erase_of_injOn (filter_subset _ _) hinj hz, ← image_insert]
        congr 1; grind [SeedAssignment.mem_activeAt_iff]
      · rw [nodeDom_replaceAtNode_other scheme _ h2 hℓ _ _ _ _ _ hj1 hℓ u fun _ => hu,
          hpost.above_dom_eq (m + 2) hj1 hℓ (by omega) u, hwf.dom_eq (m + 2) hj1 hℓ u]
        congr 1; grind [SeedAssignment.mem_activeAt_iff]
    · rw [nodeDom_replaceAtNode_other scheme _ h2 hℓ _ _ _ _ _ hj1 _ u fun h => by omega,
        hpost.le_dom_eq j hj1 (by omega) u]
      congr 1; grind [SeedAssignment.mem_activeAt_iff]
  -- table queries: `y` reads its new entry, every other key reads its old one
  · obtain ⟨hwz, hdw, hwin⟩ := of_update_none_eq_some hdw
    have hw_act := SeedAssignment.mem_activeAt_iff.mpr ⟨hwin, hnw⟩
    rw [Function.update_of_ne hwz] at hslw
    by_cases hwy : w = y
    · subst hwy
      obtain rfl : m + 2 = j := by rwa [Function.update_self] at hslw
      obtain rfl : u = u₀ := hnw.symm.trans (SeedAssignment.mem_activeAt_iff.mp hy).2
      rw [nodeQuery_replaceAtNode_same scheme _ hj1 h2 hℓ _ _ _ _ _ _ hold hnew,
        Function.update_self, Option.some.inj (hdy.symm.trans hdw)]
    · rw [Function.update_of_ne hwy] at hslw
      obtain rfl | hlt := hjℓ.eq_or_lt
      · rw [← hwf.query_eq_of_storeLvl (m + 2) hj1 hℓ u w vw hdw hnw ((hsl w hwy).1.mp hslw),
          ← hpost.above_query_eq (m + 2) hj1 hℓ (by omega) u]
        by_cases hu : u = u₀
        · subst hu
          rw [nodeQuery_replaceAtNode_same scheme _ hj1 h2 hℓ _ _ _ _ _ _ hold hnew,
            Function.update_of_ne (hinj.ne hw_act hy hwy),
            Function.update_of_ne (hinj.ne hw_act hz hwz)]
        · exact nodeQuery_replaceAtNode_other scheme _ h2 hℓ _ _ _ _ _ hj1 hℓ u _ fun _ => hu
      · rw [nodeQuery_replaceAtNode_other scheme _ h2 hℓ _ _ _ _ _ hj1 _ u _ fun h => by omega]
        exact hpost.le_query_eq j hj1 (by omega) u w vw (by rwa [Function.update_of_ne hwy]) hnw
          hslw
  -- inner tables stay full: the replacement keeps the size of the table at `(m + 2, u₀)`
  · rw [← nodeDom_inner _ (by omega) hj2 hjlt hjlt.le, ← hpost.card_nodeDom hwf hj2 hjlt u]
    by_cases hsame : ∃ h : j = m + 2, h ▸ u = u₀
    · obtain ⟨rfl, rfl⟩ := hsame
      rw [nodeDom_replaceAtNode_same scheme _ _ h2 hℓ _ _ _ _ _ hold hnew,
        card_insert_of_notMem hnew, card_erase_add_one hold]
    · rw [nodeDom_replaceAtNode_other scheme _ h2 hℓ _ _ _ _ _ _ _ u (not_exists.mp hsame)]
  -- waiting-list domains: only the list at `(m + 2, u₀)` loses `y`
  · obtain rfl | hlt := hjℓ.eq_or_lt
    · by_cases hu : u = u₀
      · subst hu
        rw [nodeWait_replaceAtNode_same scheme _ (by omega) h2 hℓ _ _ _ _ _ hold hnew, hwd,
          hwf.wait_dom_eq (m + 2) h2 hℓ u, image_erase_of_injOn (filter_subset _ _) hinj hy]
        congr 1; grind [SeedAssignment.mem_activeAt_iff]
      · rw [nodeWait_replaceAtNode_other scheme _ h2 hℓ _ _ _ _ _ h2 hℓ u fun _ => hu,
          hpost.above_wait_eq (m + 2) h2 hℓ (by omega) u, hwf.wait_dom_eq (m + 2) h2 hℓ u]
        congr 1; grind [SeedAssignment.mem_activeAt_iff]
    · rw [nodeWait_replaceAtNode_other scheme _ h2 hℓ _ _ _ _ _ hj2 _ u fun h => by omega,
        hpost.le_wait_dom_eq j hj2 (by omega) u]
      congr 1; grind [SeedAssignment.mem_activeAt_iff]
  -- waiting-list lookups of the remaining keys are unchanged
  · obtain ⟨hw_er, hnw⟩ := SeedAssignment.mem_activeAt_iff.mp hw
    obtain ⟨hwz, hwin⟩ := mem_erase.mp hw_er
    have hw_act := SeedAssignment.mem_activeAt_iff.mpr ⟨hwin, hnw⟩
    rw [Function.update_of_ne hwz] at hslw
    have hwy : w ≠ y := fun h => by subst h; rw [Function.update_self] at hslw; omega
    rw [Function.update_of_ne hwy] at hslw
    obtain rfl | hlt := hjℓ.eq_or_lt
    · have hlk := hwf.wait_lookup_eq (m + 2) h2 hℓ u w hw_act ((hsl w hwy).2.mp hslw)
      by_cases hu : u = u₀
      · subst hu
        rw [nodeWait_replaceAtNode_same scheme _ (by omega) h2 hℓ _ _ _ _ _ hold hnew, hwl,
          Function.update_of_ne (hinj.ne hw_act hy hwy), hlk]
      · rw [nodeWait_replaceAtNode_other scheme _ h2 hℓ _ _ _ _ _ h2 hℓ u fun _ => hu,
          hpost.above_wait_eq (m + 2) h2 hℓ (by omega) u, hlk]
    · rw [nodeWait_replaceAtNode_other scheme _ h2 hℓ _ _ _ _ _ hj2 _ u fun h => by omega]
      exact hpost.le_wait_lookup_eq j hj2 (by omega) u w
        (SeedAssignment.mem_activeAt_iff.mpr ⟨mem_erase.mpr ⟨hwy, hwin⟩, hnw⟩) hslw

/-- **`Algorithm 3` correctness (`deleteAndGetQuotient_spec`)**: for any active key `z` at `(ℓ, u)`
with `storeLvl z ≤ ℓ` whose ancestors at levels `2 .. ℓ` strictly exceed `nLow j`,
`deleteAndGetQuotient` returns `(quotAt ℓ z, v_z)` and establishes `DeletePrefixPost` up to `ℓ`. -/
theorem deleteAndGetQuotient_spec
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) :
    ∀ (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
      (z : Fin P.paddedUniv) (vz : Fin P.valBound),
      d z = some vz →
      st.seeds.nodeAt ℓ hℓ z = u →
      storeLvl z ≤ ℓ →
      (∀ (j : ℕ) (_hj2 : 2 ≤ j) (hj : j ≤ ℓ),
        P.nLow j <
          (st.seeds.activeAt (P.paddedDom d) j (hj.trans hℓ) (P.ancestorAt hj u)).card) →
      let ⟨st', quot, val⟩ := st.deleteAndGetQuotient scheme ℓ h1 hℓ u (st.seeds.idAt ℓ h1 hℓ z)
      quot = st.seeds.quotAt ℓ h1 hℓ z ∧
      val = vz ∧
      ∃ storeLvl' : Fin P.paddedUniv → ℕ,
        DeletePrefixPost scheme st st' d storeLvl storeLvl' ℓ hℓ z := by
  intro ℓ
  induction ℓ with
  | zero => intro h1; omega
  | succ n ih =>
    intro h1 hℓ u_cur z vz hdz hnz hslz hloads
    have hz_in : z ∈ P.paddedDom d := (P.mem_paddedDom_iff d z).mpr (by simp [hdz])
    have hz_act := SeedAssignment.mem_activeAt_iff.mpr ⟨hz_in, hnz⟩
    cases n with
    | zero =>
      dsimp only [deleteAndGetQuotient]
      rw [← st.nodeQuery_one scheme le_rfl hℓ, hwf.query_eq_of_storeLvl 1 le_rfl hℓ u_cur z vz hdz
        hnz (le_antisymm hslz (hwf.storeLvl_bounds z hz_in).1), Option.getD_some]
      exact ⟨rfl, rfl, _, deletePrefixPost_updateRoot hwf hℓ hz_act⟩
    | succ m =>
      have h2 : 2 ≤ m + 2 := by omega
      have h1_prev : 1 ≤ m + 1 := by omega
      have hlt_prev : m + 1 < P.depth := by omega
      have hloads_prev := fun j (hj2 : 2 ≤ j) (hj : j ≤ m + 1) =>
        P.ancestorAt_succ hj u_cur ▸ hloads j hj2 (Nat.le_succ_of_le hj)
      have hprev := fun w (hw : st.seeds.nodeAt (m + 2) hℓ w = u_cur) =>
        hw ▸ (st.seeds.parentNode_nodeAt hℓ w).symm
      dsimp only [deleteAndGetQuotient]
      rcases hlk : (st.nodeWait (m + 2) h2 hℓ u_cur).lookup (st.seeds.idAt (m + 2) h1 hℓ z)
        with _ | z_id_prev
      -- Branch 2: `z` is NOT in the waiting list, so `storeLvl z = m + 2`
      · have hslz_eq : storeLvl z = m + 2 := by
          by_contra hne_lvl
          cases (hwf.wait_lookup_eq (m + 2) h2 hℓ u_cur z hz_act (by omega)).symm.trans hlk
        have hne_wait : (st.nodeWait (m + 2) h2 hℓ u_cur).dom.Nonempty := by
          have hload_cur := P.ancestorAt_refl u_cur ▸ hloads (m + 2) h2 le_rfl
          exact card_pos.mp (by rw [card_nodeWait_dom_eq hwf h2 hℓ u_cur]; omega)
        simp only [hwf.query_eq_of_storeLvl (m + 2) h1 hℓ u_cur z vz hdz hnz hslz_eq,
          Option.getD_some, dite_eq_left hne_wait]
        -- the popped entry belongs to some key `y` waiting at `u_cur`
        obtain ⟨y, hy_filt, hy_id⟩ := mem_image.mp
          (hwf.wait_dom_eq (m + 2) h2 hℓ u_cur ▸ WaitingList.pop_fst_mem_dom _ hne_wait)
        obtain ⟨hy_act, hsly⟩ := mem_filter.mp hy_filt
        obtain ⟨hy_in, hny⟩ := SeedAssignment.mem_activeAt_iff.mp hy_act
        obtain ⟨vy, hdy⟩ := Option.isSome_iff_exists.mp ((P.mem_paddedDom_iff d y).mp hy_in)
        have hy_prev : _ = some (st.seeds.idAt (m + 1) h1_prev hlt_prev.le y) :=
          hwf.wait_lookup_eq (m + 2) h2 hℓ u_cur y hy_act hsly
        rw [hy_id, WaitingList.lookup_pop_fst, Option.some.injEq] at hy_prev
        obtain ⟨hq_rec, hv_rec, storeLvl_y, hpost_y⟩ :=
          ih h1_prev hlt_prev.le _ y vy hdy (hprev y hny) (by omega) hloads_prev
        rw [hy_prev, hq_rec, hv_rec, stepCoordEquiv_quotAt st.seeds h1_prev hlt_prev u_cur y hny]
        exact ⟨trivial, trivial, _, hpost_y.replaceAtNode hwf hz_act hslz_eq hy_act hsly hdy hy_id
          (WaitingList.dom_pop_snd _ _) (WaitingList.lookup_pop_snd _ _)⟩
      -- Branch 1: `z` is in the waiting list, so `storeLvl z < m + 2`
      · have hslz_lt : storeLvl z < m + 2 := by
          have hmem := (WaitingList.isSome_lookup_iff _ _).mp (by rw [hlk]; rfl)
          rwa [hwf.wait_dom_eq (m + 2) h2 hℓ u_cur, mem_image_filter_of_injOn
            (st.seeds.injOn_idAt_activeAt hwf.goodSeeds h1 hℓ u_cur) hz_act] at hmem
        obtain rfl : st.seeds.idAt (m + 1) h1_prev hlt_prev.le z = z_id_prev := Option.some.inj
          ((hwf.wait_lookup_eq (m + 2) h2 hℓ u_cur z hz_act hslz_lt).symm.trans hlk)
        obtain ⟨hq_rec, hv_rec, storeLvl', hpost_z⟩ :=
          ih h1_prev hlt_prev.le _ z vz hdz (hprev z hnz) (by omega) hloads_prev
        dsimp only
        rw [hq_rec, stepCoordEquiv_quotAt st.seeds h1_prev hlt_prev u_cur z hnz]
        exact ⟨rfl, hv_rec, _, hpost_z.removeWaitAtNode hwf hz_act hslz_lt⟩

/-- Normal-path deletion of an active internal key `z ∈ P.paddedDom d`, invoking `Algorithm 3`
starting at the leaf `(depth, nodeAt depth z)` (`Section 5.3`, PDF p. 31 / printed p. 30).
Carries a member-only contract (`z ∈ P.paddedDom d` on a `WellFormedPadded` state; `Algorithm 3`
routes by compressed ID and is not a no-op on absent keys or malformed states). -/
noncomputable def normalDeleteMem
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (z : Fin P.paddedUniv) : P.TreeState :=
  (st.deleteAndGetQuotient scheme P.depth (Nat.one_le_of_lt P.two_le_depth) le_rfl
    (st.seeds.nodeAt P.depth le_rfl z)
    (st.seeds.idAt P.depth (Nat.one_le_of_lt P.two_le_depth) le_rfl z)).1

/-- **Normal-path deletion preserves `WellFormedPadded`** whenever `z ∈ P.paddedDom d` and all
current node seeds remain good on `(P.paddedDom d).erase z`. -/
theorem wellFormedPadded_normalDeleteMem
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) {z : Fin P.paddedUniv}
    (hz : z ∈ P.paddedDom d)
    (hgood' : st.seeds.AllGoodSeeds ((P.paddedDom d).erase z)) :
    (st.normalDeleteMem scheme z).sentCount = st.sentCount ∧
    (st.normalDeleteMem scheme z).seeds = st.seeds ∧
    ∃ storeLvl' : Fin P.paddedUniv → ℕ,
      (st.normalDeleteMem scheme z).WellFormedPadded scheme
        (Function.update d z none) storeLvl' := by
  obtain ⟨vz, hdz⟩ := Option.isSome_iff_exists.mp ((P.mem_paddedDom_iff d z).mp hz)
  have hloads : ∀ (j : ℕ) (_hj2 : 2 ≤ j) (hj : j ≤ P.depth),
      P.nLow j <
        (st.seeds.activeAt (P.paddedDom d) j hj
          (P.ancestorAt hj (st.seeds.nodeAt P.depth le_rfl z))).card := by
    intro j _ hj
    rw [st.seeds.ancestorAt_nodeAt hj le_rfl z]
    have hlo := (st.seeds.load_bounds_of_allGoodSeeds hgood' hj (st.seeds.nodeAt j hj z)).1
    rw [SeedAssignment.activeAt, filter_erase] at hlo
    exact hlo.trans_lt (card_erase_lt_of_mem (SeedAssignment.mem_activeAt_iff.mpr ⟨hz, rfl⟩))
  obtain ⟨_, _, storeLvl', hpost⟩ := deleteAndGetQuotient_spec hwf P.depth
    (Nat.one_le_of_lt P.two_le_depth) le_rfl _ z vz hdz rfl (hwf.storeLvl_bounds z hz).2 hloads
  dsimp only [normalDeleteMem]
  refine ⟨hpost.sentCount_eq, hpost.seeds_eq, storeLvl', ?_⟩
  -- after rewriting the seeds and the padded domain, each field is a field of `hpost`
  constructor <;> try simp only [hpost.seeds_eq, P.paddedDom_update_none]
  exacts [hgood', fun w hw => hpost.storeLvl_le_bounds w hw
    (hwf.storeLvl_bounds w (mem_of_mem_erase hw)).2, hpost.storeLvl_outside, hpost.le_dom_eq,
    hpost.le_query_eq, fun ℓ h2 hlt u => hpost.le_inner_full ℓ h2 hlt hlt.le u,
    hpost.le_wait_dom_eq, hpost.le_wait_lookup_eq]

end TreeSchedule.TreeState

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
