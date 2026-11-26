/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.TreeQuery

/-!
# Normal-Path Fresh Insertion in the Multi-Level Dictionary Tree

This file formalizes collision- and overflow-free fresh insertion (`normalInsertFresh`) for the
subconstant-redundancy dictionary tree of Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou,
*Dynamic Dictionary with Subconstant Wasted Bits per Key* ([LiLiangYuZhou2024, Section 5.3];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 30–31 / printed pp. 29–30).

When all node seeds remain good on `Insert.insert x (P.paddedDom d)`, `normalInsertFresh` stores
`(x_quot^[1], v)` directly in the level-1 root storage table at `u_1 = nodeAt 1 x` and pushes
`(x_id^[ℓ], x_id^[ℓ - 1])` onto the waiting list of every visited node `u_ℓ = nodeAt ℓ x` across
levels `2 ≤ ℓ ≤ depth`.

## Main definitions

* `TreeSchedule.TreeState.normalInsertFresh`: normal-path fresh key insertion.
* `TreeSchedule.TreeState.removeWaitAtNode`: helper for Algorithm 3 (`deleteAndGetQuotient`)
  removing a waiting entry at an intermediate node.
* `TreeSchedule.TreeState.replaceAtNode`: helper for Algorithm 3 replacing a popped quotient at a
  node.

## Main results

* `TreeSchedule.TreeState.wellFormedPadded_normalInsertFresh`: preservation of `WellFormedPadded`
  with storage-level map `Function.update storeLvl x 1`.
* `TreeSchedule.TreeState.seeds_removeWaitAtNode`,
  `TreeSchedule.TreeState.sentCount_removeWaitAtNode`,
  `TreeSchedule.TreeState.nodeDom_removeWaitAtNode`,
  `TreeSchedule.TreeState.nodeQuery_removeWaitAtNode`,
  `TreeSchedule.TreeState.nodeWait_removeWaitAtNode_same`,
  `TreeSchedule.TreeState.nodeWait_removeWaitAtNode_other`: node-component frame equations after
  removing a waiting entry during Algorithm 3.
* `TreeSchedule.TreeState.seeds_replaceAtNode`,
  `TreeSchedule.TreeState.sentCount_replaceAtNode`,
  `TreeSchedule.TreeState.nodeDom_replaceAtNode_same`,
  `TreeSchedule.TreeState.nodeDom_replaceAtNode_other`,
  `TreeSchedule.TreeState.nodeQuery_replaceAtNode_same`,
  `TreeSchedule.TreeState.nodeQuery_replaceAtNode_other`,
  `TreeSchedule.TreeState.nodeWait_replaceAtNode_same`,
  `TreeSchedule.TreeState.nodeWait_replaceAtNode_other`: node-component update and frame equations
  after quotient replacement during Algorithm 3.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Finset

namespace TreeSchedule.TreeState

variable {P : TreeSchedule}

/-- Normal-path insertion of a fresh internal key `x ∉ P.paddedDom d` when all current node seeds
remain good on `Insert.insert x (P.paddedDom d)` (`Section 5.3`, PDF pp. 30–31 / printed
pp. 29–30): stores `(q_1, v)` at the root `u_1` and pushes `(x_id^[ℓ], x_id^[ℓ - 1])` onto each
visited node's waiting list at `2 ≤ ℓ ≤ depth`. -/
noncomputable def normalInsertFresh
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (x : Fin P.paddedUniv) (v : Fin P.valBound) (hx_fresh : x ∉ P.paddedDom d)
    (hgood' : st.seeds.AllGoodSeeds (Insert.insert x (P.paddedDom d))) : P.TreeState :=
  let h1d : 1 ≤ P.depth := Nat.one_le_of_lt P.two_le_depth
  let u₁ := st.seeds.nodeAt 1 h1d x
  let id₁ := st.seeds.idAt 1 le_rfl h1d x
  let q₁ := st.seeds.quotAt 1 le_rfl h1d x
  have hact_ins : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ P.depth),
      st.seeds.activeAt (Insert.insert x (P.paddedDom d)) ℓ hℓ (st.seeds.nodeAt ℓ hℓ x) =
        Insert.insert x (st.seeds.activeAt (P.paddedDom d) ℓ hℓ (st.seeds.nodeAt ℓ hℓ x)) := by
    intro ℓ hℓ; ext y
    simp only [SeedAssignment.mem_activeAt_iff, mem_insert]
    constructor
    · rintro ⟨rfl | hy, hny⟩
      · left; rfl
      · right; exact ⟨hy, hny⟩
    · rintro (rfl | ⟨hy, hny⟩)
      · exact ⟨Or.inl rfl, rfl⟩
      · exact ⟨Or.inr hy, hny⟩
  have hnotMem_act : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ P.depth),
      x ∉ st.seeds.activeAt (P.paddedDom d) ℓ hℓ (st.seeds.nodeAt ℓ hℓ x) := fun ℓ hℓ h =>
    hx_fresh (SeedAssignment.mem_activeAt_iff.mp h).1
  have hroot_cap : (st.roots u₁).table.tableMeta.dom.card < P.tableCap 1 := by
    have hsum1 := card_root_dom_add_eq hwf u₁
    have hhi1 := (st.seeds.load_bounds_of_allGoodSeeds hgood' h1d u₁).2
    dsimp only [u₁] at hsum1 hhi1 ⊢
    rw [hact_ins 1 h1d, card_insert_of_notMem (hnotMem_act 1 h1d)] at hhi1
    have hcap1 : P.tableCap 1 = P.nHigh 1 - P.branchFactor 1 * P.nLow 2 := by
      dsimp only [tableCap]; rw [ite_eq_left rfl]
    omega
  have hid₁_notMem : id₁ ∉ (st.roots u₁).table.tableMeta.dom := by
    intro hmem
    have hdom1 := hwf.dom_eq 1 le_rfl h1d u₁
    rw [nodeDom_one] at hdom1
    rw [hdom1] at hmem
    obtain ⟨y, hy_filt, hid_eq⟩ := mem_image.mp hmem
    have hy_act := (mem_filter.mp hy_filt).1
    have hinj := st.seeds.injOn_idAt_activeAt hgood' le_rfl h1d u₁
    dsimp only [u₁, id₁] at hy_act hinj hid_eq
    rw [hact_ins 1 h1d] at hinj
    have hyx := hinj (mem_insert_of_mem hy_act) (mem_insert_self x _) hid_eq
    exact hnotMem_act 1 h1d (hyx ▸ hy_act)
  have hwait_cap : ∀ (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth),
      (st.nodeWait ℓ h2 hℓ (st.seeds.nodeAt ℓ hℓ x)).entries.length + 1 ≤ P.waitCap ℓ := by
    intro ℓ h2 hℓ
    rw [← WaitingList.card_dom, card_nodeWait_dom_eq hwf h2 hℓ]
    have hlo := (st.seeds.load_bounds_of_allGoodSeeds hwf.goodSeeds hℓ (st.seeds.nodeAt ℓ hℓ x)).1
    have hhi := (st.seeds.load_bounds_of_allGoodSeeds hgood' hℓ (st.seeds.nodeAt ℓ hℓ x)).2
    rw [hact_ins ℓ hℓ, card_insert_of_notMem (hnotMem_act ℓ hℓ)] at hhi
    have hdiff := P.nHigh_sub_nLow (by omega : 1 ≤ ℓ) hℓ
    omega
  have hwait_notMem : ∀ (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth),
      st.seeds.idAt ℓ (by omega) hℓ x ∉
        (st.nodeWait ℓ h2 hℓ (st.seeds.nodeAt ℓ hℓ x)).dom := by
    intro ℓ h2 hℓ hmem
    rw [hwf.wait_dom_eq ℓ h2 hℓ] at hmem
    obtain ⟨y, hy_filt, hid_eq⟩ := mem_image.mp hmem
    have hy_act := (mem_filter.mp hy_filt).1
    have hinj := st.seeds.injOn_idAt_activeAt hgood' (by omega) hℓ (st.seeds.nodeAt ℓ hℓ x)
    rw [hact_ins ℓ hℓ] at hinj
    have hyx := hinj (mem_insert_of_mem hy_act) (mem_insert_self x _) hid_eq
    exact hnotMem_act ℓ hℓ (hyx ▸ hy_act)
  let u_d := st.seeds.nodeAt P.depth le_rfl x
  let ln := st.leaves u_d
  have hwc_d : ln.leafMeta.wait.entries.length + 1 ≤ P.waitCap P.depth := by
    simpa only [nodeWait_depth] using hwait_cap P.depth P.two_le_depth le_rfl
  have hwn_d : st.seeds.idAt P.depth h1d le_rfl x ∉ ln.leafMeta.wait.dom := by
    simpa only [nodeWait_depth] using hwait_notMem P.depth P.two_le_depth le_rfl
  { topSeed := st.topSeed
    roots := Function.update st.roots u₁
      { (st.roots u₁) with table := (st.roots u₁).table.insert id₁ (q₁, v) hroot_cap hid₁_notMem }
    inner := fun ℓ h2 hlt u =>
      if hu : u = st.seeds.nodeAt ℓ hlt.le x then
        have hwc : (st.inner ℓ h2 hlt u).wait.entries.length + 1 ≤ P.waitCap ℓ := by
          subst hu; simpa only [nodeWait_inner _ h2 hlt hlt.le] using hwait_cap ℓ h2 hlt.le
        have hwn : st.seeds.idAt ℓ (by omega) hlt.le x ∉ (st.inner ℓ h2 hlt u).wait.dom := by
          subst hu; simpa only [nodeWait_inner _ h2 hlt hlt.le] using hwait_notMem ℓ h2 hlt.le
        { (st.inner ℓ h2 hlt u) with
          wait := (st.inner ℓ h2 hlt u).wait.push
            (st.seeds.idAt ℓ (by omega) hlt.le x)
            (st.seeds.idAt (ℓ - 1) (by omega) (by omega) x) hwc hwn }
      else st.inner ℓ h2 hlt u
    leaves := Function.update st.leaves u_d
      { ln with
        leafMeta :=
          { ln.leafMeta with
            wait := ln.leafMeta.wait.push (st.seeds.idAt P.depth h1d le_rfl x)
              (st.seeds.idAt (P.depth - 1) (by have := P.two_le_depth; omega) (by omega) x)
              hwc_d hwn_d } }
    sentCount := st.sentCount }

theorem seeds_normalInsertFresh
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (x : Fin P.paddedUniv) (v : Fin P.valBound) (hx_fresh : x ∉ P.paddedDom d)
    (hgood' : st.seeds.AllGoodSeeds (Insert.insert x (P.paddedDom d))) :
    (st.normalInsertFresh hwf x v hx_fresh hgood').seeds = st.seeds := by
  ext ℓ hℓ u
  rcases eq_or_ne ℓ 0 with rfl | h0
  · simp [normalInsertFresh]
  rcases eq_or_ne ℓ 1 with rfl | h1
  · simp only [seeds_one, normalInsertFresh]
    by_cases hu : u = st.seeds.nodeAt 1 hℓ x <;> simp [hu]
  rcases lt_or_eq_of_le hℓ with hlt | rfl
  · simp only [seeds_inner _ (by omega) hlt hℓ, normalInsertFresh]
    split_ifs <;> rfl
  · simp only [seeds_depth, normalInsertFresh]
    by_cases hu : u = st.seeds.nodeAt P.depth le_rfl x <;> simp [hu]

theorem sentCount_normalInsertFresh
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (x : Fin P.paddedUniv) (v : Fin P.valBound) (hx_fresh : x ∉ P.paddedDom d)
    (hgood' : st.seeds.AllGoodSeeds (Insert.insert x (P.paddedDom d))) :
    (st.normalInsertFresh hwf x v hx_fresh hgood').sentCount = st.sentCount := by
  unfold normalInsertFresh; rfl

/-- `normalInsertFresh` leaves the waiting list of every node other than `nodeAt ℓ x`
unchanged. -/
private theorem nodeWait_normalInsertFresh_of_ne
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (x : Fin P.paddedUniv) (v : Fin P.valBound) (hx_fresh : x ∉ P.paddedDom d)
    (hgood' : st.seeds.AllGoodSeeds (Insert.insert x (P.paddedDom d)))
    {ℓ : ℕ} (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) {u : Fin (P.numNodes ℓ)}
    (hu : u ≠ st.seeds.nodeAt ℓ hℓ x) :
    (st.normalInsertFresh hwf x v hx_fresh hgood').nodeWait ℓ h2 hℓ u = st.nodeWait ℓ h2 hℓ u := by
  by_cases hlt : ℓ < P.depth
  · simp only [nodeWait_inner _ h2 hlt, normalInsertFresh, dite_eq_right hu]
  · obtain rfl : ℓ = P.depth := by omega
    simp only [nodeWait_depth, normalInsertFresh, Function.update_of_ne hu]

/-- `normalInsertFresh` pushes `(x_id^[ℓ], x_id^[ℓ - 1])` onto the waiting list of
`nodeAt ℓ x`. -/
private theorem nodeWait_normalInsertFresh_self
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (x : Fin P.paddedUniv) (v : Fin P.valBound) (hx_fresh : x ∉ P.paddedDom d)
    (hgood' : st.seeds.AllGoodSeeds (Insert.insert x (P.paddedDom d)))
    {ℓ : ℕ} (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) :
    ((st.normalInsertFresh hwf x v hx_fresh hgood').nodeWait ℓ h2 hℓ
        (st.seeds.nodeAt ℓ hℓ x)).dom =
        Insert.insert (st.seeds.idAt ℓ (by omega) hℓ x)
          (st.nodeWait ℓ h2 hℓ (st.seeds.nodeAt ℓ hℓ x)).dom ∧
      ((st.normalInsertFresh hwf x v hx_fresh hgood').nodeWait ℓ h2 hℓ
        (st.seeds.nodeAt ℓ hℓ x)).lookup =
        Function.update (st.nodeWait ℓ h2 hℓ (st.seeds.nodeAt ℓ hℓ x)).lookup
          (st.seeds.idAt ℓ (by omega) hℓ x)
          (some (st.seeds.idAt (ℓ - 1) (by omega) (by omega) x)) := by
  by_cases hlt : ℓ < P.depth
  · simp only [nodeWait_inner _ h2 hlt, normalInsertFresh]
    exact ⟨WaitingList.dom_push .., funext fun _ => WaitingList.lookup_push ..⟩
  · obtain rfl : ℓ = P.depth := by omega
    simp only [nodeWait_depth, normalInsertFresh, Function.update_self]
    exact ⟨WaitingList.dom_push .., funext fun _ => WaitingList.lookup_push ..⟩

/-- **Normal-path fresh insertion preserves `WellFormedPadded`** (`storeLvl` extended with
`x ↦ 1`). -/
theorem wellFormedPadded_normalInsertFresh
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (x : Fin P.paddedUniv) (v : Fin P.valBound) (hx_fresh : x ∉ P.paddedDom d)
    (hgood' : st.seeds.AllGoodSeeds (Insert.insert x (P.paddedDom d))) :
    (st.normalInsertFresh hwf x v hx_fresh hgood').WellFormedPadded scheme
      (Function.update d x (some v)) (Function.update storeLvl x 1) := by
  set st' := st.normalInsertFresh hwf x v hx_fresh hgood'
  have hseeds : st'.seeds = st.seeds :=
    st.seeds_normalInsertFresh hwf x v hx_fresh hgood'
  have hdom_upd : P.paddedDom (Function.update d x (some v)) = Insert.insert x (P.paddedDom d) :=
    P.paddedDom_update_some d x v
  have h1d : 1 ≤ P.depth := Nat.one_le_of_lt P.two_le_depth
  have hx_act : ∀ ℓ (hℓ : ℓ ≤ P.depth),
      x ∈ st.seeds.activeAt (Insert.insert x (P.paddedDom d)) ℓ hℓ (st.seeds.nodeAt ℓ hℓ x) :=
    fun _ _ => SeedAssignment.mem_activeAt_iff.mpr ⟨mem_insert_self x _, rfl⟩
  refine
    { goodSeeds := by rw [hseeds, hdom_upd]; exact hgood'
      storeLvl_bounds := fun y hy => by
        rw [hdom_upd, mem_insert] at hy
        rcases hy with rfl | hy_old
        · simp [h1d]
        · rw [Function.update_of_ne (ne_of_mem_of_not_mem hy_old hx_fresh)]
          exact hwf.storeLvl_bounds y hy_old
      storeLvl_outside := fun y hy => by
        rw [hdom_upd, mem_insert, not_or] at hy
        simpa only [Function.update_of_ne hy.1] using hwf.storeLvl_outside y hy.2
      dom_eq := fun ℓ h1 hℓ u => ?_
      query_eq_of_storeLvl := fun ℓ h1 hℓ u y vy hdy hny hsly => ?_
      inner_full := fun ℓ h2 hlt u => by
        dsimp only [st', normalInsertFresh]
        split_ifs <;> exact hwf.inner_full ℓ h2 hlt u
      wait_dom_eq := fun ℓ h2 hℓ u => ?_
      wait_lookup_eq := fun ℓ h2 hℓ u y hy hsly => ?_ }
  · rw [hseeds, hdom_upd]
    by_cases h_one : ℓ = 1
    · subst h_one
      have hd_old := hwf.dom_eq 1 le_rfl hℓ u
      rw [nodeDom_one] at hd_old ⊢
      dsimp only [st', normalInsertFresh]
      rw [Function.update_apply]
      split_ifs with hu
      · subst hu
        rw [StorageTable.dom_insert, hd_old, ← image_insert]; congr 1; ext y
        by_cases hyx : y = x <;> simp [SeedAssignment.mem_activeAt_iff, hyx]
      · rw [hd_old]; congr 1; ext y
        by_cases hyx : y = x <;> simp [SeedAssignment.mem_activeAt_iff, hyx, Ne.symm hu]
    · have hf_eq : ((st.seeds.activeAt (Insert.insert x (P.paddedDom d)) ℓ hℓ u).filter
          fun y => Function.update storeLvl x 1 y = ℓ) =
          (st.seeds.activeAt (P.paddedDom d) ℓ hℓ u).filter fun y => storeLvl y = ℓ := by
        ext y
        by_cases hyx : y = x <;>
          simp [SeedAssignment.mem_activeAt_iff, hyx, hx_fresh, Ne.symm h_one]
      rw [hf_eq, ← hwf.dom_eq ℓ h1 hℓ u]
      by_cases hlt : ℓ < P.depth
      · simp only [nodeDom_inner _ h1 (by omega) hlt hℓ]
        dsimp only [st', normalInsertFresh]; split_ifs <;> rfl
      · obtain rfl : ℓ = P.depth := by omega
        rcases eq_or_ne u (st.seeds.nodeAt P.depth le_rfl x) with rfl | hu
        · simp only [nodeDom_depth, st', normalInsertFresh, Function.update_self]; rfl
        · simp only [nodeDom_depth, st', normalInsertFresh, Function.update_of_ne hu]
  · rw [hseeds] at hny ⊢
    by_cases h_one : ℓ = 1
    · subst h_one
      rw [nodeQuery_one]
      dsimp only [st', normalInsertFresh]
      by_cases hyx : y = x
      · subst y
        rw [Function.update_self, Option.some.injEq] at hdy
        subst hdy hny
        rw [Function.update_self, StorageTable.query_insert, Function.update_self]
      · rw [Function.update_of_ne hyx] at hdy hsly
        have hy_old := hwf.query_eq_of_storeLvl 1 le_rfl hℓ u y vy hdy hny hsly
        rw [nodeQuery_one] at hy_old
        rw [Function.update_apply]; split_ifs with hu
        · subst hu
          have hy_in : y ∈ P.paddedDom d := (P.mem_paddedDom_iff d y).mpr (by simp [hdy])
          have hid_ne : st.seeds.idAt 1 le_rfl h1d y ≠ st.seeds.idAt 1 le_rfl h1d x := fun h =>
            hyx (st.seeds.injOn_idAt_activeAt hgood' le_rfl h1d _
              (SeedAssignment.mem_activeAt_iff.mpr ⟨mem_insert_of_mem hy_in, hny⟩) (hx_act 1 h1d) h)
          rw [StorageTable.query_insert, Function.update_of_ne hid_ne, hy_old]
        · exact hy_old
    · have hyx : y ≠ x := by rintro rfl; rw [Function.update_self] at hsly; omega
      rw [Function.update_of_ne hyx] at hdy hsly
      have hy_old := hwf.query_eq_of_storeLvl ℓ h1 hℓ u y vy hdy hny hsly
      by_cases hlt : ℓ < P.depth
      · rw [nodeQuery_inner _ _ h1 (by omega) hlt hℓ] at hy_old ⊢
        dsimp only [st', normalInsertFresh]; split_ifs <;> exact hy_old
      · obtain rfl : ℓ = P.depth := by omega
        rw [nodeQuery_depth] at hy_old ⊢
        dsimp only [st', normalInsertFresh]
        rw [Function.update_apply]; split_ifs with hu
        · subst hu; exact hy_old
        · exact hy_old
  · rw [hseeds, hdom_upd]
    have hw_old := hwf.wait_dom_eq ℓ h2 hℓ u
    by_cases hu : u = st.seeds.nodeAt ℓ hℓ x
    · subst hu
      rw [(nodeWait_normalInsertFresh_self st hwf x v hx_fresh hgood' h2 hℓ).1, hw_old,
        ← image_insert]
      congr 1; ext y
      by_cases hyx : y = x <;>
        simp [SeedAssignment.mem_activeAt_iff, hyx, Nat.one_lt_two.trans_le h2]
    · rw [nodeWait_normalInsertFresh_of_ne st hwf x v hx_fresh hgood' h2 hℓ hu, hw_old]
      congr 1; ext y
      by_cases hyx : y = x <;> simp [SeedAssignment.mem_activeAt_iff, hyx, Ne.symm hu]
  · rw [hseeds, hdom_upd] at hy
    rw [hseeds]
    obtain ⟨hy_ins, hny⟩ := SeedAssignment.mem_activeAt_iff.mp hy
    by_cases hyx : y = x
    · subst y; subst hny
      rw [(nodeWait_normalInsertFresh_self st hwf x v hx_fresh hgood' h2 hℓ).2,
        Function.update_self]
    · have hy_dom : y ∈ P.paddedDom d := (mem_insert.mp hy_ins).resolve_left hyx
      rw [Function.update_of_ne hyx] at hsly
      have hy_old := hwf.wait_lookup_eq ℓ h2 hℓ u y
        (SeedAssignment.mem_activeAt_iff.mpr ⟨hy_dom, hny⟩) hsly
      by_cases hu : u = st.seeds.nodeAt ℓ hℓ x
      · subst hu
        have hid_ne : st.seeds.idAt ℓ (by omega) hℓ y ≠ st.seeds.idAt ℓ (by omega) hℓ x :=
          fun h => hyx (st.seeds.injOn_idAt_activeAt hgood' (by omega) hℓ _ hy (hx_act ℓ hℓ) h)
        rw [(nodeWait_normalInsertFresh_self st hwf x v hx_fresh hgood' h2 hℓ).2,
          Function.update_of_ne hid_ne, hy_old]
      · rw [nodeWait_normalInsertFresh_of_ne st hwf x v hx_fresh hgood' h2 hℓ hu, hy_old]

/-! ## Section 1: Uniform node helpers for `Algorithm 3` (`removeWaitAtNode`, `replaceAtNode`) -/

private def removeWaitLeafAt (st : P.TreeState) (u : Fin (P.numNodes P.depth))
    (k : Fin (2 ^ P.idBits P.depth)) : P.TreeState :=
  let ln := st.leaves u
  st.updateLeaf u
    { ln with leafMeta := { ln.leafMeta with wait := ln.leafMeta.wait.remove k } }

/-- Remove `k` from the waiting list of node `(L, uL)` (`2 ≤ L ≤ depth`). -/
def removeWaitAtNode (st : P.TreeState) (L : ℕ) (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L)) : P.TreeState :=
  if hlt : L < P.depth then
    let nd := st.inner L h2L hlt uL
    st.updateInner L h2L hlt uL { nd with wait := nd.wait.remove k }
  else
    have hd : L = P.depth := by omega
    Eq.ndrec
      (motive := fun m => Fin (P.numNodes m) → Fin (2 ^ P.idBits m) → P.TreeState)
      (removeWaitLeafAt st) hd.symm uL k

private theorem removeWaitAtNode_cases (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L)
    (hLL : L ≤ P.depth) (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L)) :
    let st' := st.removeWaitAtNode L h2L hLL uL k
    (∃ (hlt : L < P.depth) (nd : P.InnerNode L),
      nd.seed = (st.inner L h2L hlt uL).seed ∧
      nd.table = (st.inner L h2L hlt uL).table ∧
      st' = st.updateInner L h2L hlt uL nd) ∨
    (∃ (hd : L = P.depth) (ln : P.LeafNode),
      ln.leafMeta.seed = (st.leaves (hd ▸ uL)).leafMeta.seed ∧
      ln.toFixedEncoded = (st.leaves (hd ▸ uL)).toFixedEncoded ∧
      st' = st.updateLeaf (hd ▸ uL) ln) := by
  dsimp only [removeWaitAtNode]
  by_cases hLlt : L < P.depth
  · rw [dite_eq_left hLlt]
    refine Or.inl ⟨hLlt, _, ?_, ?_, rfl⟩ <;> rfl
  · obtain rfl : L = P.depth := by omega
    rw [dite_eq_right (lt_irrefl _)]; dsimp only [removeWaitLeafAt]
    refine Or.inr ⟨rfl, _, ?_, ?_, rfl⟩ <;> rfl

theorem seeds_removeWaitAtNode (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L)) :
    (st.removeWaitAtNode L h2L hLL uL k).seeds = st.seeds := by
  rcases st.removeWaitAtNode_cases h2L hLL uL k with
    ⟨hlt, nd, hs, _, h⟩ | ⟨rfl, ln, hs, _, h⟩
  · rw [h]; exact st.seeds_updateInner_of_seed_eq h2L hlt uL nd hs
  · rw [h]; exact st.seeds_updateLeaf_of_seed_eq uL ln hs

theorem sentCount_removeWaitAtNode (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L)) :
    (st.removeWaitAtNode L h2L hLL uL k).sentCount = st.sentCount := by
  rcases st.removeWaitAtNode_cases h2L hLL uL k with
    ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ <;> rw [h] <;> rfl

theorem nodeDom_removeWaitAtNode (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) :
    (st.removeWaitAtNode L h2L hLL uL k).nodeDom ℓ h1 hℓ u = st.nodeDom ℓ h1 hℓ u := by
  by_cases hsame : ∃ h_eq : ℓ = L, h_eq ▸ u = uL
  · obtain ⟨rfl, rfl⟩ := hsame
    rcases st.removeWaitAtNode_cases h2L hLL u k with
      ⟨hlt, nd, _, htbl, h⟩ | ⟨rfl, ln, _, hfe, h⟩
    · simp [h, nodeDom_inner _ h1 h2L hlt hℓ, updateInner, htbl]
    · simp [h, LeafNode.dom, updateLeaf, hfe]
  · rcases st.removeWaitAtNode_cases h2L hLL uL k with ⟨hlt, nd, _, _, h⟩ | ⟨rfl, ln, _, _, h⟩
    exacts [h.symm ▸ st.nodeDom_updateInner_other h2L hlt uL nd h1 hℓ u (not_exists.mp hsame),
      h.symm ▸ st.nodeDom_updateLeaf_other uL ln h1 hℓ u (not_exists.mp hsame)]

theorem nodeQuery_removeWaitAtNode
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (k' : Fin (2 ^ P.idBits ℓ)) :
    (st.removeWaitAtNode L h2L hLL uL k).nodeQuery scheme ℓ h1 hℓ u k' =
      st.nodeQuery scheme ℓ h1 hℓ u k' := by
  by_cases hsame : ∃ h_eq : ℓ = L, h_eq ▸ u = uL
  · obtain ⟨rfl, rfl⟩ := hsame
    rcases st.removeWaitAtNode_cases h2L hLL u k with
      ⟨hlt, nd, _, htbl, h⟩ | ⟨rfl, ln, _, hfe, h⟩
    · simp [h, nodeQuery_inner _ _ h1 h2L hlt hℓ, updateInner, htbl]
    · simp [h, LeafNode.query, updateLeaf, hfe]
  · rcases st.removeWaitAtNode_cases h2L hLL uL k with ⟨hlt, nd, _, _, h⟩ | ⟨rfl, ln, _, _, h⟩
    exacts [h.symm ▸ st.nodeQuery_updateInner_other scheme h2L hlt uL nd h1 hℓ u k'
      (not_exists.mp hsame),
      h.symm ▸ st.nodeQuery_updateLeaf_other scheme uL ln h1 hℓ u k' (not_exists.mp hsame)]

theorem nodeWait_removeWaitAtNode_same (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L)
    (hLL : L ≤ P.depth) (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L)) :
    (st.removeWaitAtNode L h2L hLL uL k).nodeWait L h2L hLL uL =
      (st.nodeWait L h2L hLL uL).remove k := by
  dsimp only [removeWaitAtNode]
  by_cases hLlt : L < P.depth
  · rw [dite_eq_left hLlt, nodeWait_inner _ h2L hLlt hLL, nodeWait_inner _ h2L hLlt hLL]
    simp [updateInner]
  · obtain rfl : L = P.depth := by omega
    rw [dite_eq_right (lt_irrefl _), nodeWait_depth, nodeWait_depth]
    simp [removeWaitLeafAt, updateLeaf]

theorem nodeWait_removeWaitAtNode_other (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L)
    (hLL : L ≤ P.depth) (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    {ℓ : ℕ} (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (hdiff : ∀ h_eq : ℓ = L, h_eq ▸ u ≠ uL) :
    (st.removeWaitAtNode L h2L hLL uL k).nodeWait ℓ h2 hℓ u = st.nodeWait ℓ h2 hℓ u := by
  rcases st.removeWaitAtNode_cases h2L hLL uL k with
    ⟨hlt, nd, _, _, h⟩ | ⟨rfl, ln, _, _, h⟩
  · rw [h]; exact st.nodeWait_updateInner_other h2L hlt uL nd h2 hℓ u hdiff
  · rw [h]; exact st.nodeWait_updateLeaf_other uL ln h2 hℓ u hdiff

private def replaceInnerAt (st : P.TreeState) (L : ℕ) (h2 : 2 ≤ L) (hlt : L < P.depth)
    (u : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L)) (qv_new : Fin (P.quotUniv L) × Fin P.valBound) :
    P.TreeState :=
  let nd := st.inner L h2 hlt u
  if h : k_old ∈ nd.table.tableMeta.dom ∧ k_new ∉ nd.table.tableMeta.dom.erase k_old then
    st.updateInner L h2 hlt u
      { nd with wait := wait', table := nd.table.replace k_old k_new qv_new h.1 h.2 }
  else st

private def replaceLeafAt
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (u : Fin (P.numNodes P.depth))
    (wait' : WaitingList (P.idBits P.depth) (P.idBits (P.depth - 1)) (P.waitCap P.depth))
    (k_old k_new : Fin (2 ^ P.idBits P.depth))
    (qv_new : Fin (P.quotUniv P.depth) × Fin P.valBound) : P.TreeState :=
  let ln := st.leaves u
  if h : k_old ∈ ln.dom ∧ k_new ∉ ln.dom.erase k_old then
    st.updateLeaf u (ln.replace scheme wait' k_old k_new qv_new h.1 h.2)
  else st

/-- Replace `k_old` with `(k_new, qv_new)` and update waiting list to `wait'` at `(L, uL)`
(`2 ≤ L ≤ depth`, `Algorithm 3` Branch 2). -/
def replaceAtNode (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (L : ℕ) (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound) : P.TreeState :=
  if hlt : L < P.depth then
    replaceInnerAt st L h2L hlt uL wait' k_old k_new qv_new
  else
    have hd : L = P.depth := by omega
    Eq.ndrec
      (motive := fun m => Fin (P.numNodes m) →
        WaitingList (P.idBits m) (P.idBits (m - 1)) (P.waitCap m) →
        Fin (2 ^ P.idBits m) → Fin (2 ^ P.idBits m) →
        Fin (P.quotUniv m) × Fin P.valBound → P.TreeState)
      (replaceLeafAt scheme st) hd.symm uL wait' k_old k_new qv_new

private theorem replaceAtNode_cases
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound) :
    let st' := st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new
    st' = st ∨
      (∃ (hlt : L < P.depth) (nd : P.InnerNode L),
        nd.seed = (st.inner L h2L hlt uL).seed ∧ st' = st.updateInner L h2L hlt uL nd) ∨
      (∃ (hd : L = P.depth) (ln : P.LeafNode),
        ln.leafMeta.seed = (st.leaves (hd ▸ uL)).leafMeta.seed ∧
        st' = st.updateLeaf (hd ▸ uL) ln) := by
  dsimp only [replaceAtNode]
  by_cases hLlt : L < P.depth
  · rw [dite_eq_left hLlt]; dsimp only [replaceInnerAt]
    split_ifs with h
    · refine Or.inr (Or.inl ⟨hLlt, _, ?_, rfl⟩)
      rfl
    · exact Or.inl rfl
  · obtain rfl : L = P.depth := by omega
    rw [dite_eq_right (lt_irrefl _)]; dsimp only [replaceLeafAt]
    split_ifs with h
    · refine Or.inr (Or.inr ⟨rfl, _, ?_, rfl⟩)
      rfl
    · exact Or.inl rfl

theorem seeds_replaceAtNode
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound) :
    (st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new).seeds = st.seeds := by
  rcases st.replaceAtNode_cases scheme h2L hLL uL wait' k_old k_new qv_new with
    h | ⟨hlt, nd, hs, h⟩ | ⟨rfl, ln, hs, h⟩
  exacts [congrArg seeds h, h.symm ▸ st.seeds_updateInner_of_seed_eq h2L hlt uL nd hs,
    h.symm ▸ st.seeds_updateLeaf_of_seed_eq uL ln hs]

theorem sentCount_replaceAtNode
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound) :
    (st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new).sentCount = st.sentCount := by
  rcases st.replaceAtNode_cases scheme h2L hLL uL wait' k_old k_new qv_new with
    h | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [h] <;> rfl

theorem nodeDom_replaceAtNode_same
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound)
    (hold : k_old ∈ st.nodeDom L h1L hLL uL)
    (hnew : k_new ∉ (st.nodeDom L h1L hLL uL).erase k_old) :
    (st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new).nodeDom L h1L hLL uL =
      Insert.insert k_new ((st.nodeDom L h1L hLL uL).erase k_old) := by
  dsimp only [replaceAtNode, replaceInnerAt]
  by_cases hLlt : L < P.depth
  · rw [nodeDom_inner st h1L h2L hLlt hLL] at hold hnew ⊢
    rw [dite_eq_left hLlt, dite_eq_left ⟨hold, hnew⟩, nodeDom_inner _ h1L h2L hLlt hLL]
    simp [updateInner]
  · obtain rfl : L = P.depth := by omega
    rw [nodeDom_depth] at hold hnew
    rw [dite_eq_right (lt_irrefl _), nodeDom_depth, nodeDom_depth]
    simp [replaceLeafAt, hold, hnew, updateLeaf]

theorem nodeDom_replaceAtNode_other
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound)
    {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (hdiff : ∀ h_eq : ℓ = L, h_eq ▸ u ≠ uL) :
    (st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new).nodeDom ℓ h1 hℓ u =
      st.nodeDom ℓ h1 hℓ u := by
  rcases st.replaceAtNode_cases scheme h2L hLL uL wait' k_old k_new qv_new with
    h | ⟨hlt, nd, _, h⟩ | ⟨rfl, ln, _, h⟩
  exacts [by rw [h], h.symm ▸ st.nodeDom_updateInner_other h2L hlt uL nd h1 hℓ u hdiff,
    h.symm ▸ st.nodeDom_updateLeaf_other uL ln h1 hℓ u hdiff]

theorem nodeQuery_replaceAtNode_same
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new k' : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound)
    (hold : k_old ∈ st.nodeDom L h1L hLL uL)
    (hnew : k_new ∉ (st.nodeDom L h1L hLL uL).erase k_old) :
    (st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new).nodeQuery scheme L h1L hLL uL
      k' = Function.update
        (Function.update (st.nodeQuery scheme L h1L hLL uL) k_old none) k_new (some qv_new) k' := by
  dsimp only [replaceAtNode, replaceInnerAt]
  by_cases hLlt : L < P.depth
  · rw [nodeDom_inner st h1L h2L hLlt hLL] at hold hnew
    rw [dite_eq_left hLlt, dite_eq_left ⟨hold, hnew⟩, nodeQuery_inner _ _ h1L h2L hLlt hLL,
      funext (nodeQuery_inner scheme st h1L h2L hLlt hLL uL)]
    simp [updateInner]
  · obtain rfl : L = P.depth := by omega
    rw [nodeDom_depth] at hold hnew
    rw [dite_eq_right (lt_irrefl _), nodeQuery_depth,
      funext (nodeQuery_depth scheme st h1L hLL uL)]
    simp [replaceLeafAt, hold, hnew, updateLeaf]

theorem nodeQuery_replaceAtNode_other
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound)
    {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (k' : Fin (2 ^ P.idBits ℓ)) (hdiff : ∀ h_eq : ℓ = L, h_eq ▸ u ≠ uL) :
    (st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new).nodeQuery scheme ℓ h1 hℓ u k' =
      st.nodeQuery scheme ℓ h1 hℓ u k' := by
  rcases st.replaceAtNode_cases scheme h2L hLL uL wait' k_old k_new qv_new with
    h | ⟨hlt, nd, _, h⟩ | ⟨rfl, ln, _, h⟩
  exacts [by rw [h], h.symm ▸ st.nodeQuery_updateInner_other scheme h2L hlt uL nd h1 hℓ u k' hdiff,
    h.symm ▸ st.nodeQuery_updateLeaf_other scheme uL ln h1 hℓ u k' hdiff]

theorem nodeWait_replaceAtNode_same
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound)
    (hold : k_old ∈ st.nodeDom L h1L hLL uL)
    (hnew : k_new ∉ (st.nodeDom L h1L hLL uL).erase k_old) :
    (st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new).nodeWait L h2L hLL uL =
      wait' := by
  dsimp only [replaceAtNode, replaceInnerAt]
  by_cases hLlt : L < P.depth
  · rw [nodeDom_inner st h1L h2L hLlt hLL] at hold hnew
    rw [dite_eq_left hLlt, dite_eq_left ⟨hold, hnew⟩, nodeWait_inner _ h2L hLlt hLL]
    simp [updateInner]
  · obtain rfl : L = P.depth := by omega
    rw [nodeDom_depth] at hold hnew
    rw [dite_eq_right (lt_irrefl _), nodeWait_depth]
    simp [replaceLeafAt, hold, hnew, updateLeaf, LeafNode.replace, LeafNode.ofFixedEncoded]

theorem nodeWait_replaceAtNode_other
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound)
    {ℓ : ℕ} (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (hdiff : ∀ h_eq : ℓ = L, h_eq ▸ u ≠ uL) :
    (st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new).nodeWait ℓ h2 hℓ u =
      st.nodeWait ℓ h2 hℓ u := by
  rcases st.replaceAtNode_cases scheme h2L hLL uL wait' k_old k_new qv_new with
    h | ⟨hlt, nd, _, h⟩ | ⟨rfl, ln, _, h⟩
  exacts [by rw [h], h.symm ▸ st.nodeWait_updateInner_other h2L hlt uL nd h2 hℓ u hdiff,
    h.symm ▸ st.nodeWait_updateLeaf_other uL ln h2 hℓ u hdiff]

end TreeSchedule.TreeState

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
