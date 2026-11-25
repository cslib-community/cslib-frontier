/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick.InsertBase
-- `import all`: reads private epoch/buffer helpers (`curEp_ne_oldEp`, `BufMapRel.insert_skip`,
-- `inLiveTree_curEp_eq_false`) from `Common`.
import all CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick.Common
import Mathlib.Tactic.Linarith

/-!
# Colliding-Fingerprint Buffer Branch of `fastInsert`

Internal correctness proof for the `hasFpCollision = true` branch of `fastInsertFresh`, inserting
the newly allocated coordinate into the current-epoch buffer trie `fs.buf fs.curEp` with state
`2 + fs.curEp` [BenderFarachColtonKuszmaulKuszmaul2024].

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.fastInsertFresh_collision_spec`: proves `CoreFastInv`,
  off-bucket `OvermarsBucketInv`, target-bucket `PreOvermarsBucketInv`, and `ValidEpochStage` in
  the colliding-fingerprint branch.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset
open scoped BigOperators


/-- Invariant preservation for `fastInsertFresh` in the `hasFpCollision = true` branch. -/
theorem fastInsertFresh_collision_spec {c U V n_max : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U}
    (hv : ValidFastState c U V n_max θ fs dict) {u : Fin U} {v : ℕ}
    {hasFpCollision : Bool}
    (hbase : FastInsertFreshBase c U V n_max θ fs dict u v hasFpCollision)
    (hg3 : ¬(hasFpCollision ∧
      !bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
        (fpReducedKey c U n_max θ.2 u) ∧
      2 * sMaxWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc))
    (hfp_coll : hasFpCollision = true) :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    CoreFastInv c U V n_max θ fsIns (Function.update dict u (some v)) ∧
    (∀ b' < numBucketsWhp n_max, b' ≠ b → OvermarsBucketInv c U n_max θ fsIns b') ∧
    PreOvermarsBucketInv c U n_max θ fsIns b ∧
    ValidEpochStage c U n_max θ fsIns ∧
    fsIns.epochClock = fs.epochClock := by
  subst hasFpCollision
  obtain ⟨hfsIns_bkt, hfp_pres, hrk_pres, _, hrk_new, hno_rk_cur, hno_rk_any,
    hqv_glob', hbkt_le', hbkt_ge0', hact_item', hquot_inj', hdict_map',
    hpoolTop', hbp_val', hfree_lt', hbp_inj', hfree_inj', hdisj', hcons'⟩ := hbase
  dsimp only at *
  set h1 := bktHash c U n_max θ.1
  set b := feistelBucket (bWhp n_max) h1 u.val
  set q_val := keyQuotient (bWhp n_max) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  set X := fs.bktCount b
  set rKey := fpReducedKey c U n_max θ.2 u
  have hrk_lt : rKey < 2 ^ (cTabWhp c * bCharWhp n_max) := fpReducedKey_lt c U n_max θ.2 u
  set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  set lIdx := fs.liveSliceIdx b
  set fsAlloc := fastInsertAlloc n_max b X fs
  set fsIns := fastInsertFresh c n_max b X q_val v rKey fp lIdx true fsAlloc
  obtain ⟨hia_cur, hna_cur, curMap, hv_cur, hrel_cur⟩ := hv.bufCur_valid
  have hlocState_eq : fsIns.locState =
      Function.update fs.locState b (Function.update (fs.locState b) X (2 + fs.curEp)) := rfl
  have hbuf_eq : fsIns.buf = Function.update fs.buf fs.curEp
      (bufInsert (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey b X) := rfl
  -- Fields of `fs` that the collision insertion leaves untouched.
  obtain ⟨hcur_eq, hold_eq, hstg_eq, hdf_eq, hbs_eq, hsl_eq, hlic_eq, hli_eq, hoa_eq, hoc_eq,
      hoi_eq, hosi_eq, hrsi_eq, hsc_eq, hdc_eq, hdb_eq, hdi_eq, hrq_eq, hcs_eq, hrc_eq, hri_eq⟩ :
      fsIns.curEp = fs.curEp ∧ fsIns.oldEp = fs.oldEp ∧ fsIns.rebStage = fs.rebStage ∧
      fsIns.rebDoneFlag = fs.rebDoneFlag ∧ fsIns.bktSalt = fs.bktSalt ∧
      fsIns.slices = fs.slices ∧ fsIns.liveInsCount = fs.liveInsCount ∧
      fsIns.liveSliceIdx = fs.liveSliceIdx ∧ fsIns.overmarsActive = fs.overmarsActive ∧
      fsIns.overmarsCursor = fs.overmarsCursor ∧ fsIns.overmarsInsCount = fs.overmarsInsCount ∧
      fsIns.overmarsSliceIdx = fs.overmarsSliceIdx ∧ fsIns.rebSliceIdx = fs.rebSliceIdx ∧
      fsIns.stageCursor = fs.stageCursor ∧ fsIns.dirtyCount = fs.dirtyCount ∧
      fsIns.dirtyBuckets = fs.dirtyBuckets ∧ fsIns.dirtyIdx = fs.dirtyIdx ∧
      fsIns.rebQueued = fs.rebQueued ∧ fsIns.rebCandSalt = fs.rebCandSalt ∧
      fsIns.rebScanCursor = fs.rebScanCursor ∧ fsIns.rebInsCount = fs.rebInsCount :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  have hls_pres : ∀ b' < numBucketsWhp n_max, ∀ l' < fs.bktCount b',
      fsIns.locState b' l' = fs.locState b' l' := by
    intro b' _ l' hl'
    rw [hlocState_eq]
    by_cases hbb : b' = b
    · subst hbb; rw [Function.update_self, Function.update_of_ne (by omega)]
    · rw [Function.update_of_ne hbb]
  have hls_new : fsIns.locState b X = 2 + fs.curEp := by
    rw [hlocState_eq, Function.update_self, Function.update_self]
  have hinL_X : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fsIns.locState b X) =
      false := by
    rw [hls_new]; exact inLiveTree_curEp_eq_false hv.curEp_or _
  have hins_cur := hv_cur.insert_spec (b := b) (loc := X) hrk_lt
  set tr' := bufInsert (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey b X
  have hia_tr' : tr'.itemAlloc ≤ 2 * sMaxWhp c n_max := by
    by_cases hev : bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey = true
    · rw [(hins_cur.2.2.2.2.2.1 hev).2]; exact hia_cur
    · have hevf : bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey = false :=
        Bool.eq_false_iff.mpr hev
      have hlt_cap : (fs.buf fs.curEp).itemAlloc < 2 * sMaxWhp c n_max := by
        by_contra hge
        exact hg3 ⟨rfl, by simp [hevf], Nat.not_lt.mp hge⟩
      have hia_eq : tr'.itemAlloc = (fs.buf fs.curEp).itemAlloc + 1 :=
        hins_cur.2.2.2.1.trans (ite_eq_right hev)
      omega
  have hna_tr' : tr'.nodeAlloc ≤ 1 + cTabWhp c * tr'.itemAlloc :=
    hv_cur.insert_nodeAlloc_le hrk_lt hna_cur
  have hbuf_cur_eq : fsIns.buf fsIns.curEp = tr' := by
    rw [hcur_eq, hbuf_eq, Function.update_self]
  have hbuf_old_eq : fsIns.buf fsIns.oldEp = fs.buf fs.oldEp := by
    rw [hold_eq, hbuf_eq]
    exact Function.update_of_ne (curEp_ne_oldEp hv.curEp_or).symm _ _
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · refine
      { hth := hv.hth
        curEp_or := hcur_eq ▸ hv.curEp_or
        epochClock_lt := hv.epochClock_lt
        rebStage_le := hv.rebStage_le
        rebCollision_zero := hv.rebCollision_zero
        qv_global := hqv_glob'
        bktCount_le := hbkt_le'
        bktCount_ge_zero := hbkt_ge0'
        locState_active := fun b' hb' l' hl' => by
          rw [hfsIns_bkt] at hl'
          by_cases hbb : b' = b
          · subst hbb; rw [Function.update_self] at hl'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hlt | rfl
            · rw [hls_pres b hb l' hlt]; exact hv.locState_active b hb l' hlt
            · rw [hls_new]; rcases hv.curEp_or with hc | hc <;> omega
          · rw [Function.update_of_ne hbb] at hl'
            rw [hls_pres b' hb' l' hl']; exact hv.locState_active b' hb' l' hl'
        locState_inactive := fun b' l' hnot => by
          rw [hfsIns_bkt] at hnot
          rw [hlocState_eq]
          by_cases hbb : b' = b
          · subst hbb; rw [Function.update_self] at hnot ⊢
            rw [Function.update_of_ne (by omega)]
            exact hv.locState_inactive b l' (by omega)
          · rw [Function.update_of_ne hbb] at hnot ⊢
            exact hv.locState_inactive b' l' hnot
        active_item := hact_item'
        quot_inj := hquot_inj'
        dict_map := hdict_map'
        poolFreeTop_le := hpoolTop'
        backPtr_valid := hbp_val'
        freeStack_lt := hfree_lt'
        backPtr_inj := hbp_inj'
        freeStack_inj := hfree_inj'
        back_free_disj := hdisj'
        pool_conservation := hcons'
        roles_valid := hv.roles_valid
        bktSalt_lt := hv.bktSalt_lt
        live_fp_inj := fun b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq => by
          rw [hstg_eq, hold_eq, hdf_eq] at hin₁ hin₂
          rw [hbs_eq] at hfeq
          rw [hfsIns_bkt] at hl₁ hl₂
          by_cases hbb : b' = b
          · subst hbb; rw [Function.update_self] at hl₁ hl₂
            have hl1_lt : l₁ < X := by
              rcases Nat.lt_succ_iff_lt_or_eq.mp hl₁ with h | rfl
              · exact h
              · rw [hinL_X] at hin₁; cases hin₁
            have hl2_lt : l₂ < X := by
              rcases Nat.lt_succ_iff_lt_or_eq.mp hl₂ with h | rfl
              · exact h
              · rw [hinL_X] at hin₂; cases hin₂
            rw [hls_pres b hb l₁ hl1_lt] at hin₁
            rw [hls_pres b hb l₂ hl2_lt] at hin₂
            rw [hfp_pres _ b hb l₁ hl1_lt, hfp_pres _ b hb l₂ hl2_lt] at hfeq
            exact hv.live_fp_inj b hb l₁ hl1_lt l₂ hl2_lt hin₁ hin₂ hfeq
          · rw [Function.update_of_ne hbb] at hl₁ hl₂
            rw [hls_pres b' hb' l₁ hl₁] at hin₁
            rw [hls_pres b' hb' l₂ hl₂] at hin₂
            rw [hfp_pres _ b' hb' l₁ hl₁, hfp_pres _ b' hb' l₂ hl₂] at hfeq
            exact hv.live_fp_inj b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq
        live_valid := fun b' hb' => by
          obtain ⟨lm, hvl, hrl⟩ := hv.live_valid b' hb'
          refine ⟨lm, ?_, ?_⟩
          · rwa [hsl_eq, hlic_eq, hli_eq]
          · rw [hstg_eq, hold_eq, hdf_eq, hbs_eq, hfsIns_bkt]
            by_cases hbb : b' = b
            · subst hbb; rw [Function.update_self]
              have hrl' := hrl.congr (f' := fsIns.fpAt c U n_max θ (fs.bktSalt b) b)
                (P' := fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b)
                  (fsIns.locState b loc) = true)
                (fun loc hlt => hfp_pres _ b hb loc hlt)
                (fun loc hlt => by rw [hls_pres b hb loc hlt])
              exact hrl'.step_false (by rw [hinL_X]; decide)
            · rw [Function.update_of_ne hbb]
              exact hrl.congr (fun loc hlt => hfp_pres _ b' hb' loc hlt)
                (fun loc hlt => by rw [hls_pres b' hb' loc hlt])
        rKey_buf_inj := fun b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂ h2₁ h2₂ hrkeq => by
          rw [hfsIns_bkt] at hl₁ hl₂
          have hcase : ∀ b' < numBucketsWhp n_max,
              ∀ l' < Function.update fs.bktCount b (X + 1) b',
              (b' = b ∧ l' = X) ∨ (l' < fs.bktCount b' ∧ ¬(b' = b ∧ l' = X)) := by
            intro b' _ l' hl'
            by_cases hbb : b' = b
            · subst hbb; rw [Function.update_self] at hl'
              rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with h | rfl
              · exact Or.inr ⟨h, fun ⟨_, he⟩ => by omega⟩
              · exact Or.inl ⟨rfl, rfl⟩
            · rw [Function.update_of_ne hbb] at hl'
              exact Or.inr ⟨hl', fun ⟨hb0, _⟩ => hbb hb0⟩
          rcases hcase b₁ hb₁ l₁ hl₁ with ⟨rfl, rfl⟩ | ⟨hl1_0, _⟩ <;>
            rcases hcase b₂ hb₂ l₂ hl₂ with ⟨rfl, rfl⟩ | ⟨hl2_0, _⟩
          · exact ⟨rfl, rfl⟩
          · rw [hrk_new, hrk_pres b₂ hb₂ l₂ hl2_0] at hrkeq
            rw [hls_pres b₂ hb₂ l₂ hl2_0] at h2₂
            exact absurd hrkeq.symm (hno_rk_any b₂ hb₂ l₂ hl2_0 h2₂)
          · rw [hrk_pres b₁ hb₁ l₁ hl1_0, hrk_new] at hrkeq
            rw [hls_pres b₁ hb₁ l₁ hl1_0] at h2₁
            exact absurd hrkeq (hno_rk_any b₁ hb₁ l₁ hl1_0 h2₁)
          · rw [hrk_pres b₁ hb₁ l₁ hl1_0, hrk_pres b₂ hb₂ l₂ hl2_0] at hrkeq
            rw [hls_pres b₁ hb₁ l₁ hl1_0] at h2₁
            rw [hls_pres b₂ hb₂ l₂ hl2_0] at h2₂
            exact hv.rKey_buf_inj b₁ hb₁ l₁ hl1_0 b₂ hb₂ l₂ hl2_0 h2₁ h2₂ hrkeq
        bufCur_valid := by
          rw [hbuf_cur_eq, hcur_eq]
          refine ⟨hia_tr', hna_tr', Function.update curMap rKey (some (b, X)), hins_cur.1, ?_⟩
          rw [hfsIns_bkt, ← hrk_new]
          exact hrel_cur.insert_fresh hb hls_new hls_pres hrk_pres
            (fun b' hb' loc hloc hst => hrk_new.symm ▸ hno_rk_cur b' hb' loc hloc hst)
        bufOld_valid := by
          rw [hstg_eq, hbuf_old_eq, hold_eq]
          have hbo := hv.bufOld_valid
          have hnew_ne_old : fsIns.locState b X ≠ 2 + fs.oldEp := by
            rw [hls_new]; have := curEp_ne_oldEp hv.curEp_or; omega
          by_cases hle3 : fs.rebStage ≤ 3
          · rw [ite_eq_left hle3] at hbo ⊢
            obtain ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩ := hbo
            refine ⟨hia_o, hna_o, oldMap, hv_o, ?_⟩
            rw [hfsIns_bkt]
            exact hrel_o.insert_skip hnew_ne_old hls_pres hrk_pres
          · rw [ite_eq_right hle3] at hbo ⊢
            have hno_old' : ∀ b' < numBucketsWhp n_max, ∀ l' < fsIns.bktCount b',
                fsIns.locState b' l' ≠ 2 + fs.oldEp := by
              intro b' hb' l' hl'
              rw [hfsIns_bkt] at hl'
              have hno0 : ∀ b'' < numBucketsWhp n_max, ∀ l'' < fs.bktCount b'',
                  fs.locState b'' l'' ≠ 2 + fs.oldEp := by
                split_ifs at hbo <;> exact hbo.1
              by_cases hbb : b' = b
              · subst hbb; rw [Function.update_self] at hl'
                rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hlt | rfl
                · rw [hls_pres b hb l' hlt]; exact hno0 b hb l' hlt
                · exact hnew_ne_old
              · rw [Function.update_of_ne hbb] at hl'
                rw [hls_pres b' hb' l' hl']; exact hno0 b' hb' l' hl'
            split_ifs at hbo ⊢ <;> exact ⟨hno_old', hbo.2⟩ }
  · intro b' hb' hne
    exact OvermarsBucketInv.of_eq_lt (hv.overmars_valid b' hb') (congrFun hbs_eq _)
      (fun loc hlt => hfp_pres _ b' hb' loc hlt) hstg_eq hcur_eq (congrFun hdf_eq _)
      (fun loc hlt => hls_pres b' hb' loc hlt)
      (by rw [hfsIns_bkt, Function.update_of_ne hne])
      (congrFun hlic_eq _) (congrFun hoa_eq _) (congrFun hoc_eq _) (congrFun hoi_eq _)
      (by rw [hsl_eq, hosi_eq])
  · exact (OvermarsBucketInv.of_eq_lt (hv.overmars_valid b hb) (congrFun hbs_eq _)
      (fun loc hlt => hfp_pres _ b hb loc hlt) hstg_eq hcur_eq (congrFun hdf_eq _)
      (fun loc hlt => hls_pres b hb loc hlt)
      (by rw [hfsIns_bkt, Function.update_self]; omega)
      (congrFun hlic_eq _) (congrFun hoa_eq _) (congrFun hoc_eq _) (congrFun hoi_eq _)
      (by rw [hsl_eq, hosi_eq])).toPre
  · have hstg := hv.stage_valid
    dsimp only [ValidEpochStage] at hstg ⊢
    rw [hbuf_old_eq, hold_eq, hstg_eq, hsc_eq, hdc_eq, hdb_eq, hdi_eq, hdf_eq, hrq_eq,
      hcs_eq, hrc_eq, hri_eq, hsl_eq]
    split_ifs at hstg ⊢ with hs0 hs1 hs2 hs3
    · exact hstg
    · exact hstg
    · rcases hstg with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hreb⟩
      refine ⟨hd1, hd2, hd3, hd4, hd5, ?_, fun hlt_s => ?_⟩
      · intro b' hb' l' hl' hst'
        rw [hfsIns_bkt] at hl'
        by_cases hbb : b' = b
        · subst hbb; rw [Function.update_self] at hl'
          rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hlt | rfl
          · rw [hls_pres b hb l' hlt] at hst'; exact hd6 b hb l' hlt hst'
          · rw [hls_new] at hst'
            exact absurd (by omega : fs.curEp = fs.oldEp) (curEp_ne_oldEp hv.curEp_or)
        · rw [Function.update_of_ne hbb] at hl'
          rw [hls_pres b' hb' l' hl'] at hst'; exact hd6 b' hb' l' hl' hst'
      · obtain ⟨hcur_r, hinj_r, rm, hvr, hrr⟩ := hreb hlt_s
        set bc := fs.dirtyBuckets fs.dirtyIdx
        have hbc : bc < numBucketsWhp n_max := hd3 _ hd2
        have hbkt_ge : fs.bktCount bc ≤ fsIns.bktCount bc := by
          rw [hfsIns_bkt]
          by_cases hbb : bc = b
          · rw [hbb, Function.update_self]; omega
          · rw [Function.update_of_ne hbb]
        have hmin_eq : min (fsIns.bktCount bc) fs.rebScanCursor =
            min (fs.bktCount bc) fs.rebScanCursor := by
          rcases hcur_r with ⟨hc0, _⟩ | ⟨_, hc_lt, _⟩
          · simp [hc0]
          · rw [Nat.min_eq_right (hc_lt.le.trans hbkt_ge), Nat.min_eq_right hc_lt.le]
        have hmin_le : min (fs.bktCount bc) fs.rebScanCursor ≤ fs.bktCount bc :=
          Nat.min_le_left _ _
        rw [hmin_eq, hrsi_eq]
        refine ⟨?_, ?_, rm, hvr, ?_⟩
        · rcases hcur_r with ⟨hc0, hi0⟩ | ⟨h16, hc_lt, hins_r⟩
          · exact Or.inl ⟨hc0, hi0⟩
          · exact Or.inr ⟨h16, hc_lt.trans_le hbkt_ge, hins_r⟩
        · intro l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
          have hl1_b := hl₁.trans_le hmin_le
          have hl2_b := hl₂.trans_le hmin_le
          rw [hls_pres bc hbc l₁ hl1_b] at hp₁
          rw [hls_pres bc hbc l₂ hl2_b] at hp₂
          rw [hfp_pres _ bc hbc l₁ hl1_b, hfp_pres _ bc hbc l₂ hl2_b] at hfeq
          exact hinj_r l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
        · exact hrr.congr (fun loc hlt => hfp_pres _ bc hbc loc (hlt.trans_le hmin_le))
            (fun loc hlt => by rw [hls_pres bc hbc loc (hlt.trans_le hmin_le)])
    · exact hstg

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
