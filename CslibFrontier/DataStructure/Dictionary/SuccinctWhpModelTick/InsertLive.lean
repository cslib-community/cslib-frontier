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
-- `import all`: reads private fingerprint/buffer helpers (`fpOfSalt_lt`, `BufMapRel.insert_skip`)
-- and public `liveInsCount_le_eight` from `Common`.
import all CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick.Common
import Mathlib.Tactic.Linarith

/-!
# Collision-Free Live-Slice Branch of `fastInsert`

Internal correctness proof for the `hasFpCollision = false` branch of `fastInsertFresh`, inserting
the newly allocated coordinate directly into the bucket's live B-tree slice `fs.slices lIdx` with
state `1` [BenderFarachColtonKuszmaulKuszmaul2024].

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.fastInsertFresh_live_spec`: proves `CoreFastInv`,
  off-bucket `OvermarsBucketInv`, target-bucket `PreOvermarsBucketInv`, and `ValidEpochStage` in
  the collision-free live-slice branch.

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


/-- Invariant preservation for `fastInsertFresh` in the `hasFpCollision = false` branch. -/
theorem fastInsertFresh_live_spec {c U V n_max : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U}
    (hv : ValidFastState c U V n_max θ fs dict) {u : Fin U} {v : ℕ}
    (hX_lt : fs.bktCount (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val) <
      totalLocalCoordsWhp n_max)
    {hasFpCollision : Bool}
    (hbase : FastInsertFreshBase c U V n_max θ fs dict u v hasFpCollision)
    (hfp_def :
      let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
      hasFpCollision =
        (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b))
          (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)).isSome)
    (hfp_coll : ¬(hasFpCollision = true)) :
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
  have hfp_false : hasFpCollision = false := Bool.eq_false_iff.mpr hfp_coll
  subst hfp_false
  obtain ⟨hfsIns_bkt, hfp_pres, hrk_pres, hfp_new, _, _, _,
    hqv_glob', hbkt_le', hbkt_ge0', hact_item', hquot_inj', hdict_map',
    hpoolTop', hbp_val', hfree_lt', hbp_inj', hfree_inj', hdisj', hcons'⟩ := hbase
  dsimp only at *
  set h1 := bktHash c U n_max θ.1
  set b := feistelBucket (bWhp n_max) h1 u.val
  set q_val := keyQuotient (bWhp n_max) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  set X := fs.bktCount b
  set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  set lIdx := fs.liveSliceIdx b
  set rKey := fpReducedKey c U n_max θ.2 u
  set fsAlloc := fastInsertAlloc n_max b X fs
  set fsIns := fastInsertFresh c n_max b X q_val v rKey fp lIdx false fsAlloc
  obtain ⟨hia_cur, hna_cur, curMap, hv_cur, hrel_cur⟩ := hv.bufCur_valid
  have hlocState_eq : fsIns.locState =
      Function.update fs.locState b (Function.update (fs.locState b) X 1) := rfl
  have hsl_eq : fsIns.slices = Function.update fs.slices lIdx
      (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices lIdx) fp X) := rfl
  have hlic_eq : fsIns.liveInsCount =
      Function.update fs.liveInsCount b (fs.liveInsCount b + 1) := rfl
  -- Fields of `fs` that the live insertion leaves untouched.
  obtain ⟨hcur_eq, hold_eq, hstg_eq, hdf_eq, hbs_eq, hbuf_eq, hli_eq, hoa_eq, hoc_eq, hoi_eq,
      hosi_eq, hrsi_eq⟩ :
      fsIns.curEp = fs.curEp ∧ fsIns.oldEp = fs.oldEp ∧ fsIns.rebStage = fs.rebStage ∧
      fsIns.rebDoneFlag = fs.rebDoneFlag ∧ fsIns.bktSalt = fs.bktSalt ∧ fsIns.buf = fs.buf ∧
      fsIns.liveSliceIdx = fs.liveSliceIdx ∧ fsIns.overmarsActive = fs.overmarsActive ∧
      fsIns.overmarsCursor = fs.overmarsCursor ∧ fsIns.overmarsInsCount = fs.overmarsInsCount ∧
      fsIns.overmarsSliceIdx = fs.overmarsSliceIdx ∧ fsIns.rebSliceIdx = fs.rebSliceIdx :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hls_pres : ∀ b' < numBucketsWhp n_max, ∀ l' < fs.bktCount b',
      fsIns.locState b' l' = fs.locState b' l' := by
    intro b' _ l' hl'
    rw [hlocState_eq]
    by_cases hbb : b' = b
    · subst hbb; rw [Function.update_self, Function.update_of_ne (by omega)]
    · rw [Function.update_of_ne hbb]
  have hls_new : fsIns.locState b X = 1 := by
    rw [hlocState_eq, Function.update_self, Function.update_self]
  have hinL_X : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fsIns.locState b X) =
      true := by
    rw [hls_new]; simp [inLiveTree]
  obtain ⟨liveMap0, hv_live0, hrel_live0⟩ := hv.live_valid b hb
  have hlic_le8 : fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 :=
    liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb)
  have hfp_lt : fp < 2 ^ fpBitsWhp n_max := fpOfSalt_lt θ.2 _ u
  have hX_val : X < 2 ^ valLaneBitsWhp n_max := by
    have hX3 : X < 3 * (slabScale n_max) ^ 12 :=
      hX_lt.trans_le totalLocalCoordsWhp_le_three_mul
    rw [two_pow_valLaneBitsWhp n_max]; omega
  have hlk_live_none :
      btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices lIdx) fp = none := by
    cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices lIdx) fp with
    | none => rfl
    | some _ => simp [hlk] at hfp_def
  have hlm0_none : liveMap0 fp = none :=
    (hv_live0.lookup_eq hv.hth hlic_le8 hfp_lt).symm.trans hlk_live_none
  have hno_fp_coll : ∀ loc < X,
      inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true →
      fs.fpAt c U n_max θ (fs.bktSalt b) b loc ≠ fp :=
    (hrel_live0.1 fp).mp hlm0_none
  have hins_live := (hv_live0.insert_spec hv.hth hlic_le8 hfp_lt hX_val).2
  obtain ⟨hlr_b, hor_b, hro_ne_b⟩ := hv.roles_valid b hb
  have hne_all : ∀ b' < numBucketsWhp n_max,
      fs.overmarsSliceIdx b' ≠ lIdx ∧ fs.rebSliceIdx b' ≠ lIdx := by
    intro b' hb'
    obtain ⟨hlr', hor', hne'⟩ := hv.roles_valid b' hb'
    have hrr' : fs.rebRole b' < 3 ∧ fs.rebRole b' ≠ fs.liveRole b' := by
      dsimp only [FastState.rebRole]; omega
    dsimp only [FastState.overmarsSliceIdx, FastState.rebSliceIdx, lIdx, FastState.liveSliceIdx]
    by_cases hbb : b' = b
    · subst hbb; omega
    · exact ⟨fun heq => hbb (sliceIdx_inj hor' hlr_b heq).1,
        fun heq => hbb (sliceIdx_inj hrr'.1 hlr_b heq).1⟩
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
            · rw [hls_new]; omega
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
            rcases Nat.lt_succ_iff_lt_or_eq.mp hl₁ with hl1_lt | rfl <;>
              rcases Nat.lt_succ_iff_lt_or_eq.mp hl₂ with hl2_lt | rfl
            · rw [hls_pres b hb l₁ hl1_lt] at hin₁
              rw [hls_pres b hb l₂ hl2_lt] at hin₂
              rw [hfp_pres _ b hb l₁ hl1_lt, hfp_pres _ b hb l₂ hl2_lt] at hfeq
              exact hv.live_fp_inj b hb l₁ hl1_lt l₂ hl2_lt hin₁ hin₂ hfeq
            · rw [hls_pres b hb l₁ hl1_lt] at hin₁
              rw [hfp_pres _ b hb l₁ hl1_lt, hfp_new] at hfeq
              exact absurd hfeq (hno_fp_coll l₁ hl1_lt hin₁)
            · rw [hls_pres b hb l₂ hl2_lt] at hin₂
              rw [hfp_new, hfp_pres _ b hb l₂ hl2_lt] at hfeq
              exact absurd hfeq.symm (hno_fp_coll l₂ hl2_lt hin₂)
            · rfl
          · rw [Function.update_of_ne hbb] at hl₁ hl₂
            rw [hls_pres b' hb' l₁ hl₁] at hin₁
            rw [hls_pres b' hb' l₂ hl₂] at hin₂
            rw [hfp_pres _ b' hb' l₁ hl₁, hfp_pres _ b' hb' l₂ hl₂] at hfeq
            exact hv.live_fp_inj b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq
        live_valid := fun b' hb' => by
          rw [hstg_eq, hold_eq, hdf_eq, hbs_eq, hli_eq, hfsIns_bkt]
          by_cases hbb : b' = b
          · subst hbb
            rw [Function.update_self]
            refine ⟨Function.update liveMap0 fp (some X), ?_, ?_⟩
            · rw [hlic_eq, hsl_eq, Function.update_self, Function.update_self]
              exact hins_live
            · have hrl' := hrel_live0.congr
                (f' := fsIns.fpAt c U n_max θ (fs.bktSalt b) b)
                (P' := fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b)
                  (fsIns.locState b loc) = true)
                (fun loc hlt => hfp_pres _ b hb loc hlt)
                (fun loc hlt => by rw [hls_pres b hb loc hlt])
              have hstep := hrl'.step_true hinL_X (fun loc hlt hin => by
                rw [hfp_pres _ b hb loc hlt, hfp_new]
                rw [hls_pres b hb loc hlt] at hin
                exact hno_fp_coll loc hlt hin)
              rwa [hfp_new] at hstep
          · rw [Function.update_of_ne hbb]
            obtain ⟨lm, hvl, hrl⟩ := hv.live_valid b' hb'
            have hne_s : fs.liveSliceIdx b' ≠ lIdx := by
              dsimp only [FastState.liveSliceIdx, lIdx]
              intro heq
              exact hbb (sliceIdx_inj (hv.roles_valid b' hb').1 hlr_b heq).1
            refine ⟨lm, ?_, hrl.congr (fun loc hlt => hfp_pres _ b' hb' loc hlt)
              (fun loc hlt => by rw [hls_pres b' hb' loc hlt])⟩
            rw [hlic_eq, hsl_eq]
            simp only [Function.update_of_ne hbb, Function.update_of_ne hne_s]
            exact hvl
        rKey_buf_inj := fun b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂ h2₁ h2₂ hrkeq => by
          rw [hfsIns_bkt] at hl₁ hl₂
          have hlt0 : ∀ b' < numBucketsWhp n_max,
              ∀ l' < Function.update fs.bktCount b (X + 1) b',
              2 ≤ fsIns.locState b' l' → l' < fs.bktCount b' := by
            intro b' _ l' hl' h2
            by_cases hbb : b' = b
            · subst hbb; rw [Function.update_self] at hl'
              rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with h | rfl
              · exact h
              · rw [hls_new] at h2; omega
            · rwa [Function.update_of_ne hbb] at hl'
          have hl1_0 := hlt0 b₁ hb₁ l₁ hl₁ h2₁
          have hl2_0 := hlt0 b₂ hb₂ l₂ hl₂ h2₂
          rw [hls_pres b₁ hb₁ l₁ hl1_0] at h2₁
          rw [hls_pres b₂ hb₂ l₂ hl2_0] at h2₂
          rw [hrk_pres b₁ hb₁ l₁ hl1_0, hrk_pres b₂ hb₂ l₂ hl2_0] at hrkeq
          exact hv.rKey_buf_inj b₁ hb₁ l₁ hl1_0 b₂ hb₂ l₂ hl2_0 h2₁ h2₂ hrkeq
        bufCur_valid := by
          rw [hbuf_eq, hcur_eq]
          refine ⟨hia_cur, hna_cur, curMap, hv_cur, ?_⟩
          rw [hfsIns_bkt]
          exact hrel_cur.insert_skip
            (by rw [hls_new]; rcases hv.curEp_or with hc | hc <;> omega)
            hls_pres hrk_pres
        bufOld_valid := by
          rw [hstg_eq, hold_eq, hbuf_eq]
          have hbo := hv.bufOld_valid
          have hnew_ne_old : fsIns.locState b X ≠ 2 + fs.oldEp := by
            rw [hls_new]; omega
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
    exact OvermarsBucketInv.of_eq_lt (hv.overmars_valid b' hb')
      (congrFun hbs_eq b') (fun loc hlt => hfp_pres _ b' hb' loc hlt)
      hstg_eq hcur_eq (congrFun hdf_eq b')
      (fun loc hlt => hls_pres b' hb' loc hlt)
      (by rw [hfsIns_bkt, Function.update_of_ne hne])
      (by
        exact Function.update_of_ne hne _ _)
      (congrFun hoa_eq b') (congrFun hoc_eq b') (congrFun hoi_eq b')
      (by
        rw [hosi_eq, hsl_eq]
        exact Function.update_of_ne (hne_all b' hb').1 _ _)
  · have hlic_b : fsIns.liveInsCount b = fs.liveInsCount b + 1 := by
      rw [hlic_eq, Function.update_self]
    have hom_sl : fsIns.slices (fsIns.overmarsSliceIdx b) =
        fs.slices (fs.overmarsSliceIdx b) := by
      rw [hosi_eq, hsl_eq]
      exact Function.update_of_ne (hne_all b hb).1 _ _
    rcases hv.overmars_valid b hb with
      ⟨ha0, hlt5⟩ | ⟨ha1, h16, hcur, hlin, hins_om, omM, hvO, hrO⟩
    · exact Or.inl ⟨(congrFun hoa_eq b).trans ha0, by omega⟩
    · refine Or.inr ⟨(congrFun hoa_eq b).trans ha1, hoc_eq.symm ▸ h16, ?_, ?_, ?_, omM, ?_, ?_⟩
      · rw [hoc_eq, hfsIns_bkt, Function.update_self]; omega
      · rw [hoc_eq, hlic_b]; omega
      · rw [hoc_eq, hoi_eq]; omega
      · rwa [hoi_eq, hom_sl]
      · rw [hbs_eq, hstg_eq, hold_eq, hdf_eq, hoc_eq, hfsIns_bkt, Function.update_self,
          Nat.min_eq_right (by omega : fs.overmarsCursor b ≤ X + 1)]
        exact hrO.congr (fun loc hlt => hfp_pres _ b hb loc (hlt.trans hcur))
          (fun loc hlt => by rw [hls_pres b hb loc (hlt.trans hcur)])
  · refine hv.stage_valid.fastInsertFresh hv.curEp_or (b := b) (q := q_val) (v := v)
      (rk := rKey) (fp := fp) (collision := false) rfl hfp_pres fun bc hbc => ?_
    rw [hrsi_eq, hsl_eq]
    exact Function.update_of_ne (hne_all bc hbc).2 _ _

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
