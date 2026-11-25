/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick.InsertCollision
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick.InsertLive

/-!
# Fast-Mode Insertion Specification (`ValidFastState.fastInsert_spec`)

Assembles the in-place overwrite branch and the colliding-buffer / live-slice fresh-insertion
branches with Overmars bucket rebuilding (`overmarsStep_spec`) to prove
`ValidFastState.fastInsert_spec` [BenderFarachColtonKuszmaulKuszmaul2024].

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidFastState.fastInsert_spec`: whenever
  `fastInsert` returns `some fs'`, `fs'` refines `Dynamic.step dict (.insert u v)` and preserves
  `CoreFastInv`, `OvermarsBucketInv`, and `ValidEpochStage`.

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

/-- Whenever `fastInsert` succeeds (`= some fs'`), `fs'` refines `Dynamic.step dict (.insert u v)`
and preserves `CoreFastInv`, `OvermarsBucketInv` on all buckets, and `ValidEpochStage` (hence also
`ValidEpochStagePreTick`). -/
theorem ValidFastState.fastInsert_spec {c U V n_max : ℕ} (hnU : n_max ≤ U)
    {θ : SeedWhp c U n_max} {fs fs' : FastState} {dict : State U}
    (hv : ValidFastState c U V n_max θ fs dict) {u : Fin U} {v : ℕ}
    (hvalid : Dynamic.valid V n_max dict (.insert u v))
    (hins : fastInsert c U n_max θ fs u v = some fs') :
    CoreFastInv c U V n_max θ fs' (Dynamic.step dict (.insert u v)).1 ∧
    (∀ b' < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs' b') ∧
    ValidEpochStage c U n_max θ fs' ∧
    fs'.epochClock = fs.epochClock := by
  have hv_lt : v < V := hvalid.2
  have hv_max : v < max V 1 := hv_lt.trans_le (le_max_left V 1)
  have hfl := hv.fastFindLoc_spec u
  set h1 := bktHash c U n_max θ.1
  set b := feistelBucket (bWhp n_max) h1 u.val
  set q_val := keyQuotient (bWhp n_max) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  dsimp only [fastInsert, Dynamic.step] at hins ⊢
  cases hfind : fastFindLoc c U n_max θ fs u with
  | some loc =>
    rw [hfind] at hins hfl
    simp only [Option.some.injEq] at hins
    obtain ⟨hloc_lt, hq_loc⟩ := hfl
    obtain ⟨_, hphys_inj⟩ := hv.physSlot_lt_and_inj
    set p := fs.physSlot n_max b loc
    set fs_ov : FastState := { fs with valArr := Function.update fs.valArr p v }
    have hc_ov : CoreFastInv c U V n_max θ fs_ov (Function.update dict u (some v)) :=
      { hth := hv.hth
        curEp_or := hv.curEp_or
        epochClock_lt := hv.epochClock_lt
        rebStage_le := hv.rebStage_le
        rebCollision_zero := hv.rebCollision_zero
        qv_global := fun p' => by
          dsimp only [fs_ov]
          by_cases hp : p' = p
          · subst hp; rw [Function.update_self]; exact ⟨(hv.qv_global _).1, hv_max⟩
          · rw [Function.update_of_ne hp]; exact hv.qv_global p'
        bktCount_le := hv.bktCount_le
        bktCount_ge_zero := hv.bktCount_ge_zero
        locState_active := hv.locState_active
        locState_inactive := hv.locState_inactive
        active_item := fun b' hb' l' hl' => by
          obtain ⟨h1', h2', h3', h4'⟩ := hv.active_item b' hb' l' hl'
          refine ⟨h1', h2', h3', ?_⟩
          have hp_eq : fs_ov.physSlot n_max b' l' = fs.physSlot n_max b' l' := rfl
          rw [hp_eq]
          dsimp only [fs_ov]
          by_cases hp : fs.physSlot n_max b' l' = p
          · rw [hp, Function.update_self]; exact hv_lt
          · rw [Function.update_of_ne hp]; exact h4'
        quot_inj := hv.quot_inj
        dict_map := fun u' => by
          dsimp only
          have hp_eq : fs_ov.physSlot n_max = fs.physSlot n_max := rfl
          rw [hp_eq]
          dsimp only [fs_ov]
          set b' := feistelBucket (bWhp n_max) h1 u'.val
          set q' := keyQuotient (bWhp n_max) u'.val
          have hb' : b' < numBucketsWhp n_max := feistelBucket_lt _ _ _
          by_cases hu' : u' = u
          · subst hu'
            have hb'_eq : b' = b := rfl
            have hq'_eq : q' = q_val := rfl
            rw [Function.update_self, hb'_eq, hq'_eq]
            refine ⟨⟨fun h => (by cases h), fun hall => absurd hq_loc (hall loc hloc_lt)⟩,
              fun v' => ⟨fun h => ?_, fun ⟨l', hl', hql, hvl⟩ => ?_⟩⟩
            · injection h with hv_eq; subst hv_eq
              exact ⟨loc, hloc_lt, hq_loc, Function.update_self _ _ _⟩
            · have hl_eq : l' = loc := hv.quot_inj b hb l' hl' loc hloc_lt (hql.trans hq_loc.symm)
              subst hl_eq
              rw [Function.update_self] at hvl
              exact congrArg some hvl
          · rw [Function.update_of_ne hu']
            obtain ⟨hn_iff, hs_iff⟩ := hv.dict_map u'
            refine ⟨hn_iff, fun v' => ?_⟩
            rw [hs_iff v']
            have hne_p_of : ∀ l' < fs.bktCount b',
                fs.quotArr (fs.physSlot n_max b' l') = q' → fs.physSlot n_max b' l' ≠ p := by
              intro l' hl' hql heq
              obtain ⟨hbb, hll⟩ := hphys_inj b' hb' l' hl' b hb loc hloc_lt heq
              have hqq : q' = q_val := by
                rw [← hql, hbb, hll, hq_loc]
              have huv : u'.val = u.val := by
                rw [← feistelReconstruct_feistelBucket (bWhp n_max) h1 u'.val,
                  ← feistelReconstruct_feistelBucket (bWhp n_max) h1 u.val]
                change feistelReconstruct (bWhp n_max) h1 b' q' =
                  feistelReconstruct (bWhp n_max) h1 b q_val
                rw [hbb, hqq]
              exact hu' (Fin.ext huv)
            refine ⟨fun ⟨l', hl', hql, hvl⟩ => ⟨l', hl', hql, ?_⟩,
              fun ⟨l', hl', hql, hvl⟩ => ⟨l', hl', hql, ?_⟩⟩
            · rwa [Function.update_of_ne (hne_p_of l' hl' hql)]
            · rwa [Function.update_of_ne (hne_p_of l' hl' hql)] at hvl
        poolFreeTop_le := hv.poolFreeTop_le
        backPtr_valid := hv.backPtr_valid
        freeStack_lt := hv.freeStack_lt
        backPtr_inj := hv.backPtr_inj
        freeStack_inj := hv.freeStack_inj
        back_free_disj := hv.back_free_disj
        pool_conservation := hv.pool_conservation
        roles_valid := hv.roles_valid
        bktSalt_lt := hv.bktSalt_lt
        live_fp_inj := hv.live_fp_inj
        live_valid := hv.live_valid
        rKey_buf_inj := hv.rKey_buf_inj
        bufCur_valid := hv.bufCur_valid
        bufOld_valid := hv.bufOld_valid }
    have hom_ov : ∀ b' < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs_ov b' :=
      fun b' hb' => hv.overmars_valid b' hb'
    have hst_ov : ValidEpochStage c U n_max θ fs_ov := hv.stage_valid
    rw [← hins]
    obtain ⟨hc', hom', hst', _, _, hclk', _, _⟩ :=
      overmarsStep_spec hc_ov hb (fun b' hb' _ => hom_ov b' hb') (hom_ov b hb).toPre
    exact ⟨hc', hom', hst' hst_ov, hclk'⟩
  | none =>
    rw [hfind] at hins hfl
    have hno_q : ∀ loc < fs.bktCount b, fs.quotArr (fs.physSlot n_max b loc) ≠ q_val :=
      (hv.dict_map u).1.mp hfl
    set X := fs.bktCount b
    set cf := capFrontWhp n_max
    by_cases hg1 : totalLocalCoordsWhp n_max ≤ X ∨ (cf ≤ X ∧ fs.poolFreeTop = 0)
    · rw [ite_eq_left hg1] at hins; cases hins
    rw [ite_eq_right hg1] at hins
    have hX_lt : X < totalLocalCoordsWhp n_max := by omega
    have htop_pos : cf ≤ X → 0 < fs.poolFreeTop := by omega
    set rKey := fpReducedKey c U n_max θ.2 u
    have hrk_lt : rKey < 2 ^ (cTabWhp c * bCharWhp n_max) := fpReducedKey_lt c U n_max θ.2 u
    by_cases hg2 : (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey).isSome ∨
        (fs.rebStage ≤ 3 ∧
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome)
    · rw [ite_eq_left hg2] at hins; cases hins
    rw [ite_eq_right hg2] at hins
    have hcur_lk_none : bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey = none := by
      cases hlk : bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey with
      | none => rfl
      | some _ => exact absurd (Or.inl (by simp [hlk])) hg2
    have hold_lk_none : fs.rebStage ≤ 3 →
        bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey = none := by
      intro hle3
      cases hlk : bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey with
      | none => rfl
      | some _ => exact absurd (Or.inr ⟨hle3, by simp [hlk]⟩) hg2
    set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
    set lIdx := fs.liveSliceIdx b
    set hasFpCollision :=
      (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices lIdx) fp).isSome
    by_cases hg3 : hasFpCollision ∧
        !bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey ∧
        2 * sMaxWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc
    · rw [ite_eq_left hg3] at hins; cases hins
    rw [ite_eq_right hg3] at hins
    set fsAlloc := fastInsertAlloc n_max b X fs
    set fsIns := fastInsertFresh c n_max b X q_val v rKey fp lIdx hasFpCollision fsAlloc
    have hins_eq : overmarsStep c U n_max θ b fsIns = fs' := Option.some.inj hins
    rw [← hins_eq]
    -- Common facts about `fsIns` (holding in both `hasFpCollision = true` and `false` branches)
    have hbase : FastInsertFreshBase c U V n_max θ fs dict u v hasFpCollision :=
      fastInsertFresh_base hnU hv hv_lt hno_q hX_lt htop_pos hcur_lk_none hold_lk_none
        hasFpCollision
    have hsplit :
        CoreFastInv c U V n_max θ fsIns (Function.update dict u (some v)) ∧
        (∀ b' < numBucketsWhp n_max, b' ≠ b → OvermarsBucketInv c U n_max θ fsIns b') ∧
        PreOvermarsBucketInv c U n_max θ fsIns b ∧
        ValidEpochStage c U n_max θ fsIns ∧
        fsIns.epochClock = fs.epochClock := by
      by_cases hfp_coll : hasFpCollision = true
      · exact fastInsertFresh_collision_spec hv hbase hg3 hfp_coll
      · exact fastInsertFresh_live_spec hv hX_lt hbase rfl hfp_coll
    obtain ⟨hc_ins, hom_other, hom_b, hst_ins, hclk_ins⟩ := hsplit
    obtain ⟨hc', hom', hst', _, _, hclk', _, _⟩ :=
      overmarsStep_spec hc_ins hb hom_other hom_b
    exact ⟨hc', hom', hst' hst_ins, hclk'.trans hclk_ins⟩

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
