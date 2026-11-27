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
      { hv.toCore with
        qv_global := fun p' => ⟨(hv.qv_global p').1, by
          simp only [fs_ov, Function.update_apply]
          split_ifs
          exacts [hv_max, (hv.qv_global p').2]⟩
        active_item := fun b' hb' l' hl' =>
          let ⟨h1', h2', h3', h4'⟩ := hv.active_item b' hb' l' hl'
          ⟨h1', h2', h3', by
            change Function.update fs.valArr p v (fs.physSlot n_max b' l') < V
            rw [Function.update_apply]
            split_ifs
            exacts [hv_lt, h4']⟩
        dict_map := fun u' => by
          rw [show fs_ov.physSlot n_max = fs.physSlot n_max from rfl]
          dsimp only [fs_ov]
          set b' := feistelBucket (bWhp n_max) h1 u'.val
          set q' := keyQuotient (bWhp n_max) u'.val
          have hb' : b' < numBucketsWhp n_max := feistelBucket_lt _ _ _
          by_cases hu' : u' = u
          · subst hu'
            simp only [Function.update_self, reduceCtorEq, false_iff, Option.some.injEq]
            exact ⟨fun hall => absurd hq_loc (hall loc hloc_lt), fun v' =>
              ⟨fun h => ⟨loc, hloc_lt, hq_loc, h ▸ Function.update_self _ _ _⟩,
               fun ⟨l', hl', hql, hvl⟩ => by
                 obtain rfl := hv.quot_inj b hb l' hl' loc hloc_lt (hql.trans hq_loc.symm)
                 simpa only [b, b', p, Function.update_self] using hvl⟩⟩
          · rw [Function.update_of_ne hu']
            obtain ⟨hn_iff, hs_iff⟩ := hv.dict_map u'
            refine ⟨hn_iff, fun v' => (hs_iff v').trans ?_⟩
            have hne_p_of : ∀ l' < fs.bktCount b',
                fs.quotArr (fs.physSlot n_max b' l') = q' → fs.physSlot n_max b' l' ≠ p := by
              intro l' hl' hql heq
              obtain ⟨hbb, hll⟩ := hphys_inj b' hb' l' hl' b hb loc hloc_lt heq
              have huv : u'.val = u.val := by
                rw [← feistelReconstruct_feistelBucket (bWhp n_max) h1 u'.val,
                  ← feistelReconstruct_feistelBucket (bWhp n_max) h1 u.val]
                exact congrArg₂ (feistelReconstruct (bWhp n_max) h1) hbb
                  (show q' = q_val by rw [← hql, hbb, hll, hq_loc])
              exact hu' (Fin.ext huv)
            exact exists_congr fun l' => and_congr_right fun hl' => and_congr_right fun hql => by
              rw [Function.update_of_ne (hne_p_of l' hl' hql)] }
    rw [← hins]
    obtain ⟨hc', hom', hst', _, _, hclk', _, _⟩ := overmarsStep_spec hc_ov hb
      (fun b' hb' _ => hv.overmars_valid b' hb') (hv.overmars_valid b hb).toPre
    exact ⟨hc', hom', hst' hv.stage_valid, hclk'⟩
  | none =>
    rw [hfind] at hins hfl
    have hno_q : ∀ loc < fs.bktCount b, fs.quotArr (fs.physSlot n_max b loc) ≠ q_val :=
      (hv.dict_map u).1.mp hfl
    set X := fs.bktCount b
    set cf := capFrontWhp n_max
    set rKey := fpReducedKey c U n_max θ.2 u
    set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
    set lIdx := fs.liveSliceIdx b
    set hasFpCollision :=
      (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices lIdx) fp).isSome
    simp only [Option.ite_none_left_eq_some, Option.some.injEq] at hins
    obtain ⟨hg1, hg2, hg3, rfl⟩ := hins
    have hX_lt : X < totalLocalCoordsWhp n_max := by omega
    have htop_pos : cf ≤ X → 0 < fs.poolFreeTop := by omega
    have hcur_lk_none : bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey = none :=
      Option.not_isSome_iff_eq_none.mp fun h => hg2 (.inl h)
    have hold_lk_none : fs.rebStage ≤ 3 →
        bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey = none := fun hle3 =>
      Option.not_isSome_iff_eq_none.mp fun h => hg2 (.inr ⟨hle3, h⟩)
    -- Common facts about `fsIns` (holding in both `hasFpCollision = true` and `false` branches)
    have hbase : FastInsertFreshBase c U V n_max θ fs dict u v hasFpCollision :=
      fastInsertFresh_base hnU hv hv_lt hno_q hX_lt htop_pos hcur_lk_none hold_lk_none
        hasFpCollision
    obtain ⟨hc_ins, hom_other, hom_b, hst_ins, hclk_ins⟩ :=
      if hfp_coll : hasFpCollision = true then
        fastInsertFresh_collision_spec hv hbase hg3 hfp_coll
      else
        fastInsertFresh_live_spec hv hX_lt hbase rfl hfp_coll
    obtain ⟨hc', hom', hst', _, _, hclk', _, _⟩ :=
      overmarsStep_spec hc_ins hb hom_other hom_b
    exact ⟨hc', hom', hst' hst_ins, hclk'.trans hclk_ins⟩

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
