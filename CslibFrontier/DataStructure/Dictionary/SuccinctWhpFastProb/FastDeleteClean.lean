/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpFastProb.WorkPotential
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpFastProb.ScanMeta

/-!
# `fastDelete` Preservation of Clean-Window State for `SuccinctWhpFastProb`

Internal proof (`fastDelete_clean_props`) that `fastDelete` preserves `epochClock`, `curEp`,
`(fs.buf fs.curEp).itemAlloc`, `bufEverPresent`, `stageWorkRemaining ≤`, and `SaltBoundAt`
(not re-exported by `SuccinctWhpFastProb`).
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset

private theorem fastDeleteMoveSlices_rebSliceIdx (n_max b loc_del loc_last fp : ℕ)
    (s : FastState)
    (hroles : s.liveRole b < 3 ∧ s.overmarsRole b < 3 ∧ s.liveRole b ≠ s.overmarsRole b) :
    (fastDeleteMoveSlices n_max b loc_del loc_last fp s).1 (s.rebSliceIdx b) =
      s.slices (s.rebSliceIdx b) := by
  have hne1 : s.rebSliceIdx b ≠ s.liveSliceIdx b := by
    dsimp [FastState.rebSliceIdx, FastState.liveSliceIdx, FastState.rebRole]; omega
  have hne2 : s.rebSliceIdx b ≠ s.overmarsSliceIdx b := by
    dsimp [FastState.rebSliceIdx, FastState.overmarsSliceIdx, FastState.rebRole]; omega
  dsimp only [fastDeleteMoveSlices]
  have h1 : ∀ (f : ℕ → BTreeSlice),
      f (s.rebSliceIdx b) = s.slices (s.rebSliceIdx b) →
      (if s.overmarsActive b = 1 ∧
          inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc_last) then
        if loc_last < s.overmarsCursor b then
          (Function.update f (s.overmarsSliceIdx b)
            (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (f (s.overmarsSliceIdx b)) fp loc_del), s.overmarsInsCount)
        else if loc_del < s.overmarsCursor b then
          (Function.update f (s.overmarsSliceIdx b)
            (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (f (s.overmarsSliceIdx b)) fp loc_del),
           Function.update s.overmarsInsCount b (s.overmarsInsCount b + 1))
        else (f, s.overmarsInsCount)
      else (f, s.overmarsInsCount)).1 (s.rebSliceIdx b) = s.slices (s.rebSliceIdx b) := by
    intro f hf
    by_cases hc1 : s.overmarsActive b = 1 ∧
        inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc_last)
    · rw [ite_eq_left hc1]
      by_cases hc2 : loc_last < s.overmarsCursor b
      · rw [ite_eq_left hc2]; dsimp only; rw [Function.update_of_ne hne2]; exact hf
      · rw [ite_eq_right hc2]
        by_cases hc3 : loc_del < s.overmarsCursor b
        · rw [ite_eq_left hc3]; dsimp only; rw [Function.update_of_ne hne2]; exact hf
        · rw [ite_eq_right hc3]; exact hf
    · rw [ite_eq_right hc1]; exact hf
  apply h1
  by_cases hc0 : inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc_last)
  · rw [ite_eq_left hc0, Function.update_of_ne hne1]
  · rw [ite_eq_right hc0]

private theorem fastDeleteRemove_rebSliceIdx (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (s : FastState) (u : Fin U) (b loc_del : ℕ)
    (hroles : s.liveRole b < 3 ∧ s.overmarsRole b < 3 ∧ s.liveRole b ≠ s.overmarsRole b) :
    (fastDeleteRemove c U n_max θ s u b loc_del).slices (s.rebSliceIdx b) =
      if (decide (s.rebStage = 2 ∧ s.dirtyIdx < s.dirtyCount ∧
            s.dirtyBuckets s.dirtyIdx = b ∧ s.rebCandSalt < sMaxWhp c n_max ∧
            s.rebCollision = 0) &&
          decide (loc_del < s.rebScanCursor ∧
            (s.locState b loc_del = 1 ∨ s.locState b loc_del = 2 + s.oldEp))) = true then
        btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (s.slices (s.rebSliceIdx b)) (fpOfSalt c U n_max θ.2 s.rebCandSalt u)
      else s.slices (s.rebSliceIdx b) := by
  have hne1 : s.rebSliceIdx b ≠ s.liveSliceIdx b := by
    dsimp [FastState.rebSliceIdx, FastState.liveSliceIdx, FastState.rebRole]; omega
  have hne2 : s.rebSliceIdx b ≠ s.overmarsSliceIdx b := by
    dsimp [FastState.rebSliceIdx, FastState.overmarsSliceIdx, FastState.rebRole]; omega
  dsimp only [fastDeleteRemove]
  have hs2 : ∀ (f : ℕ → BTreeSlice),
      f (s.rebSliceIdx b) = s.slices (s.rebSliceIdx b) →
      (if s.overmarsActive b = 1 ∧ loc_del < s.overmarsCursor b ∧
          inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc_del) then
        Function.update f (s.overmarsSliceIdx b)
          (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (f (s.overmarsSliceIdx b)) (fpOfSalt c U n_max θ.2 (s.bktSalt b) u))
      else f) (s.rebSliceIdx b) = s.slices (s.rebSliceIdx b) := by
    intro f hf
    by_cases hc2 : s.overmarsActive b = 1 ∧ loc_del < s.overmarsCursor b ∧
        inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc_del)
    · rw [ite_eq_left hc2, Function.update_of_ne hne2]; exact hf
    · rw [ite_eq_right hc2]; exact hf
  have hs1 : (if inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc_del) then
      Function.update s.slices (s.liveSliceIdx b)
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (s.slices (s.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (s.bktSalt b) u))
    else s.slices) (s.rebSliceIdx b) = s.slices (s.rebSliceIdx b) := by
    by_cases hc1 : inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc_del)
    · rw [ite_eq_left hc1, Function.update_of_ne hne1]
    · rw [ite_eq_right hc1]
  have hmid := hs2 _ hs1
  by_cases hc3 : (decide (s.rebStage = 2 ∧ s.dirtyIdx < s.dirtyCount ∧
        s.dirtyBuckets s.dirtyIdx = b ∧ s.rebCandSalt < sMaxWhp c n_max ∧
        s.rebCollision = 0) &&
      decide (loc_del < s.rebScanCursor ∧
        (s.locState b loc_del = 1 ∨ s.locState b loc_del = 2 + s.oldEp))) = true
  · rw [ite_eq_left hc3, ite_eq_left hc3, Function.update_self, hmid]
  · rw [ite_eq_right hc3, ite_eq_right hc3, hmid]

private theorem fastDelete_rKey_ne {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hc : CoreFastInv c U V n_max θ fs dict)
    {u : Fin U} {b loc_del : ℕ} (hb : b < numBucketsWhp n_max) (hloc_del : loc_del < fs.bktCount b)
    (hb_eq : b = feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val)
    (hst_cur : fs.locState b loc_del = 2 + fs.curEp)
    (hfl_sp : fs.quotArr (fs.physSlot n_max b loc_del) = keyQuotient (bWhp n_max) u.val)
    {m : ℕ → Option (ℕ × ℕ)}
    (hrel : BufMapRel (numBucketsWhp n_max) (2 + fs.curEp) fs.bktCount fs.locState
      (fs.rKeyAt c U n_max θ) m)
    {rk b' l' : ℕ} (hne : l' ≠ loc_del) (hm : m rk = some (b', l')) :
    rk ≠ fpReducedKey c U n_max θ.2 u := by
  intro heq; subst heq
  obtain ⟨hb', hl', hst', hrk'⟩ := (hrel.2 _ b' l').mp hm
  have hkv_del : fs.keyValAt c U n_max θ.1 b loc_del = u.val := by
    dsimp only [FastState.keyValAt]
    rw [hfl_sp, hb_eq, feistelReconstruct_feistelBucket (bWhp n_max) _ u.val]
  have hrk_del : fs.rKeyAt c U n_max θ b loc_del = fpReducedKey c U n_max θ.2 u := by
    dsimp only [FastState.rKeyAt]; simp [hkv_del, u.isLt]
  rcases hc.curEp_or with hcep | hcep <;>
    have hbl := hc.rKey_buf_inj b' hb' l' hl' b hb loc_del hloc_del
      (by omega) (by omega) (hrk'.trans hrk_del.symm) <;>
    exact hne hbl.2

private theorem buf_update23_at_self {α : Type*} (f : ℕ → α) (a₀ a₁ : α) (st ep : ℕ)
    (hep : ep = 0 ∨ ep = 1) :
    (if st = 2 then Function.update f 0 a₀
     else if st = 3 then Function.update f 1 a₁ else f) ep =
      if st = 2 + ep then (if ep = 0 then a₀ else a₁) else f ep := by
  rcases hep with rfl | rfl
  · by_cases h2 : st = 2
    · simp [h2]
    · by_cases h3 : st = 3 <;> simp [h2, h3]
  · by_cases h2 : st = 2
    · simp [h2]
    · by_cases h3 : st = 3 <;> simp [h2, h3]

private theorem buf_update23_at_other {α : Type*} (f : ℕ → α) (a₀ a₁ : α) (st ep : ℕ)
    (hep : ep = 0 ∨ ep = 1) (hne : st ≠ 2 + ep) :
    (if st = 2 then Function.update f 0 a₀
     else if st = 3 then Function.update f 1 a₁ else f) ep = f ep := by
  rw [buf_update23_at_self f a₀ a₁ st ep hep, ite_eq_right hne]

theorem fastDelete_clean_props {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hv : ValidFastState c U V n_max θ fs dict)
    (hdom_sub : (Dictionary.dom dict : Set (Fin U)) ⊆ (W_keys : Set (Fin U)))
    (hsalt_cur : SaltBoundAt c U n_max θ W_keys fs) (u : Fin U) :
    let fs' := fastDelete c U n_max θ fs u
    fs'.epochClock = fs.epochClock ∧
    fs'.curEp = fs.curEp ∧
    (fs'.buf fs'.curEp).itemAlloc = (fs.buf fs.curEp).itemAlloc ∧
    (∀ k < 2 ^ (cTabWhp c * bCharWhp n_max),
      bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs'.buf fs'.curEp) k =
        bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) k) ∧
    stageWorkRemaining c n_max fs' ≤ stageWorkRemaining c n_max fs ∧
    SaltBoundAt c U n_max θ W_keys fs' := by
  have hc := hv.toCore
  set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt (bWhp n_max) _ u.val
  dsimp only [fastDelete]
  have hom_m := fun s => overmarsStep_meta c U n_max b θ s
  cases hfl : fastFindLoc c U n_max θ fs u with
  | none =>
    dsimp only
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hom_m fs
    have hw_eq := stageWorkRemaining_eq_of_meta c n_max h4 h5 h6 h7 h9 h10
      (by dsimp only [FastState.oldEp]; rw [h3, h2])
    refine ⟨h1, h2, by rw [h3, h2], fun k _ => by rw [h3, h2], hw_eq.le, ?_⟩
    intro hs2 hdi; rw [h4] at hs2; rw [h7, h6] at hdi
    rw [h8, h7, h9]; exact hsalt_cur hs2 hdi
  | some loc_del =>
    dsimp only
    have hfl_sp := hv.fastFindLoc_spec u
    dsimp only at hfl_sp; rw [hfl] at hfl_sp
    have hloc_del : loc_del < fs.bktCount b := hfl_sp.1
    set loc_last := fs.bktCount b - 1
    have hloc_last : loc_last < fs.bktCount b := by omega
    set rebActiveB : Bool :=
      decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
        fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
        fs.rebCollision = 0)
    set fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
    set fs2 := if loc_del < loc_last then
      fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1 else fs1
    set fs3 := fastDeleteShrink n_max b loc_last fs2
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hom_m fs3
    have hclk_eq : fs3.epochClock = fs.epochClock := by
      dsimp only [fs3, fastDeleteShrink, fs2, fastDeleteMoveLast, fs1, fastDeleteRemove]
      by_cases hlt : loc_del < loc_last <;> [rw [ite_eq_left hlt]; rw [ite_eq_right hlt]]
    have hep_eq : fs3.curEp = fs.curEp := by
      dsimp only [fs3, fastDeleteShrink, fs2, fastDeleteMoveLast, fs1, fastDeleteRemove]
      by_cases hlt : loc_del < loc_last <;> [rw [ite_eq_left hlt]; rw [ite_eq_right hlt]]
    -- Buffer `curEp` preservation across `fs1` and `fs2`:
    obtain ⟨_, _, curMap, hv_c, hrel_c⟩ := hc.bufCur_valid
    have hrk_u_lt : fpReducedKey c U n_max θ.2 u < 2 ^ (cTabWhp c * bCharWhp n_max) :=
      fpReducedKey_lt c U n_max θ.2 u
    have hbuf1_c :
        (∃ m1, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs1.buf fs.curEp) m1 ∧
          ∀ rk b' l', l' ≠ loc_del → curMap rk = some (b', l') → m1 rk = some (b', l')) ∧
        (fs1.buf fs.curEp).itemAlloc = (fs.buf fs.curEp).itemAlloc ∧
        (∀ k < 2 ^ (cTabWhp c * bCharWhp n_max),
          bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs1.buf fs.curEp) k =
            bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) k) := by
      have hbuf1_eq : fs1.buf fs.curEp =
          if fs.locState b loc_del = 2 + fs.curEp then
            bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
              (fpReducedKey c U n_max θ.2 u)
          else fs.buf fs.curEp := by
        dsimp only [fs1, fastDeleteRemove]
        rw [buf_update23_at_self _ _ _ _ _ hc.curEp_or]
        rcases hc.curEp_or with hcep | hcep <;> simp [hcep]
      rw [hbuf1_eq]
      by_cases hst_cur : fs.locState b loc_del = 2 + fs.curEp
      · rw [ite_eq_left hst_cur]
        obtain ⟨hv_d, _, hia_d, _, _⟩ := hv_c.delete_spec hrk_u_lt
        refine ⟨⟨_, hv_d, fun rk b' l' hne hm => ?_⟩, hia_d,
          fun k _ => bufDelete_everPresent _ _ _ _ k⟩
        have hrk_ne := fastDelete_rKey_ne hc hb hloc_del rfl hst_cur hfl_sp.2 hrel_c hne hm
        rwa [Function.update_of_ne hrk_ne]
      · rw [ite_eq_right hst_cur]
        exact ⟨⟨curMap, hv_c, fun _ _ _ _ h => h⟩, rfl, fun _ _ => rfl⟩
    obtain ⟨⟨m1, hv_m1, hm1_pres⟩, hia1, hev1⟩ := hbuf1_c
    have hbuf2_c :
        (fs2.buf fs.curEp).itemAlloc = (fs.buf fs.curEp).itemAlloc ∧
        (∀ k < 2 ^ (cTabWhp c * bCharWhp n_max),
          bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs2.buf fs.curEp) k =
            bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) k) := by
      dsimp only [fs2]
      by_cases hlt_dl : loc_del < loc_last
      · rw [ite_eq_left hlt_dl]
        have hrk_last_lt : fs.rKeyAt c U n_max θ b loc_last < 2 ^ (cTabWhp c * bCharWhp n_max) := by
          dsimp only [FastState.rKeyAt]
          split_ifs with hu
          · exact fpReducedKey_lt c U n_max θ.2 ⟨_, hu⟩
          · exact Nat.two_pow_pos _
        have hbuf2_eq :
            (fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1).buf fs.curEp =
              if fs.locState b loc_last = 2 + fs.curEp then
                bufInsert (cTabWhp c) (bCharWhp n_max) (fs1.buf fs.curEp)
                  (fs.rKeyAt c U n_max θ b loc_last) b loc_del
              else fs1.buf fs.curEp := by
          dsimp only [fastDeleteMoveLast]
          have hls1 : fs1.locState = fs.locState := rfl
          have hrk1 : fs1.rKeyAt c U n_max θ b loc_last = fs.rKeyAt c U n_max θ b loc_last := rfl
          rw [hls1, hrk1, buf_update23_at_self _ _ _ _ _ hc.curEp_or]
          rcases hc.curEp_or with hcep | hcep <;> simp [hcep]
        rw [hbuf2_eq]
        by_cases hsl_cur : fs.locState b loc_last = 2 + fs.curEp
        · rw [ite_eq_left hsl_cur]
          have hm_last : curMap (fs.rKeyAt c U n_max θ b loc_last) = some (b, loc_last) :=
            (hrel_c.2 _ b loc_last).mpr ⟨hb, hloc_last, hsl_cur, rfl⟩
          have hm1_last := hm1_pres _ b loc_last (by omega) hm_last
          have hev_last := hv_m1.everPresent_of_map_some hrk_last_lt hm1_last
          have hins := hv_m1.insert_spec (b := b) (loc := loc_del) hrk_last_lt
          refine ⟨(hins.2.2.2.2.2.1 hev_last).2.trans hia1, fun k hk => ?_⟩
          rw [hins.2.2.2.2.1 k hk]
          by_cases hkr : k = fs.rKeyAt c U n_max θ b loc_last
          · subst hkr; rw [ite_eq_left rfl, ← hev1 _ hrk_last_lt, hev_last]
          · rw [ite_eq_right hkr]; exact hev1 k hk
        · rw [ite_eq_right hsl_cur]; exact ⟨hia1, hev1⟩
      · rw [ite_eq_right hlt_dl]; exact ⟨hia1, hev1⟩
    have hno_reb_coll : ∀ {prev_loc : ℕ} {s_opt : Fin (sMaxWhp c n_max)},
        fs.rebStage = 2 →
        fs.dirtyBuckets fs.dirtyIdx = b →
        fs.rebCandSalt < sMaxWhp c n_max →
        ¬(loc_last < fs1.rebScanCursor) →
        loc_del < fs1.rebScanCursor →
        Set.InjOn (fpHash c U n_max θ.2 s_opt)
          (W_keys.filter (fun w =>
            feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
              fs.dirtyBuckets fs.dirtyIdx) : Set (Fin U)) →
        btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          ((fastDeleteMoveSlices n_max b loc_del loc_last
            (fs1.fpAt c U n_max θ (fs1.bktSalt b) b loc_last) fs1).1 (fs1.rebSliceIdx b))
          (fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last) = some prev_loc →
        fs.rebCandSalt ≠ s_opt.val := by
      intro prev_loc s_opt hs2 hdb_eq hcs_lt hll_sc hld_sc hs_opt_inj hlk heq_s
      have hstg := hv.stage_valid
      dsimp only [ValidEpochStage] at hstg
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hs2] at hstg
      obtain ⟨_, _, _, _, _, _, hreb⟩ := hstg
      rw [hdb_eq] at hreb
      obtain ⟨hcur_r, _, rm0, hvr0, hrr0⟩ := hreb hcs_lt
      have hroles1 : fs1.liveRole b < 3 ∧ fs1.overmarsRole b < 3 ∧
          fs1.liveRole b ≠ fs1.overmarsRole b := hc.roles_valid b hb
      rw [fastDeleteMoveSlices_rebSliceIdx n_max b loc_del loc_last _ fs1 hroles1] at hlk
      have hr_eq1 : fs1.rebSliceIdx b = fs.rebSliceIdx b := rfl
      have hfp_eq1 : fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last =
          fs.fpAt c U n_max θ fs.rebCandSalt b loc_last := rfl
      rw [hr_eq1, hfp_eq1] at hlk
      have hins_le8 : fs.rebInsCount ≤ 8 * (slabScale n_max) ^ 12 := by
        have hcnt3 := (hc.bktCount_le b hb).trans totalLocalCoordsWhp_le_three_mul
        have hL2 := two_le_slabScale n_max
        have : 4096 ≤ (slabScale n_max) ^ 12 := by
          calc 4096 = 2 ^ 12 := by norm_num
            _ ≤ (slabScale n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
        rcases hcur_r with ⟨_, hi0⟩ | ⟨_, _, hins_le⟩ <;> omega
      have hfp_cl_lt : fs.fpAt c U n_max θ fs.rebCandSalt b loc_last <
          2 ^ fpBitsWhp n_max := by
        dsimp only [FastState.fpAt]
        by_cases hs : fs.rebCandSalt < sMaxWhp c n_max
        · rw [dite_eq_left hs]
          by_cases hu : fs.keyValAt c U n_max θ.1 b loc_last < U
          · rw [dite_eq_left hu]; exact fpHash_lt c U n_max θ.2 ⟨_, hs⟩ ⟨_, hu⟩
          · rw [dite_eq_right hu]; exact Nat.two_pow_pos _
        · rw [dite_eq_right hs]; exact Nat.two_pow_pos _
      have hrm_prev : rm0 (fs.fpAt c U n_max θ fs.rebCandSalt b loc_last) =
          some prev_loc := by
        dsimp only [fs1] at hlk
        rw [fastDeleteRemove_rebSliceIdx _ _ _ _ _ _ _ _ (hc.roles_valid b hb)] at hlk
        split_ifs at hlk
        · have hfp_d_lt : fpOfSalt c U n_max θ.2 fs.rebCandSalt u < 2 ^ fpBitsWhp n_max := by
            dsimp only [fpOfSalt]
            by_cases hs : fs.rebCandSalt < sMaxWhp c n_max
            · rw [dite_eq_left hs]; exact fpHash_lt c U n_max θ.2 ⟨_, hs⟩ u
            · rw [dite_eq_right hs]; exact Nat.two_pow_pos _
          have hvd := hvr0.delete_spec hc.hth hins_le8 hfp_d_lt
          rw [hvd.lookup_eq hc.hth hins_le8 hfp_cl_lt] at hlk
          by_cases heq_fp : fs.fpAt c U n_max θ fs.rebCandSalt b loc_last =
              fpOfSalt c U n_max θ.2 fs.rebCandSalt u
          · change Function.update rm0 (fpOfSalt c U n_max θ.2 fs.rebCandSalt u) none
              (fs.fpAt c U n_max θ fs.rebCandSalt b loc_last) = some prev_loc at hlk
            rw [heq_fp, Function.update_self] at hlk; cases hlk
          · change Function.update rm0 (fpOfSalt c U n_max θ.2 fs.rebCandSalt u) none
              (fs.fpAt c U n_max θ fs.rebCandSalt b loc_last) = some prev_loc at hlk
            rwa [Function.update_of_ne heq_fp] at hlk
        · rwa [hvr0.lookup_eq hc.hth hins_le8 hfp_cl_lt] at hlk
      obtain ⟨hprev_min, _, hfp_prev⟩ := (hrr0.2 _ prev_loc).mp hrm_prev
      have hprev_lt_sc : prev_loc < fs.rebScanCursor :=
        hprev_min.trans_le (Nat.min_le_right _ _)
      have hprev_lt_cnt : prev_loc < fs.bktCount b :=
        hprev_min.trans_le (Nat.min_le_left _ _)
      obtain ⟨hm₁, hfb₁⟩ := hc.mem_dom_of_loc hb hprev_lt_cnt
      obtain ⟨hm₂, hfb₂⟩ := hc.mem_dom_of_loc hb hloc_last
      let u₁ : Fin U :=
        ⟨fs.keyValAt c U n_max θ.1 b prev_loc, (hc.active_item b hb prev_loc hprev_lt_cnt).1⟩
      let u₂ : Fin U :=
        ⟨fs.keyValAt c U n_max θ.1 b loc_last, (hc.active_item b hb loc_last hloc_last).1⟩
      have hw₁ : u₁ ∈ W_keys.filter (fun w =>
          feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
            fs.dirtyBuckets fs.dirtyIdx) :=
        mem_filter.mpr ⟨hdom_sub hm₁, hfb₁.trans hdb_eq.symm⟩
      have hw₂ : u₂ ∈ W_keys.filter (fun w =>
          feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
            fs.dirtyBuckets fs.dirtyIdx) :=
        mem_filter.mpr ⟨hdom_sub hm₂, hfb₂.trans hdb_eq.symm⟩
      have hf₁ : fs.fpAt c U n_max θ fs.rebCandSalt b prev_loc =
          fpHash c U n_max θ.2 s_opt u₁ := by
        dsimp only [FastState.fpAt]; simp [heq_s, s_opt.isLt, u₁.isLt, u₁]
      have hf₂ : fs.fpAt c U n_max θ fs.rebCandSalt b loc_last =
          fpHash c U n_max θ.2 s_opt u₂ := by
        dsimp only [FastState.fpAt]; simp [heq_s, s_opt.isLt, u₂.isLt, u₂]
      have hu_eq : u₁ = u₂ := hs_opt_inj hw₁ hw₂ (hf₁.symm.trans (hfp_prev.trans hf₂))
      have hkv_eq : fs.keyValAt c U n_max θ.1 b prev_loc =
          fs.keyValAt c U n_max θ.1 b loc_last := congrArg Fin.val hu_eq
      have hq₁ := (hc.active_item b hb prev_loc hprev_lt_cnt).2.2.1
      have hq₂ := (hc.active_item b hb loc_last hloc_last).2.2.1
      have hl_eq := hc.quot_inj b hb prev_loc hprev_lt_cnt loc_last hloc_last
        (hq₁.symm.trans (hkv_eq ▸ hq₂))
      change loc_del < fs.rebScanCursor at hld_sc
      change ¬(loc_last < fs.rebScanCursor) at hll_sc
      omega
    have hbuf3_eq : fs3.buf = fs2.buf := rfl
    refine ⟨h1.trans hclk_eq, h2.trans hep_eq,
      by rw [h3, hbuf3_eq, h2, hep_eq]; exact hbuf2_c.1,
      fun k hk => by rw [h3, hbuf3_eq, h2, hep_eq]; exact hbuf2_c.2 k hk, ?_, ?_⟩
    · -- `stageWorkRemaining` across `fastDelete` (`≤`)
      have hw_om : stageWorkRemaining c n_max (overmarsStep c U n_max θ b fs3) =
          stageWorkRemaining c n_max fs3 :=
        stageWorkRemaining_eq_of_meta c n_max h4 h5 h6 h7 h9 h10
          (by dsimp only [FastState.oldEp]; rw [h3, h2])
      rw [hw_om]
      have hw32 : stageWorkRemaining c n_max fs3 = stageWorkRemaining c n_max fs2 :=
        stageWorkRemaining_eq_of_meta c n_max rfl rfl rfl rfl rfl rfl rfl
      rw [hw32]
      have hold4_na : fs.rebStage = 4 →
          (fs2.buf fs2.oldEp).nodeAlloc = (fs.buf fs.oldEp).nodeAlloc := by
        intro hs4
        have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
          dsimp only [FastState.oldEp]; rcases hc.curEp_or with h | h <;> omega
        have hbo := hc.bufOld_valid
        rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_left hs4] at hbo
        have hno_old := hbo.1
        have h1_na : fs1.buf fs.oldEp = fs.buf fs.oldEp := by
          dsimp only [fs1, fastDeleteRemove]
          exact buf_update23_at_other _ _ _ _ _ hold_or (hno_old b hb loc_del hloc_del)
        dsimp only [fs2]
        by_cases hlt_dl : loc_del < loc_last
        · rw [ite_eq_left hlt_dl]
          have hold2 :
              (fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1).oldEp =
                fs.oldEp := rfl
          rw [hold2]; dsimp only [fastDeleteMoveLast]
          have hls1 : fs1.locState = fs.locState := rfl; rw [hls1]
          rw [buf_update23_at_other _ _ _ _ _ hold_or (hno_old b hb loc_last hloc_last), h1_na]
        · rw [ite_eq_right hlt_dl]
          have hold1 : fs1.oldEp = fs.oldEp := rfl; rw [hold1, h1_na]
      dsimp only [fs2]
      by_cases hlt_dl : loc_del < loc_last
      · rw [ite_eq_left hlt_dl]
        by_cases hs4 : fs.rebStage = 4
        · have hw_eq : stageWorkRemaining c n_max
              (fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1) =
              stageWorkRemaining c n_max fs := by
            dsimp only [stageWorkRemaining]
            have hst_mv :
                (fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1).rebStage =
                  fs.rebStage := rfl
            simp only [hst_mv, hs4, show ¬(4 = 0) by decide, show ¬(4 = 1) by decide,
              show ¬(4 = 2) by decide, show ¬(4 = 3) by decide, ↓reduceIte]
            have h := hold4_na hs4
            dsimp only [fs2] at h; rw [ite_eq_left hlt_dl] at h; exact h
          exact hw_eq.le
        · -- `fs.rebStage ≠ 4`: check whether `rebCandSalt` bumped in `fastDeleteMoveLast`
          dsimp only [fastDeleteMoveLast]
          have h1_meta : fs1.rebStage = fs.rebStage ∧ fs1.stageCursor = fs.stageCursor ∧
              fs1.dirtyCount = fs.dirtyCount ∧ fs1.dirtyIdx = fs.dirtyIdx ∧
              fs1.rebCandSalt = fs.rebCandSalt ∧ fs1.rebScanCursor = fs.rebScanCursor :=
            ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          by_cases hreb_act : (rebActiveB && decide (fs1.locState b loc_last = 1 ∨
              fs1.locState b loc_last = 2 + fs1.oldEp)) = true
          · simp only [hreb_act, ↓reduceIte]
            obtain ⟨hra_t, hst_last_ok⟩ := Bool.and_eq_true_iff.mp hreb_act
            rw [decide_eq_true_iff] at hra_t hst_last_ok
            obtain ⟨hs2, hd2, hdb_eq, hcs_lt, _⟩ := hra_t
            by_cases hll_sc : loc_last < fs1.rebScanCursor
            · simp only [hll_sc, ↓reduceIte]
              dsimp only [stageWorkRemaining]
              rw [h1_meta.1, h1_meta.2.1, h1_meta.2.2.1, h1_meta.2.2.2.1, h1_meta.2.2.2.2.1,
                h1_meta.2.2.2.2.2]
              simp only [hs4, ↓reduceIte]; exact le_rfl
            · simp only [hll_sc, ↓reduceIte]
              by_cases hld_sc : loc_del < fs1.rebScanCursor
              · simp only [hld_sc, ↓reduceIte]
                cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                    ((fastDeleteMoveSlices n_max b loc_del loc_last
                      (fs1.fpAt c U n_max θ (fs1.bktSalt b) b loc_last) fs1).1
                      (fs1.rebSliceIdx b))
                    (fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last) with
                | none =>
                  dsimp only [stageWorkRemaining]
                  rw [h1_meta.1, h1_meta.2.1, h1_meta.2.2.1, h1_meta.2.2.2.1, h1_meta.2.2.2.2.1,
                    h1_meta.2.2.2.2.2]
                  simp only [hs4, ↓reduceIte]; exact le_rfl
                | some prev_loc =>
                  obtain ⟨s_opt, hs_opt_inj, hc_le_s⟩ := hsalt_cur hs2 hd2
                  have hne_s : fs.rebCandSalt ≠ s_opt.val :=
                    hno_reb_coll hs2 hdb_eq hcs_lt hll_sc hld_sc hs_opt_inj hlk
                  dsimp only [stageWorkRemaining]
                  simp only [h1_meta.1, h1_meta.2.2.1, h1_meta.2.2.2.1, h1_meta.2.2.2.2.1, hs2,
                    show ¬(2 = 0) by decide, show ¬(2 = 1) by decide, ↓reduceIte, Nat.min_zero]
                  have hs_lt_max : fs.rebCandSalt + 1 ≤ sMaxWhp c n_max - 1 := by
                    have := s_opt.isLt; omega
                  have hsub1 : sMaxWhp c n_max - 1 - fs.rebCandSalt =
                      (sMaxWhp c n_max - 1 - (fs.rebCandSalt + 1)) + 1 := by omega
                  rw [hsub1, Nat.add_mul, one_mul]; omega
              · simp only [hld_sc, ↓reduceIte]
                dsimp only [stageWorkRemaining]
                rw [h1_meta.1, h1_meta.2.1, h1_meta.2.2.1, h1_meta.2.2.2.1, h1_meta.2.2.2.2.1,
                  h1_meta.2.2.2.2.2]
                simp only [hs4, ↓reduceIte]; exact le_rfl
          · simp only [hreb_act, Bool.false_eq_true, ↓reduceIte]
            dsimp only [stageWorkRemaining]
            rw [h1_meta.1, h1_meta.2.1, h1_meta.2.2.1, h1_meta.2.2.2.1, h1_meta.2.2.2.2.1,
              h1_meta.2.2.2.2.2]
            simp only [hs4, ↓reduceIte]; exact le_rfl
      · rw [ite_eq_right hlt_dl]
        by_cases hs4 : fs.rebStage = 4
        · have h := hold4_na hs4; dsimp only [fs2] at h; rw [ite_eq_right hlt_dl] at h
          exact (stageWorkRemaining_eq_of_meta (s₁ := fs1) (s₂ := fs) c n_max
            rfl rfl rfl rfl rfl rfl h).le
        · dsimp only [stageWorkRemaining]
          have hst1 : fs1.rebStage = fs.rebStage := rfl
          rw [hst1]; simp only [hs4, ↓reduceIte]; exact le_rfl
    · -- `SaltBoundAt` across `fastDelete`: prove directly from `hsalt_cur`.
      have h3_meta : fs3.rebStage = fs.rebStage ∧ fs3.dirtyCount = fs.dirtyCount ∧
          fs3.dirtyIdx = fs.dirtyIdx ∧ fs3.dirtyBuckets = fs.dirtyBuckets ∧
          fs3.rebCandSalt = fs2.rebCandSalt := by
        dsimp only [fs3, fastDeleteShrink, fs2, fastDeleteMoveLast, fs1, fastDeleteRemove]
        by_cases hlt_dl : loc_del < loc_last
        · rw [ite_eq_left hlt_dl]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
        · rw [ite_eq_right hlt_dl]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      intro hs2' hdi'
      rw [h4, h3_meta.1] at hs2'
      rw [h7, h6, h3_meta.2.2.1, h3_meta.2.1] at hdi'
      rw [h8, h7, h9, h3_meta.2.2.2.1, h3_meta.2.2.1, h3_meta.2.2.2.2]
      obtain ⟨s_opt, hs_opt_inj, hc_le_s⟩ := hsalt_cur hs2' hdi'
      have hs2 : fs.rebStage = 2 := hs2'
      refine ⟨s_opt, hs_opt_inj, ?_⟩
      dsimp only [fs2]
      by_cases hlt_dl : loc_del < loc_last
      · rw [ite_eq_left hlt_dl]; dsimp only [fastDeleteMoveLast]
        split_ifs with hreb_act hll_sc hld_sc
        · exact hc_le_s
        · cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              ((fastDeleteMoveSlices n_max b loc_del loc_last
                (fs1.fpAt c U n_max θ (fs1.bktSalt b) b loc_last) fs1).1
                (fs1.rebSliceIdx b))
              (fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last) with
          | none => exact hc_le_s
          | some prev_loc =>
            dsimp only
            obtain ⟨hra_t, _⟩ := Bool.and_eq_true_iff.mp hreb_act
            rw [decide_eq_true_iff] at hra_t
            obtain ⟨_, _, hdb_eq, hcs_lt, _⟩ := hra_t
            have hne_s := hno_reb_coll hs2 hdb_eq hcs_lt hll_sc hld_sc hs_opt_inj hlk
            change fs.rebCandSalt + 1 ≤ s_opt.val
            omega
        · exact hc_le_s
        · exact hc_le_s
      · rw [ite_eq_right hlt_dl]; exact hc_le_s

end Cslib.DataStructure.Dictionary.SuccinctWhp
