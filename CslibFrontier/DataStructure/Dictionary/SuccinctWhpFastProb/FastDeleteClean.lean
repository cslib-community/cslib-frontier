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
  split_ifs <;> simp [Function.update_of_ne hne1, Function.update_of_ne hne2]

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
  split_ifs <;> simp [Function.update_of_ne hne1, Function.update_of_ne hne2]

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
  rcases hep with rfl | rfl <;> split_ifs <;> simp_all

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
    obtain ⟨hclk3, hep3, hold3, hst3, hsc3, hdc3, hdi3, hdb3⟩ :
        fs3.epochClock = fs.epochClock ∧ fs3.curEp = fs.curEp ∧ fs3.oldEp = fs.oldEp ∧
          fs3.rebStage = fs.rebStage ∧ fs3.stageCursor = fs.stageCursor ∧
          fs3.dirtyCount = fs.dirtyCount ∧ fs3.dirtyIdx = fs.dirtyIdx ∧
          fs3.dirtyBuckets = fs.dirtyBuckets := by
      dsimp only [fs3, fastDeleteShrink, fs2]
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
      split_ifs with hst_cur
      · obtain ⟨hv_d, _, hia_d, _, _⟩ := hv_c.delete_spec hrk_u_lt
        refine ⟨⟨_, hv_d, fun rk b' l' hne hm => ?_⟩, hia_d,
          fun k _ => bufDelete_everPresent _ _ _ _ k⟩
        have hrk_ne := fastDelete_rKey_ne hc hb hloc_del rfl hst_cur hfl_sp.2 hrel_c hne hm
        rwa [Function.update_of_ne hrk_ne]
      · exact ⟨⟨curMap, hv_c, fun _ _ _ _ h => h⟩, rfl, fun _ _ => rfl⟩
    obtain ⟨⟨m1, hv_m1, hm1_pres⟩, hia1, hev1⟩ := hbuf1_c
    have hbuf2_c :
        (fs2.buf fs.curEp).itemAlloc = (fs.buf fs.curEp).itemAlloc ∧
        (∀ k < 2 ^ (cTabWhp c * bCharWhp n_max),
          bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs2.buf fs.curEp) k =
            bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) k) := by
      dsimp only [fs2]
      split_ifs with hlt_dl
      · have hrk_last_lt : fs.rKeyAt c U n_max θ b loc_last < 2 ^ (cTabWhp c * bCharWhp n_max) := by
          dsimp only [FastState.rKeyAt]
          split_ifs with hu
          exacts [fpReducedKey_lt c U n_max θ.2 ⟨_, hu⟩, Nat.two_pow_pos _]
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
        split_ifs with hsl_cur
        · have hm_last : curMap (fs.rKeyAt c U n_max θ b loc_last) = some (b, loc_last) :=
            (hrel_c.2 _ b loc_last).mpr ⟨hb, hloc_last, hsl_cur, rfl⟩
          have hm1_last := hm1_pres _ b loc_last (by omega) hm_last
          have hev_last := hv_m1.everPresent_of_map_some hrk_last_lt hm1_last
          have hins := hv_m1.insert_spec (b := b) (loc := loc_del) hrk_last_lt
          refine ⟨(hins.2.2.2.2.2.1 hev_last).2.trans hia1, fun k hk => ?_⟩
          rw [hins.2.2.2.2.1 k hk]
          split_ifs with hkr
          · subst hkr; rw [← hev1 _ hrk_last_lt, hev_last]
          · exact hev1 k hk
        · exact ⟨hia1, hev1⟩
      · exact ⟨hia1, hev1⟩
    -- `rebCandSalt` / `rebScanCursor` are unchanged, unless relocating `loc_last` collides in the
    -- stage-2 rebuild slice; that bumps the candidate salt, which stays below an injective salt.
    have hcand3 : (fs3.rebCandSalt = fs.rebCandSalt ∧ fs3.rebScanCursor = fs.rebScanCursor) ∨
        (fs.rebStage = 2 ∧ fs3.rebScanCursor = 0 ∧ fs3.rebCandSalt = fs.rebCandSalt + 1 ∧
          ∃ s_opt : Fin (sMaxWhp c n_max),
            Set.InjOn (fpHash c U n_max θ.2 s_opt)
              (W_keys.filter (fun w =>
                feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
                  fs.dirtyBuckets fs.dirtyIdx) : Set (Fin U)) ∧
            fs.rebCandSalt + 1 ≤ s_opt.val) := by
      dsimp only [fs3, fastDeleteShrink, fs2]
      split_ifs with hlt_dl
      swap
      · exact .inl ⟨rfl, rfl⟩
      dsimp only [fastDeleteMoveLast]
      split_ifs with hreb_act hll_sc hld_sc
      · exact .inl ⟨rfl, rfl⟩
      · rcases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            ((fastDeleteMoveSlices n_max b loc_del loc_last
              (fs1.fpAt c U n_max θ (fs1.bktSalt b) b loc_last) fs1).1
              (fs1.rebSliceIdx b))
            (fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last) with _ | prev_loc
        · exact .inl ⟨rfl, rfl⟩
        obtain ⟨hs2, hd2, hdb_eq, hcs_lt, -⟩ :=
          of_decide_eq_true (Bool.and_eq_true_iff.mp hreb_act).1
        obtain ⟨s_opt, hs_opt_inj, hc_le_s⟩ := hsalt_cur hs2 hd2
        refine .inr ⟨hs2, rfl, rfl, s_opt, hs_opt_inj,
          Nat.lt_of_le_of_ne hc_le_s fun heq_s => ?_⟩
        -- A collision puts `loc_last` and an earlier scanned coordinate under one key.
        have hstg := hv.stage_valid
        dsimp only [ValidEpochStage] at hstg
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hs2] at hstg
        obtain ⟨_, _, _, _, _, _, hreb⟩ := hstg
        rw [hdb_eq] at hreb
        obtain ⟨hcur_r, _, rm0, hvr0, hrr0⟩ := hreb hcs_lt
        rw [fastDeleteMoveSlices_rebSliceIdx n_max b loc_del loc_last _ fs1
          (hc.roles_valid b hb)] at hlk
        change btreeLookup _ _ _ (fs1.slices (fs.rebSliceIdx b))
          (fs.fpAt c U n_max θ fs.rebCandSalt b loc_last) = some prev_loc at hlk
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
          rw [dite_eq_left hcs_lt]
          split_ifs with hu
          exacts [fpHash_lt c U n_max θ.2 ⟨_, hcs_lt⟩ ⟨_, hu⟩, Nat.two_pow_pos _]
        have hrm_prev : rm0 (fs.fpAt c U n_max θ fs.rebCandSalt b loc_last) =
            some prev_loc := by
          dsimp only [fs1] at hlk
          rw [fastDeleteRemove_rebSliceIdx _ _ _ _ _ _ _ _ (hc.roles_valid b hb)] at hlk
          split_ifs at hlk
          · have hfp_d_lt : fpOfSalt c U n_max θ.2 fs.rebCandSalt u < 2 ^ fpBitsWhp n_max := by
              simp only [fpOfSalt, hcs_lt, ↓reduceDIte]
              exact fpHash_lt c U n_max θ.2 ⟨_, hcs_lt⟩ u
            have hvd := hvr0.delete_spec hc.hth hins_le8 hfp_d_lt
            rw [hvd.lookup_eq hc.hth hins_le8 hfp_cl_lt] at hlk
            change Function.update rm0 (fpOfSalt c U n_max θ.2 fs.rebCandSalt u) none
              (fs.fpAt c U n_max θ fs.rebCandSalt b loc_last) = some prev_loc at hlk
            rw [Function.update_apply] at hlk
            split_ifs at hlk
            exact hlk
          · rwa [hvr0.lookup_eq hc.hth hins_le8 hfp_cl_lt] at hlk
        obtain ⟨hprev_min, _, hfp_prev⟩ := (hrr0.2 _ prev_loc).mp hrm_prev
        have := hprev_min.trans_le (Nat.min_le_right _ _)
        have hprev_lt_cnt : prev_loc < fs.bktCount b := hprev_min.trans_le (Nat.min_le_left _ _)
        obtain ⟨hm₁, hfb₁⟩ := hc.mem_dom_of_loc hb hprev_lt_cnt
        obtain ⟨hm₂, hfb₂⟩ := hc.mem_dom_of_loc hb hloc_last
        let u₁ : Fin U := ⟨_, (hc.active_item b hb prev_loc hprev_lt_cnt).1⟩
        let u₂ : Fin U := ⟨_, (hc.active_item b hb loc_last hloc_last).1⟩
        have hu_eq : u₁ = u₂ := hs_opt_inj
          (mem_filter.mpr ⟨hdom_sub hm₁, hfb₁.trans hdb_eq.symm⟩)
          (mem_filter.mpr ⟨hdom_sub hm₂, hfb₂.trans hdb_eq.symm⟩) <| by
            simpa [FastState.fpAt, heq_s, s_opt.isLt, u₁.isLt, u₂.isLt, u₁, u₂] using hfp_prev
        have hkv_eq : fs.keyValAt c U n_max θ.1 b prev_loc =
            fs.keyValAt c U n_max θ.1 b loc_last := congrArg Fin.val hu_eq
        have hq₁ := (hc.active_item b hb prev_loc hprev_lt_cnt).2.2.1
        have hq₂ := (hc.active_item b hb loc_last hloc_last).2.2.1
        have hl_eq := hc.quot_inj b hb prev_loc hprev_lt_cnt loc_last hloc_last
          (hq₁.symm.trans (hkv_eq ▸ hq₂))
        change loc_del < fs.rebScanCursor at hld_sc
        change ¬(loc_last < fs.rebScanCursor) at hll_sc
        omega
      · exact .inl ⟨rfl, rfl⟩
      · exact .inl ⟨rfl, rfl⟩
    have hbuf3_eq : fs3.buf = fs2.buf := rfl
    refine ⟨h1.trans hclk3, h2.trans hep3,
      by rw [h3, hbuf3_eq, h2, hep3]; exact hbuf2_c.1,
      fun k hk => by rw [h3, hbuf3_eq, h2, hep3]; exact hbuf2_c.2 k hk, ?_, ?_⟩
    · -- `stageWorkRemaining` across `fastDelete` (`≤`)
      rw [stageWorkRemaining_eq_of_meta c n_max h4 h5 h6 h7 h9 h10
        (by dsimp only [FastState.oldEp]; rw [h3, h2])]
      by_cases hs4 : fs.rebStage = 4
      · -- Stage 4: the remaining work is the old buffer's `nodeAlloc`, which deletion preserves.
        have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
          dsimp only [FastState.oldEp]; rcases hc.curEp_or with h | h <;> omega
        have hbo := hc.bufOld_valid
        rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_left hs4] at hbo
        have h1_na : fs1.buf fs.oldEp = fs.buf fs.oldEp := by
          dsimp only [fs1, fastDeleteRemove]
          exact buf_update23_at_other _ _ _ _ _ hold_or (hbo.1 b hb loc_del hloc_del)
        have h2_na : fs2.buf fs.oldEp = fs.buf fs.oldEp := by
          dsimp only [fs2]
          split_ifs
          · exact (buf_update23_at_other _ _ _ _ _ hold_or
              (hbo.1 b hb loc_last hloc_last)).trans h1_na
          · exact h1_na
        dsimp only [stageWorkRemaining]
        simp only [hst3, hold3, hs4, Nat.reduceEqDiff, ↓reduceIte]
        rw [hbuf3_eq, h2_na]
      rcases hcand3 with ⟨hcs3, hcur3⟩ | ⟨hs2, hcur3, hcs3, s_opt, -, hle⟩ <;>
        dsimp only [stageWorkRemaining] <;>
        simp only [hst3, hsc3, hdc3, hdi3, hcs3, hcur3, hs4, ↓reduceIte]
      · exact le_rfl
      · simp only [hs2, Nat.reduceEqDiff, ↓reduceIte, Nat.min_zero]
        have hsub1 : sMaxWhp c n_max - 1 - fs.rebCandSalt =
            (sMaxWhp c n_max - 1 - (fs.rebCandSalt + 1)) + 1 := by
          have := s_opt.isLt; omega
        rw [hsub1, Nat.add_mul, one_mul]; omega
    · -- `SaltBoundAt` across `fastDelete`: prove directly from `hsalt_cur` and `hcand3`.
      intro hs2' hdi'
      rw [h8, h7, h9, hdb3, hdi3]
      rcases hcand3 with ⟨hcs3, -⟩ | ⟨-, -, hcs3, hbump⟩ <;> rw [hcs3]
      exacts [hsalt_cur (hst3 ▸ h4 ▸ hs2') (hdc3 ▸ h6 ▸ hdi3 ▸ h7 ▸ hdi'), hbump]

end Cslib.DataStructure.Dictionary.SuccinctWhp
