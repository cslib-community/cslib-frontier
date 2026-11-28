/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.RebRole
import CslibFrontier.Tactic.Realize

/-!
# Fast Deletion Removal in Rebuild Slice & Info Reader

Stage-2 rebuild-slice deletion helper and read-only pre-fetch `(st_del, (rKey_u, fp_live_u))`
for `fastDeleteRemoveGenProg`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delRemRebGenProg`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delRemReadInfoGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_delRemRebGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delRemRebGenProg_fastStep`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_delRemReadInfoGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delRemReadInfoGenProg_spec`
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

attribute [local simp] clientResult_pure_whp clientState_pure_whp

/-- Guard helper for `delRemRebGenProg`: return `1` iff Stage 2 is actively scanning bucket `b`
past `loc_del` and `st_del ∈ {1, 2 + oldEp}`. -/
@[irreducible] private def delRemRebCheckProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((((cp, base), b), loc_del), st_del) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let z2 ← pure 2
    let rebAct ← readRebActiveBGenProg ((cp, base), b)
    let rebCur ← readHdrProg (base, hdrRebScanCursor)
    let oldEp ← readOldEpProg base
    let tagOld ← pure (z2 + oldEp)
    if rebAct = z1 ∧ loc_del < rebCur ∧ (st_del = z1 ∨ st_del = tagOld) then
      pure z1
    else
      pure z0

private theorem realizes_delRemRebCheck :
    Realizes .exact delRemRebCheckProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((((cp, base), _), _), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1))
      (fun _ _ => 0) := by
  unfold delRemRebCheckProg
  realize [realizes_readRebActiveBGen, realizes_readHdr, realizes_readOldEp]
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, loc_del⟩, st_del⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hce⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h2w := henv.two_le_w
    have h32_sp := headerWords_le_largeSpaceWhp c U V w n_max
    obtain ⟨hst_ra, hres_ra, _, _⟩ := readRebActiveBGenProg_spec henv hrep (b := b) (s := s)
    obtain ⟨hst_rc, hres_rc, _, _⟩ := readHdrProg_large_spec c U V w n_max
      (base := base) (hdrOff := hdrRebScanCursor) (s := s) (by decide)
    obtain ⟨hst_o, hres_o, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
      hrep.2.2.2.1 (s := s)
    have hdc_mem : s.mem (base + hdrDirtyCount) ≤ qEpochWhp n_max :=
      hrep.2.2.2.2.2.2.2.1.trans_le hrep.1
    have hfit_old : Fits w (2 + fs.oldEp) := by
      have h4 : 4 ≤ 2 ^ w := (by decide : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right two_pos h2w)
      rcases hce with hc | hc <;> simp only [Fits, FastState.oldEp, hc] <;> omega
    simp only [hst_ra, hres_ra, hst_rc, hres_rc, hst_o, hres_o, wp_large_qEpoch hth] at *
    first
    | exact h2w
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hdc_mem
    | exact hfit_old
  )

/-- Evaluate `fpOfSaltOpt` on `rebCandSalt` and `u_val` without mutating memory. -/
@[irreducible] private def readCandFpGenProg : (WhpParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((wp, base), u_val) => do
    let cand ← readHdrProg (base, hdrRebCandSalt)
    let hrt ← mkHashRtGenProg (wp, base)
    fpOfSaltOptRtProg ((hrt, cand), u_val)

private theorem realizes_readCandFpGen :
    Realizes .exact readCandFpGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((wp, base), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem)
      (fun _ _ => 0) := by
  unfold readCandFpGenProg
  realize [realizes_readHdr, realizes_mkHashRtGen, realizes_fpOfSaltOptRt]
  all_goals (
    rcases d with ⟨⟨wp, base⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_wp, hseed⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have h32_sp := headerWords_le_largeSpaceWhp c U V w n_max
    obtain ⟨hst_cs, _, _, _⟩ := readHdrProg_large_spec c U V w n_max
      (base := base) (hdrOff := hdrRebCandSalt) (s := s) (by decide)
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    simp only [hst_cs, hmh_st, hmh_res] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
  )

/-- Active deletion helper for `delRemRebGenProg`: evaluate `fpOfSalt rebCandSalt u` and delete it
from `rebSlice[b]`. -/
@[irreducible] private def delRemRebActiveProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((wp, base), b), u_val) => do
    let fp_c ← readCandFpGenProg ((wp, base), u_val)
    let rIdx ← readRebSliceIdxGenProg ((wp.1, base), b)
    btreeDeleteGenProg (((wp.1, base), rIdx), fp_c)

private theorem realizes_delRemRebActive :
    Realizes .exact delRemRebActiveProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((wp, base), b), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (rm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.rebSliceIdx b < 3 * numBucketsWhp n_max ∧
          fs.rebInsCount ≤ 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm)
      (fun _ _ => 0) := by
  unfold delRemRebActiveProg
  realize [realizes_readCandFpGen, realizes_readRebSliceIdxGen, realizes_btreeDeleteGen]
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, rm, henv, heq_wp, hseed, hrep, hb, hrIdx, hins_r, hv_r⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have h32_sp := headerWords_le_largeSpaceWhp c U V w n_max
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hst_cs, hres_cs, _, _⟩ := readHdrProg_large_spec c U V w n_max
      (base := base) (hdrOff := hdrRebCandSalt) (s := s) (by decide)
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfp_st, hfp_res, _, _⟩ :=
      fpOfSaltOptRtProg_spec (salt := s.mem (base + hdrRebCandSalt)) (kv := u_val)
        henv hseed (s := s)
    have hrc_st : (Memory.spec 0).clientState s
        (readCandFpGenProg ((mkWhpParams c U V w n_max, base), u_val)) = s := by
      unfold readCandFpGenProg
      rw [clientState_bind, hst_cs, hres_cs, clientState_bind, hmh_st, hmh_res, hfp_st]
    have hrc_res : (Memory.spec 0).clientResult s
        (readCandFpGenProg ((mkWhpParams c U V w n_max, base), u_val)) =
        (if hs : s.mem (base + hdrRebCandSalt) < sMaxWhp c n_max then
          if hu : u_val < U then fpHash c U n_max θ.2 ⟨s.mem (base + hdrRebCandSalt), hs⟩
            ⟨u_val, hu⟩ else 0
         else 0) := by
      unfold readCandFpGenProg
      rw [clientResult_bind, hst_cs, hres_cs, clientResult_bind, hmh_st, hmh_res, hfp_res]
    obtain ⟨hrs_st, hrs_res, _, _⟩ := readRebSliceIdxGenProg_spec henv hb hrep (s := s)
    have hfp_lt := fpOfSaltOpt_lt c U n_max (s.mem (base + hdrRebCandSalt)) u_val θ.2
    simp only [hcp_eq, hrc_st, hrc_res, hrs_st, hrs_res, wp_large_M hth] at *
    first
    | exact hb
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, fs.rebInsCount, fs.slices (fs.rebSliceIdx b), rm,
        henv, rfl, hrIdx, hins_r, hrep.slice_rep hrIdx, hv_r, hfp_lt⟩
  )

/-- Sub-helper 6.1d: delete `fpOfSalt rebCandSalt u` from `rebSlice[b]` when Stage 2 is actively
scanning bucket `b` past `loc_del`. -/
@[irreducible] def delRemRebGenProg :
    (((WhpParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((wp, base), b), loc_del), (st_del, u_val)) => do
    let z1 ← pure 1
    let act ← delRemRebCheckProg ((((wp.1, base), b), loc_del), st_del)
    if act = z1 then
      delRemRebActiveProg (((wp, base), b), u_val)
    else
      pure ()

theorem realizes_delRemRebGen :
    Realizes .exact delRemRebGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((((wp, base), b), _), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max ∧
          fs.rebSliceIdx b < 3 * numBucketsWhp n_max ∧
          (decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
              fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
              fs.rebCollision = 0) = true →
            fs.rebInsCount ≤ 8 * (slabScale n_max) ^ 12 ∧
            ∃ rm, ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm))
      (fun _ _ => 0) := by
  unfold delRemRebGenProg
  realize [realizes_delRemRebCheck, realizes_delRemRebActive]
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, b⟩, loc_del⟩, ⟨st_del, u_val⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hce, hb, hrIdx, hreb_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have h32_sp := headerWords_le_largeSpaceWhp c U V w n_max
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hst_ra, hres_ra, _, _⟩ := readRebActiveBGenProg_spec henv hrep (b := b) (s := s)
    obtain ⟨hst_rc, hres_rc, _, _⟩ := readHdrProg_large_spec c U V w n_max
      (base := base) (hdrOff := hdrRebScanCursor) (s := s) (by decide)
    obtain ⟨hst_o, hres_o, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
      hrep.2.2.2.1 (s := s)
    have hck_st : (Memory.spec 0).clientState s
        (delRemRebCheckProg
          ((((mkWhpCoreParams c U V w n_max, base), b), loc_del), st_del)) = s := by
      unfold delRemRebCheckProg
      simp only [pure_bind]
      rw [clientState_bind, hst_ra, hres_ra, clientState_bind, hst_rc, hres_rc,
        clientState_bind, hst_o, hres_o]
      split_ifs <;> rfl
    have hck_res : (Memory.spec 0).clientResult s
        (delRemRebCheckProg ((((mkWhpCoreParams c U V w n_max, base), b), loc_del), st_del)) = 1 →
        decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
          fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
          fs.rebCollision = 0) = true := by
      unfold delRemRebCheckProg
      simp only [pure_bind]
      rw [clientResult_bind, hst_ra, hres_ra, clientResult_bind, hst_rc, hres_rc,
        clientResult_bind, hst_o, hres_o]
      by_cases hd : decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
          fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
          fs.rebCollision = 0) = true
      · exact fun _ => hd
      · rw [ite_eq_right hd, ite_eq_right (by simp), clientResult_pure_whp]; omega
    simp only [hcp_eq, hck_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hce⟩
    | (obtain ⟨hins_r, rm, hv_r⟩ := hreb_fn (hck_res (by assumption))
       exact ⟨c, U, V, w, n_max, θ, fs, rm, henv, rfl, hseed, hrep, hb, hrIdx, hins_r, hv_r⟩)
  )

theorem delRemRebGenProg_fastStep {c U V w n_max base b loc_del st_del : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State} (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max)
    (hrIdx : fs.rebSliceIdx b < 3 * numBucketsWhp n_max)
    (hreb_fn : decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
        fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
        fs.rebCollision = 0) = true →
      fs.rebInsCount ≤ 8 * (slabScale n_max) ^ 12 ∧
      ∃ rm, ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delRemRebGenProg
      ((((mkWhpParams c U V w n_max, base), b), loc_del), (st_del, u.val))
    let s' := (Memory.spec 0).clientState s prog
    let rebActiveB : Bool :=
      decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
        fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
        fs.rebCollision = 0)
    let rIdx := fs.rebSliceIdx b
    let slices3 :=
      if rebActiveB && decide (loc_del < fs.rebScanCursor ∧
          (st_del = 1 ∨ st_del = 2 + fs.oldEp)) then
        Function.update fs.slices rIdx
          (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices rIdx) (fpOfSalt c U n_max θ.2 fs.rebCandSalt u))
      else fs.slices
    memoryCost prog s ≤ hashEvalCostWhp c + 290 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ { fs with slices := slices3 } s s' := by
  have hth := henv.2.2.2.1
  set cp := mkWhpCoreParams c U V w n_max
  have hwp1 : (mkWhpParams c U V w n_max).1 = cp := by
    simp [cp, mkWhpParams, Nat.not_lt.mpr hth]
  have h32_sp := headerWords_le_largeSpaceWhp c U V w n_max
  obtain ⟨hst_ra, hres_ra, hmc_ra, hvp_ra⟩ := readRebActiveBGenProg_spec henv hrep (b := b) (s := s)
  obtain ⟨hst_rc, hres_rc, hmc_rc, hvp_rc⟩ := readHdrProg_large_spec c U V w n_max
    (base := base) (hdrOff := hdrRebScanCursor) (s := s) (by decide)
  rw [hrep.2.2.2.2.2.2.2.2.2.2.1] at hres_rc
  obtain ⟨hst_o, hres_o, hmc_o, hvp_o⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
    hrep.2.2.2.1 (s := s)
  set rebActiveB : Bool :=
    decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
      fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
      fs.rebCollision = 0)
  have hcond_iff :
      ((if rebActiveB then 1 else 0) = 1 ∧ loc_del < fs.rebScanCursor ∧
        (st_del = 1 ∨ st_del = 2 + fs.oldEp)) ↔
      (rebActiveB && decide (loc_del < fs.rebScanCursor ∧
        (st_del = 1 ∨ st_del = 2 + fs.oldEp))) = true := by
    cases rebActiveB <;> simp
  have hck : CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
      (delRemRebCheckProg ((((cp, base), b), loc_del), st_del)) s
      (if (if rebActiveB then 1 else 0) = 1 ∧ loc_del < fs.rebScanCursor ∧
        (st_del = 1 ∨ st_del = 2 + fs.oldEp) then 1 else 0) 10 := by
    unfold delRemRebCheckProg; simp only [pure_bind]
    exact .mono (.bind ⟨hst_ra, hres_ra, hmc_ra, hvp_ra⟩ <|
      .bind ⟨hst_rc, hres_rc, hmc_rc.le, hvp_rc⟩ <|
      .bind ⟨hst_o, hres_o, hmc_o.le, hvp_o⟩ (by split_ifs <;> exact .pure _ _)) (by omega)
  unfold delRemRebGenProg
  simp only [hwp1, pure_bind]
  by_cases hcond : (rebActiveB && decide (loc_del < fs.rebScanCursor ∧
      (st_del = 1 ∨ st_del = 2 + fs.oldEp))) = true
  · rw [ite_eq_left hcond]
    rw [ite_eq_left (hcond_iff.mpr hcond)] at hck
    obtain ⟨hins_r, rm, hv_r⟩ := hreb_fn ((Bool.and_eq_true _ _).mp hcond).1
    obtain ⟨hst_cs, hres_cs, hmc_cs, hvp_cs⟩ := readHdrProg_large_spec c U V w n_max
      (base := base) (hdrOff := hdrRebCandSalt) (s := s) (by decide)
    rw [hrep.2.2.2.2.2.2.2.2.2.1] at hres_cs
    obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
      mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfp_st, hfp_res, hfp_mc, hfp_vp⟩ :=
      fpOfSaltOptRtProg_spec (salt := fs.rebCandSalt) (kv := u.val) henv hseed (s := s)
    simp only [u.isLt, ↓reduceDIte] at hfp_res
    change _ = fpOfSalt c U n_max θ.2 fs.rebCandSalt u at hfp_res
    obtain ⟨hrs_st, hrs_res, hrs_mc, hrs_vp⟩ := readRebSliceIdxGenProg_spec henv hb hrep (s := s)
    have hfp_lt : fpOfSalt c U n_max θ.2 fs.rebCandSalt u < 2 ^ fpBitsWhp n_max := by
      simpa only [fpOfSalt, u.isLt, ↓reduceDIte] using fpOfSaltOpt_lt c U n_max _ u.val θ.2
    obtain ⟨hbd_mc, hbd_vp, hbd_step⟩ :=
      btreeDeleteGenProg_fastStep henv hrIdx hins_r hseed hrep hv_r hfp_lt (s := s)
    have hact : CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
        (delRemRebActiveProg (((mkWhpParams c U V w n_max, base), b), u.val))
        ((Memory.spec 0).clientState s (btreeDeleteGenProg
          (((cp, base), fs.rebSliceIdx b), fpOfSalt c U n_max θ.2 fs.rebCandSalt u))) ()
        (hashEvalCostWhp c + 279) := by
      unfold delRemRebActiveProg readCandFpGenProg
      simp only [hwp1]
      exact .mono (.bind (.bind ⟨hst_cs, hres_cs, hmc_cs.le, hvp_cs⟩ <|
        .bind ⟨hmh_st, hmh_res, hmh_mc.le, hmh_vp⟩ ⟨hfp_st, hfp_res, hfp_mc, hfp_vp⟩) <|
        .bind ⟨hrs_st, hrs_res, hrs_mc.le, hrs_vp⟩ ⟨rfl, rfl, hbd_mc, hbd_vp⟩) (by omega)
    exact CostBoundedStep.elim (.bind hck hact) (by omega) hbd_step
  · rw [ite_eq_right hcond]
    rw [ite_eq_right (fun h => hcond (hcond_iff.mp h))] at hck
    exact CostBoundedStep.elim (.bind hck (.pure _ _)) (by omega) (FastStateStep.refl hseed hrep)

/-- Read `(st_del, (rKey_u, fp_live_u))` for `fastDeleteRemoveGenProg` without mutating memory. -/
@[irreducible] def delRemReadInfoGenProg :
    (((WhpParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((((wp, base), b), loc_del), u_val) => do
    let st_del ← readFastLocGenProg (((wp.1, base), b), loc_del)
    let hrt ← mkHashRtGenProg (wp, base)
    let rKey_u ← fpReducedKeyOptRtProg (hrt, u_val)
    let salt_b ← readBktFieldGenProg (((wp.1, base), b), 1)
    let fp_live_u ← fpOfSaltOptRtProg ((hrt, salt_b), u_val)
    pure (st_del, (rKey_u, fp_live_u))

theorem realizes_delRemReadInfoGen :
    Realizes .exact delRemReadInfoGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((((wp, base), b), loc_del), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          loc_del < totalLocalCoordsWhp n_max)
      (fun _ _ => 0) := by
  unfold delRemReadInfoGenProg
  realize [realizes_readFastLocGen, realizes_mkHashRtGen, realizes_fpReducedKeyOptRt,
    realizes_readBktFieldGen, realizes_fpOfSaltOptRt]
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, b⟩, loc_del⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hb, hld_tl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hst_l, _, _, _⟩ := readFastLocGenProg_spec henv hb hld_tl hrep (s := s)
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hrk_st, _, _, _⟩ := fpReducedKeyOptRtProg_spec (kv := u_val) henv hseed (s := s)
    obtain ⟨hs1_st, hs1_res, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 1 < 10)
      hrep (s := s)
    simp only [getBktField] at hs1_res
    obtain ⟨hfp_st, _, _, _⟩ :=
      fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u_val) henv hseed (s := s)
    simp only [hcp_eq, hst_l, hmh_st, hmh_res, hrk_st, hs1_st, hs1_res, hfp_st,
      wp_large_M hth, wp_large_totalLoc hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hld_tl
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
  )

theorem delRemReadInfoGenProg_spec {c U V w n_max base b loc_del : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State} (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max)
    (hld_tl : loc_del < totalLocalCoordsWhp n_max) :
    let prog := delRemReadInfoGenProg ((((mkWhpParams c U V w n_max, base), b), loc_del), u.val)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (fs.locState b loc_del,
       (fpReducedKey c U n_max θ.2 u, fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)) ∧
    memoryCost prog s ≤ hashEvalCostWhp c + 5 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  obtain ⟨hst_l, hres_l, hmc_l, hvp_l⟩ := readFastLocGenProg_spec henv hb hld_tl hrep (s := s)
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hrk_st, hrk_res, hrk_mc, hrk_vp⟩ :=
    fpReducedKeyOptRtProg_spec (kv := u.val) henv hseed (s := s)
  obtain ⟨hs1_st, hs1_res, hs1_mc, hs1_vp⟩ := readBktFieldGenProg_spec henv hb (by decide : 1 < 10)
    hrep (s := s)
  simp only [getBktField] at hs1_res
  obtain ⟨hfp_st, hfp_res, hfp_mc, hfp_vp⟩ :=
    fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u.val) henv hseed (s := s)
  simp only [u.isLt, ↓reduceDIte] at hrk_res hfp_res
  change _ = fpOfSalt c U n_max θ.2 (fs.bktSalt b) u at hfp_res
  suffices h : CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
      (delRemReadInfoGenProg ((((mkWhpParams c U V w n_max, base), b), loc_del), u.val)) s
      (fs.locState b loc_del,
        (fpReducedKey c U n_max θ.2 u, fpOfSalt c U n_max θ.2 (fs.bktSalt b) u))
      (hashEvalCostWhp c + 5) from
    ⟨h.clientState_eq, h.clientResult_eq, h.memoryCost_le, h.validProg⟩
  unfold delRemReadInfoGenProg
  simp only [hwp1]
  exact .mono (.bind ⟨hst_l, hres_l, hmc_l.le, hvp_l⟩ <|
    .bind ⟨hmh_st, hmh_res, hmh_mc.le, hmh_vp⟩ <| .bind ⟨hrk_st, hrk_res, hrk_mc, hrk_vp⟩ <|
    .bind ⟨hs1_st, hs1_res, hs1_mc.le, hs1_vp⟩ <|
    .bind ⟨hfp_st, hfp_res, hfp_mc, hfp_vp⟩ (.pure _ _)) (by omega)

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
