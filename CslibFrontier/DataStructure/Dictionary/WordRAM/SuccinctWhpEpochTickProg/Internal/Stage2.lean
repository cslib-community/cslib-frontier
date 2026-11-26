/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpEpochTickProg.Internal.RebScan
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpEpochTickProg.Internal.Stage2Swap
import CslibFrontier.Tactic.Realize

/-!
# Stage 2 of `epochTick`

Implements and verifies `epochTickStage2GenProg`, running a 16-coordinate `rebScanLoopGenProg`
burst followed by `stage2PostScanGenProg` (collision salt increment or live/rebuild role swap),
or transitioning to Stage 3 once all dirty buckets are rebuilt.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

attribute [local simp] clientResult_pure_whp clientState_pure_whp

/-- Execute Stage 2 of `epochTick` (`d = (wp, base)`). -/
@[irreducible] def epochTickStage2GenProg :
    WhpParams × ℕ → Memory.Prog Unit
  | (wp, base) => do
    let c16 ← pure 16
    let di ← readHdrProg (base, hdrDirtyIdx)
    let dc ← readHdrProg (base, hdrDirtyCount)
    if di < dc then
      let b ← readDirtyBucketGenProg ((wp.1, base), di)
      let cand ← readHdrProg (base, hdrRebCandSalt)
      let smax ← pure (wpSMax wp.1)
      if cand < smax then
        rebScanLoopGenProg ((((wp, base), b), ()), c16)
        stage2PostScanGenProg ((wp.1, base), b)
      else
        pure ()
    else
      tickToStage3Prog base

private theorem stage2_rebScan16_facts {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hcore : CoreFastInv c U V n_max θ fs dict)
    (hpre : ValidEpochStagePreTick c U n_max θ fs)
    (hs2 : fs.rebStage = 2)
    (hdi_lt : fs.dirtyIdx < fs.dirtyCount)
    (hcs_lt : fs.rebCandSalt < sMaxWhp c n_max) :
    let b := fs.dirtyBuckets fs.dirtyIdx
    let fsScan := rebScanSteps c U n_max θ b 16 fs
    b < numBucketsWhp n_max ∧
    fs.rebSliceIdx b < 3 * numBucketsWhp n_max ∧
    fs.bktCount b ≤ totalLocalCoordsWhp n_max ∧
    (∀ p, fs.quotArr p < 2 ^ quotBitsWhp U n_max) ∧
    (∀ idx < fs.bktCount b - capFrontWhp n_max, fs.backPtr b idx < poolSizeWhp n_max) ∧
    (fs.rebCollision = 0 →
      fs.rebScanCursor + 16 ≤ n_max ∧
      fs.rebInsCount + 16 ≤ 8 * (slabScale n_max) ^ 12 ∧
      ∃ rm, ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm) ∧
    (fsScan.liveRole b < 3 ∧ fsScan.overmarsRole b < 3 ∧
      fsScan.liveRole b ≠ fsScan.overmarsRole b) ∧
    fsScan.rebSliceIdx b < 3 * numBucketsWhp n_max ∧
    fsScan.rebCandSalt < sMaxWhp c n_max ∧
    fsScan.rebInsCount ≤ n_max ∧
    fsScan.dirtyIdx < fsScan.dirtyCount ∧
    (fsScan.dirtyIdx + 1 < fsScan.dirtyCount →
      fsScan.dirtyBuckets (fsScan.dirtyIdx + 1) < numBucketsWhp n_max ∧
      ({ fsScan with liveRole := Function.update fsScan.liveRole b (fsScan.rebRole b) } :
        FastState).rebSliceIdx (fsScan.dirtyBuckets (fsScan.dirtyIdx + 1)) <
        3 * numBucketsWhp n_max) := by
  have hth := henv.2.2.2.1
  dsimp only [ValidEpochStagePreTick] at hpre
  rw [ite_eq_right (by omega : ¬(fs.rebStage = 0)),
    ite_eq_right (by omega : ¬(fs.rebStage = 1)), ite_eq_left hs2] at hpre
  obtain ⟨_, _, hd3, _, _, _, hreb_fn⟩ := hpre
  have hb : fs.dirtyBuckets fs.dirtyIdx < numBucketsWhp n_max := hd3 _ hdi_lt
  obtain ⟨hcur_r, _, rm0, hvr0, _⟩ := hreb_fn hcs_lt
  have hcnt_le : fs.bktCount (fs.dirtyBuckets fs.dirtyIdx) ≤ totalLocalCoordsWhp n_max :=
    hcore.bktCount_le _ hb
  have hcnt_3L : fs.bktCount (fs.dirtyBuckets fs.dirtyIdx) ≤ 3 * (slabScale n_max) ^ 12 :=
    hcnt_le.trans totalLocalCoordsWhp_le_three_mul
  have h2tl := (large_index_bounds hth).2.2.1
  have h4096 : 4096 ≤ (slabScale n_max) ^ 12 :=
    Nat.pow_le_pow_left (two_le_slabScale n_max) 12
  have ⟨hcur16, hins16⟩ :
      fs.rebScanCursor + 16 ≤ n_max ∧ fs.rebInsCount + 16 ≤ 8 * (slabScale n_max) ^ 12 := by
    rcases hcur_r with ⟨h0, hi0⟩ | ⟨_, hle, hins_le⟩ <;> constructor <;> omega
  have hrIdx : fs.rebSliceIdx (fs.dirtyBuckets fs.dirtyIdx) < 3 * numBucketsWhp n_max :=
    rebSliceIdx_lt_of_core hcore hb
  have hpres := rebScanSteps_preserved θ (fs.dirtyBuckets fs.dirtyIdx) 16 fs
  set b := fs.dirtyBuckets fs.dirtyIdx
  set fsScan := rebScanSteps c U n_max θ b 16 fs
  have hrIdxS : fsScan.rebSliceIdx b < 3 * numBucketsWhp n_max := by
    simpa only [FastState.rebSliceIdx, FastState.rebRole, hpres.liveRole, hpres.overmarsRole]
      using hrIdx
  have h8L_lt := (large_bounds_lt_n_max hth).2.2.2.1
  have hinsS_le : fsScan.rebInsCount ≤ n_max := by have := hpres.rebInsCount_le; omega
  have hrv := hcore.roles_valid b hb
  refine ⟨hb, hrIdx, hcnt_le, fun p => (hcore.qv_global p).1,
    fun idx hidx => (hcore.backPtr_valid b hb idx hidx).1, fun _ => ⟨hcur16, hins16, rm0, hvr0⟩,
    ⟨hpres.liveRole ▸ hrv.1, hpres.overmarsRole ▸ hrv.2.1,
      by rw [hpres.liveRole, hpres.overmarsRole]; exact hrv.2.2⟩,
    hrIdxS, hpres.rebCandSalt ▸ hcs_lt, hinsS_le,
    by simpa only [fsScan, b, hpres.dirtyIdx, hpres.dirtyCount] using hdi_lt, fun hlt_n => ?_⟩
  rw [hpres.dirtyIdx, hpres.dirtyCount] at hlt_n
  have hbN : fs.dirtyBuckets (fs.dirtyIdx + 1) < numBucketsWhp n_max := hd3 _ hlt_n
  rw [hpres.dirtyBuckets, hpres.dirtyIdx]
  refine ⟨hbN, ?_⟩
  dsimp only [FastState.rebSliceIdx, FastState.rebRole]
  rw [hpres.liveRole, hpres.overmarsRole]
  by_cases hbb : fs.dirtyBuckets (fs.dirtyIdx + 1) = b
  · rw [hbb, Function.update_self]
    obtain ⟨h1, h2, h3⟩ := hrv
    omega
  · rw [Function.update_of_ne hbb]
    exact rebSliceIdx_lt_of_core hcore hbN

/-- `Realizes .exact` certificate for `epochTickStage2GenProg`. -/
theorem realizes_epochTickStage2Gen :
    Realizes .exact epochTickStage2GenProg
      (WordEncoding.encode (α := WhpParams × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (wp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          CoreFastInv c U V n_max θ fs dict ∧
          ValidEpochStagePreTick c U n_max θ fs ∧
          fs.rebStage = 2)
      (fun _ _ => 0) := by
  unfold epochTickStage2GenProg
  have hrh := realizes_readHdr
  have hrd := realizes_readDirtyBucketGen
  have hsl := realizes_rebScanLoopGen
  have hps := realizes_stage2PostScanGen
  have ht3 := realizes_tickToStage3
  realize
  all_goals (
    rcases d with ⟨wp, base⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hcore, hpre, hs2⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hh := fastMemHdrs hrep
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hdr (off : ℕ) (hoff : off < 32) := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := off) (by omega) (s := s)
    obtain ⟨hdi_st, hdi_res, _, _⟩ := hdr hdrDirtyIdx (by decide)
    obtain ⟨hdc_st, hdc_res, _, _⟩ := hdr hdrDirtyCount (by decide)
    simp only [hcp_eq, hdi_st, hdi_res.trans hh.dirtyIdx, hdc_st, hdc_res.trans hh.dirtyCount,
      wp_large_sMax hth] at *
    first
    | exact h2w
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrDirtyIdx, hdrDirtyCount]; omega)
    | exact henv.fits_largeSpace.of_le (by omega)
    | (have hdi_lt : fs.dirtyIdx < fs.dirtyCount := by assumption
       obtain ⟨hrd_st, hrd_res, _, _⟩ := readDirtyBucketGenProg_spec henv hdi_lt hrep (s := s)
       obtain ⟨hcd_st, hcd_res, _, _⟩ := hdr hdrRebCandSalt (by decide)
       simp only [hrd_st, hrd_res, hcd_st, hcd_res.trans hh.rebCandSalt] at *
       first
       | exact henv.fits_hdr_addr (by dsimp [hdrRebCandSalt]; omega)
       | exact ⟨c, U, V, w, n_max, henv, rfl⟩
       | (rw [wp_large_qEpoch hth]; exact hdi_lt.trans_le hrep.1)
       | (have hcs_lt : fs.rebCandSalt < sMaxWhp c n_max := by assumption
          obtain ⟨hb, hrIdx, hcnt_le, hq_all, hbp_v, hcoll_k, hrvS, hrIdxS, hcandS_lt,
            hinsS_le, hdiS, hnxtS⟩ :=
            stage2_rebScan16_facts henv hcore hpre hs2 hdi_lt hcs_lt
          obtain ⟨hsafe16, _, _, hscan_step⟩ := rebScanLoop_spec henv hb θ 16 fs s
            hcore.curEp_or hrIdx hcnt_le hq_all hbp_v hcoll_k hseed hrep
          first
          | exact hsafe16
          | exact ⟨c, U, V, w, n_max, θ, _, henv, rfl, hscan_step.2.1, hscan_step.2.2.1,
              hb, hrvS.1, hrvS.2.1, hrvS.2.2, hrIdxS, hcandS_lt, hinsS_le, hdiS, hnxtS⟩))
  )

/-- `FastStateStep` specification for `epochTickStage2GenProg`. -/
theorem epochTickStage2GenProg_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hcore : CoreFastInv c U V n_max θ fs dict)
    (hpre : ValidEpochStagePreTick c U n_max θ fs)
    (hs2 : fs.rebStage = 2)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := epochTickStage2GenProg (mkWhpParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 32 * hashEvalCostWhp c + 43930 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (epochTickStage2 c U n_max θ fs) s s' := by
  have hth := henv.2.2.2.1
  have hh := fastMemHdrs hrep
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  have hsmax_cp : wpSMax cp = sMaxWhp c n_max := wp_large_sMax hth
  have hdr (off : ℕ) (hoff : off < 32) := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := off) (by omega) (s := s)
  obtain ⟨hdi_st, hdi_res, hdi_mc, hdi_vp⟩ := hdr hdrDirtyIdx (by decide)
  obtain ⟨hdc_st, hdc_res, hdc_mc, hdc_vp⟩ := hdr hdrDirtyCount (by decide)
  dsimp only
  let ok (acc : ℕ) (p : Memory.Prog Unit) (fs' : FastState) : Prop :=
    acc + memoryCost p s ≤ 32 * hashEvalCostWhp c + 43930 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s p ∧
    FastStateStep base c U V w n_max θ fs' s ((Memory.spec 0).clientState s p)
  have step_read {α : Type} {acc cm : ℕ} {m : Memory.Prog α} {k : α → Memory.Prog Unit}
      {v : α} {fs' : FastState}
      (hst : (Memory.spec 0).clientState s m = s) (hres : (Memory.spec 0).clientResult s m = v)
      (hmc : memoryCost m s = cm) (hvp : ValidProg w (base + largeSpaceWhp c U V w n_max) s m)
      (hk : ok (acc + cm) (k v) fs') : ok acc (m >>= k) fs' := by
    refine ⟨?_, validProg_bind hvp (by simpa only [hst, hres] using hk.2.1), ?_⟩
    · have := hk.1
      simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hst, hres, hmc]; omega
    · rw [clientState_bind, hst, hres]
      exact hk.2.2
  simp only [epochTickStage2GenProg, epochTickStage2, hwp1, pure_bind, hsmax_cp]
  rw [← Nat.zero_add (memoryCost _ s)]
  apply step_read hdi_st (hdi_res.trans hh.dirtyIdx) hdi_mc hdi_vp
  apply step_read hdc_st (hdc_res.trans hh.dirtyCount) hdc_mc hdc_vp
  by_cases hdi_lt : fs.dirtyIdx < fs.dirtyCount
  · simp only [ite_eq_left hdi_lt]
    set b := fs.dirtyBuckets fs.dirtyIdx
    obtain ⟨hrd_st, hrd_res, hrd_mc, hrd_vp⟩ :=
      readDirtyBucketGenProg_spec henv hdi_lt hrep (s := s)
    obtain ⟨hcd_st, hcd_res, hcd_mc, hcd_vp⟩ := hdr hdrRebCandSalt (by decide)
    apply step_read hrd_st hrd_res hrd_mc hrd_vp
    apply step_read hcd_st (hcd_res.trans hh.rebCandSalt) hcd_mc hcd_vp
    by_cases hcs_lt : fs.rebCandSalt < sMaxWhp c n_max
    · simp only [ite_eq_left hcs_lt]
      obtain ⟨hb, hrIdx, hcnt_le, hq_all, hbp_v, hcoll_k, hrvS, hrIdxS, hcandS_lt,
        hinsS_le, hdiS, hnxtS⟩ :=
        stage2_rebScan16_facts henv hcore hpre hs2 hdi_lt hcs_lt
      obtain ⟨_, hscan_mc, hscan_vp, hscan_step⟩ := rebScanLoop_spec henv hb θ 16 fs s
        hcore.curEp_or hrIdx hcnt_le hq_all hbp_v hcoll_k hseed hrep
      set sScan := (Memory.spec 0).clientState s
        (rebScanLoopGenProg ((((mkWhpParams c U V w n_max, base), b), ()), 16))
      set fsScan := rebScanSteps c U n_max θ b 16 fs
      obtain ⟨hps_mc, hps_vp, hps_step⟩ :=
        stage2PostScanGenProg_fastStep (fsScan := fsScan) henv hb hrvS
          hrIdxS hcandS_lt hinsS_le hdiS hnxtS
          hscan_step.2.1 hscan_step.2.2.1 (s := sScan)
      refine ⟨?_, validProg_bind hscan_vp hps_vp, ?_⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        dsimp only [sScan, cp, b] at hscan_mc hps_mc ⊢; omega
      · rw [clientState_bind]
        exact hscan_step.trans hps_step
    · simp only [ite_eq_right hcs_lt]
      refine ⟨by rw [memoryCost_pure]; omega, validProg_pure _, ?_⟩
      rw [clientState_pure_whp]
      exact FastStateStep.refl hseed hrep
  · simp only [ite_eq_right hdi_lt]
    obtain ⟨ht3_mc, ht3_vp, ht3_step⟩ := tickToStage3Prog_fastStep henv hseed hrep (s := s)
    exact ⟨by omega, ht3_vp, ht3_step⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

end
