/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg
import CslibFrontier.Tactic.Realize

/-!
# Shared Helpers for Global Epoch Ticks

This module provides shared header representations, `Memory.Prog` transition helpers, sequential
proof combinators, Stage-2 scan preservation facts, and the rollover success predicate
`epochTickWillSucceed` used across the split submodules of `SuccinctWhpEpochTickProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

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
open Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

attribute [local simp] clientResult_pure_whp clientState_pure_whp

/-- Projection of the header-word and bucket-count invariants from `FastMemRep`. -/
structure FastMemHdrs (base c U V w n_max : ℕ) (fs : FastState) (mem : ℕ → ℕ) : Prop where
  /-- Dirty bucket queue size does not exceed `qEpochWhp n_max`. -/
  dc_le : fs.dirtyCount ≤ qEpochWhp n_max
  /-- Header slot `hdrMode` equals `1` (fast mode). -/
  mode : mem (base + hdrMode) = 1
  /-- Header slot `hdrPoolFreeTop` matches `fs.poolFreeTop`. -/
  poolFreeTop : mem (base + hdrPoolFreeTop) = fs.poolFreeTop
  /-- Header slot `hdrCurEp` matches `fs.curEp`. -/
  curEp : mem (base + hdrCurEp) = fs.curEp
  /-- Header slot `hdrEpochClock` matches `fs.epochClock`. -/
  epochClock : mem (base + hdrEpochClock) = fs.epochClock
  /-- Header slot `hdrRebStage` matches `fs.rebStage`. -/
  rebStage : mem (base + hdrRebStage) = fs.rebStage
  /-- Header slot `hdrStageCursor` matches `fs.stageCursor`. -/
  stageCursor : mem (base + hdrStageCursor) = fs.stageCursor
  /-- Header slot `hdrDirtyCount` matches `fs.dirtyCount`. -/
  dirtyCount : mem (base + hdrDirtyCount) = fs.dirtyCount
  /-- Header slot `hdrDirtyIdx` matches `fs.dirtyIdx`. -/
  dirtyIdx : mem (base + hdrDirtyIdx) = fs.dirtyIdx
  /-- Header slot `hdrRebCandSalt` matches `fs.rebCandSalt`. -/
  rebCandSalt : mem (base + hdrRebCandSalt) = fs.rebCandSalt
  /-- Header slot `hdrRebScanCursor` matches `fs.rebScanCursor`. -/
  rebScanCursor : mem (base + hdrRebScanCursor) = fs.rebScanCursor
  /-- Header slot `hdrRebInsCount` matches `fs.rebInsCount`. -/
  rebInsCount : mem (base + hdrRebInsCount) = fs.rebInsCount
  /-- Header slot `hdrRebCollision` matches `fs.rebCollision`. -/
  rebCollision : mem (base + hdrRebCollision) = fs.rebCollision
  /-- Each bucket's packed `bktCount` header word matches `fs.bktCount b`. -/
  bktCount_read : ∀ b < numBucketsWhp n_max,
    readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem (16 * b) =
      fs.bktCount b

/-- Extract `FastMemHdrs` from a full `FastMemRep` witness. -/
theorem fastMemHdrs {base c U V w n_max : ℕ} {fs : FastState} {mem : ℕ → ℕ}
    (hrep : FastMemRep base c U V w n_max fs mem) :
    FastMemHdrs base c U V w n_max fs mem :=
  let ⟨hdc_le, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, _, _, hbmeta, _⟩ :=
    hrep
  ⟨hdc_le, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    fun b hb => (hbmeta b hb).1⟩

/-- Named bucket accessor for a `bufCheckSlotGenProg` result `(presentFlag, (bkt, loc))`. -/
abbrev slotCheckBucket (cs : ℕ × (ℕ × ℕ)) : ℕ := cs.2.1

/-- Read `(tr.nodeAlloc, tr.itemAlloc)` for buffer `ep ∈ {0, 1}` (`d = (base, ep)`). -/
@[irreducible] def readBufAllocsProg : ℕ × ℕ → Memory.Prog (ℕ × ℕ)
  | (base, ep) => do
    let z0 ← pure 0
    if ep = z0 then
      let na ← readHdrProg (base, hdrBuf0NodeAlloc)
      let ia ← readHdrProg (base, hdrBuf0ItemAlloc)
      pure (na, ia)
    else
      let na ← readHdrProg (base, hdrBuf1NodeAlloc)
      let ia ← readHdrProg (base, hdrBuf1ItemAlloc)
      pure (na, ia)

/-- `Realizes .exact` certificate for `readBufAllocsProg`. -/
theorem realizes_readBufAllocs :
    Realizes .exact readBufAllocsProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (base, _) _ => 0 < w ∧ Fits w (base + 32))
      (fun _ _ => 0) := by
  unfold readBufAllocsProg
  realize [realizes_readHdr]
  all_goals exact h.2.of_le (by
    dsimp [hdrBuf0NodeAlloc, hdrBuf0ItemAlloc, hdrBuf1NodeAlloc, hdrBuf1ItemAlloc]; omega)

private theorem readBufAllocsProg_pair_spec {w F base offNa offIa na ia : ℕ}
    {s : Memory.State} (hNa : base + offNa < F) (hIa : base + offIa < F)
    (hmNa : s.mem (base + offNa) = na) (hmIa : s.mem (base + offIa) = ia) :
    let prog := readHdrProg (base, offNa) >>= fun na' =>
      readHdrProg (base, offIa) >>= fun ia' => pure (na', ia')
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (na, ia) ∧
    memoryCost prog s ≤ 2 ∧
    ValidProg w F s prog := by
  obtain ⟨hn_st, hn_res, hn_mc, hn_vp⟩ :=
    readHdrProg_spec (w := w) (F := F) (base := base) (hdrOff := offNa) hNa (s := s)
  obtain ⟨hi_st, hi_res, hi_mc, hi_vp⟩ :=
    readHdrProg_spec (w := w) (F := F) (base := base) (hdrOff := offIa) hIa (s := s)
  refine ⟨by rw [clientState_bind, hn_st, clientState_bind, hi_st]; rfl, ?_,
    ?_, validProg_bind hn_vp (hn_st.symm ▸ validProg_bind hi_vp (hi_st.symm ▸ validProg_pure _))⟩
  · rw [clientResult_bind, hn_st, hn_res, hmNa, clientResult_bind, hi_st, hi_res, hmIa]
    rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]
    rw [hn_st, hn_mc, hi_mc]

/-- Cost and result specification for `readBufAllocsProg`. -/
theorem readBufAllocsProg_spec {c U V w n_max base ep : ℕ}
    {fs : FastState} {s : Memory.State}
    (_henv : WhpLargeEnv c U V w n_max w base)
    (hep : ep = 0 ∨ ep = 1)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readBufAllocsProg (base, ep)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = ((fs.buf ep).nodeAlloc, (fs.buf ep).itemAlloc) ∧
    memoryCost prog s ≤ 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  obtain ⟨_, _, hmNa, hmIa, _⟩ := hrep.buf_rep hep
  unfold readBufAllocsProg
  rcases hep with rfl | rfl <;> simp only [pure_bind, one_ne_zero, ↓reduceIte]
  · exact readBufAllocsProg_pair_spec (by dsimp [hdrBuf0NodeAlloc]; omega)
      (by dsimp [hdrBuf0ItemAlloc]; omega) hmNa hmIa
  · exact readBufAllocsProg_pair_spec (by dsimp [hdrBuf1NodeAlloc]; omega)
      (by dsimp [hdrBuf1ItemAlloc]; omega) hmNa hmIa

/-- `FastStateStep` wrapper around `bufClearStepsGenProg_spec`. -/
theorem bufClearStepsGenProg_fastStep {c U V w n_max base ep k : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hclr : ClearableBufTrie (fs.buf ep))
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := bufClearStepsGenProg (((mkWhpCoreParams c U V w n_max, base), ep), k)
    let s' := (Memory.spec 0).clientState s prog
    let tr' := bufClearSteps k (fs.buf ep)
    memoryCost prog s ≤ 15 * k ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ { fs with buf := Function.update fs.buf ep tr' } s s' := by
  obtain ⟨hfr, hmc, hvp, hrep_tr', hbfr⟩ :=
    bufClearStepsGenProg_spec henv hep (hrep.buf_rep hep) hclr (k := k) (s := s)
  exact ⟨hmc, hvp, fastStep_of_bufEpFrame henv.2.1 hep hfr hseed hrep hrep_tr' hbfr⟩

/-- Under `CoreFastInv`, every bucket's rebuild role index is `< 3`. -/
private theorem rebRole_lt_of_core {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hcore : CoreFastInv c U V n_max θ fs dict)
    {b : ℕ} (hb : b < numBucketsWhp n_max) :
    fs.rebRole b < 3 := by
  have ⟨h1, h2, h3⟩ := hcore.roles_valid b hb
  dsimp only [FastState.rebRole]; omega

/-- Under `CoreFastInv`, every bucket's rebuild slice index is `< 3 * numBucketsWhp n_max`. -/
theorem rebSliceIdx_lt_of_core {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hcore : CoreFastInv c U V n_max θ fs dict)
    {b : ℕ} (hb : b < numBucketsWhp n_max) :
    fs.rebSliceIdx b < 3 * numBucketsWhp n_max := by
  have hr := rebRole_lt_of_core hcore hb
  dsimp only [FastState.rebSliceIdx]; omega

/-- Compose two sequential `Memory.Prog Unit` `FastStateStep` transitions `p₁ >>= fun _ => p₂`. -/
theorem seqUnitProg_fastStep {c U V w n_max base c₁ c₂ : ℕ}
    {θ : SeedWhp c U n_max} {fs₁ fs₂ : FastState} {s : Memory.State}
    {p₁ p₂ : Memory.Prog Unit}
    (h₁ : memoryCost p₁ s ≤ c₁ ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s p₁ ∧
      FastStateStep base c U V w n_max θ fs₁ s ((Memory.spec 0).clientState s p₁))
    (h₂ : memoryCost p₂ ((Memory.spec 0).clientState s p₁) ≤ c₂ ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max)
        ((Memory.spec 0).clientState s p₁) p₂ ∧
      FastStateStep base c U V w n_max θ fs₂ ((Memory.spec 0).clientState s p₁)
        ((Memory.spec 0).clientState ((Memory.spec 0).clientState s p₁) p₂)) :
    memoryCost (p₁ >>= fun _ => p₂) s ≤ c₁ + c₂ ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s (p₁ >>= fun _ => p₂) ∧
    FastStateStep base c U V w n_max θ fs₂ s
      ((Memory.spec 0).clientState s (p₁ >>= fun _ => p₂)) := by
  refine ⟨?_, validProg_bind h₁.2.1 h₂.2.1, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]; omega
  · rw [clientState_bind]; exact h₁.2.2.trans h₂.2.2

/-- Write `mem[base + hdrOff] := val` as a single `FastStateStep` with cost `≤ 1`. -/
theorem writeHdrStep {c U V w n_max base hdrOff val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hhdr : 1 ≤ hdrOff ∧ hdrOff ≤ 11) (hfit_val : Fits w val)
    (hdc : hdrOff = 6 → val ≤ fs.dirtyCount)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := writeHdrProg ((base, hdrOff), val)
    memoryCost prog s ≤ 1 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (updateFastHdr fs hdrOff val) s
      ((Memory.spec 0).clientState s prog) := by
  obtain ⟨hmc, hvp, hst⟩ :=
    writeHdrProg_fastStep (fs := fs) henv hhdr hfit_val hdc hseed hrep
      (hdrOff := hdrOff) (val := val) (s := s)
  exact ⟨le_of_eq hmc, hvp, hst⟩

/-- Write `0` into any header slot `hdrOff ∈ [1, 11]` as a single `FastStateStep` (`cost ≤ 1`). -/
theorem writeHdrZeroStep {c U V w n_max base hdrOff : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hhdr : 1 ≤ hdrOff ∧ hdrOff ≤ 11)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := writeHdrProg ((base, hdrOff), 0)
    memoryCost prog s ≤ 1 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (updateFastHdr fs hdrOff 0) s
      ((Memory.spec 0).clientState s prog) :=
  writeHdrStep henv hhdr (Nat.two_pow_pos w) (fun _ => Nat.zero_le _) hseed hrep

/-- Append a `writeHdrProg ((base, hdrOff), val)` write onto an existing `Memory.Prog Unit` step. -/
theorem thenWriteHdr {c U V w n_max base hdrOff val c₁ : ℕ}
    {θ : SeedWhp c U n_max} {fs₁ : FastState} {s : Memory.State} {p₁ : Memory.Prog Unit}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hhdr : 1 ≤ hdrOff ∧ hdrOff ≤ 11) (hfit_val : Fits w val)
    (hdc : hdrOff = 6 → val ≤ fs₁.dirtyCount)
    (h₁ : memoryCost p₁ s ≤ c₁ ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s p₁ ∧
      FastStateStep base c U V w n_max θ fs₁ s ((Memory.spec 0).clientState s p₁)) :
    let prog := p₁ >>= fun _ => writeHdrProg ((base, hdrOff), val)
    memoryCost prog s ≤ c₁ + 1 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (updateFastHdr fs₁ hdrOff val) s
      ((Memory.spec 0).clientState s prog) :=
  seqUnitProg_fastStep h₁
    (writeHdrStep (fs := fs₁) henv hhdr hfit_val hdc h₁.2.2.2.1 h₁.2.2.2.2.1
      (s := (Memory.spec 0).clientState s p₁))

/-- Bundled specification for the shared 3-read prefix `(oldEp, allocs, sc)` of Stages 0, 1, 3. -/
structure StageCursorReads (w F base oldEp na ia sc : ℕ) (s : Memory.State) : Prop where
  /-- State preservation for `readOldEpProg base`. -/
  ro_st : (Memory.spec 0).clientState s (readOldEpProg base) = s
  /-- Result `fs.oldEp` from `readOldEpProg base`. -/
  ro_res : (Memory.spec 0).clientResult s (readOldEpProg base) = oldEp
  /-- Memory cost of `readOldEpProg base`. -/
  ro_mc : memoryCost (readOldEpProg base) s ≤ 1
  /-- Validity of `readOldEpProg base`. -/
  ro_vp : ValidProg w F s (readOldEpProg base)
  /-- State preservation for `readBufAllocsProg (base, oldEp)`. -/
  ra_st : (Memory.spec 0).clientState s (readBufAllocsProg (base, oldEp)) = s
  /-- Result `(na, ia)` from `readBufAllocsProg (base, oldEp)`. -/
  ra_res : (Memory.spec 0).clientResult s (readBufAllocsProg (base, oldEp)) = (na, ia)
  /-- Memory cost of `readBufAllocsProg (base, oldEp)`. -/
  ra_mc : memoryCost (readBufAllocsProg (base, oldEp)) s ≤ 2
  /-- Validity of `readBufAllocsProg (base, oldEp)`. -/
  ra_vp : ValidProg w F s (readBufAllocsProg (base, oldEp))
  /-- State preservation for `readHdrProg (base, hdrStageCursor)`. -/
  sc_st : (Memory.spec 0).clientState s (readHdrProg (base, hdrStageCursor)) = s
  /-- Result `fs.stageCursor` from `readHdrProg (base, hdrStageCursor)`. -/
  sc_res : (Memory.spec 0).clientResult s (readHdrProg (base, hdrStageCursor)) = sc
  /-- Memory cost of `readHdrProg (base, hdrStageCursor)`. -/
  sc_mc : memoryCost (readHdrProg (base, hdrStageCursor)) s ≤ 1
  /-- Validity of `readHdrProg (base, hdrStageCursor)`. -/
  sc_vp : ValidProg w F s (readHdrProg (base, hdrStageCursor))

/-- Read `(oldEp, (na, ia), stageCursor)` under `FastMemRep` and `fs.curEp ∈ {0, 1}`. -/
theorem stageCursorReads_spec {c U V w n_max base : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    StageCursorReads w (base + largeSpaceWhp c U V w n_max) base fs.oldEp
      (fs.buf fs.oldEp).nodeAlloc (fs.buf fs.oldEp).itemAlloc fs.stageCursor s := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hh := fastMemHdrs hrep
  obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
    hh.curEp (s := s)
  obtain ⟨hra_st, hra_res, hra_mc, hra_vp⟩ := readBufAllocsProg_spec henv hold_or hrep (s := s)
  obtain ⟨hsc_st, hsc_res, hsc_mc, hsc_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrStageCursor)
    (by dsimp [hdrStageCursor]; omega) (s := s)
  rw [hh.stageCursor] at hsc_res
  exact ⟨hro_st, hro_res, le_of_eq hro_mc, hro_vp, hra_st, hra_res, hra_mc, hra_vp,
    hsc_st, hsc_res, le_of_eq hsc_mc, hsc_vp⟩

private theorem stageCursorPrefix_ite_fastStep {c U V w n_max base tailCost : ℕ}
    {θ : SeedWhp c U n_max} {fs fsOut : FastState} {s : Memory.State}
    {kLt kGe : ℕ → ℕ × ℕ → ℕ → Memory.Prog Unit}
    {pBranch : Memory.Prog Unit}
    (hr : StageCursorReads w (base + largeSpaceWhp c U V w n_max) base fs.oldEp
      (fs.buf fs.oldEp).nodeAlloc (fs.buf fs.oldEp).itemAlloc fs.stageCursor s)
    (hIte : (if fs.stageCursor < (fs.buf fs.oldEp).itemAlloc then
        kLt fs.oldEp ((fs.buf fs.oldEp).nodeAlloc, (fs.buf fs.oldEp).itemAlloc) fs.stageCursor
      else
        kGe fs.oldEp ((fs.buf fs.oldEp).nodeAlloc, (fs.buf fs.oldEp).itemAlloc) fs.stageCursor) =
      pBranch)
    (hBr_mc : memoryCost pBranch s ≤ tailCost)
    (hBr_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s pBranch)
    (hBr_step : FastStateStep base c U V w n_max θ fsOut s
      ((Memory.spec 0).clientState s pBranch)) :
    let prog := readOldEpProg base >>= fun oldEp =>
      readBufAllocsProg (base, oldEp) >>= fun allocs =>
      readHdrProg (base, hdrStageCursor) >>= fun sc =>
      if sc < allocs.2 then kLt oldEp allocs sc else kGe oldEp allocs sc
    memoryCost prog s ≤ tailCost + 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fsOut s ((Memory.spec 0).clientState s prog) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hr.ro_st, hr.ro_res, hr.ra_st, hr.ra_res, hr.sc_st, hr.sc_res]; dsimp only
    rw [hIte]
    have hro_mc := hr.ro_mc; have hra_mc := hr.ra_mc; have hsc_mc := hr.sc_mc
    omega
  · refine validProg_bind hr.ro_vp ?_; rw [hr.ro_st, hr.ro_res]
    refine validProg_bind hr.ra_vp ?_; rw [hr.ra_st, hr.ra_res]
    refine validProg_bind hr.sc_vp ?_; rw [hr.sc_st, hr.sc_res]; dsimp only
    rw [hIte]; exact hBr_vp
  · rw [clientState_bind, hr.ro_st, hr.ro_res, clientState_bind, hr.ra_st, hr.ra_res,
      clientState_bind, hr.sc_st, hr.sc_res]; dsimp only
    rw [hIte]; exact hBr_step

/-- Lift a verified `< itemAlloc` branch across the shared 3-read prefix of Stages 0, 1, 3. -/
private theorem stageCursorPrefix_lt_fastStep {c U V w n_max base tailCost : ℕ}
    {θ : SeedWhp c U n_max} {fs fsOut : FastState} {s : Memory.State}
    {kLt kGe : ℕ → ℕ × ℕ → ℕ → Memory.Prog Unit}
    {pBranch : Memory.Prog Unit}
    (hr : StageCursorReads w (base + largeSpaceWhp c U V w n_max) base fs.oldEp
      (fs.buf fs.oldEp).nodeAlloc (fs.buf fs.oldEp).itemAlloc fs.stageCursor s)
    (hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc)
    (hBr_eq : kLt fs.oldEp ((fs.buf fs.oldEp).nodeAlloc, (fs.buf fs.oldEp).itemAlloc)
      fs.stageCursor = pBranch)
    (hBr_mc : memoryCost pBranch s ≤ tailCost)
    (hBr_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s pBranch)
    (hBr_step : FastStateStep base c U V w n_max θ fsOut s
      ((Memory.spec 0).clientState s pBranch)) :
    let prog := readOldEpProg base >>= fun oldEp =>
      readBufAllocsProg (base, oldEp) >>= fun allocs =>
      readHdrProg (base, hdrStageCursor) >>= fun sc =>
      if sc < allocs.2 then kLt oldEp allocs sc else kGe oldEp allocs sc
    memoryCost prog s ≤ tailCost + 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fsOut s ((Memory.spec 0).clientState s prog) :=
  stageCursorPrefix_ite_fastStep hr (by rw [ite_eq_left hlt, hBr_eq]) hBr_mc hBr_vp hBr_step

/-- Lift a verified `itemAlloc ≤ stageCursor` branch across the Stage 0/1/3 3-read prefix. -/
theorem stageCursorPrefix_ge_fastStep {c U V w n_max base tailCost maxCost : ℕ}
    {θ : SeedWhp c U n_max} {fs fsOut : FastState} {s : Memory.State}
    {kLt kGe : ℕ → ℕ × ℕ → ℕ → Memory.Prog Unit}
    {pBranch : Memory.Prog Unit}
    (hr : StageCursorReads w (base + largeSpaceWhp c U V w n_max) base fs.oldEp
      (fs.buf fs.oldEp).nodeAlloc (fs.buf fs.oldEp).itemAlloc fs.stageCursor s)
    (hnlt : ¬(fs.stageCursor < (fs.buf fs.oldEp).itemAlloc))
    (hBr_eq : kGe fs.oldEp ((fs.buf fs.oldEp).nodeAlloc, (fs.buf fs.oldEp).itemAlloc)
      fs.stageCursor = pBranch)
    (hBr_mc : memoryCost pBranch s ≤ tailCost)
    (hBr_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s pBranch)
    (hBr_step : FastStateStep base c U V w n_max θ fsOut s
      ((Memory.spec 0).clientState s pBranch))
    (hCost : tailCost + 4 ≤ maxCost) :
    let prog := readOldEpProg base >>= fun oldEp =>
      readBufAllocsProg (base, oldEp) >>= fun allocs =>
      readHdrProg (base, hdrStageCursor) >>= fun sc =>
      if sc < allocs.2 then kLt oldEp allocs sc else kGe oldEp allocs sc
    memoryCost prog s ≤ maxCost ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fsOut s ((Memory.spec 0).clientState s prog) :=
  have h := stageCursorPrefix_ite_fastStep hr (by rw [ite_eq_right hnlt, hBr_eq])
    hBr_mc hBr_vp hBr_step
  ⟨by have := h.1; omega, h.2.1, h.2.2⟩

/-- Lift a `bufCheckSlotGenProg` continuation across `stageCursorPrefix_lt_fastStep` and
`seqUnitProg_fastStep`. -/
theorem stageSlotCheckSeq_fastStep {c U V w n_max base midCost tailCost maxCost : ℕ}
    {θ : SeedWhp c U n_max} {fs fsMid fsOut : FastState} {s : Memory.State}
    {kLt kGe : ℕ → ℕ × ℕ → ℕ → Memory.Prog Unit}
    {kSlot : ℕ × (ℕ × ℕ) → Memory.Prog Unit}
    {pMid pTail : Memory.Prog Unit} {csRes : ℕ × (ℕ × ℕ)}
    (hr : StageCursorReads w (base + largeSpaceWhp c U V w n_max) base fs.oldEp
      (fs.buf fs.oldEp).nodeAlloc (fs.buf fs.oldEp).itemAlloc fs.stageCursor s)
    (hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc)
    (hkLt : kLt fs.oldEp ((fs.buf fs.oldEp).nodeAlloc, (fs.buf fs.oldEp).itemAlloc) fs.stageCursor =
      bufCheckSlotGenProg (((mkWhpCoreParams c U V w n_max, base), fs.oldEp), fs.stageCursor) >>=
        kSlot)
    (hcs_st : (Memory.spec 0).clientState s
      (bufCheckSlotGenProg (((mkWhpCoreParams c U V w n_max, base), fs.oldEp), fs.stageCursor)) = s)
    (hcs_res : (Memory.spec 0).clientResult s
      (bufCheckSlotGenProg (((mkWhpCoreParams c U V w n_max, base), fs.oldEp),
        fs.stageCursor)) = csRes)
    (hcs_mc : memoryCost (bufCheckSlotGenProg
      (((mkWhpCoreParams c U V w n_max, base), fs.oldEp), fs.stageCursor)) s ≤ 12)
    (hcs_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (bufCheckSlotGenProg (((mkWhpCoreParams c U V w n_max, base), fs.oldEp), fs.stageCursor)))
    (hSlot_eq : kSlot csRes = pMid >>= fun _ => pTail)
    (hMid_mc : memoryCost pMid s ≤ midCost)
    (hMid_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s pMid)
    (hMid_step : FastStateStep base c U V w n_max θ fsMid s ((Memory.spec 0).clientState s pMid))
    (hTail_mc : memoryCost pTail ((Memory.spec 0).clientState s pMid) ≤ tailCost)
    (hTail_vp : ValidProg w (base + largeSpaceWhp c U V w n_max)
      ((Memory.spec 0).clientState s pMid) pTail)
    (hTail_step : FastStateStep base c U V w n_max θ fsOut
      ((Memory.spec 0).clientState s pMid)
      ((Memory.spec 0).clientState ((Memory.spec 0).clientState s pMid) pTail))
    (hCost : midCost + tailCost + 16 ≤ maxCost) :
    let prog := readOldEpProg base >>= fun oldEp =>
      readBufAllocsProg (base, oldEp) >>= fun allocs =>
      readHdrProg (base, hdrStageCursor) >>= fun sc =>
      if sc < allocs.2 then kLt oldEp allocs sc else kGe oldEp allocs sc
    memoryCost prog s ≤ maxCost ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fsOut s ((Memory.spec 0).clientState s prog) := by
  obtain ⟨hmc_seq, hvp_seq, hst_seq⟩ := seqUnitProg_fastStep (c₁ := midCost) (c₂ := tailCost)
    ⟨hMid_mc, hMid_vp, hMid_step⟩ ⟨hTail_mc, hTail_vp, hTail_step⟩
  have hpref := stageCursorPrefix_lt_fastStep (kLt := kLt) (kGe := kGe) hr hlt hkLt
    (tailCost := midCost + tailCost + 12)
    (by simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hcs_st, hcs_res, hSlot_eq]; omega)
    (validProg_bind hcs_vp (by rwa [hcs_st, hcs_res, hSlot_eq]))
    (by rwa [clientState_bind, hcs_st, hcs_res, hSlot_eq])
  exact ⟨by have := hpref.1; omega, hpref.2.1, hpref.2.2⟩

/-- Transition to Stage 3 (`rebStage := 3, stageCursor := 0`). -/
@[irreducible] def tickToStage3Prog (base : ℕ) : Memory.Prog Unit := do
  let z0 ← pure 0
  let z3 ← pure 3
  writeHdrProg ((base, hdrRebStage), z3)
  writeHdrProg ((base, hdrStageCursor), z0)

/-- `Realizes .exact` certificate for `tickToStage3Prog`. -/
theorem realizes_tickToStage3 :
    Realizes .exact tickToStage3Prog
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w base _ => 2 ≤ w ∧ Fits w (base + 32))
      (fun _ _ => 0) := by
  unfold tickToStage3Prog
  realize [realizes_writeHdr]
  all_goals first
    | exact lt_of_lt_of_le (by decide : 3 < 2 ^ 2) (Nat.pow_le_pow_right two_pos h.1)
    | exact h.2.of_le (by dsimp [hdrRebStage, hdrStageCursor]; omega)

/-- `FastStateStep` specification for `tickToStage3Prog`. -/
theorem tickToStage3Prog_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := tickToStage3Prog base
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ { fs with rebStage := 3, stageCursor := 0 } s s' := by
  have h1 := writeHdrStep (fs := fs) henv (by dsimp [hdrRebStage]; decide)
    (henv.fits_const (by decide)) (fun h => by dsimp [hdrRebStage] at h; omega) hseed hrep
    (hdrOff := hdrRebStage) (val := 3)
  unfold tickToStage3Prog; simp only [pure_bind]
  exact thenWriteHdr (hdrOff := hdrStageCursor) henv
    (by simp [hdrStageCursor]) (Nat.two_pow_pos w) (fun _ => Nat.zero_le _) h1

/-- Set `(rebCandSalt, rebScanCursor, rebInsCount, rebCollision) := (cand, 0, 0, 0)`
(`d = (base, cand)`). -/
@[irreducible] def resetRebScanHdrsProg : ℕ × ℕ → Memory.Prog Unit
  | (base, cand) => do
    let z0 ← pure 0
    writeHdrProg ((base, hdrRebCandSalt), cand)
    writeHdrProg ((base, hdrRebScanCursor), z0)
    writeHdrProg ((base, hdrRebInsCount), z0)
    writeHdrProg ((base, hdrRebCollision), z0)

/-- `Realizes .exact` certificate for `resetRebScanHdrsProg`. -/
theorem realizes_resetRebScanHdrs :
    Realizes .exact resetRebScanHdrsProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (base, _) _ => 0 < w ∧ Fits w (base + 32))
      (fun _ _ => 0) := by
  unfold resetRebScanHdrsProg
  realize [realizes_writeHdr]
  all_goals
    obtain ⟨_, hfit32⟩ := h
    exact hfit32.of_le
      (by dsimp [hdrRebCandSalt, hdrRebScanCursor, hdrRebInsCount, hdrRebCollision]; omega)

/-- `FastStateStep` specification for `resetRebScanHdrsProg`. -/
theorem resetRebScanHdrsProg_fastStep {c U V w n_max base cand : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hcand : Fits w cand)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := resetRebScanHdrsProg (base, cand)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        rebCandSalt := cand
        rebScanCursor := 0
        rebInsCount := 0
        rebCollision := 0 } s s' := by
  have h1 := writeHdrStep (fs := fs) henv (by dsimp [hdrRebCandSalt]; decide) hcand
    (fun h => by dsimp [hdrRebCandSalt] at h; omega) hseed hrep
    (hdrOff := hdrRebCandSalt) (val := cand) (s := s)
  set fs1 : FastState := { fs with rebCandSalt := cand }
  have h2 := writeHdrZeroStep (fs := fs1) henv (by dsimp [hdrRebScanCursor]; decide)
    h1.2.2.2.1 h1.2.2.2.2.1 (hdrOff := hdrRebScanCursor)
  set fs2 : FastState := { fs1 with rebScanCursor := 0 }
  have h3 := writeHdrZeroStep (fs := fs2) henv (by dsimp [hdrRebInsCount]; decide)
    h2.2.2.2.1 h2.2.2.2.2.1 (hdrOff := hdrRebInsCount)
  set fs3 : FastState := { fs2 with rebInsCount := 0 }
  have h4 := writeHdrZeroStep (fs := fs3) henv (by dsimp [hdrRebCollision]; decide)
    h3.2.2.2.1 h3.2.2.2.2.1 (hdrOff := hdrRebCollision)
  unfold resetRebScanHdrsProg; simp only [pure_bind]
  exact seqUnitProg_fastStep h1 (seqUnitProg_fastStep h2 (seqUnitProg_fastStep h3 h4))

/-- Frame invariant preserved across `rebScanSteps c U n_max θ b k fs`. -/
structure RebScanPreserved (fs fs' : FastState) (k : ℕ) : Prop where
  /-- Current epoch index is unchanged. -/
  curEp : fs'.curEp = fs.curEp
  /-- Epoch clock is unchanged. -/
  epochClock : fs'.epochClock = fs.epochClock
  /-- Rebuild stage is unchanged. -/
  rebStage : fs'.rebStage = fs.rebStage
  /-- Stage cursor is unchanged. -/
  stageCursor : fs'.stageCursor = fs.stageCursor
  /-- Dirty bucket count is unchanged. -/
  dirtyCount : fs'.dirtyCount = fs.dirtyCount
  /-- Dirty bucket index is unchanged. -/
  dirtyIdx : fs'.dirtyIdx = fs.dirtyIdx
  /-- Dirty bucket array is unchanged. -/
  dirtyBuckets : fs'.dirtyBuckets = fs.dirtyBuckets
  /-- Candidate rebuild salt is unchanged. -/
  rebCandSalt : fs'.rebCandSalt = fs.rebCandSalt
  /-- Bucket item counts are unchanged. -/
  bktCount : fs'.bktCount = fs.bktCount
  /-- Live slice roles are unchanged. -/
  liveRole : fs'.liveRole = fs.liveRole
  /-- Overmars slice roles are unchanged. -/
  overmarsRole : fs'.overmarsRole = fs.overmarsRole
  /-- Rebuild insertion count increases by at most `k`. -/
  rebInsCount_le : fs'.rebInsCount ≤ fs.rebInsCount + k

/-- `rebScanSteps c U n_max θ b k fs` satisfies `RebScanPreserved fs _ k`. -/
theorem rebScanSteps_preserved {c U n_max : ℕ} (θ : SeedWhp c U n_max) (b : ℕ) :
    ∀ k (fs : FastState),
      RebScanPreserved fs (rebScanSteps c U n_max θ b k fs) k
  | 0, _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_rfl⟩
  | k + 1, fs => by
    dsimp only [rebScanSteps]
    by_cases hcnz : fs.rebCollision ≠ 0
    · rw [ite_eq_left hcnz]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_add_right _ _⟩
    · rw [ite_eq_right hcnz]
      refine (fun {fs1} (hp1 : RebScanPreserved fs fs1 1) =>
        let hpk := rebScanSteps_preserved θ b k fs1
        (⟨hpk.curEp.trans hp1.curEp, hpk.epochClock.trans hp1.epochClock,
          hpk.rebStage.trans hp1.rebStage, hpk.stageCursor.trans hp1.stageCursor,
          hpk.dirtyCount.trans hp1.dirtyCount, hpk.dirtyIdx.trans hp1.dirtyIdx,
          hpk.dirtyBuckets.trans hp1.dirtyBuckets, hpk.rebCandSalt.trans hp1.rebCandSalt,
          hpk.bktCount.trans hp1.bktCount, hpk.liveRole.trans hp1.liveRole,
          hpk.overmarsRole.trans hp1.overmarsRole,
          (hpk.rebInsCount_le.trans (Nat.add_le_add_right hp1.rebInsCount_le k)).trans_eq
            (by omega)⟩ :
          RebScanPreserved fs _ (k + 1))) ?_
      split_ifs with hact
      · cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices (fs.rebSliceIdx b))
            (fs.fpAt c U n_max θ fs.rebCandSalt b fs.rebScanCursor) <;>
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by dsimp only; omega⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_succ _⟩

/-- Exact read-only rollover pre-condition guaranteeing `(epochTick c U n_max θ fs).isSome`. -/
@[expose] def epochTickWillSucceed (n_max : ℕ) (fs : FastState) : Bool :=
  decide (fs.epochClock + 1 < qEpochWhp n_max ∨ fs.rebStage = 5 ∨
    (fs.rebStage = 4 ∧ (fs.buf fs.oldEp).nodeAlloc ≤ 8))

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

end
