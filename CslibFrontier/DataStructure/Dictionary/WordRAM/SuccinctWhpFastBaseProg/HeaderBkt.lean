/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.Frame
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.Internal
import CslibFrontier.Tactic.Realize

/-!
# Fast-Mode Header, Bucket-Metadata, Dirty-Queue, and Control-Predicate Subroutines

This module implements the parameter-free `Memory.Prog` subroutines and `Realizes .exact`
certificates for scalar header words, `bktMeta` bucket fields, the dirty-bucket queue, and
fast-mode control predicates on `FastMemRep`:

1. Header word accessors (`readHdrProg`, `writeHdrProg`, `updateFastHdr`, `readOldEpProg`).
2. Bucket scalar metadata accessors (`getBktField`, `setBktField`, `readBktFieldGenProg`,
   `writeBktFieldGenProg`, `readLiveSaltIdxGenProg`, `fpOfSaltOpt_lt`).
3. Dirty-bucket queue accessors (`readDirtyBucketGenProg`, `pushDirtyBucketGenProg`).
4. Control predicates (`inLiveTreeProg`, `readRebActiveBGenProg`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.readHdrProg`, `writeHdrProg`,
  `updateFastHdr`, `getBktField`, `setBktField`, `readBktFieldGenProg`, `writeBktFieldGenProg`,
  `readDirtyBucketGenProg`, `pushDirtyBucketGenProg`, `inLiveTreeProg`, `readRebActiveBGenProg`,
  `readOldEpProg`, `readLiveSaltIdxGenProg`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.writeHdrProg_fastStep`,
  `writeBktFieldGenProg_fastStep`, `pushDirtyBucketGenProg_fastStep`, `inLiveTreeProg_spec`,
  `readRebActiveBGenProg_spec`, `readLiveSaltIdxGenProg_spec`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

attribute [local simp] clientResult_pure_whp clientState_pure_whp

/-! ## Section 1: Header Word Accessors -/

/-- Read header word `mem[base + hdrOff]` (`hdrOff < 32`). -/
@[irreducible] def readHdrProg : ℕ × ℕ → Memory.Prog ℕ
  | (base, hdrOff) => do
    let addr ← pure (base + hdrOff)
    Memory.read addr

theorem realizes_readHdr :
    Realizes .exact readHdrProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (base, hdrOff) _ => Fits w (base + hdrOff))
      (fun _ _ => 0) := by
  unfold readHdrProg
  realize
  exact h

theorem readHdrProg_spec {w F base hdrOff : ℕ} {s : Memory.State}
    (ha : base + hdrOff < F) :
    let prog := readHdrProg (base, hdrOff)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = s.mem (base + hdrOff) ∧
    memoryCost prog s = 1 ∧
    ValidProg w F s prog := by
  unfold readHdrProg
  simp only [pure_bind]
  exact ⟨rfl, rfl, rfl, validProg_read ha⟩

/-- Specialization of `readHdrProg_spec` to the `largeSpaceWhp` frontier for any `hdrOff < 32`. -/
private theorem readHdrProg_large_spec {c U V w n_max base hdrOff : ℕ} {s : Memory.State}
    (hoff : hdrOff < 32) :
    let prog := readHdrProg (base, hdrOff)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = s.mem (base + hdrOff) ∧
    memoryCost prog s = 1 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  exact readHdrProg_spec (by omega)

/-- Write header word `mem[base + hdrOff] := val` (`hdrOff < 32`). -/
@[irreducible] def writeHdrProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((base, hdrOff), val) => do
    let addr ← pure (base + hdrOff)
    Memory.write addr val

theorem realizes_writeHdr :
    Realizes .exact writeHdrProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((base, hdrOff), _) _ => Fits w (base + hdrOff))
      (fun _ _ => 0) := by
  unfold writeHdrProg
  realize
  rcases d with ⟨⟨base, hdrOff⟩, _⟩
  exact h

/-- Update `FastState` on a single header slot `hdrOff ∈ {1 .. 11}`. -/
@[expose] def updateFastHdr (fs : FastState) (hdrOff val : ℕ) : FastState :=
  match hdrOff with
  | 1 => { fs with poolFreeTop := val }
  | 2 => { fs with curEp := val }
  | 3 => { fs with epochClock := val }
  | 4 => { fs with rebStage := val }
  | 5 => { fs with stageCursor := val }
  | 6 => { fs with dirtyCount := val }
  | 7 => { fs with dirtyIdx := val }
  | 8 => { fs with rebCandSalt := val }
  | 9 => { fs with rebScanCursor := val }
  | 10 => { fs with rebInsCount := val }
  | 11 => { fs with rebCollision := val }
  | _ => fs

theorem writeHdrProg_fastStep {c U V w n_max base hdrOff val : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hhdr : 1 ≤ hdrOff ∧ hdrOff ≤ 11)
    (hfit_val : Fits w val)
    (hdc : hdrOff = 6 → val ≤ fs.dirtyCount)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := writeHdrProg ((base, hdrOff), val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 1 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (updateFastHdr fs hdrOff val) s s' := by
  have hw := henv.2.1
  have hch := largeOffsetChain c U V w n_max
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  unfold writeHdrProg
  simp only [pure_bind]
  set m' := Function.update s.mem (base + hdrOff) val
  have hs'_eq : (Memory.spec 0).clientState s (Memory.write (base + hdrOff) val) =
      { mem := m', frontier := s.frontier } := rfl
  rw [hs'_eq]
  have hrp32 : ∀ {off N k idx}, idx < N → 32 ≤ off →
      readPacked (base + off) k w m' idx = readPacked (base + off) k w s.mem idx :=
    fun hidx hoff => readPacked_update_outside hw hidx (Or.inl (by omega))
  have hupd_at : ∀ k, m' (base + k) = if k = hdrOff then val else s.mem (base + k) := by
    intro k
    dsimp only [m']
    by_cases hk : k = hdrOff
    · subst hk; simp
    · rw [Function.update_of_ne (by omega)]; simp [hk]
  rcases hrep with ⟨hdc_le0, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    hqv0, hloc0, hbmeta0, hbptr0, hpool0, hsl0, hbuf0, hbuf1, hdirty0⟩
  have hrep_orig : FastMemRep base c U V w n_max fs s.mem :=
    ⟨hdc_le0, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
      hqv0, hloc0, hbmeta0, hbptr0, hpool0, hsl0, hbuf0, hbuf1, hdirty0⟩
  set fs' := updateFastHdr fs hdrOff val
  have hcases : hdrOff = 1 ∨ hdrOff = 2 ∨ hdrOff = 3 ∨ hdrOff = 4 ∨ hdrOff = 5 ∨
      hdrOff = 6 ∨ hdrOff = 7 ∨ hdrOff = 8 ∨ hdrOff = 9 ∨ hdrOff = 10 ∨ hdrOff = 11 := by omega
  have hscalars :
      fs'.slices = fs.slices ∧ fs'.buf = fs.buf ∧
      fs'.quotArr = fs.quotArr ∧ fs'.valArr = fs.valArr ∧ fs'.locState = fs.locState ∧
      fs'.bktCount = fs.bktCount ∧ fs'.bktSalt = fs.bktSalt ∧ fs'.liveRole = fs.liveRole ∧
      fs'.liveInsCount = fs.liveInsCount ∧ fs'.overmarsRole = fs.overmarsRole ∧
      fs'.overmarsActive = fs.overmarsActive ∧ fs'.overmarsCursor = fs.overmarsCursor ∧
      fs'.overmarsInsCount = fs.overmarsInsCount ∧ fs'.rebDoneFlag = fs.rebDoneFlag ∧
      fs'.rebQueued = fs.rebQueued ∧ fs'.backPtr = fs.backPtr ∧
      fs'.poolFreeStack = fs.poolFreeStack ∧ fs'.poolOwner = fs.poolOwner ∧
      fs'.dirtyBuckets = fs.dirtyBuckets ∧ fs'.dirtyCount ≤ fs.dirtyCount ∧
      m' (base + hdrMode) = 1 ∧
      m' (base + hdrPoolFreeTop) = fs'.poolFreeTop ∧
      m' (base + hdrCurEp) = fs'.curEp ∧
      m' (base + hdrEpochClock) = fs'.epochClock ∧
      m' (base + hdrRebStage) = fs'.rebStage ∧
      m' (base + hdrStageCursor) = fs'.stageCursor ∧
      m' (base + hdrDirtyCount) = fs'.dirtyCount ∧
      m' (base + hdrDirtyIdx) = fs'.dirtyIdx ∧
      m' (base + hdrRebCandSalt) = fs'.rebCandSalt ∧
      m' (base + hdrRebScanCursor) = fs'.rebScanCursor ∧
      m' (base + hdrRebInsCount) = fs'.rebInsCount ∧
      m' (base + hdrRebCollision) = fs'.rebCollision := by
    dsimp only [hdrMode, hdrPoolFreeTop, hdrCurEp, hdrEpochClock, hdrRebStage,
      hdrStageCursor, hdrDirtyCount, hdrDirtyIdx, hdrRebCandSalt, hdrRebScanCursor,
      hdrRebInsCount, hdrRebCollision]
    rw [hupd_at 0, hupd_at 1, hupd_at 2, hupd_at 3, hupd_at 4, hupd_at 5, hupd_at 6,
      hupd_at 7, hupd_at 8, hupd_at 9, hupd_at 10, hupd_at 11]
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, le_rfl, hm0, rfl, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, le_rfl, hm0, hm1, rfl, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, le_rfl, hm0, hm1, hm2, rfl, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, le_rfl, hm0, hm1, hm2, hm3, rfl, hm5, hm6, hm7, hm8, hm9, hm10, hm11⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, le_rfl, hm0, hm1, hm2, hm3, hm4, rfl, hm6, hm7, hm8, hm9, hm10, hm11⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, hdc rfl, hm0, hm1, hm2, hm3, hm4, hm5, rfl, hm7, hm8, hm9, hm10, hm11⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, le_rfl, hm0, hm1, hm2, hm3, hm4, hm5, hm6, rfl, hm8, hm9, hm10, hm11⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, le_rfl, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, rfl, hm9, hm10, hm11⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, le_rfl, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, rfl, hm10, hm11⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, le_rfl, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, rfl, hm11⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, le_rfl, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, rfl⟩
  rcases hscalars with ⟨hsl_e, hbf_e, hq_e, hv_e, hls_e, hbc_e, hbs_e, hlr_e, hli_e, hor_e,
    hoa_e, hoc_e, hoi_e, hrd_e, hrq_e, hbp_e, hps_e, hpo_e, hdb_e, hdc_sub, hhdrs⟩
  refine ⟨rfl, validProg_write (by omega) hfit_val,
    fastStep_nonSliceNonBuf hw rfl hseed hrep_orig hsl_e hbf_e
      (fun a ha =>
        show Function.update s.mem (base + hdrOff) val a = s.mem a from
          Function.update_of_ne (by rcases ha with h | h | h | h <;> omega) val s.mem)
      (fun idx hidx _ => hrp32 hidx (by omega))
      (fun id hid => hrp32 (show id < 6 * qEpochWhp n_max + 6 by omega) (by omega))
      (hdc_sub.trans hdc_le0) hhdrs
      (fun i hi => by
        rw [hq_e, hv_e]
        exact ⟨(hrp32 hi (by omega)).trans (hqv0 i hi).1,
          (hrp32 hi (by omega)).trans (hqv0 i hi).2⟩)
      (fun b hb loc hl => by
        rw [hls_e]
        exact (hrp32 (mul_add_lt_mul_bound hb hl) (by omega)).trans (hloc0 b hb loc hl))
      (fun b hb => by
        rw [hbc_e, hbs_e, hlr_e, hli_e, hor_e, hoa_e, hoc_e, hoi_e, hrd_e, hrq_e]
        exact bktMeta_congr_of_readPacked
          (fun k hk => hrp32 (show 16 * b + k < 16 * numBucketsWhp n_max by omega) (by omega))
          (hbmeta0 b hb))
      (fun b hb k hk => by
        rw [hbp_e]
        exact (hrp32 (mul_add_lt_mul_bound hb hk) (by omega)).trans (hbptr0 b hb k hk))
      (fun j hj => by
        rw [hps_e, hpo_e]
        exact ⟨(hrp32 hj (by omega)).trans (hpool0 j hj).1,
          (hrp32 hj (by omega)).trans (hpool0 j hj).2⟩)
      (fun j hj => by
        rw [hdb_e]
        exact (hrp32 (show 3 * qEpochWhp n_max + j < 6 * qEpochWhp n_max + 6 by omega)
          (by omega)).trans (hdirty0 j (hj.trans_le hdc_sub)))⟩

/-! ## Section 2: Bucket Scalar Metadata Accessors -/

/-- Pure projection of bucket `b`'s scalar metadata field `field ∈ {0 .. 9}`. -/
@[expose] def getBktField (fs : FastState) (b field : ℕ) : ℕ :=
  match field with
  | 0 => fs.bktCount b
  | 1 => fs.bktSalt b
  | 2 => fs.liveRole b
  | 3 => fs.liveInsCount b
  | 4 => fs.overmarsRole b
  | 5 => fs.overmarsActive b
  | 6 => fs.overmarsCursor b
  | 7 => fs.overmarsInsCount b
  | 8 => fs.rebDoneFlag b
  | 9 => fs.rebQueued b
  | _ => 0

/-- Pure update of bucket `b`'s scalar metadata field `field ∈ {0 .. 9}`. -/
@[expose] def setBktField (fs : FastState) (b field val : ℕ) : FastState :=
  match field with
  | 0 => { fs with bktCount := Function.update fs.bktCount b val }
  | 1 => { fs with bktSalt := Function.update fs.bktSalt b val }
  | 2 => { fs with liveRole := Function.update fs.liveRole b val }
  | 3 => { fs with liveInsCount := Function.update fs.liveInsCount b val }
  | 4 => { fs with overmarsRole := Function.update fs.overmarsRole b val }
  | 5 => { fs with overmarsActive := Function.update fs.overmarsActive b val }
  | 6 => { fs with overmarsCursor := Function.update fs.overmarsCursor b val }
  | 7 => { fs with overmarsInsCount := Function.update fs.overmarsInsCount b val }
  | 8 => { fs with rebDoneFlag := Function.update fs.rebDoneFlag b val }
  | 9 => { fs with rebQueued := Function.update fs.rebQueued b val }
  | _ => fs

private theorem bktField_realize_bounds {w base b field : ℕ} {cp : WhpCoreParams}
    (h : WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ field < 10) :
    Fits w 16 ∧ Fits w (16 * b + field) ∧
    ∃ N', w = wpW cp ∧ 0 < w ∧ wpGlobalPtrBits cp ≤ w ∧ 16 * b + field < N' ∧
      Fits w (base + wpOffBktMeta cp + packedWords N' (wpGlobalPtrBits cp) w) := by
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb, hfield⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  have h16M := sixteen_mul_numBuckets_le_n_max hth
  simp only [wp_large_M hth, wp_large_offBktMeta hth, wp_large_globalPtrBits hth,
    wp_large_w hth] at hb ⊢
  exact ⟨henv.fits_const (by decide), henv.fits_of_le_n_max (by omega),
    by obtain ⟨N', _, h2, h3, h4, h5⟩ := henv.bktMeta_safe (idx := 16 * b + field) (by omega)
       exact ⟨N', trivial, h2, h3, h4, h5⟩⟩

/-- Read bucket `b`'s scalar metadata field `field < 10` (`d = (((cp, base), b), field)`). -/
@[expose, irreducible] def readBktFieldGenProg : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, base), b), field) => do
    let idx ← pure (16 * b + field)
    readPackedGenProg (((base, wpOffBktMeta cp), (wpGlobalPtrBits cp, wpW cp)), idx)

theorem realizes_readBktFieldGen :
    Realizes .exact readBktFieldGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((cp, base), b), field) _ =>
        WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ field < 10)
      (fun _ _ => 0) := by
  unfold readBktFieldGenProg
  have hrp := realizes_readPackedGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, field⟩
    obtain ⟨h16, hidx, hsafe⟩ := bktField_realize_bounds h
    first | exact h16 | exact hidx | exact hsafe
  )

theorem readBktFieldGenProg_spec {c U V w n_max base b field : ℕ} {fs : FastState}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hfield : field < 10)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), field)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = getBktField fs b field ∧
    memoryCost prog s = 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hbm_le := seg_add_le (base := base) (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.1
  have hidx : 16 * b + field < 16 * numBucketsWhp n_max := by omega
  have hm := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b hb
  unfold readBktFieldGenProg
  simp only [wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth, pure_bind]
  refine ⟨rfl, ?_, rfl, validProg_readPacked hw hidx hbm_le⟩
  rw [clientResult_readPackedGen]
  have hcases : field = 0 ∨ field = 1 ∨ field = 2 ∨ field = 3 ∨ field = 4 ∨
      field = 5 ∨ field = 6 ∨ field = 7 ∨ field = 8 ∨ field = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hm.1
  · exact hm.2.1
  · exact hm.2.2.1
  · exact hm.2.2.2.1
  · exact hm.2.2.2.2.1
  · exact hm.2.2.2.2.2.1
  · exact hm.2.2.2.2.2.2.1
  · exact hm.2.2.2.2.2.2.2.1
  · exact hm.2.2.2.2.2.2.2.2.1
  · exact hm.2.2.2.2.2.2.2.2.2

/-- Write bucket `b`'s scalar metadata field `field < 10`
(`d = ((((cp, base), b), field), val)`). -/
@[expose, irreducible] def writeBktFieldGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), field), val) => do
    let idx ← pure (16 * b + field)
    writePackedGenProg ((((base, wpOffBktMeta cp), (wpGlobalPtrBits cp, wpW cp)), idx), val)

theorem realizes_writeBktFieldGen :
    Realizes .exact writeBktFieldGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), field), _) _ =>
        WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ field < 10)
      (fun _ _ => 0) := by
  unfold writeBktFieldGenProg
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, field⟩, val⟩
    obtain ⟨h16, hidx, hsafe⟩ := bktField_realize_bounds h
    first | exact h16 | exact hidx | exact hsafe
  )

theorem writeBktFieldGenProg_fastStep {c U V w n_max base b field val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hfield : field < 10)
    (hval_le : val ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := writeBktFieldGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), field), val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (setBktField fs b field val) s s' := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hch := largeOffsetChain c U V w n_max
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hval_g : val < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max hval_le
  have hbm_le := seg_add_le (base := base) (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.1
  set idxW := 16 * b + field
  have hidxW : idxW < 16 * numBucketsWhp n_max := by omega
  unfold writeBktFieldGenProg
  simp only [wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth, pure_bind]
  set m' := writePacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idxW val
  have hs'_eq : (Memory.spec 0).clientState s
      (writePackedGenProg
        ((((base, offBktMeta c U V w n_max), (globalPtrBits n_max, w)), idxW), val)) =
      { mem := m', frontier := s.frontier } := rfl
  rw [hs'_eq]
  have hout_bm : ∀ a, (a < base + offBktMeta c U V w n_max ∨
      base + offFbStart c U V w n_max ≤ a) → m' a = s.mem a :=
    fun a ha => writePacked_outside hw _ hidxW _ (by omega)
  have hrp_at : ∀ b' < numBucketsWhp n_max, ∀ k < 10,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w m' (16 * b' + k) =
        if b' = b ∧ k = field then val
        else readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem
          (16 * b' + k) := by
    intro b' _ k hk
    by_cases hbk : b' = b ∧ k = field
    · rcases hbk with ⟨rfl, rfl⟩
      simp only [and_self, ↓reduceIte]
      exact readPacked_writePacked_self _ _ _ s.mem idxW hval_g
    · simp only [hbk, ↓reduceIte]
      have hne : 16 * b' + k ≠ idxW := by
        dsimp only [idxW]
        intro heq
        have h1 : b' * 16 + k = b * 16 + field := by omega
        exact hbk (mul_add_inj_right (by omega : k < 16) (by omega : field < 16) h1)
      exact readPacked_writePacked_of_ne hw s.mem hne val
  rcases hrep with ⟨hdc_le0, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    hqv0, hloc0, hbmeta0, hbptr0, hpool0, hsl0, hbuf0, hbuf1, hdirty0⟩
  have hrep_orig : FastMemRep base c U V w n_max fs s.mem :=
    ⟨hdc_le0, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
      hqv0, hloc0, hbmeta0, hbptr0, hpool0, hsl0, hbuf0, hbuf1, hdirty0⟩
  set fs' := setBktField fs b field val
  have hcases : field = 0 ∨ field = 1 ∨ field = 2 ∨ field = 3 ∨ field = 4 ∨
      field = 5 ∨ field = 6 ∨ field = 7 ∨ field = 8 ∨ field = 9 := by omega
  have hhdr_eq : ∀ h < 16, m' (base + h) = s.mem (base + h) :=
    fun h _ => hout_bm (base + h) (Or.inl (by omega))
  have hunch :
      fs'.slices = fs.slices ∧ fs'.buf = fs.buf ∧ fs'.dirtyCount = fs.dirtyCount ∧
      fs'.poolFreeTop = fs.poolFreeTop ∧ fs'.curEp = fs.curEp ∧ fs'.epochClock = fs.epochClock ∧
      fs'.rebStage = fs.rebStage ∧ fs'.stageCursor = fs.stageCursor ∧
      fs'.dirtyIdx = fs.dirtyIdx ∧ fs'.rebCandSalt = fs.rebCandSalt ∧
      fs'.rebScanCursor = fs.rebScanCursor ∧ fs'.rebInsCount = fs.rebInsCount ∧
      fs'.rebCollision = fs.rebCollision ∧ fs'.quotArr = fs.quotArr ∧ fs'.valArr = fs.valArr ∧
      fs'.locState = fs.locState ∧ fs'.backPtr = fs.backPtr ∧
      fs'.poolFreeStack = fs.poolFreeStack ∧ fs'.poolOwner = fs.poolOwner ∧
      fs'.dirtyBuckets = fs.dirtyBuckets := by
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [fs', setBktField]
  rcases hunch with ⟨hsl_e, hbf_e, hdc_e, hpft_e, hce_e, hec_e, hrs_e, hsc_e, hdi_e, hrcs_e,
    hrsc_e, hric_e, hrcl_e, hq_e, hv_e, hls_e, hbp_e, hps_e, hpo_e, hdb_e⟩
  refine ⟨rfl, validProg_writePacked hw hgk hidxW hbm_le,
    fastStep_nonSliceNonBuf hw rfl hseed hrep_orig hsl_e hbf_e
      (fun a ha => hout_bm a (by rcases ha with h1 | ⟨_, h2⟩ | ⟨h3, _⟩ | h4 <;> omega))
      (fun idx _ h10 => readPacked_writePacked_of_ne hw s.mem (by dsimp [idxW]; omega) val)
      (fun id hid => readPacked_congr hw (hidx := show id < 6 * qEpochWhp n_max + 6 by omega)
        fun a ⟨ha1, _⟩ => hout_bm a (Or.inr (by omega)))
      (hdc_e ▸ hdc_le0)
      ⟨(hhdr_eq hdrMode (by decide)).trans hm0,
       (hhdr_eq hdrPoolFreeTop (by decide)).trans (hpft_e ▸ hm1),
       (hhdr_eq hdrCurEp (by decide)).trans (hce_e ▸ hm2),
       (hhdr_eq hdrEpochClock (by decide)).trans (hec_e ▸ hm3),
       (hhdr_eq hdrRebStage (by decide)).trans (hrs_e ▸ hm4),
       (hhdr_eq hdrStageCursor (by decide)).trans (hsc_e ▸ hm5),
       (hhdr_eq hdrDirtyCount (by decide)).trans (hdc_e ▸ hm6),
       (hhdr_eq hdrDirtyIdx (by decide)).trans (hdi_e ▸ hm7),
       (hhdr_eq hdrRebCandSalt (by decide)).trans (hrcs_e ▸ hm8),
       (hhdr_eq hdrRebScanCursor (by decide)).trans (hrsc_e ▸ hm9),
       (hhdr_eq hdrRebInsCount (by decide)).trans (hric_e ▸ hm10),
       (hhdr_eq hdrRebCollision (by decide)).trans (hrcl_e ▸ hm11)⟩
      (fun i hi => by
        rw [hq_e, hv_e]
        exact ⟨(readPacked_congr hw (hidx := hi) fun a ⟨_, ha2⟩ =>
            hout_bm a (Or.inl (by omega))).trans (hqv0 i hi).1,
          (readPacked_congr hw (hidx := hi) fun a ⟨_, ha2⟩ =>
            hout_bm a (Or.inl (by omega))).trans (hqv0 i hi).2⟩)
      (fun b' hb' loc hl => by
        rw [hls_e]
        exact (readPacked_congr hw (hidx := mul_add_lt_mul_bound hb' hl) fun a ⟨_, ha2⟩ =>
          hout_bm a (Or.inl (by omega))).trans (hloc0 b' hb' loc hl))
      (fun b' hb' => ?_)
      (fun b' hb' k hk => by
        rw [hbp_e]
        exact (readPacked_congr hw (hidx := mul_add_lt_mul_bound hb' hk) fun a ⟨ha1, _⟩ =>
          hout_bm a (Or.inr (by omega))).trans (hbptr0 b' hb' k hk))
      (fun j hj => by
        rw [hps_e, hpo_e]
        exact ⟨(readPacked_congr hw (hidx := hj) fun a ⟨ha1, _⟩ =>
            hout_bm a (Or.inr (by omega))).trans (hpool0 j hj).1,
          (readPacked_congr hw (hidx := hj) fun a ⟨ha1, _⟩ =>
            hout_bm a (Or.inr (by omega))).trans (hpool0 j hj).2⟩)
      (fun j hj => by
        rw [hdc_e] at hj; rw [hdb_e]
        exact (readPacked_congr hw (hidx :=
          show 3 * qEpochWhp n_max + j < 6 * qEpochWhp n_max + 6 by omega)
          fun a ⟨ha1, _⟩ => hout_bm a (Or.inr (by omega))).trans (hdirty0 j hj))⟩
  dsimp only
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := hbmeta0 b' hb'
  rw [hrp_at b' hb' 0 (by decide), hrp_at b' hb' 1 (by decide), hrp_at b' hb' 2 (by decide),
    hrp_at b' hb' 3 (by decide), hrp_at b' hb' 4 (by decide), hrp_at b' hb' 5 (by decide),
    hrp_at b' hb' 6 (by decide), hrp_at b' hb' 7 (by decide), hrp_at b' hb' 8 (by decide),
    hrp_at b' hb' 9 (by decide), r0, r1, r2, r3, r4, r5, r6, r7, r8, r9]
  by_cases hbb : b' = b <;>
    (rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [fs', setBktField, hbb])

/-! ## Section 3: Dirty-Bucket Queue Subroutines -/

private theorem dirtyBuckets_seg_le (c U V w n_max base : ℕ) :
    base + offTrieItems0 c U V w n_max +
      packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max :=
  seg_add_le (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Read `fs.dirtyBuckets j` (`j < fs.dirtyCount ≤ qEpochWhp n_max`, `d = ((cp, base), j)`). -/
@[irreducible] def readDirtyBucketGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), j) => do
    let idx ← pure (3 * wpQEpoch cp + j)
    readPackedGenProg (((base, wpOffTrieItems0 cp), (wpGlobalPtrBits cp, wpW cp)), idx)

theorem realizes_readDirtyBucketGen :
    Realizes .exact readDirtyBucketGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), j) _ => WhpLargeEnvGen w cp base ∧ j < wpQEpoch cp)
      (fun _ _ => 0) := by
  unfold readDirtyBucketGenProg
  have hrp := realizes_readPackedGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, j⟩
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hj⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h6q := (large_index_bounds hth).2.2.2.2.2
    have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
    simp only [wp_large_qEpoch hth, wp_large_offTrieItems0 hth, wp_large_globalPtrBits hth,
      wp_large_w hth] at hj ⊢
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.packed_safe_true hgk (show 3 * qEpochWhp n_max + j < 6 * qEpochWhp n_max + 6 by
        omega) (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  )

theorem readDirtyBucketGenProg_spec {c U V w n_max base j : ℕ} {fs : FastState}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hj : j < fs.dirtyCount)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readDirtyBucketGenProg ((mkWhpCoreParams c U V w n_max, base), j)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.dirtyBuckets j ∧
    memoryCost prog s = 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hdc_le := hrep.1
  have hidx : 3 * qEpochWhp n_max + j < 6 * qEpochWhp n_max + 6 := by omega
  unfold readDirtyBucketGenProg
  simp only [wp_large_qEpoch hth, wp_large_offTrieItems0 hth, wp_large_globalPtrBits hth,
    wp_large_w hth, pure_bind]
  exact ⟨rfl, (clientResult_readPackedGen _ _ _ _ _ _).trans
    (hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj), rfl,
    validProg_readPacked hw hidx (dirtyBuckets_seg_le c U V w n_max base)⟩

/-- Append bucket `b` at `dirtyBuckets[dirtyCount]` and increment `dirtyCount`
(`d = ((cp, base), b)`). -/
@[irreducible] def pushDirtyBucketGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let dc ← readHdrProg (base, hdrDirtyCount)
    let idx ← pure (3 * wpQEpoch cp + dc)
    writePackedGenProg ((((base, wpOffTrieItems0 cp), (wpGlobalPtrBits cp, wpW cp)), idx), b)
    let dc1 ← pure (dc + 1)
    writeHdrProg ((base, hdrDirtyCount), dc1)

theorem realizes_pushDirtyBucketGen :
    Realizes .exact pushDirtyBucketGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), _) s =>
        WhpLargeEnvGen w cp base ∧ s.mem (base + hdrDirtyCount) < wpQEpoch cp)
      (fun _ _ => 0) := by
  unfold pushDirtyBucketGenProg
  have hrh := realizes_readHdr
  have hwp := realizes_writePackedGen
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hdc_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h6q := (large_index_bounds hth).2.2.2.2.2
    have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
    obtain ⟨hrh_st, hrh_res, _, _⟩ := readHdrProg_large_spec (c := c) (U := U) (V := V) (w := w)
      (n_max := n_max) (base := base) (hdrOff := hdrDirtyCount) (s := s) (by decide)
    simp only [hrh_st, hrh_res] at *
    simp only [wp_large_qEpoch hth, wp_large_offTrieItems0 hth, wp_large_globalPtrBits hth,
      wp_large_w hth] at hdc_lt ⊢
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.packed_safe_true hgk
        (show 3 * qEpochWhp n_max + s.mem (base + hdrDirtyCount) < 6 * qEpochWhp n_max + 6 by
          omega)
        (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  )

theorem pushDirtyBucketGenProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hdc_lt : fs.dirtyCount < qEpochWhp n_max)
    (hb : b < numBucketsWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := pushDirtyBucketGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 6 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        dirtyBuckets := Function.update fs.dirtyBuckets fs.dirtyCount b
        dirtyCount := fs.dirtyCount + 1 } s s' := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hch := largeOffsetChain c U V w n_max
  have h6q := (large_index_bounds hth).2.2.2.2.2
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hb_g : b < 2 ^ globalPtrBits n_max :=
    lt_two_pow_globalPtrBits_of_le_n_max (hb.le.trans henv.numBuckets_le_n_max)
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  rcases hrep with ⟨hdc_le0, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    hqv0, hloc0, hbmeta0, hbptr0, hpool0, hsl0, hbuf0, hbuf1, hdirty0⟩
  have hrep_orig : FastMemRep base c U V w n_max fs s.mem :=
    ⟨hdc_le0, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
      hqv0, hloc0, hbmeta0, hbptr0, hpool0, hsl0, hbuf0, hbuf1, hdirty0⟩
  obtain ⟨hrh_st, hrh_res, hrh_mc, hrh_vp⟩ := readHdrProg_large_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) (hdrOff := hdrDirtyCount) (s := s) (by decide)
  set idxW := 3 * qEpochWhp n_max + fs.dirtyCount
  have hidxW : idxW < 6 * qEpochWhp n_max + 6 := by omega
  set m1 := writePacked (base + offTrieItems0 c U V w n_max) (globalPtrBits n_max) w s.mem idxW b
  set m2 := Function.update m1 (base + hdrDirtyCount) (fs.dirtyCount + 1)
  have hwh_vp : ValidProg w (base + largeSpaceWhp c U V w n_max)
      { mem := m1, frontier := s.frontier }
      (writeHdrProg ((base, hdrDirtyCount), fs.dirtyCount + 1)) := by
    unfold writeHdrProg; simp only [pure_bind]
    exact validProg_write (by dsimp [hdrDirtyCount]; omega) (henv.fits_of_le_n_max (by omega))
  unfold pushDirtyBucketGenProg
  simp only [wp_large_qEpoch hth, wp_large_offTrieItems0 hth, wp_large_globalPtrBits hth,
    wp_large_w hth, pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (readHdrProg (base, hdrDirtyCount) >>= fun dc =>
        writePackedGenProg
          ((((base, offTrieItems0 c U V w n_max), (globalPtrBits n_max, w)),
            3 * qEpochWhp n_max + dc), b) >>= fun _ =>
        writeHdrProg ((base, hdrDirtyCount), dc + 1)) =
      { mem := m2, frontier := s.frontier } := by
    rw [clientState_bind, hrh_st, hrh_res, hm6, clientState_bind,
      clientState_writePackedGen]
    unfold writeHdrProg
    simp only [pure_bind]
    rfl
  have hmc_eq : memoryCost
      (readHdrProg (base, hdrDirtyCount) >>= fun dc =>
        writePackedGenProg
          ((((base, offTrieItems0 c U V w n_max), (globalPtrBits n_max, w)),
            3 * qEpochWhp n_max + dc), b) >>= fun _ =>
        writeHdrProg ((base, hdrDirtyCount), dc + 1)) s = 6 := by
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hrh_st, hrh_res, hrh_mc, hm6, clientState_writePackedGen, memoryCost_writePackedGen]
    unfold writeHdrProg
    simp only [pure_bind, memoryCost_memRead_and_write.2]
  have hvp_all : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (readHdrProg (base, hdrDirtyCount) >>= fun dc =>
        writePackedGenProg
          ((((base, offTrieItems0 c U V w n_max), (globalPtrBits n_max, w)),
            3 * qEpochWhp n_max + dc), b) >>= fun _ =>
        writeHdrProg ((base, hdrDirtyCount), dc + 1)) := by
    refine validProg_bind hrh_vp ?_
    rw [hrh_st, hrh_res, hm6]
    exact validProg_bind (validProg_writePacked hw hgk hidxW
      (dirtyBuckets_seg_le c U V w n_max base)) hwh_vp
  rw [hs'_eq]
  have hout_m2 : ∀ a, a ≠ base + hdrDirtyCount →
      (a < base + offTrieItems0 c U V w n_max ∨ base + offTrieItems1 c U V w n_max ≤ a) →
      m2 a = s.mem a := fun a hne ha =>
    (Function.update_of_ne hne _ _).trans (writePacked_outside hw _ hidxW _ (by omega))
  have hrp_pre : ∀ {off N k idx}, idx < N → 32 ≤ off →
      off + packedWords N k w ≤ offTrieItems0 c U V w n_max →
      readPacked (base + off) k w m2 idx = readPacked (base + off) k w s.mem idx :=
    fun hidx h32 hhi => readPacked_congr hw (hidx := hidx) fun a ⟨ha1, ha2⟩ =>
      hout_m2 a (by dsimp [hdrDirtyCount]; omega) (Or.inl (by omega))
  have hne_dc : ∀ k < 12, k ≠ 6 → base + k ≠ base + hdrDirtyCount := by
    dsimp only [hdrDirtyCount]; omega
  refine ⟨hmc_eq, hvp_all,
    fastStep_nonSliceNonBuf hw rfl hseed hrep_orig rfl rfl
      (fun a ha => hout_m2 a (by dsimp [hdrDirtyCount]; rcases ha with h | h | h | h <;> omega)
        (by rcases ha with h | h | h | h <;> omega))
      (fun idx hidx _ => hrp_pre hidx (by omega) (by omega))
      (fun id hid => ?_)
      (by dsimp only; omega)
      ⟨(hout_m2 _ (hne_dc hdrMode (by decide) (by decide))
          (Or.inl (by dsimp [hdrMode]; omega))).trans hm0,
       (hout_m2 _ (hne_dc hdrPoolFreeTop (by decide) (by decide))
          (Or.inl (by dsimp [hdrPoolFreeTop]; omega))).trans hm1,
       (hout_m2 _ (hne_dc hdrCurEp (by decide) (by decide))
          (Or.inl (by dsimp [hdrCurEp]; omega))).trans hm2,
       (hout_m2 _ (hne_dc hdrEpochClock (by decide) (by decide))
          (Or.inl (by dsimp [hdrEpochClock]; omega))).trans hm3,
       (hout_m2 _ (hne_dc hdrRebStage (by decide) (by decide))
          (Or.inl (by dsimp [hdrRebStage]; omega))).trans hm4,
       (hout_m2 _ (hne_dc hdrStageCursor (by decide) (by decide))
          (Or.inl (by dsimp [hdrStageCursor]; omega))).trans hm5,
       Function.update_self _ _ _,
       (hout_m2 _ (hne_dc hdrDirtyIdx (by decide) (by decide))
          (Or.inl (by dsimp [hdrDirtyIdx]; omega))).trans hm7,
       (hout_m2 _ (hne_dc hdrRebCandSalt (by decide) (by decide))
          (Or.inl (by dsimp [hdrRebCandSalt]; omega))).trans hm8,
       (hout_m2 _ (hne_dc hdrRebScanCursor (by decide) (by decide))
          (Or.inl (by dsimp [hdrRebScanCursor]; omega))).trans hm9,
       (hout_m2 _ (hne_dc hdrRebInsCount (by decide) (by decide))
          (Or.inl (by dsimp [hdrRebInsCount]; omega))).trans hm10,
       (hout_m2 _ (hne_dc hdrRebCollision (by decide) (by decide))
          (Or.inl (by dsimp [hdrRebCollision]; omega))).trans hm11⟩
      (fun i hi => ⟨(hrp_pre hi (by omega) (by omega)).trans (hqv0 i hi).1,
        (hrp_pre hi (by omega) (by omega)).trans (hqv0 i hi).2⟩)
      (fun b' hb' loc hl =>
        (hrp_pre (mul_add_lt_mul_bound hb' hl) (by omega) (by omega)).trans (hloc0 b' hb' loc hl))
      (fun b' hb' => bktMeta_congr_of_readPacked
        (fun k hk => hrp_pre (show 16 * b' + k < 16 * numBucketsWhp n_max by omega)
          (by omega) (by omega))
        (hbmeta0 b' hb'))
      (fun b' hb' k hk =>
        (hrp_pre (mul_add_lt_mul_bound hb' hk) (by omega) (by omega)).trans (hbptr0 b' hb' k hk))
      (fun j hj => ⟨(hrp_pre hj (by omega) (by omega)).trans (hpool0 j hj).1,
        (hrp_pre hj (by omega) (by omega)).trans (hpool0 j hj).2⟩)
      (fun j hj => ?_)⟩
  · dsimp only [m2, m1]
    rw [readPacked_update_outside hw (show id < 6 * qEpochWhp n_max + 6 by omega)
      (Or.inl (by dsimp [hdrDirtyCount]; omega))]
    exact readPacked_writePacked_of_ne hw s.mem (by dsimp [idxW]; omega) b
  · dsimp only [m2, m1] at hj ⊢
    rw [readPacked_update_outside hw
      (show 3 * qEpochWhp n_max + j < 6 * qEpochWhp n_max + 6 by omega)
      (Or.inl (by dsimp [hdrDirtyCount]; omega))]
    by_cases hjd : j = fs.dirtyCount
    · subst hjd
      simp only [Function.update_self]
      exact readPacked_writePacked_self _ _ _ s.mem idxW hb_g
    · simp only [Function.update_of_ne hjd]
      exact (readPacked_writePacked_of_ne hw s.mem (by dsimp [idxW]; omega) b).trans
        (hdirty0 j (by omega))

/-! ## Section 4: Control-Predicate and Composite Header/Bucket Helpers -/

/-- Pure-ALU evaluation of `inLiveTree rebStage oldEp rebDoneB st` (`0` or `1`). -/
@[irreducible] def inLiveTreeProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((rebStage, oldEp), (rebDoneB, st)) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let z2 ← pure 2
    let z3 ← pure 3
    if st = z1 then
      pure z1
    else do
      let tagOld ← pure (z2 + oldEp)
      if st = tagOld then
        if rebStage = z3 then
          pure z1
        else if rebStage = z2 then
          if rebDoneB = z1 then pure z1 else pure z0
        else
          pure z0
      else
        pure z0

theorem realizes_inLiveTree :
    Realizes .exact inLiveTreeProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w ((_, oldEp), _) _ => 2 ≤ w ∧ oldEp ≤ 1)
      (fun _ _ => 0) := by
  unfold inLiveTreeProg
  realize
  all_goals (
    rcases d with ⟨⟨rebStage, oldEp⟩, ⟨rebDoneB, st⟩⟩
    dsimp only at *
    obtain ⟨hw2, hold⟩ := h
    have h4 : 4 ≤ 2 ^ w := (by decide : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right two_pos hw2)
    change _ < 2 ^ w
    omega
  )

theorem inLiveTreeProg_spec {w F rebStage oldEp rebDoneB st : ℕ} {s : Memory.State} :
    let prog := inLiveTreeProg ((rebStage, oldEp), (rebDoneB, st))
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if inLiveTree rebStage oldEp rebDoneB st then 1 else 0) ∧
    memoryCost prog s = 0 ∧
    ValidProg w F s prog := by
  have hin : (inLiveTree rebStage oldEp rebDoneB st = true) ↔
      (st = 1 ∨ (st = 2 + oldEp ∧ ((rebStage = 2 ∧ rebDoneB = 1) ∨ rebStage = 3))) := by
    unfold inLiveTree
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  dsimp only
  simp only [hin]
  unfold inLiveTreeProg
  simp only [pure_bind]
  by_cases h1 : st = 1
  · subst h1
    simp only [↓reduceIte, true_or]
    exact ⟨rfl, rfl, rfl, validProg_pure _⟩
  · simp only [h1, ↓reduceIte, false_or]
    by_cases ho : st = 2 + oldEp
    · simp only [ho, ↓reduceIte, true_and]
      by_cases hs3 : rebStage = 3
      · subst hs3
        simp only [↓reduceIte, or_true]
        exact ⟨rfl, rfl, rfl, validProg_pure _⟩
      · simp only [hs3, ↓reduceIte, or_false]
        by_cases hs2 : rebStage = 2
        · subst hs2
          simp only [↓reduceIte, true_and]
          by_cases hd1 : rebDoneB = 1 <;>
            (simp only [hd1, ↓reduceIte]; exact ⟨rfl, rfl, rfl, validProg_pure _⟩)
        · simp only [hs2, ↓reduceIte, false_and]
          exact ⟨rfl, rfl, rfl, validProg_pure _⟩
    · simp only [ho, ↓reduceIte, false_and]
      exact ⟨rfl, rfl, rfl, validProg_pure _⟩

/-- Check `rebActiveB` for bucket `b` (`d = ((cp, base), b)`), returning `1` or `0`. -/
@[irreducible] def readRebActiveBGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), b) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let z2 ← pure 2
    let stg ← readHdrProg (base, hdrRebStage)
    if stg = z2 then do
      let dIdx ← readHdrProg (base, hdrDirtyIdx)
      let dCnt ← readHdrProg (base, hdrDirtyCount)
      if dIdx < dCnt then do
        let db ← readDirtyBucketGenProg ((cp, base), dIdx)
        if db = b then do
          let cand ← readHdrProg (base, hdrRebCandSalt)
          let coll ← readHdrProg (base, hdrRebCollision)
          if cand < wpSMax cp then
            if coll = z0 then pure z1 else pure z0
          else
            pure z0
        else
          pure z0
      else
        pure z0
    else
      pure z0

theorem realizes_readRebActiveBGen :
    Realizes .exact readRebActiveBGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), _) s =>
        WhpLargeEnvGen w cp base ∧ s.mem (base + hdrDirtyCount) ≤ wpQEpoch cp)
      (fun _ _ => 0) := by
  unfold readRebActiveBGenProg
  have hrh := realizes_readHdr
  have hrd := realizes_readDirtyBucketGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hdc_le⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hcs_h : ∀ off < 32, ∀ s',
        (Memory.spec 0).clientState s' (readHdrProg (base, off)) = s' :=
      fun off hoff s' => (readHdrProg_large_spec (c := c) (U := U) (V := V) (w := w)
        (n_max := n_max) (s := s') hoff).1
    have hcr_h : ∀ off < 32, ∀ s',
        (Memory.spec 0).clientResult s' (readHdrProg (base, off)) = s'.mem (base + off) :=
      fun off hoff s' => (readHdrProg_large_spec (c := c) (U := U) (V := V) (w := w)
        (n_max := n_max) (s := s') hoff).2.1
    have hcs4 := hcs_h hdrRebStage (by decide)
    have hcr4 := hcr_h hdrRebStage (by decide)
    have hcs6 := hcs_h hdrDirtyCount (by decide)
    have hcr6 := hcr_h hdrDirtyCount (by decide)
    have hcs7 := hcs_h hdrDirtyIdx (by decide)
    have hcr7 := hcr_h hdrDirtyIdx (by decide)
    have hcs8 := hcs_h hdrRebCandSalt (by decide)
    have hcr8 := hcr_h hdrRebCandSalt (by decide)
    have hcs11 := hcs_h hdrRebCollision (by decide)
    have hcr11 := hcr_h hdrRebCollision (by decide)
    simp only [hcs4, hcr4] at *
    simp only [hcs6, hcr6] at *
    simp only [hcs7, hcr7] at *
    simp only [hcs8, hcr8] at *
    simp only [hcs11, hcr11] at *
    simp only [wp_large_qEpoch hth] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | omega
  )

theorem readRebActiveBGenProg_spec {c U V w n_max base b : ℕ} {fs : FastState}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readRebActiveBGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    let rebActiveB : Bool :=
      decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
        fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
        fs.rebCollision = 0)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (if rebActiveB then 1 else 0) ∧
    memoryCost prog s ≤ 7 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  rcases hrep with ⟨hdc_le, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    hqv, hloc, hbmeta, hbptr, hpool, hsl, hbuf0, hbuf1, hdirty⟩
  have hrep_orig : FastMemRep base c U V w n_max fs s.mem :=
    ⟨hdc_le, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
      hqv, hloc, hbmeta, hbptr, hpool, hsl, hbuf0, hbuf1, hdirty⟩
  obtain ⟨hst4, hres4, hmc4, hvp4⟩ := readHdrProg_large_spec (c := c) (U := U) (V := V) (w := w)
    (n_max := n_max) (base := base) (hdrOff := hdrRebStage) (s := s) (by decide)
  obtain ⟨hst7, hres7, hmc7, hvp7⟩ := readHdrProg_large_spec (c := c) (U := U) (V := V) (w := w)
    (n_max := n_max) (base := base) (hdrOff := hdrDirtyIdx) (s := s) (by decide)
  obtain ⟨hst6, hres6, hmc6, hvp6⟩ := readHdrProg_large_spec (c := c) (U := U) (V := V) (w := w)
    (n_max := n_max) (base := base) (hdrOff := hdrDirtyCount) (s := s) (by decide)
  obtain ⟨hst8, hres8, hmc8, hvp8⟩ := readHdrProg_large_spec (c := c) (U := U) (V := V) (w := w)
    (n_max := n_max) (base := base) (hdrOff := hdrRebCandSalt) (s := s) (by decide)
  obtain ⟨hst11, hres11, hmc11, hvp11⟩ := readHdrProg_large_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) (hdrOff := hdrRebCollision) (s := s) (by decide)
  dsimp only
  unfold readRebActiveBGenProg
  simp only [wp_large_sMax hth, pure_bind]
  by_cases hs2 : fs.rebStage = 2
  · by_cases hdi : fs.dirtyIdx < fs.dirtyCount
    · obtain ⟨hdb_st, hdb_res, hdb_mc, hdb_vp⟩ :=
        readDirtyBucketGenProg_spec henv hdi hrep_orig (s := s)
      by_cases hdb : fs.dirtyBuckets fs.dirtyIdx = b
      · refine ⟨?_, ?_, ?_, ?_⟩
        · rw [clientState_bind, hst4, hres4, hm4]; simp only [hs2, ↓reduceIte]
          rw [clientState_bind, hst7, hres7, hm7, clientState_bind, hst6, hres6, hm6]
          simp only [hdi, ↓reduceIte]
          rw [clientState_bind, hdb_st, hdb_res]; simp only [hdb, ↓reduceIte]
          rw [clientState_bind, hst8, hres8, hm8, clientState_bind, hst11, hres11, hm11]
          split_ifs <;> rfl
        · rw [clientResult_bind, hst4, hres4, hm4, ite_eq_left hs2,
            clientResult_bind, hst7, hres7, hm7, clientResult_bind, hst6, hres6, hm6,
            ite_eq_left hdi, clientResult_bind, hdb_st, hdb_res, ite_eq_left hdb,
            clientResult_bind, hst8, hres8, hm8, clientResult_bind, hst11, hres11, hm11]
          by_cases hcs : fs.rebCandSalt < sMaxWhp c n_max
          · rw [ite_eq_left hcs]
            by_cases hcl : fs.rebCollision = 0
            · rw [ite_eq_left hcl, decide_eq_true ⟨hs2, hdi, hdb, hcs, hcl⟩]; rfl
            · rw [ite_eq_right hcl, decide_eq_false (fun h => hcl h.2.2.2.2)]; rfl
          · rw [ite_eq_right hcs, decide_eq_false (fun h => hcs h.2.2.2.1)]; rfl
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hst4, hres4, hmc4, hm4]; simp only [hs2, ↓reduceIte, memoryCost_bind]
          rw [hst7, hres7, hmc7, hm7, hst6, hres6, hmc6, hm6]
          simp only [hdi, ↓reduceIte, memoryCost_bind]
          rw [hdb_st, hdb_res, hdb_mc]; simp only [hdb, ↓reduceIte, memoryCost_bind]
          rw [hst8, hres8, hmc8, hm8, hst11, hres11, hmc11, hm11]
          split_ifs <;> simp
        · refine validProg_bind hvp4 ?_
          rw [hst4, hres4, hm4]; simp only [hs2, ↓reduceIte]
          refine validProg_bind hvp7 ?_
          rw [hst7, hres7, hm7]
          refine validProg_bind hvp6 ?_
          rw [hst6, hres6, hm6]; simp only [hdi, ↓reduceIte]
          refine validProg_bind hdb_vp ?_
          rw [hdb_st, hdb_res]; simp only [hdb, ↓reduceIte]
          refine validProg_bind hvp8 ?_
          rw [hst8]
          refine validProg_bind hvp11 ?_
          rw [hst11]
          split_ifs <;> exact validProg_pure _
      · refine ⟨?_, ?_, ?_, ?_⟩
        · rw [clientState_bind, hst4, hres4, hm4]; simp only [hs2, ↓reduceIte]
          rw [clientState_bind, hst7, hres7, hm7, clientState_bind, hst6, hres6, hm6]
          simp only [hdi, ↓reduceIte]
          rw [clientState_bind, hdb_st, hdb_res, ite_eq_right hdb]; rfl
        · rw [clientResult_bind, hst4, hres4, hm4]; simp only [hs2, ↓reduceIte]
          rw [clientResult_bind, hst7, hres7, hm7, clientResult_bind, hst6, hres6, hm6]
          simp only [hdi, ↓reduceIte]
          rw [clientResult_bind, hdb_st, hdb_res, ite_eq_right hdb]; simp [hdb]
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hst4, hres4, hmc4, hm4]; simp only [hs2, ↓reduceIte, memoryCost_bind]
          rw [hst7, hres7, hmc7, hm7, hst6, hres6, hmc6, hm6]
          simp only [hdi, ↓reduceIte, memoryCost_bind]
          rw [hdb_st, hdb_res, hdb_mc, ite_eq_right hdb]; simp
        · refine validProg_bind hvp4 ?_
          rw [hst4, hres4, hm4]; simp only [hs2, ↓reduceIte]
          refine validProg_bind hvp7 ?_
          rw [hst7, hres7, hm7]
          refine validProg_bind hvp6 ?_
          rw [hst6, hres6, hm6]; simp only [hdi, ↓reduceIte]
          refine validProg_bind hdb_vp ?_
          rw [hdb_st, hdb_res, ite_eq_right hdb]; exact validProg_pure _
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [clientState_bind, hst4, hres4, hm4]; simp only [hs2, ↓reduceIte]
        rw [clientState_bind, hst7, hres7, hm7, clientState_bind, hst6, hres6, hm6,
          ite_eq_right hdi]; rfl
      · rw [clientResult_bind, hst4, hres4, hm4]; simp only [hs2, ↓reduceIte]
        rw [clientResult_bind, hst7, hres7, hm7, clientResult_bind, hst6, hres6, hm6,
          ite_eq_right hdi]; simp [hdi]
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hst4, hres4, hmc4, hm4]; simp only [hs2, ↓reduceIte, memoryCost_bind]
        rw [hst7, hres7, hmc7, hm7, hst6, hres6, hmc6, hm6, ite_eq_right hdi]; simp
      · refine validProg_bind hvp4 ?_
        rw [hst4, hres4, hm4]; simp only [hs2, ↓reduceIte]
        refine validProg_bind hvp7 ?_
        rw [hst7, hres7, hm7]
        refine validProg_bind hvp6 ?_
        rw [hst6, hres6, hm6, ite_eq_right hdi]; exact validProg_pure _
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hst4, hres4, hm4, ite_eq_right hs2]; rfl
    · rw [clientResult_bind, hst4, hres4, hm4, ite_eq_right hs2]; simp [hs2]
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst4, hres4, hmc4, hm4, ite_eq_right hs2]; simp
    · refine validProg_bind hvp4 ?_
      rw [hst4, hres4, hm4, ite_eq_right hs2]; exact validProg_pure _

/-- Read `fs.oldEp = 1 - fs.curEp` from `mem[base + hdrCurEp]`. -/
@[irreducible] def readOldEpProg (base : ℕ) : Memory.Prog ℕ := do
  let z0 ← pure 0
  let z1 ← pure 1
  let curEp ← readHdrProg (base, hdrCurEp)
  if curEp = z0 then pure z1 else pure z0

theorem realizes_readOldEp :
    Realizes .exact readOldEpProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w base _ => 2 ≤ w ∧ Fits w (base + hdrCurEp))
      (fun _ _ => 0) := by
  unfold readOldEpProg
  have hrh := realizes_readHdr
  realize
  all_goals (
    obtain ⟨hw2, hfit⟩ := h
    first
    | exact Nat.one_lt_two_pow (by omega)
    | (change 2 < 2 ^ w
       calc 2 < 2 ^ 2 := by decide
         _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw2)
    | exact hfit
  )

theorem readOldEpProg_spec {w F base : ℕ} {fs : FastState} {s : Memory.State}
    (ha : base + hdrCurEp < F) (hce_or : fs.curEp = 0 ∨ fs.curEp = 1)
    (hm2 : s.mem (base + hdrCurEp) = fs.curEp) :
    let prog := readOldEpProg base
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.oldEp ∧
    memoryCost prog s = 1 ∧
    ValidProg w F s prog := by
  obtain ⟨hst, hres, hmc, hvp⟩ := readHdrProg_spec (w := w) (F := F) ha (s := s)
  rw [hm2] at hres
  unfold readOldEpProg
  simp only [pure_bind]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hst]; split_ifs <;> rfl
  · rw [clientResult_bind, hst, hres]
    rcases hce_or with h0 | h1
    · simp [FastState.oldEp, h0]
    · simp [FastState.oldEp, h1]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hst, hmc]; split_ifs <;> rfl
  · refine validProg_bind hvp ?_; rw [hst]; split_ifs <;> exact validProg_pure _

/-- Read `(bktSalt b, liveSliceIdx b)` for bucket `b` (`d = ((cp, base), b)`). -/
@[irreducible] def readLiveSaltIdxGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, base), b) => do
    let z1 ← pure 1
    let z2 ← pure 2
    let salt ← readBktFieldGenProg (((cp, base), b), z1)
    let lRole ← readBktFieldGenProg (((cp, base), b), z2)
    let lIdx ← pure (3 * b + lRole)
    pure (salt, lIdx)

theorem realizes_readLiveSaltIdxGen :
    Realizes .exact readLiveSaltIdxGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((cp, base), b) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.liveRole b < 3)
      (fun _ _ => 0) := by
  unfold readLiveSaltIdxGenProg
  have hrb := realizes_readBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hlr⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h3M := (large_index_bounds hth).2.2.2.2.1
    obtain ⟨hr1_st, hr1_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 1 < 10) hrep (s := s)
    obtain ⟨hr2_st, hr2_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 2 < 10) hrep (s := s)
    simp only [getBktField] at hr1_res hr2_res
    simp only [hr1_st, hr2_st, hr2_res, wp_large_M hth] at *
    first
    | decide
    | assumption
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
  )

theorem readLiveSaltIdxGenProg_spec {c U V w n_max base b : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readLiveSaltIdxGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (fs.bktSalt b, fs.liveSliceIdx b) ∧
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨hr1_st, hr1_res, hr1_mc, hr1_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 1 < 10) hrep (s := s)
  obtain ⟨hr2_st, hr2_res, hr2_mc, hr2_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 2 < 10) hrep (s := s)
  simp only [getBktField] at hr1_res hr2_res
  unfold readLiveSaltIdxGenProg
  simp only [pure_bind]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hr1_st, clientState_bind, hr2_st]; rfl
  · rw [clientResult_bind, hr1_st, hr1_res, clientResult_bind, hr2_st, hr2_res]; rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hr1_st, hr1_mc, hr2_st, hr2_mc]; rfl
  · refine validProg_bind hr1_vp ?_; rw [hr1_st]
    refine validProg_bind hr2_vp ?_; rw [hr2_st]
    exact validProg_pure _

theorem fpOfSaltOpt_lt (c U n_max salt kv : ℕ) (θ₂ : FpSeed c U n_max) :
    (if hs : salt < sMaxWhp c n_max then
      if hu : kv < U then fpHash c U n_max θ₂ ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
     else 0) < 2 ^ fpBitsWhp n_max := by
  split_ifs with hs hu
  · exact fpHash_lt c U n_max θ₂ ⟨salt, hs⟩ ⟨kv, hu⟩
  · exact Nat.two_pow_pos _
  · exact Nat.two_pow_pos _

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
