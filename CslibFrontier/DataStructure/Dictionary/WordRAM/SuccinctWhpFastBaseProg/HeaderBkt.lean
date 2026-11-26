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

/-- From `s`, `p` leaves the state unchanged, returns `r`, issues exactly `C` memory operations,
and is valid below frontier `F`. -/
private structure ReadSpec {α : Type} (w F : ℕ) (s : Memory.State) (p : Memory.Prog α) (r : α)
    (C : ℕ) : Prop where
  state : (Memory.spec 0).clientState s p = s
  result : (Memory.spec 0).clientResult s p = r
  cost : memoryCost p s = C
  valid : ValidProg w F s p

private theorem ReadSpec.of {α : Type} {w F C : ℕ} {s : Memory.State} {p : Memory.Prog α}
    {r r' : α} (h : (Memory.spec 0).clientState s p = s ∧ (Memory.spec 0).clientResult s p = r ∧
      memoryCost p s = C ∧ ValidProg w F s p) (hr : r = r') : ReadSpec w F s p r' C :=
  ⟨h.1, hr ▸ h.2.1, h.2.2.1, h.2.2.2⟩

private theorem ReadSpec.toAnd {α : Type} {w F C C' : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {r r' : α} (h : ReadSpec w F s p r C) (hr : r = r') (hC : C = C') :
    (Memory.spec 0).clientState s p = s ∧ (Memory.spec 0).clientResult s p = r' ∧
      memoryCost p s = C' ∧ ValidProg w F s p :=
  ⟨h.state, hr ▸ h.result, hC ▸ h.cost, h.valid⟩

private theorem ReadSpec.toAnd_le {α : Type} {w F C C' : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {r r' : α} (h : ReadSpec w F s p r C) (hr : r = r') (hC : C ≤ C') :
    (Memory.spec 0).clientState s p = s ∧ (Memory.spec 0).clientResult s p = r' ∧
      memoryCost p s ≤ C' ∧ ValidProg w F s p :=
  ⟨h.state, hr ▸ h.result, h.cost ▸ hC, h.valid⟩

private theorem ReadSpec.pure {α : Type} {w F : ℕ} {s : Memory.State} (a : α) :
    ReadSpec w F s (pure a) a 0 :=
  ⟨rfl, rfl, rfl, validProg_pure a⟩

/-- Peel a read-only prefix `m` off `m >>= k`. -/
private theorem ReadSpec.bind_eq {α β : Type} {w F C : ℕ} {s : Memory.State}
    {m : Memory.Prog α} {a : α} (hm : ReadSpec w F s m a C) (k : α → Memory.Prog β) :
    (Memory.spec 0).clientState s (m >>= k) = (Memory.spec 0).clientState s (k a) ∧
    (Memory.spec 0).clientResult s (m >>= k) = (Memory.spec 0).clientResult s (k a) ∧
    memoryCost (m >>= k) s = C + memoryCost (k a) s ∧
    (ValidProg w F s (k a) → ValidProg w F s (m >>= k)) :=
  ⟨by rw [clientState_bind, hm.state, hm.result], by rw [clientResult_bind, hm.state, hm.result],
    by rw [memoryCost_bind', hm.state, hm.result, hm.cost],
    fun h => validProg_bind hm.valid (by rw [hm.state, hm.result]; exact h)⟩

private theorem ReadSpec.bind {α β : Type} {w F C₁ C₂ : ℕ} {s : Memory.State}
    {m : Memory.Prog α} {k : α → Memory.Prog β} {a : α} {b : β}
    (hm : ReadSpec w F s m a C₁) (hk : ReadSpec w F s (k a) b C₂) :
    ReadSpec w F s (m >>= k) b (C₁ + C₂) :=
  have h := hm.bind_eq k
  ⟨h.1.trans hk.state, h.2.1.trans hk.result, h.2.2.1.trans (congrArg _ hk.cost),
    h.2.2.2 hk.valid⟩

private theorem ReadSpec.ite {α : Type} {w F C : ℕ} {s : Memory.State} {c : Prop}
    [Decidable c] {p₁ p₂ : Memory.Prog α} {r₁ r₂ : α}
    (h₁ : ReadSpec w F s p₁ r₁ C) (h₂ : ReadSpec w F s p₂ r₂ C) :
    ReadSpec w F s (if c then p₁ else p₂) (if c then r₁ else r₂) C := by
  split_ifs <;> assumption

private theorem ReadSpec.if_pos {α : Type} {w F C : ℕ} {s : Memory.State} {c : Prop}
    [Decidable c] {p₁ p₂ : Memory.Prog α} {r : α} (hc : c) (h : ReadSpec w F s p₁ r C) :
    ReadSpec w F s (if c then p₁ else p₂) r C := by
  rwa [ite_eq_left hc]

private theorem ReadSpec.if_neg {α : Type} {w F C : ℕ} {s : Memory.State} {c : Prop}
    [Decidable c] {p₁ p₂ : Memory.Prog α} {r : α} (hc : ¬c) (h : ReadSpec w F s p₂ r C) :
    ReadSpec w F s (if c then p₁ else p₂) r C := by
  rwa [ite_eq_right hc]

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
  have hupd_at : ∀ k, m' (base + k) = if k = hdrOff then val else s.mem (base + k) := fun k => by
    by_cases hk : k = hdrOff <;> simp [m', hk]
  obtain ⟨hdc_le0, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    hqv0, hloc0, hbmeta0, hbptr0, hpool0, _, _, _, hdirty0⟩ := id hrep
  set fs' := updateFastHdr fs hdrOff val
  have hcases : hdrOff = 1 ∨ hdrOff = 2 ∨ hdrOff = 3 ∨ hdrOff = 4 ∨ hdrOff = 5 ∨
      hdrOff = 6 ∨ hdrOff = 7 ∨ hdrOff = 8 ∨ hdrOff = 9 ∨ hdrOff = 10 ∨ hdrOff = 11 := by omega
  let fs₁ : FastState :=
    { fs with
      poolFreeTop := fs'.poolFreeTop, curEp := fs'.curEp, epochClock := fs'.epochClock,
      rebStage := fs'.rebStage, stageCursor := fs'.stageCursor, dirtyCount := fs'.dirtyCount,
      dirtyIdx := fs'.dirtyIdx, rebCandSalt := fs'.rebCandSalt, rebScanCursor := fs'.rebScanCursor,
      rebInsCount := fs'.rebInsCount, rebCollision := fs'.rebCollision }
  have hfs' : fs' = fs₁ := by
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hdc_sub : fs'.dirtyCount ≤ fs.dirtyCount := by
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact le_rfl | exact hdc rfl
  have hhdrs :
      m' (base + hdrMode) = 1 ∧ m' (base + hdrPoolFreeTop) = fs'.poolFreeTop ∧
      m' (base + hdrCurEp) = fs'.curEp ∧ m' (base + hdrEpochClock) = fs'.epochClock ∧
      m' (base + hdrRebStage) = fs'.rebStage ∧ m' (base + hdrStageCursor) = fs'.stageCursor ∧
      m' (base + hdrDirtyCount) = fs'.dirtyCount ∧ m' (base + hdrDirtyIdx) = fs'.dirtyIdx ∧
      m' (base + hdrRebCandSalt) = fs'.rebCandSalt ∧
      m' (base + hdrRebScanCursor) = fs'.rebScanCursor ∧
      m' (base + hdrRebInsCount) = fs'.rebInsCount ∧
      m' (base + hdrRebCollision) = fs'.rebCollision := by
    dsimp only [hdrMode, hdrPoolFreeTop, hdrCurEp, hdrEpochClock, hdrRebStage,
      hdrStageCursor, hdrDirtyCount, hdrDirtyIdx, hdrRebCandSalt, hdrRebScanCursor,
      hdrRebInsCount, hdrRebCollision]
    rw [hupd_at 0, hupd_at 1, hupd_at 2, hupd_at 3, hupd_at 4, hupd_at 5, hupd_at 6,
      hupd_at 7, hupd_at 8, hupd_at 9, hupd_at 10, hupd_at 11]
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | assumption
  refine ⟨rfl, validProg_write (by omega) hfit_val, hfs' ▸
    fastStep_nonSliceNonBuf hw rfl hseed hrep rfl rfl
      (fun a ha =>
        show Function.update s.mem (base + hdrOff) val a = s.mem a from
          Function.update_of_ne (by rcases ha with h | h | h | h <;> omega) val s.mem)
      (fun _ hidx _ => hrp32 hidx (by omega))
      (fun id hid => hrp32 (show id < 6 * qEpochWhp n_max + 6 by omega) (by omega))
      (hdc_sub.trans hdc_le0) hhdrs
      (fun i hi => ⟨(hrp32 hi (by omega)).trans (hqv0 i hi).1,
        (hrp32 hi (by omega)).trans (hqv0 i hi).2⟩)
      (fun b hb loc hl =>
        (hrp32 (mul_add_lt_mul_bound hb hl) (by omega)).trans (hloc0 b hb loc hl))
      (fun b hb => bktMeta_congr_of_readPacked
        (fun k hk => hrp32 (show 16 * b + k < 16 * numBucketsWhp n_max by omega) (by omega))
        (hbmeta0 b hb))
      (fun b hb k hk =>
        (hrp32 (mul_add_lt_mul_bound hb hk) (by omega)).trans (hbptr0 b hb k hk))
      (fun j hj => ⟨(hrp32 hj (by omega)).trans (hpool0 j hj).1,
        (hrp32 hj (by omega)).trans (hpool0 j hj).2⟩)
      (fun j (hj : j < fs'.dirtyCount) =>
        (hrp32 (show 3 * qEpochWhp n_max + j < 6 * qEpochWhp n_max + 6 by omega)
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
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b hb
  unfold readBktFieldGenProg
  simp only [wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth, pure_bind]
  refine ⟨rfl, ?_, rfl, validProg_readPacked hw hidx hbm_le⟩
  rw [clientResult_readPackedGen]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : field = 0 ∨ field = 1 ∨
    field = 2 ∨ field = 3 ∨ field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 ∨ field = 8 ∨
    field = 9 := by omega
  all_goals assumption

/-- `readBktFieldGenProg_spec` packaged as a `CostBoundedStep`. -/
theorem CostBoundedStep.readBkt {c U V w n_max base b field : ℕ} {fs : FastState}
    {s : Memory.State} (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hfield : field < 10)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
      (readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), field)) s
      (getBktField fs b field) 2 :=
  .of (readBktFieldGenProg_spec henv hb hfield hrep)

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
      simpa using readPacked_writePacked_self _ _ _ s.mem idxW hval_g
    · simp only [hbk, ↓reduceIte]
      refine readPacked_writePacked_of_ne hw s.mem (fun heq => hbk ?_) val
      exact mul_add_inj_right (Nat.lt_of_lt_of_le hk (Nat.le_add_right 10 6))
        (Nat.lt_of_lt_of_le hfield (Nat.le_add_right 10 6)) (by omega)
  obtain ⟨hdc_le0, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    hqv0, hloc0, hbmeta0, hbptr0, hpool0, _, _, _, hdirty0⟩ := id hrep
  set fs' := setBktField fs b field val
  have hcases : field = 0 ∨ field = 1 ∨ field = 2 ∨ field = 3 ∨ field = 4 ∨
      field = 5 ∨ field = 6 ∨ field = 7 ∨ field = 8 ∨ field = 9 := by omega
  let fs₁ : FastState :=
    { fs with
      bktCount := fs'.bktCount, bktSalt := fs'.bktSalt, liveRole := fs'.liveRole,
      liveInsCount := fs'.liveInsCount, overmarsRole := fs'.overmarsRole,
      overmarsActive := fs'.overmarsActive, overmarsCursor := fs'.overmarsCursor,
      overmarsInsCount := fs'.overmarsInsCount, rebDoneFlag := fs'.rebDoneFlag,
      rebQueued := fs'.rebQueued }
  have hfs' : fs' = fs₁ := by
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hhdr_eq : ∀ h < 16, m' (base + h) = s.mem (base + h) :=
    fun h _ => hout_bm (base + h) (Or.inl (by omega))
  have hlo : ∀ {off N k idx}, idx < N → off + packedWords N k w ≤ offBktMeta c U V w n_max →
      readPacked (base + off) k w m' idx = readPacked (base + off) k w s.mem idx :=
    fun hidx _ => readPacked_congr hw (hidx := hidx) fun a ⟨_, _⟩ => hout_bm a (Or.inl (by omega))
  have hhi : ∀ {off N k idx}, idx < N → offFbStart c U V w n_max ≤ off →
      readPacked (base + off) k w m' idx = readPacked (base + off) k w s.mem idx :=
    fun hidx _ => readPacked_congr hw (hidx := hidx) fun a ⟨_, _⟩ => hout_bm a (Or.inr (by omega))
  refine ⟨rfl, validProg_writePacked hw hgk hidxW hbm_le, hfs' ▸
    fastStep_nonSliceNonBuf hw rfl hseed hrep rfl rfl
      (fun a ha => hout_bm a (by rcases ha with h1 | ⟨_, h2⟩ | ⟨h3, _⟩ | h4 <;> omega))
      (fun _ _ _ => readPacked_writePacked_of_ne hw s.mem (by dsimp [idxW]; omega) val)
      (fun id hid => hhi (show id < 6 * qEpochWhp n_max + 6 by omega) (by omega))
      hdc_le0
      ⟨(hhdr_eq _ (by decide)).trans hm0, (hhdr_eq _ (by decide)).trans hm1,
        (hhdr_eq _ (by decide)).trans hm2, (hhdr_eq _ (by decide)).trans hm3,
        (hhdr_eq _ (by decide)).trans hm4, (hhdr_eq _ (by decide)).trans hm5,
        (hhdr_eq _ (by decide)).trans hm6, (hhdr_eq _ (by decide)).trans hm7,
        (hhdr_eq _ (by decide)).trans hm8, (hhdr_eq _ (by decide)).trans hm9,
        (hhdr_eq _ (by decide)).trans hm10, (hhdr_eq _ (by decide)).trans hm11⟩
      (fun i hi => ⟨(hlo hi (by omega)).trans (hqv0 i hi).1,
        (hlo hi (by omega)).trans (hqv0 i hi).2⟩)
      (fun b' hb' loc hl =>
        (hlo (mul_add_lt_mul_bound hb' hl) (by omega)).trans (hloc0 b' hb' loc hl))
      (fun b' hb' => ?_)
      (fun b' hb' k hk =>
        (hhi (mul_add_lt_mul_bound hb' hk) (by omega)).trans (hbptr0 b' hb' k hk))
      (fun j hj => ⟨(hhi hj (by omega)).trans (hpool0 j hj).1,
        (hhi hj (by omega)).trans (hpool0 j hj).2⟩)
      (fun j (hj : j < fs.dirtyCount) =>
        (hhi (show 3 * qEpochWhp n_max + j < 6 * qEpochWhp n_max + 6 by omega)
          (by omega)).trans (hdirty0 j hj))⟩
  dsimp only [fs₁]
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
  obtain ⟨hdc_le0, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    hqv0, hloc0, hbmeta0, hbptr0, hpool0, _, _, _, hdirty0⟩ := id hrep
  have hR := ReadSpec.of (readHdrProg_large_spec (c := c) (U := U) (V := V) (w := w)
    (n_max := n_max) (base := base) (hdrOff := hdrDirtyCount) (s := s) (by decide)) hm6
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
  rw [(hR.bind_eq _).1, (hR.bind_eq _).2.2.1]
  refine ⟨?_, (hR.bind_eq _).2.2.2 (validProg_bind (validProg_writePacked hw hgk hidxW
    (dirtyBuckets_seg_le c U V w n_max base)) hwh_vp), ?_⟩
  · rw [memoryCost_bind', clientState_writePackedGen, memoryCost_writePackedGen]
    unfold writeHdrProg
    simp only [pure_bind, memoryCost_memRead_and_write.2]
  rw [clientState_bind, clientState_writePackedGen]
  unfold writeHdrProg
  simp only [pure_bind]
  change FastStateStep base c U V w n_max θ _ s { mem := m2, frontier := s.frontier }
  have hout_m2 : ∀ a, a ≠ base + hdrDirtyCount →
      (a < base + offTrieItems0 c U V w n_max ∨ base + offTrieItems1 c U V w n_max ≤ a) →
      m2 a = s.mem a := fun a hne ha =>
    (Function.update_of_ne hne _ _).trans (writePacked_outside hw _ hidxW _ (by omega))
  have hrp_pre : ∀ {off N k idx}, idx < N → 32 ≤ off →
      off + packedWords N k w ≤ offTrieItems0 c U V w n_max →
      readPacked (base + off) k w m2 idx = readPacked (base + off) k w s.mem idx :=
    fun hidx h32 hhi => readPacked_congr hw (hidx := hidx) fun a ⟨ha1, ha2⟩ =>
      hout_m2 a (by dsimp [hdrDirtyCount]; omega) (Or.inl (by omega))
  have hhdr : ∀ k < 12, k ≠ 6 → m2 (base + k) = s.mem (base + k) := fun k hk h6 =>
    hout_m2 _ (by dsimp only [hdrDirtyCount]; omega) (Or.inl (by omega))
  refine fastStep_nonSliceNonBuf hw rfl hseed hrep rfl rfl
      (fun a ha => hout_m2 a (by dsimp [hdrDirtyCount]; rcases ha with h | h | h | h <;> omega)
        (by rcases ha with h | h | h | h <;> omega))
      (fun idx hidx _ => hrp_pre hidx (by omega) (by omega))
      (fun id hid => ?_)
      (by dsimp only; omega)
      ⟨(hhdr _ (by decide) (by decide)).trans hm0, (hhdr _ (by decide) (by decide)).trans hm1,
        (hhdr _ (by decide) (by decide)).trans hm2, (hhdr _ (by decide) (by decide)).trans hm3,
        (hhdr _ (by decide) (by decide)).trans hm4, (hhdr _ (by decide) (by decide)).trans hm5,
        Function.update_self _ _ _, (hhdr _ (by decide) (by decide)).trans hm7,
        (hhdr _ (by decide) (by decide)).trans hm8, (hhdr _ (by decide) (by decide)).trans hm9,
        (hhdr _ (by decide) (by decide)).trans hm10, (hhdr _ (by decide) (by decide)).trans hm11⟩
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
      (fun j hj => ?_)
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
  dsimp only
  unfold inLiveTreeProg
  simp only [pure_bind]
  split_ifs <;> refine ⟨rfl, ?_, rfl, validProg_pure _⟩ <;> simp_all [inLiveTree]

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
    simp only [hcs_h hdrRebStage (by decide), hcr_h hdrRebStage (by decide),
      hcs_h hdrDirtyCount (by decide), hcr_h hdrDirtyCount (by decide),
      hcs_h hdrDirtyIdx (by decide), hcr_h hdrDirtyIdx (by decide)] at *
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
  obtain ⟨_, _, _, _, _, hm4, _, hm6, hm7, hm8, _, _, hm11, _⟩ := id hrep
  have hR {off v : ℕ} (hoff : off < 32) (hv : s.mem (base + off) = v) :=
    ReadSpec.of (readHdrProg_large_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
      (base := base) (s := s) hoff) hv
  dsimp only
  unfold readRebActiveBGenProg
  simp only [wp_large_sMax hth, pure_bind]
  by_cases hs2 : fs.rebStage = 2
  · by_cases hdi : fs.dirtyIdx < fs.dirtyCount
    · have hdb_r := ReadSpec.of (readDirtyBucketGenProg_spec henv hdi hrep (s := s)) rfl
      by_cases hdb : fs.dirtyBuckets fs.dirtyIdx = b
      · exact ReadSpec.toAnd_le ((hR (by decide) hm4).bind <| .if_pos hs2 <|
          (hR (by decide) hm7).bind <| (hR (by decide) hm6).bind <| .if_pos hdi <|
          hdb_r.bind <| .if_pos hdb <| (hR (by decide) hm8).bind <| (hR (by decide) hm11).bind <|
          .ite (.ite (.pure 1) (.pure 0)) (.pure 0)) (by simp [hs2, hdi, hdb, ite_and]) le_rfl
      · exact ReadSpec.toAnd_le ((hR (by decide) hm4).bind <| .if_pos hs2 <|
          (hR (by decide) hm7).bind <| (hR (by decide) hm6).bind <| .if_pos hdi <|
          hdb_r.bind <| .if_neg hdb <| .pure 0) (by simp [hdb]) (by omega)
    · exact ReadSpec.toAnd_le ((hR (by decide) hm4).bind <| .if_pos hs2 <|
        (hR (by decide) hm7).bind <| (hR (by decide) hm6).bind <| .if_neg hdi <| .pure 0)
        (by simp [hdi]) (by omega)
  · exact ReadSpec.toAnd_le ((hR (by decide) hm4).bind <| .if_neg hs2 <| .pure 0)
      (by simp [hs2]) (by omega)

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
  unfold readOldEpProg
  simp only [pure_bind]
  exact ReadSpec.toAnd ((ReadSpec.of (readHdrProg_spec (w := w) ha (s := s)) hm2).bind <|
    .ite (.pure 1) (.pure 0)) (by rcases hce_or with h | h <;> simp [FastState.oldEp, h]) rfl

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
  unfold readLiveSaltIdxGenProg
  simp only [pure_bind]
  exact ReadSpec.toAnd
    ((ReadSpec.of (readBktFieldGenProg_spec henv hb (by decide : 1 < 10) hrep (s := s)) rfl).bind <|
      (ReadSpec.of (readBktFieldGenProg_spec henv hb (by decide : 2 < 10) hrep (s := s))
        rfl).bind <| .pure _) rfl rfl

theorem fpOfSaltOpt_lt (c U n_max salt kv : ℕ) (θ₂ : FpSeed c U n_max) :
    (if hs : salt < sMaxWhp c n_max then
      if hu : kv < U then fpHash c U n_max θ₂ ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
     else 0) < 2 ^ fpBitsWhp n_max := by
  split_ifs with hs hu
  · exact fpHash_lt c U n_max θ₂ ⟨salt, hs⟩ ⟨kv, hu⟩
  all_goals exact Nat.two_pow_pos _

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
