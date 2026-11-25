/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.Frame

/-!
# Internal Frame and Packed-Segment Helpers for `SuccinctWhpFastBaseProg`

Privately imported proof infrastructure shared across the `SuccinctWhpFastBaseProg` submodules
(`SliceBuf`, `HeaderBkt`, `SlotArrays`, `LocPoolArrays`). This module is intentionally omitted from
the `SuccinctWhpFastBaseProg` umbrella's `public import`s so internal proof helpers do not leak
into the public API.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-- Reassociate `off + len ≤ sp` into `base + off + len ≤ base + sp`. -/
theorem seg_add_le {base off len sp : ℕ} (h : off + len ≤ sp) :
    base + off + len ≤ base + sp := by
  rw [Nat.add_assoc]
  exact Nat.add_le_add_left h _

/-- Packed-array safety discharge in the form expected by `realizes_readPackedGen` /
`realizes_writePackedGen`. -/
theorem WhpLargeEnv.packed_safe_true {c U V w n_max base off N k idx : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hk : k ≤ w) (hidx : idx < N)
    (hseg : off + packedWords N k w ≤ largeSpaceWhp c U V w n_max) :
    ∃ N', True ∧ 0 < w ∧ k ≤ w ∧ idx < N' ∧ Fits w (base + off + packedWords N' k w) := by
  obtain ⟨N', _, h2, h3, h4, h5⟩ := henv.packed_safe_of_le hk hidx hseg
  exact ⟨N', trivial, h2, h3, h4, h5⟩

/-- Injectivity of row-major index encoding `a * B + b` for `b < B`. -/
theorem mul_add_inj_right {B a₁ b₁ a₂ b₂ : ℕ} (hb₁ : b₁ < B) (hb₂ : b₂ < B)
    (heq : a₁ * B + b₁ = a₂ * B + b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have hB : 0 < B := by omega
  have ha : a₁ = a₂ := by
    have hd1 : (a₁ * B + b₁) / B = a₁ := by
      rw [Nat.mul_comm a₁ B, Nat.mul_add_div hB, Nat.div_eq_of_lt hb₁, Nat.add_zero]
    have hd2 : (a₂ * B + b₂) / B = a₂ := by
      rw [Nat.mul_comm a₂ B, Nat.mul_add_div hB, Nat.div_eq_of_lt hb₂, Nat.add_zero]
    rw [← hd1, heq, hd2]
  exact ⟨ha, by subst ha; omega⟩

/-- Congruence for the 10 scalar bucket-metadata fields in `offBktMeta`. -/
theorem bktMeta_congr_of_readPacked {base c U V w n_max b : ℕ} {fs : FastState}
    {mem₁ mem₂ : ℕ → ℕ}
    (h9 : ∀ k < 10,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem₂ (16 * b + k) =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem₁ (16 * b + k))
    (hm :
      let bm := offBktMeta c U V w n_max
      let g := globalPtrBits n_max
      readPacked (base + bm) g w mem₁ (16 * b + 0) = fs.bktCount b ∧
      readPacked (base + bm) g w mem₁ (16 * b + 1) = fs.bktSalt b ∧
      readPacked (base + bm) g w mem₁ (16 * b + 2) = fs.liveRole b ∧
      readPacked (base + bm) g w mem₁ (16 * b + 3) = fs.liveInsCount b ∧
      readPacked (base + bm) g w mem₁ (16 * b + 4) = fs.overmarsRole b ∧
      readPacked (base + bm) g w mem₁ (16 * b + 5) = fs.overmarsActive b ∧
      readPacked (base + bm) g w mem₁ (16 * b + 6) = fs.overmarsCursor b ∧
      readPacked (base + bm) g w mem₁ (16 * b + 7) = fs.overmarsInsCount b ∧
      readPacked (base + bm) g w mem₁ (16 * b + 8) = fs.rebDoneFlag b ∧
      readPacked (base + bm) g w mem₁ (16 * b + 9) = fs.rebQueued b) :
    let bm := offBktMeta c U V w n_max
    let g := globalPtrBits n_max
    readPacked (base + bm) g w mem₂ (16 * b + 0) = fs.bktCount b ∧
    readPacked (base + bm) g w mem₂ (16 * b + 1) = fs.bktSalt b ∧
    readPacked (base + bm) g w mem₂ (16 * b + 2) = fs.liveRole b ∧
    readPacked (base + bm) g w mem₂ (16 * b + 3) = fs.liveInsCount b ∧
    readPacked (base + bm) g w mem₂ (16 * b + 4) = fs.overmarsRole b ∧
    readPacked (base + bm) g w mem₂ (16 * b + 5) = fs.overmarsActive b ∧
    readPacked (base + bm) g w mem₂ (16 * b + 6) = fs.overmarsCursor b ∧
    readPacked (base + bm) g w mem₂ (16 * b + 7) = fs.overmarsInsCount b ∧
    readPacked (base + bm) g w mem₂ (16 * b + 8) = fs.rebDoneFlag b ∧
    readPacked (base + bm) g w mem₂ (16 * b + 9) = fs.rebQueued b :=
  ⟨(h9 0 (by decide)).trans hm.1,
    (h9 1 (by decide)).trans hm.2.1,
    (h9 2 (by decide)).trans hm.2.2.1,
    (h9 3 (by decide)).trans hm.2.2.2.1,
    (h9 4 (by decide)).trans hm.2.2.2.2.1,
    (h9 5 (by decide)).trans hm.2.2.2.2.2.1,
    (h9 6 (by decide)).trans hm.2.2.2.2.2.2.1,
    (h9 7 (by decide)).trans hm.2.2.2.2.2.2.2.1,
    (h9 8 (by decide)).trans hm.2.2.2.2.2.2.2.2.1,
    (h9 9 (by decide)).trans hm.2.2.2.2.2.2.2.2.2⟩

/-- `BufTrieMemRep` invariance when headers `12..15` and `[offTrieChild0, largeSpaceWhp)` are
unchanged (or `offTrieItems0` is only modified at indices `≥ 3 * qEpochWhp`). -/
theorem bufTrieMemRep_congr_nonBuf {base c U V w n_max ep : ℕ} {tr : BufTrie}
    {mem₁ mem₂ : ℕ → ℕ} (hw : 0 < w) (hep : ep = 0 ∨ ep = 1)
    (hhdr : ∀ h, 12 ≤ h → h < 16 → mem₂ (base + h) = mem₁ (base + h))
    (htrie : ∀ a, base + offTrieChild0 c U V w n_max ≤ a →
      a < base + offTrieItems0 c U V w n_max → mem₂ a = mem₁ a)
    (hit0 : ∀ id < 3 * qEpochWhp n_max,
      readPacked (base + offTrieItems0 c U V w n_max) (globalPtrBits n_max) w mem₂ id =
        readPacked (base + offTrieItems0 c U V w n_max) (globalPtrBits n_max) w mem₁ id)
    (hit1 : ∀ a, base + offTrieItems1 c U V w n_max ≤ a →
      a < base + largeSpaceWhp c U V w n_max → mem₂ a = mem₁ a)
    (hrep : BufTrieMemRep base c U V w n_max ep tr mem₁) :
    BufTrieMemRep base c U V w n_max ep tr mem₂ := by
  have hch := largeOffsetChain c U V w n_max
  have hch_eq : ∀ offC, offTrieChild0 c U V w n_max ≤ offC →
      offC + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤
        offTrieItems0 c U V w n_max →
      ∀ u < maxTrieNodesWhp c n_max, ∀ ch < 2 ^ bCharWhp n_max,
        readPacked (base + offC) (globalPtrBits n_max) w mem₂ (u * 2 ^ bCharWhp n_max + ch) =
          readPacked (base + offC) (globalPtrBits n_max) w mem₁ (u * 2 ^ bCharWhp n_max + ch) :=
    fun _ hlo hhi u hu ch hch_lt => by
      have hi : u * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max :=
        mul_add_lt_mul_bound hu hch_lt
      exact readPacked_congr hw (hidx := hi) fun a ⟨h1, h2⟩ =>
        htrie a (by omega) (by omega)
  have hmeta_eq : ∀ offM, offTrieChild0 c U V w n_max ≤ offM →
      offM + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
        offTrieItems0 c U V w n_max →
      ∀ u < maxTrieNodesWhp c n_max, ∀ k < 4,
        readPacked (base + offM) (globalPtrBits n_max) w mem₂ (4 * u + k) =
          readPacked (base + offM) (globalPtrBits n_max) w mem₁ (4 * u + k) :=
    fun _ hlo hhi u hu k hk =>
      readPacked_congr hw (hidx := show 4 * u + k < 6 * maxTrieNodesWhp c n_max by omega)
        fun a ⟨h1, h2⟩ => htrie a (by omega) (by omega)
  have hit : ∀ id < 3 * qEpochWhp n_max,
      readPacked (base + if ep = 0 then offTrieItems0 c U V w n_max
        else offTrieItems1 c U V w n_max) (globalPtrBits n_max) w mem₂ id =
      readPacked (base + if ep = 0 then offTrieItems0 c U V w n_max
        else offTrieItems1 c U V w n_max) (globalPtrBits n_max) w mem₁ id := by
    rcases hep with rfl | rfl
    · exact hit0
    · rw [ite_eq_right one_ne_zero]
      exact fun id hid => readPacked_congr hw (hidx := show id < 6 * qEpochWhp n_max + 6 by omega)
        fun a ⟨h1, h2⟩ => hit1 a h1 (by omega)
  have hmc := hmeta_eq (if ep = 0 then offTrieMeta0 c U V w n_max else offTrieMeta1 c U V w n_max)
    (by split <;> omega) (by split <;> omega)
  dsimp only [BufTrieMemRep] at hrep ⊢
  obtain ⟨hna, hia, hhdr_na, hhdr_ia, hchild, hpar, hleaf, hitems⟩ := hrep
  refine ⟨hna, hia,
    (hhdr _ (by split <;> decide) (by split <;> decide)).trans hhdr_na,
    (hhdr _ (by split <;> decide) (by split <;> decide)).trans hhdr_ia,
    fun u hu ch hch_lt =>
      (hch_eq _ (by split <;> omega) (by split <;> omega) u hu ch hch_lt).trans
        (hchild u hu ch hch_lt),
    fun u hu1 hu =>
      ⟨(hmc u (hu.trans_le hna) 0 (by decide)).trans (hpar u hu1 hu).1,
       (hmc u (hu.trans_le hna) 1 (by decide)).trans (hpar u hu1 hu).2⟩,
    fun u hu =>
      ⟨(hmc u (hu.trans_le hna) 2 (by decide)).trans (hleaf u hu).1,
       fun hnz => (hmc u (hu.trans_le hna) 3 (by decide)).trans ((hleaf u hu).2 hnz)⟩,
    fun id hid => ⟨(hit id (by omega)).trans (hitems id hid).1,
      (hit _ (by omega)).trans (hitems id hid).2.1,
      (hit _ (by omega)).trans (hitems id hid).2.2⟩⟩

/-- Master frame helper for scalar/array updates that leave `slices` and `buf` unchanged. -/
theorem fastStep_nonSliceNonBuf {base c U V w n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState} {s s' : Memory.State}
    (hw : 0 < w)
    (hfr : s'.frontier = s.frontier)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hsl_eq : fs'.slices = fs.slices)
    (hbuf_eq : fs'.buf = fs.buf)
    (hfence : ∀ a, (a < base ∨
        (base + 12 ≤ a ∧ a < base + offQuotWhp c w n_max) ∨
        (base + offBtMeta c U V w n_max ≤ a ∧ a < base + offTrieItems0 c U V w n_max) ∨
        base + offTrieItems1 c U V w n_max ≤ a) → s'.mem a = s.mem a)
    (hbm_sl : ∀ idx < 16 * numBucketsWhp n_max, 10 ≤ idx % 16 →
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx)
    (hit0 : ∀ id < 3 * qEpochWhp n_max,
      readPacked (base + offTrieItems0 c U V w n_max) (globalPtrBits n_max) w s'.mem id =
        readPacked (base + offTrieItems0 c U V w n_max) (globalPtrBits n_max) w s.mem id)
    (hdc_le : fs'.dirtyCount ≤ qEpochWhp n_max)
    (hhdrs : s'.mem (base + hdrMode) = 1 ∧
      s'.mem (base + hdrPoolFreeTop) = fs'.poolFreeTop ∧
      s'.mem (base + hdrCurEp) = fs'.curEp ∧
      s'.mem (base + hdrEpochClock) = fs'.epochClock ∧
      s'.mem (base + hdrRebStage) = fs'.rebStage ∧
      s'.mem (base + hdrStageCursor) = fs'.stageCursor ∧
      s'.mem (base + hdrDirtyCount) = fs'.dirtyCount ∧
      s'.mem (base + hdrDirtyIdx) = fs'.dirtyIdx ∧
      s'.mem (base + hdrRebCandSalt) = fs'.rebCandSalt ∧
      s'.mem (base + hdrRebScanCursor) = fs'.rebScanCursor ∧
      s'.mem (base + hdrRebInsCount) = fs'.rebInsCount ∧
      s'.mem (base + hdrRebCollision) = fs'.rebCollision)
    (hqv : ∀ i < n_max,
      readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s'.mem i = fs'.quotArr i ∧
      readPacked (base + offValWhp c U w n_max) (valBits V) w s'.mem i = fs'.valArr i)
    (hloc : ∀ b < numBucketsWhp n_max, ∀ loc < totalLocalCoordsWhp n_max,
      readPacked (base + offLocState c U V w n_max) 2 w s'.mem
        (b * totalLocalCoordsWhp n_max + loc) = fs'.locState b loc)
    (hbmeta : ∀ b < numBucketsWhp n_max,
      let bm := offBktMeta c U V w n_max
      let g := globalPtrBits n_max
      readPacked (base + bm) g w s'.mem (16 * b + 0) = fs'.bktCount b ∧
      readPacked (base + bm) g w s'.mem (16 * b + 1) = fs'.bktSalt b ∧
      readPacked (base + bm) g w s'.mem (16 * b + 2) = fs'.liveRole b ∧
      readPacked (base + bm) g w s'.mem (16 * b + 3) = fs'.liveInsCount b ∧
      readPacked (base + bm) g w s'.mem (16 * b + 4) = fs'.overmarsRole b ∧
      readPacked (base + bm) g w s'.mem (16 * b + 5) = fs'.overmarsActive b ∧
      readPacked (base + bm) g w s'.mem (16 * b + 6) = fs'.overmarsCursor b ∧
      readPacked (base + bm) g w s'.mem (16 * b + 7) = fs'.overmarsInsCount b ∧
      readPacked (base + bm) g w s'.mem (16 * b + 8) = fs'.rebDoneFlag b ∧
      readPacked (base + bm) g w s'.mem (16 * b + 9) = fs'.rebQueued b)
    (hbptr : ∀ b < numBucketsWhp n_max, ∀ k < capBackWhp n_max,
      readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s'.mem
        (b * capBackWhp n_max + k) = fs'.backPtr b k)
    (hpool : ∀ j < poolSizeWhp n_max,
      readPacked (base + offPoolFreeStack c U V w n_max) (globalPtrBits n_max) w s'.mem j =
        fs'.poolFreeStack j ∧
      readPacked (base + offPoolOwner c U V w n_max) (globalPtrBits n_max) w s'.mem j =
        fs'.poolOwner j)
    (hdirty : ∀ j < fs'.dirtyCount,
      readPacked (base + offTrieItems0 c U V w n_max) (globalPtrBits n_max) w s'.mem
        (3 * qEpochWhp n_max + j) = fs'.dirtyBuckets j) :
    FastStateStep base c U V w n_max θ fs' s s' := by
  have hch := largeOffsetChain c U V w n_max
  have hout : ∀ a, (a < base ∨ base + largeSpaceWhp c U V w n_max ≤ a) → s'.mem a = s.mem a := by
    intro a ha
    rcases ha with hlt | hge
    · exact hfence a (Or.inl hlt)
    · exact hfence a (Or.inr (Or.inr (Or.inr (by omega))))
  have hseed' : SeedWhpMemRep base c U w n_max θ s'.mem :=
    hseed.congr_hash hw fun a ha1 ha2 =>
      (hfence a (Or.inr (Or.inl ⟨by dsimp [offHashBkt] at ha1; omega, ha2⟩))).symm
  have hslices0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbuf0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbuf1 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbuf_c : ∀ ep, ep = 0 ∨ ep = 1 →
      BufTrieMemRep base c U V w n_max ep (fs.buf ep) s.mem →
      BufTrieMemRep base c U V w n_max ep (fs'.buf ep) s'.mem := fun ep hep htr => by
    rw [hbuf_eq]
    exact bufTrieMemRep_congr_nonBuf hw hep
      (fun h h12 h16 => hfence (base + h) (Or.inr (Or.inl ⟨by omega, by omega⟩)))
      (fun a ha1 ha2 => hfence a (Or.inr (Or.inr (Or.inl ⟨by omega, ha2⟩))))
      hit0 (fun a ha1 _ => hfence a (Or.inr (Or.inr (Or.inr ha1)))) htr
  rcases hhdrs with ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11⟩
  refine ⟨hfr, hseed', ⟨hdc_le, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11,
    hqv, hloc, hbmeta, hbptr, hpool, fun sIdx hsIdx => ?_,
    hbuf_c 0 (Or.inl rfl) hbuf0, hbuf_c 1 (Or.inr rfl) hbuf1, hdirty⟩, hout⟩
  rw [hsl_eq]
  have hrole_lt : sIdx % 3 < 3 := Nat.mod_lt _ (by decide)
  exact bTreeSliceMemRep_congr hw hsIdx
    ⟨hbm_sl _ (by omega) (by omega), hbm_sl _ (by omega) (by omega)⟩
    (fun a ha1 ha2 => hfence a (Or.inr (Or.inr (Or.inl ⟨ha1, by omega⟩))))
    (hslices0 sIdx hsIdx)

/-- Frame helper for a single `writePacked` inside `[offQuotWhp, offBtMeta)` disjoint from
`offBktMeta`. -/
theorem fastStep_pureArray {base c U V w n_max offW NW kW idxW valW : ℕ}
    {θ : SeedWhp c U n_max} {fs fs' : FastState} {s : Memory.State}
    (hw : 0 < w) (hidxW : idxW < NW)
    (hseg_lo : offQuotWhp c w n_max ≤ offW)
    (hseg_hi : offW + packedWords NW kW w ≤ offBtMeta c U V w n_max)
    (hbm_disj : offW + packedWords NW kW w ≤ offBktMeta c U V w n_max ∨
      offFbStart c U V w n_max ≤ offW)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hunch : fs'.slices = fs.slices ∧ fs'.buf = fs.buf ∧ fs'.dirtyCount = fs.dirtyCount ∧
      fs'.poolFreeTop = fs.poolFreeTop ∧ fs'.curEp = fs.curEp ∧ fs'.epochClock = fs.epochClock ∧
      fs'.rebStage = fs.rebStage ∧ fs'.stageCursor = fs.stageCursor ∧
      fs'.dirtyIdx = fs.dirtyIdx ∧ fs'.rebCandSalt = fs.rebCandSalt ∧
      fs'.rebScanCursor = fs.rebScanCursor ∧ fs'.rebInsCount = fs.rebInsCount ∧
      fs'.rebCollision = fs.rebCollision ∧ fs'.bktCount = fs.bktCount ∧
      fs'.bktSalt = fs.bktSalt ∧ fs'.liveRole = fs.liveRole ∧
      fs'.liveInsCount = fs.liveInsCount ∧ fs'.overmarsRole = fs.overmarsRole ∧
      fs'.overmarsActive = fs.overmarsActive ∧ fs'.overmarsCursor = fs.overmarsCursor ∧
      fs'.overmarsInsCount = fs.overmarsInsCount ∧ fs'.rebDoneFlag = fs.rebDoneFlag ∧
      fs'.rebQueued = fs.rebQueued ∧ fs'.dirtyBuckets = fs.dirtyBuckets)
    (hqv : ∀ i < n_max,
      let m' := writePacked (base + offW) kW w s.mem idxW valW
      readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w m' i = fs'.quotArr i ∧
      readPacked (base + offValWhp c U w n_max) (valBits V) w m' i = fs'.valArr i)
    (hloc : ∀ b < numBucketsWhp n_max, ∀ loc < totalLocalCoordsWhp n_max,
      let m' := writePacked (base + offW) kW w s.mem idxW valW
      readPacked (base + offLocState c U V w n_max) 2 w m'
        (b * totalLocalCoordsWhp n_max + loc) = fs'.locState b loc)
    (hbptr : ∀ b < numBucketsWhp n_max, ∀ k < capBackWhp n_max,
      let m' := writePacked (base + offW) kW w s.mem idxW valW
      readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w m'
        (b * capBackWhp n_max + k) = fs'.backPtr b k)
    (hpool : ∀ j < poolSizeWhp n_max,
      let m' := writePacked (base + offW) kW w s.mem idxW valW
      readPacked (base + offPoolFreeStack c U V w n_max) (globalPtrBits n_max) w m' j =
        fs'.poolFreeStack j ∧
      readPacked (base + offPoolOwner c U V w n_max) (globalPtrBits n_max) w m' j =
        fs'.poolOwner j) :
    FastStateStep base c U V w n_max θ fs' s
      { mem := writePacked (base + offW) kW w s.mem idxW valW, frontier := s.frontier } := by
  have hch := largeOffsetChain c U V w n_max
  set m' := writePacked (base + offW) kW w s.mem idxW valW
  have houtW : ∀ a, (a < base + offW ∨ base + offW + packedWords NW kW w ≤ a) → m' a = s.mem a :=
    fun a ha => writePacked_outside hw _ hidxW _ (by cases ha <;> omega)
  have hbm_all : ∀ idx < 16 * numBucketsWhp n_max,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w m' idx =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx :=
    fun idx hidx => readPacked_congr hw (hidx := hidx) fun a ⟨ha1, ha2⟩ =>
      houtW a (by rcases hbm_disj with h1 | h2 <;> omega)
  have hhdr_eq : ∀ h < 16, m' (base + h) = s.mem (base + h) :=
    fun h _ => houtW (base + h) (Or.inl (by omega))
  obtain ⟨hdc_le0, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    -, -, hbmeta0, -, -, -, -, -, hdirty0⟩ := id hrep
  rcases hunch with ⟨hsl_e, hbf_e, hdc_e, hpft_e, hce_e, hec_e, hrs_e, hsc_e, hdi_e, hrcs_e,
    hrsc_e, hric_e, hrcl_e, hbc_e, hbs_e, hlr_e, hli_e, hor_e, hoa_e, hoc_e, hoi_e, hrd_e,
    hrq_e, hdb_e⟩
  exact fastStep_nonSliceNonBuf hw rfl hseed hrep hsl_e hbf_e
    (fun a ha => houtW a (by rcases ha with h1 | ⟨_, h2⟩ | ⟨h3, _⟩ | h4 <;> omega))
    (fun idx hidx _ => hbm_all idx hidx)
    (fun id hid => readPacked_congr hw (hidx := show id < 6 * qEpochWhp n_max + 6 by omega)
      fun a ⟨ha1, _⟩ => houtW a (Or.inr (by omega)))
    (hdc_e ▸ hdc_le0)
    (by simp (disch := decide) only [hhdr_eq, hpft_e, hce_e, hec_e, hrs_e, hsc_e, hdc_e, hdi_e,
      hrcs_e, hrsc_e, hric_e, hrcl_e, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10,
      hm11, and_self])
    hqv hloc
    (fun b hb => by
      rw [hbc_e, hbs_e, hlr_e, hli_e, hor_e, hoa_e, hoc_e, hoi_e, hrd_e, hrq_e]
      exact bktMeta_congr_of_readPacked (fun k hk => hbm_all _ (by omega)) (hbmeta0 b hb))
    hbptr hpool
    (fun j hj => by
      rw [hdc_e] at hj; rw [hdb_e]
      exact (readPacked_congr hw (hidx :=
        show 3 * qEpochWhp n_max + j < 6 * qEpochWhp n_max + 6 by omega)
        fun a ⟨ha1, _⟩ => houtW a (Or.inr (by omega))).trans (hdirty0 j hj))

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
