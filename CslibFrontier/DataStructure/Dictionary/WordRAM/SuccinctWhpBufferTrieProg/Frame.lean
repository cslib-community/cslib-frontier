/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Rt
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Helpers

/-!
# External Word & Opposite-Buffer Preservation Laws for `BufEpFrame`

Establishes `BufEpFrame.mem_outside` and `BufEpFrame.other_bufTrieMemRep`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.BufEpFrame.mem_outside`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.BufEpFrame.other_bufTrieMemRep`
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Finset
open scoped BigOperators
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

attribute [local simp] clientResult_pure_whp clientState_pure_whp

/-- `BufEpFrame` preserves every word before `offTrieChild0` (except `hdrNA(ep)` and `hdrIA(ep)`)
and every word at or above `base + largeSpaceWhp`. -/
theorem BufEpFrame.mem_outside {base c U V w n_max ep a : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hep : ep = 0 ∨ ep = 1) (hf : BufEpFrame base c U V w n_max ep m₁ m₂)
    (ha : (a < base + offTrieChild0 c U V w n_max ∧
            a ≠ base + brHdrNA (mkBufRt c U V w n_max base ep) ∧
            a ≠ base + brHdrIA (mkBufRt c U V w n_max base ep)) ∨
          base + largeSpaceWhp c U V w n_max ≤ a) :
    m₂ a = m₁ a := by
  have hseg := rt_seg_le c U V w n_max base ep hep
  have hch := largeOffsetChain c U V w n_max
  rcases hep with rfl | rfl <;>
    (dsimp only [mkBufRt, brHdrNA, brHdrIA, brOffChild, brOffMeta, brOffItems,
       hdrBuf0NodeAlloc, hdrBuf0ItemAlloc, hdrBuf1NodeAlloc, hdrBuf1ItemAlloc] at ha hseg ⊢
     simp only [↓reduceIte, Nat.one_ne_zero] at ha hseg
     exact hf.1 a
       (by dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc, hdrBuf1NodeAlloc]; omega)
       (by dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc, hdrBuf1ItemAlloc]; omega)
       (by dsimp [mkBufRt, brOffChild]; omega)
       (by dsimp [mkBufRt, brOffMeta]; omega)
       (by dsimp [mkBufRt, brOffItems]; omega))

/-- `BufEpFrame` on `ep` preserves `BufTrieMemRep` on the opposite buffer `1 - ep`. -/
theorem BufEpFrame.other_bufTrieMemRep {base c U V w n_max ep : ℕ} {tr : BufTrie}
    {m₁ m₂ : ℕ → ℕ} (hw : 0 < w) (hep : ep = 0 ∨ ep = 1)
    (hf : BufEpFrame base c U V w n_max ep m₁ m₂)
    (hrep : BufTrieMemRep base c U V w n_max (1 - ep) tr m₁) :
    BufTrieMemRep base c U V w n_max (1 - ep) tr m₂ := by
  have hoff := largeOffsetChain c U V w n_max
  -- The frame on `ep` preserves the three trie arrays of the opposite buffer `1 - ep` ...
  have hmem : ∀ a, let rt := mkBufRt c U V w n_max base (1 - ep)
      (base + brOffChild rt ≤ a ∧ a < base + brOffChild rt +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w) ∨
      (base + brOffMeta rt ≤ a ∧ a < base + brOffMeta rt +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w) ∨
      (base + brOffItems rt ≤ a ∧ a < base + brOffItems rt +
        packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w) → m₂ a = m₁ a := by
    intro a
    dsimp only
    intro ha
    rcases hep with rfl | rfl <;> dsimp [mkBufRt, brOffChild, brOffMeta, brOffItems] at ha <;>
    exact hf.1 a
      (by dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc, hdrBuf1NodeAlloc]; omega)
      (by dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc, hdrBuf1ItemAlloc]; omega)
      (by dsimp [mkBufRt, brOffChild]; omega)
      (by dsimp [mkBufRt, brOffMeta]; omega)
      (by dsimp [mkBufRt, brOffItems]; omega)
  -- ... and its two allocation headers.
  have hhdr : ∀ h, h = (if 1 - ep = 0 then hdrBuf0NodeAlloc else hdrBuf1NodeAlloc) ∨
      h = (if 1 - ep = 0 then hdrBuf0ItemAlloc else hdrBuf1ItemAlloc) →
      m₂ (base + h) = m₁ (base + h) := by
    intro h hh
    refine hf.mem_outside hep (Or.inl ⟨?_, ?_, ?_⟩) <;>
    rcases hep with rfl | rfl <;>
    dsimp [mkBufRt, brHdrNA, brHdrIA, hdrBuf0NodeAlloc, hdrBuf1NodeAlloc, hdrBuf0ItemAlloc,
      hdrBuf1ItemAlloc] at hh ⊢ <;> omega
  dsimp only [BufTrieMemRep] at hrep ⊢
  obtain ⟨hna, hia, hhdr_na, hhdr_ia, hch, hpar, hleaf, hitems⟩ := hrep
  refine ⟨hna, hia, (hhdr _ (Or.inl rfl)).trans hhdr_na, (hhdr _ (Or.inr rfl)).trans hhdr_ia,
    fun u hu ch hch_lt => ?_, fun u hu1 hu => ?_, fun u hu => ?_, fun id hid => ?_⟩
  · have hidx : u * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max :=
      mul_add_lt_mul_bound hu hch_lt
    exact (readPacked_congr hw (hidx := hidx) fun a ⟨ha1, ha2⟩ =>
      hmem a (Or.inl ⟨ha1, ha2⟩)).trans (hch u hu ch hch_lt)
  · exact ⟨(readPacked_congr hw (hidx := show 4 * u + 0 < 6 * maxTrieNodesWhp c n_max by omega)
        fun a ⟨ha1, ha2⟩ => hmem a (Or.inr (Or.inl ⟨ha1, ha2⟩))).trans (hpar u hu1 hu).1,
      (readPacked_congr hw (hidx := show 4 * u + 1 < 6 * maxTrieNodesWhp c n_max by omega)
        fun a ⟨ha1, ha2⟩ => hmem a (Or.inr (Or.inl ⟨ha1, ha2⟩))).trans (hpar u hu1 hu).2⟩
  · exact ⟨(readPacked_congr hw (hidx := show 4 * u + 2 < 6 * maxTrieNodesWhp c n_max by omega)
        fun a ⟨ha1, ha2⟩ => hmem a (Or.inr (Or.inl ⟨ha1, ha2⟩))).trans (hleaf u hu).1,
      fun hnz =>
        (readPacked_congr hw (hidx := show 4 * u + 3 < 6 * maxTrieNodesWhp c n_max by omega)
          fun a ⟨ha1, ha2⟩ => hmem a (Or.inr (Or.inl ⟨ha1, ha2⟩))).trans ((hleaf u hu).2 hnz)⟩
  · exact ⟨(readPacked_congr hw (hidx := show id < 6 * qEpochWhp n_max + 6 by omega)
        fun a ⟨ha1, ha2⟩ => hmem a (Or.inr (Or.inr ⟨ha1, ha2⟩))).trans (hitems id hid).1,
      (readPacked_congr hw (hidx := show qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega)
        fun a ⟨ha1, ha2⟩ => hmem a (Or.inr (Or.inr ⟨ha1, ha2⟩))).trans (hitems id hid).2.1,
      (readPacked_congr hw (hidx :=
        show 2 * qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega)
        fun a ⟨ha1, ha2⟩ => hmem a (Or.inr (Or.inr ⟨ha1, ha2⟩))).trans (hitems id hid).2.2⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
