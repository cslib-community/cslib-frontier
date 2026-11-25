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
  dsimp only [BufTrieMemRep] at hrep ⊢
  obtain ⟨hna, hia, hhdr_na, hhdr_ia, hch, hpar, hleaf, hitems⟩ := hrep
  rcases hep with rfl | rfl
  · simp only [Nat.sub_zero, Nat.one_ne_zero, ↓reduceIte] at hhdr_na hhdr_ia hch hpar hleaf hitems ⊢
    have hmem_c1 : ∀ a, base + offTrieChild1 c U V w n_max ≤ a →
        a < base + offTrieChild1 c U V w n_max +
          packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w → m₂ a = m₁ a :=
      fun a h1 h2 => hf.1 a
        (by dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc]; omega)
        (by dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc]; omega)
        (Or.inr (by dsimp [mkBufRt, brOffChild]; omega))
        (Or.inl (by dsimp [mkBufRt, brOffMeta]; omega))
        (Or.inl (by dsimp [mkBufRt, brOffItems]; omega))
    have hmem_m1 : ∀ a, base + offTrieMeta1 c U V w n_max ≤ a →
        a < base + offTrieMeta1 c U V w n_max +
          packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w → m₂ a = m₁ a :=
      fun a h1 h2 => hf.1 a
        (by dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc]; omega)
        (by dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc]; omega)
        (Or.inr (by dsimp [mkBufRt, brOffChild]; omega))
        (Or.inr (by dsimp [mkBufRt, brOffMeta]; omega))
        (Or.inl (by dsimp [mkBufRt, brOffItems]; omega))
    have hmem_i1 : ∀ a, base + offTrieItems1 c U V w n_max ≤ a →
        a < base + offTrieItems1 c U V w n_max +
          packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w → m₂ a = m₁ a :=
      fun a h1 h2 => hf.1 a
        (by dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc]; omega)
        (by dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc]; omega)
        (Or.inr (by dsimp [mkBufRt, brOffChild]; omega))
        (Or.inr (by dsimp [mkBufRt, brOffMeta]; omega))
        (Or.inr (by dsimp [mkBufRt, brOffItems]; omega))
    refine ⟨hna, hia,
      (hf.mem_outside (Or.inl rfl) (Or.inl ⟨by dsimp [hdrBuf1NodeAlloc]; omega,
        by dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc, hdrBuf1NodeAlloc]; omega,
        by dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc, hdrBuf1NodeAlloc]; omega⟩)).trans hhdr_na,
      (hf.mem_outside (Or.inl rfl) (Or.inl ⟨by dsimp [hdrBuf1ItemAlloc]; omega,
        by dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc, hdrBuf1ItemAlloc]; omega,
        by dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc, hdrBuf1ItemAlloc]; omega⟩)).trans hhdr_ia,
      fun u hu ch hch_lt => ?_, fun u hu1 hu => ?_, fun u hu => ?_, fun id hid => ?_⟩
    · have hidx : u * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max := by
        unfold trieChildEntriesWhp
        calc u * 2 ^ bCharWhp n_max + ch < u * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max :=
              Nat.add_lt_add_left hch_lt _
          _ = (u + 1) * 2 ^ bCharWhp n_max := by ring
          _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hu
      exact (readPacked_congr hw (hidx := hidx) (fun a ⟨ha1,
        ha2⟩ => hmem_c1 a ha1 ha2)).trans (hch u hu ch hch_lt)
    · exact ⟨(readPacked_congr hw (hidx := show 4 * u + 0 < 6 * maxTrieNodesWhp c n_max by omega)
          (fun a ⟨ha1, ha2⟩ => hmem_m1 a ha1 ha2)).trans (hpar u hu1 hu).1,
        (readPacked_congr hw (hidx := show 4 * u + 1 < 6 * maxTrieNodesWhp c n_max by omega)
          (fun a ⟨ha1, ha2⟩ => hmem_m1 a ha1 ha2)).trans (hpar u hu1 hu).2⟩
    · exact ⟨(readPacked_congr hw (hidx := show 4 * u + 2 < 6 * maxTrieNodesWhp c n_max by omega)
          (fun a ⟨ha1, ha2⟩ => hmem_m1 a ha1 ha2)).trans (hleaf u hu).1,
        fun hnz =>
          (readPacked_congr hw (hidx := show 4 * u + 3 < 6 * maxTrieNodesWhp c n_max by omega)
          (fun a ⟨ha1, ha2⟩ => hmem_m1 a ha1 ha2)).trans ((hleaf u hu).2 hnz)⟩
    · exact ⟨(readPacked_congr hw (hidx := show id < 6 * qEpochWhp n_max + 6 by omega) (fun a ⟨ha1,
        ha2⟩ => hmem_i1 a ha1 ha2)).trans
          (hitems id hid).1,
        (readPacked_congr hw (hidx := show qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega)
          (fun a ⟨ha1, ha2⟩ => hmem_i1 a ha1 ha2)).trans (hitems id hid).2.1,
        (readPacked_congr hw (hidx :=
          show 2 * qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega)
          (fun a ⟨ha1, ha2⟩ => hmem_i1 a ha1 ha2)).trans (hitems id hid).2.2⟩
  · simp only [Nat.sub_self, ↓reduceIte] at hhdr_na hhdr_ia hch hpar hleaf hitems ⊢
    have hmem_c0 : ∀ a, base + offTrieChild0 c U V w n_max ≤ a →
        a < base + offTrieChild0 c U V w n_max +
          packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w → m₂ a = m₁ a :=
      fun a h1 h2 => hf.1 a
        (by dsimp [mkBufRt, brHdrNA, hdrBuf1NodeAlloc]; omega)
        (by dsimp [mkBufRt, brHdrIA, hdrBuf1ItemAlloc]; omega)
        (Or.inl (by dsimp [mkBufRt, brOffChild]; omega))
        (Or.inl (by dsimp [mkBufRt, brOffMeta]; omega))
        (Or.inl (by dsimp [mkBufRt, brOffItems]; omega))
    have hmem_m0 : ∀ a, base + offTrieMeta0 c U V w n_max ≤ a →
        a < base + offTrieMeta0 c U V w n_max +
          packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w → m₂ a = m₁ a :=
      fun a h1 h2 => hf.1 a
        (by dsimp [mkBufRt, brHdrNA, hdrBuf1NodeAlloc]; omega)
        (by dsimp [mkBufRt, brHdrIA, hdrBuf1ItemAlloc]; omega)
        (Or.inr (by dsimp [mkBufRt, brOffChild]; omega))
        (Or.inl (by dsimp [mkBufRt, brOffMeta]; omega))
        (Or.inl (by dsimp [mkBufRt, brOffItems]; omega))
    have hmem_i0 : ∀ a, base + offTrieItems0 c U V w n_max ≤ a →
        a < base + offTrieItems0 c U V w n_max +
          packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w → m₂ a = m₁ a :=
      fun a h1 h2 => hf.1 a
        (by dsimp [mkBufRt, brHdrNA, hdrBuf1NodeAlloc]; omega)
        (by dsimp [mkBufRt, brHdrIA, hdrBuf1ItemAlloc]; omega)
        (Or.inr (by dsimp [mkBufRt, brOffChild]; omega))
        (Or.inr (by dsimp [mkBufRt, brOffMeta]; omega))
        (Or.inl (by dsimp [mkBufRt, brOffItems]; omega))
    refine ⟨hna, hia,
      (hf.mem_outside (Or.inr rfl) (Or.inl ⟨by dsimp [hdrBuf0NodeAlloc]; omega,
        by dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc, hdrBuf1NodeAlloc]; omega,
        by dsimp [mkBufRt, brHdrIA, hdrBuf0NodeAlloc, hdrBuf1ItemAlloc]; omega⟩)).trans hhdr_na,
      (hf.mem_outside (Or.inr rfl) (Or.inl ⟨by dsimp [hdrBuf0ItemAlloc]; omega,
        by dsimp [mkBufRt, brHdrNA, hdrBuf0ItemAlloc, hdrBuf1NodeAlloc]; omega,
        by dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc, hdrBuf1ItemAlloc]; omega⟩)).trans hhdr_ia,
      fun u hu ch hch_lt => ?_, fun u hu1 hu => ?_, fun u hu => ?_, fun id hid => ?_⟩
    · have hidx : u * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max := by
        unfold trieChildEntriesWhp
        calc u * 2 ^ bCharWhp n_max + ch < u * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max :=
              Nat.add_lt_add_left hch_lt _
          _ = (u + 1) * 2 ^ bCharWhp n_max := by ring
          _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hu
      exact (readPacked_congr hw (hidx := hidx) (fun a ⟨ha1,
        ha2⟩ => hmem_c0 a ha1 ha2)).trans (hch u hu ch hch_lt)
    · exact ⟨(readPacked_congr hw (hidx := show 4 * u + 0 < 6 * maxTrieNodesWhp c n_max by omega)
          (fun a ⟨ha1, ha2⟩ => hmem_m0 a ha1 ha2)).trans (hpar u hu1 hu).1,
        (readPacked_congr hw (hidx := show 4 * u + 1 < 6 * maxTrieNodesWhp c n_max by omega)
          (fun a ⟨ha1, ha2⟩ => hmem_m0 a ha1 ha2)).trans (hpar u hu1 hu).2⟩
    · exact ⟨(readPacked_congr hw (hidx := show 4 * u + 2 < 6 * maxTrieNodesWhp c n_max by omega)
          (fun a ⟨ha1, ha2⟩ => hmem_m0 a ha1 ha2)).trans (hleaf u hu).1,
        fun hnz =>
          (readPacked_congr hw (hidx := show 4 * u + 3 < 6 * maxTrieNodesWhp c n_max by omega)
          (fun a ⟨ha1, ha2⟩ => hmem_m0 a ha1 ha2)).trans ((hleaf u hu).2 hnz)⟩
    · exact ⟨(readPacked_congr hw (hidx := show id < 6 * qEpochWhp n_max + 6 by omega) (fun a ⟨ha1,
        ha2⟩ => hmem_i0 a ha1 ha2)).trans
          (hitems id hid).1,
        (readPacked_congr hw (hidx := show qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega)
          (fun a ⟨ha1, ha2⟩ => hmem_i0 a ha1 ha2)).trans (hitems id hid).2.1,
        (readPacked_congr hw (hidx :=
          show 2 * qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega)
          (fun a ⟨ha1, ha2⟩ => hmem_i0 a ha1 ha2)).trans (hitems id hid).2.2⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
