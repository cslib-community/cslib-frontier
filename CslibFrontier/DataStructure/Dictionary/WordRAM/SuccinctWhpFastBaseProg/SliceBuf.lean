/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.Frame
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.Internal

/-!
# Fast-Mode SWAR B+-Tree Slice and Epoch-Buffer `FastStateStep` Wrappers

This module lifts the certified SWAR B+-tree slice operations (`SuccinctWhpBTreeProg`) and
character-trie epoch buffer operations (`SuccinctWhpBufferTrieProg`) into `FastStateStep`
transitions on `FastMemRep`:

1. `fastStep_of_bufEpFrame`, `bufDeleteGenProg_fastStep`, `bufInsertGenProg_fastStep`.
2. `resetBTreeSliceGenProg_fastStep`, `btreeDeleteGenProg_fastStep`,
   `btreeUpdateGenProg_fastStep`, `btreeInsertGenProg_fastStep`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastStep_of_bufEpFrame`,
  `resetBTreeSliceGenProg_fastStep`, `btreeDeleteGenProg_fastStep`,
  `btreeUpdateGenProg_fastStep`, `btreeInsertGenProg_fastStep`, `bufDeleteGenProg_fastStep`,
  `bufInsertGenProg_fastStep`.
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

/-- Lift any `BufEpFrame` + `BufTrieMemRep` update on `ep ∈ {0, 1}` into `FastStateStep`. -/
theorem fastStep_of_bufEpFrame {base c U V w n_max ep : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {tr' : BufTrie} {s s' : Memory.State}
    (hw : 0 < w) (hep : ep = 0 ∨ ep = 1)
    (hfr : s'.frontier = s.frontier)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (htr' : BufTrieMemRep base c U V w n_max ep tr' s'.mem)
    (hbfr : BufEpFrame base c U V w n_max ep s.mem s'.mem) :
    FastStateStep base c U V w n_max θ
      { fs with buf := Function.update fs.buf ep tr' } s s' := by
  have hch := largeOffsetChain c U V w n_max
  have hpre_tc0 : ∀ a < base + offTrieChild0 c U V w n_max,
      (∀ h, 12 ≤ h → h < 16 → a ≠ base + h) → s'.mem a = s.mem a := by
    intro a ha hne
    refine hbfr.mem_outside hep (Or.inl ⟨ha, ?_, ?_⟩) <;>
      (rcases hep with rfl | rfl <;>
        (dsimp only [mkBufRt, brHdrNA, brHdrIA, hdrBuf0NodeAlloc, hdrBuf0ItemAlloc,
          hdrBuf1NodeAlloc, hdrBuf1ItemAlloc];
         exact hne _ (by decide) (by decide)))
  have hout : ∀ a, (a < base ∨ base + largeSpaceWhp c U V w n_max ≤ a) → s'.mem a = s.mem a := by
    intro a ha
    rcases ha with hlt | hge
    · exact hpre_tc0 a (by omega) (fun h _ _ => by omega)
    · exact hbfr.mem_outside hep (Or.inr hge)
  have hseed' : SeedWhpMemRep base c U w n_max θ s'.mem :=
    hseed.congr_hash hw fun a ha1 ha2 =>
      (hpre_tc0 a (by omega) (fun h _ _ => by dsimp [offHashBkt] at ha1; omega)).symm
  have hhdr : ∀ h < 12, s'.mem (base + h) = s.mem (base + h) :=
    fun h hh => hpre_tc0 (base + h) (by omega) (fun h' h12 _ => by omega)
  have hrp_pre : ∀ {off N k idx}, idx < N →
      off + packedWords N k w ≤ offTrieChild0 c U V w n_max → 32 ≤ off →
      readPacked (base + off) k w s'.mem idx = readPacked (base + off) k w s.mem idx :=
    fun hidx hhi hlo => readPacked_congr hw (hidx := hidx) fun a ⟨ha1, ha2⟩ =>
      hpre_tc0 a (by omega) (fun h _ _ => by omega)
  dsimp only [FastMemRep] at hrep ⊢
  rcases hrep with ⟨hdc_le, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    hqv, hloc, hbmeta, hbptr, hpool, hslices, hbuf0, hbuf1, hdirty⟩
  refine ⟨hfr, hseed', ⟨hdc_le,
    (hhdr 0 (by decide)).trans hm0,
    (hhdr 1 (by decide)).trans hm1,
    (hhdr 2 (by decide)).trans hm2,
    (hhdr 3 (by decide)).trans hm3,
    (hhdr 4 (by decide)).trans hm4,
    (hhdr 5 (by decide)).trans hm5,
    (hhdr 6 (by decide)).trans hm6,
    (hhdr 7 (by decide)).trans hm7,
    (hhdr 8 (by decide)).trans hm8,
    (hhdr 9 (by decide)).trans hm9,
    (hhdr 10 (by decide)).trans hm10,
    (hhdr 11 (by decide)).trans hm11,
    fun i hi => ⟨(hrp_pre hi (by omega) (by omega)).trans (hqv i hi).1,
      (hrp_pre hi (by omega) (by omega)).trans (hqv i hi).2⟩,
    fun b hb loc hloc_lt => (hrp_pre (mul_add_lt_mul_bound hb hloc_lt) (by omega) (by omega)).trans
      (hloc b hb loc hloc_lt),
    fun b hb => bktMeta_congr_of_readPacked
      (fun k hk => hrp_pre (show 16 * b + k < 16 * numBucketsWhp n_max by omega)
        (by omega) (by omega))
      (hbmeta b hb),
    fun b hb k hk => (hrp_pre (mul_add_lt_mul_bound hb hk) (by omega) (by omega)).trans
      (hbptr b hb k hk),
    fun j hj => ⟨(hrp_pre hj (by omega) (by omega)).trans (hpool j hj).1,
      (hrp_pre hj (by omega) (by omega)).trans (hpool j hj).2⟩,
    fun sIdx hsIdx => bTreeSliceMemRep_congr hw hsIdx
      ⟨hrp_pre (show 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3) < 16 * numBucketsWhp n_max by omega)
        (by omega) (by omega),
       hrp_pre (show 16 * (sIdx / 3) + 11 + 2 * (sIdx % 3) < 16 * numBucketsWhp n_max by omega)
        (by omega) (by omega)⟩
      (fun a ha1 ha2 => hpre_tc0 a ha2 (fun _ _ _ => by omega)) (hslices sIdx hsIdx),
    ?_, ?_,
    fun j hj => (hbfr.2 (3 * qEpochWhp n_max + j) (by omega)
      (by dsimp only at hj; omega)).trans (hdirty j hj)⟩, hout⟩
  · rcases hep with rfl | rfl
    · simpa only [Function.update_self] using htr'
    · simpa only [Function.update_of_ne (by decide : (0 : ℕ) ≠ 1)] using
        hbfr.other_bufTrieMemRep hw (Or.inr rfl) hbuf0
  · rcases hep with rfl | rfl
    · simpa only [Function.update_of_ne (by decide : (1 : ℕ) ≠ 0)] using
        hbfr.other_bufTrieMemRep hw (Or.inl rfl) hbuf1
    · simpa only [Function.update_self] using htr'

/-- Lift any single-slice `BTreeSliceMemRep` update (touching at most slice `sIdx`'s `(alloc, root)`
in `offBktMeta` and `[offBtMeta, offTrieChild0)`) into `FastStateStep`. -/
private theorem fastStep_of_sliceUpdate {base c U V w n_max sIdx : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {sl' : BTreeSlice} {s s' : Memory.State}
    (hw : 0 < w) (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hfr : s'.frontier = s.frontier)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hsl' : BTreeSliceMemRep base c U V w n_max sIdx sl' s'.mem)
    (hoth : ∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl₂,
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s'.mem)
    (hbm : ∀ idx < 16 * numBucketsWhp n_max,
      idx ≠ 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3) →
      idx ≠ 16 * (sIdx / 3) + 11 + 2 * (sIdx % 3) →
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx)
    (hout_seg : ∀ a, (a < base + offBktMeta c U V w n_max ∨
        (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
        base + offTrieChild0 c U V w n_max ≤ a) →
      s'.mem a = s.mem a) :
    FastStateStep base c U V w n_max θ
      { fs with slices := Function.update fs.slices sIdx sl' } s s' := by
  have hch := largeOffsetChain c U V w n_max
  have hout : ∀ a, (a < base ∨ base + largeSpaceWhp c U V w n_max ≤ a) → s'.mem a = s.mem a := by
    intro a ha
    rcases ha with hlt | hge
    · exact hout_seg a (Or.inl (by omega))
    · exact hout_seg a (Or.inr (Or.inr (by omega)))
  have hseed' : SeedWhpMemRep base c U w n_max θ s'.mem :=
    hseed.congr_hash hw fun a _ ha2 => (hout_seg a (Or.inl (by omega))).symm
  have hhdr : ∀ h < 16, s'.mem (base + h) = s.mem (base + h) :=
    fun h _ => hout_seg (base + h) (Or.inl (by omega))
  dsimp only [FastMemRep] at hrep ⊢
  rcases hrep with ⟨hdc_le, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    hqv, hloc, hbmeta, hbptr, hpool, hslices, hbuf0, hbuf1, hdirty⟩
  have hbuf_c : ∀ ep, ep = 0 ∨ ep = 1 → ∀ tr,
      BufTrieMemRep base c U V w n_max ep tr s.mem →
      BufTrieMemRep base c U V w n_max ep tr s'.mem := fun ep hep tr htr =>
    bufTrieMemRep_congr_nonBuf hw hep (fun h _ h16 => hhdr h h16)
      (fun a ha1 _ => hout_seg a (Or.inr (Or.inr ha1)))
      (fun id hid => readPacked_congr hw (hidx := show id < 6 * qEpochWhp n_max + 6 by omega)
        fun a ⟨ha1, _⟩ => hout_seg a (Or.inr (Or.inr (by omega))))
      (fun a ha1 _ => hout_seg a (Or.inr (Or.inr (by omega)))) htr
  refine ⟨hfr, hseed', ⟨hdc_le,
    (hhdr 0 (by decide)).trans hm0,
    (hhdr 1 (by decide)).trans hm1,
    (hhdr 2 (by decide)).trans hm2,
    (hhdr 3 (by decide)).trans hm3,
    (hhdr 4 (by decide)).trans hm4,
    (hhdr 5 (by decide)).trans hm5,
    (hhdr 6 (by decide)).trans hm6,
    (hhdr 7 (by decide)).trans hm7,
    (hhdr 8 (by decide)).trans hm8,
    (hhdr 9 (by decide)).trans hm9,
    (hhdr 10 (by decide)).trans hm10,
    (hhdr 11 (by decide)).trans hm11,
    fun i hi => ⟨(readPacked_congr hw (hidx := hi) fun a ⟨_, ha2⟩ =>
        hout_seg a (Or.inl (by omega))).trans (hqv i hi).1,
      (readPacked_congr hw (hidx := hi) fun a ⟨_, ha2⟩ =>
        hout_seg a (Or.inl (by omega))).trans (hqv i hi).2⟩,
    fun b hb loc hloc_lt =>
      (readPacked_congr hw (hidx := mul_add_lt_mul_bound hb hloc_lt) fun a ⟨_, ha2⟩ =>
        hout_seg a (Or.inl (by omega))).trans (hloc b hb loc hloc_lt),
    fun b hb => bktMeta_congr_of_readPacked
      (fun k hk => hbm (16 * b + k) (by omega) (by omega) (by omega))
      (hbmeta b hb),
    fun b hb k hk =>
      (readPacked_congr hw (hidx := mul_add_lt_mul_bound hb hk) fun a ⟨ha1, ha2⟩ =>
        hout_seg a (Or.inr (Or.inl ⟨by omega, by omega⟩))).trans (hbptr b hb k hk),
    fun j hj => ⟨(readPacked_congr hw (hidx := hj) fun a ⟨ha1, ha2⟩ =>
        hout_seg a (Or.inr (Or.inl ⟨by omega, by omega⟩))).trans (hpool j hj).1,
      (readPacked_congr hw (hidx := hj) fun a ⟨ha1, ha2⟩ =>
        hout_seg a (Or.inr (Or.inl ⟨by omega, by omega⟩))).trans (hpool j hj).2⟩,
    fun sIdx' hsIdx' => ?_,
    hbuf_c 0 (Or.inl rfl) _ hbuf0,
    hbuf_c 1 (Or.inr rfl) _ hbuf1,
    fun j hj => (readPacked_congr hw (hidx :=
      show 3 * qEpochWhp n_max + j < 6 * qEpochWhp n_max + 6 by dsimp only at hj; omega)
      fun a ⟨ha1, _⟩ => hout_seg a (Or.inr (Or.inr (by omega)))).trans (hdirty j hj)⟩, hout⟩
  by_cases heq : sIdx' = sIdx
  · subst heq; simpa only [Function.update_self] using hsl'
  · simpa only [Function.update_of_ne heq] using hoth sIdx' hsIdx' heq _ (hslices sIdx' hsIdx')

/-! ### B+-Tree Slice `FastStateStep` Wrappers -/

private theorem fastStep_of_btreeInPlace {base c U V w n_max sIdx : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {sl' : BTreeSlice} {s s' : Memory.State}
    (hw : 0 < w) (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hfr : s'.frontier = s.frontier)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hsl' : BTreeSliceMemRep base c U V w n_max sIdx sl' s'.mem)
    (hoth : ∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl₂,
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s'.mem)
    (hout : ∀ a, (a < base + offBtMeta c U V w n_max ∨
        base + offTrieChild0 c U V w n_max ≤ a) → s'.mem a = s.mem a) :
    FastStateStep base c U V w n_max θ
      { fs with slices := Function.update fs.slices sIdx sl' } s s' := by
  have hch := largeOffsetChain c U V w n_max
  refine fastStep_of_sliceUpdate hw hsIdx hfr hseed hrep hsl' hoth ?_ ?_
  · intro idx hidx _ _
    exact readPacked_congr hw (hidx := hidx) fun a ⟨_, ha2⟩ => hout a (Or.inl (by omega))
  · intro a ha
    rcases ha with h1 | ⟨_, h2⟩ | h3
    · exact hout a (Or.inl (by omega))
    · exact hout a (Or.inl h2)
    · exact hout a (Or.inr h3)

theorem resetBTreeSliceGenProg_fastStep {c U V w n_max base sIdx : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := resetBTreeSliceGenProg ((mkWhpCoreParams c U V w n_max, base), sIdx)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 8 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with slices := Function.update fs.slices sIdx (resetBTreeSlice (fs.slices sIdx)) }
      s s' := by
  have hch := largeOffsetChain c U V w n_max
  obtain ⟨hfr, hmc, hvp, hsl0, hoth, hbm, hout⟩ :=
    resetBTreeSliceGenProg_spec henv.2.2.2.1 henv.2.1 henv.2.2.2.2.1 henv.2.2.2.2.2.1 hsIdx (s := s)
  have hsl_reset : BTreeSliceMemRep base c U V w n_max sIdx
      (resetBTreeSlice (fs.slices sIdx))
      ((Memory.spec 0).clientState s
        (resetBTreeSliceGenProg ((mkWhpCoreParams c U V w n_max, base), sIdx))).mem :=
    ⟨hsl0.1, hsl0.2.1, hsl0.2.2.1, fun _ hu => absurd hu (Nat.not_lt_zero _)⟩
  refine ⟨hmc, hvp, fastStep_of_sliceUpdate henv.2.1 hsIdx hfr hseed hrep hsl_reset hoth hbm ?_⟩
  intro a ha
  rcases ha with h1 | ⟨h2, _⟩ | h3
  · exact hout a (Or.inl h1)
  · exact hout a (Or.inr h2)
  · exact hout a (Or.inr (by omega))

theorem btreeDeleteGenProg_fastStep {c U V w n_max base sIdx insCount q : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidWhpSlice n_max insCount (fs.slices sIdx) mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) :
    let prog := btreeDeleteGenProg (((mkWhpCoreParams c U V w n_max, base), sIdx), q)
    let s' := (Memory.spec 0).clientState s prog
    let sl' := btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices sIdx) q
    memoryCost prog s ≤ 274 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with slices := Function.update fs.slices sIdx sl' } s s' := by
  have hsl_rep := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 sIdx hsIdx
  obtain ⟨hfr, hmc, hvp, hsl', hoth, hout⟩ :=
    btreeDeleteGenProg_spec henv hsIdx hins hsl_rep hv hq (s := s)
  exact ⟨hmc, hvp, fastStep_of_btreeInPlace henv.2.1 hsIdx hfr hseed hrep hsl' hoth hout⟩

theorem btreeUpdateGenProg_fastStep {c U V w n_max base sIdx insCount q newVal : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidWhpSlice n_max insCount (fs.slices sIdx) mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) (hval : newVal < 2 ^ valLaneBitsWhp n_max) :
    let prog := btreeUpdateGenProg ((((mkWhpCoreParams c U V w n_max, base), sIdx), q), newVal)
    let s' := (Memory.spec 0).clientState s prog
    let sl' := btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices sIdx) q newVal
    memoryCost prog s ≤ 274 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with slices := Function.update fs.slices sIdx sl' } s s' := by
  have hsl_rep := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 sIdx hsIdx
  obtain ⟨hfr, hmc, hvp, hsl', hoth, hout⟩ :=
    btreeUpdateGenProg_spec henv hsIdx hins hsl_rep hv hq hval (s := s)
  exact ⟨hmc, hvp, fastStep_of_btreeInPlace henv.2.1 hsIdx hfr hseed hrep hsl' hoth hout⟩

theorem btreeInsertGenProg_fastStep {c U V w n_max base sIdx insCount q val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidWhpSlice n_max insCount (fs.slices sIdx) mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) (hval : val < 2 ^ valLaneBitsWhp n_max) :
    let prog := btreeInsertGenProg ((((mkWhpCoreParams c U V w n_max, base), sIdx), q), val)
    let s' := (Memory.spec 0).clientState s prog
    let sl' := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices sIdx) q val
    memoryCost prog s ≤ 2426 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with slices := Function.update fs.slices sIdx sl' } s s' := by
  have hsl_rep := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 sIdx hsIdx
  obtain ⟨hfr, hmc, hvp, hsl', _, hoth, hbm, hout⟩ :=
    btreeInsertGenProg_spec henv hsIdx hins hsl_rep hv hq hval (s := s)
  exact ⟨hmc, hvp, fastStep_of_sliceUpdate henv.2.1 hsIdx hfr hseed hrep hsl' hoth hbm hout⟩

/-! ### `BufTrie` `FastStateStep` Wrappers -/

theorem bufDeleteGenProg_fastStep {c U V w n_max base ep rKey : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf ep) mapFn) :
    let prog := bufDeleteGenProg (((mkWhpCoreParams c U V w n_max, base), ep), rKey)
    let s' := (Memory.spec 0).clientState s prog
    let tr' := bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey
    memoryCost prog s ≤ 2 * cTabWhp c + 8 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ { fs with buf := Function.update fs.buf ep tr' } s s' := by
  obtain ⟨hfr, hmc, hvp, htr', hbfr⟩ :=
    bufDeleteGenProg_spec henv hep (hrep.buf_rep hep) hv (rKey := rKey) (s := s)
  exact ⟨hmc, hvp, fastStep_of_bufEpFrame henv.2.1 hep hfr hseed hrep htr' hbfr⟩

theorem bufInsertGenProg_fastStep {c U V w n_max base ep rKey b loc : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf ep) mapFn)
    (hna_cap : (fs.buf ep).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max)
    (hia_cap : (fs.buf ep).itemAlloc < qEpochWhp n_max)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max) :
    let prog := bufInsertGenProg ((((mkWhpCoreParams c U V w n_max, base), ep), rKey), (b, loc))
    let s' := (Memory.spec 0).clientState s prog
    let tr' := bufInsert (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey b loc
    memoryCost prog s ≤ 20 * cTabWhp c + 24 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ { fs with buf := Function.update fs.buf ep tr' } s s' := by
  obtain ⟨hfr, hmc, hvp, htr', hbfr⟩ :=
    bufInsertGenProg_spec henv hep (hrep.buf_rep hep) hv hna_cap hia_cap hb hloc
      (rKey := rKey) (s := s)
  exact ⟨hmc, hvp, fastStep_of_bufEpFrame henv.2.1 hep hfr hseed hrep htr' hbfr⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
